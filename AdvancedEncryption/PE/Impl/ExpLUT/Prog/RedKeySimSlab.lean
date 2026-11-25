import PE.Impl.ExpLUT.SimEval
import PE.Impl.ExpLUT.Prog.KeyVM

/-!
# `KGsim` on the VM (module 6a): the simulation matrices slab by slab

The rows of a simulation matrix `R̂ ∈ R^{LCol × 2τ}` are indexed by `LCol = (Fin W × Wb) ⊕
(Fin W × J × Col τ) ≃ Fin W × Rest` with `Rest = Wb ⊕ (J × Col τ)` (`lcol i r`). Every operation of
Corollary 1's propagation maps the **slab** `r` (the `W` rows `(i, r)`, `i < W`) of its outputs to a
function of the slabs `r` of its inputs only:

* `simS`, `simMul`, `· * Y`, sums, scalings: row by row (`slab_simMul`);
* `simPerm e`: the rows of a slab are rotated, `(i, r) ↦ (g^e i, r)`, and `σ_{g^e}` applied
  (`slab_simPerm`);
* hence `simAut`, `simRounds`, `simLut`, `simEvalAt` (`slab_simAut`, `slab_simRounds`,
  `slab_simLut`, **`slab_simEvalAt`**, **`slab_simEval`**);
* the fresh matrices: `jβ i Z` lives on the slabs `inl w` (`slab_jβ`), `jη i k` on the slabs
  `inr (k, c')` (`slab_jη`).

So `R̂_F = simKey …` is computed slab by slab (`slabKey`, **`slab_simKey`**): each slab only needs
the public matrices of the evaluation and the slab `r` of the fresh data, a `W × 2τ` matrix — the
VM computes `R̂_F` as `|Rest|` independent slab evaluations (module 6b).
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo.Lattices Matrix

variable {R : Type*} [CommRing R] {S : Setting R} {Wb J Pos : Type*} [Fintype Wb] [Fintype J]

/-! ### Slabs -/

/-- The slab indices: the `Ā` columns, then the `η` columns `(k, c)`. -/
abbrev Rest (Wb J : Type*) (τ : ℕ) := Wb ⊕ (J × Col τ)

/-- The row `(i, r)` of `L`'s columns. -/
def lcol (i : Fin S.E.W) : Rest Wb J S.τ → LCol Wb J S.τ S.E.W
  | .inl w => .inl (i, w)
  | .inr (k, c) => .inr (i, k, c)

/-- A slab: `W` rows of `2τ` entries. -/
abbrev Slab (S : Setting R) := Fin S.E.W → Col S.τ → R

/-- **The slab `r`** of a simulation matrix. -/
def slab (Rh : SimMat Wb J S) (r : Rest Wb J S.τ) : Slab S := fun i => Rh (lcol i r)

theorem slab_add (A B : SimMat Wb J S) (r : Rest Wb J S.τ) : slab (A + B) r = slab A r + slab B r :=
  rfl

theorem slab_smul (μ : R) (A : SimMat Wb J S) (r : Rest Wb J S.τ) :
    slab (μ • A) r = μ • slab A r := rfl

theorem slab_mul (A : SimMat Wb J S) (Y : Matrix (Col S.τ) (Col S.τ) R) (r : Rest Wb J S.τ) :
    slab (A * Y) r = fun i => slab A r i ᵥ* Y := rfl

theorem slab_sum {ι : Type*} (T : Finset ι) (A : ι → SimMat Wb J S) (r : Rest Wb J S.τ) :
    slab (∑ j ∈ T, A j) r = ∑ j ∈ T, slab (A j) r := by
  classical
  funext i c
  induction T using Finset.induction_on with
  | empty => rfl
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    simp only [slab, Matrix.add_apply, Pi.add_apply] at ih ⊢
    rw [ih]

/-! ### The operations on slabs -/

/-- `simMul` on a slab: row by row. -/
def slabMul (A C : Matrix (Fin 2) (Col S.τ) R) (μ : R) (sc sz : Slab S) (sd : Dig S.τ → Slab S) :
    Slab S :=
  fun i j => (∑ ri : Col S.τ, (sd (ri.1, j, ri.2) i ᵥ* S.ginv A) ri) + (sc i ᵥ* S.ginv C) j +
    μ * sz i j

theorem slab_simMul (A C : Matrix (Fin 2) (Col S.τ) R) (μ : R) (Rc Z : SimMat Wb J S)
    (Rd : Dig S.τ → SimMat Wb J S) (r : Rest Wb J S.τ) :
    slab (simMul A C μ Rc Z Rd) r = slabMul A C μ (slab Rc r) (slab Z r) (fun d => slab (Rd d) r) :=
  rfl

/-- `simPerm e` on a slab: rotate the rows by `g^e`, apply `σ_{g^e}`. -/
def slabPerm (e : ℕ) (s : Slab S) : Slab S :=
  fun i j => S.E.σ (S.idx e) (s ((rotEquiv (S := S) e).symm i) j)

theorem rotCEquiv_symm_lcol (e : ℕ) (i : Fin S.E.W) (r : Rest Wb J S.τ) :
    (rotCEquiv (Wb := Wb) (J := J) (S := S) e).symm (lcol i r) =
      lcol ((rotEquiv (S := S) e).symm i) r := by
  rcases r with w | ⟨k, c⟩ <;> rfl

theorem slab_simPerm (e : ℕ) (Rh : SimMat Wb J S) (r : Rest Wb J S.τ) :
    slab (simPerm e Rh) r = slabPerm e (slab Rh r) := by
  funext i j
  simp only [slab, simPerm, Matrix.of_apply, slabPerm, rotCEquiv_symm_lcol]

/-- `simAut` on a slab. -/
def slabAut (e : ℕ) (Hk' : Matrix (Fin 2) (Col S.τ) R) (Aaut : Dig S.τ → Matrix (Fin 2) (Col S.τ) R)
    (A : Matrix (Fin 2) (Col S.τ) R) (hk' : Col S.τ → R) (μ : R) (sh sC : Slab S)
    (sd : Dig S.τ → Slab S) (sc : Slab S) : Slab S :=
  (fun i => sh i ᵥ* S.ginv (autMid S (S.idx e) Aaut A)) +
    slabMul (autMat S (S.idx e) A) (gcAut S (S.idx e) Hk' hk') (S.E.σ (S.idx e) μ)
      (slabPerm e sc) sC sd

theorem slab_simAut (e : ℕ) (Hk' : Matrix (Fin 2) (Col S.τ) R)
    (Aaut : Dig S.τ → Matrix (Fin 2) (Col S.τ) R) (A : Matrix (Fin 2) (Col S.τ) R) (hk' : Col S.τ → R)
    (μ : R) (Rhk RC : SimMat Wb J S) (Rd : Dig S.τ → SimMat Wb J S) (Rc : SimMat Wb J S)
    (r : Rest Wb J S.τ) :
    slab (simAut e Hk' Aaut A hk' μ Rhk RC Rd Rc) r =
      slabAut e Hk' Aaut A hk' μ (slab Rhk r) (slab RC r) (fun d => slab (Rd d) r) (slab Rc r) := by
  unfold simAut slabAut
  rw [slab_add, slab_mul, slab_simMul, slab_simPerm]

/-- The slabs of the helper data of the rounds. -/
structure SlabAut (S : Setting R) where
  /-- Of `H_{g_t}`. -/
  hf : ℕ → Slab S
  /-- Of `C_{g_t}`. -/
  C : ℕ → Slab S
  /-- Of the digit encodings of `C_{g_t}`. -/
  aut : ℕ → Dig S.τ → Slab S

/-- The slab `r` of the helper data. -/
def autSlab (Q : SimAut Wb J S) (r : Rest Wb J S.τ) : SlabAut S :=
  ⟨fun t => ExpLUT.Prog.slab (Q.Rhf t) r, fun t => ExpLUT.Prog.slab (Q.RC t) r,
    fun t d => ExpLUT.Prog.slab (Q.Raut t d) r⟩

/-- `simRounds` on a slab. -/
def slabRounds (P : AutPub S) (A : Matrix (Fin 2) (Col S.τ) R) (h : AutData S) (Q : SlabAut S)
    (μ : R) (sc : Slab S) : ℕ → ℕ → Slab S
  | 0, _ => sc
  | t + 1, j =>
    if j < 2 ^ t then slabRounds P A h Q μ sc t j
    else slabAut (2 ^ t) (P.Hi t) (P.Aaut t) (roundsPK P A t (j - 2 ^ t)) (h.hi t)
      (S.E.σ (S.idx (j - 2 ^ t)) μ) (Q.hf t) (Q.C t) (Q.aut t) (slabRounds P A h Q μ sc t (j - 2 ^ t))

theorem slab_simRounds (P : AutPub S) (A : Matrix (Fin 2) (Col S.τ) R) (h : AutData S)
    (Q : SimAut Wb J S) (μ : R) (Rc : SimMat Wb J S) (r : Rest Wb J S.τ) :
    ∀ t j, slab (simRounds P A h Q μ Rc t j) r = slabRounds P A h (autSlab Q r) μ (slab Rc r) t j
  | 0, _ => rfl
  | t + 1, j => by
    simp only [simRounds, slabRounds]
    split_ifs
    · exact slab_simRounds P A h Q μ Rc r t j
    · rw [slab_simAut, slab_simRounds P A h Q μ Rc r t (j - 2 ^ t)]; rfl

/-- `simLut` on a slab: `Σ_{j<W} s_j G⁻¹(α_j G)`. -/
def slabLut (P : AutPub S) (coef : ℕ → R) (A : Matrix (Fin 2) (Col S.τ) R) (h : AutData S)
    (Q : SlabAut S) (μ : R) (sc : Slab S) : Slab S :=
  ∑ j ∈ Finset.range S.E.W, fun i => slabRounds P A h Q μ sc S.b j i ᵥ* S.ginv (coef j • S.G)

theorem slab_simLut (P : AutPub S) (coef : ℕ → R) (A : Matrix (Fin 2) (Col S.τ) R) (h : AutData S)
    (Q : SimAut Wb J S) (μ : R) (Rc : SimMat Wb J S) (r : Rest Wb J S.τ) :
    slab (simLut P coef A h Q μ Rc) r = slabLut P coef A h (autSlab Q r) μ (slab Rc r) := by
  unfold simLut slabLut
  rw [slab_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [slab_mul, slab_simRounds]

/-- The slabs of the fresh data of the evaluation. -/
structure SlabFresh (Pos : Type*) (S : Setting R) where
  /-- Of `c₀`. -/
  R0 : Slab S
  /-- Of `C^in_t`. -/
  Zin : Pos → Slab S
  /-- Of the digit encodings of `C^in_t`. -/
  Rin : Pos → Dig S.τ → Slab S
  /-- Of the helper data. -/
  aut : SlabAut S

/-- The slab `r` of the fresh data. -/
def freshSlab (Q : SimFresh Wb J Pos S) (r : Rest Wb J S.τ) : SlabFresh Pos S :=
  ⟨ExpLUT.Prog.slab Q.R0 r, fun t => ExpLUT.Prog.slab (Q.Zin t) r,
    fun t d => ExpLUT.Prog.slab (Q.Rin t d) r, autSlab Q.aut r⟩

/-- `simEvalAt` on a slab. -/
def slabEvalAt (F : BP Pos) (pp : EvalPub S Pos) (ct : EvalCTData S Pos) (x : Pos → ℕ)
    (Q : SlabFresh Pos S) : ℕ → Slab S
  | 0 => Q.R0
  | i + 1 => slabLut pp.aut (F.coefs S i) (mulPK S (evalPKAt F pp i) (pp.Ain (F.read i))) ct.aut
      Q.aut (S.E.X ^ (F.state x i + F.w * x (F.read i)))
      (slabMul (evalPKAt F pp i) (ct.Cin (F.read i)) (S.E.X ^ F.state x i)
        (slabEvalAt F pp ct x Q i) (Q.Zin (F.read i)) (Q.Rin (F.read i)))

/-- **The evaluation, slab by slab.** -/
theorem slab_simEvalAt (F : BP Pos) (pp : EvalPub S Pos) (ct : EvalCTData S Pos) (x : Pos → ℕ)
    (Q : SimFresh Wb J Pos S) (r : Rest Wb J S.τ) :
    ∀ i, slab (simEvalAt F pp ct x Q i) r = slabEvalAt F pp ct x (freshSlab Q r) i
  | 0 => rfl
  | i + 1 => by
    simp only [simEvalAt, slabEvalAt]
    rw [slab_simLut, slab_simMul, slab_simEvalAt F pp ct x Q r i]
    rfl

/-- **`R̂_F`, slab by slab.** -/
theorem slab_simEval (F : BP Pos) (pp : EvalPub S Pos) (ct : EvalCTData S Pos) (x : Pos → ℕ)
    (Q : SimFresh Wb J Pos S) (r : Rest Wb J S.τ) :
    slab (simEval F pp ct x Q) r = slabEvalAt F pp ct x (freshSlab Q r) F.T :=
  slab_simEvalAt F pp ct x Q r F.T

/-! ### The fresh slabs of the scheme -/

variable [DecidableEq J]

/-- The slab of `J_{β_i} Z`: `Z_w` at the row `i` of the slab `inl w`, zero elsewhere. -/
def slabβ (i : Fin S.E.W) (Z : Matrix Wb (Col S.τ) R) : Rest Wb J S.τ → Slab S
  | .inl w => fun i' c => if i' = i then Z w c else 0
  | .inr _ => 0

/-- The slab of `J_{η_{i,k}}`: the unit row `e_{c'}` at the row `i` of the slab `inr (k, c')`. -/
def slabη (i : Fin S.E.W) (k : J) : Rest Wb J S.τ → Slab S
  | .inl _ => 0
  | .inr (k', c') => fun i' c => if i' = i ∧ k' = k ∧ c' = c then 1 else 0

theorem slab_jβ (i : Fin S.E.W) (Z : Matrix Wb (Col S.τ) R) (r : Rest Wb J S.τ) :
    slab (jβ (Wb := Wb) (J := J) i Z) r = slabβ i Z r := by
  funext i' c
  rcases r with w | ⟨k, c'⟩ <;> rfl

theorem slab_jη (i : Fin S.E.W) (k : J) (r : Rest Wb J S.τ) :
    slab (jη (Wb := Wb) (S := S) i k) r = slabη i k r := by
  funext i' c
  rcases r with w | ⟨k', c'⟩ <;> rfl

/-- The slab `r` of `finExt`. -/
theorem slab_finExt (f : Fin S.b → SimMat Wb J S) (r : Rest Wb J S.τ) (t : ℕ) :
    slab (finExt f t) r = finExt (fun t => slab (f t) r) t := by
  unfold finExt
  split_ifs <;> rfl

/-- The fresh slabs of a programmed public key. -/
def slabFreshOf (M : HelperMap S J) (P : Prog S Wb J Pos) (r : Rest Wb J S.τ) : SlabFresh Pos S where
  R0 := slabβ S.row0 P.R0 r
  Zin t := slabβ S.row0 (P.Z t) r
  Rin t d := slabβ S.row0 (P.Rin t d) r
  aut :=
    { hf := finExt fun t => slabη S.row0 (M.fwd t) r
      C := finExt fun t => slabη (S.rowT t) (M.inv t) r
      aut := finExt fun t d => slabβ (S.rowT t) (P.Raut t d) r }

theorem simFreshOf_slab (M : HelperMap S J) (P : Prog S Wb J Pos) (r : Rest Wb J S.τ) :
    freshSlab (simFreshOf M P) r = slabFreshOf M P r := by
  simp only [freshSlab, simFreshOf, slabFreshOf, autSlab, slab_jβ]
  congr 1
  congr 1
  · funext t; rw [slab_finExt]; simp only [slab_jη]
  · funext t; rw [slab_finExt]; simp only [slab_jη]
  · funext t d
    unfold finExt
    split_ifs <;> simp [slab_jβ]
    rfl

/-- **`R̂_F = simKey …`, slab by slab**: the slab `r` is the slab evaluation from the public data
and the fresh slabs `slabFreshOf M P r` only. -/
theorem slab_simKey (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos)
    (ct : Ciphertext S Wb J Pos) (x : Pos → ℕ) (P : Prog S Wb J Pos) (r : Rest Wb J S.τ) :
    slab (simKey M mpk F ct x P) r =
      slabEvalAt F (evalPub M mpk) (evalData M mpk ct) x (slabFreshOf M P r) F.T := by
  unfold simKey
  rw [slab_simEval, simFreshOf_slab]

/-! ### The rounds as an index-carrying paired bit chain -/

section Chain

/-- One step of the paired chain at the bit `s`: the row index grows by `2^s`, the public matrix
takes `Aut_{g_s}` (`autPK`), the slab takes `slabAut` with the payload `σ_{idx k}(μ)` of the
current index `k`. -/
def slabChainStep (P : AutPub S) (h : AutData S) (Q : SlabAut S) (μ : R) (s : ℕ)
    (st : ℕ × Matrix (Fin 2) (Col S.τ) R × Slab S) : ℕ × Matrix (Fin 2) (Col S.τ) R × Slab S :=
  (st.1 + 2 ^ s, autPK S (S.kf s) (P.Hf s) (P.Aaut s) st.2.1,
    slabAut (2 ^ s) (P.Hi s) (P.Aaut s) st.2.1 (h.hi s) (S.E.σ (S.idx st.1) μ) (Q.hf s) (Q.C s)
      (Q.aut s) st.2.2)

/-- **The paired chain** of `j`: the steps for the set bits of `j` below `t`, in increasing order,
from `(0, A, s_c)`. -/
def slabChain (P : AutPub S) (A : Matrix (Fin 2) (Col S.τ) R) (h : AutData S) (Q : SlabAut S)
    (μ : R) (sc : Slab S) (t j : ℕ) : ℕ × Matrix (Fin 2) (Col S.τ) R × Slab S :=
  bitChain (slabChainStep P h Q μ) t j (0, A, sc)

/-- **The rounds are the paired chain**: for `j < 2^t` the chain ends at `(j, roundsPK t j,
slabRounds t j)`. -/
theorem slabChain_eq (P : AutPub S) (A : Matrix (Fin 2) (Col S.τ) R) (h : AutData S)
    (Q : SlabAut S) (μ : R) (sc : Slab S) : ∀ t j, j < 2 ^ t →
      slabChain P A h Q μ sc t j = (j, roundsPK P A t j, slabRounds P A h Q μ sc t j)
  | 0, j, hj => by
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    rfl
  | t + 1, j, hj => by
    unfold slabChain
    simp only [bitChain, testBit_top hj]
    by_cases hlt : j < 2 ^ t
    · rw [decide_eq_false (by omega)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show bitChain (slabChainStep P h Q μ) t j (0, A, sc) = slabChain P A h Q μ sc t j from rfl,
        slabChain_eq P A h Q μ sc t j hlt]
      simp only [roundsPK, slabRounds, hlt, ↓reduceIte]
    · rw [decide_eq_true (by omega)]
      simp only [↓reduceIte]
      have hj' : j - 2 ^ t < 2 ^ t := by rw [pow_succ] at hj; omega
      rw [bitChain_congr _ t (fun s hs => (testBit_sub_two_pow (by omega) hj hs).symm),
        show bitChain (slabChainStep P h Q μ) t (j - 2 ^ t) (0, A, sc) =
          slabChain P A h Q μ sc t (j - 2 ^ t) from rfl,
        slabChain_eq P A h Q μ sc t (j - 2 ^ t) hj']
      simp only [slabChainStep, roundsPK, slabRounds, hlt, ↓reduceIte]
      exact Prod.ext (by simp; omega) rfl

/-- **The table on a slab, by chains**: `Σ_{j<W} (chain j).slab · G⁻¹(α_j G)`. -/
theorem slabLut_eq_chain (P : AutPub S) (coef : ℕ → R) (A : Matrix (Fin 2) (Col S.τ) R)
    (h : AutData S) (Q : SlabAut S) (μ : R) (sc : Slab S) :
    slabLut P coef A h Q μ sc = ∑ j ∈ Finset.range S.E.W,
      fun i => (slabChain P A h Q μ sc S.b j).2.2 i ᵥ* S.ginv (coef j • S.G) := by
  unfold slabLut
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [slabChain_eq P A h Q μ sc S.b j (by rw [← S.W_eq]; exact Finset.mem_range.mp hj)]

/-- **The public table, by the same chains**: `lutPK = Σ_{j<W} smulPK (α_j) (chain j).public`. -/
theorem lutPK_eq_chain (P : AutPub S) (coef : ℕ → R) (A : Matrix (Fin 2) (Col S.τ) R)
    (h : AutData S) (Q : SlabAut S) (μ : R) (sc : Slab S) :
    lutPK P coef A = ∑ j ∈ Finset.range S.E.W,
      smulPK S (coef j) (slabChain P A h Q μ sc S.b j).2.1 := by
  unfold lutPK
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [slabChain_eq P A h Q μ sc S.b j (by rw [← S.W_eq]; exact Finset.mem_range.mp hj)]

end Chain

end AdvancedEncryption.ExpLUT.Prog
