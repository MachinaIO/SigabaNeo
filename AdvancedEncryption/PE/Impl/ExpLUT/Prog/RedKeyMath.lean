import PE.Impl.ExpLUT.SimTrap
import PE.Impl.ExpLUT.Prog.KeyVM

/-!
# `KGsim` on the VM (package G2, item 5): streaming forms of Lemma 11's trapdoor

The math-level reformulations of `simTrap`/`simX`/`vRounds` that the VM routines of the reduction's
key component compute (see `RedKeyPLAN.md`), over the abstract setting:

* `pubZ_apply`, **`pubZ_sub_gadZ_apply`**: row `i` of `M_F (0, z) − (I_W ⊗ g) z` is
  `Σ_c (σ_i(B⁽¹⁾_c) − g_c) z(i, c)` (the gadget columns of `B⁽¹⁾` only);
* **`simTrap_apply`**: `T_sim z q = Σ_ic X q ic · u ic` with `u = gadDec (M_F (0, z) − (I_W ⊗ g) z)`;
* `simX_apply`, **`simTrap_rows`**: `T_sim z = Σ_j Σ_c (V_j)_{·,(0,c)} u(j, c)` (row `j` of `u`
  meets the first `τ` columns of `V_j`);
* `vChain`, **`vChain_eq`**: `vRounds t j` is an index-carrying bit chain of `vStep` (the steps
  for the set bits `s` of `j`, in increasing order, the step at `s` using the row index
  `j mod 2^s`), as `roundsPK_eq_bitChain` for the public side — no queue of `W` matrices.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo.Lattices Matrix

variable {R : Type*} [CommRing R] {S : Setting R} {Wb J Pos : Type*} [Fintype Wb] [Fintype J]

/-! ### `M_F (0, z) − (I_W ⊗ g) z` -/


/-- **`M_F (0, z)`**, row `i`: only the gadget columns of the block `β_i`. -/
theorem pubZ_apply (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos)
    (z : ZIdx S.τ S.E.W → R) (i : Fin S.E.W) :
    pubZ M mpk F z i = ∑ c, S.E.σ (S.idx i) (mpk.B 0 (.inr c)) * z (i, c) := by
  classical
  simp only [pubZ, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
    assemble, keyMat, Matrix.of_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero,
    ite_mul, zero_mul]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp


/-- **Row `i` of `M_F (0, z) − (I_W ⊗ g) z`**: `Σ_c (σ_i(B⁽¹⁾_c) − g_c) z(i, c)`. -/
theorem pubZ_sub_gadZ_apply (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos)
    (z : ZIdx S.τ S.E.W → R) (i : Fin S.E.W) :
    (pubZ M mpk F z - gadZ z) i =
      ∑ c, (S.E.σ (S.idx i) (mpk.B 0 (.inr c)) - S.D.g c) * z (i, c) := by
  rw [Pi.sub_apply, pubZ_apply, gadZ, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun c _ => (sub_mul _ _ _).symm

/-! ### `T_sim` -/

variable [DecidableEq J]

/-- **`T_sim z q = Σ_ic X q ic · u ic`**, `u = gadDec (M_F (0, z) − (I_W ⊗ g) z)`. -/
theorem simTrap_apply (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos) (Rh : SimMat Wb J S)
    (z : ZIdx S.τ S.E.W → R) (q : PIdx Wb J S.τ S.E.W) :
    simTrap M mpk F Rh z q =
      ∑ ic, simX M (h1Of mpk) (keyPK M mpk F) Rh q ic * gadDec (pubZ M mpk F z - gadZ z) ic :=
  rfl

/-- The entry `(q, (j, c))` of `X`: the entry `(q, (0, c))` of `V_j` (on the short coordinates). -/
theorem simX_apply (M : HelperMap S J) (H1 : J → Col S.τ → R) (AF : Matrix (Fin 2) (Col S.τ) R)
    (Rh : SimMat Wb J S) (q : PIdx Wb J S.τ S.E.W) (j : Fin S.E.W) (c : Fin S.τ) :
    simX M H1 AF Rh q (j, c) =
      pOf (fun ℓ => (vRounds M H1 AF Rh S.b le_rfl j).1 ℓ (0, c))
        (fun r => (vRounds M H1 AF Rh S.b le_rfl j).2 r (0, c)) q :=
  rfl

/-- **`T_sim` row by row of `u`**: `T_sim z q = Σ_j Σ_c (V_j)_{q,(0,c)} u(j, c)`. -/
theorem simTrap_rows (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos) (Rh : SimMat Wb J S)
    (z : ZIdx S.τ S.E.W → R) (q : PIdx Wb J S.τ S.E.W) :
    simTrap M mpk F Rh z q =
      ∑ j : Fin S.E.W, ∑ c : Fin S.τ,
        pOf (fun ℓ => (vRounds M (h1Of mpk) (keyPK M mpk F) Rh S.b le_rfl j).1 ℓ (0, c))
          (fun r => (vRounds M (h1Of mpk) (keyPK M mpk F) Rh S.b le_rfl j).2 r (0, c)) q *
        gadDec (pubZ M mpk F z - gadZ z) (j, c) := by
  rw [simTrap_apply, Fintype.sum_prod_type]
  rfl

/-! ### `vRounds` as an index-carrying bit chain -/

/-- One step of the chain at the bit `s`: the row index grows by `2^s` and `V` takes the step
`vStep` from the current row along the binary-basis helper `fwd s`. -/
def vChainStep (M : HelperMap S J) (H1 : J → Col S.τ → R) (s : ℕ) (kv : ℕ × VMat Wb J S) :
    ℕ × VMat Wb J S :=
  if h : s < S.b then (kv.1 + 2 ^ s, vStep H1 (Fin.ofNat S.E.W kv.1) (M.fwd ⟨s, h⟩) kv.2) else kv

/-- **The chain of `V_j`**: the steps for the set bits of `j` below `t`, in increasing order,
starting at row `0` with `V₁`. -/
def vChain (M : HelperMap S J) (H1 : J → Col S.τ → R) (Rh : SimMat Wb J S) (t j : ℕ) :
    ℕ × VMat Wb J S :=
  bitChain (vChainStep M H1) t j (0, vOne Rh)

/-- **`vRounds` is the chain**: for `t ≤ b` and `j < 2^t`, the chain ends at row `j` with
`vRounds t j`. -/
theorem vChain_eq (M : HelperMap S J) (H1 : J → Col S.τ → R) (AF : Matrix (Fin 2) (Col S.τ) R)
    (Rh : SimMat Wb J S) : ∀ (t : ℕ) (ht : t ≤ S.b) (j : ℕ), j < 2 ^ t →
      vChain M H1 Rh t j = (j, vRounds M H1 AF Rh t ht j)
  | 0, _, j, hj => by
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    rfl
  | t + 1, ht, j, hj => by
    unfold vChain
    simp only [bitChain, testBit_top hj]
    by_cases h : j < 2 ^ t
    · rw [decide_eq_false (by omega)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show bitChain (vChainStep M H1) t j (0, vOne Rh) = vChain M H1 Rh t j from rfl,
        vChain_eq M H1 AF Rh t (Nat.le_of_succ_le ht) j h]
      simp only [vRounds, h, ↓reduceIte]
    · rw [decide_eq_true (by omega)]
      simp only [↓reduceIte]
      have hj' : j - 2 ^ t < 2 ^ t := by rw [pow_succ] at hj; omega
      rw [bitChain_congr _ t (fun s hs => (testBit_sub_two_pow (by omega) hj hs).symm),
        show bitChain (vChainStep M H1) t (j - 2 ^ t) (0, vOne Rh) =
          vChain M H1 Rh t (j - 2 ^ t) from rfl,
        vChain_eq M H1 AF Rh t (Nat.le_of_succ_le ht) (j - 2 ^ t) hj']
      have hts : t < S.b := by omega
      simp only [vChainStep, hts, ↓reduceDIte, vRounds, h, ↓reduceIte]
      exact Prod.ext (by simp; omega) rfl

/-- **`V_j` from the chain** (`j < W`). -/
theorem vRounds_eq_vChain (M : HelperMap S J) (H1 : J → Col S.τ → R)
    (AF : Matrix (Fin 2) (Col S.τ) R) (Rh : SimMat Wb J S) (j : ℕ) (hj : j < S.E.W) :
    vRounds M H1 AF Rh S.b le_rfl j = (vChain M H1 Rh S.b j).2 := by
  rw [vChain_eq M H1 AF Rh S.b le_rfl j (by rw [← S.W_eq]; exact hj)]

end AdvancedEncryption.ExpLUT.Prog
