import PE.Impl.ExpLUT.Scheme

/-!
# Simulation forms (Appendix A, Definition 3 and Lemma 10)

The matrix `L` of eq. (3) — `M_F` without its last `2τ` columns — and the simulation forms of the
proof of Theorem 2 (ePrint 2026/2539, Appendix A), over the abstract setting of
`PE.Impl.ExpLUT.Basic`.

* `LCol Wb J τ W`: the **short** columns of `L`: the `Ā` columns of the blocks `β_i` and the blocks
  `η_{i,k}`. The gadget columns of the `β_i` are left out: every simulation matrix of the proof is
  supported on the `Ā` columns (the programming matrices are, by the choice of the hybrids), so the
  simulation matrices `R̂` are matrices `LCol → Col τ`, and the trapdoor of Lemma 11 has zero rows
  on the gadget coordinates by construction (`PE.Impl.ExpLUT.SimTrap`).
* `simL M Ab H1`: `L` restricted to these columns, from `Ā` (`Ab`) and the first rows of the `H_k`
  (`H1`): `L (i', β_i, w) = [i' = i] σ_i(Ā_w)`, `L (i', η_{i,k}, c) = [i' = i] σ_i(H_k⁽¹⁾)_c −
  [i' = i·k] G⁽¹⁾_c`.
* `rowE i a = δ_iᵀ ⊗ a` and **the simulation form** (Definition 3, eq. (6)):
  `SimForm i i' A μ R̂ : δ_iᵀ ⊗ A⁽¹⁾ − δ_{i'}ᵀ ⊗ μ G⁽¹⁾ = L R̂`. It is a statement about the first row
  of a public matrix only (for encodings `⟦μ s_{i'}⟧^A_{s_i}` and for gadget ciphertexts
  `GC_{s_i}(μ s_{i'})` alike).

**Lemma 10**, with the explicit matrices of the outputs:

* Add: `simForm_add`, `simForm_sum` (`R̂₁ + R̂₂`).
* SMul: `simForm_smul` (`R̂ G⁻¹(αG)`).
* Mul: `simForm_mul` (`S + R̂ G⁻¹(C) + μ Ẑ`, `simMul`).
* `σ_k` entrywise: `simForm_σ` (`Π_k σ_k(R̂)`, `simPerm`), from `simL_rot` (`P_k σ_k(L) = L Π_k`).
* The mask switch: `simForm_maskSwitch` (`Ĥ G⁻¹(A') + R̂'`).
* Aut: `simForm_aut` (`simAut`), the composition of the three.
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix

variable {R : Type*} [CommRing R] {S : Setting R}

instance Setting.neZeroW (S : Setting R) : NeZero S.E.W := ⟨S.E.W_pos.ne'⟩

/-- The short columns of `L`: the `Ā` columns of the blocks `β_i` and the blocks `η_{i,k}`. -/
abbrev LCol (Wb J : Type*) (τ W : ℕ) := (Fin W × Wb) ⊕ (Fin W × J × Col τ)

/-- `δ_iᵀ ⊗ a`: the row `a` in the row indexed by `i`. -/
def rowE (i : Fin S.E.W) (a : Col S.τ → R) : Matrix (Fin S.E.W) (Col S.τ) R :=
  Matrix.of fun i' c => if i' = i then a c else 0

/-- The row `i + e` (mod `W`): `δ_i ↦ δ_{g^e · i}`. -/
def Setting.rot (S : Setting R) (e : ℕ) (i : Fin S.E.W) : Fin S.E.W := i + Fin.ofNat S.E.W e

theorem rot_val (e : ℕ) (i : Fin S.E.W) : (S.rot e i : ℕ) = (i + e) % S.E.W := by
  simp [Setting.rot, Fin.val_add]

theorem rot_injective (e : ℕ) : Function.Injective (S.rot e) := fun a b h => by
  simpa [Setting.rot] using h

theorem mulRow_eq {J : Type*} (M : HelperMap S J) (i : Fin S.E.W) (k : J) :
    M.mulRow i k = S.rot (M.je k) i := by
  ext; rw [rot_val]; rfl

/-- `σ_{g^i}` for a row `i`. -/
theorem σ_rot (e : ℕ) (i : Fin S.E.W) (a : R) :
    S.E.σ (S.idx e) (S.E.σ (S.idx i) a) = S.E.σ (S.idx (S.rot e i)) a := by
  rw [S.idx_add, rot_val, Nat.add_comm]

variable {Wb J : Type*} [Fintype Wb] [Fintype J]

/-- **The matrix `L`** of eq. (3), on its short columns. -/
def simL (M : HelperMap S J) (Ab : Wb → R) (H1 : J → Col S.τ → R) :
    Matrix (Fin S.E.W) (LCol Wb J S.τ S.E.W) R :=
  Matrix.of fun i' c => match c with
    | .inl (i, w) => if i' = i then S.E.σ (S.idx i) (Ab w) else 0
    | .inr (i, k, c) => (if i' = i then S.E.σ (S.idx i) (H1 k c) else 0) -
        if i' = M.mulRow i k then S.G 0 c else 0

/-- The simulation matrices: `LCol → Col τ`. -/
abbrev SimMat (Wb J : Type*) (S : Setting R) := Matrix (LCol Wb J S.τ S.E.W) (Col S.τ) R

/-- **The simulation form** (Definition 3, eq. (6)): `δ_iᵀ ⊗ A⁽¹⁾ − δ_{i'}ᵀ ⊗ μ G⁽¹⁾ = L R̂`. -/
def SimForm (M : HelperMap S J) (Ab : Wb → R) (H1 : J → Col S.τ → R) (i i' : Fin S.E.W)
    (A : Matrix (Fin 2) (Col S.τ) R) (μ : R) (Rh : SimMat Wb J S) : Prop :=
  rowE i (A 0) - rowE i' (μ • S.G 0) = simL M Ab H1 * Rh

/-! ### `δ_iᵀ ⊗ ·` -/

theorem rowE_add (i : Fin S.E.W) (a b : Col S.τ → R) : rowE i (a + b) = rowE i a + rowE i b := by
  ext i' c; simp only [rowE, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]; split_ifs <;> simp

theorem rowE_sub (i : Fin S.E.W) (a b : Col S.τ → R) : rowE i (a - b) = rowE i a - rowE i b := by
  ext i' c; simp only [rowE, Matrix.of_apply, Matrix.sub_apply, Pi.sub_apply]; split_ifs <;> simp

theorem rowE_smul (i : Fin S.E.W) (r : R) (a : Col S.τ → R) : rowE i (r • a) = r • rowE i a := by
  ext i' c; simp only [rowE, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply]; split_ifs <;> simp

theorem rowE_zero (i : Fin S.E.W) : rowE i (0 : Col S.τ → R) = 0 := by
  ext i' c; simp [rowE]

theorem rowE_sum {ι : Type*} (T : Finset ι) (i : Fin S.E.W) (a : ι → Col S.τ → R) :
    rowE i (∑ t ∈ T, a t) = ∑ t ∈ T, rowE i (a t) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [rowE_zero]
  | insert t T ht ih => rw [Finset.sum_insert ht, Finset.sum_insert ht, rowE_add, ih]

/-- `(δ_iᵀ ⊗ a) Y = δ_iᵀ ⊗ (a Y)`. -/
theorem rowE_mul (i : Fin S.E.W) (a : Col S.τ → R) (Y : Matrix (Col S.τ) (Col S.τ) R) :
    rowE i a * Y = rowE i (a ᵥ* Y) := by
  ext i' c
  simp only [rowE, Matrix.mul_apply, Matrix.of_apply, Matrix.vecMul, dotProduct]
  split_ifs <;> simp

/-- `G⁽¹⁾ Y = (G Y)⁽¹⁾`. -/
theorem G0_vecMul (Y : Matrix (Col S.τ) (Col S.τ) R) : S.G 0 ᵥ* Y = (S.G * Y) 0 := by
  ext c; simp [Matrix.vecMul, dotProduct, Matrix.mul_apply]

/-- `σ_k` fixes `G⁽¹⁾`. -/
theorem σ_G0 (k : ℕ) (c : Col S.τ) : S.E.σ k (S.G 0 c) = S.G 0 c := by
  have := congrFun (congrFun (G_map_σ (S := S) k) 0) c
  simpa only [Matrix.map_apply] using this

/-- `a G⁻¹(C)`: the digits of `C` weighted by `a`. -/
theorem vecMul_ginv_apply (a : Col S.τ → R) (C : Matrix (Fin 2) (Col S.τ) R) (j : Col S.τ) :
    (a ᵥ* S.ginv C) j = ∑ ri : Col S.τ, digits S C (ri.1, j, ri.2) * a ri := by
  simp only [Matrix.vecMul, dotProduct, ginv_apply, digits]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

variable (M : HelperMap S J) (Ab : Wb → R) (H1 : J → Col S.τ → R)

/-! ### Add and SMul -/

theorem simForm_add {i i' : Fin S.E.W} {A A' : Matrix (Fin 2) (Col S.τ) R} {μ μ' : R}
    {Rh Rh' : SimMat Wb J S} (h : SimForm M Ab H1 i i' A μ Rh) (h' : SimForm M Ab H1 i i' A' μ' Rh') :
    SimForm M Ab H1 i i' (A + A') (μ + μ') (Rh + Rh') := by
  unfold SimForm at *
  rw [Matrix.mul_add, ← h, ← h', show (A + A') 0 = A 0 + A' 0 from rfl, rowE_add, add_smul,
    rowE_add]
  abel

theorem simForm_zero (i i' : Fin S.E.W) : SimForm M Ab H1 i i' 0 0 (0 : SimMat Wb J S) := by
  unfold SimForm
  rw [Matrix.mul_zero, zero_smul, rowE_zero, sub_zero]
  exact rowE_zero i

theorem simForm_sum {ι : Type*} (T : Finset ι) {i i' : Fin S.E.W}
    {A : ι → Matrix (Fin 2) (Col S.τ) R} {μ : ι → R} {Rh : ι → SimMat Wb J S}
    (h : ∀ t ∈ T, SimForm M Ab H1 i i' (A t) (μ t) (Rh t)) :
    SimForm M Ab H1 i i' (∑ t ∈ T, A t) (∑ t ∈ T, μ t) (∑ t ∈ T, Rh t) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using simForm_zero M Ab H1 i i'
  | insert t T ht ih =>
    simp only [Finset.sum_insert ht]
    exact simForm_add M Ab H1 (h t (Finset.mem_insert_self t T))
      (ih fun u hu => h u (Finset.mem_insert_of_mem hu))

/-- **Right multiplication**: `(δ_iᵀ ⊗ A⁽¹⁾) Y − (δ_{i'}ᵀ ⊗ μ G⁽¹⁾) Y = L R̂ Y`. -/
theorem simForm_mul_right {i i' : Fin S.E.W} {A : Matrix (Fin 2) (Col S.τ) R} {μ : R}
    {Rh : SimMat Wb J S} (h : SimForm M Ab H1 i i' A μ Rh) (Y : Matrix (Col S.τ) (Col S.τ) R) :
    rowE i ((A * Y) 0) - rowE i' (μ • (S.G * Y) 0) = simL M Ab H1 * (Rh * Y) := by
  rw [← Matrix.mul_assoc, ← h, Matrix.sub_mul, rowE_mul, rowE_mul, Matrix.smul_vecMul, G0_vecMul]
  congr 2

/-- **SMul_α** (Lemma 10.2): the output is in simulation form with respect to `R̂ G⁻¹(αG)`. -/
theorem simForm_smul (α : R) {i i' : Fin S.E.W} {A : Matrix (Fin 2) (Col S.τ) R} {μ : R}
    {Rh : SimMat Wb J S} (h : SimForm M Ab H1 i i' A μ Rh) :
    SimForm M Ab H1 i i' (smulPK S α A) (α * μ) (Rh * S.ginv (α • S.G)) := by
  have := simForm_mul_right M Ab H1 h (S.ginv (α • S.G))
  rw [G_mul_ginv] at this
  unfold SimForm smulPK
  rw [← this, show (α • S.G) 0 = α • S.G 0 from rfl, smul_smul, mul_comm]

/-! ### Mul -/

/-- The matrix `S` of Lemma 10.3: `S_j = Σ_{(r,i)} (R̂_{r,j,i} G⁻¹(A))_{(r,i)}`. -/
def simS (A : Matrix (Fin 2) (Col S.τ) R) (Rd : Dig S.τ → SimMat Wb J S) : SimMat Wb J S :=
  Matrix.of fun ℓ j => ∑ ri : Col S.τ, (Rd (ri.1, j, ri.2) * S.ginv A) ℓ ri

/-- **The simulation matrix of Mul** (Lemma 10.3): `S + R̂ G⁻¹(C) + μ Ẑ`. -/
def simMul (A C : Matrix (Fin 2) (Col S.τ) R) (μ : R) (Rc Z : SimMat Wb J S)
    (Rd : Dig S.τ → SimMat Wb J S) : SimMat Wb J S :=
  simS A Rd + Rc * S.ginv C + μ • Z

omit [Fintype Wb] [Fintype J] in
theorem simS_apply (A : Matrix (Fin 2) (Col S.τ) R) (Rd : Dig S.τ → SimMat Wb J S) ℓ j :
    simS A Rd ℓ j = ∑ ri : Col S.τ, (Rd (ri.1, j, ri.2) * S.ginv A) ℓ ri := rfl

/-- `L S`, column by column. -/
theorem simL_mul_simS (A : Matrix (Fin 2) (Col S.τ) R) (Rd : Dig S.τ → SimMat Wb J S) :
    simL M Ab H1 * simS A Rd =
      Matrix.of fun w j => ∑ ri : Col S.τ, (simL M Ab H1 * (Rd (ri.1, j, ri.2) * S.ginv A)) w ri := by
  ext w j
  simp only [Matrix.mul_apply, simS_apply, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_comm

/-- **Mul** (Lemma 10.3): from `c` in simulation form at `(i, i)` with respect to `R̂`, a gadget
ciphertext `C` at `(i, i')` with respect to `Ẑ` and its digit encodings at `(i, i)` with respect to
`R̂_{r,j,i''}`, the output of `Mul` is in simulation form at `(i, i')` with respect to
`S + R̂ G⁻¹(C) + μ Ẑ`. -/
theorem simForm_mul {i i' : Fin S.E.W} {A C : Matrix (Fin 2) (Col S.τ) R} {μ ν : R}
    {Rc Z : SimMat Wb J S} {Ad : Dig S.τ → Matrix (Fin 2) (Col S.τ) R} {Rd : Dig S.τ → SimMat Wb J S}
    (hc : SimForm M Ab H1 i i A μ Rc) (hC : SimForm M Ab H1 i i' C ν Z)
    (hd : ∀ t, SimForm M Ab H1 i i (Ad t) (digits S C t) (Rd t)) :
    SimForm M Ab H1 i i' (mulPK S A Ad) (μ * ν) (simMul A C μ Rc Z Rd) := by
  unfold SimForm simMul
  rw [Matrix.mul_add, Matrix.mul_add, simL_mul_simS, ← simForm_mul_right M Ab H1 hc,
    Matrix.mul_smul, ← hC, G_mul_ginv]
  have hS : (Matrix.of fun w j => ∑ ri : Col S.τ,
      (simL M Ab H1 * (Rd (ri.1, j, ri.2) * S.ginv A)) w ri) =
      rowE i (mulPK S A Ad 0) - rowE i ((A 0) ᵥ* S.ginv C) := by
    ext w j
    simp only [Matrix.of_apply]
    simp only [← simForm_mul_right M Ab H1 (hd _), G_mul_ginv, rowE, Matrix.sub_apply,
      Matrix.of_apply, vecMul_ginv_apply, mulPK, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp [Finset.sum_sub_distrib]
  rw [hS, show (A * S.ginv C) 0 = A 0 ᵥ* S.ginv C from rfl]
  simp only [rowE_smul, smul_sub, smul_smul]
  abel

/-! ### Automorphisms -/

/-- The columns of `L` moved by `σ_{g^e}`: `β_i ↦ β_{g^e i}`, `η_{i,k} ↦ η_{g^e i, k}`. -/
def rotC (e : ℕ) : LCol Wb J S.τ S.E.W → LCol Wb J S.τ S.E.W
  | .inl (i, w) => .inl (S.rot e i, w)
  | .inr (i, k, c) => .inr (S.rot e i, k, c)

/-- The rows moved by `σ_{g^e}`, as a permutation. -/
def rotEquiv (e : ℕ) : Fin S.E.W ≃ Fin S.E.W := Equiv.addRight (Fin.ofNat S.E.W e)

omit [Fintype Wb] [Fintype J] in
theorem rotEquiv_apply (e : ℕ) (i : Fin S.E.W) : rotEquiv (S := S) e i = S.rot e i := rfl

/-- The columns moved by `σ_{g^e}`, as a permutation. -/
def rotCEquiv (e : ℕ) : LCol Wb J S.τ S.E.W ≃ LCol Wb J S.τ S.E.W :=
  Equiv.sumCongr (Equiv.prodCongr (rotEquiv e) (Equiv.refl _))
    (Equiv.prodCongr (rotEquiv e) (Equiv.refl _))

omit [Fintype Wb] [Fintype J] in
theorem rotCEquiv_apply (e : ℕ) (c : LCol Wb J S.τ S.E.W) : rotCEquiv e c = rotC e c := by
  rcases c with ⟨i, w⟩ | ⟨i, k, c⟩ <;> rfl

omit [Fintype Wb] [Fintype J] in
/-- **`P_k σ_k(L) = L Π_k`**: `L (g^e i', Π c) = σ_{g^e}(L (i', c))`. -/
theorem simL_rot (e : ℕ) (i' : Fin S.E.W) (c : LCol Wb J S.τ S.E.W) :
    simL M Ab H1 (S.rot e i') (rotC e c) = S.E.σ (S.idx e) (simL M Ab H1 i' c) := by
  have hinj := rot_injective (S := S) e
  rcases c with ⟨i, w⟩ | ⟨i, k, c⟩
  · simp only [simL, rotC, Matrix.of_apply, hinj.eq_iff]
    split_ifs <;> simp [σ_rot]
  · simp only [simL, rotC, Matrix.of_apply, hinj.eq_iff, map_sub]
    have hm : M.mulRow (S.rot e i) k = S.rot e (M.mulRow i k) := by
      rw [mulRow_eq, mulRow_eq]; simp only [Setting.rot]; abel
    simp only [hm, hinj.eq_iff]
    congr 1
    · split_ifs <;> simp [σ_rot]
    · split_ifs <;> simp [σ_G0]

/-- **The simulation matrix of `σ_{g^e}` entrywise**: `Π_k σ_k(R̂)`. -/
def simPerm (e : ℕ) (Rh : SimMat Wb J S) : SimMat Wb J S :=
  Matrix.of fun c j => S.E.σ (S.idx e) (Rh ((rotCEquiv e).symm c) j)

/-- **σ_k entrywise** (first step of Lemma 10.4): `σ_{g^e}(c)` is in simulation form at
`(g^e i, g^e i')` with respect to `Π σ(R̂)`. -/
theorem simForm_σ (e : ℕ) {i i' : Fin S.E.W} {A : Matrix (Fin 2) (Col S.τ) R} {μ : R}
    {Rh : SimMat Wb J S} (h : SimForm M Ab H1 i i' A μ Rh) :
    SimForm M Ab H1 (S.rot e i) (S.rot e i') (autMat S (S.idx e) A) (S.E.σ (S.idx e) μ)
      (simPerm e Rh) := by
  unfold SimForm at h ⊢
  ext w j
  obtain ⟨w', rfl⟩ : ∃ w', S.rot e w' = w :=
    ⟨(rotEquiv e).symm w, by rw [← rotEquiv_apply, Equiv.apply_symm_apply]⟩
  have hR : (simL M Ab H1 * simPerm e Rh) (S.rot e w') j =
      S.E.σ (S.idx e) ((simL M Ab H1 * Rh) w' j) := by
    simp only [Matrix.mul_apply, simPerm, Matrix.of_apply, map_sum, map_mul]
    refine (Equiv.sum_comp (rotCEquiv e) _).symm.trans (Finset.sum_congr rfl fun c _ => ?_)
    rw [Equiv.symm_apply_apply, rotCEquiv_apply, simL_rot]
  rw [hR, ← h]
  simp only [rowE, Matrix.sub_apply, Matrix.of_apply, (rot_injective (S := S) e).eq_iff, autMat,
    Matrix.map_apply, Pi.smul_apply, smul_eq_mul, map_sub]
  split_ifs <;> simp [σ_G0]

/-- **The mask switch** (third step of Lemma 10.4): a helper `H` in simulation form at `(i₀, i₁)`
(payload `1`) with respect to `Ĥ`, and `A'` at `(i₁, i₂)` with respect to `R̂'`, give `H G⁻¹(A')` at
`(i₀, i₂)` with respect to `Ĥ G⁻¹(A') + R̂'`. -/
theorem simForm_maskSwitch {i₀ i₁ i₂ : Fin S.E.W} {H A' : Matrix (Fin 2) (Col S.τ) R} {μ : R}
    {Rh Rh' : SimMat Wb J S} (hh : SimForm M Ab H1 i₀ i₁ H 1 Rh) (h' : SimForm M Ab H1 i₁ i₂ A' μ Rh') :
    SimForm M Ab H1 i₀ i₂ (H * S.ginv A') μ (Rh * S.ginv A' + Rh') := by
  have h1 := simForm_mul_right M Ab H1 hh (S.ginv A')
  rw [G_mul_ginv, one_smul] at h1
  unfold SimForm at *
  rw [Matrix.mul_add, ← h1, ← h']
  abel

/-- **The simulation matrix of `Aut_k`** (Lemma 10.4), `k = g^e`: `Ĥ_k G⁻¹(A'_k) + R̂'_k` with
`R̂'_k` the matrix of `Mul(σ_k(c), RHS_{s_k}(C_k))`. -/
def simAut (e : ℕ) (Hk' : Matrix (Fin 2) (Col S.τ) R) (Aaut : Dig S.τ → Matrix (Fin 2) (Col S.τ) R)
    (A : Matrix (Fin 2) (Col S.τ) R) (hk' : Col S.τ → R) (μ : R) (Rhk RC : SimMat Wb J S)
    (Rd : Dig S.τ → SimMat Wb J S) (Rc : SimMat Wb J S) : SimMat Wb J S :=
  Rhk * S.ginv (autMid S (S.idx e) Aaut A) +
    simMul (autMat S (S.idx e) A) (gcAut S (S.idx e) Hk' hk') (S.E.σ (S.idx e) μ) (simPerm e Rc) RC Rd

/-- **Aut_k** (Lemma 10.4), `k = g^e`: from `c` in simulation form at `(i, i)` with respect to `R̂`,
the helper `H_k` at `(i, k i)`, the gadget ciphertext `C_k = σ_k(H_{k'}) − [0; σ_k(h_{k'})]` at
`(k i, i)` and its digit encodings at `(k i, k i)`, `Aut_k(c)` is in simulation form at `(i, i)`
with respect to `simAut`. -/
theorem simForm_aut (e : ℕ) {i : Fin S.E.W} {A Hk Hk' : Matrix (Fin 2) (Col S.τ) R} {μ : R}
    {hk' : Col S.τ → R} {Aaut : Dig S.τ → Matrix (Fin 2) (Col S.τ) R} {Rc Rhk RC : SimMat Wb J S}
    {Rd : Dig S.τ → SimMat Wb J S}
    (hc : SimForm M Ab H1 i i A μ Rc) (hh : SimForm M Ab H1 i (S.rot e i) Hk 1 Rhk)
    (hC : SimForm M Ab H1 (S.rot e i) i (gcAut S (S.idx e) Hk' hk') 1 RC)
    (hd : ∀ t, SimForm M Ab H1 (S.rot e i) (S.rot e i) (Aaut t)
      (digits S (gcAut S (S.idx e) Hk' hk') t) (Rd t)) :
    SimForm M Ab H1 i i (autPK S (S.idx e) Hk Aaut A) (S.E.σ (S.idx e) μ)
      (simAut e Hk' Aaut A hk' μ Rhk RC Rd Rc) := by
  have h1 := simForm_σ M Ab H1 e hc
  have h2 := simForm_mul M Ab H1 h1 hC hd
  rw [mul_one] at h2
  exact simForm_maskSwitch M Ab H1 hh h2

/-! ### Fresh simulation forms -/

variable [DecidableEq J]

/-- The embedding `J_{η_{i,k}}` of the block `η_{i,k}`. -/
def jη (i : Fin S.E.W) (k : J) : SimMat Wb J S :=
  Matrix.of fun c col => match c with
    | .inl _ => 0
    | .inr (i', k', c') => if i' = i ∧ k' = k ∧ c' = col then 1 else 0

/-- `J_{β_i} Z`: the matrix `Z ∈ R^{m̄ × 2τ}` on the `Ā` columns of the block `β_i`. -/
def jβ (i : Fin S.E.W) (Z : Matrix Wb (Col S.τ) R) : SimMat Wb J S :=
  Matrix.of fun c col => match c with
    | .inl (i', w) => if i' = i then Z w col else 0
    | .inr _ => 0

/-- `L J_{η_{i,k}} = δ_iᵀ ⊗ σ_i(H_k⁽¹⁾) − δ_{i·k}ᵀ ⊗ G⁽¹⁾`. -/
theorem simL_mul_jη (i : Fin S.E.W) (k : J) :
    simL M Ab H1 * jη i k = rowE i (S.E.σ (S.idx i) ∘ H1 k) - rowE (M.mulRow i k) (S.G 0) := by
  ext w col
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, jη, Matrix.of_apply, mul_zero,
    Finset.sum_const_zero, zero_add]
  rw [Finset.sum_eq_single (i, k, col)]
  · simp [simL, rowE]
  · rintro ⟨i', k', c'⟩ _ hb
    split_ifs with h
    · obtain ⟨rfl, rfl, rfl⟩ := h
      exact absurd rfl hb
    · exact mul_zero _
  · simp

omit [DecidableEq J] in
/-- `L J_{β_i} Z = δ_iᵀ ⊗ σ_i(Ā) Z`. -/
theorem simL_mul_jβ (i : Fin S.E.W) (Z : Matrix Wb (Col S.τ) R) :
    simL M Ab H1 * jβ i Z = rowE i ((S.E.σ (S.idx i) ∘ Ab) ᵥ* Z) := by
  ext w col
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, jβ, Matrix.of_apply, mul_zero,
    Finset.sum_const_zero, add_zero, Fintype.sum_prod_type, mul_ite]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
  simp only [ite_true, simL, Matrix.of_apply, rowE, Matrix.vecMul, dotProduct, Function.comp_apply]
  split_ifs <;> simp

/-- **A helper**, `h_k : ⟦s_k⟧^{H_k}_{s_i}` with `H_k⁽¹⁾ = σ_i(H1_k)`, is in simulation form at
`(i, i·k)` with respect to `J_{η_{i,k}}` (payload `1`). -/
theorem simForm_jη {i : Fin S.E.W} {k : J} {A : Matrix (Fin 2) (Col S.τ) R}
    (hA : A 0 = S.E.σ (S.idx i) ∘ H1 k) : SimForm M Ab H1 i (M.mulRow i k) A 1 (jη i k) := by
  unfold SimForm
  rw [simL_mul_jη, hA, one_smul]

omit [DecidableEq J] in
/-- **A programmed matrix** `A⁽¹⁾ = σ_i(Ā) Z + μ G⁽¹⁾` is in simulation form at `(i, i)` with
respect to `J_{β_i} Z`. -/
theorem simForm_jβ {i : Fin S.E.W} {A : Matrix (Fin 2) (Col S.τ) R} {μ : R} {Z : Matrix Wb (Col S.τ) R}
    (hA : A 0 = (S.E.σ (S.idx i) ∘ Ab) ᵥ* Z + μ • S.G 0) : SimForm M Ab H1 i i A μ (jβ i Z) := by
  unfold SimForm
  rw [simL_mul_jβ, hA, rowE_add]
  abel

end AdvancedEncryption.ExpLUT
