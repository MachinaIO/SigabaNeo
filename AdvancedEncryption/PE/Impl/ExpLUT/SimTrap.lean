import PE.Impl.ExpLUT.SimBound
import PE.Impl.ExpLUT.KeyGen

/-!
# Lemma 11: a gadget trapdoor of `M_F` without the trapdoor of `B⁽¹⁾`

For `F(x*) = 1` and `R̂_F` with `δ₁ᵀ ⊗ A_F⁽¹⁾ − δ₁ᵀ ⊗ G⁽¹⁾ = L R̂_F` (Corollary 1), the proof of
Lemma 11 (ePrint 2026/2539, Appendix A) builds, for every row `i` of `H`, a matrix `V_i` with
`M_F V_i = δ_iᵀ ⊗ G⁽¹⁾`:

* `V₁ = (−R̂_F; I_{2τ})` (`vOne`, `mfMul_vOne`);
* `V_{j·a} = V_j G̃⁻¹(σ_j(H_a⁽¹⁾)) − J̃_{η_{j,a}}` (`vStep`, `mfMul_vStep`), with `G̃⁻¹(Y)` the
  binary matrix with `G⁽¹⁾ G̃⁻¹(Y) = Y` (`ginvTop`);
* along the binary basis `g_t` (`vRounds`, `mfMul_vRounds`), every row after `b` rounds.

The first `τ` columns of the `V_i` form `X` with `M_F X = I_W ⊗ g` (`simX`, `pubShort_simX`).
Its rows are indexed by the **short** coordinates `PIdx` of C's box sampler only (the `V_i` live
on the short columns of `L` and the last `2τ` columns), i.e. `X` has zero rows on the gadget
coordinates `ZIdx`, so

* `T_sim z = X · gadDec(M_F (0, z) − (I_W ⊗ g) z)` (`simTrap`) is a good trapdoor for C's box
  sampler (`simTrap_good`), and by `keyLaw_eq_of_good` the keys it gives have the law of the
  real keys (`keyLaw_real_eq_sim`) and the ideal law (`keyLaw_sim_eq_ideal`), when the boxes
  cover both shifts;
* coefficient bounds (`matBnd_vRounds`, `rowBnd_simTrap`): `‖V_{j·a}‖ ≤ D ‖V_j‖ + 1`, hence
  `‖X‖ ≤ (D · + 1)^[b] max(B_R̂, 1)` and `‖T_sim z‖ ≤ W τ n ‖X‖`.
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix

variable {R : Type*} [CommRing R] {S : Setting R} {Wb J Pos : Type*} [Fintype Wb] [Fintype J]
  [DecidableEq J] (M : HelperMap S J) (Ab : Wb → R) (H1 : J → Col S.τ → R)

/-- `G̃⁻¹(Y)`: `g⁻¹(Y)` padded with zero rows, so that `G⁽¹⁾ G̃⁻¹(Y) = Y`. -/
def ginvTop (Y : Col S.τ → R) : Matrix (Col S.τ) (Col S.τ) R :=
  Matrix.of fun ri c => if ri.1 = 0 then S.D.d (Y c) ri.2 else 0

theorem G0_vecMul_ginvTop (Y : Col S.τ → R) : S.G 0 ᵥ* ginvTop Y = Y := by
  funext c
  simp only [Matrix.vecMul, dotProduct, ginvTop, Matrix.of_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, G_apply]
  simp [S.D.recompose]

/-- A block of columns of the right-hand side of `M_F`: its part on the short columns of `L`, and
its part on the last `2τ` columns. -/
abbrev VMat (Wb J : Type*) (S : Setting R) := SimMat Wb J S × Matrix (Col S.τ) (Col S.τ) R

/-- `M_F V = L V_L + (δ₁ᵀ ⊗ A_F⁽¹⁾) V_last`. -/
def mfMul (AF : Matrix (Fin 2) (Col S.τ) R) (V : VMat Wb J S) : Matrix (Fin S.E.W) (Col S.τ) R :=
  simL M Ab H1 * V.1 + rowE S.row0 (AF 0) * V.2

/-- `V₁ = (−R̂_F; I_{2τ})`. -/
def vOne (Rh : SimMat Wb J S) : VMat Wb J S := (-Rh, 1)

/-- `V_{j·a} = V_j G̃⁻¹(σ_j(H_a⁽¹⁾)) − J̃_{η_{j,a}}`. -/
def vStep (j : Fin S.E.W) (a : J) (V : VMat Wb J S) : VMat Wb J S :=
  (V.1 * ginvTop (S.E.σ (S.idx j) ∘ H1 a) - jη j a, V.2 * ginvTop (S.E.σ (S.idx j) ∘ H1 a))

omit [DecidableEq J] in
/-- **The row indexed by `1`**: `M_F V₁ = δ₁ᵀ ⊗ G⁽¹⁾` when `F(x*) = 1`. -/
theorem mfMul_vOne {AF : Matrix (Fin 2) (Col S.τ) R} {Rh : SimMat Wb J S}
    (h : SimForm M Ab H1 S.row0 S.row0 AF 1 Rh) :
    mfMul M Ab H1 AF (vOne Rh) = rowE S.row0 (S.G 0) := by
  unfold mfMul vOne SimForm at *
  rw [Matrix.mul_neg, ← h, Matrix.mul_one, one_smul]
  abel

/-- **Moving the gadget from row `j` to row `j · a`.** -/
theorem mfMul_vStep (AF : Matrix (Fin 2) (Col S.τ) R) (j : Fin S.E.W) (a : J) {V : VMat Wb J S}
    (h : mfMul M Ab H1 AF V = rowE j (S.G 0)) :
    mfMul M Ab H1 AF (vStep H1 j a V) = rowE (M.mulRow j a) (S.G 0) := by
  set Y := S.E.σ (S.idx j) ∘ H1 a
  have h' := congrArg (· * ginvTop Y) h
  simp only [mfMul, Matrix.add_mul, Matrix.mul_assoc] at h'
  rw [rowE_mul j, G0_vecMul_ginvTop] at h'
  unfold mfMul vStep
  simp only
  rw [Matrix.mul_sub, simL_mul_jη]
  calc _ = (simL M Ab H1 * (V.1 * ginvTop Y) + rowE S.row0 (AF 0) * (V.2 * ginvTop Y)) - rowE j Y +
        rowE (M.mulRow j a) (S.G 0) := by abel
    _ = _ := by rw [h', sub_self, zero_add]

/-- The matrices `V_j`, `j < 2^t`, after `t ≤ b` rounds along the binary basis. -/
def vRounds (AF : Matrix (Fin 2) (Col S.τ) R) (Rh : SimMat Wb J S) :
    (t : ℕ) → t ≤ S.b → ℕ → VMat Wb J S
  | 0, _, _ => vOne Rh
  | t + 1, ht, j =>
    if j < 2 ^ t then vRounds AF Rh t (Nat.le_of_succ_le ht) j
    else vStep H1 (Fin.ofNat S.E.W (j - 2 ^ t)) (M.fwd ⟨t, ht⟩)
      (vRounds AF Rh t (Nat.le_of_succ_le ht) (j - 2 ^ t))

omit [Fintype Wb] [Fintype J] [DecidableEq J] in
theorem mulRow_ofNat_fwd {t : ℕ} (ht : t + 1 ≤ S.b) {j : ℕ} (hj : j < 2 ^ t) :
    M.mulRow (Fin.ofNat S.E.W j) (M.fwd ⟨t, ht⟩) = Fin.ofNat S.E.W (j + 2 ^ t) := by
  have hW : 2 ^ (t + 1) ≤ S.E.W := by rw [S.W_eq]; exact Nat.pow_le_pow_right (by norm_num) ht
  have hjW : j < S.E.W := by rw [pow_succ] at hW; omega
  ext
  rw [mulRow_eq, rot_val, M.je_fwd]
  simp [Nat.mod_eq_of_lt hjW]

/-- **All rows**: `M_F V_j = δ_jᵀ ⊗ G⁽¹⁾` for every `j < 2^t`. -/
theorem mfMul_vRounds {AF : Matrix (Fin 2) (Col S.τ) R} {Rh : SimMat Wb J S}
    (h : SimForm M Ab H1 S.row0 S.row0 AF 1 Rh) :
    ∀ t (ht : t ≤ S.b), ∀ j < 2 ^ t,
      mfMul M Ab H1 AF (vRounds M H1 AF Rh t ht j) = rowE (Fin.ofNat S.E.W j) (S.G 0) := by
  intro t
  induction t with
  | zero =>
    intro _ j hj
    have hj0 : j = 0 := by omega
    subst hj0
    rw [vRounds, mfMul_vOne M Ab H1 h]
    congr 1
  | succ t ih =>
    intro ht j hj
    simp only [vRounds]
    split_ifs with hjt
    · exact ih _ j hjt
    · have hj' : j - 2 ^ t < 2 ^ t := by rw [pow_succ] at hj; omega
      rw [mfMul_vStep M Ab H1 AF _ _ (ih _ _ hj'), mulRow_ofNat_fwd M ht hj',
        show j - 2 ^ t + 2 ^ t = j by omega]

/-! ### The trapdoor `X` and `T_sim` -/

/-- A short vector from its parts on the short columns of `L` and on the last `2τ` columns. -/
def pOf (v : LCol Wb J S.τ S.E.W → R) (u : Col S.τ → R) : PIdx Wb J S.τ S.E.W → R
  | .inl q => v (.inl q)
  | .inr (.inl q) => v (.inr q)
  | .inr (.inr c) => u c

/-- **The gadget trapdoor `X` of Lemma 11**: the first `τ` columns of the `V_i`, on the short
coordinates. -/
def simX (AF : Matrix (Fin 2) (Col S.τ) R) (Rh : SimMat Wb J S) :
    Matrix (PIdx Wb J S.τ S.E.W) (ZIdx S.τ S.E.W) R :=
  Matrix.of fun p ic =>
    pOf (fun ℓ => (vRounds M H1 AF Rh S.b le_rfl ic.1).1 ℓ (0, ic.2))
      (fun r => (vRounds M H1 AF Rh S.b le_rfl ic.1).2 r (0, ic.2)) p

/-- **`T_sim z = X · gadDec(M_F (0, z) − (I_W ⊗ g) z)`**. -/
def simTrap (mpk : MPK S Wb J Pos) (F : BP Pos) (Rh : SimMat Wb J S) (z : ZIdx S.τ S.E.W → R) :
    PIdx Wb J S.τ S.E.W → R :=
  simX M (h1Of mpk) (keyPK M mpk F) Rh *ᵥ gadDec (pubZ M mpk F z - gadZ z)

omit [DecidableEq J] in
/-- **`M_F` on a short vector**: `M_F (pOf v u, 0) = L v + (δ₁ᵀ ⊗ A_F⁽¹⁾) u`. -/
theorem pubShort_pOf (mpk : MPK S Wb J Pos) (F : BP Pos) (v : LCol Wb J S.τ S.E.W → R)
    (u : Col S.τ → R) :
    pubShort M mpk F (pOf v u) =
      simL M (abarOf mpk) (h1Of mpk) *ᵥ v + rowE S.row0 (keyPK M mpk F 0) *ᵥ u := by
  funext i'
  simp only [pubShort, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Pi.add_apply, assemble, pOf, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, add_zero]
  simp only [keyMat, simL, rowE, Matrix.of_apply, abarOf, h1Of]
  ring

omit [DecidableEq J] in
/-- `M_F (X y, 0) = Σ_col y_col M_F (X_col, 0)`. -/
theorem pubShort_mulVec (mpk : MPK S Wb J Pos) (F : BP Pos)
    (X : Matrix (PIdx Wb J S.τ S.E.W) (ZIdx S.τ S.E.W) R) (y : ZIdx S.τ S.E.W → R) (i' : Fin S.E.W) :
    pubShort M mpk F (X *ᵥ y) i' = ∑ col, pubShort M mpk F (fun p => X p col) i' * y col := by
  have ha : ∀ k, assemble (X *ᵥ y) 0 k = ∑ col, assemble (fun p => X p col) 0 k * y col := by
    intro k
    rcases k with ⟨i, w | c⟩ | q <;> simp [assemble, Matrix.mulVec, dotProduct]
  simp only [pubShort, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mulVec, dotProduct] at ha ⊢
  simp only [ha, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **Lemma 11**: `M_F X = I_W ⊗ g`, for `F(x*) = 1` and `R̂_F` with
`δ₁ᵀ ⊗ A_F⁽¹⁾ − δ₁ᵀ ⊗ G⁽¹⁾ = L R̂_F`. -/
theorem pubShort_simX (mpk : MPK S Wb J Pos) (F : BP Pos) {Rh : SimMat Wb J S}
    (h : SimForm M (abarOf mpk) (h1Of mpk) S.row0 S.row0 (keyPK M mpk F) 1 Rh)
    (ic : ZIdx S.τ S.E.W) :
    pubShort M mpk F (fun p => simX M (h1Of mpk) (keyPK M mpk F) Rh p ic) =
      fun i' => if i' = ic.1 then S.D.g ic.2 else 0 := by
  have hV := mfMul_vRounds M (abarOf mpk) (h1Of mpk) h S.b le_rfl ic.1
    (by rw [← S.W_eq]; exact ic.1.2)
  have hic : Fin.ofNat S.E.W (ic.1 : ℕ) = ic.1 := by ext; simp
  rw [hic] at hV
  funext i'
  have := congrFun (congrFun hV i') (0, ic.2)
  simp only [simX, Matrix.of_apply]
  rw [pubShort_pOf]
  simp only [mfMul, Matrix.add_apply, Matrix.mul_apply] at this
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct]
  rw [this]
  simp [rowE, G_apply]

/-- **`T_sim` is a good trapdoor** for C's box sampler. -/
theorem simTrap_good (mpk : MPK S Wb J Pos) (F : BP Pos) {Rh : SimMat Wb J S}
    (h : SimForm M (abarOf mpk) (h1Of mpk) S.row0 S.row0 (keyPK M mpk F) 1 Rh) :
    GoodTrap M mpk F (simTrap M mpk F Rh) := by
  intro z
  have key : pubShort M mpk F (simTrap M mpk F Rh z) = pubZ M mpk F z - gadZ z := by
    funext i'
    unfold simTrap
    rw [pubShort_mulVec]
    simp only [pubShort_simX M mpk F h, ite_mul, zero_mul]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single i' (fun b _ hb => by simp [Ne.symm hb])
      (by simp)]
    simp only [ite_true]
    conv_rhs => rw [← gadZ_gadDec (pubZ M mpk F z - gadZ z)]
    rfl
  rw [key, sub_add_cancel]

/-! ### Keys -/

variable [DecidableEq R] (Big Small : Finset (PIdx Wb J S.τ S.E.W → R)) (hBig : Big.Nonempty)
  (dec : (Fin S.E.W → R) → ZIdx S.τ S.E.W → R)

/-- **Hybrid H3's exactness**: the keys of KeyGen (trapdoor `T` of `B⁽¹⁾`) and the keys of the
gadget trapdoor of Lemma 11 have the same law, when the boxes cover both shifts. -/
theorem keyLaw_real_eq_sim (hdec : ∀ y, gadZ (dec y) = y) (mpk : MPK S Wb J Pos) (F : BP Pos)
    (T : Matrix Wb (Fin S.τ) R) (hT : TrapOK mpk T) {Rh : SimMat Wb J S}
    (h : SimForm M (abarOf mpk) (h1Of mpk) S.row0 S.row0 (keyPK M mpk F) 1 Rh)
    (hcov : ∀ x ∈ Small, ∀ y, x + realTrap T (dec y) ∈ Big)
    (hcov' : ∀ x ∈ Small, ∀ y, x + simTrap M mpk F Rh (dec y) ∈ Big) :
    keyLaw Big Small hBig dec M mpk F (realTrap T) = keyLaw Big Small hBig dec M mpk F (simTrap M mpk F Rh) :=
  keyLaw_eq_of_good Big Small hBig dec hdec M mpk F _ _ (realTrap_good M mpk F T hT)
    (simTrap_good M mpk F h) hcov hcov'

/-- **The simulated keys have the ideal law** (a function of `mpk` and `F` only). -/
theorem keyLaw_sim_eq_ideal (hdec : ∀ y, gadZ (dec y) = y) (mpk : MPK S Wb J Pos) (F : BP Pos)
    {Rh : SimMat Wb J S} (h : SimForm M (abarOf mpk) (h1Of mpk) S.row0 S.row0 (keyPK M mpk F) 1 Rh)
    (hcov : ∀ x ∈ Small, ∀ y, x + simTrap M mpk F Rh (dec y) ∈ Big) :
    keyLaw Big Small hBig dec M mpk F (simTrap M mpk F Rh) = idealKeyLaw Big Small hBig dec M mpk F :=
  keyLaw_eq_ideal Big Small hBig dec hdec M mpk F _ (simTrap_good M mpk F h) hcov

/-! ### Coefficient bounds (proof of Lemma 11) -/

section Bounds

variable {N : NormSpec S}

omit [Fintype Wb] [Fintype J] [DecidableEq J] [DecidableEq R] in
theorem matBnd_ginvTop (Y : Col S.τ → R) : MatBnd N (ginvTop Y) 1 := by
  intro ri c
  simp only [ginvTop, Matrix.of_apply]
  split_ifs
  · exact N.nrm_digit _ _
  · simp [N.nrm_zero]

omit [Fintype Wb] [Fintype J] [DecidableEq J] [DecidableEq R] in
/-- A product with a matrix of digits multiplies the bound by `D = 2τn`. -/
theorem matBnd_mul_digits {ι : Type*} {X : Matrix ι (Col S.τ) R} {E : ℕ} (hX : MatBnd N X E)
    {Y : Matrix (Col S.τ) (Col S.τ) R} (hY : MatBnd N Y 1) : MatBnd N (X * Y) (S.gfac * E) := by
  intro ℓ c
  rw [Matrix.mul_apply]
  refine (N.nrm_sum_le _ _ (S.E.n * E) fun ri _ => ?_).trans (le_of_eq ?_)
  · refine (N.nrm_mul _ _).trans ?_
    calc S.E.n * N.nrm (X ℓ ri) * N.nrm (Y ri c) ≤ S.E.n * E * 1 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (hX ℓ ri)) (hY ri c)
      _ = S.E.n * E := mul_one _
  · rw [Finset.card_univ, card_col]; ring

/-- Both parts of `V` bounded by `E`. -/
def VBnd (V : VMat Wb J S) (E : ℕ) : Prop := MatBnd N V.1 E ∧ MatBnd N V.2 E

/-- The bound after one step: `D E + 1`. -/
def vBound (S : Setting R) (E : ℕ) : ℕ := S.gfac * E + 1

omit [Fintype Wb] [Fintype J] [DecidableEq J] [DecidableEq R] in
theorem vBnd_vOne (h1 : N.nrm 1 ≤ 1) {Rh : SimMat Wb J S} {B : ℕ} (hR : MatBnd N Rh B) :
    VBnd (N := N) (vOne Rh) (max B 1) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp only [vOne, Matrix.neg_apply, N.nrm_neg]
    exact (hR i j).trans (le_max_left _ _)
  · simp only [vOne, Matrix.one_apply]
    split_ifs
    · exact h1.trans (le_max_right _ _)
    · simp [N.nrm_zero]

omit [Fintype Wb] [Fintype J] [DecidableEq R] in
theorem vBnd_vStep (h1 : N.nrm 1 ≤ 1) (j : Fin S.E.W) (a : J) {V : VMat Wb J S} {E : ℕ}
    (hV : VBnd (N := N) V E) : VBnd (N := N) (vStep H1 j a V) (vBound S E) := by
  refine ⟨fun i c => ?_, fun i c => ?_⟩
  · simp only [vStep, Matrix.sub_apply]
    exact (N.nrm_sub _ _).trans (Nat.add_le_add (matBnd_mul_digits hV.1 (matBnd_ginvTop _) i c)
      (matBnd_jη h1 j a i c))
  · simp only [vStep]
    exact (matBnd_mul_digits hV.2 (matBnd_ginvTop _) i c).trans (Nat.le_succ _)

omit [Fintype Wb] [Fintype J] [DecidableEq R] in
theorem vBnd_vRounds (h1 : N.nrm 1 ≤ 1) (hD : 1 ≤ S.gfac) (AF : Matrix (Fin 2) (Col S.τ) R)
    {Rh : SimMat Wb J S} {B : ℕ} (hR : MatBnd N Rh B) :
    ∀ t (ht : t ≤ S.b) j, VBnd (N := N) (vRounds M H1 AF Rh t ht j) ((vBound S)^[t] (max B 1)) := by
  have hmono : ∀ E t, (vBound S)^[t] E ≤ (vBound S)^[t + 1] E := by
    intro E t
    rw [Function.iterate_succ_apply']
    generalize (vBound S)^[t] E = Y
    unfold vBound
    have := Nat.le_mul_of_pos_left Y hD
    omega
  intro t
  induction t with
  | zero => intro _ j; exact vBnd_vOne h1 hR
  | succ t ih =>
    intro ht j
    simp only [vRounds]
    split_ifs
    · obtain ⟨h₁, h₂⟩ := ih (Nat.le_of_succ_le ht) j
      exact ⟨matBnd_mono h₁ (hmono _ _), matBnd_mono h₂ (hmono _ _)⟩
    · rw [Function.iterate_succ_apply']
      exact vBnd_vStep H1 h1 _ _ (ih _ _)

omit [Fintype Wb] [Fintype J] [DecidableEq R] in
/-- **The bound of `X`**: `(D · + 1)^[b] max(B_R̂, 1)`. -/
theorem matBnd_simX (h1 : N.nrm 1 ≤ 1) (hD : 1 ≤ S.gfac) (AF : Matrix (Fin 2) (Col S.τ) R)
    {Rh : SimMat Wb J S} {B : ℕ} (hR : MatBnd N Rh B) :
    MatBnd N (simX M H1 AF Rh) ((vBound S)^[S.b] (max B 1)) := by
  intro p ic
  obtain ⟨h₁, h₂⟩ := vBnd_vRounds M H1 h1 hD AF hR S.b le_rfl ic.1
  rcases p with q | q | c
  · exact h₁ _ _
  · exact h₁ _ _
  · exact h₂ _ _

omit [DecidableEq R] in
/-- **The bound of `T_sim z`**: every entry is at most `W τ n ‖X‖`, for every `z`. -/
theorem rowBnd_simTrap (h1 : N.nrm 1 ≤ 1) (hD : 1 ≤ S.gfac) (mpk : MPK S Wb J Pos) (F : BP Pos)
    {Rh : SimMat Wb J S} {B : ℕ} (hR : MatBnd N Rh B) (z : ZIdx S.τ S.E.W → R) :
    RowBnd N (simTrap M mpk F Rh z) (S.E.W * S.τ * (S.E.n * (vBound S)^[S.b] (max B 1))) := by
  intro p
  simp only [simTrap, Matrix.mulVec, dotProduct]
  refine (N.nrm_sum_le _ _ (S.E.n * (vBound S)^[S.b] (max B 1)) fun ic _ => ?_).trans (le_of_eq ?_)
  · refine (N.nrm_mul _ _).trans ?_
    calc S.E.n * N.nrm (simX M (h1Of mpk) (keyPK M mpk F) Rh p ic) * N.nrm (gadDec _ ic)
        ≤ S.E.n * (vBound S)^[S.b] (max B 1) * 1 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (matBnd_simX M _ h1 hD _ hR p ic))
            (N.nrm_digit _ _)
      _ = _ := mul_one _
  · simp [Finset.card_univ]

omit [Fintype Wb] [Fintype J] [DecidableEq J] [DecidableEq R] in
/-- Closed form: `(D · + 1)^[t] E + 1 ≤ D^t (E + 1)` for `D ≥ 2`. -/
theorem vBound_iterate_le (hD : 2 ≤ S.gfac) (E t : ℕ) :
    (vBound S)^[t] E + 1 ≤ S.gfac ^ t * (E + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    generalize (vBound S)^[t] E = Y at ih ⊢
    unfold vBound
    calc S.gfac * Y + 1 + 1 ≤ S.gfac * (Y + 1) := by nlinarith
      _ ≤ S.gfac * (S.gfac ^ t * (E + 1)) := Nat.mul_le_mul_left _ ih
      _ = S.gfac ^ t * S.gfac * (E + 1) := by ring

end Bounds

end AdvancedEncryption.ExpLUT
