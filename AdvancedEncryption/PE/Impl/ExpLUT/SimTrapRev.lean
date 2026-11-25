import PE.Impl.ExpLUT.SimTrap

/-!
# `T_sim z` without the matrices `V_i` (package G2c)

Lemma 11's trapdoor is `T_sim z = X u` with `u = gadDec(M_F (0, z) − (I_W ⊗ g) z)` and `X` the
first `τ` columns of the `W` matrices `V_i` (`vRounds`), each with `|LCol| · 2τ` entries. The
reduction never needs `X` itself: since `V_{j + 2^t} = V_j G̃_{j,t} − J̃_{η_{j, g_t}}`
(`vStep`), the sum `Σ_j V_j y_j` is computed **backwards over the rounds on vectors**:

* `bStep t y`: `y_j ← y_j + G̃⁻¹(σ_j(H1_{g_t})) y_{j + 2^t}` for `j < 2^t` (round `t` folded into
  the rows below `2^t`);
* `eStep t y = Σ_{j<2^t} J̃_{η_{j, g_t}} y_{j+2^t}` (the vectors `y_{j + 2^t}` placed in the
  blocks `η_{j, g_t}`);
* `revW t y`: rounds `t − 1, …, 0`, returning the folded vector `w = y_0` and the sum `e` of the
  `eStep`s.

**`sum_vApp_vRounds`**: `Σ_{j<2^t} V_j y_j = (−R̂ w − e, w)`, hence **`simX_mulVec`**:
`X u = pOf(−R̂ w − e, w)` for `(w, e) = revW b (liftU u)`, and **`simTrap_eq_rev`**:
`T_sim z = pOf(−R̂_F w − e, w)`. So a key query of the reduction costs one matrix–vector product
`R̂_F w` and `W` products `2τ × 2τ` by vectors besides the computation of `R̂_F`.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix

variable {R : Type*} [CommRing R] {S : Setting R} {Wb J Pos : Type*} [Fintype Wb] [Fintype J]
  [DecidableEq J] (M : HelperMap S J) (H1 : J → Col S.τ → R)

/-- A pair `V = (V_L, V_last)` applied to a vector. -/
def vApp (V : VMat Wb J S) (y : Col S.τ → R) : (LCol Wb J S.τ S.E.W → R) × (Col S.τ → R) :=
  (V.1 *ᵥ y, V.2 *ᵥ y)

/-- `G̃⁻¹(σ_j(H1_{g_t}))`, the matrix of round `t` at the row `j`. -/
def gRound (t : ℕ) (ht : t < S.b) (j : ℕ) : Matrix (Col S.τ) (Col S.τ) R :=
  ginvTop (S.E.σ (S.idx (Fin.ofNat S.E.W j : ℕ)) ∘ H1 (M.fwd ⟨t, ht⟩))

/-- **The backward step of round `t`**: `y_j + G̃⁻¹(σ_j(H1_{g_t})) y_{j + 2^t}`. -/
def bStep (t : ℕ) (ht : t < S.b) (y : ℕ → Col S.τ → R) : ℕ → Col S.τ → R :=
  fun j => y j + gRound M H1 t ht j *ᵥ y (j + 2 ^ t)

/-- **The `η` part of round `t`**: `Σ_{j<2^t} J̃_{η_{j, g_t}} y_{j+2^t}`. -/
def eStep (t : ℕ) (ht : t < S.b) (y : ℕ → Col S.τ → R) : LCol Wb J S.τ S.E.W → R :=
  ∑ j ∈ Finset.range (2 ^ t), jη (Wb := Wb) (Fin.ofNat S.E.W j) (M.fwd ⟨t, ht⟩) *ᵥ y (j + 2 ^ t)

/-- **The backward pass**: rounds `t − 1, …, 0`; the folded vector and the sum of the `η` parts. -/
def revW : (t : ℕ) → t ≤ S.b → (ℕ → Col S.τ → R) → (Col S.τ → R) × (LCol Wb J S.τ S.E.W → R)
  | 0, _, y => (y 0, 0)
  | t + 1, ht, y =>
    ((revW t (Nat.le_of_succ_le ht) (bStep M H1 t ht y)).1,
      (revW t (Nat.le_of_succ_le ht) (bStep M H1 t ht y)).2 + eStep M t ht y)

omit [DecidableEq J] in
theorem vApp_add (V : VMat Wb J S) (y y' : Col S.τ → R) :
    vApp V (y + y') = vApp V y + vApp V y' := by
  simp [vApp, Matrix.mulVec_add]

theorem vApp_vStep (j : Fin S.E.W) (a : J) (V : VMat Wb J S) (y : Col S.τ → R) :
    vApp (vStep H1 j a V) y =
      vApp V (ginvTop (S.E.σ (S.idx j) ∘ H1 a) *ᵥ y) - (jη j a *ᵥ y, 0) := by
  simp [vApp, vStep, Matrix.sub_mulVec, Matrix.mulVec_mulVec]

/-- **`Σ_{j<2^t} V_j y_j = (−R̂ w − e, w)`** with `(w, e) = revW t y`. -/
theorem sum_vApp_vRounds (AF : Matrix (Fin 2) (Col S.τ) R) (Rh : SimMat Wb J S) :
    ∀ (t : ℕ) (ht : t ≤ S.b) (y : ℕ → Col S.τ → R),
      ∑ j ∈ Finset.range (2 ^ t), vApp (vRounds M H1 AF Rh t ht j) (y j) =
        (-(Rh *ᵥ (revW (Wb := Wb) M H1 t ht y).1) - (revW M H1 t ht y).2, (revW (Wb := Wb) M H1 t ht y).1) := by
  intro t
  induction t with
  | zero =>
    intro _ y
    simp [vRounds, vOne, vApp, revW, Matrix.neg_mulVec]
  | succ t ih =>
    intro ht y
    rw [pow_succ, mul_two, Finset.sum_range_add]
    have h1 : ∀ j ∈ Finset.range (2 ^ t), vApp (vRounds M H1 AF Rh (t + 1) ht j) (y j) =
        vApp (vRounds M H1 AF Rh t (Nat.le_of_succ_le ht) j) (y j) := by
      intro j hj
      simp only [vRounds, Finset.mem_range.mp hj, ↓reduceIte]
    have h2 : ∀ j ∈ Finset.range (2 ^ t),
        vApp (vRounds M H1 AF Rh (t + 1) ht (2 ^ t + j)) (y (2 ^ t + j)) =
        vApp (vRounds M H1 AF Rh t (Nat.le_of_succ_le ht) j) (gRound M H1 t ht j *ᵥ y (j + 2 ^ t)) -
          (jη (Fin.ofNat S.E.W j) (M.fwd ⟨t, ht⟩) *ᵥ y (j + 2 ^ t), 0) := by
      intro j _
      simp only [vRounds, show ¬ (2 ^ t + j < 2 ^ t) by omega, ↓reduceIte]
      rw [show 2 ^ t + j - 2 ^ t = j by omega, vApp_vStep,
        add_comm (2 ^ t) j]
      rfl
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_sub_distrib, ← add_sub_assoc,
      ← Finset.sum_add_distrib]
    have h3 : ∀ j ∈ Finset.range (2 ^ t),
        vApp (vRounds M H1 AF Rh t (Nat.le_of_succ_le ht) j) (y j) +
          vApp (vRounds M H1 AF Rh t (Nat.le_of_succ_le ht) j) (gRound M H1 t ht j *ᵥ y (j + 2 ^ t)) =
        vApp (vRounds M H1 AF Rh t (Nat.le_of_succ_le ht) j) (bStep M H1 t ht y j) := by
      intro j _
      rw [← vApp_add]; rfl
    rw [Finset.sum_congr rfl h3, ih (Nat.le_of_succ_le ht) (bStep M H1 t ht y)]
    have he : ∑ j ∈ Finset.range (2 ^ t),
        ((jη (Wb := Wb) (Fin.ofNat S.E.W j) (M.fwd ⟨t, ht⟩) *ᵥ y (j + 2 ^ t),
          (0 : Col S.τ → R)) : (LCol Wb J S.τ S.E.W → R) × (Col S.τ → R)) =
        (eStep M t ht y, 0) := by
      ext : 1
      · rw [Prod.fst_sum]; rfl
      · rw [Prod.snd_sum]; simp
    rw [he]
    simp only [revW, Prod.mk_sub_mk, sub_zero]
    congr 1
    abel

/-! ### `X u` and `T_sim z` -/

/-- The vectors `ũ_j = (u_j, 0) ∈ R^{2τ}` of the rows of `u ∈ R^{W × τ}`. -/
def liftU (u : ZIdx S.τ S.E.W → R) : ℕ → Col S.τ → R :=
  fun j rc => if rc.1 = 0 then u (Fin.ofNat S.E.W j, rc.2) else 0

omit [Fintype Wb] [Fintype J] [DecidableEq J] in
theorem mulVec_liftU {ι : Type*} (A : Matrix ι (Col S.τ) R) (u : ZIdx S.τ S.E.W → R) (j : ℕ)
    (l : ι) : (A *ᵥ liftU u j) l = ∑ c, A l (0, c) * u (Fin.ofNat S.E.W j, c) := by
  simp [Matrix.mulVec, dotProduct, liftU, Fintype.sum_prod_type]

/-- **`X u` from the backward pass**: `simX · u = pOf(−R̂ w − e, w)` with `(w, e) = revW b (liftU u)`;
no `V_i` is formed. -/
theorem simX_mulVec (AF : Matrix (Fin 2) (Col S.τ) R) (Rh : SimMat Wb J S)
    (u : ZIdx S.τ S.E.W → R) :
    simX M H1 AF Rh *ᵥ u =
      pOf (-(Rh *ᵥ (revW (Wb := Wb) M H1 S.b le_rfl (liftU u)).1) - (revW M H1 S.b le_rfl (liftU u)).2)
        (revW (Wb := Wb) M H1 S.b le_rfl (liftU u)).1 := by
  have hs := sum_vApp_vRounds M H1 AF Rh S.b le_rfl (liftU u)
  rw [← S.W_eq] at hs
  have hsum : ∀ (f : ℕ → (LCol Wb J S.τ S.E.W → R) × (Col S.τ → R)),
      ∑ j ∈ Finset.range S.E.W, f j = ∑ i : Fin S.E.W, f i := fun f =>
    (Fin.sum_univ_eq_sum_range f _).symm
  rw [hsum] at hs
  suffices h : simX M H1 AF Rh *ᵥ u =
      pOf (∑ i : Fin S.E.W, vApp (vRounds M H1 AF Rh S.b le_rfl (i : ℕ)) (liftU u (i : ℕ))).1
        (∑ i : Fin S.E.W, vApp (vRounds M H1 AF Rh S.b le_rfl (i : ℕ)) (liftU u (i : ℕ))).2 by
    rw [h, hs]
  funext p
  rcases p with q | q | c
  · simp only [Matrix.mulVec, dotProduct, simX, Matrix.of_apply, pOf, Prod.fst_sum,
      Finset.sum_apply, vApp]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [liftU, Fintype.sum_prod_type]
  · simp only [Matrix.mulVec, dotProduct, simX, Matrix.of_apply, pOf, Prod.fst_sum,
      Finset.sum_apply, vApp]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [liftU, Fintype.sum_prod_type]
  · simp only [Matrix.mulVec, dotProduct, simX, Matrix.of_apply, pOf, Prod.snd_sum,
      Finset.sum_apply, vApp]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [liftU, Fintype.sum_prod_type]

/-- **`T_sim z` from the backward pass** (Lemma 11 without the `V_i`): with
`u = gadDec(M_F (0, z) − (I_W ⊗ g) z)` and `(w, e) = revW b (liftU u)` (over the first rows
`H1 = h1Of mpk` of the helpers), `T_sim z = pOf(−R̂_F w − e, w)`. -/
theorem simTrap_eq_rev (mpk : MPK S Wb J Pos) (F : BP Pos) (Rh : SimMat Wb J S)
    (z : ZIdx S.τ S.E.W → R) :
    simTrap M mpk F Rh z =
      pOf (-(Rh *ᵥ (revW (Wb := Wb) M (h1Of mpk) S.b le_rfl
          (liftU (gadDec (pubZ M mpk F z - gadZ z)))).1) -
          (revW M (h1Of mpk) S.b le_rfl (liftU (gadDec (pubZ M mpk F z - gadZ z)))).2)
        (revW (Wb := Wb) M (h1Of mpk) S.b le_rfl (liftU (gadDec (pubZ M mpk F z - gadZ z)))).1 :=
  simX_mulVec M (h1Of mpk) _ Rh _

end AdvancedEncryption.ExpLUT
