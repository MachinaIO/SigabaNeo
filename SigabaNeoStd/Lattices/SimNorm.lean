import SigabaNeoStd.Lattices.Homomorphic.SLPSim

/-!
# The norm of simulation trapdoors

The simulation trapdoors of `EvalF` (`evalSim`, for circuits) and of its program version
(`slpSim`) evolve by `NAND(a, b) ↦ −(W_a · G⁻¹(A_b) + a(x) W_b)`: every gate acts on the left of
`W` by the same recursion as the error of an encoding. Row by row, a simulation trapdoor *is* an
error of `EvalFX` (`rowOf_slpSim`, `rowOf_evalSim`), so the noise analysis bounds it: with binary
input trapdoors (`W_j`, `Rᵢ` with entries of norm at most `E`) and `0/1` inputs, every row of
`W_w` has norm at most `slpBound (|W| N) E` (`rnorm_rowOf_slpSim_le`) and every row of `W_f` at
most `errBound (|W| N) E f` (`rnorm_rowOf_evalSim_le`). A matrix with rows of norm at most `ρ`
maps a vector with coefficients at most `D` to coefficients at most `|W| N ρ D`
(`cnorm_mulVec_le`).
-/

namespace SigabaNeo.Lattices

open Matrix Cslib

variable {R : Type*} [CommRing R] {r W m : Type*} [Fintype W]

/-- The row `i` of a matrix, as a `1 × W` matrix. -/
def rowOf (M : Matrix m W R) (i : m) : Matrix (Fin 1) W R := Matrix.of fun _ c => M i c

omit [CommRing R] [Fintype W] in
theorem rowOf_apply (M : Matrix m W R) (i : m) (a : Fin 1) (c : W) : rowOf M i a c = M i c := rfl

theorem rowOf_mul {W' : Type*} (M : Matrix m W R) (X : Matrix W W' R) (i : m) :
    rowOf (M * X) i = rowOf M i * X := by
  ext a c; simp [rowOf, Matrix.mul_apply]

omit [Fintype W] in
theorem rowOf_add (M M' : Matrix m W R) (i : m) : rowOf (M + M') i = rowOf M i + rowOf M' i := by
  ext a c; simp [rowOf]

omit [Fintype W] in
theorem rowOf_neg (M : Matrix m W R) (i : m) : rowOf (-M) i = -rowOf M i := by
  ext a c; simp [rowOf]

omit [Fintype W] in
theorem rowOf_smul (x : R) (M : Matrix m W R) (i : m) : rowOf (x • M) i = x • rowOf M i := by
  ext a c; simp [rowOf]

omit [Fintype W] in
theorem rowOf_zero (i : m) : rowOf (0 : Matrix m W R) i = 0 := by
  ext a c; simp [rowOf]

variable [Fintype r] (Γ : GadgetMatrix R r W) {ι : Type*}

omit [Fintype r] in
/-- **A row of the program trapdoor is an error of `EvalFX`.** -/
theorem rowOf_slpSim (A : ι → Matrix r W R) (Wm : ι → Matrix m W R) (x : ι → R) (p : SLP ι)
    (w : Wire ι) (i : m) :
    rowOf (slpSim Γ A Wm x p w) i = slpEnc Γ A x (fun j => rowOf (Wm j) i) p w := by
  have h := SLP.valueOf_map (fun j => (A j, Wm j, x j)) (Γ.G, 0, 1) (simStep Γ)
    (fun j => (A j, x j, rowOf (Wm j) i)) (Γ.G, 1, 0) (encStep Γ)
    (fun u => (u.1, u.2.2, rowOf u.2.1 i)) (fun _ => rfl) (by simp [rowOf_zero])
    (fun u v => by simp [simStep, encStep, rowOf_neg, rowOf_add, rowOf_mul, rowOf_smul]) p w
  exact congrArg (fun t => t.2.2) h

omit [Fintype r] in
/-- **A row of the circuit trapdoor is an error of `EvalFX`.** -/
theorem rowOf_evalSim (A : ι → Matrix r W R) (x : ι → R) (Wm : ι → Matrix m W R) (f : Circuit ι)
    (i : m) : rowOf (evalSim Γ A x Wm f) i = evalErr Γ A x (fun j => rowOf (Wm j) i) f := by
  induction f with
  | input j => rfl
  | one => exact rowOf_zero i
  | nand a b iha ihb =>
    simp only [evalSim, evalErr, rowOf_neg, rowOf_add, rowOf_mul, rowOf_smul, iha, ihb]

section Norm

variable {N q : ℕ} [NeZero q] {r : Type*}

omit [NeZero q] in
theorem rnorm_rowOf_le (M : Matrix m W (Negacyclic (ZMod q) N)) (i : m) (E : ℕ)
    (h : ∀ c, cnorm (M i c) ≤ E) : rnorm (rowOf M i) ≤ E :=
  (rnorm_le_iff _ _).mpr h

/-- **The norm of the program trapdoor**: with `0/1` inputs and input trapdoors with entries of
norm at most `E`, every row of `W_w` has norm at most `slpBound (|W| N) E`. -/
theorem rnorm_rowOf_slpSim_le (Γ : GadgetMatrix (Negacyclic (ZMod q) N) r W)
    (hΓ : ∀ A c c', cnorm (Γ.ginv A c c') ≤ 1) (A : ι → Matrix r W (Negacyclic (ZMod q) N))
    (Wm : ι → Matrix m W (Negacyclic (ZMod q) N)) (x : ι → Negacyclic (ZMod q) N)
    (hx : ∀ j, x j = 0 ∨ x j = 1) (E : ℕ) (hW : ∀ j i c, cnorm (Wm j i c) ≤ E) (p : SLP ι)
    (w : Wire ι) (i : m) :
    rnorm (rowOf (slpSim Γ A Wm x p w) i) ≤ slpBound (Fintype.card W * N) E p w := by
  rw [rowOf_slpSim]
  exact slp_enc_noise Γ hΓ A x hx _ E (fun j => rnorm_rowOf_le _ _ _ (hW j i)) p w

/-- **The norm of the circuit trapdoor**: with `0/1` inputs and input trapdoors with entries of
norm at most `E`, every row of `W_f` has norm at most `errBound (|W| N) E f`. -/
theorem rnorm_rowOf_evalSim_le (Γ : GadgetMatrix (Negacyclic (ZMod q) N) r W)
    (hΓ : ∀ A c c', cnorm (Γ.ginv A c c') ≤ 1) (A : ι → Matrix r W (Negacyclic (ZMod q) N))
    (x : ι → Negacyclic (ZMod q) N) (hx : ∀ j, x j = 0 ∨ x j = 1)
    (Wm : ι → Matrix m W (Negacyclic (ZMod q) N)) (E : ℕ) (hW : ∀ j i c, cnorm (Wm j i c) ≤ E)
    (f : Circuit ι) (i : m) :
    rnorm (rowOf (evalSim Γ A x Wm f) i) ≤ errBound (Fintype.card W * N) E f := by
  rw [rowOf_evalSim]
  exact rnorm_evalErr_le Γ hΓ A x hx _ E (fun j => rnorm_rowOf_le _ _ _ (hW j i)) f

/-- **A matrix times a vector**: rows of norm at most `ρ` and coefficients at most `D` give
coefficients at most `|W| N ρ D`. -/
theorem cnorm_mulVec_le (M : Matrix m W (Negacyclic (ZMod q) N)) (z : W → Negacyclic (ZMod q) N)
    (ρ D : ℕ) (hM : ∀ i, rnorm (rowOf M i) ≤ ρ) (hz : ∀ c, cnorm (z c) ≤ D) (i : m) :
    cnorm ((M *ᵥ z) i) ≤ Fintype.card W * N * ρ * D := by
  simp only [Matrix.mulVec, dotProduct]
  refine (cnorm_sum_le _ _).trans ?_
  calc ∑ c, cnorm (M i c * z c) ≤ ∑ _c : W, N * ρ * D := Finset.sum_le_sum fun c _ =>
        (cnorm_mul_le _ _).trans (Nat.mul_le_mul (Nat.mul_le_mul_left _
          ((cnorm_le_rnorm (rowOf M i) c).trans (hM i))) (hz c))
    _ = Fintype.card W * N * ρ * D := by simp [mul_assoc]

end Norm

end SigabaNeo.Lattices
