import SigabaNeoStd.Lattices.Homomorphic.Eval
import SigabaNeoStd.Lattices.Homomorphic.Norm
import SigabaNeoStd.Lattices.Homomorphic.BinaryDigits

/-!
# Noise bounds of homomorphic evaluation over `ℤ_q[X]/(X^N + 1)`

For a row `e ∈ R^{1×W}`, `rnorm e` is the largest coefficient norm of its entries. With a gadget
whose decompositions have entries of norm at most `1` (binary digits), a NAND step multiplies the
error of its left input by at most `|W| · N` and adds that of its right input (`rnorm_mul_le`):
the error of `evalErr` on `0/1` inputs is at most `errBound (|W| N) E f`, where every input error
is at most `E` (`rnorm_evalErr_le`). This covers both BGG+ encodings and Ring-GSW ciphertexts.
-/

namespace SigabaNeo.Lattices

open Cslib Matrix

variable {N q : ℕ} {W : Type*} [Fintype W]

/-- The norm of a row: the largest coefficient norm of its entries. -/
def rnorm (e : Matrix (Fin 1) W (Negacyclic (ZMod q) N)) : ℕ :=
  Finset.univ.sup fun c => cnorm (e 0 c)

theorem cnorm_le_rnorm (e : Matrix (Fin 1) W (Negacyclic (ZMod q) N)) (c : W) :
    cnorm (e 0 c) ≤ rnorm e :=
  Finset.le_sup (f := fun c => cnorm (e 0 c)) (Finset.mem_univ c)

theorem rnorm_le_iff (e : Matrix (Fin 1) W (Negacyclic (ZMod q) N)) (B : ℕ) :
    rnorm e ≤ B ↔ ∀ c, cnorm (e 0 c) ≤ B := by
  simp [rnorm, Finset.sup_le_iff]

theorem rnorm_add_le (e f : Matrix (Fin 1) W (Negacyclic (ZMod q) N)) :
    rnorm (e + f) ≤ rnorm e + rnorm f := by
  rw [rnorm_le_iff]; intro c
  exact (cnorm_add_le _ _).trans (Nat.add_le_add (cnorm_le_rnorm e c) (cnorm_le_rnorm f c))

theorem rnorm_neg (e : Matrix (Fin 1) W (Negacyclic (ZMod q) N)) : rnorm (-e) = rnorm e := by
  simp [rnorm, cnorm_neg]

theorem rnorm_sub_le (e f : Matrix (Fin 1) W (Negacyclic (ZMod q) N)) :
    rnorm (e - f) ≤ rnorm e + rnorm f := by
  rw [sub_eq_add_neg]; exact (rnorm_add_le _ _).trans (by rw [rnorm_neg])

theorem rnorm_zero : rnorm (0 : Matrix (Fin 1) W (Negacyclic (ZMod q) N)) = 0 := by
  apply le_antisymm _ (Nat.zero_le _)
  rw [rnorm_le_iff]; intro c; simp [cnorm_zero]

theorem rnorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin 1) W (Negacyclic (ZMod q) N)) :
    rnorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, rnorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rnorm_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (rnorm_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- A `0/1` scalar does not increase the norm. -/
theorem rnorm_smul_le_of_bit (x : Negacyclic (ZMod q) N) (hx : x = 0 ∨ x = 1)
    (e : Matrix (Fin 1) W (Negacyclic (ZMod q) N)) : rnorm (x • e) ≤ rnorm e := by
  rcases hx with rfl | rfl
  · rw [zero_smul, rnorm_zero]; exact Nat.zero_le _
  · rw [one_smul]

variable [NeZero q] {W' : Type*} [Fintype W']

/-- **A row times a matrix** with entries of norm at most `D`: the norm grows by `|W| · N · D`. -/
theorem rnorm_mul_le (e : Matrix (Fin 1) W (Negacyclic (ZMod q) N))
    (M : Matrix W W' (Negacyclic (ZMod q) N)) (D : ℕ) (hM : ∀ c c', cnorm (M c c') ≤ D) :
    rnorm (e * M) ≤ Fintype.card W * N * rnorm e * D := by
  rw [rnorm_le_iff]; intro c'
  simp only [Matrix.mul_apply]
  refine (cnorm_sum_le _ _).trans ?_
  calc ∑ c, cnorm (e 0 c * M c c') ≤ ∑ _c : W, N * rnorm e * D := Finset.sum_le_sum fun c _ =>
        (cnorm_mul_le _ _).trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ (cnorm_le_rnorm e c)) (hM c c'))
    _ = Fintype.card W * N * rnorm e * D := by simp [mul_assoc]

/-- The error bound of a circuit: `E` at the inputs, `0` at `1`, and `WN · E_a + E_b` at a NAND. -/
def errBound {ι : Type*} (WN E : ℕ) : Circuit ι → ℕ
  | .input _ => E
  | .one => 0
  | .nand a b => WN * errBound WN E a + errBound WN E b

/-- On `0/1` inputs, a circuit evaluates to `0/1`. -/
theorem Circuit.eval_bit {ι : Type*} {R : Type*} [CommRing R] (x : ι → R)
    (hx : ∀ i, x i = 0 ∨ x i = 1) (f : Circuit ι) : f.eval x = 0 ∨ f.eval x = 1 := by
  induction f with
  | input i => exact hx i
  | one => exact Or.inr rfl
  | nand a b iha ihb =>
    simp only [Circuit.eval]
    rcases iha with ha | ha <;> rcases ihb with hb | hb <;> simp [ha, hb]

variable {r : Type*}

/-- **The noise of homomorphic evaluation.** With decompositions of norm at most `1`, `0/1` inputs
and input errors of norm at most `E`, the error of `evalErr` is at most `errBound (|W| N) E f`. -/
theorem rnorm_evalErr_le {ι : Type*} (Γ : GadgetMatrix (Negacyclic (ZMod q) N) r W)
    (hΓ : ∀ A c c', cnorm (Γ.ginv A c c') ≤ 1) (M : ι → Matrix r W (Negacyclic (ZMod q) N))
    (x : ι → Negacyclic (ZMod q) N) (hx : ∀ i, x i = 0 ∨ x i = 1)
    (e : ι → Matrix (Fin 1) W (Negacyclic (ZMod q) N)) (E : ℕ) (he : ∀ i, rnorm (e i) ≤ E)
    (f : Circuit ι) : rnorm (evalErr Γ M x e f) ≤ errBound (Fintype.card W * N) E f := by
  induction f with
  | input i => exact he i
  | one => simp [evalErr, errBound, rnorm_zero]
  | nand a b iha ihb =>
    simp only [evalErr, errBound, rnorm_neg]
    refine (rnorm_add_le _ _).trans (Nat.add_le_add ?_ ?_)
    · refine (rnorm_mul_le _ _ 1 (hΓ _)).trans ?_
      rw [mul_one]
      exact Nat.mul_le_mul_left _ iha
    · exact (rnorm_smul_le_of_bit _ (Circuit.eval_bit x hx a) _).trans ihb

/-! ### Binary digits have norm `1` -/

omit [NeZero q] in
theorem cnorm_binaryDigit_le [NeZero q] (a : Negacyclic (ZMod q) N) (i : ℕ) :
    cnorm (binaryDigit a i) ≤ 1 := by
  rw [cnorm_le_iff]; intro j
  rw [coeffs_binaryDigit]
  split_ifs
  · exact zabs_one_le
  · rw [zabs_zero]; exact Nat.zero_le _

/-- The decompositions of a gadget matrix with binary digits have entries of norm at most `1`. -/
theorem cnorm_gadgetOf_binary_ginv_le {k : ℕ} (hk : q ≤ 2 ^ k) {ρ : Type*} [Fintype r]
    [Fintype ρ] [DecidableEq r] [DecidableEq ρ] (ι : r → ρ) (hι : Function.Injective ι)
    (A : Matrix r (ρ × Fin k) (Negacyclic (ZMod q) N)) (c : ρ × Fin k) (col : ρ × Fin k) :
    cnorm ((gadgetOf (binaryDigits N q k hk) ι hι).ginv A c col) ≤ 1 := by
  simp only [gadgetOf, Matrix.of_apply]
  by_cases h : ∃ a, ι a = c.1
  · obtain ⟨a, ha⟩ := h
    rw [Finset.sum_eq_single a]
    · simp only [ha, ↓reduceIte]; exact cnorm_binaryDigit_le _ _
    · intro b _ hb
      have : ι b ≠ c.1 := fun hb' => hb (hι (hb'.trans ha.symm))
      simp [this]
    · simp
  · have : ∀ a, ι a ≠ c.1 := fun a ha => h ⟨a, ha⟩
    simp [this, cnorm_zero]

end SigabaNeo.Lattices
