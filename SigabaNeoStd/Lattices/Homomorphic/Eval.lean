import SigabaNeoStd.Lattices.Homomorphic.Gadget
import SigabaNeoStd.Lattices.Homomorphic.Circuit
import Mathlib.Tactic.Module

/-!
# Homomorphic evaluation: BGG+ encodings and Ring-GSW ciphertexts

One recursion serves both: for a gadget `Γ` and matrices `M i ∈ R^{r × W}`, `evalMat Γ M f` sends
the constant `1` to `G` and `NAND(a, b)` to `G − M_a · G⁻¹(M_b)`.

* **BGG+** (BTVW17 Theorem 3.7, the "key equation"). `evalMat Γ A f` is the public key
  `EvalF(f, A)`, and `evalEnc` evaluates encodings, knowing the inputs `x`: if every
  `cᵢ = s(Aᵢ − xᵢ G) + eᵢ`, then `evalEnc = s(A_f − f(x) G) + e_f` (`bgg_key_relation`), with the
  error `e_f = evalErr` built from the input errors.
* **Ring-GSW** (the FHE of BTVW17 Lemma 3.9). `evalMat Γ Ψ f` is `FHE.Eval(f, Ψ)`. If every
  `t Ψᵢ = xᵢ (t G) + eᵢ`, then `t Ψ_f = f(x) (t G) + e_f` (`gsw_invariant`), with the error
  `gswErr`.
* **Simulation** (BTVW17 §4.2). Public keys `Aᵢ = B Wᵢ + xᵢ G` evaluate to `B W_f + f(x) G`
  (`sim_relation`, with `W_f = evalSim`): the identity behind `Setup*` and `KeyGen*`.
* **Matrix-valued functions** (BTVW17 §4.1). Encodings `c_b` of the bits `y_b` of a matrix
  `Y = ∑_b y_b V_b` combine, through `G⁻¹(V_b)`, into an encoding of `Y` itself
  (`matrix_key_relation`; `matrix_key_relation_bits` for a bit decomposition `MatrixBits`).

The algebra of a NAND step is mxx's `multiplication_core`/`linear_add_core`
(`crates/khe/lean/BggMultiplication.lean`), with one secret.
-/

namespace SigabaNeo.Lattices

open Matrix

variable {R : Type*} [CommRing R] {r W : Type*} [Fintype r] [Fintype W]
  (Γ : GadgetMatrix R r W) {ι : Type*}

/-- `EvalF` / `FHE.Eval`: `1 ↦ G`, `NAND(a, b) ↦ G − M_a · G⁻¹(M_b)`. -/
def evalMat (M : ι → Matrix r W R) : Circuit ι → Matrix r W R
  | .input i => M i
  | .one => Γ.G
  | .nand a b => Γ.G - evalMat M a * Γ.ginv (evalMat M b)

/-- Error recursion shared by both evaluations: `NAND(a, b) ↦ −(e_a · G⁻¹(M_b) + a(x) e_b)`. -/
def evalErr (M : ι → Matrix r W R) (x : ι → R) (e : ι → Matrix (Fin 1) W R) :
    Circuit ι → Matrix (Fin 1) W R
  | .input i => e i
  | .one => 0
  | .nand a b => -(evalErr M x e a * Γ.ginv (evalMat Γ M b) + a.eval x • evalErr M x e b)

/-- `EvalFX` on encodings, knowing the inputs `x`. -/
def evalEnc (A : ι → Matrix r W R) (x : ι → R) (c : ι → Matrix (Fin 1) W R) :
    Circuit ι → Matrix (Fin 1) W R :=
  evalErr Γ A x c

/-- **The BGG+ key relation.** Encodings `cᵢ = s(Aᵢ − xᵢ G) + eᵢ` evaluate to an encoding of
`f(x)` under `EvalF(f, A)`. -/
theorem bgg_key_relation (s : Matrix (Fin 1) r R) (A : ι → Matrix r W R) (x : ι → R)
    (c e : ι → Matrix (Fin 1) W R) (h : ∀ i, c i = s * (A i - x i • Γ.G) + e i)
    (f : Circuit ι) :
    evalEnc Γ A x c f = s * (evalMat Γ A f - f.eval x • Γ.G) + evalErr Γ A x e f := by
  induction f with
  | input i => exact h i
  | one => simp [evalEnc, evalErr, evalMat, Circuit.eval]
  | nand a b iha ihb =>
    simp only [evalEnc] at iha ihb ⊢
    simp only [evalErr, evalMat, Circuit.eval, iha, ihb]
    have hG := Γ.mul_ginv (evalMat Γ A b)
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_assoc, hG, sub_smul, one_smul, smul_add, smul_sub, smul_smul]
    module

/-- **The Ring-GSW invariant.** Ciphertexts with `t Ψᵢ = xᵢ (t G) + eᵢ` evaluate to `Ψ_f` with
`t Ψ_f = f(x) (t G) + e_f`. -/
theorem gsw_invariant (t : Matrix (Fin 1) r R) (Ψ : ι → Matrix r W R) (x : ι → R)
    (e : ι → Matrix (Fin 1) W R) (h : ∀ i, t * Ψ i = x i • (t * Γ.G) + e i)
    (f : Circuit ι) :
    t * evalMat Γ Ψ f = f.eval x • (t * Γ.G) + evalErr Γ Ψ x e f := by
  induction f with
  | input i => exact h i
  | one => simp [evalErr, evalMat, Circuit.eval]
  | nand a b iha ihb =>
    have hG := Γ.mul_ginv (evalMat Γ Ψ b)
    have hstep : t * (evalMat Γ Ψ a * Γ.ginv (evalMat Γ Ψ b)) =
        (a.eval x • (t * Γ.G) + evalErr Γ Ψ x e a) * Γ.ginv (evalMat Γ Ψ b) := by
      rw [← Matrix.mul_assoc, iha]
    simp only [evalErr, evalMat, Circuit.eval, Matrix.mul_sub, hstep]
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, hG, ihb, smul_add, smul_smul,
      sub_smul, one_smul]
    module

/-- The simulation trapdoor of `EvalF`: for public keys `Aᵢ = B Wᵢ + xᵢ G`,
`NAND(a, b) ↦ −(W_a · G⁻¹(A_b) + a(x) W_b)`. -/
def evalSim {m : Type*} (A : ι → Matrix r W R) (x : ι → R) (Wm : ι → Matrix m W R) :
    Circuit ι → Matrix m W R
  | .input i => Wm i
  | .one => 0
  | .nand a b => -(evalSim A x Wm a * Γ.ginv (evalMat Γ A b) + a.eval x • evalSim A x Wm b)

omit [Fintype r] in
/-- **The simulation relation** (BTVW17 §4.2, `Setup*`/`KeyGen*`; [ABB10], [BGG+14]). Public keys
`Aᵢ = B Wᵢ + xᵢ G` evaluate to `A_f = B W_f + f(x) G`. The same relation for Ring-GSW ciphertexts
`Ψᵢ = A Rᵢ + xᵢ G` gives `Ψ_f = A R_f + f(x) G`. -/
theorem sim_relation {m : Type*} [Fintype m] (B : Matrix r m R) (A : ι → Matrix r W R)
    (x : ι → R) (Wm : ι → Matrix m W R) (h : ∀ i, A i = B * Wm i + x i • Γ.G) (f : Circuit ι) :
    evalMat Γ A f = B * evalSim Γ A x Wm f + f.eval x • Γ.G := by
  induction f with
  | input i => exact h i
  | one => simp [evalSim, evalMat, Circuit.eval]
  | nand a b iha ihb =>
    have hG := Γ.mul_ginv (evalMat Γ A b)
    simp only [evalSim, evalMat, Circuit.eval]
    rw [iha, Matrix.add_mul, Matrix.smul_mul, hG, ihb]
    simp only [Matrix.mul_neg, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc, smul_add,
      smul_smul, sub_smul, one_smul]
    module

/-- **Matrix-valued functions** (BTVW17 §4.1). Encodings `c_b = s(B_b − y_b G) + e_b` of the bits of
`Y = ∑_b y_b V_b` give `∑_b c_b G⁻¹(V_b) = s(∑_b B_b G⁻¹(V_b) − Y) + ∑_b e_b G⁻¹(V_b)`. -/
theorem matrix_key_relation {β : Type*} [Fintype β] (s : Matrix (Fin 1) r R)
    (B : β → Matrix r W R) (y : β → R) (V : β → Matrix r W R) (c e : β → Matrix (Fin 1) W R)
    (h : ∀ b, c b = s * (B b - y b • Γ.G) + e b) :
    ∑ b, c b * Γ.ginv (V b) =
      s * (∑ b, B b * Γ.ginv (V b) - ∑ b, y b • V b) + ∑ b, e b * Γ.ginv (V b) := by
  have hb : ∀ b, c b * Γ.ginv (V b) =
      s * (B b * Γ.ginv (V b)) - y b • (s * V b) + e b * Γ.ginv (V b) := by
    intro b
    rw [h b, Matrix.add_mul, Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
      Γ.mul_ginv, Matrix.mul_smul]
  rw [Finset.sum_congr rfl fun b _ => hb b, Matrix.mul_sub, Matrix.mul_sum, Matrix.mul_sum,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Matrix.mul_smul]

/-- A decomposition of matrices into bits: `Y = ∑_b bits(Y)_b · V_b`. -/
structure MatrixBits (R : Type*) [CommRing R] (r W : Type*) where
  /-- The positions of the bits. -/
  Index : Type
  [fintype : Fintype Index]
  /-- The bits of a matrix. -/
  bits : Matrix r W R → Index → R
  /-- The matrix of each position. -/
  V : Index → Matrix r W R
  /-- Recomposition. -/
  recompose : ∀ Y, ∑ b, bits Y b • V b = Y

attribute [instance] MatrixBits.fintype

/-- **Matrix-valued functions, with a bit decomposition.** Encodings `c_b` of the bits of `Y` give
`∑_b c_b G⁻¹(V_b) = s(∑_b B_b G⁻¹(V_b) − Y) + ∑_b e_b G⁻¹(V_b)`. -/
theorem matrix_key_relation_bits (β : MatrixBits R r W) (s : Matrix (Fin 1) r R)
    (B : β.Index → Matrix r W R) (Y : Matrix r W R) (c e : β.Index → Matrix (Fin 1) W R)
    (h : ∀ b, c b = s * (B b - β.bits Y b • Γ.G) + e b) :
    ∑ b, c b * Γ.ginv (β.V b) =
      s * (∑ b, B b * Γ.ginv (β.V b) - Y) + ∑ b, e b * Γ.ginv (β.V b) := by
  rw [matrix_key_relation Γ s B (β.bits Y) β.V c e h, β.recompose]

end SigabaNeo.Lattices
