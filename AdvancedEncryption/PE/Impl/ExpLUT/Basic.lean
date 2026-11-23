import SigabaNeo.Lib.Lattices.Automorphism.Interface
import SigabaNeo.Lib.Lattices.Homomorphic.Gadget
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Setting of the scheme of ePrint 2026/2539 §4–§5: encodings and gadget ciphertexts

The algebra of the predicate encryption from lookup tables over exponents (Suegami, *Implementing
Predicate Encryption for Branching Programs*, ePrint 2026/2539), over an abstract commutative ring
`R` with automorphisms (`SigabaNeo.Lattices.ExpRing`).

* `Setting R`: the ring with automorphisms `E`, the gadget digits `D` (`g`, `G⁻¹`, `τ` digits),
  which the automorphisms fix (`σ_g`), and the cyclic group `H ⊆ (ℤ/2n)^×` of order `W = 2^b`
  in **exponent form** (§3.2): `idx j` is the index of `g^j` (`g = 1 + 2n/W`), so that
  `σ_{idx i} ∘ σ_{idx j} = σ_{idx ((i + j) mod W)}` (`idx_add`) and `σ_{idx 0} = id`. Rows "indexed by
  `H`" are indexed by the exponents `j < W`; the binary basis of §3.2 is `g_t = g^{2^t}`
  (exponent `2^t`, inverse exponent `W − 2^t`).
* `Col τ = Fin 2 × Fin τ`: the `2τ` columns of the gadget `G = I₂ ⊗ g` (`S.G`), `Dig τ`: the digit
  positions `(r, j, i)` of a `2 × 2τ` matrix (§4.2).
* `sec a = (a, 1)`: the secret `s = (s̄, 1)` and its conjugates `s_k = σ_k(s) = (σ_k(s̄), 1)`.
* `Encodes S s A x e c` (§4.1, `c : ⟨xG⟩^A_s`): **exactly** `c = s A − x G + e`; an encoding of
  `μ` under `s` has payload `x = μ s`.
* `IsGC S s C z f` (§4.1, `C : GC_s⟨z G + f⟩`): `s C = z G + f`.

Everything is stated with explicit errors, so that noise bounds are a separate, norm-level step
(`PE.Impl.ExpLUT.Noise`).
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix

/-- The columns of the gadget `G = I₂ ⊗ g`: a row index and a digit. -/
abbrev Col (τ : ℕ) := Fin 2 × Fin τ

/-- The digit positions `(r, j, i)` of a `2 × 2τ` matrix: row `r`, column `j`, digit `i`. -/
abbrev Dig (τ : ℕ) := Fin 2 × Col τ × Fin τ

/-- The setting: a ring with automorphisms, gadget digits fixed by the automorphisms, and the group
`H` in exponent form. -/
structure Setting (R : Type*) [CommRing R] where
  /-- The ring with automorphisms. -/
  E : ExpRing R
  /-- The number of digits `τ`. -/
  τ : ℕ
  /-- The gadget digits (`g`, `G⁻¹`). -/
  D : GadgetDigits R τ
  /-- The automorphisms fix the gadget. -/
  σ_g : ∀ k i, E.σ k (D.g i) = D.g i
  /-- `b = log₂ W`. -/
  b : ℕ
  W_eq : E.W = 2 ^ b
  /-- The index of `g^j` in `(ℤ/2n)^×`. -/
  idx : ℕ → ℕ
  idx_odd : ∀ j, Odd (idx j)
  idx_zero : ∀ a, E.σ (idx 0) a = a
  /-- The group law of `H` in exponent form. -/
  idx_add : ∀ i j a, E.σ (idx i) (E.σ (idx j) a) = E.σ (idx ((i + j) % E.W)) a

variable {R : Type*} [CommRing R] (S : Setting R)

/-- The gadget matrix `G = I₂ ⊗ g` with its decomposition `G⁻¹`. -/
abbrev Setting.gad : GadgetMatrix R (Fin 2) (Col S.τ) := gswGadget S.D

/-- `G`. -/
abbrev Setting.G : Matrix (Fin 2) (Col S.τ) R := S.gad.G

/-- `G⁻¹`. -/
abbrev Setting.ginv (A : Matrix (Fin 2) (Col S.τ) R) : Matrix (Col S.τ) (Col S.τ) R := S.gad.ginv A

/-- The secret `(a, 1)`. -/
def sec (a : R) : Fin 2 → R := ![a, 1]

@[simp] theorem sec_zero (a : R) : sec a 0 = a := rfl
@[simp] theorem sec_one (a : R) : sec a 1 = 1 := rfl

/-- **An encoding**: `c = s A − x G + e` (`c : ⟨x G⟩^A_s` with error `e`). -/
def Encodes (s : Fin 2 → R) (A : Matrix (Fin 2) (Col S.τ) R) (x : Fin 2 → R) (e c : Col S.τ → R) :
    Prop :=
  c = s ᵥ* A - x ᵥ* S.G + e

/-- **A gadget ciphertext**: `s C = z G + f`. -/
def IsGC (s : Fin 2 → R) (C : Matrix (Fin 2) (Col S.τ) R) (z : Fin 2 → R) (f : Col S.τ → R) : Prop :=
  s ᵥ* C = z ᵥ* S.G + f

variable {S}

theorem G_apply (a : Fin 2) (c : Col S.τ) : S.G a c = if a = c.1 then S.D.g c.2 else 0 := rfl

theorem ginv_apply (A : Matrix (Fin 2) (Col S.τ) R) (c col : Col S.τ) :
    S.ginv A c col = S.D.d (A c.1 col) c.2 := by
  obtain ⟨r, i⟩ := c
  fin_cases r <;> simp [Setting.ginv, Setting.gad, gswGadget, gadgetOf]

/-- `(x G)_{(r, i)} = x_r g_i`. -/
theorem vecMul_G_apply (x : Fin 2 → R) (c : Col S.τ) : (x ᵥ* S.G) c = x c.1 * S.D.g c.2 := by
  obtain ⟨r, i⟩ := c
  fin_cases r <;> simp [Matrix.vecMul, dotProduct, G_apply]

theorem G_mul_ginv (A : Matrix (Fin 2) (Col S.τ) R) : S.G * S.ginv A = A := S.gad.mul_ginv A

theorem vecMul_G_ginv (x : Fin 2 → R) (A : Matrix (Fin 2) (Col S.τ) R) :
    x ᵥ* S.G ᵥ* S.ginv A = x ᵥ* A := by
  rw [Matrix.vecMul_vecMul, G_mul_ginv]

/-- The automorphisms fix `G`. -/
theorem G_map_σ (k : ℕ) : S.G.map (S.E.σ k) = S.G := by
  ext a c
  simp only [Matrix.map_apply, G_apply]
  split_ifs <;> simp [S.σ_g]

/-- `σ_k(a, 1) = (σ_k a, 1)`. -/
theorem σ_comp_sec (k : ℕ) (a : R) : (S.E.σ k) ∘ sec a = sec (S.E.σ k a) := by
  funext i
  fin_cases i <;> simp [sec]

theorem σ_idx_inv (t : ℕ) (ht : 2 ^ t ≤ S.E.W) (a : R) :
    S.E.σ (S.idx (2 ^ t)) (S.E.σ (S.idx (S.E.W - 2 ^ t)) a) = a := by
  rw [S.idx_add, show 2 ^ t + (S.E.W - 2 ^ t) = S.E.W by omega, Nat.mod_self, S.idx_zero]

/-! ### Elementary operations on encodings (§4.2) -/

/-- **Applying `σ_k` entrywise**: `σ_k(c) : ⟨σ_k(x) G⟩^{σ_k(A)}_{σ_k(s)}`. -/
theorem encodes_σ (k : ℕ) {s : Fin 2 → R} {A : Matrix (Fin 2) (Col S.τ) R} {x : Fin 2 → R}
    {e c : Col S.τ → R} (h : Encodes S s A x e c) :
    Encodes S (S.E.σ k ∘ s) (A.map (S.E.σ k)) (S.E.σ k ∘ x) (S.E.σ k ∘ e) (S.E.σ k ∘ c) := by
  unfold Encodes at h ⊢
  funext j
  rw [h]
  simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, map_add, map_sub,
    RingHom.map_vecMul, G_map_σ]

theorem encodes_add {s : Fin 2 → R} {A₁ A₂ : Matrix (Fin 2) (Col S.τ) R} {x₁ x₂ : Fin 2 → R}
    {e₁ e₂ c₁ c₂ : Col S.τ → R} (h₁ : Encodes S s A₁ x₁ e₁ c₁) (h₂ : Encodes S s A₂ x₂ e₂ c₂) :
    Encodes S s (A₁ + A₂) (x₁ + x₂) (e₁ + e₂) (c₁ + c₂) := by
  unfold Encodes at *
  rw [h₁, h₂, Matrix.vecMul_add, Matrix.add_vecMul]
  abel

theorem encodes_zero (s : Fin 2 → R) : Encodes S s 0 0 0 0 := by
  simp [Encodes]

theorem encodes_sum {ι : Type*} (T : Finset ι) {s : Fin 2 → R} {A : ι → Matrix (Fin 2) (Col S.τ) R}
    {x : ι → Fin 2 → R} {e c : ι → Col S.τ → R} (h : ∀ i ∈ T, Encodes S s (A i) (x i) (e i) (c i)) :
    Encodes S s (∑ i ∈ T, A i) (∑ i ∈ T, x i) (∑ i ∈ T, e i) (∑ i ∈ T, c i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using encodes_zero s
  | insert i T hi ih =>
    simp only [Finset.sum_insert hi]
    exact encodes_add (h i (Finset.mem_insert_self i T))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- **Right multiplication by a matrix** `Y` with `G Y = M` for the gadget: `c Y : ⟨x M⟩^{A Y}_s`. -/
theorem encodes_mul_right {s : Fin 2 → R} {A : Matrix (Fin 2) (Col S.τ) R} {x : Fin 2 → R}
    {e c : Col S.τ → R} (h : Encodes S s A x e c) (Y : Matrix (Col S.τ) (Col S.τ) R) :
    c ᵥ* Y = s ᵥ* (A * Y) - x ᵥ* (S.G * Y) + e ᵥ* Y := by
  unfold Encodes at h
  rw [h, Matrix.add_vecMul, Matrix.sub_vecMul, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul]

/-- **Mask switching** (the second step of `Aut_k`, §4.2): with a helper `h : ⟨s' G⟩^H_s` and an
encoding `r : ⟨y G⟩^{A'}_{s'}` under the mask `s'`, `h G⁻¹(A') + r : ⟨y G⟩^{H G⁻¹(A')}_s`. -/
theorem encodes_maskSwitch {s s' : Fin 2 → R} {H A' : Matrix (Fin 2) (Col S.τ) R} {y : Fin 2 → R}
    {e e' h r : Col S.τ → R} (hh : Encodes S s H s' e h) (hr : Encodes S s' A' y e' r) :
    Encodes S s (H * S.ginv A') y (e ᵥ* S.ginv A' + e') (h ᵥ* S.ginv A' + r) := by
  rw [encodes_mul_right hh, G_mul_ginv]
  unfold Encodes at hr ⊢
  rw [hr]
  abel

end AdvancedEncryption.ExpLUT
