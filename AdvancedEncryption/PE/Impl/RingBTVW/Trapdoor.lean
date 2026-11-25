import PE.Impl.RingBTVW.Scheme

/-!
# The trapdoor part of the public key

`B₁ = [1 | a | G̲ − (t a + e)]` with `a` uniform and `t`, `e` short has the exact trapdoor
`T = [e; t I; I]`: `B₁ T = G̲` (`trapRow_mul_trapMat`). The pair `(a, t a + e)` is a Ring-LWE
instance with secret `t`, so `B₁` is pseudorandom under Ring-LWE (hybrid 3 of the security proof).
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW.Fresh

variable {R : Type*} [CommRing R] {k : ℕ} (S : Setting R k)

/-- The columns of `B₁`: the constant `1`, then `a`, then `G̲ − (t a + e)`. -/
abbrev TrapCol (k : ℕ) := Fin 1 ⊕ Col k ⊕ Col k

/-- `B₁ = [1 | a | G̲ − (t a + e)]`. -/
def trapRow (a e : Matrix (Fin 1) (Col k) R) (t : R) : Matrix (Fin 1) (TrapCol k) R :=
  Matrix.of fun _ c => match c with
    | .inl _ => 1
    | .inr (.inl c) => a 0 c
    | .inr (.inr c) => S.Γ₁.G 0 c - (t * a 0 c + e 0 c)

/-- `T = [e; t I; I]`. -/
def trapMat (e : Matrix (Fin 1) (Col k) R) (t : R) : Matrix (TrapCol k) (Col k) R :=
  Matrix.of fun c c' => match c with
    | .inl _ => e 0 c'
    | .inr (.inl c) => if c = c' then t else 0
    | .inr (.inr c) => if c = c' then 1 else 0

/-- **`B₁ T = G̲`.** -/
theorem trapRow_mul_trapMat (a e : Matrix (Fin 1) (Col k) R) (t : R) :
    trapRow S a e t * trapMat e t = S.Γ₁.G := by
  ext i c'
  fin_cases i
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, trapRow, trapMat, Matrix.of_apply,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, one_mul, mul_ite, mul_zero,
    mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring_nf
  rfl

end AdvancedEncryption.RingBTVW
