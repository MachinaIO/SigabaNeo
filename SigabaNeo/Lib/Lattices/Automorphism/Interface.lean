import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Parity

/-!
# Rings with automorphisms for lookup tables over exponents

The interface of ePrint 2026/2539 §3.2/§4.3 used by the scheme of `AdvancedEncryption/PE/Impl/ExpLUT`,
over an abstract commutative ring, so that the algebra of the scheme does not depend on the concrete
ring `Negacyclic (ZMod q) n`, which instantiates it (`SigabaNeo.Lib.Lattices.Automorphism`).

`ExpRing R`: the ring degree `n` (`X^n = −1`), the lookup width `W` (`W ∣ n`, `W < n`) with an
inverse of `W` in `R`, the monomial `X`, and the automorphisms `σ k` (`X ↦ X^k`, meaningful for odd
`k`, periodic in `k` with period `2n`, `σ 1 = id`, `σ k ∘ σ k' = σ (k k')`), and the **coefficient
sieve** (Lemma 7) on monomials: summing `σ_k` over `H = {1 + j · 2n/W : j < W}` keeps exactly the
monomials at positions divisible by `W`, multiplied by `W`.
-/

namespace SigabaNeo.Lattices

/-- The index `1 + j · 2n/W` of the subgroup `H` of `(ℤ/2n)^×`. -/
def hIdx (n W j : ℕ) : ℕ := 1 + j * (2 * n / W)

/-- A commutative ring with the monomial `X`, `X^n = −1`, the automorphisms `σ k` and the
coefficient sieve for the width `W`. -/
structure ExpRing (R : Type*) [CommRing R] where
  /-- The ring degree. -/
  n : ℕ
  /-- The lookup width. -/
  W : ℕ
  /-- The monomial `X`. -/
  X : R
  /-- The automorphisms `σ_k : X ↦ X^k`, for odd `k`. -/
  σ : ℕ → R →+* R
  /-- An inverse of `W`. -/
  Winv : R
  n_pos : 0 < n
  W_pos : 0 < W
  W_dvd : W ∣ n
  W_lt : W < n
  W_mul_Winv : (W : R) * Winv = 1
  X_pow_n : X ^ n = -1
  σ_X : ∀ k, Odd k → σ k X = X ^ k
  σ_one : σ 1 = RingHom.id R
  σ_comp : ∀ k k', Odd k → Odd k' → (σ k).comp (σ k') = σ (k * k')
  σ_period : ∀ k, σ (k + 2 * n) = σ k
  /-- **Lemma 7** on monomials: `Σ_{j<W} σ_{1 + j·2n/W}(X^p) = W · X^p` if `W ∣ p`, `0` otherwise. -/
  sieve : ∀ p : ℕ, (∑ j ∈ Finset.range W, σ (hIdx n W j) (X ^ p)) =
    if W ∣ p then (W : R) * X ^ p else 0

end SigabaNeo.Lattices
