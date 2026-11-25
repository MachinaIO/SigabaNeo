import SigabaNeoStd.Lattices.CircularRingLWE
import SigabaNeoStd.Lattices.Estimator.Bound.CbdQ

/-!
# The strength of circular Ring-LWE at `q = 2^K − 1`, generically

The underlying Ring-LWE instance of ExpLUT's circular Ring-LWE assumption: ring degree `N` (a power
of two), `m` plain samples, the odd modulus `q = 2^K − 1` (`PLAN.md`, design decision 1),
`CBD(16)` secret and error (normal form, as `RingBTVW`'s `confA`).

* `ringParams N K m`: these Ring-LWE parameters; `circParams N K m J τ`: the circular ones with
  automorphism indices `J` and gadget length `τ`.
* `ringLWE_H_ge`: `kb ≤ RingLWE.H (ringParams N K m)` for **every** `m` with `M₀ ≤ N m` and
  `56 N m ≤ (N − ZA) · R^6`, from the closed facts `cbdFactsQ N kb W ZA K₀ R` and the per-block-size
  checks `cbdCheckQ N (K · 2^P − 1) M₀ kb W b` (`Estimator.cbd16q_estimatorBits_ge`). The modulus
  enters only through `log₂ q = K − 2^{−P}` (`Fx.log2Nat_two_pow_sub_one`), so `2^K − 1` is never
  computed.
* `circularRingLWE_H_ge`: the same for `CircularRingLWE.H`, which is `RingLWE.H` of the base,
  for every `J` and `τ`.

The checks depend on `K` (through `log₂ q`), on `N`, `M₀`, `kb` and `W`, not on `m`, `J` or `τ`;
`W`, `ZA`, `K₀`, `R` are the free constants of the lower-bound argument
(`SigabaNeoStd/Lattices/Estimator/Bound/CbdQ.lean`).
-/

namespace AdvancedEncryption.ExpLUT.Params

open SigabaNeo.Lattices SigabaNeo.Lattices.Estimator Fx

theorem two_pow_sub_one_pos {K : ℕ} (hK : 1 ≤ K) : 0 < 2 ^ K - 1 := by
  have : 2 ≤ 2 ^ K :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK
  omega

/-- The Ring-LWE parameters: ring degree `N`, `m` samples, `q = 2^K − 1`, `CBD(16)` secret and
error (`K ≥ 1`). -/
def ringParams (N K m : ℕ) (hK : 1 ≤ K) : RingLWE.Params :=
  ⟨N, m, 2 ^ K - 1, .cbd 16, .cbd 16, two_pow_sub_one_pos hK⟩

/-- The circular Ring-LWE parameters over `ringParams N K m`, with automorphism indices `J` and
gadget length `τ`. -/
def circParams (N K m : ℕ) (hK : 1 ≤ K) (J : List ℕ) (τ : ℕ) : CircularRingLWE.Params :=
  ⟨ringParams N K m hK, J, τ⟩

theorem ringParams_inDomain {N K m : ℕ} (hK : 2 ≤ K) (hN : Hardness.isPow2 N = true)
    (hm : 1 ≤ m) : (ringParams N K m (by omega)).toModule.inDomain = true := by
  have h4 : 4 ≤ 2 ^ K :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK
  simp only [ModuleLWE.Params.inDomain, RingLWE.Params.toModule, ringParams, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨hN, rfl⟩, decide_eq_true hm⟩, decide_eq_true (by omega)⟩, rfl⟩, rfl⟩

/-- **`kb ≤ RingLWE.H`** at `N`, `q = 2^K − 1` (`K ≥ 1025`), `CBD(16)`, every sample count `m`
with `M₀ ≤ N m`, `maxBeta + 1 + W + kb + 22 ≤ N m + N` and `56 N m ≤ (N − ZA) · R^6`, from the
closed facts and the per-block-size checks. -/
theorem ringLWE_H_ge {N K m M₀ kb W ZA K₀ R : ℕ} (hK : 1025 ≤ K) (hN : Hardness.isPow2 N = true)
    (hm : 1 ≤ m) (hM₀ : M₀ ≤ N * m) (hMlo : maxBeta + 1 + W + (kb + 22) ≤ N * m + N)
    (hMhi : 56 * (N * m) ≤ (N - ZA) * R ^ 6)
    (hf : cbdFactsQ N kb W ZA K₀ R = true)
    (hc : ∀ b < maxBeta + 2, cbdCheckQ N ((K : ℤ) * ONE - 1) M₀ kb W b = true) :
    kb ≤ RingLWE.H (ringParams N K m (by omega)) := by
  apply RingLWE.H_ge_of (ringParams_inDomain (by omega) hN hm)
  show kb ≤ estimatorBits (cbdPq (N * 1) (2 ^ K - 1) (N * m))
  rw [Nat.mul_one]
  have hq : 2 ^ 1024 ≤ 2 ^ K - 1 :=
    Nat.le_sub_one_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hK97 : Fx.K + 1 < K := by
    have : Fx.K = 96 := rfl
    omega
  exact cbd16q_estimatorBits_ge (e := 1024) hq le_rfl (Fx.log2Nat_two_pow_sub_one hK97)
    (Fx.log2_ofInt_two_pow_sub_one hK97) hM₀ hMlo hMhi hf hc

/-- **`kb ≤ CircularRingLWE.H`** under the same conditions, for every `J` and `τ`. -/
theorem circularRingLWE_H_ge {N K m M₀ kb W ZA K₀ R : ℕ} (hK : 1025 ≤ K)
    (hN : Hardness.isPow2 N = true) (hm : 1 ≤ m) (hM₀ : M₀ ≤ N * m)
    (hMlo : maxBeta + 1 + W + (kb + 22) ≤ N * m + N)
    (hMhi : 56 * (N * m) ≤ (N - ZA) * R ^ 6)
    (hf : cbdFactsQ N kb W ZA K₀ R = true)
    (hc : ∀ b < maxBeta + 2, cbdCheckQ N ((K : ℤ) * ONE - 1) M₀ kb W b = true)
    (J : List ℕ) (τ : ℕ) :
    kb ≤ CircularRingLWE.H (circParams N K m (by omega) J τ) :=
  ringLWE_H_ge hK hN hm hM₀ hMlo hMhi hf hc

end AdvancedEncryption.ExpLUT.Params
