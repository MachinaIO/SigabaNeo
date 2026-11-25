import PE.Impl.RingBTVW.Registry
import SigabaNeo.Lib.Lattices.Estimator.Bound.Cbd

/-!
# The Ring-LWE strength of the registry's instances, generically

At ring degree `N` (a power of two), modulus `q = 2^e`, `CBD(16)` secret and error, the registry's
instances (`RingBTVW/Registry.lean`) are

* hybrid 3, `params3 N (2^e) k (cbd 16)`: `2k` samples (`params3_eq`);
* hybrid 5, `params5 N (2^e) k (Fin d) (cbd 16)`: `d + 4k + 1` samples (`params5_eq`).

`H_ge_of_cbd` reduces `kb ≤ RingLWE.H` at `m` samples to the closed facts and the per-block-size
checks of `Estimator.cbd16_estimatorBits_ge` at `N · m` LWE samples; `registry3_ge`,
`registry5_ge` state it for the two instances. The instances are made by the files
`Params/Strength.lean` (`N = 2^34`) and `Params/StrengthA.lean` (`N = 2^36`).
-/

namespace AdvancedEncryption.RingBTVW.Params.Strength

open SigabaNeo.Lattices SigabaNeo.Lattices.Estimator

instance neZero_two_pow (e : ℕ) : NeZero ((2 : ℕ) ^ e) := ⟨by positivity⟩

theorem two_le_two_pow {e : ℕ} (he : 1 ≤ e) : 2 ≤ 2 ^ e :=
  calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ e := pow_le_pow_right₀ (by norm_num) he

theorem inDomain_of {N q m : ℕ} (hN : Hardness.isPow2 N = true) (hq0 : 0 < q) (hq : 2 ≤ q)
    (hm : 1 ≤ m) :
    (RingLWE.Params.toModule ⟨N, m, q, .cbd 16, .cbd 16, hq0⟩).inDomain = true := by
  simp only [ModuleLWE.Params.inDomain, RingLWE.Params.toModule, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨hN, rfl⟩, decide_eq_true hm⟩, decide_eq_true hq⟩, rfl⟩, rfl⟩

/-- The bound on `RingLWE.H` from the bound on the estimator at the LWE view (any modulus `q`;
the kernel never computes it). -/
theorem H_ge_of_bits {N q m kb : ℕ} (hN : Hardness.isPow2 N = true) (hq0 : 0 < q) (hq : 2 ≤ q)
    (hm : 1 ≤ m)
    (h : kb ≤ estimatorBits (LWEParams.mk' (N * 1) q (ND.cbd 16) (ND.cbd 16) (some (N * m)))) :
    kb ≤ RingLWE.H ⟨N, m, q, .cbd 16, .cbd 16, hq0⟩ :=
  RingLWE.H_ge_of (inDomain_of hN hq0 hq hm) h

/-- **`kb ≤ RingLWE.H`** at ring degree `N`, `m` samples, `q = 2^e`, `CBD(16)`, from the closed
facts and the per-block-size checks at `N · m` LWE samples. -/
theorem H_ge_of_cbd {N e m kb : ℕ} (hN : Hardness.isPow2 N = true) (he : 1 ≤ e) (hm : 1 ≤ m)
    (hf : cbdFacts (N * 1) e (N * m) kb = true)
    (hc : ∀ b < maxBeta + 2, cbdCheck (N * 1) e (N * m) kb b = true) :
    kb ≤ RingLWE.H ⟨N, m, 2 ^ e, .cbd 16, .cbd 16, by positivity⟩ :=
  H_ge_of_bits hN _ (two_le_two_pow he) hm (cbd16_estimatorBits_ge hf hc)

/-- Hybrid 3's instance has `2k` samples. -/
theorem params3_eq (N q k : ℕ) [NeZero q] (err : SecretDist) :
    params3 N q k err = ⟨N, 2 * k, q, err, err, NeZero.pos q⟩ := by
  unfold params3
  simp only [RingLWE.Params.mk.injEq, and_true, true_and]
  simp [RingBTVW.Fresh.Col]

/-- Hybrid 5's instance at `Wd = Fin d` has `d + 4k + 1` samples. -/
theorem params5_eq (N q k d : ℕ) [NeZero q] [NeZero d] (err : SecretDist) :
    params5 N q k (Fin d) err = ⟨N, d + 4 * k + 1, q, err, err, NeZero.pos q⟩ := by
  unfold params5
  simp only [RingLWE.Params.mk.injEq, and_true, true_and]
  simp [Idx5, RingBTVW.Fresh.Col]
  ring

/-- **The registry's hybrid 3 instance: `kb ≤ RingLWE.H`** (`M = N · 2k` LWE samples). -/
theorem registry3_ge {N e k M kb : ℕ} [NeZero (2 ^ e : ℕ)] (hN : Hardness.isPow2 N = true)
    (he : 1 ≤ e) (hk : 1 ≤ k) (hM : N * (2 * k) = M)
    (hf : cbdFacts (N * 1) e M kb = true)
    (hc : ∀ b < maxBeta + 2, cbdCheck (N * 1) e M kb b = true) :
    kb ≤ RingLWE.H (params3 N (2 ^ e) k (.cbd 16)) := by
  subst hM; rw [params3_eq]; exact H_ge_of_cbd hN he (by omega) hf hc

/-- **The registry's hybrid 5 instance at `Wd = Fin d`: `kb ≤ RingLWE.H`** (`M = N · (d + 4k + 1)`
LWE samples). -/
theorem registry5_ge {N e k d M kb : ℕ} [NeZero (2 ^ e : ℕ)] [NeZero d]
    (hN : Hardness.isPow2 N = true) (he : 1 ≤ e) (hM : N * (d + 4 * k + 1) = M)
    (hf : cbdFacts (N * 1) e M kb = true)
    (hc : ∀ b < maxBeta + 2, cbdCheck (N * 1) e M kb b = true) :
    kb ≤ RingLWE.H (params5 N (2 ^ e) k (Fin d) (.cbd 16)) := by
  subst hM; rw [params5_eq]; exact H_ge_of_cbd hN he (by omega) hf hc

end AdvancedEncryption.RingBTVW.Params.Strength
