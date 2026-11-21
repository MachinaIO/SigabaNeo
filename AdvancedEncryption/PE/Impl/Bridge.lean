import PE

/-!
# From scheme laws to the machine-level propositions

An implementation whose machines realize the laws of a scheme, through encodings of its keys and
ciphertexts, inherits the scheme's correctness (`correct_of_laws`): if `Setup`, `KeyGen`, `Enc` and
`Dec` output the encodings of the scheme's `(mpk, msk)`, keys, ciphertexts and decryptions, and
the scheme decrypts correctly with probability at least `1 − 2^{-κ}` for every authorized
predicate, then `PE.Correct` holds. The machines themselves come from
`SigabaNeo.Lib.Machines.Randomized` and `Guarded`.
-/

namespace AdvancedEncryption.PE

open SigabaNeo

variable {U : Universe} (p : Params) (impl : Impl sig)

/-- **Correctness from the scheme's laws.** -/
theorem correct_of_laws {MPK MSK SK CT : Type}
    (encMPK : MPK → List Bool) (encMSK : MSK → List Bool) (encSK : SK → List Bool)
    (encCT : CT → List Bool) (setupM : PMF (MPK × MSK))
    (keyM : MSK → List Bool → PMF SK) (encM : MPK → U.Attr → U.Msg → PMF CT)
    (decM : SK → List Bool → CT → List Bool)
    (hsetup : setup (U := U) p impl = setupM.map fun v => (encMPK v.1, encMSK v.2))
    (hkey : ∀ msk C (x : U.Attr), Authorized p impl C x → keyGen (U := U) p impl (encMSK msk) C =
      (keyM msk C).map encSK)
    (henc : ∀ mpk x μ, enc p impl (encMPK mpk) x μ = (encM mpk x μ).map encCT)
    (hdec : ∀ sk C ct (x : U.Attr), Authorized p impl C x →
      dec (U := U) p impl (encSK sk) C (encCT ct) = PMF.pure (decM sk C ct))
    (hscheme : ∀ x C, Authorized p impl C x → ∀ μ,
      1 - ((2 : ℝ) ^ p.corrBits)⁻¹ ≤
        ((setupM.bind fun v => (keyM v.2 C).bind fun sk => (encM v.1 x μ).map fun ct =>
          decM sk C ct) (U.encMsg μ)).toReal) :
    Correct U p impl := by
  intro x C hC μ
  have hlaw : decryptLaw U p impl x C μ = setupM.bind fun v => (keyM v.2 C).bind fun sk =>
      (encM v.1 x μ).map fun ct => decM sk C ct := by
    unfold decryptLaw
    simp only [Cslib.Probability.PMF.monad_bind_eq_bind, hsetup, PMF.bind_map]
    refine congrArg (PMF.bind setupM) (funext fun v => ?_)
    simp only [Function.comp_apply, hkey v.2 C x hC, PMF.bind_map, henc]
    refine congrArg (PMF.bind _) (funext fun sk => ?_)
    simp only [Function.comp_apply]
    rw [PMF.map]
    refine congrArg (PMF.bind _) (funext fun ct => ?_)
    simp only [Function.comp_apply, hdec sk C ct x hC]
  rw [hlaw]
  exact hscheme x C hC μ

end AdvancedEncryption.PE
