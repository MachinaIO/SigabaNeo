import PE.Impl.ExpLUT.CorrectBound
import CslibFrontier.Probability.Product
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Cslib.Probability.PMF

/-!
# The laws of the coins of `Setup` and `Enc`

Over a finite ring, with abstract laws of ring elements (the plan's binary and box laws are
instances): `χT` for the entries of the TrapGen trapdoor `T`, `χs` for the secret, `χ` for the base
errors (`e_b`, `e_k`, `e_m`) and `χfl` for the flooding errors (`e₀`, `e_t`, and of the digit
encodings). All entries are independent (`iidLaw`, `Cslib.Probability.PMF.pi`), the public
matrices uniform.

* `setupCoinsLaw`, `setupLaw`: the law of `Setup`; on its support, `msk` holds the public key and
  its trapdoor (`mem_support_setupLaw`).
* `encCoinsLaw`, `encLaw`: the law of `Enc`; on its support, the coins satisfy `CoinBounds` when the
  supports of `χ` and `χfl` are within `B_χ` and `B_fl` (`coinBounds_of_mem_support`).
* `decrypt_fail_le` (Theorem 1, probabilistic form): with a good covered trapdoor, decryption
  fails at most with the abort probability of key generation.
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix
open scoped ENNReal

variable {R : Type} [CommRing R] [Fintype R] {S : Setting R} {Wb J Pos : Type} [Fintype Wb]
  [DecidableEq Wb] [Fintype J] [DecidableEq J] [Fintype Pos] [DecidableEq Pos]

/-- Independent entries from `χ`. -/
noncomputable def iidLaw (χ : PMF R) (ι : Type) [Fintype ι] : PMF (ι → R) :=
  Cslib.Probability.PMF.pi fun _ : ι => χ

omit [CommRing R] in
theorem mem_support_iidLaw {χ : PMF R} {ι : Type} [Fintype ι] {v : ι → R}
    (hv : v ∈ (iidLaw χ ι).support) (i : ι) : v i ∈ χ.support :=
  (Cslib.Probability.PMF.mem_support_pi_iff _ v).mp hv i

/-- Independent families of rows from `χ`. -/
noncomputable def iidFam (χ : PMF R) (κ ι : Type) [Fintype κ] [Fintype ι] : PMF (κ → ι → R) :=
  Cslib.Probability.PMF.pi fun _ : κ => iidLaw χ ι

omit [CommRing R] in
theorem mem_support_iidFam {χ : PMF R} {κ ι : Type} [Fintype κ] [Fintype ι] {v : κ → ι → R}
    (hv : v ∈ (iidFam χ κ ι).support) (k : κ) (i : ι) : v k i ∈ χ.support :=
  mem_support_iidLaw ((Cslib.Probability.PMF.mem_support_pi_iff _ v).mp hv k) i

variable (S Wb J Pos)

/-- **The law of the coins of `Setup`**: `Ā`, `B⁽²⁾`, `H_k`, `a_t`, `A₀`, `A^in`, `A^aut`, `d`
uniform, `T` with independent entries from `χT`. -/
noncomputable def setupCoinsLaw (χT : PMF R) : PMF (SetupCoins S Wb J Pos) :=
  (Cslib.Probability.PMF.uniformOfFintype (Wb → R)).bind fun Abar =>
  (iidFam χT Wb (Fin S.τ)).bind fun T =>
  (Cslib.Probability.PMF.uniformOfFintype (BCol Wb S.τ → R)).bind fun B2 =>
  (Cslib.Probability.PMF.uniformOfFintype (J → Matrix (Fin 2) (Col S.τ) R)).bind fun H =>
  (Cslib.Probability.PMF.uniformOfFintype (Pos → Col S.τ → R)).bind fun a =>
  (Cslib.Probability.PMF.uniformOfFintype (Matrix (Fin 2) (Col S.τ) R)).bind fun A0 =>
  (Cslib.Probability.PMF.uniformOfFintype (Pos → Dig S.τ → Matrix (Fin 2) (Col S.τ) R)).bind fun Ain =>
  (Cslib.Probability.PMF.uniformOfFintype (Fin S.b → Dig S.τ → Matrix (Fin 2) (Col S.τ) R)).bind fun Aaut =>
  (Cslib.Probability.PMF.uniformOfFintype (Fin 2 → R)).map fun d => ⟨Abar, T, B2, H, a, A0, Ain, Aaut, d⟩

/-- **The law of `Setup`.** -/
noncomputable def setupLaw (χT : PMF R) : PMF (MPK S Wb J Pos × MSK S Wb J Pos) :=
  (setupCoinsLaw S Wb J Pos χT).map setup

/-- **The law of the coins of `Enc`**: `s̄ ← χs`, base errors from `χ`, flooding errors from
`χfl`, all independent. -/
noncomputable def encCoinsLaw (χs χ χfl : PMF R) : PMF (EncCoins S Wb J Pos) :=
  χs.bind fun s =>
  (iidLaw χ (BCol Wb S.τ)).bind fun eb =>
  (iidFam χ J (Col S.τ)).bind fun eh =>
  (iidFam χfl (Fin S.b × Dig S.τ) (Col S.τ)).bind fun eaut =>
  (iidFam χfl Pos (Col S.τ)).bind fun ein =>
  (iidFam χfl (Pos × Dig S.τ) (Col S.τ)).bind fun edin =>
  (iidLaw χfl (Col S.τ)).bind fun e0 =>
  χ.map fun em => ⟨s, eb, eh, fun t d => eaut (t, d), ein, fun t d => edin (t, d), e0, em⟩

/-- **The law of `Enc`.** -/
noncomputable def encLaw (χs χ χfl : PMF R) (M : HelperMap S J) (w : ℕ) (half : R)
    (mpk : MPK S Wb J Pos) (x : Pos → ℕ) (m : R) : PMF (Ciphertext S Wb J Pos) :=
  (encCoinsLaw S Wb J Pos χs χ χfl).map (encrypt M w half mpk x m)

variable {S Wb J Pos}

/-- On the support of `Setup`, `msk = (mpk, T)` with `B⁽¹⁾ = [Ā | g − Ā T]` and `T` from `χT`. -/
theorem mem_support_setupLaw {χT : PMF R} {v : MPK S Wb J Pos × MSK S Wb J Pos}
    (hv : v ∈ (setupLaw S Wb J Pos χT).support) :
    v.2.mpk = v.1 ∧ TrapOK v.1 v.2.T ∧ ∀ w c, v.2.T w c ∈ χT.support := by
  simp only [setupLaw, setupCoinsLaw, PMF.support_map, PMF.support_bind, Set.mem_image,
    Set.mem_iUnion] at hv
  obtain ⟨r, ⟨Abar, -, T, hT, B2, -, H, -, a, -, A0, -, Ain, -, Aaut, -, d, -, rfl⟩, rfl⟩ := hv
  exact ⟨rfl, fun c => rfl, fun w c => mem_support_iidFam hT w c⟩

omit [DecidableEq Wb] [DecidableEq J] [DecidableEq Pos] in
/-- **The coins of `Enc` are bounded** on the support of their law. -/
theorem coinBounds_of_mem_support (N : NormSpec S) {χs χ χfl : PMF R} {Bχ Bfl : ℕ}
    (hχ : ∀ a ∈ χ.support, N.nrm a ≤ Bχ) (hfl : ∀ a ∈ χfl.support, N.nrm a ≤ Bfl)
    {r : EncCoins S Wb J Pos} (hr : r ∈ (encCoinsLaw S Wb J Pos χs χ χfl).support) :
    CoinBounds N r Bχ Bfl := by
  simp only [encCoinsLaw, PMF.support_map, PMF.support_bind, Set.mem_image, Set.mem_iUnion] at hr
  obtain ⟨s, -, eb, heb, eh, heh, eaut, heaut, ein, hein, edin, hedin, e0, he0, em, hem, rfl⟩ := hr
  exact
    { eb := fun c => hχ _ (mem_support_iidLaw heb c)
      eh := fun k c => hχ _ (mem_support_iidFam heh k c)
      em := hχ _ hem
      eaut := fun t d c => hfl _ (mem_support_iidFam heaut (t, d) c)
      ein := fun t c => hfl _ (mem_support_iidFam hein t c)
      edin := fun t d c => hfl _ (mem_support_iidFam hedin (t, d) c)
      e0 := fun c => hfl _ (mem_support_iidLaw he0 c) }

omit [DecidableEq Wb] [DecidableEq J] [DecidableEq Pos] in
/-- **Theorem 1, probabilistic form**: for `F(x) = 0`, with a good trapdoor covered by the boxes,
short boxes and decompositions, coins from laws within the bounds and `decode` exact within
`corrBound`, the probability that decryption with a key of `keyLaw` does not return `m` is at most
the abort probability of key generation. -/
theorem decrypt_fail_le [DecidableEq R] (N : NormSpec S) (h8 : Lemma8 S) (M : HelperMap S J)
    {w : ℕ} (half : R) (mpk : MPK S Wb J Pos) (F : BP Pos) (hF : F.WF S.E.W) (hw : F.w = w)
    (x : Pos → ℕ) (hx : ∀ t, x t < F.nsym) (hFx : F.eval x = 0) (m : R)
    {χs χ χfl : PMF R} {Bχ Bfl K : ℕ} (hD : 1 ≤ S.gfac)
    (hχ : ∀ a ∈ χ.support, N.nrm a ≤ Bχ) (hfl : ∀ a ∈ χfl.support, N.nrm a ≤ Bfl)
    (Big Small : Finset (PIdx Wb J S.τ S.E.W → R)) (hBig : Big.Nonempty)
    (dec : (Fin S.E.W → R) → ZIdx S.τ S.E.W → R) (hdec : ∀ y, gadZ (dec y) = y)
    (T : (ZIdx S.τ S.E.W → R) → PIdx Wb J S.τ S.E.W → R) (hT : GoodTrap M mpk F T)
    (hcov : ∀ x ∈ Small, ∀ y, x + T (dec y) ∈ Big)
    (hSmall : ∀ v ∈ Small, RowBnd N v K) (hdecK : ∀ y, RowBnd N (dec y) K)
    {Msg : Type} [DecidableEq Msg] (decode : R → Msg) (mm : Msg)
    (hdecode : ∀ e, N.nrm e ≤ corrBound S Wb J F.T Bχ Bfl K → decode (half * m + e) = mm) :
    ((keyLaw Big Small hBig dec M mpk F T).bind fun o =>
        (encLaw S Wb J Pos χs χ χfl M w half mpk x m).map fun ct =>
          decide (decrypt decode M mpk F (keyOfOutput o) ct = mm)) false ≤
      keyLaw Big Small hBig dec M mpk F T none := by
  rw [PMF.bind_apply, tsum_eq_single none]
  · exact mul_le_of_le_one_right' (PMF.coe_le_one _ _)
  · intro o ho
    cases o with
    | none => exact absurd rfl ho
    | some v =>
      by_cases hv : some v ∈ (keyLaw Big Small hBig dec M mpk F T).support
      · refine mul_eq_zero_of_right _ ?_
        rw [encLaw, PMF.map_comp, PMF.map_apply]
        refine tsum_eq_zero_iff.mpr fun r => ?_
        by_cases hrs : r ∈ (encCoinsLaw S Wb J Pos χs χ χfl).support
        · have hc := decrypt_correct_of_mem_support h8 M half mpk F hF hw x hx hFx m r hD
            (coinBounds_of_mem_support N hχ hfl hrs) Big Small hBig dec hdec T hT hcov hSmall
            hdecK v hv decode mm hdecode
          simp [hc]
        · simp [(PMF.apply_eq_zero_iff _ _).mpr hrs]
      · simp [(PMF.apply_eq_zero_iff _ _).mpr hv]

end AdvancedEncryption.ExpLUT
