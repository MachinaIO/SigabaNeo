import PE.Impl.ExpLUT.GameChain
import PE.Impl.Game.OneSetup

/-!
# The chain without the union over attributes (package G)

`GameChain.chain` pays `|Attr|` for every statistical step (`Generic.closeTo_runWith_setup`, a
union over all attributes: `2^128` for the universe `w8`). The secret is drawn once, at the
selection, so each step costs its distance once (`Generic.closeTo_runWith_setup_one`):
`gameV_close_one`, and `chain1`: real vs ideal within `δ₁ + ε_fl + δ_T + δ₄ + δ₅ + δ_T`.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix Cslib Cslib.Probability AdvancedEncryption.PE
open scoped ENNReal

variable {R : Type} [CommRing R] [Fintype R] [DecidableEq R] {S : Setting R} {Wb J Pos : Type}
  [Fintype Wb] [DecidableEq Wb] [Nonempty Wb] [Fintype J] [DecidableEq J] [Fintype Pos]
  [DecidableEq Pos]

variable (U : Universe) [Fintype U.Attr] [DecidableEq U.Attr] (half : R) (msgOf : U.Msg → R)
  (encMPK : MPK S Wb J Pos → List Bool) (encCT : Ciphertext S Wb J Pos → List Bool)
  (KGi : MPK S Wb J Pos → List Bool → PMF (List Bool)) (authB : List Bool → U.Attr → Bool)

/-- **A statistical step of the experiment costs its distance once.** -/
theorem gameV_close_one {α : Type} (prog : ProbOracleComp (fun _ : Fin 3 × List Bool => List Bool) α)
    {V V' : U.Attr → PMF (MPK S Wb J Pos × Ciphertext S Wb J Pos)} {ε : ℝ≥0∞}
    (h : ∀ x, CloseTo (V x) (V' x) ε) :
    CloseTo (gameV U half msgOf encMPK encCT KGi authB prog V)
      (gameV U half msgOf encMPK encCT KGi authB prog V') ε := by
  unfold gameV
  exact (Generic.closeTo_runWith_setup_one (specV U half msgOf encMPK encCT KGi authB V) V' h prog
    {}).map _

/-! ### The chain -/

variable (M : HelperMap S J) (w : ℕ) (χs χ χfl : PMF R) (attrOf : U.Attr → Pos → ℕ)

/-- **Theorem 2, the chain, without the union over attributes**: for every program (adversary with its oracles) and every continuation
`Dc` of its observable output, the real experiment (`hyb0`: `Setup`, `Enc`) and the ideal one
(`idealView`: `Setup`'s public key, the simulator's uniform ciphertext) are within
`δ₁ + ε_fl + δ_T + δ₄ + δ₅ + δ_T`, where `ε_fl` is the flooding distance and
`δ₄` the circular Ring-LWE advantage of the experiment-as-distinguisher run on the reduction `red`. -/
theorem chain1 {α β : Type} (prog : ProbOracleComp (fun _ : Fin 3 × List Bool => List Bool) α)
    (Dc : α × Option U.Attr × Option U.Msg × Bool → PMF β) {εfl δ₄ : ℝ≥0∞}
    (hflood : ∀ eb ∈ (iidLaw χ (BCol Wb S.τ)).support, ∀ zr : PrI S Pos → Wb → Bool,
      CloseTo ((floodLaw S Pos χfl).map (· + floodShift eb zr)) (floodLaw S Pos χfl) εfl)
    (h₄ : CloseTo ((circReal S Wb J M χs χ).bind fun inst =>
        (gameV U half msgOf encMPK encCT KGi authB prog fun x => red M w χfl (attrOf x) inst).bind Dc)
      ((circUnif S Wb J).bind fun inst =>
        (gameV U half msgOf encMPK encCT KGi authB prog fun x => red M w χfl (attrOf x) inst).bind Dc)
      δ₄) :
    CloseTo
      ((gameV U half msgOf encMPK encCT KGi authB prog fun x =>
        hyb0 M w half χs χ χfl (attrOf x)).bind Dc)
      ((gameV U half msgOf encMPK encCT KGi authB prog fun _ => idealView).bind Dc)
      (delta1 S Wb Pos + εfl + deltaT S Wb + δ₄ + delta5 S Wb Pos + deltaT S Wb) := by
  have g01 := (gameV_close_one U half msgOf encMPK encCT KGi authB prog
    (fun x => hybrid01_close (Wb := Wb) M w half χs χ χfl (attrOf x))).bind_left Dc
  have g12 := (gameV_close_one U half msgOf encMPK encCT KGi authB prog
    (fun x => hybrid2_close (Wb := Wb) M w half χs χ χfl (attrOf x) hflood)).bind_left Dc
  have g23 := (gameV_close_one U half msgOf encMPK encCT KGi authB prog
    (fun x => hybrid23_close (Wb := Wb) M w χs χ χfl (attrOf x))).bind_left Dc
  have e3 : gameV U half msgOf encMPK encCT KGi authB prog (fun x => hyb3 M w χs χ χfl (attrOf x)) =
      (circReal S Wb J M χs χ).bind fun inst =>
        gameV U half msgOf encMPK encCT KGi authB prog fun x => red M w χfl (attrOf x) inst := by
    rw [← gameV_bind]; congr 1; funext x; exact (reduction_real (Wb := Wb) M w χs χ χfl (attrOf x)).symm
  have e4 : gameV U half msgOf encMPK encCT KGi authB prog (fun x => hyb4 M w χfl (attrOf x)) =
      (circUnif S Wb J).bind fun inst =>
        gameV U half msgOf encMPK encCT KGi authB prog fun x => red M w χfl (attrOf x) inst := by
    rw [← gameV_bind]; congr 1; funext x; exact (reduction_unif (Wb := Wb) M w χfl (attrOf x)).symm
  have g34 : CloseTo
      ((gameV U half msgOf encMPK encCT KGi authB prog fun x => hyb3 M w χs χ χfl (attrOf x)).bind Dc)
      ((gameV U half msgOf encMPK encCT KGi authB prog fun x => hyb4 M w χfl (attrOf x)).bind Dc) δ₄ := by
    rw [e3, e4, PMF.bind_bind, PMF.bind_bind]; exact h₄
  have g45 := (gameV_close_one U half msgOf encMPK encCT KGi authB prog
    (fun x => (hyb4_eq_L (Wb := Wb) M w χfl (attrOf x)) ▸ hybrid45_close (Wb := Wb) M w χfl (attrOf x))).bind_left Dc
  have g56 := (gameV_close_one U half msgOf encMPK encCT KGi authB prog
    (fun x => (hyb5_eq_final (Wb := Wb) M w χfl (attrOf x)).symm ▸
      (idealView_eq (S := S) (Wb := Wb) (J := J) (Pos := Pos)).symm ▸ hybrid56_close)).bind_left Dc
  exact ((((g01.trans g12).trans g23).trans g34).trans g45).trans g56

end AdvancedEncryption.ExpLUT
