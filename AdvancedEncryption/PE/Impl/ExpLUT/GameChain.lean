import PE.Impl.ExpLUT.Hybrid6
import PE.Impl.Game.Generic

/-!
# The hybrids as experiments with oracles (Theorem 2, the chain)

The adversary of `PE.AttributeHiding` interacts with the challenger through oracles. With the
challenger's secret the pair `(mpk, ct₀)` of the public key and the challenge for the message `0`
(`specV`), the key oracle answering from `mpk` only (any `KGi`; the real keys have the ideal law
`idealKeyLaw` of `M_F`, a function of `mpk`, by `keyLaw_eq_ideal`) and the challenge for `μ` the
shift of `c_m` by `⌊q/2⌉ · μ` (`shiftCT`, `encrypt_shift`), the hybrids of
`PE.Impl.ExpLUT.Hybrid*` become changes of the law `V x` of the secret for the selected attribute
`x` (as in `PE.Impl.RingBTVW.GameChain`):

* statistical steps (H1, H2, H3′, H5, H6) move the experiment by at most `|Attr|` times the step's
  distance (`gameV_close`, from `Generic.closeTo_runWith_setup`);
* the circular Ring-LWE step (H3′ → H4) is an average over one instance (`gameV_bind`, from
  `Generic.runWith_bind_setup`): the whole experiment, as a function of the instance, is the
  distinguisher (`red`, `reduction_real`, `reduction_unif`).

`chain`: **the real experiment is close to the ideal one** (H6: `Setup`'s public key and the
simulator's uniform ciphertext), within `|Attr| (δ₁ + ε_fl + δ_T) + δ₄ + |Attr| (δ₅ + δ_T)`, where
`δ₄` is the advantage of the experiment-as-distinguisher on circular Ring-LWE instances.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix Cslib Cslib.Probability AdvancedEncryption.PE
open scoped ENNReal

variable {R : Type} [CommRing R] [Fintype R] [DecidableEq R] {S : Setting R} {Wb J Pos : Type}
  [Fintype Wb] [DecidableEq Wb] [Nonempty Wb] [Fintype J] [DecidableEq J] [Fintype Pos]
  [DecidableEq Pos]

instance finiteMPK : Finite (MPK S Wb J Pos) :=
  @Finite.of_injective _ _
    (@Finite.of_fintype _ (@instFintypeProd _ _ inferInstance (@instFintypeProd _ _ inferInstance
      (@instFintypeProd _ _ inferInstance (@instFintypeProd _ _ inferInstance
        (@instFintypeProd _ _ inferInstance (@instFintypeProd _ _ inferInstance inferInstance)))))))
    (fun m : MPK S Wb J Pos => (m.B, m.H, m.a, m.A0, m.Ain, m.Aaut, m.d))
    (by rintro ⟨⟩ ⟨⟩ h; simp_all)

instance finiteCiphertext : Finite (Ciphertext S Wb J Pos) :=
  @Finite.of_injective _ _
    (@Finite.of_fintype _ (@instFintypeProd _ _ inferInstance (@instFintypeProd _ _ inferInstance
      (@instFintypeProd _ _ inferInstance (@instFintypeProd _ _ inferInstance
        (@instFintypeProd _ _ inferInstance (@instFintypeProd _ _ inferInstance inferInstance)))))))
    (fun c : Ciphertext S Wb J Pos => (c.b, c.h, c.caut, c.cinBot, c.cin, c.c0, c.cm))
    (by rintro ⟨⟩ ⟨⟩ h; simp_all)

/-- The challenge for the message `m` from the challenge for `0`: `c_m + ⌊q/2⌉ m`. -/
def shiftCT (half m : R) (ct : Ciphertext S Wb J Pos) : Ciphertext S Wb J Pos :=
  { ct with cm := ct.cm + half * m }

theorem encrypt_shift (M : HelperMap S J) (w : ℕ) (half : R) (mpk : MPK S Wb J Pos) (x : Pos → ℕ)
    (m : R) (r : EncCoins S Wb J Pos) :
    encrypt M w half mpk x m r = shiftCT half m (encrypt M w half mpk x 0 r) := by
  simp [encrypt, shiftCT]

/-- **The simulator's ciphertext absorbs the message**: a uniform `c_m` shifted is uniform. -/
theorem ctU_shift (half m : R) : (ctU S Wb J Pos).map (shiftCT half m) = ctU S Wb J Pos := by
  unfold ctU
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, shiftCT]
  refine congrArg (PMF.bind _) (funext fun b => congrArg (PMF.bind _) (funext fun h => ?_))
  exact uniform_bind_add (half * m) (fun cm =>
    (PMF.uniformOfFintype (Pos → Col S.τ → R)).bind fun cb =>
    (PMF.uniformOfFintype (Col S.τ → R)).bind fun c0 =>
    (PMF.uniformOfFintype (Pos → Dig S.τ → Col S.τ → R)).bind fun cin =>
    (PMF.uniformOfFintype (Fin S.b → Dig S.τ → Col S.τ → R)).map fun caut =>
      (⟨b, h, caut, cb, cin, c0, cm⟩ : Ciphertext S Wb J Pos))

variable (U : Universe) [Fintype U.Attr] [DecidableEq U.Attr] (half : R) (msgOf : U.Msg → R)
  (encMPK : MPK S Wb J Pos → List Bool) (encCT : Ciphertext S Wb J Pos → List Bool)
  (KGi : MPK S Wb J Pos → List Bool → PMF (List Bool)) (authB : List Bool → U.Attr → Bool)

/-- The challenger with the secret `(mpk, ct₀)` drawn from `V x`. -/
noncomputable def specV (V : U.Attr → PMF (MPK S Wb J Pos × Ciphertext S Wb J Pos)) :
    Generic.Spec U (MPK S Wb J Pos × Ciphertext S Wb J Pos) where
  setup := V
  pub σ := encMPK σ.1
  key σ := KGi σ.1
  chal σ μ := PMF.pure (encCT (shiftCT half (msgOf μ) σ.2))
  auth := authB

/-- The observable law of the experiment of the program `prog` against `specV V`. -/
noncomputable def gameV {α : Type} (prog : ProbOracleComp (fun _ : Fin 3 × List Bool => List Bool) α)
    (V : U.Attr → PMF (MPK S Wb J Pos × Ciphertext S Wb J Pos)) :=
  (ProbOracleComp.runWith (Generic.oracle (specV U half msgOf encMPK encCT KGi authB V)) prog
    ({} : Generic.GState U (MPK S Wb J Pos × Ciphertext S Wb J Pos))).map Generic.obs

/-- A statistical step of the experiment. -/
theorem gameV_close {α : Type} (prog : ProbOracleComp (fun _ : Fin 3 × List Bool => List Bool) α)
    {V V' : U.Attr → PMF (MPK S Wb J Pos × Ciphertext S Wb J Pos)} {ε : ℝ≥0∞}
    (h : ∀ x, CloseTo (V x) (V' x) ε) :
    CloseTo (gameV U half msgOf encMPK encCT KGi authB prog V)
      (gameV U half msgOf encMPK encCT KGi authB prog V') (Fintype.card U.Attr * ε) := by
  unfold gameV
  have := Generic.closeTo_runWith_setup (specV U half msgOf encMPK encCT KGi authB V) prog V'
    (fun _ => ε) h
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
  exact this.map _

/-- An assumption step of the experiment: an average over one instance. -/
theorem gameV_bind {α : Type} (prog : ProbOracleComp (fun _ : Fin 3 × List Bool => List Bool) α)
    {Inst : Type} (inst : PMF Inst) (F : U.Attr → Inst → PMF (MPK S Wb J Pos × Ciphertext S Wb J Pos)) :
    gameV U half msgOf encMPK encCT KGi authB prog (fun x => inst.bind (F x)) =
      inst.bind fun i => gameV U half msgOf encMPK encCT KGi authB prog fun x => F x i := by
  unfold gameV
  exact Generic.runWith_bind_setup (specV U half msgOf encMPK encCT KGi authB fun x => inst.bind (F x))
    inst F prog

/-! ### The chain -/

variable (M : HelperMap S J) (w : ℕ) (χs χ χfl : PMF R) (attrOf : U.Attr → Pos → ℕ)

/-- **Theorem 2, the chain**: for every program (adversary with its oracles) and every continuation
`Dc` of its observable output, the real experiment (`hyb0`: `Setup`, `Enc`) and the ideal one
(`idealView`: `Setup`'s public key, the simulator's uniform ciphertext) are within
`|Attr| (δ₁ + ε_fl + δ_T) + δ₄ + |Attr| (δ₅ + δ_T)`, where `ε_fl` is the flooding distance and
`δ₄` the circular Ring-LWE advantage of the experiment-as-distinguisher run on the reduction `red`. -/
theorem chain {α β : Type} (prog : ProbOracleComp (fun _ : Fin 3 × List Bool => List Bool) α)
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
      (Fintype.card U.Attr * delta1 S Wb Pos + Fintype.card U.Attr * εfl +
        Fintype.card U.Attr * deltaT S Wb + δ₄ + Fintype.card U.Attr * delta5 S Wb Pos +
        Fintype.card U.Attr * deltaT S Wb) := by
  have g01 := (gameV_close U half msgOf encMPK encCT KGi authB prog
    (fun x => hybrid01_close (Wb := Wb) M w half χs χ χfl (attrOf x))).bind_left Dc
  have g12 := (gameV_close U half msgOf encMPK encCT KGi authB prog
    (fun x => hybrid2_close (Wb := Wb) M w half χs χ χfl (attrOf x) hflood)).bind_left Dc
  have g23 := (gameV_close U half msgOf encMPK encCT KGi authB prog
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
  have g45 := (gameV_close U half msgOf encMPK encCT KGi authB prog
    (fun x => (hyb4_eq_L (Wb := Wb) M w χfl (attrOf x)) ▸ hybrid45_close (Wb := Wb) M w χfl (attrOf x))).bind_left Dc
  have g56 := (gameV_close U half msgOf encMPK encCT KGi authB prog
    (fun x => (hyb5_eq_final (Wb := Wb) M w χfl (attrOf x)).symm ▸
      (idealView_eq (S := S) (Wb := Wb) (J := J) (Pos := Pos)).symm ▸ hybrid56_close)).bind_left Dc
  exact ((((g01.trans g12).trans g23).trans g34).trans g45).trans g56

end AdvancedEncryption.ExpLUT
