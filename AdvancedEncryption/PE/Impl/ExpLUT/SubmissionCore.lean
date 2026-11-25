import PE.Impl.ExpLUT.Prog.KeyTimeFront
import PE.Impl.ExpLUT.Prog.EncTimeConf
import PE.Impl.ExpLUT.Prog.EncTightFront
import PE.Impl.ExpLUT.Prog.SetupConf
import PE.Impl.ExpLUT.Prog.SetupTight
import PE.Impl.ExpLUT.Prog.DescTightEnc
import PE.Impl.ExpLUT.Prog.TapeEncTime
import PE.Impl.ExpLUT.Prog.KeyBoxW
import PE.Impl.ExpLUT.AH.Correct
import PE.Impl.ExpLUT.AH.RedCompsR
import PE.Impl.ExpLUT.AH.Flood
import SigabaNeo.Trusted.Submission

/-!
# Assembling the ExpLUT submission from its parts

The implementation `implE decM` uses the finished machines `setupMP (binSampler Dc)`
(`SetupSpec`, clock `≤ 2^242`, description `≤ 2^249`), `keyMachine` (`KeySpec`, `KeyLongSpec`,
clock `≤ 2^508`, description `≤ 2^620`), `EncConf.encMachine` (`EncSpec`, clock `≤ 2^253` by `EncConf.time_encMachine_tight`,
description `≤ 2^744`) and
`evalMachineX`, with a deterministic `Dec` machine `decM`.

* `registry`: decision circular Ring-LWE (`CircularRingLWE.decision`);
* `prem`: the premise of attribute hiding, `1155` bits at `circParamsD Dc`;
* **`spec_of_parts`**: `Spec` for the submission with any claimed cost `N` bounding `PE.cost`,
  from `DecSpec Dc predLen decM` and reduction components `RawComps` whose constant satisfies
  `64 · 2^256 · const ≤ 2^1155`;
* `cost_implE_le`: the cost from the clocks and description lengths of `Dec`.
-/

namespace AdvancedEncryption.ExpLUT.Sub

open SigabaNeo SigabaNeo.Lattices AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open AdvancedEncryption.ExpLUT AdvancedEncryption.ExpLUT.Prog AdvancedEncryption.ExpLUT.Params

/-! ### The registry -/

/-- The names of the registered assumptions. -/
inductive AName where
  | circularRingLWE

/-- The registered assumptions: decision circular Ring-LWE with automorphism keys. -/
noncomputable def assumptions : AName → Assumption
  | .circularRingLWE => CircularRingLWE.decision

/-- The registry. -/
noncomputable abbrev registry : Registry := Registry.of assumptions

/-- The strength asked of circular Ring-LWE. -/
abbrev kbE : ℕ := 1155

/-- The premise of attribute hiding: circular Ring-LWE at the concrete parameters. -/
noncomputable def prem : Premise registry :=
  ⟨AName.circularRingLWE, (circParamsD Dc : CircularRingLWE.decision.Params), kbE⟩

/-- The premises of each proposition. -/
noncomputable def deps : PropIndex → List (Premise registry)
  | .correctness => []
  | .attributeHiding => [prem]
  | .expressiveness => []

/-! ### The implementation -/

/-- The implementation with the `Dec` machine `decM`. -/
noncomputable def implE (decM : Machine) (hdet : decM.Deterministic) : Impl PE.sig where
  machine
    | .setup => setupMP (binSampler Dc)
    | .enc => TapeEnc.encMachineP
    | .keyGen => KeyCore.keyMachine
    | .dec => decM
    | .eval => evalMachineX
  deterministic a h := by
    cases a
    all_goals first
      | exact absurd h (by decide)
      | exact hdet
      | exact evalMachineX_deterministic

/-- `PE.cost` at `params` (one run of each algorithm) from bounds on each machine. -/
theorem cost_le_parts {impl : Impl PE.sig} {a b c d e f g h : ℕ}
    (ha : (impl.machine .setup).time ≤ a) (hb : (impl.machine .keyGen).time ≤ b)
    (hc : (impl.machine .enc).time ≤ c) (hd : (impl.machine .dec).time ≤ d)
    (he : (impl.machine .setup).descLen ≤ e) (hf : (impl.machine .keyGen).descLen ≤ f)
    (hg : (impl.machine .enc).descLen ≤ g) (hh : (impl.machine .dec).descLen ≤ h) :
    PE.cost params impl ≤ a + 1 * b + 1 * (c + d) + (e + f + g + h) := by
  unfold PE.cost
  show _ + 1 * _ + 1 * (_ + _) + _ ≤ _
  gcongr

section
variable (decM : Machine) (hdet : decM.Deterministic)

theorem implE_setup : (implE decM hdet).machine .setup = setupMP (binSampler Dc) := rfl
theorem implE_enc : (implE decM hdet).machine .enc = TapeEnc.encMachineP := rfl
theorem implE_key : (implE decM hdet).machine .keyGen = KeyCore.keyMachine := rfl
theorem implE_dec : (implE decM hdet).machine .dec = decM := rfl
theorem implE_eval : (implE decM hdet).machine .eval = evalMachineX := rfl

theorem setupSpec_Dc : SetupSpec Dc (χbin Dc) (setupMP (binSampler Dc)) :=
  setupSpec_setupMP (binSampler Dc)

theorem implSpec_implE :
    ImplSpec Dc kbDc predLen (implE decM hdet) χc χc χfl where
  setup := setupSpec_Dc
  enc := TapeEnc.encSpec_encMachineP
  key := KeyCore.keySpec_keyMachine
  keyLong := KeyCore.keyLongSpec_keyMachine
  eval := rfl

/-- **Correctness** given the `Dec` specification. -/
theorem correct_implE (hD : DecSpec Dc predLen decM) :
    Correct (univ w8) params (implE decM hdet) :=
  correct_of_specs (L := predLen) setupSpec_Dc TapeEnc.encSpec_encMachineP KeyCore.keySpec_keyMachine hD
    rfl le_rfl

/-- **Expressiveness.** -/
theorem expressive_implE : Expressive (univ w8) params (implE decM hdet) :=
  expressive _ rfl

/-- **Attribute hiding** from circular Ring-LWE at `1155` bits, given the reduction's components. -/
theorem attributeHiding_implE (rc : RawComps Dc kbDc predLen (implE decM hdet) χfl)
    (hC : 64 * ((2 : ℝ) ^ 128) ^ 2 * ((rc.toRedComps nDc encLen_le_nDc).const : ℝ) ≤
      (2 : ℝ) ^ 1155)
    (hard : CircularRingLWE.decision.HardAt (circParamsD Dc) kbE) :
    AttributeHiding (univ w8) params (implE decM hdet) := by
  have hI := implSpec_implE decM hdet
  have hpos : (0 : ℝ) < (rc.toRedComps nDc encLen_le_nDc).const := by
    have : 0 < (rc.toRedComps nDc encLen_le_nDc).const := by
      unfold RedComps.const chainConst; omega
    exact_mod_cast this
  exact attributeHiding_Dc' hI kbCover_Dc kbE _ hpos hC hard fun A Dm _ =>
    redMachine_of_comps (rc.toRedComps nDc encLen_le_nDc) hI.eval le_rfl le_rfl A Dm

/-- The cost from the four clocks and description lengths. -/
theorem cost_implE_le {T S : ℕ} (hT : decM.time ≤ T) (hS : decM.descLen ≤ S) :
    PE.cost params (implE decM hdet) ≤
      2 ^ 241 + 1 * 2 ^ 508 + 1 * (2 ^ 253 + T) + (2 ^ 233 + 2 ^ 620 + 2 ^ 325 + S) := by
  have hmb : Dc.mb = 3 * 2 ^ 40 + 408 := by
    show mbar = _
    rw [mbar_def, Kc_def]; norm_num [en]
  have hK : Dc.K = 2 ^ 16 := by show Kc = _; rw [Kc_def]
  have hs : ((implE decM hdet).machine .setup).time ≤ 2 ^ 241 := by
    rw [implE_setup]; exact time_setupMP_conf_tight Dc rfl hK rfl hmb
  have hsd : ((implE decM hdet).machine .setup).descLen ≤ 2 ^ 233 := by
    rw [implE_setup]; exact descLen_setupMP_conf_tight Dc rfl hK rfl hmb
  have hk : ((implE decM hdet).machine .keyGen).time ≤ 2 ^ 508 := by
    rw [implE_key]; exact KeyCore.time_keyMachine
  have hkd : ((implE decM hdet).machine .keyGen).descLen ≤ 2 ^ 620 := by
    rw [implE_key]; exact KeyCore.descLen_keyMachine
  have he : ((implE decM hdet).machine .enc).time ≤ 2 ^ 253 := by
    rw [implE_enc]; exact TapeEnc.time_encMachineP
  have hed : ((implE decM hdet).machine .enc).descLen ≤ 2 ^ 325 := by
    rw [implE_enc]; exact TapeEnc.descLen_encMachineP
  have hd : ((implE decM hdet).machine .dec).time ≤ T := by rw [implE_dec]; exact hT
  have hdd : ((implE decM hdet).machine .dec).descLen ≤ S := by rw [implE_dec]; exact hS
  exact cost_le_parts hs hk he hd hsd hkd hed hdd

end

/-! ### The submission -/

/-- **The submission** with the `Dec` machine `decM` and the claimed cost `N`. -/
noncomputable def submissionOf (decM : Machine) (hdet : decM.Deterministic) (N : ℕ) :
    Submission (BranchingProgram.primitive BranchingProgram.w8) registry where
  impl := implE decM hdet
  deps := deps
  N := N

/-- `Spec` from its parts, for any submission. -/
theorem spec_of {u : Submission (BranchingProgram.primitive BranchingProgram.w8) registry}
    (hc : Correct (univ w8) params u.impl)
    (ha : (∀ d ∈ u.deps .attributeHiding, d.Holds) → AttributeHiding (univ w8) params u.impl)
    (he : Expressive (univ w8) params u.impl)
    (hcost : PE.cost params u.impl ≤ u.N) :
    Spec (BranchingProgram.primitive BranchingProgram.w8) registry u := by
  refine ⟨fun i hi => ?_, hcost⟩
  cases i with
  | correctness => exact hc
  | attributeHiding => exact ha hi
  | expressiveness => exact he

theorem submissionOf_impl (decM : Machine) (hdet : decM.Deterministic) (N : ℕ) :
    (submissionOf decM hdet N).impl = implE decM hdet := rfl

theorem submissionOf_deps (decM : Machine) (hdet : decM.Deterministic) (N : ℕ) :
    (submissionOf decM hdet N).deps .attributeHiding = [prem] := rfl

/-- **The final statement from the parts**: the `Dec` specification, the reduction's components
with their constant, and a claimed cost bounding `PE.cost`. -/
theorem spec_of_parts (decM : Machine) (hdet : decM.Deterministic) (N : ℕ)
    (hD : DecSpec Dc predLen decM)
    (rc : RawComps Dc kbDc predLen (implE decM hdet) χfl)
    (hC : 64 * ((2 : ℝ) ^ 128) ^ 2 * ((rc.toRedComps nDc encLen_le_nDc).const : ℝ) ≤
      (2 : ℝ) ^ 1155)
    (hN : PE.cost params (implE decM hdet) ≤ N) :
    Spec (BranchingProgram.primitive BranchingProgram.w8) registry (submissionOf decM hdet N) := by
  refine spec_of ?_ ?_ ?_ ?_
  · rw [submissionOf_impl]; exact correct_implE decM hdet hD
  · intro h
    rw [submissionOf_deps] at h
    rw [submissionOf_impl]
    exact attributeHiding_implE decM hdet rc hC (h prem (List.mem_singleton_self _))
  · rw [submissionOf_impl]; exact expressive_implE decM hdet
  · rw [submissionOf_impl]; exact hN

/-- The premise is valid at the initial strengths: `1155 ≤ H (circParamsD Dc)`. -/
theorem valid_submissionOf (decM : Machine) (hdet : decM.Deterministic) (N : ℕ) :
    (submissionOf decM hdet N).Valid (Registry.initial assumptions) := by
  intro i d hd
  cases i with
  | correctness => exact absurd hd List.not_mem_nil
  | expressiveness => exact absurd hd List.not_mem_nil
  | attributeHiding =>
    have hd' : d = prem := List.mem_singleton.mp hd
    subst hd'
    show kbE ≤ CircularRingLWE.decision.H (circParamsD Dc)
    exact strength_Dc

end AdvancedEncryption.ExpLUT.Sub
