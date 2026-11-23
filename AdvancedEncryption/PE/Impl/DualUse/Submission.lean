import PE.Impl.DualUse.AHConcrete
import PE.Impl.DualUse.ImplBP
import PE.Impl.DualUse.Prog.SetupConfA
import PE.Impl.DualUse.Prog.EncConfA
import PE.Impl.DualUse.Params.Strength
import SigabaNeo.Trusted.Submission

/-!
# The submission for predicate encryption for branching programs

`submission`: the compiled implementation `implC` (`ImplBP`) of the Ring-LWE scheme at `confP`
(the sizes of `confA`: `N = 2^36`, `K = 2^27`, `k = K + 1`, `d = 2^65`), with the χ sampler
`chiSamplerP`, the key-row block `bfX … wfC` and the `c_f̂` block `cfX … wfC` around the stream
block `wfC`; attribute hiding rests on decision Ring-LWE at the parameters of hybrids 3 and 5 with
**`965` bits** each, correctness and expressiveness on nothing. The claimed cost is `N = 2^1002`.

* `spec_submission`: the final statement `Spec` (`correct_implC`, `expressive_implC`,
  `attributeHiding_conf`, and the cost from the clocks and description lengths: `Setup`
  `≤ 2^387`, `Enc` `≤ 2^452` steps, both `≤ 2^300` description bits, proved; `KeyGen` and `Dec`
  from the hypothesis `KeyDecCost`);
* `valid_submission`: every premise is valid at the initial strengths of the registry
  (`965 ≤ 2650 ≤ RingLWE.H`, `ringLWE_H_registry3/5`).

**The remaining hypotheses** (the cost workstreams of `KeyGen` and `Dec`, not yet merged):

* `KeyDecCost`: `KeyGen` and `Dec` of `implC` take at most `2^700` steps and have description
  lengths at most `2^1000` (expected `≤ 2^629` and `≤ 2^951`, `BP_PLAN.md` §6);
* `KeyRConfA` (`AHConcrete`): the cost of the reductions' key component (`KeyRCost`), the same
  shell around the same block as `KeyGen`.
-/

namespace AdvancedEncryption.DualUse.Sub

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Tape AdvancedEncryption.PE
open AdvancedEncryption.DualUse.Prog AdvancedEncryption.DualUse.Params
open AdvancedEncryption.DualUse.Params.Strength

/-! ### The registry -/

/-- The names of the registered assumptions. -/
inductive AName where
  | ringLWE

/-- The registered assumptions: decision Ring-LWE. -/
noncomputable def assumptions : AName → Assumption
  | .ringLWE => RingLWE.decision

/-- The registry. -/
noncomputable abbrev registry : Registry := Registry.of assumptions

/-! ### The submission -/

/-- The strength asked of Ring-LWE: `965` bits (`kb_confA`). -/
abbrev kbA : ℕ := 965

/-- The premise of decision Ring-LWE at the parameters of hybrid 3. -/
noncomputable def prem3 : Premise registry :=
  ⟨AName.ringLWE, (params3 Np (2 ^ Kp) kp (.cbd 16) : RingLWE.Params), kbA⟩

/-- The premise of decision Ring-LWE at the parameters of hybrid 5. -/
noncomputable def prem5 : Premise registry :=
  ⟨AName.ringLWE, (params5 Np (2 ^ Kp) kp (Fin confP.d) (.cbd 16) : RingLWE.Params), kbA⟩

/-- The premises of each proposition. -/
noncomputable def deps : PropIndex → List (Premise registry)
  | .correctness => []
  | .attributeHiding => [prem3, prem5]
  | .expressiveness => []

/-- The claimed cost. -/
def Ncost : ℕ := 2 ^ 1002

/-- **The submission.** -/
noncomputable def submission : Submission BranchingProgram.primitive registry where
  impl := implC
  deps := deps
  N := Ncost

/-! ### The cost -/

theorem e_setup : implC.machine .setup = setupMP hkp confP chiSamplerP := rfl
theorem e_key : implC.machine .keyGen = keyMachineP hkp confP bfC cfP := rfl
theorem e_enc : implC.machine .enc = encMP hkp confP chiSamplerP := rfl
theorem e_dec : implC.machine .dec = decMachineP hkp confP cfC := rfl

/-- **The clocks and description lengths of `KeyGen` and `Dec` of `implC`** (the hypothesis of the
cost; expected `≤ 2^629` steps and `≤ 2^951` description bits). -/
structure KeyDecCost : Prop where
  keyTime : (keyMachineP hkp confP bfC cfP).time ≤ 2 ^ 700
  decTime : (decMachineP hkp confP cfC).time ≤ 2 ^ 700
  keyDesc : (keyMachineP hkp confP bfC cfP).descLen ≤ 2 ^ 1000
  decDesc : (decMachineP hkp confP cfC).descLen ≤ 2 ^ 1000

set_option exponentiation.threshold 2000 in
theorem cost_arith {a b c d e f g h : ℕ} (ha : a ≤ 2 ^ 387) (hb : b ≤ 2 ^ 700) (hc : c ≤ 2 ^ 452)
    (hd : d ≤ 2 ^ 700) (he : e ≤ 2 ^ 300) (hf : f ≤ 2 ^ 1000) (hg : g ≤ 2 ^ 300)
    (hh : h ≤ 2 ^ 1000) : a + 1 * b + 1 * (c + d) + (e + f + g + h) ≤ 2 ^ 1002 :=
  calc a + 1 * b + 1 * (c + d) + (e + f + g + h)
      ≤ 2 ^ 387 + 1 * 2 ^ 700 + 1 * (2 ^ 452 + 2 ^ 700) + (2 ^ 300 + 2 ^ 1000 + 2 ^ 300 + 2 ^ 1000) := by
        gcongr
    _ ≤ 2 ^ 1002 := by norm_num

/-- The cost at `params` (one run of each algorithm). -/
theorem cost_le_of {impl : Impl PE.sig} {T : ℕ}
    (h : (impl.machine .setup).time + 1 * (impl.machine .keyGen).time +
      1 * ((impl.machine .enc).time + (impl.machine .dec).time) +
      ((impl.machine .setup).descLen + (impl.machine .keyGen).descLen +
        (impl.machine .enc).descLen + (impl.machine .dec).descLen) ≤ T) :
    PE.cost BranchingProgram.params impl ≤ T := h

/-- **The cost of the implementation** at `confP` is at most `2^1002`, from the clocks and
description lengths of `KeyGen` and `Dec` (`KeyDecCost`); those of `Setup` and `Enc` are proved
(`time_setupMP_conf'`, `time_encMP_confT`, `descLen_setupMP_conf`, `descLen_encMP_conf`). -/
theorem cost_implC (hKD : KeyDecCost) : PE.cost BranchingProgram.params implC ≤ 2 ^ 1002 := by
  refine cost_le_of ?_
  rw [e_setup, e_key, e_enc, e_dec]
  exact cost_arith time_setupMP_conf' hKD.keyTime time_encMP_confT hKD.decTime
    descLen_setupMP_conf hKD.keyDesc descLen_encMP_conf hKD.decDesc

/-! ### The final statement -/

/-- `Spec` from its four parts, for any submission. -/
theorem spec_of {u : Submission BranchingProgram.primitive registry}
    (hc : Correct PUniv BranchingProgram.params u.impl)
    (ha : (∀ d ∈ u.deps .attributeHiding, d.Holds) →
      AttributeHiding PUniv BranchingProgram.params u.impl)
    (he : Expressive PUniv BranchingProgram.params u.impl)
    (hcost : PE.cost BranchingProgram.params u.impl ≤ u.N) :
    Spec BranchingProgram.primitive registry u := by
  refine ⟨fun i hi => ?_, hcost⟩
  cases i with
  | correctness => exact hc
  | attributeHiding => exact ha hi
  | expressiveness => exact he

/-- **Attribute hiding of `implC`** from the two premises (decision Ring-LWE at `965` bits), given
the cost of the reductions' key component (`KeyRConfA`). -/
theorem attributeHiding_implC (hkey : KeyRConfA) (h3 : prem3.Holds) (h5 : prem5.Holds) :
    AttributeHiding PUniv BranchingProgram.params implC := by
  rw [implC_eq]; exact attributeHiding_conf_rlwe hkey kbA le_rfl h3 h5

theorem submission_impl : submission.impl = implC := rfl
theorem submission_N : submission.N = Ncost := rfl
theorem submission_deps : submission.deps .attributeHiding = [prem3, prem5] := rfl

/-- **The final statement of the submission**, given the cost of `KeyGen` and `Dec`
(`KeyDecCost`) and of the reductions' key component (`KeyRConfA`). -/
theorem spec_submission (hkey : KeyRConfA) (hKD : KeyDecCost) :
    Spec BranchingProgram.primitive registry submission := by
  refine spec_of ?_ ?_ ?_ ?_
  · rw [submission_impl]; exact correct_implC
  · intro h
    rw [submission_deps] at h
    rw [submission_impl]
    exact attributeHiding_implC hkey (h prem3 (List.mem_cons_self ..))
      (h prem5 (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · rw [submission_impl]; exact expressive_implC
  · rw [submission_impl, submission_N]; exact cost_implC hKD

/-- **The submission is valid** at the initial strengths of the registry: `965 ≤ 2650 ≤ RingLWE.H`
at both instances. -/
theorem valid_submission : submission.Valid (Registry.initial assumptions) := by
  intro i d hd
  cases i with
  | correctness => exact absurd hd (List.not_mem_nil)
  | expressiveness => exact absurd hd (List.not_mem_nil)
  | attributeHiding =>
    rw [submission_deps] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact registry_covers_kb.1
    · exact registry_covers_kb.2

end AdvancedEncryption.DualUse.Sub
