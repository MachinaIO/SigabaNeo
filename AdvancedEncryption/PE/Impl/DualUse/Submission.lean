import PE.Impl.DualUse.AHConcrete
import PE.Impl.DualUse.ImplBP
import PE.Impl.DualUse.Relaxed
import PE.Impl.DualUse.Prog.SetupConfA
import PE.Impl.DualUse.Prog.EncConfA
import PE.Impl.DualUse.Prog.KeyTightConf
import PE.Impl.DualUse.Prog.KeySize
import PE.Impl.DualUse.Prog.DecTightConf
import PE.Impl.DualUse.Prog.DecSize
import PE.Impl.DualUse.Prog.KeyCostV
import PE.Impl.DualUse.Params.Strength
import SigabaNeo.Trusted.Submission

/-!
# The submission for predicate encryption for branching programs

The width chosen is `w8` (16 symbols of 8 bits); the implementation's predicates are the programs on
14-bit states of `PE/Impl/Gates/BP14.lean` (`univ w8` field by field, `Relaxed`), compiled to mux
trees of depth at most `478` (`depth_bpPred`).

`submission`: the compiled implementation `implC` (`ImplBP`) of the Ring-LWE scheme at `confP`
(`N = 2^34`, `K = 2^26`, `k = K + 1`, `d = 2^62`, depth `≤ 478`), with the χ sampler
`chiSamplerP`, the key-row block `bfX … wfC` and the `c_f̂` block `cfX … wfC` around the stream
block `wfC`; attribute hiding rests on decision Ring-LWE at the parameters of hybrids 3 and 5 with
**`965` bits** each, correctness and expressiveness on nothing. The claimed cost is `N = 2^677`.

* `spec_submission`: the final statement `Spec` (`correct_implC`, `expressive_implC`,
  `attributeHiding_conf_rlwe`, and `cost_implC`: clocks `Setup ≤ 2^371`, `KeyGen ≤ 2^629`,
  `Enc ≤ 2^452`, `Dec ≤ 2^629` steps, description lengths `≤ 2^300`, `≤ 2^615`, `≤ 2^300`,
  `≤ 2^676` bits);
* `valid_submission`: every premise is valid at the initial strengths of the registry
  (`965 ≤ 1158 ≤ RingLWE.H`, `ringLWE_H_registry3/5`).
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
def Ncost : ℕ := 2 ^ 677

/-- **The submission.** -/
noncomputable def submission : Submission (BranchingProgram.primitive BranchingProgram.w8) registry where
  impl := implC
  deps := deps
  N := Ncost

/-! ### The cost -/

theorem e_setup : implC.machine .setup = setupMP hkp confP chiSamplerP := rfl
theorem e_key : implC.machine .keyGen = keyMachineP hkp confP bfC cfP := rfl
theorem e_enc : implC.machine .enc = encMP hkp confP chiSamplerP := rfl
theorem e_dec : implC.machine .dec = decMachineP hkp confP cfC := rfl

set_option exponentiation.threshold 2000 in
theorem cost_arith {a b c d e f g h : ℕ} (ha : a ≤ 2 ^ 371) (hb : b ≤ 2 ^ 629) (hc : c ≤ 2 ^ 452)
    (hd : d ≤ 2 ^ 629) (he : e ≤ 2 ^ 300) (hf : f ≤ 2 ^ 615) (hg : g ≤ 2 ^ 300)
    (hh : h ≤ 2 ^ 676) : a + 1 * b + 1 * (c + d) + (e + f + g + h) ≤ 2 ^ 677 :=
  calc a + 1 * b + 1 * (c + d) + (e + f + g + h)
      ≤ 2 ^ 371 + 1 * 2 ^ 629 + 1 * (2 ^ 452 + 2 ^ 629) + (2 ^ 300 + 2 ^ 615 + 2 ^ 300 + 2 ^ 676) := by
        gcongr
    _ ≤ 2 ^ 677 := by norm_num

/-- The cost at `params` (one run of each algorithm). -/
theorem cost_le_of {impl : Impl PE.sig} {T : ℕ}
    (h : (impl.machine .setup).time + 1 * (impl.machine .keyGen).time +
      1 * ((impl.machine .enc).time + (impl.machine .dec).time) +
      ((impl.machine .setup).descLen + (impl.machine .keyGen).descLen +
        (impl.machine .enc).descLen + (impl.machine .dec).descLen) ≤ T) :
    PE.cost BranchingProgram.params impl ≤ T := h

/-- **The cost of the implementation** at `confP` is at most `2^677`: the clocks `Setup ≤ 2^371`
(`time_setupMP_conf'`), `KeyGen ≤ 2^629` (`time_keyMachineP_conf'`), `Enc ≤ 2^452`
(`time_encMP_confT`), `Dec ≤ 2^629` (`time_decMachineP_conf'`), and the description lengths
`≤ 2^300`, `≤ 2^615` (`descLen_keyMachineP_conf`), `≤ 2^300`, `≤ 2^676`
(`descLen_decMachineP_conf`). -/
theorem cost_implC : PE.cost BranchingProgram.params implC ≤ 2 ^ 677 := by
  refine cost_le_of ?_
  rw [e_setup, e_key, e_enc, e_dec]
  exact cost_arith time_setupMP_conf' time_keyMachineP_conf' time_encMP_confT
    time_decMachineP_conf' descLen_setupMP_conf descLen_keyMachineP_conf descLen_encMP_conf
    descLen_decMachineP_conf

/-! ### The final statement -/

/-- `Spec` from its four parts, for any submission. -/
theorem spec_of {u : Submission (BranchingProgram.primitive BranchingProgram.w8) registry}
    (hc : Correct PUniv BranchingProgram.params u.impl)
    (ha : (∀ d ∈ u.deps .attributeHiding, d.Holds) →
      AttributeHiding PUniv BranchingProgram.params u.impl)
    (he : Expressive PUniv BranchingProgram.params u.impl)
    (hcost : PE.cost BranchingProgram.params u.impl ≤ u.N) :
    Spec (BranchingProgram.primitive BranchingProgram.w8) registry u := by
  refine ⟨fun i hi => ?_, hcost⟩
  cases i with
  | correctness => exact (Relaxed.correct_iff _).mpr hc
  | attributeHiding => exact (Relaxed.attributeHiding_iff _).mpr (ha hi)
  | expressiveness => exact Relaxed.expressive_of he

/-- **Attribute hiding of `implC`** from the two premises (decision Ring-LWE at `965` bits), given
the cost of the reductions' key component (`KeyRConfA`). -/
theorem attributeHiding_implC (hkey : KeyRConfA) (h3 : prem3.Holds) (h5 : prem5.Holds) :
    AttributeHiding PUniv BranchingProgram.params implC := by
  rw [implC_eq]; exact attributeHiding_conf_rlwe hkey kbA le_rfl h3 h5

theorem submission_impl : submission.impl = implC := rfl
theorem submission_N : submission.N = Ncost := rfl
theorem submission_deps : submission.deps .attributeHiding = [prem3, prem5] := rfl

/-- **The final statement of the submission.** -/
theorem spec_submission :
    Spec (BranchingProgram.primitive BranchingProgram.w8) registry submission := by
  refine spec_of ?_ ?_ ?_ ?_
  · rw [submission_impl]; exact correct_implC
  · intro h
    rw [submission_deps] at h
    rw [submission_impl]
    exact attributeHiding_implC keyRConfA (h prem3 (List.mem_cons_self ..))
      (h prem5 (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · rw [submission_impl]; exact expressive_implC
  · rw [submission_impl, submission_N]; exact cost_implC

/-- **The submission is valid** at the initial strengths of the registry: `965 ≤ 1158 ≤ RingLWE.H`
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
