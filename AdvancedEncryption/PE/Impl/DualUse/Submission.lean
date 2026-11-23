import PE.Impl.DualUse.AHFinal
import PE.Impl.DualUse.ImplP
import PE.Impl.DualUse.Prog.CfX
import PE.Impl.DualUse.Prog.WfB2CoinFree
import PE.Impl.DualUse.Prog.CompCost
import PE.Impl.DualUse.Prog.CostConf
import PE.Impl.DualUse.Prog.DescConf
import PE.Impl.DualUse.Params.Strength
import SigabaNeo.Trusted.Submission

/-!
# The submission for the date-window predicate encryption

`submission`: the compiled implementation `implC` of the Ring-LWE scheme at `confP`
(`N = 2^34`, `K = 2^25`, `k = K + 1`, `d = 2^61`), with the χ sampler `chiSamplerP`, the key-row
block `bfX … (wfB2 …)` and the `c_f̂` block `cfX … (wfB2 …)`; attribute hiding rests on decision
Ring-LWE at the parameters of hybrids 3 and 5 with `2645` bits each, correctness and
expressiveness on nothing. The claimed cost is `N = 2^8001`.

* `spec_submission`: the final statement `Spec` (`correct_conf`, `attributeHiding_conf_rlwe`,
  `expressive_conf`, and the cost from the closed bounds of the four clocks and description
  lengths: `time_setupMP_conf` `≤ 2^3200`, `time_keyMachineP_conf` `≤ 2^4200`,
  `time_encMP_conf` `≤ 2^8000`, `time_decMachineP_conf` `≤ 2^4200`, the description lengths
  `≤ 2^1000`);
* `valid_submission`: every premise is valid at the initial strengths of the registry
  (`2645 ≤ 2650 ≤ RingLWE.H`, `ringLWE_H_registry3/5`).
-/

namespace AdvancedEncryption.DualUse.Sub

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Tape AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow
open AdvancedEncryption.DualUse.Prog AdvancedEncryption.DualUse.Params
open AdvancedEncryption.DualUse.Params.Strength

theorem confP_d3 : 3 ≤ confP.d := by show 3 ≤ dp; rw [dp_def]; norm_num

theorem hS_conf : lenKA hkp confP + Np * Kp ≤ lenZ confP := lenKA_conf

theorem hK2 : 2 ≤ Kp := by rw [Kp_def]; norm_num

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

/-- **The compiled implementation** at `confP`. -/
noncomputable def implC : Impl PE.sig :=
  implP hkp confP chiSamplerP (bfSpec_bfX confP_d3 wfSpec_wfB2_confP)
    (cfSpec_cfX confP_d3 hS_conf wfSpec_wfB2_confP (coinFree_wfB2 hkp confP WB2.Wc)) cfP cfP_valid hK2

/-- The premise of decision Ring-LWE at the parameters of hybrid 3. -/
noncomputable def prem3 : Premise registry :=
  ⟨AName.ringLWE, (params3 Np (2 ^ Kp) kp (.cbd 16) : RingLWE.Params), 2645⟩

/-- The premise of decision Ring-LWE at the parameters of hybrid 5. -/
noncomputable def prem5 : Premise registry :=
  ⟨AName.ringLWE, (params5 Np (2 ^ Kp) kp (Fin confP.d) (.cbd 16) : RingLWE.Params), 2645⟩

/-- The premises of each proposition. -/
noncomputable def deps : PropIndex → List (Premise registry)
  | .correctness => []
  | .attributeHiding => [prem3, prem5]
  | .expressiveness => []

/-- The claimed cost. -/
def Ncost : ℕ := 2 ^ 8001

/-- **The submission.** -/
noncomputable def submission : Submission DateWindow.primitive registry where
  impl := implC
  deps := deps
  N := Ncost

/-! ### The final statement -/

set_option exponentiation.threshold 9000 in
theorem cost_arith {a b c d e f g h : ℕ} (ha : a ≤ 2 ^ 3200) (hb : b ≤ 2 ^ 4200) (hc : c ≤ 2 ^ 8000)
    (hd : d ≤ 2 ^ 4200) (he : e ≤ 2 ^ 300) (hf : f ≤ 2 ^ 1000) (hg : g ≤ 2 ^ 300)
    (hh : h ≤ 2 ^ 1000) : a + 1 * b + 1 * (c + d) + (e + f + g + h) ≤ 2 ^ 8001 :=
  calc a + 1 * b + 1 * (c + d) + (e + f + g + h)
      ≤ 2 ^ 3200 + 1 * 2 ^ 4200 + 1 * (2 ^ 8000 + 2 ^ 4200) + (2 ^ 300 + 2 ^ 1000 + 2 ^ 300 + 2 ^ 1000) := by
        gcongr
    _ ≤ 2 ^ 8001 := by norm_num

theorem e_setup : implC.machine .setup = setupMP hkp confP chiSamplerP := rfl
theorem e_key : implC.machine .keyGen =
    keyMachineP hkp confP (bfX hkp confP (wfB2 hkp confP WB2.Wc)) WB2.Wc cfP := rfl
theorem e_enc : implC.machine .enc = encMP hkp confP chiSamplerP := rfl
theorem e_dec : implC.machine .dec =
    decMachineP hkp confP (cfX hkp confP (wfB2 hkp confP WB2.Wc)) WB2.Wc := rfl

/-- The cost at `params` (one run of each algorithm). -/
theorem cost_le_of {impl : Impl PE.sig} {T : ℕ}
    (h : (impl.machine .setup).time + 1 * (impl.machine .keyGen).time +
      1 * ((impl.machine .enc).time + (impl.machine .dec).time) +
      ((impl.machine .setup).descLen + (impl.machine .keyGen).descLen +
        (impl.machine .enc).descLen + (impl.machine .dec).descLen) ≤ T) :
    PE.cost params impl ≤ T := h

/-- **The cost of the implementation** at `confP` is at most `2^8001`. -/
theorem cost_implC : PE.cost params implC ≤ 2 ^ 8001 := by
  refine cost_le_of ?_
  rw [e_setup, e_key, e_enc, e_dec]
  exact cost_arith time_setupMP_conf time_keyMachineP_conf time_encMP_conf time_decMachineP_conf
    descLen_setupMP_conf descLen_keyMachineP_conf descLen_encMP_conf descLen_decMachineP_conf

/-- `Spec` from its four parts, for any submission. -/
theorem spec_of {u : Submission DateWindow.primitive registry}
    (hc : Correct dateUniverse params u.impl)
    (ha : (∀ d ∈ u.deps .attributeHiding, d.Holds) → AttributeHiding dateUniverse params u.impl)
    (he : Expressive dateUniverse params u.impl) (hcost : PE.cost params u.impl ≤ u.N) :
    Spec DateWindow.primitive registry u := by
  refine ⟨fun i hi => ?_, hcost⟩
  cases i with
  | correctness => exact hc
  | attributeHiding => exact ha hi
  | expressiveness => exact he

/-- The machines of `implC`. -/
noncomputable abbrev msC : Machines hkp confP :=
  machinesP hkp confP chiSamplerP (bfSpec_bfX confP_d3 wfSpec_wfB2_confP)
    (cfSpec_cfX confP_d3 hS_conf wfSpec_wfB2_confP (coinFree_wfB2 hkp confP WB2.Wc)) cfP cfP_valid hK2

theorem implC_eq : implC = impl hkp confP msC := rfl

theorem correct_implC : Correct dateUniverse params implC := by
  rw [implC_eq]; exact correct_conf

theorem expressive_implC : Expressive dateUniverse params implC := by
  rw [implC_eq]; exact expressive_conf

theorem attributeHiding_implC (h3 : prem3.Holds) (h5 : prem5.Holds) :
    AttributeHiding dateUniverse params implC := by
  rw [implC_eq]; exact attributeHiding_conf_rlwe 2645 le_rfl h3 h5

theorem submission_impl : submission.impl = implC := rfl
theorem submission_N : submission.N = Ncost := rfl
theorem submission_deps : submission.deps .attributeHiding = [prem3, prem5] := rfl

/-- **The final statement of the submission.** -/
theorem spec_submission : Spec DateWindow.primitive registry submission := by
  refine spec_of ?_ ?_ ?_ ?_
  · rw [submission_impl]; exact correct_implC
  · intro h
    rw [submission_deps] at h
    rw [submission_impl]
    exact attributeHiding_implC (h prem3 (List.mem_cons_self ..))
      (h prem5 (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · rw [submission_impl]; exact expressive_implC
  · rw [submission_impl, submission_N]; exact cost_implC

/-- **The submission is valid** at the initial strengths of the registry. -/
theorem valid_submission : submission.Valid (Registry.initial assumptions) := by
  intro i d hd
  cases i with
  | correctness => exact absurd hd (List.not_mem_nil)
  | expressiveness => exact absurd hd (List.not_mem_nil)
  | attributeHiding =>
    rw [submission_deps] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · show 2645 ≤ RingLWE.H (params3 Np (2 ^ Kp) kp (.cbd 16))
      rw [params3_conf]; exact le_trans (by norm_num) ringLWE_H_registry3
    · show 2645 ≤ RingLWE.H (params5 Np (2 ^ Kp) kp (Fin confP.d) (.cbd 16))
      rw [params5_conf]; exact le_trans (by norm_num) ringLWE_H_registry5

end AdvancedEncryption.DualUse.Sub
