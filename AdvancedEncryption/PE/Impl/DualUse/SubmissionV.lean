import PE.Impl.DualUse.Submission
import PE.Impl.DualUse.AHConcreteV

/-!
# A variant of the submission with `952`-bit premises

`Submission` asks decision Ring-LWE at `2645` bits at the parameters of hybrids 3 and 5. With the
reductions' components bounded per tape (`AHConcreteV`: every reduction's constant at most
`2^690`), `952` bits suffice. `submissionV` is the same implementation `implC`, cost `2^1002`, with
the premises `prem3V`, `prem5V` at `952` bits.

* `spec_submissionV`: the final statement `Spec`;
* `valid_submissionV`: valid at the initial strengths of the registry (`952 ≤ 2650 ≤ RingLWE.H`).
-/

namespace AdvancedEncryption.DualUse.Sub

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Tape AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow
open AdvancedEncryption.DualUse.Prog AdvancedEncryption.DualUse.Params
open AdvancedEncryption.DualUse.Params.Strength

/-- The premise of decision Ring-LWE at the parameters of hybrid 3, at `952` bits. -/
noncomputable def prem3V : Premise registry :=
  ⟨AName.ringLWE, (params3 Np (2 ^ Kp) kp (.cbd 16) : RingLWE.Params), 952⟩

/-- The premise of decision Ring-LWE at the parameters of hybrid 5, at `952` bits. -/
noncomputable def prem5V : Premise registry :=
  ⟨AName.ringLWE, (params5 Np (2 ^ Kp) kp (Fin confP.d) (.cbd 16) : RingLWE.Params), 952⟩

/-- The premises of each proposition. -/
noncomputable def depsV : PropIndex → List (Premise registry)
  | .correctness => []
  | .attributeHiding => [prem3V, prem5V]
  | .expressiveness => []

/-- **The submission with `952`-bit premises.** -/
noncomputable def submissionV : Submission DateWindow.primitive registry where
  impl := implC
  deps := depsV
  N := Ncost

theorem attributeHiding_implCV (h3 : prem3V.Holds) (h5 : prem5V.Holds) :
    AttributeHiding dateUniverse params implC := by
  rw [implC_eq]; exact attributeHiding_conf_rlwe' 952 le_rfl h3 h5

theorem submissionV_deps : submissionV.deps .attributeHiding = [prem3V, prem5V] := rfl

/-- **The final statement of the submission with `952`-bit premises.** -/
theorem spec_submissionV : Spec DateWindow.primitive registry submissionV := by
  refine spec_of ?_ ?_ ?_ ?_
  · exact correct_implC
  · intro h
    rw [submissionV_deps] at h
    exact attributeHiding_implCV (h prem3V (List.mem_cons_self ..))
      (h prem5V (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · exact expressive_implC
  · exact cost_implC

/-- **The submission with `952`-bit premises is valid** at the initial strengths of the
registry. -/
theorem valid_submissionV : submissionV.Valid (Registry.initial assumptions) := by
  intro i d hd
  cases i with
  | correctness => exact absurd hd (List.not_mem_nil)
  | expressiveness => exact absurd hd (List.not_mem_nil)
  | attributeHiding =>
    rw [submissionV_deps] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · show 952 ≤ RingLWE.H (params3 Np (2 ^ Kp) kp (.cbd 16))
      exact registry_covers_kb.1
    · show 952 ≤ RingLWE.H (params5 Np (2 ^ Kp) kp (Fin confP.d) (.cbd 16))
      exact registry_covers_kb.2

end AdvancedEncryption.DualUse.Sub
