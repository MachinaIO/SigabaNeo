import PE.Impl.ExpLUT.Prog.Words
import PE.Impl.Gates.Eval
import SigabaNeoStd.Machines.FromPolyTime
import Mathlib.Data.Set.Finite.List

/-!
# `Eval` of the ExpLUT implementation

**`Eval`** (`evalMachineX`) on `(pw, C, x)`: `[true]` iff `C` is a predicate word (`predLen` bits),
`x` encodes an attribute and the program of `C` outputs `false` on it. The function is constant
outside finitely many inputs, so it is computed by a deterministic machine
(`Machine.exists_of_almostConst`); `Eval` is not counted in the cost of predicate encryption.

* `authorized_iff`: `C` is authorized for `x` iff `C.length = predLen` and
  `(progOf C).output x = false`.
* `expressive`: every program `F` is the predicate word `predWord F`, authorized exactly where
  `F(x) = 0` (`progOf_predWord`).
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open AdvancedEncryption.PE.Gates

open Classical in
/-- `Eval` on the tuple `(pw, C, x)`. -/
noncomputable def evalFunX (xs : List (List Bool)) : List (List Bool) :=
  [[decide (xs = [pwW, xs.getD 1 [], xs.getD 2 []]) && decide ((xs.getD 1 []).length = predLen) &&
    match PE.decode (encAttribute w8) (xs.getD 2 []) with
    | some x => !(progOf (xs.getD 1 [])).output x
    | none => false]]

theorem decode_encAttribute (x : Attribute w8) :
    PE.decode (encAttribute w8) (encAttribute w8 x) = some x := by
  classical
  have h : ∃ a, encAttribute w8 a = encAttribute w8 x := ⟨x, rfl⟩
  rw [PE.decode, dif_pos h]
  exact congrArg some ((encAttribute w8).injective (Classical.choose_spec h))

theorem evalFunX_almostConst : ∃ b, {xs | evalFunX xs ≠ b}.Finite := by
  classical
  refine ⟨[[false]], Set.Finite.subset
    ((List.finite_length_le Bool predLen).prod (Set.finite_range (encAttribute w8)) |>.image
      fun p => [pwW, p.1, p.2]) fun xs hxs => ?_⟩
  by_contra hn
  apply hxs
  unfold evalFunX
  by_cases h1 : xs = [pwW, xs.getD 1 [], xs.getD 2 []]
  · by_cases h2 : (xs.getD 1 []).length = predLen
    · rcases hd : PE.decode (encAttribute w8) (xs.getD 2 []) with _ | x
      · simp
      · exfalso; apply hn
        refine ⟨(xs.getD 1 [], xs.getD 2 []), ⟨h2.le, x, ?_⟩, h1.symm⟩
        unfold PE.decode at hd
        split_ifs at hd with hex
        obtain rfl := Option.some.inj hd
        exact Classical.choose_spec hex
    · rw [decide_eq_false h2, Bool.and_false, Bool.false_and]
  · rw [decide_eq_false h1, Bool.false_and, Bool.false_and]

/-- **The machine of `Eval`.** -/
noncomputable def evalMachineX : Machine :=
  Classical.choose (Machine.exists_of_almostConst (encIn := encTuple) (encOut := encTuple)
    evalFunX_almostConst)

theorem evalMachineX_deterministic : evalMachineX.Deterministic :=
  (Classical.choose_spec (Machine.exists_of_almostConst (encIn := encTuple) (encOut := encTuple)
    evalFunX_almostConst)).1

theorem evalMachineX_run (xs : List (List Bool)) :
    evalMachineX.run (encodeTuple xs) = PMF.pure (encodeTuple (evalFunX xs)) :=
  (Classical.choose_spec (Machine.exists_of_almostConst (encIn := encTuple) (encOut := encTuple)
    evalFunX_almostConst)).2 xs

/-- **Authorization**: `C` is authorized for `x` iff it is a predicate word and its program
outputs `false` on `x`. -/
theorem authorized_iff (impl : Impl sig) (h : impl.machine .eval = evalMachineX)
    (C : List Bool) (x : Attribute w8) :
    Authorized (U := univ w8) params impl C x ↔
      C.length = predLen ∧ (progOf C).output x = false := by
  have he : eval (U := univ w8) params impl C x =
      PMF.pure ((evalFunX [paramsWord (univ w8) params, C, encAttribute w8 x]).getD 0 []) := by
    unfold eval Impl.run
    rw [h, evalMachineX_run, PMF.pure_map, PMF.pure_map]
    have : (sig Alg.eval).outputs.length =
        (evalFunX [paramsWord (univ w8) params, C, encAttribute w8 x]).length := rfl
    rw [this]
    exact congrArg (fun l => PMF.pure (List.getD l 0 []))
      (decodeTuple_encodeTuple (evalFunX [paramsWord (univ w8) params, C, encAttribute w8 x]))
  unfold Authorized
  rw [he, PMF.pure_apply]
  have hx : (univ w8).encAttr x = encAttribute w8 x := rfl
  simp only [evalFunX, List.getD_cons_zero, List.getD_cons_succ, decode_encAttribute, pwW]
  by_cases hC : C.length = predLen
  · by_cases ho : (progOf C).output x = false
    · simp [hC, ho]
    · simp [hC, ho]
  · simp [hC]

/-- **Expressiveness**: the word of `F` is authorized exactly where `F` outputs `false`. -/
theorem expressive (impl : Impl sig) (h : impl.machine .eval = evalMachineX) :
    Expressive (univ w8) params impl := by
  intro (F : Program w8)
  refine ⟨predWord F, fun (x : Attribute w8) => ?_⟩
  rw [authorized_iff impl h, progOf_predWord]
  exact ⟨fun h => h.2, fun h' => ⟨length_predWord F, h'⟩⟩

end AdvancedEncryption.ExpLUT.Prog
