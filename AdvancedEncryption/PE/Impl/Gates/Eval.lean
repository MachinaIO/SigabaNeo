import PE
import SigabaNeoStd.Machines.FromPolyTime
import SigabaNeoStd.Machines.Gates
import Mathlib.Data.Set.Finite.List

/-!
# `Eval` for predicates given as gate lists

Predicates are NAND gate lists in the word format of `SigabaNeo.unparse` (each wire index in unary,
ended by `false`), read on the wires `1, x₀, …, x_{n-1}` and then the gates. `Eval(C, x)` outputs
`[true]` (authorized, the paper's `C(x) = 0`) iff its whole input word has length at most `L` and
the last gate of `C` on the bits of `x` is `false` (`authorized_iff`).

**The bound `L`.** Every algorithm runs on a fixed clock, so a scheme can only serve predicates of
bounded size; `Eval` makes this explicit by authorizing no predicate whose input word is longer
than `L`. With it `Eval` is constant outside finitely many inputs, and is computed by cslib's
machine for almost constant functions (`Machine.exists_of_almostConst`). That machine reads the
input against a table; `Eval` is not counted in the cost of predicate encryption.
-/

namespace AdvancedEncryption.PE.Gates

open SigabaNeo

/-- The encoding of tuples of words as an embedding. -/
def encTuple : List (List Bool) ↪ List Bool := ⟨encodeTuple, encodeTuple_injective⟩

/-- `Eval` on the tuple `(pw, C, x)`: authorized iff the input is at most `L` long and the last
gate of `C` on `x` is `false`. -/
def evalFun (L : ℕ) (xs : List (List Bool)) : List (List Bool) :=
  [[decide ((encodeTuple xs).length ≤ L) && !evalGates (xs.getD 2 [], parse (xs.getD 1 []))]]

theorem evalFun_almostConst (L : ℕ) : ∃ b, {xs | evalFun L xs ≠ b}.Finite := by
  refine ⟨[[false]], Set.Finite.subset ((List.finite_length_le Bool L).preimage
    (encodeTuple_injective.injOn)) fun xs hxs => ?_⟩
  by_contra h
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at h
  exact hxs (by simp [evalFun, h])

/-- The machine of `Eval`. -/
noncomputable def evalMachine (L : ℕ) : Machine :=
  Classical.choose (Machine.exists_of_almostConst (encIn := encTuple) (encOut := encTuple)
    (evalFun_almostConst L))

theorem evalMachine_deterministic (L : ℕ) : (evalMachine L).Deterministic :=
  (Classical.choose_spec (Machine.exists_of_almostConst (encIn := encTuple) (encOut := encTuple)
    (evalFun_almostConst L))).1

theorem evalMachine_run (L : ℕ) (xs : List (List Bool)) :
    (evalMachine L).run (encodeTuple xs) = PMF.pure (encodeTuple (evalFun L xs)) :=
  (Classical.choose_spec (Machine.exists_of_almostConst (encIn := encTuple) (encOut := encTuple)
    (evalFun_almostConst L))).2 xs

variable {U : Universe} (p : Params) (impl : Impl sig)

/-- With the machine `evalMachine L`, `Eval` outputs one bit. -/
theorem eval_eq {L : ℕ} (h : impl.machine .eval = evalMachine L) (C : List Bool) (x : U.Attr) :
    eval p impl C x = PMF.pure [decide ((encodeTuple [paramsWord U p, C, U.encAttr x]).length ≤ L)
      && !evalGates (U.encAttr x, parse C)] := by
  unfold eval Impl.run
  rw [h, evalMachine_run, PMF.pure_map, PMF.pure_map]
  have : (sig Alg.eval).outputs.length = (evalFun L [paramsWord U p, C, U.encAttr x]).length :=
    rfl
  rw [this, decodeTuple_encodeTuple]
  rfl

/-- **Authorization** for gate-list predicates. -/
theorem authorized_iff {L : ℕ} (h : impl.machine .eval = evalMachine L) (C : List Bool)
    (x : U.Attr) : Authorized p impl C x ↔
      (encodeTuple [paramsWord U p, C, U.encAttr x]).length ≤ L ∧
        evalGates (U.encAttr x, parse C) = false := by
  unfold Authorized
  rw [eval_eq p impl h, PMF.pure_apply]
  split_ifs with he
  · have := (List.singleton_inj.mp he).symm
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at this
    simpa using this
  · simp only [zero_ne_one, false_iff]
    rintro ⟨h1, h2⟩
    exact he (by simp [h1, h2])

end AdvancedEncryption.PE.Gates
