import SigabaNeoStd.Benchmarks.Entropy
import SigabaNeoStd.Benchmarks.Families.AvoidWordDesign
import SigabaNeoStd.Benchmarks.Families.AvoidWordAttack

/-!
# What the acceptance predicates refuse (spec tests L06, L07, L10)

Kernel-checked negative facts about the trusted acceptance predicates on the bootstrap families
(python/tests/test_benchmark.py builds this module and checks these theorems with the trusted
commands' axiom policy):

* L06 (design): a submission over the cap, one whose implementation violates the task's
  proposition, and one with an inflated premise are all refused; `Spec` alone does not solve a
  task.
* L07 (cryptanalysis): a zero-gain machine and a too-expensive one are refused, and a task whose
  refutation claim is not strict (`c = k`) is unsolvable, so its solver target is false.
* L10: a generator that varies only the cap (design) or only the bound `c` (attack) is not
  certified for any `h > 0`.
-/

namespace Generators.Negatives

open SigabaNeo SigabaNeo.Benchmark SigabaNeo.Benchmark.Fixture

/-! ### L06: design -/

/-- `Spec` holds for the halting implementation at the claimed cost `65`, but the task's cap is
`64`: `Spec` alone does not solve a task. -/
theorem spec_without_cap (x : Word) (hx : x.bits ≠ []) :
    Spec (avoidDesign.primitive x) avoidDesign.registry ⟨haltImpl, fun _ => [], 65⟩ ∧
      ¬ avoidDesign.AcceptDesign x ⟨haltImpl, fun _ => [], 65⟩ := by
  refine ⟨⟨fun i _ => ?_, ?_⟩, fun h => ?_⟩
  · show haltImpl.run () x.bits [] [x.bits] = 0
    rw [haltImpl_run, PMF.pure_apply_of_ne]
    intro h
    exact hx (List.cons.inj h).1
  · show haltMachine.cost ≤ 65
    rw [haltMachine_cost]; norm_num
  · have : (65 : ℕ) ≤ 64 := h.2.2
    omega

/-- An implementation that violates the task's proposition (it outputs the forbidden word) is
refused whatever it claims, when it names no premise. -/
theorem wrong_implementation_refused (x : Word) (u : Submission (avoidDesign.primitive x)
    avoidDesign.registry) (hdeps : ∀ i, u.deps i = [])
    (hbad : ¬ avoidDesign.SemanticAccept x u.impl) : ¬ avoidDesign.AcceptDesign x u :=
  fun h => hbad fun i => h.1.1 i (by simp [hdeps i])

/-- A design family like `avoidDesign`, with one registered assumption at pinned strength `3`. -/
noncomputable def oneAssumption : Assumption := ⟨Unit, fun _ => avoidProblem [true], fun _ => 3⟩

noncomputable def withRegistry : DesignAdapter :=
  { avoidDesign with registry := Registry.of (fun _ : Unit => oneAssumption),
                     strength := Registry.initial (fun _ : Unit => oneAssumption) }

/-- A premise asking for `4` bits of an assumption pinned at `3` is invalid: the submission is
refused even if its `Spec` were proved. -/
theorem inflated_premise_refused (x : Word)
    (u : Submission (withRegistry.primitive x) withRegistry.registry)
    (hd : ⟨(), (), 4⟩ ∈ u.deps ()) : ¬ withRegistry.AcceptDesign x u := fun h => by
  have : (4 : ℕ) ≤ 3 := h.2.1 () _ hd
  omega

/-! ### L07: cryptanalysis -/

/-- A machine that outputs the task's word has gain `0`: refused. -/
theorem zero_gain_refused (x : Word) (M : Machine) (hM : M.run [] = PMF.pure x.bits) :
    ¬ avoidAttack.AcceptAttack x M := fun h => by
  have hg := h.1
  change 0 < (avoidProblem x.bits).gain M at hg
  rw [avoidProblem_gain_of_pure hM] at hg
  simp at hg

/-- A machine whose cost exceeds `2^c · gain` is refused. -/
theorem expensive_refused (x : Word) (M : Machine)
    (hc : 2 ^ avoidAttackBound * (avoidAttack.problem x).gain M < (M.cost : ℝ)) :
    ¬ avoidAttack.AcceptAttack x M := fun h => absurd h.2 (not_le.mpr hc)

/-- The attack family with a refutation claim equal to its bound (`c = k = 5`). -/
noncomputable def notStrict : AttackAdapter := { avoidAttack with refutes := fun _ => some 5 }

/-- `c = k` refutes nothing: no task of that family is solvable. -/
theorem not_strict_unsolvable (x : Word) : ¬ notStrict.SolvableAttack x := fun h => by
  have : avoidAttackBound < 5 := h.1 5 rfl
  exact absurd this (by decide)

/-- Hence its solver target is false for every descriptor. -/
theorem not_strict_target_false (bits : List Bool) : ¬ Target notStrict.family bits := by
  unfold Target
  cases hd : notStrict.family.decode bits with
  | none => exact id
  | some x => exact not_strict_unsolvable x

/-! ### L10: metadata earns no entropy -/

/-- A word with one extra bit of metadata, encoded as that bit followed by the word. -/
def flagEncode (x : Word × Bool) : List Bool := x.2 :: x.1.bits

def flagDecode : List Bool → Option (Word × Bool)
  | [] => none
  | b :: w => (Word.decode w).map (·, b)

theorem flagDecode_encode (x : Word × Bool) : flagDecode (flagEncode x) = some x := by
  obtain ⟨w, b⟩ := x
  simp [flagEncode, flagDecode, show Word.decode w.bits = some w from Word.decode_encode w]

/-- Design tasks whose extra bit only chooses the cap (64 or 65). -/
def capOnly : DesignAdapter where
  Task := Word × Bool
  encode := flagEncode
  decode := flagDecode
  decode_encode := flagDecode_encode
  Alg := Unit
  sig := avoidSig
  Params := List Bool
  params x := x.1.bits
  encodeParams := id
  PropIndex := Unit
  prop := avoidProp
  cost _ I := (I.machine ()).cost
  registry := emptyRegistry
  strength := emptyStrength
  cap x := if x.2 then 65 else 64

/-- Attack tasks whose extra bit only chooses the bound `c` (5 or 6). -/
noncomputable def boundOnly : AttackAdapter :=
  { Task := Word × Bool, encode := flagEncode, decode := flagDecode,
    decode_encode := flagDecode_encode,
    problem := fun x => avoidProblem x.1.bits, bound := fun x => if x.2 then 6 else 5,
    refutes := fun _ => none }

/-- The fixed word of the metadata-only generators. -/
def word1 : Word := ⟨[true], by simp [Word.maxLen]⟩

/-- A generator whose seed only sets metadata. -/
def metaGen (_ : Fin 1) (r : Seed 1) : Word × Bool := (word1, r 0)

theorem cap_only_not_certified : ¬ Certified capOnly.family 1 1 1 metaGen :=
  capOnly.not_certified_of_params_const one_pos 0 fun _ _ => rfl

theorem bound_only_not_certified : ¬ Certified boundOnly.family 1 1 1 metaGen :=
  boundOnly.not_certified_of_problem_const one_pos 0 fun _ _ => rfl

end Generators.Negatives
