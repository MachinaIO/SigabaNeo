import Generators.AvoidDesign

/-!
Negative fixture: a generator-controlled family whose tasks are all solvable and all different
(a permissive `Solvable`, and `SameProblem` as syntactic equality). The certificate is true, but
the family is not the policy's.
-/

namespace Generators.OwnFamily

open SigabaNeo.Benchmark SigabaNeo.Benchmark.Fixture

def permissive : Family where
  Task := Word
  encode := Word.encode
  decode := Word.decode
  decode_encode := Word.decode_encode
  Solvable _ := True
  SameProblem := (· = ·)
  sameProblem_equiv := eq_equivalence

theorem certified : Certified permissive 2 8 8 Generators.AvoidDesign.generate :=
  certified_of_injective (by norm_num) (fun _ _ => trivial)
    (fun _ _ _ h => AvoidDesign.word_injective (congrArg Word.bits h))

end Generators.OwnFamily
