/-
TEST CASE (submission). The toy assumption `Echo`, stated with cslib-frontier's definitions.

The game with secret bit `b` answers every query of the adversary with the one-bit word `[b]`.
The assumption claims that no uniform strict oracle-PPT adversary (`IsOraclePPT encBool`, one
Turing machine and one polynomial clock for every security parameter) tells `b = false` from
`b = true` with more than negligible advantage. It is false: query once and output the reply.
-/
import CslibFrontier.Crypto.Computational.PseudorandomFunction

namespace TestCase.Echo

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

/-- The game with secret bit `b`: every query is answered with `[b]`. -/
noncomputable def game (b : Bool) (adversary : OracleDistinguisher) (n : ℕ) : ProbComp Bool :=
  (adversary n []).run fun _ => pure [b]

/-- The echo assumption. -/
def target : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (game false adversary n))
    (fun adversary n => ProbComp.eval (game true adversary n)) (IsOraclePPT encBool)

end TestCase.Echo
