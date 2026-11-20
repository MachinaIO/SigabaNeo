import Definitions.Def_Echo
import CslibFrontier.Tactic.PPT
import CslibFrontier.Crypto.Negligible.Basic

/-!
# A refutation of `TestCase.Echo.target`

The adversary asks one query and outputs the first bit of the reply. `ppt` certifies that it is
uniform strict oracle PPT (cslib-frontier builds the Turing machine). Against the game with
secret `b` it outputs `b`, so its advantage is `1` at every security parameter, which is not
negligible.
-/

namespace TestCase.Echo

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM TestCase

/-- Query once, output the first bit of the reply. -/
noncomputable def echo : OracleDistinguisher := fun _ _ =>
  (fun reply : List Bool => reply.headD false) <$>
    (List.take 1 <$> ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), []))

theorem echo_ppt : IsOraclePPT encBool echo := by
  ppt [echo]

theorem game_echo (b : Bool) (n : ℕ) : ProbComp.eval (Echo.game b echo n) = PMF.pure b := by
  simp [Echo.game, echo]

theorem refutation : ¬ TestCase.Echo.target := by
  intro h
  have hneg := h echo echo_ppt
  simp only [game_echo] at hneg
  have hadv : Game.advantage (PMF.pure false) (PMF.pure true) = 1 := by
    simp [Game.advantage, Game.succProbability, NNReal.nndist_eq]
  rw [hadv] at hneg
  exact not_negligible_const one_ne_zero hneg

end TestCase.Echo
