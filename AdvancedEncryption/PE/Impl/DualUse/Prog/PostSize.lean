import PE.Impl.DualUse.Prog.Post
import SigabaNeo.Lib.Machines.Prog.MacroSize

/-!
# The states and tapes of the post-processing

The post-processing `Post n E nA nM` has `8` tapes (`tapes_post_eq`) and
`1546 + 288 (nA + nM)` states (`states_post_eq`): `74` for its four single-pass phases and
`1472 + 288 (nA + nM)` for the compiled program `postProg nA nM` (`size_postProg`). For the
date-window codes (`nA = 10`, `nM = 1`) this is `4714` (`states_post_date`).
-/

namespace AdvancedEncryption.PE.Generic

open SigabaNeo SigabaNeo.Tape

/-- **The states of the program of the post-processing.** -/
theorem size_postProg (nA nM : ℕ) : (postProg nA nM).size = 1472 + 288 * (nA + nM) := by
  simp [postProg, rnd, postRest, caseA, caseB, badB, goodB, appendFR, Prim.pad]
  ring

/-- **The tapes of the post-processing.** -/
theorem tapes_post_eq (n E nA nM : ℕ) : (Post n E nA nM).tapes = 8 := rfl

/-- **The states of the post-processing.** -/
theorem states_post_eq (n E nA nM : ℕ) :
    (Post n E nA nM).states = 1546 + 288 * (nA + nM) := by
  have h2 : Fintype.card Turing.MultiTapeTM.RewindWorkState = 2 := by decide
  have h3 : Fintype.card Turing.MultiTapeTM.MarkWorkState = 2 := by decide
  have h4 : Fintype.card Turing.MultiTapeTM.RewindState = 2 := by decide
  show Nat.card _ = _
  rw [Nat.card_eq_fintype_card]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_option, Fintype.card_bool, h2, h3,
    h4, Prog.card_state, size_postProg]
  ring

/-- The states of the post-processing of the date-window codes. -/
theorem states_post_date (n E : ℕ) : (Post n E 10 1).states = 4714 := by
  rw [states_post_eq]

end AdvancedEncryption.PE.Generic
