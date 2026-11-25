import PE.Impl.ExpLUT.Prog.RedKeyTTop
/-!
# Module 9: the input envelope of the back end `rkTailP` (`RkTailIn`)

**This is the interface between the middle phases `mid` and the back-end certificate.** The
middle phases must reach a static length bound `a` (on the `105` MVM tapes) with
`RkMidBound mid a` (`RedKeyTTop`) **and** `RkTailIn a`:

* every MVM tape `≤ 2^150` (this covers register `16`, the rows of `X`, `≈ 2^143` bits, and
  register `8`, `matL A_F`);
* the physical ring templates (tapes `35 … 38`) within their exact sizes: `K`, `N`, `N K`, `N K`
  (the template tapes `rkLiftB` sends to the store; F3's `RingInputs`/`layout` need them);
* **register `14`** (the public-key word, tape `tR 14 = 55`) `≤ 2^102`: the output of the
  component is `mpk ++ key`, and its bound `Lt` must stay `≤ 2^125`.

Everything else (coins, scratch registers, counters) only needs the uniform `2^150` cap: the
back end overwrites them. All conditions are upper bounds, so `RkTailIn` is downward closed
(`RkTailIn.mono`), i.e. `RkTailIn a ↔ a ≤ rkTailEnv` (`rkTailIn_iff`).
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyT

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM
open AdvancedEncryption.ExpLUT.Params

/-- **The input envelope of the back end** (per-tape bounds `a` on the `105` MVM tapes). -/
structure RkTailIn (a : Fin 105 → ℕ) : Prop where
  /-- Every tape (in particular register `16`, the rows of `X`) is at most `2^150`. -/
  top : ∀ t, a t ≤ 2 ^ 150
  /-- The template tape `35` (`K` bits). -/
  templateK : a 35 ≤ Dc.K
  /-- The template tape `36` (`N` bits). -/
  templateN : a 36 ≤ Dc.N
  /-- The template tape `37` (the zero ring word, `N K` bits). -/
  zeros : a 37 ≤ Dc.N * Dc.K
  /-- The template tape `38` (`N K` bits). -/
  ones : a 38 ≤ Dc.N * Dc.K
  /-- Register `14` (tape `55`), the public-key word. -/
  mpk : a (tR 14) ≤ 2 ^ 102

/-- The largest envelope satisfying `RkTailIn`. -/
def rkTailEnv (t : Fin 105) : ℕ :=
  if t = 35 then Dc.K else if t = 36 then Dc.N else if t = 37 ∨ t = 38 then Dc.N * Dc.K
  else if t = tR 14 then 2 ^ 102 else 2 ^ 150

theorem RkTailIn.mono {a b : Fin 105 → ℕ} (h : RkTailIn b) (hab : a ≤ b) : RkTailIn a :=
  ⟨fun t => (hab t).trans (h.top t), (hab 35).trans h.templateK, (hab 36).trans h.templateN,
    (hab 37).trans h.zeros, (hab 38).trans h.ones, (hab _).trans h.mpk⟩

theorem rkTailIn_env : RkTailIn rkTailEnv := by
  have hN : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
  have hK : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
  refine ⟨fun t => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold rkTailEnv; rw [hN, hK]; split_ifs <;> norm_num
  all_goals simp [rkTailEnv, tR]

theorem le_rkTailEnv {a : Fin 105 → ℕ} (h : RkTailIn a) : a ≤ rkTailEnv := by
  intro t
  unfold rkTailEnv
  split_ifs with h1 h2 h3 h4
  · subst h1; exact h.templateK
  · subst h2; exact h.templateN
  · rcases h3 with rfl | rfl
    · exact h.zeros
    · exact h.ones
  · subst h4; exact h.mpk
  · exact h.top t

theorem rkTailIn_iff (a : Fin 105 → ℕ) : RkTailIn a ↔ a ≤ rkTailEnv :=
  ⟨le_rkTailEnv, fun h => rkTailIn_env.mono h⟩

end AdvancedEncryption.ExpLUT.Prog.RedKeyT
