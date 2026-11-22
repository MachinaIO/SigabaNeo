import PE.Impl.Game.HandlersP
import SigabaNeo.Lib.Machines.Prog.MacroSize

/-!
# The states of the per-query handlers

The handlers `handlersP` are compiled framed programs (`Routine.ofXProg`), so their states are the
`XProg.size` of the handler programs `handlerProgP` (`states_handlersP`). The components are lifted
to the `R + 8` tapes through frames, which add no state, so the size of a handler is its glue (an
affine function of `nA`, `nM`, the cut `K₀` and `|kL|`) plus the sizes of the components it calls:

* `size_selH`: `1530 + 864 nA + 120 nM + 2 (|setupP| + |pubP|)` (the selection program appears in
  both branches of the state test, hence the factor `2`);
* `size_keyHP`: `1480 + 396 nA + 396 nM + 264 K₀ + 60 |kL| + |keyP| + |authP|`;
* `size_chalH`: `1469 + 396 nA + 468 nM + |chalP|`;
* `size_handlerProgP_le`: every handler has at most
  `glueSize cd K₀ kL + 2 (|setupP| + |pubP| + |keyP| + |authP| + |chalP|)` states.
-/

namespace AdvancedEncryption.PE.Generic

open SigabaNeo SigabaNeo.Tape

variable {U : Universe} {Sig : Type} {R : ℕ}

theorem size_writeA : ∀ u : List Bool, (writeA u).size = 60 * u.length + 36
  | [] => rfl
  | b :: u => by
    rw [writeA, Prog.size_seq, size_writeA u]
    simp [Prim.pad]; ring

variable (cd : Codes U Sig)

/-- **The states of the selection handler.** -/
theorem size_selH (setupP pubP : XProg (R + 2)) :
    (selH cd setupP pubP).size = 1530 + 864 * cd.nA + 120 * cd.nM + 2 * (setupP.size + pubP.size) := by
  simp [selH, testLen, selCore, glue, comp, skipG, takeQ, lenPrep, buildSel, Prim.pad]
  ring

/-- **The states of the key handler with the cut `K₀`.** -/
theorem size_keyHP (K₀ : ℕ) (kL : List Bool) (keyP authP : XProg (R + 2)) :
    (keyHP cd K₀ kL keyP authP).size =
      1480 + 396 * cd.nA + 396 * cd.nM + 264 * K₀ + 60 * kL.length + keyP.size + authP.size := by
  simp [keyHP, keySelP, keyShortP, glue, comp, skipG, cutQ, longK, keyArgP, parseSel, rebuildK,
    setBad, Prim.pad, size_writeA]
  ring

/-- **The states of the challenge handler.** -/
theorem size_chalH (chalP : XProg (R + 2)) :
    (chalH cd chalP).size = 1469 + 396 * cd.nA + 468 * cd.nM + chalP.size := by
  simp [chalH, chalSel, chalFresh, testLen, glue, comp, skipG, takeQ, lenPrep, parseC, rebuildC,
    restoreC, Prim.pad]
  ring

/-- The states of the glue of a handler (besides the components'). -/
def glueSize (K₀ : ℕ) (kL : List Bool) : ℕ :=
  1530 + 864 * cd.nA + 468 * cd.nM + 264 * K₀ + 60 * kL.length

variable {sp : Spec U Sig} {setupW : List Bool → U.Attr → PMF Sig} {IW : List Bool → Prop}
  {Ok : Sig → Prop}

/-- **The states of a handler program**: the glue plus (at most twice) the components'. -/
theorem size_handlerProgP_le (cs : Comps R cd sp setupW IW Ok) (K₀ : ℕ) (kL : List Bool)
    (o : Fin 3) :
    (handlerProgP cd cs K₀ kL o).size ≤ glueSize cd K₀ kL +
      2 * (cs.setupP.size + cs.pubP.size + cs.keyP.size + cs.authP.size + cs.chalP.size) := by
  unfold glueSize
  rcases fin3_cases o with rfl | rfl | rfl
  · rw [handlerProgP_sel, size_selH]; omega
  · rw [handlerProgP_key, size_keyHP]; omega
  · rw [handlerProgP_chal, size_chalH]; omega

/-- **The states of the handlers** are the sizes of the handler programs. -/
theorem states_handlersP (cs : Comps R cd sp setupW IW Ok) (K₀ : ℕ) (kL : List Bool) (W : ℕ)
    (o : Fin 3) : (handlersP cd cs K₀ kL W o).states = (handlerProgP cd cs K₀ kL o).size :=
  XProg.card_state _

end AdvancedEncryption.PE.Generic
