import PE.Impl.ExpLUT.Prog.RedKeyC3MT
import PE.Impl.ExpLUT.Prog.RedKeyC4X
/-!
# Phase M3 (exploration): loop hints and boxes for the checks of `RedKeyC3MH`

`m3S` runs `RedKeyC4X.c4SA` (the box search) through the `AD` mirrors. No proofs: hints and boxes
are only *used* by the checked analyzer `m3Ok`. Generator (scratch file importing this module):

    #eval m3Report (2^150) (2^24) (2^16) m3Const m3In
    #eval m3Hints … ; #eval m3OutL …
-/

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyC3M

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Prog.RedKeyC4

/-- The search on an `AD`. -/
def m3S (M N K : ℕ) : AD → List ℕ → Except String (C4R × List C4H)
  | .a ac, E => c4SA M N K ac E
  | .tw r v, E => match anD M N K (.tw r v) E [] with
    | some r => .ok (r, [])
    | none => .error s!"template {r} at {c4Show E}"
  | .s p q, E => do
    let (r1, h1) ← m3S M N K p E
    let (r2, h2) ← m3S M N K q r1.out
    pure (⟨tcomp r1.t r2.t, r1.T + r2.T, r2.out, []⟩, h1 ++ h2)

def m3Report (M N K : ℕ) (ad : AD) (E : List ℕ) : String :=
  match m3S M N K ad E with
  | .error e => "ERR " ++ e
  | .ok (r, hs) => s!"T=2^{c4Lg r.T} hints={hs.length} out={c4Show r.out}"

def m3Hints (M N K : ℕ) (ad : AD) (E : List ℕ) : String :=
  match m3S M N K ad E with
  | .error e => "ERR " ++ e
  | .ok (_, hs) => toString (hs.map fun h => match h with
      | .box b => "C4H.box " ++ toString b
      | .unroll => "C4H.unroll")

def m3OutL (M N K : ℕ) (ad : AD) (E : List ℕ) : String :=
  match m3S M N K ad E with
  | .error e => "ERR " ++ e
  | .ok (r, _) => toString ((List.range 64).map fun i => r.out.getD i 0)

def m3OutBox (M N K : ℕ) (ad : AD) (E : List ℕ) : List ℕ :=
  match m3S M N K ad E with
  | .error _ => []
  | .ok (r, _) => (List.range 64).map fun i => r.out.getD i 0

end AdvancedEncryption.ExpLUT.Prog.RedKeyC3M
