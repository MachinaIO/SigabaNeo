import PE.Impl.ExpLUT.Prog.RedKeyC4A
import PE.Impl.ExpLUT.Prog.RedKeyCAX

/-!
# Phase M4 (exploration): finding the loop hints of `RedKeyC4A.an`

`c4S M N K c E` runs the analyzer of `RedKeyC4A` but **searches** each loop box (tries `E`, then
`max B G` for the predicted iterate box `G`, up to `6` times, then unrolling for counts `≤ 64`) and
returns the hints (pre-order, one per analyzed `rep`; `C4H.box`: the registers where the box exceeds
the entry box) that make `an` succeed with a single analysis per loop body. `RedKeyC4H` was
generated with it (see `RedKeyPLAN.md`, tenth session, for the generator). No proofs: the hints are only *used* by the checked analyzer
(`c4Ok`), so a wrong hint can only make `c4Ok` fail. `c4Hints` prints them as a Lean term.
-/

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyC4

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM AdvancedEncryption.ExpLUT.Prog

/-- The sparse hint of a box `B` over the entry box `E`. -/
def c4Diff (E B : List ℕ) : List (ℕ × ℕ) :=
  (List.range 64).filterMap fun i => if B.getD i 0 > E.getD i 0 then some (i, B.getD i 0) else none

def c4Lg (n : ℕ) : ℕ := Nat.log2 n

def c4Show (E : List ℕ) : String :=
  toString ((List.range 64).filterMap fun i => if E.getD i 0 > 1 then some (i, c4Lg (E.getD i 0)) else none)

/-- The search (returns the result of `an` with the found hints, and the hints). -/
partial def c4S (M N K : ℕ) : Code → List ℕ → Except String (C4R × List C4H)
  | .seq p q, E => do
    let (r1, h1) ← c4S M N K p E
    let (r2, h2) ← c4S M N K q r1.out
    pure (⟨tcomp r1.t r2.t, r1.T + r2.T, r2.out, []⟩, h1 ++ h2)
  | .ifb _ p q, E => do
    let (r1, h1) ← c4S M N K p E
    let (r2, h2) ← c4S M N K q E
    let tj := tjoin E r1.t r2.t
    if !(topL (boxV tj E) M) then .error "ifb over M" else
    pure (⟨tj, max r1.T r2.T + 1, boxV tj E, []⟩, h1 ++ h2)
  | .rep c body, E => do
    let R := E.getD c.val 0
    let rec go : ℕ → List ℕ → Except String (C4R × List C4H)
      | 0, B => if R ≤ 64 then do
          let rec un : ℕ → C4T → ℕ → List C4H → Except String (C4T × ℕ × List C4H)
            | 0, V, Tm, acc => .ok (V, Tm, acc)
            | n + 1, V, Tm, acc => do
              let Bj := boxV V E
              if !(topL Bj M) then .error s!"unroll {c}: box over M {c4Show Bj}" else
              let (rb, hb) ← c4S M N K body Bj
              un n (tjoin E V (tcomp V rb.t)) (max Tm rb.T) (acc ++ hb)
          let (V, Tm, acc) ← un R [] 0 []
          if topL (boxV V E) M then
            pure (⟨V, R * (2 * M + Tm + 4) + 2, boxV V E, []⟩, C4H.unroll :: acc)
          else .error s!"unroll {c}: out over M"
        else .error s!"loop {c} R=2^{c4Lg R}: no box; B={c4Show B}"
      | n + 1, B => do
        let (rb, hb) ← c4S M N K body B
        let Gs := boxV (tloop rb.t B R) E
        if loopOK rb.t R && chk Gs B M then
          pure (⟨tloop rb.t B R, R * (2 * M + rb.T + 4) + 2, Gs, []⟩, .box (c4Diff E B) :: hb)
        else
          let B' := (List.range 64).map fun i => max (B.getD i 0) (Gs.getD i 0)
          if topL B' M then go n B' else go 0 B'
    go 6 E
  | c, E => match an M N K c E [] with
    | some r => .ok (r, [])
    | none => .error s!"leaf at {c4Show E}"

/-- The search on an `AC`. -/
def c4SA (M N K : ℕ) : AC → List ℕ → Except String (C4R × List C4H)
  | .c c, E => c4S M N K c E
  | .nat r u v, E => match anA M N K (.nat r u v) E [] with
    | some r => .ok (r, [])
    | none => .error s!"natC {r} {u} at {c4Show E}"
  | .s p q, E => do
    let (r1, h1) ← c4SA M N K p E
    let (r2, h2) ← c4SA M N K q r1.out
    pure (⟨tcomp r1.t r2.t, r1.T + r2.T, r2.out, []⟩, h1 ++ h2)

/-- A report: time, output box (log₂ of the entries `> 1`), number of hints. -/
def c4Report (M N K : ℕ) (ac : AC) (E : List ℕ) : String :=
  match c4SA M N K ac E with
  | .error e => "ERR " ++ e
  | .ok (r, hs) => s!"T=2^{c4Lg r.T} hints={hs.length} out={c4Show r.out}"

/-- The hints as a Lean term. -/
def c4Hints (M N K : ℕ) (ac : AC) (E : List ℕ) : String :=
  match c4SA M N K ac E with
  | .error e => "ERR " ++ e
  | .ok (_, hs) => toString (hs.map fun h => match h with
      | .box b => "C4H.box " ++ toString b
      | .unroll => "C4H.unroll")

/-- The output box (exact). -/
def c4Out (M N K : ℕ) (ac : AC) (E : List ℕ) : String :=
  match c4SA M N K ac E with
  | .error e => "ERR " ++ e
  | .ok (r, _) => toString ((List.range 64).map fun i => r.out.getD i 0)

end AdvancedEncryption.ExpLUT.Prog.RedKeyC4
