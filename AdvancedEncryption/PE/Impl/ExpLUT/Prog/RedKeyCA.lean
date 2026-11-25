import PE.Impl.ExpLUT.Prog.KeyTimeArithmetic
/-!
# Cost certificate of `mid` (ninth session): a static bound analyzer for MVM codes (exploration)

**Status: computable exploration tool, no soundness proof yet** (see `RedKeyPLAN.md`, ninth
session). `caAn L N K c E` over-approximates `XProg.lenBoundT`/`timeBoundT` of `MVM.compile c` on
the store `KeyTime.layout L N K x` for every register vector `x ≤ E` (`E` a list of `64` register
bounds; `L` the cap of every tape, used as `M` of F3's per-instruction certificates).

The abstract value of a code is a per-register **transformer** `CaT`: entry `⟨a, some (s, δ)⟩` of
register `r` means `out r ≤ max a (x s + δ)`, `⟨a, none⟩` means `out r ≤ a`. Instructions:
`cp d s ↦ ⟨0, some (s, 0)⟩`, `app d s ↦ ⟨0, some (d, E s)⟩`, `op ↦ ⟨N K, none⟩`, `clr ↦ ⟨0, none⟩`,
`mv`/`mvR`/`drop`/`tl` identity (static bounds never shrink); times are F3's
(`operationBound L N K (E c)`, `(2L+5)(20+10 E c)`, `(4 E s + 6)(2L+5)`, `2L+5`).
Loops (`rep c b`, `R = E c`): the **linear rule** — find a box `B` (tries `E`, then the box the
transformer predicts, twice) with the body transformer at `B` predicting iterates
`max a (x r) + j δ ≤ B` for self entries (`s = r`) and `≤ max a (B s + δ)` otherwise; time
`R (2L + T_body + 4) + 2` (`KeyTime.rep_family`); for `R ≤ 64` a fallback **unrolling**
(per-iteration transformers composed, prefixes joined: doubling loops).

`CaX` adds leaves for `natC` (`n r nb`: `r := nb` bits, F3 `compile_natC`), template lists
(`t ds`, F3 `compile_templateOps`) — the codes with huge literal templates (`emitBitsC` of
`N K` bits) or `codecSize` numerals can't be evaluated, so phases are mirrored with these leaves
(`RedKeyCAX`).
-/

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyC

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM AdvancedEncryption.ExpLUT.Prog

/-- `f(x)(r) ≤ max a (x s + δ)` (`d = some (s, δ)`), or `≤ a`. -/
structure CaE where
  a : ℕ
  d : Option (ℕ × ℕ)
def CaE.app (e : CaE) (x : ℕ → ℕ) : ℕ := match e.d with | none => e.a | some (s, δ) => max e.a (x s + δ)
def caId (r : ℕ) : CaE := ⟨0, some (r, 0)⟩
abbrev CaT := List CaE
def caGT (t : CaT) (i : ℕ) : CaE := t.getD i (caId i)
def CaE.comp (t1 : CaT) (g : CaE) : CaE := match g.d with
  | none => g
  | some (s2, d2) => let f := caGT t1 s2
    match f.d with
    | none => ⟨max g.a (f.a + d2), none⟩
    | some (s1, d1) => ⟨max g.a (f.a + d2), some (s1, d1 + d2)⟩
def CaE.abs (e : CaE) (E : List ℕ) : CaE := ⟨e.app (fun i => E.getD i 0), none⟩
def CaE.join (E : List ℕ) (e1 e2 : CaE) : CaE := match e1.d, e2.d with
  | none, none => ⟨max e1.a e2.a, none⟩
  | some p, none => ⟨max e1.a e2.a, some p⟩
  | none, some p => ⟨max e1.a e2.a, some p⟩
  | some (s1, d1), some (s2, d2) => if s1 = s2 then ⟨max e1.a e2.a, some (s1, max d1 d2)⟩
      else ⟨max e1.a (e2.app (fun i => E.getD i 0)), some (s1, d1)⟩
def caMap (f : ℕ → ℕ) : List ℕ := (List.range 64).map f
def caMapT (f : ℕ → CaE) : CaT := (List.range 64).map f
def caAp (t : CaT) (E : List ℕ) : List ℕ := caMap fun i => (caGT t i).app (fun j => E.getD j 0)
def caSet (r : Fin 64) (e : CaE) : CaT := (caMapT caId).set r.val e
def caComp (t1 t2 : CaT) : CaT := caMapT fun i => (caGT t2 i).comp t1
def caJoin (E : List ℕ) (t1 t2 : CaT) : CaT := caMapT fun i => (caGT t1 i).join E (caGT t2 i)
-- loop entry given loop box B
def CaE.loop (i : ℕ) (B : List ℕ) (R : ℕ) (e : CaE) : CaE := match e.d with
  | none => ⟨e.a, some (i, 0)⟩
  | some (s, δ) => if s = i then ⟨e.a + R * δ, some (i, R * δ)⟩ else ⟨max e.a (B.getD s 0 + δ), some (i, 0)⟩
def caLoopT (t : CaT) (B : List ℕ) (R : ℕ) : CaT := caMapT fun i => (caGT t i).loop i B R
def caLe (A B : List ℕ) : Bool := (List.range 64).all fun i => decide (A.getD i 0 ≤ B.getD i 0)
def caAllLe (E : List ℕ) (L : ℕ) : Bool := (List.range 64).all fun i => decide (E.getD i 0 ≤ L)
def caMax (A B : List ℕ) : List ℕ := caMap fun i => max (A.getD i 0) (B.getD i 0)
structure CaR where
  t : CaT
  T : ℕ
abbrev CaEx := Except String CaR
def caLg (n : ℕ) : ℕ := Nat.log2 n
def caLgs (E : List ℕ) : String := toString ((List.range 64).filterMap fun i => if E.getD i 0 > 1 then some (i, caLg (E.getD i 0)) else none)
-- final box of the loop from entry box E, loop transformer computed at box B
def caLBox (t : CaT) (B E : List ℕ) (R : ℕ) : List ℕ := caAp (caLoopT t B R) E
def caTry (f : List ℕ → CaEx) (L R : ℕ) (E B : List ℕ) : Except String (Option CaR × List ℕ) :=
  match f B with
  | .error e => .error e
  | .ok r => let G := caLBox r.t B E R
    if caLe G B && caAllLe B L then .ok (some r, B) else .ok (none, caMax G B)
def caLoop (c : Fin 64) (f : List ℕ → CaEx) (L R : ℕ) (E : List ℕ) : CaEx := do
  let (o, B1) ← caTry f L R E E
  let (o, B) ← match o with
    | some r => pure (r, E)
    | none => do
      let (o, B2) ← caTry f L R E B1
      match o with
      | some r => pure (r, B1)
      | none => do
        let (o, B3) ← caTry f L R E B2
        match o with
        | some r => pure (r, B2)
        | none => .error s!"loop {c} R={caLg R} diff={toString ((List.range 64).filterMap fun i => if B3.getD i 0 > B2.getD i 0 then some (i, caLg (B2.getD i 0), caLg (B3.getD i 0 - B2.getD i 0)) else none)}"
  pure ⟨caLoopT o.t B R, R * (2 * L + o.T + 4) + 2⟩
def caUnroll (f : List ℕ → CaEx) (L : ℕ) : ℕ → List ℕ → CaT → CaT → ℕ → CaEx
  | 0, _, _, P, Tm => .ok ⟨P, Tm⟩
  | n + 1, B, U, P, Tm => do
    let r ← f B
    let B' := caMax B (caAp r.t B)
    if caAllLe B' L then
      let U' := caComp U r.t
      caUnroll f L n B' U' (caJoin B' P U') (max Tm r.T)
    else .error "unroll L"
def caLoop2 (c : Fin 64) (f : List ℕ → CaEx) (L R : ℕ) (E : List ℕ) : CaEx :=
  match caLoop c f L R E with
  | .ok r => .ok r
  | .error e => if R ≤ 64 then do
      let r ← caUnroll f L R E (caMapT caId) (caMapT caId) 0
      pure ⟨r.t, R * (2 * L + r.T + 4) + 2⟩
    else .error e
def caAn (L N K : ℕ) : Code → List ℕ → CaEx
  | .op _ d _ c, E => .ok ⟨caSet d ⟨N * K, none⟩, KeyTime.operationBound L N K (E.getD c 0)⟩
  | .mv _ _ c, E => .ok ⟨caMapT caId, (2 * L + 5) * (20 + 10 * E.getD c 0)⟩
  | .mvR _ _, _ => .ok ⟨caMapT caId, (2 * L + 5) * (20 + 10 * (N * K))⟩
  | .cp d s, _ => .ok ⟨caSet d ⟨0, some (s.val, 0)⟩, 2 * L + 5⟩
  | .drop _ c, E => .ok ⟨caMapT caId, (2 * L + 5) * (20 + 10 * E.getD c 0)⟩
  | .clr d, _ => .ok ⟨caSet d ⟨0, none⟩, 2 * L + 5⟩
  | .tl _, _ => .ok ⟨caMapT caId, 2 * L + 5⟩
  | .app d s, E => if E.getD d 0 + E.getD s 0 ≤ L then
      .ok ⟨caSet d ⟨0, some (d.val, E.getD s 0)⟩, (4 * E.getD s 0 + 6) * (2 * L + 5)⟩ else .error s!"app {d} {s} {caLg (E.getD d 0)} {caLg (E.getD s 0)}"
  | .eqb f a b, _ => if f = a ∨ f = b ∨ a = b then .ok ⟨caMapT caId, 2 * L + 5⟩ else .ok ⟨caSet f ⟨1, none⟩, 2 * L + 5⟩
  | .nop, _ => .ok ⟨caMapT caId, 2 * L + 5⟩
  | .seq p q, E => do
    let r1 ← caAn L N K p E
    let r2 ← caAn L N K q (caAp r1.t E)
    pure ⟨caComp r1.t r2.t, r1.T + r2.T⟩
  | .ifb _ p q, E => do
    let r1 ← caAn L N K p E
    let r2 ← caAn L N K q E
    pure ⟨caJoin E r1.t r2.t, max r1.T r2.T + 1⟩
  | .rep c b, E => caLoop2 c (fun B => caAn L N K b B) L (E.getD c 0) E
inductive CaX where
  | c (c : Code) | n (r : Fin 64) (nb : ℕ) | t (ds : List (Fin 64 × ℕ)) | s (p q : CaX)
def caSetL (E : List ℕ) (r : Fin 64) (v : ℕ) : List ℕ := E.set r.val v
def caRunX (L N K : ℕ) : CaX → List ℕ → Except String (List ℕ × ℕ)
  | .c c, E => do let r ← caAn L N K c E; pure (caAp r.t E, r.T)
  | .n r nb, E => if nb ≤ L ∧ E.getD 38 0 ≤ 1 then .ok (caSetL E r nb, (32*nb+4)*(2*L+5)) else .error s!"natc {r}"
  | .t ds, E => .ok (ds.foldl (fun E p => caSetL E p.1 p.2) E, (ds.foldl (fun a p => a + 32*p.2+6) 1) * (2*L+5))
  | .s p q, E => do let (E1, T1) ← caRunX L N K p E; let (E2, T2) ← caRunX L N K q E1; pure (E2, T1 + T2)
def caReport (L N K : ℕ) (x : CaX) (E : List ℕ) : String :=
  match caRunX L N K x E with
  | .error e => "ERR " ++ e
  | .ok (E', T) => s!"T=2^{caLg T} out={caLgs E'}"

end AdvancedEncryption.ExpLUT.Prog.RedKeyC
