import SigabaNeoStd.Machines.Prog.ShapeS
import SigabaNeoStd.Machines.GatesSLP
import SigabaNeoStd.Lattices.Homomorphic.BoolCompare

/-!
# Generating the gate list of a compiled comparison expression

`SLP.compile p e` compiles a Boolean combination `e : BExp (Fin 10)` of comparisons of the inputs
with constants into gates; `unparse (toGates 10 …)` is its gate list as a word (wire indices in
unary). Here a tape program **writes that word**, gate by gate, for expressions `DExp` whose
comparison constants are either static or read from a tape (`geT`, `leT`: the bits of the
constant, least significant first, are popped from the tape).

Layout (`Prog 40`): `O = 2` the word, `G = 3` the index of the next gate (unary), `W = 4` the
current wire (unary), `S1 = 5`, `S2 = 6` scratch, `E = 7` the emission counter, `R d = 8 + d`
(`d < 16`) the registers of the nesting depths, `Z = 29` a popped bit; other tapes are left alone.

* `gateP x y`: append the gate `(x, y)` (`run_gateP`): the word gains `1^x 0 1^y 0`, `W` the index
  of the new gate, `G` one more;
* **`run_genE`**: from a store representing `(p, w)` (`Rep`), `genE d e` ends representing
  `compile p (e.toB env)` (the constants read from the tapes), changing only the tapes of `Clob`;
* `genPred e := … genE 0 e ⨾ gateP W W`: from blank tapes, the word `unparse (predGates …)`.
-/

namespace SigabaNeo.Tape

namespace GateGen

open Prog SigabaNeo.Lattices SigabaNeo.Lattices.SLP
open scoped Prog

/-! ### The layout -/

abbrev O : Fin 40 := 2
abbrev G : Fin 40 := 3
abbrev W : Fin 40 := 4
abbrev S1 : Fin 40 := 5
abbrev S2 : Fin 40 := 6
abbrev E : Fin 40 := 7
abbrev Z : Fin 40 := 29

/-- The layout tapes are distinct. -/
@[simp] theorem ne_O_G : (O : Fin 40) ≠ G := by decide
@[simp] theorem ne_O_W : (O : Fin 40) ≠ W := by decide
@[simp] theorem ne_O_S1 : (O : Fin 40) ≠ S1 := by decide
@[simp] theorem ne_O_S2 : (O : Fin 40) ≠ S2 := by decide
@[simp] theorem ne_O_E : (O : Fin 40) ≠ E := by decide
@[simp] theorem ne_O_Z : (O : Fin 40) ≠ Z := by decide
@[simp] theorem ne_G_O : (G : Fin 40) ≠ O := by decide
@[simp] theorem ne_G_W : (G : Fin 40) ≠ W := by decide
@[simp] theorem ne_G_S1 : (G : Fin 40) ≠ S1 := by decide
@[simp] theorem ne_G_S2 : (G : Fin 40) ≠ S2 := by decide
@[simp] theorem ne_G_E : (G : Fin 40) ≠ E := by decide
@[simp] theorem ne_G_Z : (G : Fin 40) ≠ Z := by decide
@[simp] theorem ne_W_O : (W : Fin 40) ≠ O := by decide
@[simp] theorem ne_W_G : (W : Fin 40) ≠ G := by decide
@[simp] theorem ne_W_S1 : (W : Fin 40) ≠ S1 := by decide
@[simp] theorem ne_W_S2 : (W : Fin 40) ≠ S2 := by decide
@[simp] theorem ne_W_E : (W : Fin 40) ≠ E := by decide
@[simp] theorem ne_W_Z : (W : Fin 40) ≠ Z := by decide
@[simp] theorem ne_S1_O : (S1 : Fin 40) ≠ O := by decide
@[simp] theorem ne_S1_G : (S1 : Fin 40) ≠ G := by decide
@[simp] theorem ne_S1_W : (S1 : Fin 40) ≠ W := by decide
@[simp] theorem ne_S1_S2 : (S1 : Fin 40) ≠ S2 := by decide
@[simp] theorem ne_S1_E : (S1 : Fin 40) ≠ E := by decide
@[simp] theorem ne_S1_Z : (S1 : Fin 40) ≠ Z := by decide
@[simp] theorem ne_S2_O : (S2 : Fin 40) ≠ O := by decide
@[simp] theorem ne_S2_G : (S2 : Fin 40) ≠ G := by decide
@[simp] theorem ne_S2_W : (S2 : Fin 40) ≠ W := by decide
@[simp] theorem ne_S2_S1 : (S2 : Fin 40) ≠ S1 := by decide
@[simp] theorem ne_S2_E : (S2 : Fin 40) ≠ E := by decide
@[simp] theorem ne_S2_Z : (S2 : Fin 40) ≠ Z := by decide
@[simp] theorem ne_E_O : (E : Fin 40) ≠ O := by decide
@[simp] theorem ne_E_G : (E : Fin 40) ≠ G := by decide
@[simp] theorem ne_E_W : (E : Fin 40) ≠ W := by decide
@[simp] theorem ne_E_S1 : (E : Fin 40) ≠ S1 := by decide
@[simp] theorem ne_E_S2 : (E : Fin 40) ≠ S2 := by decide
@[simp] theorem ne_E_Z : (E : Fin 40) ≠ Z := by decide
@[simp] theorem ne_Z_O : (Z : Fin 40) ≠ O := by decide
@[simp] theorem ne_Z_G : (Z : Fin 40) ≠ G := by decide
@[simp] theorem ne_Z_W : (Z : Fin 40) ≠ W := by decide
@[simp] theorem ne_Z_S1 : (Z : Fin 40) ≠ S1 := by decide
@[simp] theorem ne_Z_S2 : (Z : Fin 40) ≠ S2 := by decide
@[simp] theorem ne_Z_E : (Z : Fin 40) ≠ E := by decide

/-- The register of depth `d < 16`. -/
def R (d : ℕ) : Fin 40 := ⟨8 + d % 16, by omega⟩

/-- A unary number. -/
abbrev un (n : ℕ) : List Bool := List.replicate n true

/-! ### Emitting a wire index -/

/-- A wire index to emit: `0`, an input `i` (`1 + i`), or the unary number on a tape. -/
inductive Src
  | one
  | inp (i : ℕ)
  | tape (t : Fin 40)

/-- Its value on a store. -/
def Src.val (s : Store 40) : Src → ℕ
  | .one => 0
  | .inp i => 1 + i
  | .tape t => (s t).length

/-- `n` ones on the word. -/
def ones : ℕ → Prog 40
  | 0 => prim (.copy O O)
  | n + 1 => ones n ⨾ prim (.snoc O true)

/-- Emit a wire index and its separator. -/
def emit : Src → Prog 40
  | .one => prim (.snoc O false)
  | .inp i => ones (1 + i) ⨾ prim (.snoc O false)
  | .tape t => forN E t (prim (.snoc O true)) ⨾ prim (.snoc O false)

/-- A tape source is usable: not the word or the counter, a unary number. -/
def Src.Ok (s : Store 40) : Src → Prop
  | .one => True
  | .inp _ => True
  | .tape t => t ≠ O ∧ t ≠ E ∧ s t = un (s t).length

theorem run_ones : ∀ (n : ℕ) (s : Store 40),
    run (ones n) s = Function.update s O (s O ++ un n)
  | 0, s => by simp [ones, Prim.apply]
  | n + 1, s => by
    rw [ones, run_seq, run_ones n s, run_prim]
    simp [Prim.apply, List.replicate_succ', List.append_assoc]

theorem run_emit (x : Src) (s : Store 40) (hE : s E = []) (hx : x.Ok s) :
    run (emit x) s = Function.update s O (s O ++ un (x.val s) ++ [false]) := by
  cases x with
  | one => simp [emit, Src.val, run_prim, Prim.apply]
  | inp i => simp [emit, Src.val, run_seq, run_ones, run_prim, Prim.apply, List.append_assoc]
  | tape t =>
    obtain ⟨htO, htE, -⟩ := hx
    have hOE : (O : Fin 40) ≠ E := by decide
    rw [emit, run_seq]
    have h := run_forN E t (prim (.snoc O true)) (fun n : ℕ => Function.update s O (s O ++ un n))
      Nat.succ (fun a w => by
        rw [run_prim]; funext i
        simp only [Prim.apply, Function.update_apply]
        split_ifs <;> simp_all [List.replicate_succ']) 0 s (by simp)
    rw [h, Nat.succ_iterate, Nat.zero_add, run_prim]
    funext i
    simp only [Prim.apply, Src.val, Function.update_apply]
    split_ifs <;> simp_all [List.append_assoc]

/-! ### One gate -/

/-- Append the gate `(x, y)`: `W :=` its index, `G` one more. -/
def gateP (x y : Src) : Prog 40 := emit x ⨾ emit y ⨾ cp W G ⨾ prim (.snoc G true)

/-- The tapes a gate writes. -/
def gateTapes (t : Fin 40) : Prop := t = O ∨ t = W ∨ t = G

theorem Src.val_upd_O (x : Src) (s : Store 40) (v : List Bool) (hx : x.Ok s) :
    x.val (Function.update s O v) = x.val s := by
  cases x with
  | one => rfl
  | inp i => rfl
  | tape t => simp [Src.val, Function.update_of_ne hx.1]

theorem Src.ok_upd_O (x : Src) (s : Store 40) (v : List Bool) (hx : x.Ok s) :
    x.Ok (Function.update s O v) := by
  cases x with
  | one => trivial
  | inp i => trivial
  | tape t => exact ⟨hx.1, hx.2.1, by simpa [Function.update_of_ne hx.1] using hx.2.2⟩

theorem run_gateP (x y : Src) (s : Store 40) (hE : s E = []) (hx : x.Ok s) (hy : y.Ok s) :
    run (gateP x y) s = Function.update (Function.update (Function.update s O
      (s O ++ un (x.val s) ++ [false] ++ un (y.val s) ++ [false])) W (s G)) G (s G ++ [true]) := by
  have hOE : (O : Fin 40) ≠ E := by decide
  rw [gateP, run_seq, run_seq, run_seq, run_emit x s hE hx]
  rw [run_emit y _ (by rw [Function.update_of_ne hOE.symm]; exact hE) (Src.ok_upd_O y s _ hy),
    Src.val_upd_O y s _ hy]
  funext i
  simp only [run_copy, run_prim, Prim.apply, Function.update_apply]
  split_ifs <;> simp_all [List.append_assoc]

/-! ### The representation of a program -/

/-- The store represents the program `p` with the current wire `w`. -/
def Rep (s : Store 40) (p : SLP (Fin 10)) (w : Wire (Fin 10)) : Prop :=
  s O = unparse (toGates 10 p) ∧ s G = un (1 + 10 + p.length) ∧ s W = un (wireIdx 10 w) ∧
    s E = []

theorem unparse_snoc (p : SLP (Fin 10)) (g : Gate (Fin 10)) :
    unparse (toGates 10 (p ++ [g])) =
      unparse (toGates 10 p) ++ (un (wireIdx 10 g.a) ++ [false] ++ un (wireIdx 10 g.b) ++ [false]) := by
  simp [unparse, toGates, List.append_assoc]

/-- **A gate** extends the represented program by `addNand`. -/
theorem rep_gateP {s : Store 40} {p : SLP (Fin 10)} {w a b : Wire (Fin 10)} (h : Rep s p w)
    {x y : Src} (hx : x.Ok s) (hy : y.Ok s) (hxa : x.val s = wireIdx 10 a)
    (hyb : y.val s = wireIdx 10 b) :
    Rep (run (gateP x y) s) (addNand p a b).1 (addNand p a b).2 ∧
      ∀ t, ¬ gateTapes t → run (gateP x y) s t = s t := by
  obtain ⟨hO, hG, hW, hE⟩ := h
  rw [run_gateP x y s hE hx hy, hxa, hyb]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun t ht => ?_⟩
  · simp [addNand, unparse_snoc, hO, List.append_assoc]
  · simp only [Function.update_self, hG, addNand, List.length_append, List.length_singleton]
    rw [← List.replicate_succ']; rfl
  · simp [addNand, hG, wireIdx]
  · simpa using hE
  · simp only [gateTapes, not_or] at ht
    simp [Function.update_of_ne ht.1, Function.update_of_ne ht.2.1, Function.update_of_ne ht.2.2]

/-! ### The steps -/

/-- The tapes written by the steps. -/
def stepTapes (t : Fin 40) : Prop := t = O ∨ t = W ∨ t = G ∨ t = S1 ∨ t = S2

theorem stepTapes_of_gate {t : Fin 40} (h : gateTapes t) : stepTapes t := by
  rcases h with h | h | h <;> simp [stepTapes, h]

/-- `x ∧ W`, the result on `W`. -/
def andStep (x : Src) : Prog 40 := gateP x (.tape W) ⨾ gateP .one (.tape W)

/-- `x ∨ W` (`W` saved on `S2`). -/
def orStep (x : Src) : Prog 40 :=
  cp S2 W ⨾ gateP .one x ⨾ cp S1 W ⨾ gateP .one (.tape S2) ⨾ gateP (.tape S1) (.tape W)

theorem Rep.okW {s : Store 40} {p : SLP (Fin 10)} {w : Wire (Fin 10)} (h : Rep s p w) :
    (Src.tape W).Ok s ∧ (Src.tape W).val s = wireIdx 10 w := by
  refine ⟨⟨by decide, by decide, by rw [h.2.2.1]; simp⟩, by simp [Src.val, h.2.2.1]⟩

/-- A source tape other than the step tapes. -/
def Src.Away : Src → Prop
  | .tape t => ¬ stepTapes t
  | _ => True

theorem Src.val_eq_of_away {x : Src} (hx : x.Away) {s s' : Store 40}
    (h : ∀ t, ¬ stepTapes t → s' t = s t) : x.val s' = x.val s := by
  cases x with
  | one => rfl
  | inp _ => rfl
  | tape t => simp [Src.val, h t hx]

theorem Src.ok_of_away {x : Src} (hx : x.Away) {s s' : Store 40}
    (h : ∀ t, ¬ stepTapes t → s' t = s t) (hok : x.Ok s) : x.Ok s' := by
  cases x with
  | one => trivial
  | inp _ => trivial
  | tape t => exact ⟨hok.1, hok.2.1, by rw [h t hx]; exact hok.2.2⟩

theorem rep_andStep {s : Store 40} {p : SLP (Fin 10)} {w a : Wire (Fin 10)} (h : Rep s p w)
    {x : Src} (hx : x.Ok s) (hxa : x.val s = wireIdx 10 a) :
    Rep (run (andStep x) s) (andW p a w).1 (andW p a w).2 ∧
      ∀ t, ¬ stepTapes t → run (andStep x) s t = s t := by
  obtain ⟨hW1, hW2⟩ := h.okW
  obtain ⟨h1, f1⟩ := rep_gateP h hx hW1 hxa hW2
  obtain ⟨hW1', hW2'⟩ := h1.okW
  obtain ⟨h2, f2⟩ := rep_gateP h1 (x := .one) (a := .one) trivial hW1' rfl hW2'
  refine ⟨by simpa [andStep, andW, notW] using h2, fun t ht => ?_⟩
  have hg : ¬ gateTapes t := fun hg => ht (stepTapes_of_gate hg)
  simp only [andStep, run_seq]; rw [f2 t hg, f1 t hg]

theorem rep_cp {s : Store 40} {p : SLP (Fin 10)} {w : Wire (Fin 10)} (h : Rep s p w) {t : Fin 40}
    (hO : t ≠ O) (hG : t ≠ G) (hW : t ≠ W) (hE : t ≠ E) :
    Rep (run (cp t W) s) p w ∧ run (cp t W) s t = s W ∧
      ∀ u, u ≠ t → run (cp t W) s u = s u := by
  simp only [run_copy]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, by simp, fun u hu => by simp [Function.update_of_ne hu]⟩
  · rw [Function.update_of_ne hO.symm]; exact h.1
  · rw [Function.update_of_ne hG.symm]; exact h.2.1
  · rw [Function.update_of_ne hW.symm]; exact h.2.2.1
  · rw [Function.update_of_ne hE.symm]; exact h.2.2.2

theorem rep_orStep {s : Store 40} {p : SLP (Fin 10)} {w a : Wire (Fin 10)} (h : Rep s p w)
    {x : Src} (hx : x.Ok s) (hxa : x.val s = wireIdx 10 a) (haw : x.Away) :
    Rep (run (orStep x) s) (orW p a w).1 (orW p a w).2 ∧
      ∀ t, ¬ stepTapes t → run (orStep x) s t = s t := by
  obtain ⟨h1, h1S2, f1⟩ := rep_cp h (t := S2) (by decide) (by decide) (by decide) (by decide)
  have f1' : ∀ t, ¬ stepTapes t → run (cp S2 W) s t = s t := fun t ht =>
    f1 t (fun e => ht (by simp [stepTapes, e]))
  have hx1 := Src.ok_of_away haw f1' hx
  have hxa1 := (Src.val_eq_of_away haw f1').trans hxa
  obtain ⟨h2, f2⟩ := rep_gateP h1 (x := .one) (a := .one) trivial hx1 rfl hxa1
  obtain ⟨h3, h3S1, f3⟩ := rep_cp h2 (t := S1) (by decide) (by decide) (by decide) (by decide)
  have hS2 : run (cp S1 W) (run (gateP .one x) (run (cp S2 W) s)) S2 = un (wireIdx 10 w) := by
    rw [f3 S2 (by decide), f2 S2 (by simp [gateTapes]), h1S2, h.2.2.1]
  obtain ⟨h4, f4⟩ := rep_gateP h3 (x := .one) (y := .tape S2) (a := .one) (b := w) trivial
    ⟨by decide, by decide, by rw [hS2]; simp⟩ rfl (by show List.length _ = _; rw [hS2]; simp)
  have hS1 : run (gateP .one (.tape S2)) (run (cp S1 W) (run (gateP .one x) (run (cp S2 W) s))) S1 =
      un (wireIdx 10 (addNand p .one a).2) := by
    rw [f4 S1 (by simp [gateTapes]), h3S1, h2.2.2.1]
  obtain ⟨hW1, hW2⟩ := h4.okW
  obtain ⟨h5, f5⟩ := rep_gateP h4 (x := .tape S1) (y := .tape W)
    (a := (addNand p .one a).2) ⟨by decide, by decide, by rw [hS1]; simp⟩ hW1
    (by show List.length _ = _; rw [hS1]; simp) hW2
  refine ⟨by simpa [orStep, orW, notW] using h5, fun t ht => ?_⟩
  have hg : ¬ gateTapes t := fun hg => ht (stepTapes_of_gate hg)
  simp only [orStep, run_seq]
  rw [f5 t hg, f4 t hg, f3 t (fun e => ht (by simp [stepTapes, e])), f2 t hg, f1' t ht]

/-- One step of `leConst` (`W` the previous result, saved on `S2`). -/
def leStep (x : Src) (b : Bool) : Prog 40 :=
  cp S2 W ⨾ gateP .one x ⨾
    (if b then gateP .one (.tape W) ⨾ cp S1 W ⨾ gateP .one (.tape S2) ⨾ gateP (.tape S1) (.tape W)
     else gateP (.tape W) (.tape S2) ⨾ gateP .one (.tape W))

theorem rep_leStep {s : Store 40} {p : SLP (Fin 10)} {w a : Wire (Fin 10)} (h : Rep s p w)
    {x : Src} (hx : x.Ok s) (hxa : x.val s = wireIdx 10 a) (haw : x.Away) (b : Bool) :
    Rep (run (leStep x b) s)
      (if b then orW (notW p a).1 (notW p a).2 w else andW (notW p a).1 (notW p a).2 w).1
      (if b then orW (notW p a).1 (notW p a).2 w else andW (notW p a).1 (notW p a).2 w).2 ∧
      ∀ t, ¬ stepTapes t → run (leStep x b) s t = s t := by
  obtain ⟨h1, h1S2, f1⟩ := rep_cp h (t := S2) (by decide) (by decide) (by decide) (by decide)
  have f1' : ∀ t, ¬ stepTapes t → run (cp S2 W) s t = s t := fun t ht =>
    f1 t (fun e => ht (by simp [stepTapes, e]))
  have hx1 := Src.ok_of_away haw f1' hx
  have hxa1 := (Src.val_eq_of_away haw f1').trans hxa
  obtain ⟨h2, f2⟩ := rep_gateP h1 (x := .one) (a := .one) trivial hx1 rfl hxa1
  set s2 := run (gateP .one x) (run (cp S2 W) s)
  have hS2 : s2 S2 = un (wireIdx 10 w) := by
    rw [f2 S2 (by simp [gateTapes]), h1S2, h.2.2.1]
  have f12 : ∀ t, ¬ stepTapes t → s2 t = s t := fun t ht => by
    rw [f2 t (fun hg => ht (stepTapes_of_gate hg)), f1' t ht]
  cases b
  · -- `andW n w`
    obtain ⟨hW1, hW2⟩ := h2.okW
    obtain ⟨h3, f3⟩ := rep_gateP h2 (x := .tape W) (y := .tape S2) (b := w) hW1
      ⟨by decide, by decide, by rw [hS2]; simp⟩ hW2 (by show List.length _ = _; rw [hS2]; simp)
    obtain ⟨hW1', hW2'⟩ := h3.okW
    obtain ⟨h4, f4⟩ := rep_gateP h3 (x := .one) (a := .one) trivial hW1' rfl hW2'
    refine ⟨by simpa [leStep, andW, notW, s2] using h4, fun t ht => ?_⟩
    have hg : ¬ gateTapes t := fun hg => ht (stepTapes_of_gate hg)
    simp only [leStep, run_seq, Bool.false_eq_true, ↓reduceIte]
    rw [f4 t hg, f3 t hg]; exact f12 t ht
  · -- `orW n w`
    obtain ⟨hW1, hW2⟩ := h2.okW
    obtain ⟨h3, f3⟩ := rep_gateP h2 (x := .one) (a := .one) trivial hW1 rfl hW2
    obtain ⟨h4, h4S1, f4⟩ := rep_cp h3 (t := S1) (by decide) (by decide) (by decide) (by decide)
    have hS2' : run (cp S1 W) (run (gateP .one (.tape W)) s2) S2 = un (wireIdx 10 w) := by
      rw [f4 S2 (by decide), f3 S2 (by simp [gateTapes]), hS2]
    obtain ⟨h5, f5⟩ := rep_gateP h4 (x := .one) (y := .tape S2) (a := .one) (b := w) trivial
      ⟨by decide, by decide, by rw [hS2']; simp⟩ rfl (by show List.length _ = _; rw [hS2']; simp)
    have hS1 : run (gateP .one (.tape S2)) (run (cp S1 W) (run (gateP .one (.tape W)) s2)) S1 =
        un (wireIdx 10 (addNand (notW p a).1 .one (notW p a).2).2) := by
      rw [f5 S1 (by simp [gateTapes]), h4S1, h3.2.2.1]; rfl
    obtain ⟨hW1', hW2'⟩ := h5.okW
    obtain ⟨h6, f6⟩ := rep_gateP h5 (x := .tape S1) (y := .tape W)
      (a := (addNand (notW p a).1 .one (notW p a).2).2) ⟨by decide, by decide, by rw [hS1]; simp⟩
      hW1' (by show List.length _ = _; rw [hS1]; simp) hW2'
    refine ⟨by simpa [leStep, orW, notW, s2] using h6, fun t ht => ?_⟩
    have hg : ¬ gateTapes t := fun hg => ht (stepTapes_of_gate hg)
    simp only [leStep, run_seq, ↓reduceIte]
    rw [f6 t hg, f5 t hg, f4 t (fun e => ht (by simp [stepTapes, e])), f3 t hg]; exact f12 t ht

/-! ### Comparisons with constants -/

/-- `geConst` with static bits. -/
def geS : List (Fin 10) → List Bool → Prog 40
  | x :: xs, a :: as => geS xs as ⨾ (if a then andStep (.inp x) else orStep (.inp x))
  | _, _ => clr W

/-- `leConst` with static bits. -/
def leS : List (Fin 10) → List Bool → Prog 40
  | x :: xs, b :: bs => leS xs bs ⨾ leStep (.inp x) b
  | _, _ => clr W

/-- `geConst` with the bits popped from tape `t` (least significant first). -/
def geTS (t : Fin 40) : List (Fin 10) → Prog 40
  | [] => clr W
  | x :: xs => geTS t xs ⨾ pp t Z ⨾ ifBit Z (andStep (.inp x)) (orStep (.inp x)) ⨾ clr Z

/-- `leConst` with the bits popped from tape `t`. -/
def leTS (t : Fin 40) : List (Fin 10) → Prog 40
  | [] => clr W
  | x :: xs => leTS t xs ⨾ pp t Z ⨾ ifBit Z (leStep (.inp x) true) (leStep (.inp x) false) ⨾ clr Z

theorem rep_clrW {s : Store 40} {p : SLP (Fin 10)} {w : Wire (Fin 10)} (h : Rep s p w) :
    Rep (run (clr W) s) p .one ∧ ∀ t, ¬ stepTapes t → run (clr W) s t = s t := by
  simp only [run_clear]
  refine ⟨⟨by simp [h.1], by simp [h.2.1], by simp [wireIdx], by simp [h.2.2.2]⟩, fun t ht => ?_⟩
  rw [Function.update_of_ne (fun e => ht (by simp [stepTapes, e]))]

theorem wireIdx_input (i : Fin 10) : wireIdx 10 (.input i) = 1 + i.val := rfl

theorem rep_geS {s : Store 40} {p : SLP (Fin 10)} {w : Wire (Fin 10)} (h : Rep s p w) :
    ∀ (is : List (Fin 10)) (as : List Bool),
      Rep (run (geS is as) s) (geConst p (is.map .input) as).1 (geConst p (is.map .input) as).2 ∧
        ∀ t, ¬ stepTapes t → run (geS is as) s t = s t
  | [], as => by simpa [geS, geConst] using rep_clrW h
  | x :: xs, [] => by simpa [geS, geConst] using rep_clrW h
  | x :: xs, a :: as => by
    obtain ⟨h1, f1⟩ := rep_geS h xs as
    cases a
    · obtain ⟨h2, f2⟩ := rep_orStep h1 (x := .inp x) (a := .input x) trivial
        (wireIdx_input x).symm trivial
      refine ⟨by simpa [geS, geConst] using h2, fun t ht => ?_⟩
      simp only [geS, run_seq, Bool.false_eq_true, ↓reduceIte]; rw [f2 t ht, f1 t ht]
    · obtain ⟨h2, f2⟩ := rep_andStep h1 (x := .inp x) (a := .input x) trivial
        (wireIdx_input x).symm
      refine ⟨by simpa [geS, geConst] using h2, fun t ht => ?_⟩
      simp only [geS, run_seq, ↓reduceIte]; rw [f2 t ht, f1 t ht]

theorem rep_leS {s : Store 40} {p : SLP (Fin 10)} {w : Wire (Fin 10)} (h : Rep s p w) :
    ∀ (is : List (Fin 10)) (bs : List Bool),
      Rep (run (leS is bs) s) (leConst p (is.map .input) bs).1 (leConst p (is.map .input) bs).2 ∧
        ∀ t, ¬ stepTapes t → run (leS is bs) s t = s t
  | [], bs => by simpa [leS, leConst] using rep_clrW h
  | x :: xs, [] => by simpa [leS, leConst] using rep_clrW h
  | x :: xs, b :: bs => by
    obtain ⟨h1, f1⟩ := rep_leS h xs bs
    obtain ⟨h2, f2⟩ := rep_leStep h1 (x := .inp x) (a := .input x) trivial (wireIdx_input x).symm
      trivial b
    refine ⟨by cases b <;> simpa [leS, leConst] using h2, fun t ht => ?_⟩
    simp only [leS, run_seq]; rw [f2 t ht, f1 t ht]

/-- A source tape of constants: away from the layout. -/
def SrcTape (t : Fin 40) : Prop := ¬ stepTapes t ∧ t ≠ E ∧ t ≠ Z

theorem rep_pp {s : Store 40} {p : SLP (Fin 10)} {w : Wire (Fin 10)} (h : Rep s p w) {t : Fin 40}
    (ht : SrcTape t) :
    Rep (run (pp t Z) s) p w ∧ run (pp t Z) s t = (s t).tail ∧ run (pp t Z) s Z = (s t).take 1 ∧
      ∀ u, u ≠ t → u ≠ Z → run (pp t Z) s u = s u := by
  have h1 : t ≠ O := fun e => ht.1 (by simp [stepTapes, e])
  have h2 : t ≠ G := fun e => ht.1 (by simp [stepTapes, e])
  have h3 : t ≠ W := fun e => ht.1 (by simp [stepTapes, e])
  simp only [run_pop]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, by simp [ht.2.2], by simp, fun u hu hz => ?_⟩
  · rw [Function.update_of_ne (by decide), Function.update_of_ne h1.symm]; exact h.1
  · rw [Function.update_of_ne (by decide), Function.update_of_ne h2.symm]; exact h.2.1
  · rw [Function.update_of_ne (by decide), Function.update_of_ne h3.symm]; exact h.2.2.1
  · rw [Function.update_of_ne (by decide), Function.update_of_ne ht.2.1.symm]; exact h.2.2.2
  · rw [Function.update_of_ne hz, Function.update_of_ne hu]

theorem rep_clrZ {s : Store 40} {p : SLP (Fin 10)} {w : Wire (Fin 10)} (h : Rep s p w) :
    Rep (run (clr Z) s) p w ∧ ∀ u, u ≠ Z → run (clr Z) s u = s u := by
  simp only [run_clear]
  refine ⟨⟨by simp [h.1], by simp [h.2.1], by simp [h.2.2.1], by simp [h.2.2.2]⟩,
    fun u hu => by rw [Function.update_of_ne hu]⟩

theorem rep_geTS {t : Fin 40} (ht : SrcTape t) {p : SLP (Fin 10)} {w : Wire (Fin 10)} :
    ∀ (is : List (Fin 10)) (as rest : List Bool) (s : Store 40), Rep s p w →
      as.length = is.length → s t = as.reverse ++ rest →
      Rep (run (geTS t is) s) (geConst p (is.map .input) as).1 (geConst p (is.map .input) as).2 ∧
        run (geTS t is) s t = rest ∧
        ∀ u, ¬ stepTapes u → u ≠ Z → u ≠ t → run (geTS t is) s u = s u
  | [], as, rest, s, h, hl, hs => by
    obtain rfl : as = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    obtain ⟨h1, f1⟩ := rep_clrW h
    exact ⟨by simpa [geTS, geConst] using h1, by rw [geTS, f1 t ht.1, hs]; rfl,
      fun u hu _ _ => f1 u hu⟩
  | x :: xs, [], rest, s, h, hl, hs => by simp at hl
  | x :: xs, a :: as, rest, s, h, hl, hs => by
    have hs' : s t = as.reverse ++ (a :: rest) := by rw [hs]; simp
    obtain ⟨h1, h1t, f1⟩ := rep_geTS ht xs as (a :: rest) s h (by simpa using hl) hs'
    set s1 := run (geTS t xs) s
    obtain ⟨h2, h2t, h2Z, f2⟩ := rep_pp h1 ht
    rw [h1t] at h2t h2Z
    set s2 := run (pp t Z) s1
    have hZ : hd (s2 Z) = a := by rw [h2Z]; rfl
    have hgo : ∀ q : Prog 40, run (geTS t (x :: xs)) s =
        run (clr Z) (run (ifBit Z (andStep (.inp x)) (orStep (.inp x))) s2) := fun _ => rfl
    cases a
    · obtain ⟨h3, f3⟩ := rep_orStep h2 (x := .inp x) (a := .input x) trivial
        (wireIdx_input x).symm trivial
      obtain ⟨h4, f4⟩ := rep_clrZ h3
      have e : run (geTS t (x :: xs)) s = run (clr Z) (run (orStep (.inp x)) s2) := by
        rw [hgo (clr Z)]; simp [run_ifBit, hZ]
      refine ⟨by rw [e]; simpa [geConst] using h4, ?_, fun u hu hz hut => ?_⟩
      · rw [e, f4 t ht.2.2, f3 t ht.1, h2t]; rfl
      · rw [e, f4 u hz, f3 u hu, f2 u hut hz, f1 u hu hz hut]
    · obtain ⟨h3, f3⟩ := rep_andStep h2 (x := .inp x) (a := .input x) trivial
        (wireIdx_input x).symm
      obtain ⟨h4, f4⟩ := rep_clrZ h3
      have e : run (geTS t (x :: xs)) s = run (clr Z) (run (andStep (.inp x)) s2) := by
        rw [hgo (clr Z)]; simp [run_ifBit, hZ]
      refine ⟨by rw [e]; simpa [geConst] using h4, ?_, fun u hu hz hut => ?_⟩
      · rw [e, f4 t ht.2.2, f3 t ht.1, h2t]; rfl
      · rw [e, f4 u hz, f3 u hu, f2 u hut hz, f1 u hu hz hut]

theorem rep_leTS {t : Fin 40} (ht : SrcTape t) {p : SLP (Fin 10)} {w : Wire (Fin 10)} :
    ∀ (is : List (Fin 10)) (bs rest : List Bool) (s : Store 40), Rep s p w →
      bs.length = is.length → s t = bs.reverse ++ rest →
      Rep (run (leTS t is) s) (leConst p (is.map .input) bs).1 (leConst p (is.map .input) bs).2 ∧
        run (leTS t is) s t = rest ∧
        ∀ u, ¬ stepTapes u → u ≠ Z → u ≠ t → run (leTS t is) s u = s u
  | [], bs, rest, s, h, hl, hs => by
    obtain rfl : bs = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    obtain ⟨h1, f1⟩ := rep_clrW h
    exact ⟨by simpa [leTS, leConst] using h1, by rw [leTS, f1 t ht.1, hs]; rfl,
      fun u hu _ _ => f1 u hu⟩
  | x :: xs, [], rest, s, h, hl, hs => by simp at hl
  | x :: xs, b :: bs, rest, s, h, hl, hs => by
    have hs' : s t = bs.reverse ++ (b :: rest) := by rw [hs]; simp
    obtain ⟨h1, h1t, f1⟩ := rep_leTS ht xs bs (b :: rest) s h (by simpa using hl) hs'
    set s1 := run (leTS t xs) s
    obtain ⟨h2, h2t, h2Z, f2⟩ := rep_pp h1 ht
    rw [h1t] at h2t h2Z
    set s2 := run (pp t Z) s1
    have hZ : hd (s2 Z) = b := by rw [h2Z]; rfl
    obtain ⟨h3, f3⟩ := rep_leStep h2 (x := .inp x) (a := .input x) trivial (wireIdx_input x).symm
      trivial b
    obtain ⟨h4, f4⟩ := rep_clrZ h3
    have e : run (leTS t (x :: xs)) s = run (clr Z) (run (leStep (.inp x) b) s2) := by
      show run (clr Z) (run (ifBit Z (leStep (.inp x) true) (leStep (.inp x) false)) s2) = _
      cases b <;> simp [run_ifBit, hZ]
    refine ⟨by rw [e]; cases b <;> simpa [leConst] using h4, ?_, fun u hu hz hut => ?_⟩
    · rw [e, f4 t ht.2.2, f3 t ht.1, h2t]; rfl
    · rw [e, f4 u hz, f3 u hu, f2 u hut hz, f1 u hu hz hut]

/-! ### Boolean combinations -/

/-- Comparison expressions whose constants are static or read from tapes. -/
inductive DExp
  | ge (is : List (Fin 10)) (as : List Bool)
  | le (is : List (Fin 10)) (bs : List Bool)
  | geT (is : List (Fin 10)) (t : Fin 40)
  | leT (is : List (Fin 10)) (t : Fin 40)
  | not (e : DExp)
  | and (e f : DExp)
  | or (e f : DExp)

namespace DExp

/-- The expression, the tape constants read (most significant bit last) from `env`. -/
def toB (env : Store 40) : DExp → BExp (Fin 10)
  | ge is as => .ge is as
  | le is bs => .le is bs
  | geT is t => .ge is (env t).reverse
  | leT is t => .le is (env t).reverse
  | not e => .not (toB env e)
  | and e f => .and (toB env e) (toB env f)
  | or e f => .or (toB env e) (toB env f)

/-- The registers needed. -/
def depth : DExp → ℕ
  | not e => depth e
  | and e f => max (depth e) (depth f + 1)
  | or e f => max (depth e) (depth f + 1)
  | _ => 0

/-- The tapes of the constants. -/
def srcs : DExp → List (Fin 40)
  | geT _ t => [t]
  | leT _ t => [t]
  | not e => srcs e
  | and e f => srcs e ++ srcs f
  | or e f => srcs e ++ srcs f
  | _ => []

/-- A register tape. -/
def IsReg (t : Fin 40) : Prop := 8 ≤ t.val ∧ t.val < 24

/-- The constants are readable: on their own tapes, of the right lengths. -/
def SrcOk (s : Store 40) : DExp → Prop
  | geT is t => SrcTape t ∧ ¬ IsReg t ∧ (s t).length = is.length
  | leT is t => SrcTape t ∧ ¬ IsReg t ∧ (s t).length = is.length
  | not e => SrcOk s e
  | and e f => SrcOk s e ∧ SrcOk s f ∧ ∀ t ∈ srcs e, t ∉ srcs f
  | or e f => SrcOk s e ∧ SrcOk s f ∧ ∀ t ∈ srcs e, t ∉ srcs f
  | _ => True

theorem toB_congr {s s' : Store 40} : ∀ e : DExp, (∀ t ∈ srcs e, s' t = s t) → toB s' e = toB s e
  | ge _ _, _ => rfl
  | le _ _, _ => rfl
  | geT is t, h => by simp [toB, h t (by simp [srcs])]
  | leT is t, h => by simp [toB, h t (by simp [srcs])]
  | not e, h => by simp [toB, toB_congr e h]
  | and e f, h => by
    simp [toB, toB_congr e (fun t ht => h t (by simp [srcs, ht])),
      toB_congr f (fun t ht => h t (by simp [srcs, ht]))]
  | or e f, h => by
    simp [toB, toB_congr e (fun t ht => h t (by simp [srcs, ht])),
      toB_congr f (fun t ht => h t (by simp [srcs, ht]))]

theorem srcOk_congr {s s' : Store 40} : ∀ e : DExp, (∀ t ∈ srcs e, s' t = s t) →
    SrcOk s e → SrcOk s' e
  | ge _ _, _, h => h
  | le _ _, _, h => h
  | geT is t, hs, h => ⟨h.1, h.2.1, by rw [hs t (by simp [srcs])]; exact h.2.2⟩
  | leT is t, hs, h => ⟨h.1, h.2.1, by rw [hs t (by simp [srcs])]; exact h.2.2⟩
  | not e, hs, h => srcOk_congr e hs h
  | and e f, hs, h => ⟨srcOk_congr e (fun t ht => hs t (by simp [srcs, ht])) h.1,
      srcOk_congr f (fun t ht => hs t (by simp [srcs, ht])) h.2.1, h.2.2⟩
  | or e f, hs, h => ⟨srcOk_congr e (fun t ht => hs t (by simp [srcs, ht])) h.1,
      srcOk_congr f (fun t ht => hs t (by simp [srcs, ht])) h.2.1, h.2.2⟩

end DExp

/-- **The generator**: the gates of `compile p e`, the registers from depth `d` on. -/
def genE : ℕ → DExp → Prog 40
  | _, .ge is as => geS is as
  | _, .le is bs => leS is bs
  | _, .geT is t => geTS t is
  | _, .leT is t => leTS t is
  | d, .not e => genE d e ⨾ gateP .one (.tape W)
  | d, .and e f => genE d e ⨾ cp (R d) W ⨾ genE (d + 1) f ⨾ andStep (.tape (R d))
  | d, .or e f => genE d e ⨾ cp (R d) W ⨾ genE (d + 1) f ⨾ orStep (.tape (R d))

/-- The tapes the generator may change. -/
def Clob (d : ℕ) (e : DExp) (u : Fin 40) : Prop :=
  stepTapes u ∨ u = Z ∨ (∃ j, d ≤ j ∧ j < 16 ∧ u = R j) ∨ u ∈ e.srcs

theorem R_val {d : ℕ} (hd : d < 16) : (R d).val = 8 + d := by simp [R, Nat.mod_eq_of_lt hd]

theorem R_not_step {d : ℕ} : ¬ stepTapes (R d) := by
  simp only [stepTapes, R]
  intro h; rcases h with h | h | h | h | h <;> simp [Fin.ext_iff] at h <;> omega

theorem R_ne_E {d : ℕ} : R d ≠ E := by simp [R, Fin.ext_iff]; omega
theorem R_ne_Z {d : ℕ} : R d ≠ Z := by simp [R, Fin.ext_iff]; omega

theorem R_ne_O {d : ℕ} : R d ≠ O := by simp [R, Fin.ext_iff]; omega
theorem R_ne_G {d : ℕ} : R d ≠ G := by simp [R, Fin.ext_iff]; omega
theorem R_ne_W {d : ℕ} : R d ≠ W := by simp [R, Fin.ext_iff]; omega

theorem R_isReg (d : ℕ) : DExp.IsReg (R d) := by simp [DExp.IsReg, R]; omega

theorem R_inj {d j : ℕ} (hd : d < 16) (hj : j < 16) (h : R j = R d) : j = d := by
  have := congrArg Fin.val h; rw [R_val hj, R_val hd] at this; omega

theorem src_not_clob {e f : DExp} {d : ℕ} {s : Store 40} (hf : f.SrcOk s)
    (hdisj : ∀ t ∈ e.srcs, t ∉ f.srcs) : ∀ t ∈ f.srcs, ¬ Clob d e t ∧ t ≠ R d := by
  have key : ∀ g : DExp, g.SrcOk s → ∀ t ∈ g.srcs, SrcTape t ∧ ¬ DExp.IsReg t := by
    intro g
    induction g with
    | geT is u => intro h t ht; simp [DExp.srcs] at ht; subst ht; exact ⟨h.1, h.2.1⟩
    | leT is u => intro h t ht; simp [DExp.srcs] at ht; subst ht; exact ⟨h.1, h.2.1⟩
    | not g ih => intro h t ht; exact ih h t ht
    | and g g' ih ih' =>
      intro h t ht; simp only [DExp.srcs, List.mem_append] at ht
      rcases ht with ht | ht
      · exact ih h.1 t ht
      · exact ih' h.2.1 t ht
    | or g g' ih ih' =>
      intro h t ht; simp only [DExp.srcs, List.mem_append] at ht
      rcases ht with ht | ht
      · exact ih h.1 t ht
      · exact ih' h.2.1 t ht
    | ge => intro _ t ht; simp [DExp.srcs] at ht
    | le => intro _ t ht; simp [DExp.srcs] at ht
  intro t ht
  obtain ⟨hs, hr⟩ := key f hf t ht
  refine ⟨fun hc => ?_, fun e' => hr (e' ▸ R_isReg d)⟩
  rcases hc with hc | hc | ⟨j, -, -, hc⟩ | hc
  · exact hs.1 hc
  · exact hs.2.2 hc
  · exact hr (hc ▸ R_isReg j)
  · exact hdisj t hc ht

/-- The two operands of a binary combination, the left result saved on `R d`. -/
theorem run_bin (e f : DExp) (d : ℕ) (s : Store 40) (p : SLP (Fin 10)) (w : Wire (Fin 10))
    (h : Rep s p w) (hd16 : d < 16) (hde : d + e.depth ≤ 16) (hdf : d + 1 + f.depth ≤ 16)
    (hoke : e.SrcOk s) (hokf : f.SrcOk s) (hdisj : ∀ t ∈ e.srcs, t ∉ f.srcs)
    (IHe : Rep (run (genE d e) s) (SLP.compile p (e.toB s)).1 (SLP.compile p (e.toB s)).2 ∧
      ∀ u, ¬ Clob d e u → run (genE d e) s u = s u)
    (IHf : ∀ (s' : Store 40) (p' : SLP (Fin 10)) (w' : Wire (Fin 10)), Rep s' p' w' →
      d + 1 + f.depth ≤ 16 → f.SrcOk s' →
      Rep (run (genE (d + 1) f) s') (SLP.compile p' (f.toB s')).1 (SLP.compile p' (f.toB s')).2 ∧
        ∀ u, ¬ Clob (d + 1) f u → run (genE (d + 1) f) s' u = s' u) :
    Rep (run (genE (d + 1) f) (run (cp (R d) W) (run (genE d e) s)))
        (SLP.compile (SLP.compile p (e.toB s)).1 (f.toB s)).1
        (SLP.compile (SLP.compile p (e.toB s)).1 (f.toB s)).2 ∧
      (∀ u, ¬ Clob d (.and e f) u →
        run (genE (d + 1) f) (run (cp (R d) W) (run (genE d e) s)) u = s u) ∧
      run (genE (d + 1) f) (run (cp (R d) W) (run (genE d e) s)) (R d) =
        un (wireIdx 10 (SLP.compile p (e.toB s)).2) := by
  obtain ⟨h1, f1⟩ := IHe
  obtain ⟨h2, h2R, f2⟩ := rep_cp h1 (t := R d) R_ne_O R_ne_G R_ne_W R_ne_E
  have hsrc := src_not_clob (d := d) hokf hdisj
  have hs2 : ∀ t ∈ f.srcs, run (cp (R d) W) (run (genE d e) s) t = s t := fun t ht => by
    rw [f2 t (hsrc t ht).2, f1 t (hsrc t ht).1]
  obtain ⟨h3, f3⟩ := IHf _ _ _ h2 hdf (DExp.srcOk_congr f hs2 hokf)
  rw [DExp.toB_congr f hs2] at h3
  refine ⟨h3, fun u hu => ?_, ?_⟩
  · have hu1 : ¬ Clob d e u := fun hc => hu (by
      rcases hc with hc | hc | hc | hc
      · exact Or.inl hc
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr (Or.inl hc))
      · exact Or.inr (Or.inr (Or.inr (by simp [DExp.srcs, hc]))))
    have hu2 : u ≠ R d := fun e' => hu (Or.inr (Or.inr (Or.inl ⟨d, le_rfl, hd16, e'⟩)))
    have hu3 : ¬ Clob (d + 1) f u := fun hc => hu (by
      rcases hc with hc | hc | ⟨j, hj1, hj2, hc⟩ | hc
      · exact Or.inl hc
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr (Or.inl ⟨j, by omega, hj2, hc⟩))
      · exact Or.inr (Or.inr (Or.inr (by simp [DExp.srcs, hc]))))
    rw [f3 u hu3, f2 u hu2, f1 u hu1]
  · rw [f3 (R d) (fun hc => by
      rcases hc with hc | hc | ⟨j, hj1, hj2, hc⟩ | hc
      · exact R_not_step hc
      · exact R_ne_Z hc
      · have := R_inj hd16 hj2 hc.symm; omega
      · exact (hsrc (R d) hc).2 rfl), h2R, h1.2.2.1]


/-- **The generator writes the compiled gates.** -/
theorem run_genE : ∀ (e : DExp) (d : ℕ) (s : Store 40) (p : SLP (Fin 10)) (w : Wire (Fin 10)),
    Rep s p w → d + e.depth ≤ 16 → e.SrcOk s →
    Rep (run (genE d e) s) (compile p (e.toB s)).1 (compile p (e.toB s)).2 ∧
      ∀ u, ¬ Clob d e u → run (genE d e) s u = s u
  | .ge is as, d, s, p, w, h, _, _ => by
    obtain ⟨h1, f1⟩ := rep_geS h is as
    exact ⟨h1, fun u hu => f1 u (fun hs => hu (Or.inl hs))⟩
  | .le is bs, d, s, p, w, h, _, _ => by
    obtain ⟨h1, f1⟩ := rep_leS h is bs
    exact ⟨h1, fun u hu => f1 u (fun hs => hu (Or.inl hs))⟩
  | .geT is t, d, s, p, w, h, _, hok => by
    obtain ⟨h1, -, f1⟩ := rep_geTS hok.1 is (s t).reverse [] s h (by simp [hok.2.2]) (by simp)
    refine ⟨h1, fun u hu => f1 u (fun hs => hu (Or.inl hs)) (fun hz => hu (Or.inr (Or.inl hz)))
      (fun ht => hu (Or.inr (Or.inr (Or.inr (by simp [DExp.srcs, ht])))))⟩
  | .leT is t, d, s, p, w, h, _, hok => by
    obtain ⟨h1, -, f1⟩ := rep_leTS hok.1 is (s t).reverse [] s h (by simp [hok.2.2]) (by simp)
    refine ⟨h1, fun u hu => f1 u (fun hs => hu (Or.inl hs)) (fun hz => hu (Or.inr (Or.inl hz)))
      (fun ht => hu (Or.inr (Or.inr (Or.inr (by simp [DExp.srcs, ht])))))⟩
  | .not e, d, s, p, w, h, hd, hok => by
    obtain ⟨h1, f1⟩ := run_genE e d s p w h (by simpa [DExp.depth] using hd) hok
    obtain ⟨hW1, hW2⟩ := h1.okW
    obtain ⟨h2, f2⟩ := rep_gateP h1 (x := .one) (a := .one) trivial hW1 rfl hW2
    refine ⟨by simpa [genE, DExp.toB, SLP.compile, notW] using h2, fun u hu => ?_⟩
    simp only [genE, run_seq]
    rw [f2 u (fun hg => hu (Or.inl (stepTapes_of_gate hg))), f1 u (fun hc => hu (by
      simpa [Clob, DExp.srcs] using hc))]
  | .and e f, d, s, p, w, h, hd, hok => by
    simp only [DExp.depth] at hd
    obtain ⟨hoke, hokf, hdisj⟩ := hok
    obtain ⟨h3, f123, hR3⟩ := run_bin e f d s p w h (by omega) (by omega) (by omega) hoke hokf hdisj
      (run_genE e d s p w h (by omega) hoke) (run_genE f (d + 1))
    obtain ⟨h4, f4⟩ := rep_andStep h3 (x := .tape (R d)) (a := (SLP.compile p (e.toB s)).2) ⟨R_ne_O, R_ne_E, by rw [hR3]; simp⟩
      (by show List.length _ = _; rw [hR3]; simp)
    refine ⟨by simpa [genE, DExp.toB, SLP.compile] using h4, fun u hu => ?_⟩
    simp only [genE, run_seq]
    rw [f4 u (fun hs => hu (Or.inl hs))]
    exact f123 u hu
  | .or e f, d, s, p, w, h, hd, hok => by
    simp only [DExp.depth] at hd
    obtain ⟨hoke, hokf, hdisj⟩ := hok
    obtain ⟨h3, f123, hR3⟩ := run_bin e f d s p w h (by omega) (by omega) (by omega) hoke hokf hdisj
      (run_genE e d s p w h (by omega) hoke) (run_genE f (d + 1))
    obtain ⟨h4, f4⟩ := rep_orStep h3 (x := .tape (R d)) (a := (SLP.compile p (e.toB s)).2) ⟨R_ne_O, R_ne_E, by rw [hR3]; simp⟩
      (by show List.length _ = _; rw [hR3]; simp) R_not_step
    refine ⟨by simpa [genE, DExp.toB, SLP.compile] using h4, fun u hu => ?_⟩
    simp only [genE, run_seq]
    rw [f4 u (fun hs => hu (Or.inl hs))]
    exact f123 u hu
end GateGen

end SigabaNeo.Tape
