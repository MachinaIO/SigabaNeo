import SigabaNeo.Lib.Machines.Prog.XAbs
import SigabaNeo.Lib.Machines.Prog.XFlat
import SigabaNeo.Lib.Machines.Prog.Stream

/-!
# A machine on words with a framed step

`ValVM` runs straight-line and looping code over `nW = 64` **word tapes** with one expensive
two-argument operation, the **step** `f` (e.g. the step of a simulation on joint words), computed by
a tape program `P : Prog 132` that is generic (`VStep`): it computes `f` on words of `V` bits on its
tapes `1`, `2` into `0`, given a precondition `Pre` on its other tapes.

* `Code`: `gate d a b` (`d := f (a, b)`, operands cut to `V` bits), `mvV d s` (move `V` bits of the
  stream `s` into the register `d`), `mv d s c` (move `|c|` bits), `cp`, `drop`, `clr`, `tl`,
  `rep c body` (`|c|` rounds), `seq`, `nop`.
* `exec V f c w`: the semantics on the words `w : Fin 64 → List Bool` (total).
* `compileA cert c : XAst H nT`: the program, every instruction in a **frame** of its own tapes (the
  step in the frame of its `132` tapes, with the summary `cert`), so that its per-tape cost is
  certified by `xabs` and each instruction is charged only its own words.
* **`run_flat_compileA`**: on the encoding `enc s₀ V w` (the step's store `s₀`, the template `V`,
  the words, blank scratch), the flattened program ends in `enc s₀ V (exec V f c w)`;
  **`law_compileA`**: its law is the point mass there.
-/

namespace SigabaNeo.Tape

namespace ValVM

open Prog _root_.SigabaNeo.Tape.Sym

/-! ### Tapes -/

/-- Word tapes. -/
abbrev nW : ℕ := 64
/-- Tapes: the step's `132`, the template `V`, the words, three scratch tapes. -/
abbrev nT : ℕ := 200

/-- The step's tape `j`. -/
def tS (j : Fin 132) : Fin 200 := ⟨j.val, by have := j.isLt; show j.val < 200; omega⟩
/-- The template of `V` bits. -/
def tTV : Fin 200 := ⟨132, by decide⟩
/-- The word tape `x`. -/
def tWd (x : Fin 64) : Fin 200 := ⟨133 + x.val, by have := x.isLt; show 133 + x.val < 200; omega⟩
/-- Scratch tapes. -/
def tX0 : Fin 200 := ⟨197, by decide⟩
def tX1 : Fin 200 := ⟨198, by decide⟩
def tX2 : Fin 200 := ⟨199, by decide⟩

theorem val_tS (j : Fin 132) : (tS j).val = j.val := rfl
theorem val_tTV : tTV.val = 132 := rfl
theorem val_tX0 : tX0.val = 197 := rfl
theorem val_tX1 : tX1.val = 198 := rfl
theorem val_tX2 : tX2.val = 199 := rfl
theorem val_tWd (x : Fin 64) : (tWd x).val = 133 + x.val := rfl

/-- The step's frame. -/
def eS : Fin 132 ↪ Fin 200 := ⟨tS, fun a b h => Fin.ext (by simpa [tS] using congrArg Fin.val h)⟩

/-! ### The step -/

/-- **A step program**: `P` computes `f` on words of `V` bits (tapes `1`, `2` into `0`) under a
precondition `Pre` on its other tapes. -/
structure VStep (P : Prog 132) (V : ℕ) (f : List Bool → List Bool → List Bool)
    (Pre : Store 132 → Prop) : Prop where
  noGrow : P.NoGrow
  pre_upd : ∀ (s : Store 132) (i : Fin 132), i.val < 3 → ∀ w, Pre s → Pre (Function.update s i w)
  run_eq : ∀ s, Pre s → (s 1).length = V → (s 2).length = V →
    run P s = Function.update s 0 (f (s 1) (s 2))
  len : ∀ a b, a.length = V → b.length = V → (f a b).length = V

/-- **A certified summary of the step** (`fcall`), valid at the variable values satisfying `H`. -/
structure StepCert (H : List ℕ → Prop) (P : Prog 132) where
  σS : Asg
  σS' : Asg
  cS : Poly
  θ : List Poly
  hS : ∀ ρ, H ρ → XSoundAt (.prog P) σS σS' cS (θ.map (pEval ρ))

/-! ### Code and semantics -/

/-- The instructions. -/
inductive Code where
  /-- `d := f (a, b)` (operands cut to `V` bits). -/
  | gate (d a b : Fin 64)
  /-- Move `V` bits from the stream `s` into the register `d` (`d ≠ s`). -/
  | mvV (d s : Fin 64)
  /-- Move `|c|` bits from the stream `s` into the register `d` (pairwise distinct). -/
  | mv (d s c : Fin 64)
  /-- `d := s` (`d ≠ s`). -/
  | cp (d s : Fin 64)
  /-- `t := t.drop |c|` (`t ≠ c`). -/
  | drop (t c : Fin 64)
  /-- `t := []`. -/
  | clr (t : Fin 64)
  /-- `t := t.tail`. -/
  | tl (t : Fin 64)
  /-- `|c|` rounds of the body, each after dropping the first bit of `c`. -/
  | rep (c : Fin 64) (body : Code)
  | seq (p q : Code)
  /-- `p` if the first bit of `t` is `true`, else `q`. -/
  | ifb (t : Fin 64) (p q : Code)
  | nop

/-- Words. -/
abbrev St := Fin 64 → List Bool

/-- Shift `m` bits of the stream `s` into the register `r`. -/
def shiftIn (m : ℕ) (r s : List Bool) : List Bool := (r ++ takeD m s).drop m

/-- **The semantics.** -/
def exec (V : ℕ) (f : List Bool → List Bool → List Bool) : Code → St → St
  | .gate d a b, w => Function.update w d (f (takeD V (w a)) (takeD V (w b)))
  | .mvV d s, w => if d = s then w else
      Function.update (Function.update w s ((w s).drop V)) d (shiftIn V (w d) (w s))
  | .mv d s c, w => if d = s ∨ d = c ∨ s = c then w else
      Function.update (Function.update w s ((w s).drop (w c).length)) d
        (shiftIn (w c).length (w d) (w s))
  | .cp d s, w => Function.update w d (w s)
  | .drop t c, w => if t = c then w else Function.update w t ((w t).drop (w c).length)
  | .clr t, w => Function.update w t []
  | .tl t, w => Function.update w t (w t).tail
  | .rep c body, w =>
    (fun w' => exec V f body (Function.update w' c (w' c).tail))^[(w c).length] w
  | .seq p q, w => exec V f q (exec V f p w)
  | .ifb t p q, w => if hd (w t) = true then exec V f p w else exec V f q w
  | .nop, w => w

/-! ### The frames of the instructions -/

/-- An embedding from an injective function. -/
def mkE {m n : ℕ} (f : Fin m → Fin n) (h : Function.Injective f) : Fin m ↪ Fin n := ⟨f, h⟩

/-- A tape map from its values. -/
def ofV {m : ℕ} (g : ℕ → ℕ) (hg : ∀ j < m, g j < 200) : Fin m → Fin 200 :=
  fun j => ⟨g j.val, hg j.val j.isLt⟩

theorem ofV_inj {m : ℕ} {g : ℕ → ℕ} {hg : ∀ j < m, g j < 200}
    (h : ∀ x y, x < m → y < m → g x = g y → x = y) : Function.Injective (ofV g hg) :=
  fun x y hxy => Fin.ext (h x.val y.val x.isLt y.isLt (congrArg Fin.val hxy))

/-- Operand in: `[step tape i, TV, word a, X0, X1, X2]`. -/
def fIn (i : Fin 132) (a : Fin 64) : Fin 6 → Fin 200 :=
  ofV (fun j => if j = 0 then i.val else if j = 1 then 132 else if j = 2 then 133 + a.val
    else 194 + j) (by intro j hj; have := i.isLt; have := a.isLt; show _ < 200; split_ifs <;> omega)

theorem fIn_inj (i : Fin 132) (a : Fin 64) : Function.Injective (fIn i a) :=
  ofV_inj (by intro x y hx hy h; have := i.isLt; have := a.isLt; split_ifs at h <;> omega)

/-- Result out: `[step 0, step 1, step 2, word d]`. -/
def fOut (d : Fin 64) : Fin 4 → Fin 200 :=
  ofV (fun j => if j < 3 then j else 133 + d.val) (by
    intro j hj; have := d.isLt; show _ < 200; split_ifs <;> omega)

theorem fOut_inj (d : Fin 64) : Function.Injective (fOut d) :=
  ofV_inj (by intro x y hx hy h; split_ifs at h <;> omega)

/-- `mvP` on `[stream s, register d, X1, X2, template c]`. -/
def fMv (d s : Fin 64) (c : Fin 200) : Fin 5 → Fin 200 :=
  ofV (fun j => if j = 0 then 133 + s.val else if j = 1 then 133 + d.val else if j = 2 then 198
    else if j = 3 then 199 else c.val) (by
    intro j hj; have := d.isLt; have := s.isLt; have := c.isLt; show _ < 200; split_ifs <;> omega)

theorem fMv_inj {d s : Fin 64} {c : Fin 200} (hds : d ≠ s) (hc : c.val < 133 ∨ (c.val < 197 ∧
    c ≠ tWd d ∧ c ≠ tWd s)) : Function.Injective (fMv d s c) := by
  have hds' : d.val ≠ s.val := fun h => hds (Fin.ext h)
  have hc' : c.val < 133 ∨ (c.val < 197 ∧ c.val ≠ 133 + d.val ∧ c.val ≠ 133 + s.val) := by
    rcases hc with hc | ⟨hc, hcd, hcs⟩
    · exact Or.inl hc
    · exact Or.inr ⟨hc, fun h => hcd (Fin.ext h), fun h => hcs (Fin.ext h)⟩
  exact ofV_inj (by intro x y hx hy h; split_ifs at h <;> omega)

theorem fMv_inj_wd {d s c : Fin 64} (h : ¬(d = s ∨ d = c ∨ s = c)) :
    Function.Injective (fMv d s (tWd c)) :=
  fMv_inj (fun e => h (Or.inl e)) (Or.inr ⟨by
    have := c.isLt; show 133 + c.val < 197; omega,
    fun e => h (Or.inr (Or.inl (by
      have := congrArg Fin.val e; simp only [tWd] at this; exact Fin.ext (by omega)))),
    fun e => h (Or.inr (Or.inr (by
      have := congrArg Fin.val e; simp only [tWd] at this; exact Fin.ext (by omega))))⟩)

/-- `cp 0 1` on `[word d, word s]`. -/
def fCp (d s : Fin 64) : Fin 2 → Fin 200 :=
  ofV (fun j => if j = 0 then 133 + d.val else 133 + s.val) (by
    intro j hj; have := d.isLt; have := s.isLt; show _ < 200; split_ifs <;> omega)

theorem fCp_inj {d s : Fin 64} (h : d ≠ s) : Function.Injective (fCp d s) := by
  have hds : d.val ≠ s.val := fun e => h (Fin.ext e)
  exact ofV_inj (by intro x y hx hy h; split_ifs at h <;> omega)

/-- `dropP` on `[word t, X1, word c]`. -/
def fDr (t c : Fin 64) : Fin 3 → Fin 200 :=
  ofV (fun j => if j = 0 then 133 + t.val else if j = 1 then 198 else 133 + c.val) (by
    intro j hj; have := t.isLt; have := c.isLt; show _ < 200; split_ifs <;> omega)

theorem fDr_inj {t c : Fin 64} (h : t ≠ c) : Function.Injective (fDr t c) := by
  have htc : t.val ≠ c.val := fun e => h (Fin.ext e)
  exact ofV_inj (by intro x y hx hy h; split_ifs at h <;> omega)

/-- One tape. -/
def f1 (t : Fin 200) : Fin 1 → Fin 200 := fun _ => t

theorem f1_inj (t : Fin 200) : Function.Injective (f1 t) := fun x y _ => Subsingleton.elim x y

/-- Operand in: `step i := TV`, `X0 := a`, move `V` bits of `X0` into `step i`, clear `X0`. -/
def inP : Prog 6 := cp 0 1 ⨾ cp 3 2 ⨾ map ![3, 0, 4, 5, 1] mvP ⨾ clr 3

/-- Result out: `d := step 0`, clear the step's tapes `0 1 2`. -/
def outP : Prog 4 := cp 3 0 ⨾ clr 0 ⨾ clr 1 ⨾ clr 2

/-! ### The compiler -/

open XAst in
/-- **The program of a code**, each instruction in the frame of its own tapes. -/
def compileA {H : List ℕ → Prop} {P : Prog 132} (cert : StepCert H P) : Code → XAst H nT
  | .gate d a b =>
    .seq (.frame (mkE (fIn 1 a) (fIn_inj 1 a)) (.leafA inP)) <|
    .seq (.frame (mkE (fIn 2 b) (fIn_inj 2 b)) (.leafA inP)) <|
    .seq (.fcall eS (.prog P) cert.σS cert.σS' cert.cS cert.θ cert.hS)
      (.frame (mkE (fOut d) (fOut_inj d)) (.leafA outP))
  | .mvV d s => if h : d = s then .frame (mkE (f1 tX0) (f1_inj _)) (.leafA (nop 0)) else
      .frame (mkE (fMv d s tTV) (fMv_inj h (Or.inl (by decide)))) (.leafA mvP)
  | .mv d s c => if h : d = s ∨ d = c ∨ s = c then .frame (mkE (f1 tX0) (f1_inj _)) (.leafA (nop 0))
      else .frame (mkE (fMv d s (tWd c)) (fMv_inj_wd h))
        (.leafA mvP)
  | .cp d s => if h : d = s then .frame (mkE (f1 tX0) (f1_inj _)) (.leafA (nop 0)) else
      .frame (mkE (fCp d s) (fCp_inj h)) (.leafA (Prog.cp 0 1))
  | .drop t c => if h : t = c then .frame (mkE (f1 tX0) (f1_inj _)) (.leafA (nop 0)) else
      .frame (mkE (fDr t c) (fDr_inj h)) (.leafA dropP)
  | .clr t => .frame (mkE (f1 (tWd t)) (f1_inj _)) (.leafA (Prog.clr 0))
  | .tl t => .frame (mkE (f1 (tWd t)) (f1_inj _)) (.leafA (Prog.tl 0))
  | .rep c body => .loopA (tWd c) (compileA cert body)
  | .seq p q => .seq (compileA cert p) (compileA cert q)
  | .ifb t p q => .ifBit (tWd t) (compileA cert p) (compileA cert q)
  | .nop => .frame (mkE (f1 tX0) (f1_inj _)) (.leafA (nop 0))

/-! ### The encoding -/

/-- The store of a state: the step's store `s₀`, the template of `V` bits, the words, blank
scratch. -/
def enc (s₀ : Store 132) (V : ℕ) (w : St) : Store 200 := fun t =>
  if h : t.val < 132 then s₀ ⟨t.val, h⟩ else if t.val = 132 then List.replicate V false
  else if h' : t.val < 197 then w ⟨t.val - 133, by omega⟩ else []

section Enc

variable {s₀ : Store 132} {V : ℕ} {w : St}

@[simp] theorem enc_tS (j : Fin 132) : enc s₀ V w (tS j) = s₀ j := by
  simp [enc, tS]

@[simp] theorem enc_tTV : enc s₀ V w tTV = List.replicate V false := by simp [enc, tTV]

@[simp] theorem enc_tWd (x : Fin 64) : enc s₀ V w (tWd x) = w x := by
  have h1 : ¬ (tWd x).val < 132 := by show ¬ (133 + x.val < 132); omega
  have h2 : ¬ (tWd x).val = 132 := by show ¬ (133 + x.val = 132); omega
  have h3 : (tWd x).val < 197 := by show 133 + x.val < 197; have := x.isLt; omega
  unfold enc
  rw [dite_eq_right_of_eq_false (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2),
    dite_eq_left_of_eq_true (eq_true h3)]
  exact congrArg w (Fin.ext (by show 133 + x.val - 133 = x.val; omega))

@[simp] theorem enc_tX0 : enc s₀ V w tX0 = [] := by simp [enc, tX0]
@[simp] theorem enc_tX1 : enc s₀ V w tX1 = [] := by simp [enc, tX1]
@[simp] theorem enc_tX2 : enc s₀ V w tX2 = [] := by simp [enc, tX2]

theorem tape_cases (t : Fin 200) : (∃ j, t = tS j) ∨ t = tTV ∨ (∃ x, t = tWd x) ∨ t = tX0 ∨
    t = tX1 ∨ t = tX2 := by
  by_cases h1 : t.val < 132
  · exact Or.inl ⟨⟨t.val, h1⟩, Fin.ext rfl⟩
  by_cases h2 : t.val = 132
  · exact Or.inr (Or.inl (Fin.ext h2))
  by_cases h3 : t.val < 197
  · exact Or.inr (Or.inr (Or.inl ⟨⟨t.val - 133, by omega⟩, Fin.ext (by simp [tWd]; omega)⟩))
  have := t.isLt
  by_cases h4 : t.val = 197
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h4))))
  by_cases h5 : t.val = 198
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h5)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext (by simp [tX2]; omega))))))

theorem enc_ext {s s' : Store 200} (h1 : ∀ j, s (tS j) = s' (tS j)) (h2 : s tTV = s' tTV)
    (h3 : ∀ x, s (tWd x) = s' (tWd x)) (h4 : s tX0 = s' tX0) (h5 : s tX1 = s' tX1)
    (h6 : s tX2 = s' tX2) : s = s' := by
  funext t
  rcases tape_cases t with ⟨j, rfl⟩ | rfl | ⟨x, rfl⟩ | rfl | rfl | rfl
  exacts [h1 j, h2, h3 x, h4, h5, h6]

theorem tS_ne_tWd (j : Fin 132) (x : Fin 64) : tS j ≠ tWd x := fun h => by
  have := congrArg Fin.val h; simp [tS, tWd] at this; omega

theorem tWd_inj {x y : Fin 64} (h : tWd x = tWd y) : x = y :=
  Fin.ext (by have := congrArg Fin.val h; simp [tWd] at this; omega)

theorem update_tWd (x : Fin 64) (v : List Bool) :
    Function.update (enc s₀ V w) (tWd x) v = enc s₀ V (Function.update w x v) := by
  refine enc_ext (fun j => ?_) ?_ (fun y => ?_) ?_ ?_ ?_
  · rw [Function.update_of_ne (tS_ne_tWd j x)]; simp
  · rw [Function.update_of_ne (by simp [tTV, tWd, Fin.ext_iff]; omega)]; simp
  · by_cases h : y = x
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h (tWd_inj e))]; simp [Function.update_of_ne h]
  all_goals (rw [Function.update_of_ne (by simp [tX0, tX1, tX2, tWd, Fin.ext_iff]; omega)]; simp)

theorem update_tS (j : Fin 132) (v : List Bool) :
    Function.update (enc s₀ V w) (tS j) v = enc (Function.update s₀ j v) V w := by
  refine enc_ext (fun i => ?_) ?_ (fun y => ?_) ?_ ?_ ?_
  · by_cases h : i = j
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h (Fin.ext (by have := congrArg Fin.val e; simpa [tS] using this)))]
      simp [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp [tTV, tS, Fin.ext_iff]; omega)]; simp
  · rw [Function.update_of_ne (tS_ne_tWd j y).symm]; simp
  all_goals (rw [Function.update_of_ne (by simp [tX0, tX1, tX2, tS, Fin.ext_iff]; omega)]; simp)

theorem enc_comp_eS : (fun j => enc s₀ V w (eS j)) = s₀ := funext fun j => enc_tS j

theorem enc_comp_eS' : enc s₀ V w ∘ ⇑eS = s₀ := funext fun j => enc_tS j

theorem extend_eS (g : Store 132) :
    Function.extend eS g (enc s₀ V w) = enc g V w := by
  refine enc_ext (fun j => ?_) ?_ (fun y => ?_) ?_ ?_ ?_
  · show Function.extend eS g _ (eS j) = _
    rw [eS.injective.extend_apply]; simp
  all_goals
    rw [Function.extend_apply']
    · simp
    · rintro ⟨j, hj⟩
      have := congrArg Fin.val hj
      have hj' : (eS j).val = j.val := rfl
      have := j.isLt
      simp only [hj', val_tTV, val_tWd, val_tX0, val_tX1, val_tX2] at *
      omega

theorem tailAt_tWd (x : Fin 64) : tailAt (tWd x) (enc s₀ V w) = enc s₀ V
    (Function.update w x (w x).tail) := by
  rw [tailAt, enc_tWd, update_tWd]

end Enc

/-! ### The local programs -/

theorem drop_shift {r : List Bool} {n : ℕ} (h : r.length = n) (w : List Bool) :
    shiftIn n r w = takeD n w := by
  subst h; simp [shiftIn]

theorem inv_in : Function.Injective (![3, 0, 4, 5, 1] : Fin 5 → Fin 6) := by decide

theorem run_inP (t : Store 6) (h3 : t 3 = []) (h4 : t 4 = []) (h5 : t 5 = []) :
    run inP t = Function.update t 0 (takeD (t 1).length (t 2)) := by
  simp only [inP, run_seq, run_copy, run_clear]
  rw [run_mvP_map inv_in _ (by simp [h4]) (by simp [h5])]
  funext i
  fin_cases i <;> simp [h3]

theorem run_outP (t : Store 4) :
    run outP t = Function.update (Function.update (Function.update (Function.update t 3 (t 0))
      0 []) 1 []) 2 [] := by
  simp [outP, run_seq, run_copy, run_clear]

/-! ### The tapes of the frames -/

section Frames

variable {i : Fin 132} {a d s c t : Fin 64}

theorem mkE_apply {m n : ℕ} (f : Fin m → Fin n) (h : Function.Injective f) (j : Fin m) :
    mkE f h j = f j := rfl

theorem fIn_0 : fIn i a 0 = tS i := Fin.ext (by simp [fIn, ofV, tS])
theorem fIn_1 : fIn i a 1 = tTV := Fin.ext (by simp [fIn, ofV, tTV])
theorem fIn_2 : fIn i a 2 = tWd a := Fin.ext (by simp [fIn, ofV, tWd])
theorem fIn_3 : fIn i a 3 = tX0 := Fin.ext (by simp [fIn, ofV, tX0])
theorem fIn_4 : fIn i a 4 = tX1 := Fin.ext (by simp [fIn, ofV, tX1])
theorem fIn_5 : fIn i a 5 = tX2 := Fin.ext (by simp [fIn, ofV, tX2])
theorem fOut_0 : fOut d 0 = tS 0 := Fin.ext (by simp [fOut, ofV, tS])
theorem fOut_1 : fOut d 1 = tS 1 := Fin.ext (by simp [fOut, ofV, tS])
theorem fOut_2 : fOut d 2 = tS 2 := Fin.ext (by simp [fOut, ofV, tS])
theorem fOut_3 : fOut d 3 = tWd d := Fin.ext (by simp [fOut, ofV, tWd])
theorem fMv_0 {c' : Fin 200} : fMv d s c' 0 = tWd s := Fin.ext (by simp [fMv, ofV, tWd])
theorem fMv_1 {c' : Fin 200} : fMv d s c' 1 = tWd d := Fin.ext (by simp [fMv, ofV, tWd])
theorem fMv_2 {c' : Fin 200} : fMv d s c' 2 = tX1 := Fin.ext (by simp [fMv, ofV, tX1])
theorem fMv_3 {c' : Fin 200} : fMv d s c' 3 = tX2 := Fin.ext (by simp [fMv, ofV, tX2])
theorem fMv_4 {c' : Fin 200} : fMv d s c' 4 = c' := Fin.ext (by simp [fMv, ofV])
theorem fCp_0 : fCp d s 0 = tWd d := Fin.ext (by simp [fCp, ofV, tWd])
theorem fCp_1 : fCp d s 1 = tWd s := Fin.ext (by simp [fCp, ofV, tWd])
theorem fDr_0 : fDr t c 0 = tWd t := Fin.ext (by simp [fDr, ofV, tWd])
theorem fDr_1 : fDr t c 1 = tX1 := Fin.ext (by simp [fDr, ofV, tX1])
theorem fDr_2 : fDr t c 2 = tWd c := Fin.ext (by simp [fDr, ofV, tWd])

end Frames

/-! ### Correctness of the compiler -/

section Correct

variable {H : List ℕ → Prop} {P : Prog 132} (cert : StepCert H P) {V : ℕ}
  {f : List Bool → List Bool → List Bool} {Pre : Store 132 → Prop}

theorem run_nopF (s₀ : Store 132) (w : St) :
    run (XProg.flat (XAst.toX (.frame (mkE (f1 tX0) (f1_inj _)) (.leafA (nop 0)) :
      XAst H 200))) (enc s₀ V w) = enc s₀ V w := by
  show run (map (f1 tX0) (nop 0)) _ = _
  rw [run_map (f1_inj _)]
  simp only [run_nop]
  exact extend_comp_self _

theorem run_map_outP {u : Fin 4 → Fin 200} (hu : Function.Injective u) (S : Store 200) :
    run (map u outP) S = Function.update (Function.update (Function.update (Function.update S
      (u 3) (S (u 0))) (u 0) []) (u 1) []) (u 2) [] := by
  rw [run_map hu, run_outP, extend_update hu, extend_update hu, extend_update hu,
    extend_update hu, extend_comp_self]
  rfl

theorem run_gate (hP : VStep P V f Pre) {s₀ : Store 132} (hpre : Pre s₀) (h0 : s₀ 0 = [])
    (h1 : s₀ 1 = []) (h2 : s₀ 2 = []) (d a b : Fin 64) (w : St) :
    run (XProg.flat (compileA cert (.gate d a b)).toX) (enc s₀ V w) =
      enc s₀ V (exec V f (.gate d a b) w) := by
  show run (map (fIn 1 a) inP ⨾ (map (fIn 2 b) inP ⨾ (map eS P ⨾ map (fOut d) outP))) _ = _
  simp only [run_seq]
  -- the operands
  have r1 : run (map (fIn 1 a) inP) (enc s₀ V w) =
      enc (Function.update s₀ 1 (takeD V (w a))) V w := by
    rw [run_map_eq_update (fIn_inj 1 a) inP _ 0 _ (run_inP _ (by simp [fIn_3])
      (by simp [fIn_4]) (by simp [fIn_5]))]
    simp only [Function.comp_apply, fIn_0, fIn_1, fIn_2, enc_tTV, enc_tWd,
      List.length_replicate, update_tS]
  rw [r1]
  have r2 : run (map (fIn 2 b) inP) (enc (Function.update s₀ 1 (takeD V (w a))) V w) =
      enc (Function.update (Function.update s₀ 1 (takeD V (w a))) 2 (takeD V (w b))) V w := by
    rw [run_map_eq_update (fIn_inj 2 b) inP _ 0 _ (run_inP _ (by simp [fIn_3])
      (by simp [fIn_4]) (by simp [fIn_5]))]
    simp only [Function.comp_apply, fIn_0, fIn_1, fIn_2, enc_tTV, enc_tWd,
      List.length_replicate, update_tS]
  rw [r2]
  -- the step
  set s₁ := Function.update (Function.update s₀ 1 (takeD V (w a))) 2 (takeD V (w b))
  have hpre₁ : Pre s₁ := hP.pre_upd _ 2 (by decide) _ (hP.pre_upd _ 1 (by decide) _ hpre)
  have hs1 : s₁ 1 = takeD V (w a) := by simp [s₁]
  have hs2 : s₁ 2 = takeD V (w b) := by simp [s₁]
  rw [run_map eS.injective, enc_comp_eS', hP.run_eq s₁ hpre₁ (by rw [hs1]; simp)
    (by rw [hs2]; simp), extend_eS, hs1, hs2]
  -- the result
  rw [run_map_outP (fOut_inj d), fOut_0, fOut_1, fOut_2, fOut_3, enc_tS, Function.update_self,
    update_tWd, update_tS, update_tS, update_tS]
  congr 1
  funext j
  simp only [s₁, Function.update_apply]
  split_ifs <;> simp_all

theorem run_mvF {d s : Fin 64} {c' : Fin 200} (h : Function.Injective (fMv d s c')) (s₀ : Store 132)
    (w : St) (hc : enc s₀ V w c' = (w' : List Bool)) :
    run (map (fMv d s c') mvP) (enc s₀ V w) =
      enc s₀ V (Function.update (Function.update w s ((w s).drop w'.length)) d
        (shiftIn w'.length (w d) (w s))) := by
  rw [run_mvP_map h _ (by rw [fMv_2]; simp) (by rw [fMv_3]; simp)]
  simp only [fMv_0, fMv_1, fMv_4, enc_tWd, hc, update_tWd]
  rfl

theorem run_flat_compileA (hP : VStep P V f Pre) {s₀ : Store 132} (hpre : Pre s₀)
    (h0 : s₀ 0 = []) (h1 : s₀ 1 = []) (h2 : s₀ 2 = []) :
    ∀ (c : Code) (w : St),
      run (XProg.flat (compileA cert c).toX) (enc s₀ V w) = enc s₀ V (exec V f c w)
  | .gate d a b, w => run_gate cert hP hpre h0 h1 h2 d a b w
  | .mvV d s, w => by
    by_cases h : d = s
    · rw [show compileA cert (.mvV d s) = .frame (mkE (f1 tX0) (f1_inj _)) (.leafA (nop 0)) from
        dite_eq_left_of_eq_true (eq_true h) .., run_nopF]
      simp [exec, h]
    · rw [show compileA cert (.mvV d s) = .frame (mkE (fMv d s tTV) (fMv_inj h (Or.inl (by decide))))
        (.leafA mvP) from dite_eq_right_of_eq_false (eq_false h) ..]
      show run (map (fMv d s tTV) mvP) _ = _
      rw [run_mvF (fMv_inj h (Or.inl (by decide))) s₀ w enc_tTV]
      simp [exec, h]
  | .mv d s c, w => by
    by_cases h : d = s ∨ d = c ∨ s = c
    · rw [show compileA cert (.mv d s c) = .frame (mkE (f1 tX0) (f1_inj _)) (.leafA (nop 0)) from
        dite_eq_left_of_eq_true (eq_true h) .., run_nopF]
      simp [exec, h]
    · simp only [compileA, dite_eq_right_of_eq_false (eq_false h) ..]
      show run (map (fMv d s (tWd c)) mvP) _ = _
      rw [run_mvF (fMv_inj_wd h) s₀ w (enc_tWd c)]
      simp [exec, h]
  | .cp d s, w => by
    by_cases h : d = s
    · rw [show compileA cert (.cp d s) = .frame (mkE (f1 tX0) (f1_inj _)) (.leafA (nop 0)) from
        dite_eq_left_of_eq_true (eq_true h) .., run_nopF]
      subst h; simp [exec]
    · rw [show compileA cert (.cp d s) = .frame (mkE (fCp d s) (fCp_inj h)) (.leafA (Prog.cp 0 1))
        from dite_eq_right_of_eq_false (eq_false h) ..]
      show run (map (fCp d s) (Prog.cp 0 1)) _ = _
      rw [run_map_eq_update (fCp_inj h) _ _ 0 _ (run_copy 0 1 _)]
      simp [fCp_0, fCp_1, update_tWd, exec]
  | .drop t c, w => by
    by_cases h : t = c
    · rw [show compileA cert (.drop t c) = .frame (mkE (f1 tX0) (f1_inj _)) (.leafA (nop 0)) from
        dite_eq_left_of_eq_true (eq_true h) .., run_nopF]
      simp [exec, h]
    · rw [show compileA cert (.drop t c) = .frame (mkE (fDr t c) (fDr_inj h)) (.leafA dropP)
        from dite_eq_right_of_eq_false (eq_false h) ..]
      show run (map (fDr t c) dropP) _ = _
      rw [run_dropP_map (fDr_inj h) _ (by rw [fDr_1]; simp)]
      simp [fDr_0, fDr_2, update_tWd, exec, h]
  | .clr t, w => by
    show run (map (f1 (tWd t)) (Prog.clr 0)) _ = _
    rw [run_map_eq_update (f1_inj _) _ _ 0 _ (run_clear 0 _)]
    simp [f1, update_tWd, exec]
  | .tl t, w => by
    show run (map (f1 (tWd t)) (Prog.tl 0)) _ = _
    rw [run_map_eq_update (f1_inj _) _ _ 0 _ (run_tail 0 _)]
    simp [f1, update_tWd, exec]
  | .rep c body, w => by
    show run (Prog.loop (tWd c) (XProg.flat (compileA cert body).toX)) _ = _
    rw [run_loop, enc_tWd, exec]
    have ih := run_flat_compileA hP hpre h0 h1 h2 body
    have key : ∀ (m : ℕ) (w' : St),
        (fun t => run (XProg.flat (compileA cert body).toX) (tailAt (tWd c) t))^[m] (enc s₀ V w') =
          enc s₀ V ((fun w'' => exec V f body (Function.update w'' c (w'' c).tail))^[m] w') := by
      intro m
      induction m with
      | zero => intro w'; rfl
      | succ m ihm =>
        intro w'
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, tailAt_tWd, ih, ihm]
    exact key _ w
  | .seq p q, w => by
    show run (XProg.flat (compileA cert p).toX ⨾ XProg.flat (compileA cert q).toX) _ = _
    rw [run_seq, run_flat_compileA hP hpre h0 h1 h2 p, run_flat_compileA hP hpre h0 h1 h2 q]
    rfl
  | .ifb t p q, w => by
    show run (Prog.ifBit (tWd t) (XProg.flat (compileA cert p).toX)
      (XProg.flat (compileA cert q).toX)) _ = _
    rw [run_ifBit, enc_tWd, exec]
    split_ifs
    · exact run_flat_compileA hP hpre h0 h1 h2 p w
    · exact run_flat_compileA hP hpre h0 h1 h2 q w
  | .nop, w => run_nopF _ _

theorem noGrow_flat_compileA (hP : VStep P V f Pre) :
    ∀ c : Code, (XProg.flat (compileA cert c).toX).NoGrow
  | .gate d a b => by
    show (map (fIn 1 a) inP ⨾ (map (fIn 2 b) inP ⨾ (map eS P ⨾ map (fOut d) outP))).noGrowB = true
    simp only [noGrowB, noGrowB_map, Bool.and_eq_true]
    exact ⟨rfl, rfl, hP.noGrow, rfl⟩
  | .mvV d s => by
    unfold compileA; split_ifs
    · show (map _ (nop 0)).noGrowB = true; rw [noGrowB_map]; rfl
    · show (map _ mvP).noGrowB = true; rw [noGrowB_map]; rfl
  | .mv d s c => by
    unfold compileA; split_ifs
    · show (map _ (nop 0)).noGrowB = true; rw [noGrowB_map]; rfl
    · show (map _ mvP).noGrowB = true; rw [noGrowB_map]; rfl
  | .cp d s => by
    unfold compileA; split_ifs
    · show (map _ (nop 0)).noGrowB = true; rw [noGrowB_map]; rfl
    · show (map _ (Prog.cp 0 1)).noGrowB = true; rw [noGrowB_map]; rfl
  | .drop t c => by
    unfold compileA; split_ifs
    · show (map _ (nop 0)).noGrowB = true; rw [noGrowB_map]; rfl
    · show (map _ dropP).noGrowB = true; rw [noGrowB_map]; rfl
  | .clr t => by show (map _ (Prog.clr 0)).noGrowB = true; rw [noGrowB_map]; rfl
  | .tl t => by show (map _ (Prog.tl 0)).noGrowB = true; rw [noGrowB_map]; rfl
  | .rep c body => noGrow_flat_compileA hP body
  | .seq p q => by
    show (XProg.flat (compileA cert p).toX).noGrowB && (XProg.flat (compileA cert q).toX).noGrowB = true
    rw [noGrow_flat_compileA hP p, noGrow_flat_compileA hP q]; rfl
  | .ifb t p q => by
    show (XProg.flat (compileA cert p).toX).noGrowB && (XProg.flat (compileA cert q).toX).noGrowB = true
    rw [noGrow_flat_compileA hP p, noGrow_flat_compileA hP q]; rfl
  | .nop => by show (map _ (nop 0)).noGrowB = true; rw [noGrowB_map]; rfl

/-- **The law of a compiled code**: the point mass at the encoding of its semantics. -/
theorem law_compileA (hP : VStep P V f Pre) {s₀ : Store 132} (hpre : Pre s₀)
    (h0 : s₀ 0 = []) (h1 : s₀ 1 = []) (h2 : s₀ 2 = []) (c : Code) (w : St) :
    (compileA cert c).toX.law (enc s₀ V w) = PMF.pure (enc s₀ V (exec V f c w)) := by
  rw [XProg.law_eq_run_flat _ (noGrow_flat_compileA cert hP c),
    run_flat_compileA cert hP hpre h0 h1 h2 c w]

end Correct

end ValVM

end SigabaNeo.Tape
