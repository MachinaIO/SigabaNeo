import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.Aut
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.Canon
import SigabaNeoStd.Lattices.ProgAlgo.Digits
import SigabaNeoStd.Machines.Prog.ValVM

/-!
# A machine on ring words modulo `2^K − 1`

`RingVM` runs structured code over `nW = 200` **word registers** with the ring operations of
`ℤ_{2^K − 1}[X]/(X^N + 1)` on words of `N K` bits (`SigabaNeoStd.Lattices.ProgAlgo.Mersenne`):

* ring instructions `add`, `sub`, `mul` (`addRMP`, `subRMP`, `mulRMP`), `canon` (`canonRP`), `neg`
  (`notP`), and the instructions with a **template register** `t` (its length is the parameter):
  `digit` (the binary digit `|t|` of every coefficient, `digitRWP`), `rotB` (every coefficient times
  `2^{−|t|}`, `rotBP`), `aut` (`σ_{|t|}`, `autMP`), `rhoJ` (`X^{−|t|}`, `rhoJP`). Their operands
  are first cut to `N K` bits (`takeD`), so the semantics is total;
* the moves of `SigabaNeoStd.Machines.Prog.ValVM`: `mv d s c` (move `|c|` bits of the stream `s`
  into the register `d`), `cp`, `drop`, `clr`, `tl`, and the control `rep c body` (`|c|` rounds),
  `seq`, `ifb t p q` (on the first bit of `t`), `nop`.

`exec N K c w` is the semantics on the words `w : Fin 200 → List Bool`. `compile c : XProg 247`
places the registers on the tapes `47 …`, the templates of `K`, `N`, `N K` bits and the all-ones
word of `N K` bits on `40 … 43`, three scratch tapes on `44 … 46`, and runs every instruction in a
**frame** of its own tapes (the operation's program on the operation area `0 … 39`).

**`run_flat_compile`**: on the encoding `enc N K w` of the words (for `0 < N`, `0 < K`), the
flattened program ends in `enc N K (exec N K c w)`; **`law_compile`**: its law is the point mass
there.
-/

namespace SigabaNeo.Tape

namespace RingVM

open Prog SigabaNeo.Lattices.Algo

/-! ### Tapes -/

/-- Word registers. -/
abbrev nW : ℕ := 200
/-- Tapes: the operation area, four templates, three scratch tapes, the registers. -/
abbrev nT : ℕ := 247

/-- The operation area. -/
def tO (j : ℕ) (h : j < 40 := by omega) : Fin 247 := ⟨j, by omega⟩
/-- The templates: `K`, `N`, `N K` zeros, `N K` ones. -/
def tK : Fin 247 := ⟨40, by decide⟩
def tN : Fin 247 := ⟨41, by decide⟩
def tNK : Fin 247 := ⟨42, by decide⟩
def tOn : Fin 247 := ⟨43, by decide⟩
/-- Scratch tapes. -/
def tX0 : Fin 247 := ⟨44, by decide⟩
def tX1 : Fin 247 := ⟨45, by decide⟩
def tX2 : Fin 247 := ⟨46, by decide⟩
/-- The register `x`. -/
def tWd (x : Fin 200) : Fin 247 := ⟨47 + x.val, by have := x.isLt; omega⟩

/-- A tape map from its values. -/
def ofW {m : ℕ} (g : ℕ → ℕ) (hg : ∀ j < m, g j < 247) : Fin m → Fin 247 :=
  fun j => ⟨g j.val, hg j.val j.isLt⟩

theorem ofW_inj {m : ℕ} {g : ℕ → ℕ} {hg : ∀ j < m, g j < 247}
    (h : ∀ x y, x < m → y < m → g x = g y → x = y) : Function.Injective (ofW g hg) :=
  fun x y hxy => Fin.ext (h x.val y.val x.isLt y.isLt (congrArg Fin.val hxy))

/-- An embedding from an injective function. -/
def mkE {m n : ℕ} (f : Fin m → Fin n) (h : Function.Injective f) : Fin m ↪ Fin n := ⟨f, h⟩

/-! ### Code and semantics -/

/-- The instructions. -/
inductive Code where
  /-- `d := a + b`. -/
  | add (d a b : Fin 200)
  /-- `d := a − b`. -/
  | sub (d a b : Fin 200)
  /-- `d := a · b`. -/
  | mul (d a b : Fin 200)
  /-- `d :=` the canonical word of `a`. -/
  | canon (d a : Fin 200)
  /-- `d := −a` (bitwise NOT). -/
  | neg (d a : Fin 200)
  /-- `d :=` the binary digit `|t|` of the coefficients of `a`. -/
  | digit (d a t : Fin 200)
  /-- `d := 2^{−|t|} a`. -/
  | rotB (d a t : Fin 200)
  /-- `d := σ_{|t|}(a)`. -/
  | aut (d a t : Fin 200)
  /-- `d := X^{−|t|} a`. -/
  | rhoJ (d a t : Fin 200)
  /-- Move `|c|` bits from the stream `s` into the register `d` (pairwise distinct). -/
  | mv (d s c : Fin 200)
  /-- `d := s`. -/
  | cp (d s : Fin 200)
  /-- `t := t.drop |c|`. -/
  | drop (t c : Fin 200)
  /-- `t := []`. -/
  | clr (t : Fin 200)
  /-- `t := t.tail`. -/
  | tl (t : Fin 200)
  /-- `|c|` rounds of the body, each after dropping the first bit of `c`. -/
  | rep (c : Fin 200) (body : Code)
  | seq (p q : Code)
  /-- `p` if the first bit of `t` is `true`, else `q`. -/
  | ifb (t : Fin 200) (p q : Code)
  | nop

/-- Words. -/
abbrev St := Fin 200 → List Bool

/-- An operand cut to `N K` bits. -/
abbrev opd (N K : ℕ) (x : List Bool) : List Bool := takeD (N * K) x

/-- **The semantics.** -/
def exec (N K : ℕ) : Code → St → St
  | .add d a b, w => Function.update w d (addRMW N K (opd N K (w a)) (opd N K (w b)))
  | .sub d a b, w => Function.update w d (subRMW N K (opd N K (w a)) (opd N K (w b)))
  | .mul d a b, w => Function.update w d (mulRMW N K (opd N K (w a)) (opd N K (w b)))
  | .canon d a, w => Function.update w d (canonW N K (opd N K (w a)))
  | .neg d a, w => Function.update w d (notW (opd N K (w a)))
  | .digit d a t, w => Function.update w d (digitRW N K (w t).length (opd N K (w a)))
  | .rotB d a t, w => Function.update w d (rotBW N K (w t).length (opd N K (w a)))
  | .aut d a t, w => Function.update w d (autMW N K (w t).length (opd N K (w a)))
  | .rhoJ d a t, w => Function.update w d ((rhoMW K)^[(w t).length] (opd N K (w a)))
  | .mv d s c, w => if d = s ∨ d = c ∨ s = c then w else
      Function.update (Function.update w s ((w s).drop (w c).length)) d
        (ValVM.shiftIn (w c).length (w d) (w s))
  | .cp d s, w => Function.update w d (w s)
  | .drop t c, w => if t = c then w else Function.update w t ((w t).drop (w c).length)
  | .clr t, w => Function.update w t []
  | .tl t, w => Function.update w t (w t).tail
  | .rep c body, w =>
    (fun w' => exec N K body (Function.update w' c (w' c).tail))^[(w c).length] w
  | .seq p q, w => exec N K q (exec N K p w)
  | .ifb t p q, w => if hd (w t) = true then exec N K p w else exec N K q w
  | .nop, w => w

/-! ### The frames -/

/-- Operand in: `[area i, NK, word a, X0, X1, X2]`. -/
def fIn (i : ℕ) (hi : i < 40) (a : Fin 200) : Fin 6 → Fin 247 :=
  ofW (fun j => if j = 0 then i else if j = 1 then 42 else if j = 2 then 47 + a.val
    else 41 + j) (by intro j hj; have := a.isLt; split_ifs <;> omega)

theorem fIn_inj (i : ℕ) (hi : i < 40) (a : Fin 200) : Function.Injective (fIn i hi a) :=
  ofW_inj (by intro x y hx hy h; have := a.isLt; split_ifs at h <;> omega)

/-- Template in: `[area 2, word t]`. -/
def fTm (t : Fin 200) : Fin 2 → Fin 247 :=
  ofW (fun j => if j = 0 then 2 else 47 + t.val) (by intro j hj; have := t.isLt; split_ifs <;> omega)

theorem fTm_inj (t : Fin 200) : Function.Injective (fTm t) :=
  ofW_inj (by intro x y hx hy h; split_ifs at h <;> omega)

/-- Result out: `[area 0, area 1, area 2, word d]`. -/
def fOut (d : Fin 200) : Fin 4 → Fin 247 :=
  ofW (fun j => if j < 3 then j else 47 + d.val) (by
    intro j hj; have := d.isLt; split_ifs <;> omega)

theorem fOut_inj (d : Fin 200) : Function.Injective (fOut d) :=
  ofW_inj (by intro x y hx hy h; split_ifs at h <;> omega)

/-- `mvP` on `[stream s, register d, X1, X2, word c]`. -/
def fMv (d s c : Fin 200) : Fin 5 → Fin 247 :=
  ofW (fun j => if j = 0 then 47 + s.val else if j = 1 then 47 + d.val else if j = 2 then 45
    else if j = 3 then 46 else 47 + c.val) (by
    intro j hj; have := d.isLt; have := s.isLt; have := c.isLt; split_ifs <;> omega)

theorem fMv_inj {d s c : Fin 200} (h : ¬(d = s ∨ d = c ∨ s = c)) :
    Function.Injective (fMv d s c) := by
  have h1 : d.val ≠ s.val := fun e => h (Or.inl (Fin.ext e))
  have h2 : d.val ≠ c.val := fun e => h (Or.inr (Or.inl (Fin.ext e)))
  have h3 : s.val ≠ c.val := fun e => h (Or.inr (Or.inr (Fin.ext e)))
  exact ofW_inj (by intro x y hx hy h; split_ifs at h <;> omega)

/-- `cp 0 1` on `[word d, word s]`. -/
def fCp (d s : Fin 200) : Fin 2 → Fin 247 :=
  ofW (fun j => if j = 0 then 47 + d.val else 47 + s.val) (by
    intro j hj; have := d.isLt; have := s.isLt; split_ifs <;> omega)

theorem fCp_inj {d s : Fin 200} (h : d ≠ s) : Function.Injective (fCp d s) := by
  have hds : d.val ≠ s.val := fun e => h (Fin.ext e)
  exact ofW_inj (by intro x y hx hy h; split_ifs at h <;> omega)

/-- `dropP` on `[word t, X1, word c]`. -/
def fDr (t c : Fin 200) : Fin 3 → Fin 247 :=
  ofW (fun j => if j = 0 then 47 + t.val else if j = 1 then 45 else 47 + c.val) (by
    intro j hj; have := t.isLt; have := c.isLt; split_ifs <;> omega)

theorem fDr_inj {t c : Fin 200} (h : t ≠ c) : Function.Injective (fDr t c) := by
  have htc : t.val ≠ c.val := fun e => h (Fin.ext e)
  exact ofW_inj (by intro x y hx hy h; split_ifs at h <;> omega)

/-- One tape. -/
def f1 (t : Fin 247) : Fin 1 → Fin 247 := fun _ => t

theorem f1_inj (t : Fin 247) : Function.Injective (f1 t) := fun x y _ => Subsingleton.elim x y

/-- The operations' tape maps: `2 ↦ two`, `3 ↦ K` (if `k3`), `4 ↦ N` (if `k4`), the others in
the operation area. -/
def gOp (two : ℕ) (k3 k4 : Bool) (j : ℕ) : ℕ :=
  if j = 2 then two else if k3 && j = 3 then 40 else if k4 && j = 4 then 41 else j

/-- The tape map of an operation of `m ≤ 40` tapes. -/
def fOp (m : ℕ) (hm : m ≤ 40) (two : ℕ) (h2 : two = 2 ∨ two = 43) (k3 k4 : Bool) :
    Fin m → Fin 247 :=
  ofW (gOp two k3 k4) (by intro j hj; unfold gOp; split_ifs <;> omega)

theorem fOp_inj (m : ℕ) (hm : m ≤ 40) (two : ℕ) (h2 : two = 2 ∨ two = 43) (k3 k4 : Bool) :
    Function.Injective (fOp m hm two h2 k3 k4) :=
  ofW_inj (by
    intro x y hx hy h
    unfold gOp at h
    cases k3 <;> cases k4 <;> simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true,
      decide_eq_true_eq, ↓reduceIte] at h <;> split_ifs at h <;> omega)

/-- `[area 0 … area 2, X0, X1, X2]` for the scratch of the operation `neg`. -/
abbrev eOp (m : ℕ) (hm : m ≤ 40) (two : ℕ) (h2 : two = 2 ∨ two = 43) (k3 k4 : Bool) :
    Fin m ↪ Fin 247 :=
  mkE (fOp m hm two h2 k3 k4) (fOp_inj m hm two h2 k3 k4)

/-- Operand in: `area i := takeD |NK| a`. -/
def loadA (i : ℕ) (hi : i < 40) (a : Fin 200) : XProg 247 :=
  .frame (mkE (fIn i hi a) (fIn_inj i hi a)) (.prog ValVM.inP)

/-- Template in: `area 2 := t`. -/
def loadT (t : Fin 200) : XProg 247 := .frame (mkE (fTm t) (fTm_inj t)) (.prog (Prog.cp 0 1))

/-- Result out. -/
def store (d : Fin 200) : XProg 247 := .frame (mkE (fOut d) (fOut_inj d)) (.prog ValVM.outP)

/-- A binary operation. -/
def opBin {m : ℕ} (P : Prog (m + 1)) (e : Fin (m + 1) ↪ Fin 247) (d a b : Fin 200) : XProg 247 :=
  .seq (loadA 1 (by decide) a) (.seq (loadA 2 (by decide) b) (.seq (.frame e (.prog P)) (store d)))

/-- A unary operation. -/
def opUn {m : ℕ} (P : Prog (m + 1)) (e : Fin (m + 1) ↪ Fin 247) (d a : Fin 200) : XProg 247 :=
  .seq (loadA 1 (by decide) a) (.seq (.frame e (.prog P)) (store d))

/-- An operation with a template. -/
def opTm {m : ℕ} (P : Prog (m + 1)) (e : Fin (m + 1) ↪ Fin 247) (d a t : Fin 200) : XProg 247 :=
  .seq (loadA 1 (by decide) a) (.seq (loadT t) (.seq (.frame e (.prog P)) (store d)))

/-- The empty instruction. -/
def nopX : XProg 247 := .frame (mkE (f1 tX0) (f1_inj _)) (.prog (nop 0))

/-- **The program of a code.** -/
def compile : Code → XProg 247
  | .add d a b => opBin addRMP (eOp 28 (by decide) 2 (Or.inl rfl) true true) d a b
  | .sub d a b => opBin subRMP (eOp 28 (by decide) 2 (Or.inl rfl) true true) d a b
  | .mul d a b => opBin mulRMP (eOp 37 (by decide) 2 (Or.inl rfl) true true) d a b
  | .canon d a => opUn canonRP (eOp 28 (by decide) 43 (Or.inr rfl) true true) d a
  | .neg d a => opUn notP (eOp 11 (by decide) 2 (Or.inl rfl) false false) d a
  | .digit d a t => opTm digitRWP (eOp 31 (by decide) 2 (Or.inl rfl) true true) d a t
  | .rotB d a t => opTm rotBP (eOp 30 (by decide) 2 (Or.inl rfl) true true) d a t
  | .aut d a t => opTm autMP (eOp 25 (by decide) 2 (Or.inl rfl) true true) d a t
  | .rhoJ d a t => opTm rhoJP (eOp 7 (by decide) 2 (Or.inl rfl) true false) d a t
  | .mv d s c => if h : d = s ∨ d = c ∨ s = c then nopX else
      .frame (mkE (fMv d s c) (fMv_inj h)) (.prog ValVM.mvPc)
  | .cp d s => if h : d = s then nopX else .frame (mkE (fCp d s) (fCp_inj h)) (.prog (Prog.cp 0 1))
  | .drop t c => if h : t = c then nopX else .frame (mkE (fDr t c) (fDr_inj h)) (.prog ValVM.dropPc)
  | .clr t => .frame (mkE (f1 (tWd t)) (f1_inj _)) (.prog (Prog.clr 0))
  | .tl t => .frame (mkE (f1 (tWd t)) (f1_inj _)) (.prog (Prog.tl 0))
  | .rep c body => .loop (tWd c) (compile body)
  | .seq p q => .seq (compile p) (compile q)
  | .ifb t p q => .ifBit (tWd t) (compile p) (compile q)
  | .nop => nopX

/-! ### The encoding -/

/-- The store of a state: the operation area `o`, the templates, blank scratch, the words. -/
def encO (N K : ℕ) (o : ℕ → List Bool) (w : St) : Store 247 := fun t =>
  if t.val < 40 then o t.val else if t.val = 40 then List.replicate K false
  else if t.val = 41 then List.replicate N false
  else if t.val = 42 then List.replicate (N * K) false
  else if t.val = 43 then List.replicate (N * K) true
  else if h : 47 ≤ t.val then w ⟨t.val - 47, by have := t.isLt; omega⟩ else []

/-- **The store of the words `w`**, the operation area blank. -/
abbrev enc (N K : ℕ) (w : St) : Store 247 := encO N K (fun _ => []) w

section Enc

variable {N K : ℕ} {o : ℕ → List Bool} {w : St}

theorem encO_lt (t : Fin 247) (h : t.val < 40) : encO N K o w t = o t.val := by
  simp [encO, h]

@[simp] theorem encO_tO (j : ℕ) (h : j < 40) : encO N K o w (tO j h) = o j := encO_lt _ h
@[simp] theorem encO_tK : encO N K o w tK = List.replicate K false := by simp [encO, tK]
@[simp] theorem encO_tN : encO N K o w tN = List.replicate N false := by simp [encO, tN]
@[simp] theorem encO_tNK : encO N K o w tNK = List.replicate (N * K) false := by simp [encO, tNK]
@[simp] theorem encO_tOn : encO N K o w tOn = List.replicate (N * K) true := by simp [encO, tOn]
@[simp] theorem encO_tX0 : encO N K o w tX0 = [] := by simp [encO, tX0]
@[simp] theorem encO_tX1 : encO N K o w tX1 = [] := by simp [encO, tX1]
@[simp] theorem encO_tX2 : encO N K o w tX2 = [] := by simp [encO, tX2]

@[simp] theorem encO_tWd (x : Fin 200) : encO N K o w (tWd x) = w x := by
  have h1 : ¬ (47 + x.val < 40) := by omega
  have h2 : 47 + x.val ≠ 40 := by omega
  have h3 : 47 + x.val ≠ 41 := by omega
  have h4 : 47 + x.val ≠ 42 := by omega
  have h5 : 47 + x.val ≠ 43 := by omega
  simp only [encO, tWd, h1, h2, h3, h4, h5, ↓reduceIte, Nat.le_add_right, ↓reduceDIte,
    Nat.add_sub_cancel_left]

theorem tape_cases (t : Fin 247) : t.val < 40 ∨ t = tK ∨ t = tN ∨ t = tNK ∨ t = tOn ∨ t = tX0 ∨
    t = tX1 ∨ t = tX2 ∨ (∃ x, t = tWd x) := by
  have := t.isLt
  by_cases h : t.val < 40
  · exact Or.inl h
  by_cases h40 : t.val = 40; · exact Or.inr (Or.inl (Fin.ext h40))
  by_cases h41 : t.val = 41; · exact Or.inr (Or.inr (Or.inl (Fin.ext h41)))
  by_cases h42 : t.val = 42; · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h42))))
  by_cases h43 : t.val = 43; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h43)))))
  by_cases h44 : t.val = 44
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h44))))))
  by_cases h45 : t.val = 45
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h45)))))))
  by_cases h46 : t.val = 46
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h46))))))))
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨⟨t.val - 47, by omega⟩, Fin.ext (by simp [tWd]; omega)⟩)))))))

theorem encO_ext {s s' : Store 247} (h0 : ∀ t : Fin 247, t.val < 40 → s t = s' t)
    (h1 : s tK = s' tK) (h2 : s tN = s' tN) (h3 : s tNK = s' tNK) (h4 : s tOn = s' tOn)
    (h5 : s tX0 = s' tX0) (h6 : s tX1 = s' tX1) (h7 : s tX2 = s' tX2)
    (h8 : ∀ x, s (tWd x) = s' (tWd x)) : s = s' := by
  funext t
  rcases tape_cases t with h | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨x, rfl⟩
  exacts [h0 t h, h1, h2, h3, h4, h5, h6, h7, h8 x]

theorem encO_congr {o o' : ℕ → List Bool} (h : ∀ j < 40, o j = o' j) :
    encO N K o w = encO N K o' w := by
  refine encO_ext (fun t ht => ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun x => ?_)
  · rw [encO_lt _ ht, encO_lt _ ht, h _ ht]
  all_goals simp

theorem ne_tWd_of_lt {t : Fin 247} (h : t.val < 47) (x : Fin 200) : t ≠ tWd x := by
  intro e; subst e; simp [tWd] at h

theorem tWd_inj {x y : Fin 200} (h : tWd x = tWd y) : x = y :=
  Fin.ext (by have := congrArg Fin.val h; simp [tWd] at this; omega)

theorem update_tWd (x : Fin 200) (v : List Bool) :
    Function.update (encO N K o w) (tWd x) v = encO N K o (Function.update w x v) := by
  refine encO_ext (fun t ht => ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun y => ?_)
  · rw [Function.update_of_ne (ne_tWd_of_lt (by omega) x), encO_lt _ ht, encO_lt _ ht]
  all_goals try (rw [Function.update_of_ne (ne_tWd_of_lt (by decide) x)]; simp)
  by_cases h : y = x
  · subst h; simp
  · rw [Function.update_of_ne (fun e => h (tWd_inj e))]; simp [Function.update_of_ne h]

theorem update_lt (t : Fin 247) (ht : t.val < 40) (v : List Bool) :
    Function.update (encO N K o w) t v = encO N K (Function.update o t.val v) w := by
  refine encO_ext (fun t' ht' => ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun y => ?_)
  · rw [encO_lt _ ht']
    by_cases h : t' = t
    · subst h; simp
    · rw [Function.update_of_ne h, encO_lt _ ht', Function.update_of_ne (fun e => h (Fin.ext e))]
  all_goals try (rw [Function.update_of_ne (fun e => by subst e; simp_all [tK, tN, tNK, tOn, tX0, tX1, tX2])]; simp)
  rw [Function.update_of_ne (fun e => (ne_tWd_of_lt (by omega) y) e.symm)]; simp

theorem tailAt_tWd (x : Fin 200) : tailAt (tWd x) (encO N K o w) = encO N K o
    (Function.update w x (w x).tail) := by
  rw [tailAt, encO_tWd, update_tWd]

end Enc

/-! ### The instructions -/

section Instr

variable {N K : ℕ} {o : ℕ → List Bool} {w : St}

theorem run_loadA (i : ℕ) (hi : i < 40) (a : Fin 200) :
    run (XProg.flat (loadA i hi a)) (encO N K o w) =
      encO N K (Function.update o i (takeD (N * K) (w a))) w := by
  show run (map (fIn i hi a) ValVM.inP) _ = _
  have e0 : fIn i hi a 0 = ⟨i, by omega⟩ := rfl
  have e1 : fIn i hi a 1 = tNK := rfl
  have e2 : fIn i hi a 2 = tWd a := rfl
  have e3 : fIn i hi a 3 = tX0 := rfl
  have e4 : fIn i hi a 4 = tX1 := rfl
  have e5 : fIn i hi a 5 = tX2 := rfl
  rw [run_map_eq_update (fIn_inj i hi a) ValVM.inP _ 0 _ (ValVM.run_inP _ (by simp [e3])
    (by simp [e4]) (by simp [e5]))]
  simp only [Function.comp_apply, e0, e1, e2, encO_tNK, encO_tWd, List.length_replicate]
  rw [update_lt _ (by simp; omega)]

theorem run_loadT (t : Fin 200) :
    run (XProg.flat (loadT t)) (encO N K o w) = encO N K (Function.update o 2 (w t)) w := by
  show run (map (fTm t) (Prog.cp 0 1)) _ = _
  have e0 : fTm t 0 = ⟨2, by omega⟩ := rfl
  have e1 : fTm t 1 = tWd t := rfl
  rw [run_map_eq_update (fTm_inj t) _ _ 0 _ (run_copy 0 1 _)]
  simp only [Function.comp_apply, e0, e1, encO_tWd]
  rw [update_lt _ (by simp)]

theorem run_store (d : Fin 200) (ho : ∀ j, 3 ≤ j → j < 40 → o j = []) :
    run (XProg.flat (store d)) (encO N K o w) = enc N K (Function.update w d (o 0)) := by
  show run (map (fOut d) ValVM.outP) _ = _
  have e0 : fOut d 0 = ⟨0, by omega⟩ := rfl
  have e1 : fOut d 1 = ⟨1, by omega⟩ := rfl
  have e2 : fOut d 2 = ⟨2, by omega⟩ := rfl
  have e3 : fOut d 3 = tWd d := rfl
  rw [run_map (fOut_inj d), ValVM.run_outP, extend_update (fOut_inj d), extend_update (fOut_inj d),
    extend_update (fOut_inj d), extend_update (fOut_inj d), extend_comp_self]
  simp only [Function.comp_apply, e0, e1, e2, e3]
  rw [update_tWd, update_lt _ (by simp), update_lt _ (by simp), update_lt _ (by simp)]
  rw [show encO N K o w ⟨0, by omega⟩ = o 0 from encO_lt _ (by simp)]
  apply encO_congr
  intro j hj
  simp only [Function.update_apply]
  split_ifs <;> first | rfl | exact ho j (by omega) hj

theorem encO_eOp {m : ℕ} {hm : m ≤ 40} {two : ℕ} {h2 : two = 2 ∨ two = 43} {k3 k4 : Bool}
    (i : Fin m) : encO N K o w (eOp m hm two h2 k3 k4 i) =
      if i.val = 2 then (if two = 2 then o 2 else List.replicate (N * K) true)
      else if k3 ∧ i.val = 3 then List.replicate K false
      else if k4 ∧ i.val = 4 then List.replicate N false else o i.val := by
  have hi := i.isLt
  show encO N K o w ⟨gOp two k3 k4 i.val, _⟩ = _
  unfold gOp
  by_cases e2 : i.val = 2
  · rcases h2 with rfl | rfl <;> simp [e2, encO]
  · cases k3 <;> cases k4 <;> by_cases e3 : i.val = 3 <;> by_cases e4 : i.val = 4 <;>
      simp [e2, e3, e4, encO] <;> omega

theorem run_op {m : ℕ} (P : Prog (m + 1)) (e : Fin (m + 1) ↪ Fin 247) (he0 : e 0 = tO 0) (v : List Bool)
    (hP : run P (encO N K o w ∘ e) = Function.update (encO N K o w ∘ e) 0 v) :
    run (map e P) (encO N K o w) = encO N K (Function.update o 0 v) w := by
  rw [run_map_eq_update e.injective P _ 0 v hP, he0, update_lt _ (by show 0 < 40; omega)]
  rfl

/-- The operation area after loading `x` (and `y`). -/
def o2 (x y : List Bool) : ℕ → List Bool :=
  Function.update (Function.update (fun _ => []) 1 x) 2 y

theorem o2_ge (x y : List Bool) {j : ℕ} (h : 3 ≤ j) : o2 x y j = [] := by
  unfold o2; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

theorem run_opBin {m : ℕ} (P : Prog (m + 1)) (e : Fin (m + 1) ↪ Fin 247) (he0 : e 0 = tO 0)
    (f : List Bool → List Bool → List Bool) (d a b : Fin 200)
    (hP : ∀ x y : List Bool, x.length = N * K → y.length = N * K →
      run P (encO N K (o2 x y) w ∘ e) = Function.update (encO N K (o2 x y) w ∘ e) 0 (f x y)) :
    run (XProg.flat (opBin P e d a b)) (enc N K w) =
      enc N K (Function.update w d (f (opd N K (w a)) (opd N K (w b)))) := by
  show run (XProg.flat (loadA 1 _ a) ⨾ (XProg.flat (loadA 2 _ b) ⨾ (map e P ⨾
    XProg.flat (store d)))) _ = _
  simp only [run_seq]
  rw [run_loadA, run_loadA]
  have ho : Function.update (Function.update (fun _ : ℕ => ([] : List Bool)) 1
      (takeD (N * K) (w a))) 2 (takeD (N * K) (w b)) = o2 (opd N K (w a)) (opd N K (w b)) := rfl
  rw [ho, run_op P e he0 _ (hP _ _ (length_takeD _ _) (length_takeD _ _)), run_store]
  · simp [o2]
  · intro j hj _; rw [Function.update_of_ne (by omega)]; exact o2_ge _ _ hj

theorem run_opUn {m : ℕ} (P : Prog (m + 1)) (e : Fin (m + 1) ↪ Fin 247) (he0 : e 0 = tO 0)
    (f : List Bool → List Bool) (d a : Fin 200)
    (hP : ∀ x : List Bool, x.length = N * K →
      run P (encO N K (o2 x []) w ∘ e) = Function.update (encO N K (o2 x []) w ∘ e) 0 (f x)) :
    run (XProg.flat (opUn P e d a)) (enc N K w) =
      enc N K (Function.update w d (f (opd N K (w a)))) := by
  show run (XProg.flat (loadA 1 _ a) ⨾ (map e P ⨾ XProg.flat (store d))) _ = _
  simp only [run_seq]
  rw [run_loadA]
  have ho : Function.update (fun _ : ℕ => ([] : List Bool)) 1 (takeD (N * K) (w a)) =
      o2 (opd N K (w a)) [] := by
    funext j; simp [o2, Function.update_apply]; intro h; subst h; simp
  rw [ho, run_op P e he0 _ (hP _ (length_takeD _ _)), run_store]
  · simp [o2]
  · intro j hj _; rw [Function.update_of_ne (by omega)]; exact o2_ge _ _ hj

theorem run_opTm {m : ℕ} (P : Prog (m + 1)) (e : Fin (m + 1) ↪ Fin 247) (he0 : e 0 = tO 0)
    (f : ℕ → List Bool → List Bool) (d a t : Fin 200)
    (hP : ∀ x y : List Bool, x.length = N * K →
      run P (encO N K (o2 x y) w ∘ e) = Function.update (encO N K (o2 x y) w ∘ e) 0 (f y.length x)) :
    run (XProg.flat (opTm P e d a t)) (enc N K w) =
      enc N K (Function.update w d (f (w t).length (opd N K (w a)))) := by
  show run (XProg.flat (loadA 1 _ a) ⨾ (XProg.flat (loadT t) ⨾ (map e P ⨾
    XProg.flat (store d)))) _ = _
  simp only [run_seq]
  rw [run_loadA, run_loadT]
  have ho : Function.update (Function.update (fun _ : ℕ => ([] : List Bool)) 1
      (takeD (N * K) (w a))) 2 (w t) = o2 (opd N K (w a)) (w t) := rfl
  rw [ho, run_op P e he0 _ (hP _ _ (length_takeD _ _)), run_store]
  · simp [o2]
  · intro j hj _; rw [Function.update_of_ne (by omega)]; exact o2_ge _ _ hj

variable {m : ℕ} {hm : m ≤ 40} {two : ℕ} {h2 : two = 2 ∨ two = 43} {k3 k4 : Bool}

theorem eOp_ge5 (x y : List Bool) (i : Fin m) (hi : 5 ≤ i.val) :
    (encO N K (o2 x y) w ∘ eOp m hm two h2 k3 k4) i = [] := by
  rw [Function.comp_apply, encO_eOp, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  exact o2_ge x y (by omega)

theorem eOp_1 (x y : List Bool) (i : Fin m) (hi : i.val = 1) :
    (encO N K (o2 x y) w ∘ eOp m hm two h2 k3 k4) i = x := by
  rw [Function.comp_apply, encO_eOp, if_neg (by omega), if_neg (by omega), if_neg (by omega), hi]
  simp [o2]

theorem eOp_2 (x y : List Bool) (i : Fin m) (hi : i.val = 2) :
    (encO N K (o2 x y) w ∘ eOp m hm 2 (Or.inl rfl) k3 k4) i = y := by
  rw [Function.comp_apply, encO_eOp, if_pos hi, if_pos rfl]
  simp [o2]

theorem eOp_2' (x y : List Bool) (i : Fin m) (hi : i.val = 2) :
    (encO N K (o2 x y) w ∘ eOp m hm 43 (Or.inr rfl) k3 k4) i = List.replicate (N * K) true := by
  rw [Function.comp_apply, encO_eOp, if_pos hi, if_neg (by omega)]

theorem eOp_3 (x y : List Bool) (i : Fin m) (hi : i.val = 3) :
    (encO N K (o2 x y) w ∘ eOp m hm two h2 true k4) i = List.replicate K false := by
  rw [Function.comp_apply, encO_eOp, if_neg (by omega), if_pos ⟨rfl, hi⟩]

theorem eOp_4 (x y : List Bool) (i : Fin m) (hi : i.val = 4) :
    (encO N K (o2 x y) w ∘ eOp m hm two h2 k3 true) i = List.replicate N false := by
  rw [Function.comp_apply, encO_eOp, if_neg (by omega), if_neg (by omega), if_pos ⟨rfl, hi⟩]

end Instr

/-! ### Correctness of the compiler -/

section Correct

variable {N K : ℕ}

theorem run_nopX (w : St) : run (XProg.flat nopX) (enc N K w) = enc N K w := by
  show run (map (f1 tX0) (nop 0)) _ = _
  rw [run_map (f1_inj _)]
  simp only [run_nop]
  exact extend_comp_self _

theorem run_mvF {d s c : Fin 200} (h : ¬(d = s ∨ d = c ∨ s = c)) (w : St) :
    run (map (fMv d s c) ValVM.mvPc) (enc N K w) =
      enc N K (Function.update (Function.update w s ((w s).drop (w c).length)) d
        (ValVM.shiftIn (w c).length (w d) (w s))) := by
  have e0 : fMv d s c 0 = tWd s := rfl
  have e1 : fMv d s c 1 = tWd d := rfl
  have e2 : fMv d s c 2 = tX1 := rfl
  have e3 : fMv d s c 3 = tX2 := rfl
  have e4 : fMv d s c 4 = tWd c := rfl
  rw [ValVM.run_mvPc_map (fMv_inj h) _ (by rw [e2]; simp) (by rw [e3]; simp)]
  simp only [e0, e1, e4, encO_tWd, update_tWd]
  rfl

theorem flat_compile_mv {d s c : Fin 200} (h : ¬(d = s ∨ d = c ∨ s = c)) :
    XProg.flat (compile (.mv d s c)) = map (fMv d s c) ValVM.mvPc := by
  simp only [compile, dif_neg h]; rfl

/-- **Correctness of the compiler.** -/
theorem run_flat_compile (hN : 0 < N) (hK : 0 < K) :
    ∀ (c : Code) (w : St), run (XProg.flat (compile c)) (enc N K w) = enc N K (exec N K c w)
  | .add d a b, w => run_opBin _ _ rfl _ d a b fun x y hx hy => by
      rw [run_addRMP (K := K) (N := N) _ (fun i hi => eOp_ge5 x y i hi) (by rw [eOp_3 x y 3 rfl]; simp) (by rw [eOp_4 x y 4 rfl]; simp)
        (by rw [eOp_1 x y 1 rfl]; exact hx) (by rw [eOp_2 x y 2 rfl]; exact hy),
        eOp_1 x y 1 rfl, eOp_2 x y 2 rfl]
  | .sub d a b, w => run_opBin _ _ rfl _ d a b fun x y hx hy => by
      rw [run_subRMP (K := K) (N := N) _ (fun i hi => eOp_ge5 x y i hi) (by rw [eOp_3 x y 3 rfl]; simp) (by rw [eOp_4 x y 4 rfl]; simp)
        (by rw [eOp_1 x y 1 rfl]; exact hx) (by rw [eOp_2 x y 2 rfl]; exact hy),
        eOp_1 x y 1 rfl, eOp_2 x y 2 rfl]
  | .mul d a b, w => run_opBin _ _ rfl _ d a b fun x y hx _ => by
      rw [run_mulRMP (K := K) (N := N) _ (fun i hi => eOp_ge5 x y i hi) (by rw [eOp_3 x y 3 rfl]; simp) (by rw [eOp_4 x y 4 rfl]; simp)
        (by rw [eOp_1 x y 1 rfl]; exact hx), eOp_1 x y 1 rfl, eOp_2 x y 2 rfl]
  | .canon d a, w => run_opUn _ _ rfl _ d a fun x hx => by
      rw [run_canonRP (K := K) (N := N) hK _ (fun i hi => eOp_ge5 x [] i hi) (by rw [eOp_3 x [] 3 rfl]; simp) (by rw [eOp_4 x [] 4 rfl]; simp)
        (by rw [eOp_1 x [] 1 rfl]; exact hx) (by rw [eOp_2' x [] 2 rfl]; simp),
        eOp_1 x [] 1 rfl]
  | .neg d a, w => run_opUn _ _ rfl _ d a fun x _ => by
      rw [run_notP _ (fun i hi => by
          rcases (show i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ 5 ≤ i.val by omega) with h | h | h | h
          · rw [Function.comp_apply, encO_eOp, if_pos h, if_pos rfl]; simp [o2]
          · rw [Function.comp_apply, encO_eOp, if_neg (by omega)]; simp [h]; exact o2_ge _ _ (by omega)
          · rw [Function.comp_apply, encO_eOp, if_neg (by omega)]; simp [h]; exact o2_ge _ _ (by omega)
          · exact eOp_ge5 x [] i h),
        eOp_1 x [] 1 rfl]
  | .digit d a t, w => run_opTm _ _ rfl _ d a t fun x y hx => by
      rw [run_digitRWP (K := K) (N := N) _ (fun i hi => eOp_ge5 x y i hi) (i := y.length) (by rw [eOp_2 x y 2 rfl])
        (by rw [eOp_3 x y 3 rfl]; simp) (by rw [eOp_4 x y 4 rfl]; simp) (by rw [eOp_1 x y 1 rfl]; exact hx), eOp_1 x y 1 rfl]
  | .rotB d a t, w => run_opTm _ _ rfl _ d a t fun x y hx => by
      rw [run_rotBP (K := K) (N := N) _ (fun i hi => eOp_ge5 x y i hi) (by rw [eOp_3 x y 3 rfl]; simp) (by rw [eOp_4 x y 4 rfl]; simp)
        (by rw [eOp_1 x y 1 rfl]; exact hx), eOp_1 x y 1 rfl, eOp_2 x y 2 rfl]
  | .aut d a t, w => run_opTm _ _ rfl _ d a t fun x y hx => by
      rw [run_autMP (K := K) (N := N) _ (fun i hi => eOp_ge5 x y i hi) (by rw [eOp_3 x y 3 rfl]; simp) (by rw [eOp_4 x y 4 rfl]; simp)
        (by rw [eOp_1 x y 1 rfl]; exact hx) hN, eOp_1 x y 1 rfl, eOp_2 x y 2 rfl]
  | .rhoJ d a t, w => run_opTm _ _ rfl _ d a t fun x y _ => by
      rw [run_rhoJP _ (fun i hi => by
          rcases (show i.val = 4 ∨ 5 ≤ i.val by omega) with h | h
          · rw [Function.comp_apply, encO_eOp, if_neg (by omega), if_neg (by omega)]
            simp [h, o2]
          · exact eOp_ge5 x y i h),
        eOp_1 x y 1 rfl, eOp_2 x y 2 rfl, eOp_3 x y 3 rfl, List.length_replicate]
  | .mv d s c, w => by
    by_cases h : d = s ∨ d = c ∨ s = c
    · rw [show compile (.mv d s c) = nopX from dif_pos h, run_nopX]
      simp [exec, h]
    · rw [flat_compile_mv h, run_mvF h]
      simp [exec, h]
  | .cp d s, w => by
    by_cases h : d = s
    · rw [show compile (.cp d s) = nopX from dif_pos h, run_nopX]
      subst h; simp [exec]
    · rw [show compile (.cp d s) = .frame (mkE (fCp d s) (fCp_inj h)) (.prog (Prog.cp 0 1))
        from dif_neg h]
      show run (map (fCp d s) (Prog.cp 0 1)) _ = _
      rw [run_map_eq_update (fCp_inj h) _ _ 0 _ (run_copy 0 1 _)]
      have e0 : fCp d s 0 = tWd d := rfl
      have e1 : fCp d s 1 = tWd s := rfl
      simp [e0, e1, update_tWd, exec]
  | .drop t c, w => by
    by_cases h : t = c
    · rw [show compile (.drop t c) = nopX from dif_pos h, run_nopX]
      simp [exec, h]
    · rw [show compile (.drop t c) = .frame (mkE (fDr t c) (fDr_inj h)) (.prog ValVM.dropPc)
        from dif_neg h]
      show run (map (fDr t c) ValVM.dropPc) _ = _
      have e0 : fDr t c 0 = tWd t := rfl
      have e1 : fDr t c 1 = tX1 := rfl
      have e2 : fDr t c 2 = tWd c := rfl
      rw [ValVM.run_dropPc_map (fDr_inj h) _ (by rw [e1]; simp)]
      simp [e0, e2, update_tWd, exec, h]
  | .clr t, w => by
    show run (map (f1 (tWd t)) (Prog.clr 0)) _ = _
    rw [run_map_eq_update (f1_inj _) _ _ 0 _ (run_clear 0 _)]
    simp [f1, update_tWd, exec]
  | .tl t, w => by
    show run (map (f1 (tWd t)) (Prog.tl 0)) _ = _
    rw [run_map_eq_update (f1_inj _) _ _ 0 _ (run_tail 0 _)]
    simp [f1, update_tWd, exec]
  | .rep c body, w => by
    show run (Prog.loop (tWd c) (XProg.flat (compile body))) _ = _
    rw [run_loop, show enc N K w (tWd c) = w c from encO_tWd c, exec]
    have ih := run_flat_compile hN hK body
    have key : ∀ (m : ℕ) (w' : St),
        (fun t => run (XProg.flat (compile body)) (tailAt (tWd c) t))^[m] (enc N K w') =
          enc N K ((fun w'' => exec N K body (Function.update w'' c (w'' c).tail))^[m] w') := by
      intro m
      induction m with
      | zero => intro w'; rfl
      | succ m ihm =>
        intro w'
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, tailAt_tWd, ih, ihm]
    exact key _ w
  | .seq p q, w => by
    show run (XProg.flat (compile p) ⨾ XProg.flat (compile q)) _ = _
    rw [run_seq, run_flat_compile hN hK p, run_flat_compile hN hK q]
    rfl
  | .ifb t p q, w => by
    show run (Prog.ifBit (tWd t) (XProg.flat (compile p)) (XProg.flat (compile q))) _ = _
    rw [run_ifBit, show enc N K w (tWd t) = w t from encO_tWd t, exec]
    split_ifs
    · exact run_flat_compile hN hK p w
    · exact run_flat_compile hN hK q w
  | .nop, w => run_nopX w

theorem noGrow_opBin {m : ℕ} (P : Prog (m + 1)) (hP : P.NoGrow) (e : Fin (m + 1) ↪ Fin 247) (d a b : Fin 200) :
    (XProg.flat (opBin P e d a b)).NoGrow := by
  show (map _ ValVM.inP ⨾ (map _ ValVM.inP ⨾ (map e P ⨾ map _ ValVM.outP))).noGrowB = true
  simp only [noGrowB, noGrowB_map, Bool.and_eq_true]
  exact ⟨rfl, rfl, hP, rfl⟩

theorem noGrow_opUn {m : ℕ} (P : Prog (m + 1)) (hP : P.NoGrow) (e : Fin (m + 1) ↪ Fin 247) (d a : Fin 200) :
    (XProg.flat (opUn P e d a)).NoGrow := by
  show (map _ ValVM.inP ⨾ (map e P ⨾ map _ ValVM.outP)).noGrowB = true
  simp only [noGrowB, noGrowB_map, Bool.and_eq_true]
  exact ⟨rfl, hP, rfl⟩

theorem noGrow_opTm {m : ℕ} (P : Prog (m + 1)) (hP : P.NoGrow) (e : Fin (m + 1) ↪ Fin 247) (d a t : Fin 200) :
    (XProg.flat (opTm P e d a t)).NoGrow := by
  show (map _ ValVM.inP ⨾ (map _ (Prog.cp 0 1) ⨾ (map e P ⨾ map _ ValVM.outP))).noGrowB = true
  simp only [noGrowB, noGrowB_map, Bool.and_eq_true]
  exact ⟨rfl, rfl, hP, rfl⟩

theorem noGrow_nopX : (XProg.flat nopX).NoGrow := by
  show (map _ (nop 0)).noGrowB = true; rw [noGrowB_map]; rfl

theorem noGrow_flat_compile : ∀ c : Code, (XProg.flat (compile c)).NoGrow
  | .add d a b => noGrow_opBin _ noGrow_addRMP _ d a b
  | .sub d a b => noGrow_opBin _ noGrow_subRMP _ d a b
  | .mul d a b => noGrow_opBin _ noGrow_mulRMP _ d a b
  | .canon d a => noGrow_opUn _ noGrow_canonRP _ d a
  | .neg d a => noGrow_opUn _ noGrow_notP _ d a
  | .digit d a t => noGrow_opTm _ noGrow_digitRWP _ d a t
  | .rotB d a t => noGrow_opTm _ noGrow_rotBP _ d a t
  | .aut d a t => noGrow_opTm _ noGrow_autMP _ d a t
  | .rhoJ d a t => noGrow_opTm _ noGrow_rhoJP _ d a t
  | .mv d s c => by
    unfold compile; split_ifs
    · exact noGrow_nopX
    · show (map _ ValVM.mvPc).noGrowB = true; rw [noGrowB_map]; rfl
  | .cp d s => by
    unfold compile; split_ifs
    · exact noGrow_nopX
    · show (map _ (Prog.cp 0 1)).noGrowB = true; rw [noGrowB_map]; rfl
  | .drop t c => by
    unfold compile; split_ifs
    · exact noGrow_nopX
    · show (map _ ValVM.dropPc).noGrowB = true; rw [noGrowB_map]; rfl
  | .clr t => by show (map _ (Prog.clr 0)).noGrowB = true; rw [noGrowB_map]; rfl
  | .tl t => by show (map _ (Prog.tl 0)).noGrowB = true; rw [noGrowB_map]; rfl
  | .rep c body => noGrow_flat_compile body
  | .seq p q => by
    show (XProg.flat (compile p)).noGrowB && (XProg.flat (compile q)).noGrowB = true
    rw [noGrow_flat_compile p, noGrow_flat_compile q]; rfl
  | .ifb t p q => by
    show (XProg.flat (compile p)).noGrowB && (XProg.flat (compile q)).noGrowB = true
    rw [noGrow_flat_compile p, noGrow_flat_compile q]; rfl
  | .nop => noGrow_nopX

/-- **The law of a compiled code**: the point mass at the encoding of its semantics. -/
theorem law_compile (hN : 0 < N) (hK : 0 < K) (c : Code) (w : St) :
    (compile c).law (enc N K w) = PMF.pure (enc N K (exec N K c w)) := by
  rw [XProg.law_eq_run_flat _ (noGrow_flat_compile c), run_flat_compile hN hK c w]

end Correct

end RingVM

end SigabaNeo.Tape
