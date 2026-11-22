import SigabaNeo.Lib.Machines.Prog.Frame
import SigabaNeo.Lib.Machines.Prog.Macros

/-!
# Glue tapes and component programs

A layout for handler programs on `R + 8` tapes built from *components*: the tapes `0 … 7` are
*glue* tapes, the tapes `8 … R + 7` scratch tapes lent to components. A component is a framed
program `c : XProg (R + 2)` with its input and output words on its tapes `0`, `1` and its `R`
scratch tapes blank before and after. `comp p q c` runs `c` with its tapes `0`, `1` on the glue
tapes `p`, `q` and its scratch tapes on `8 … R + 7`; `glue P` runs a plain program `P : Prog 8`
on the glue tapes.

On stores whose scratch tapes are blank (`ext8 v []`), both act on the glue part only:

* `law_glue`: `glue P` acts as `P`;
* `law_comp`: if `c` maps `(a, b)` on its tapes `0`, `1` to `(r, [])` with `r ← μ`, then
  `comp p q c` maps `v` to `v` with `q := []` and `p := r`.

Per-tape bounds of the same shape (`ext8 u 0`) behave alike (`lenBoundT_glue`,
`timeBoundT_glue`, `lenBoundT_comp_le`, `timeBoundT_comp_le`).
-/

namespace SigabaNeo.Tape

open Cslib

variable {R : ℕ} {α : Type}

/-! ### Layouts -/

/-- The glue values `v` on the tapes `0 … 7`, the default `d` on the scratch tapes. -/
def ext8 (v : Fin 8 → α) (d : α) : Fin (R + 8) → α :=
  fun l => if h : l.val < 8 then v ⟨l.val, h⟩ else d

/-- The values `a`, `b` on the tapes `0`, `1` of a component, `d` on its scratch tapes. -/
def io2 (a b d : α) : Fin (R + 2) → α :=
  fun j => if j.val = 0 then a else if j.val = 1 then b else d

/-- The glue tapes. -/
def glueEmb : Fin 8 ↪ Fin (R + 8) :=
  ⟨fun j => ⟨j.val, by omega⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩

/-- The map of the tapes of a component. -/
def compFun (p q : Fin 8) (j : Fin (R + 2)) : Fin (R + 8) :=
  if j.val = 0 then ⟨p.val, by omega⟩ else if j.val = 1 then ⟨q.val, by omega⟩
    else ⟨j.val + 6, by omega⟩

theorem compFun_val (p q : Fin 8) (j : Fin (R + 2)) :
    (compFun p q j).val = if j.val = 0 then p.val else if j.val = 1 then q.val else j.val + 6 := by
  unfold compFun
  split_ifs <;> rfl

/-- The tapes of a component: `0 ↦ p`, `1 ↦ q`, `j + 2 ↦ j + 8`. -/
def compEmb (p q : Fin 8) (hpq : p ≠ q) : Fin (R + 2) ↪ Fin (R + 8) where
  toFun := compFun p q
  inj' a b h := by
    have hpq' : p.val ≠ q.val := fun h => hpq (Fin.ext h)
    have hp := p.isLt
    have hq := q.isLt
    have h' := congrArg Fin.val h
    rw [compFun_val, compFun_val] at h'
    apply Fin.ext
    split_ifs at h' <;> omega

@[simp] theorem glueEmb_val (j : Fin 8) : (glueEmb (R := R) j).val = j.val := rfl

theorem compEmb_val (p q : Fin 8) (hpq : p ≠ q) (j : Fin (R + 2)) :
    (compEmb p q hpq j).val = if j.val = 0 then p.val else if j.val = 1 then q.val else j.val + 6 :=
  compFun_val p q j

theorem not_mem_range_of_partialInv {k m : ℕ} {e : Fin m ↪ Fin k} {l : Fin k}
    (h : Turing.MultiTapeTM.partialInv e l = none) (j : Fin m) : e j ≠ l := by
  rintro rfl
  rw [partialInv_self] at h
  exact Option.some_ne_none _ h

theorem glue_restrict (v : Fin 8 → α) (d : α) :
    (fun j => ext8 (R := R) v d (glueEmb j)) = v := by
  funext j
  simp [ext8]

theorem embedF_glue (v w : Fin 8 → α) (d : α) :
    embedF glueEmb (ext8 (R := R) v d) w = ext8 w d := by
  funext l
  rcases embedF_cases glueEmb (ext8 v d) w l with ⟨hl, h⟩ | ⟨j, hj, h⟩
  · rw [h]
    have hl8 : ¬ l.val < 8 := fun h8 =>
      not_mem_range_of_partialInv hl ⟨l.val, h8⟩ (Fin.ext (by simp))
    simp [ext8, hl8]
  · subst hj
    rw [h]
    simp [ext8]

theorem comp_restrict (p q : Fin 8) (hpq : p ≠ q) (v : Fin 8 → α) (d : α) :
    (fun j => ext8 (R := R) v d (compEmb p q hpq j)) = io2 (v p) (v q) d := by
  funext j
  have hp := p.isLt
  have hq := q.isLt
  simp only [ext8, io2, compEmb_val]
  by_cases h0 : j.val = 0
  · simp [h0, hp]
  · by_cases h1 : j.val = 1
    · simp [h1, hq]
    · simp only [h0, h1]
      split_ifs <;> first | rfl | omega

theorem embedF_comp (p q : Fin 8) (hpq : p ≠ q) (v : Fin 8 → α) (a b d : α) :
    embedF (compEmb p q hpq) (ext8 (R := R) v d) (io2 a b d) =
      ext8 (Function.update (Function.update v q b) p a) d := by
  have hpq' : p.val ≠ q.val := fun h => hpq (Fin.ext h)
  funext l
  rcases embedF_cases (compEmb p q hpq) (ext8 v d) (io2 a b d) l with ⟨hl, h⟩ | ⟨j, hj, h⟩
  · rw [h]
    have hp : l.val ≠ p.val := fun h' =>
      not_mem_range_of_partialInv hl ⟨0, by omega⟩ (Fin.ext (by simp [compEmb_val, h']))
    have hq : l.val ≠ q.val := fun h' =>
      not_mem_range_of_partialInv hl ⟨1, by omega⟩ (Fin.ext (by simp [compEmb_val, h']))
    by_cases hl8 : l.val < 8
    · have hp' : (⟨l.val, hl8⟩ : Fin 8) ≠ p := fun h' => hp (by rw [← h'])
      have hq' : (⟨l.val, hl8⟩ : Fin 8) ≠ q := fun h' => hq (by rw [← h'])
      simp [ext8, hl8, hp', hq']
    · exfalso
      exact not_mem_range_of_partialInv hl ⟨l.val - 6, by omega⟩
        (Fin.ext (by simp only [compEmb_val]; split_ifs <;> omega))
  · subst hj
    rw [h]
    have hp := p.isLt
    have hq := q.isLt
    simp only [ext8, compEmb_val, io2]
    by_cases h0 : j.val = 0
    · simp [h0, hp]
    · by_cases h1 : j.val = 1
      · have : q ≠ p := fun h => hpq h.symm
        simp [h1, hq, this]
      · simp only [h0, h1]
        split_ifs <;> first | rfl | omega | contradiction

theorem ext8_mono {u u' : Fin 8 → ℕ} (h : u ≤ u') : ext8 (R := R) u 0 ≤ ext8 u' 0 := by
  intro l
  simp only [ext8]
  split_ifs
  · exact h _
  · exact le_rfl

theorem io2_mono {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    io2 (R := R) a b 0 ≤ io2 a' b' 0 := by
  intro j
  simp only [io2]
  split_ifs <;> omega

theorem fits_ext8 {v : Store 8} {u : Fin 8 → ℕ} (h : Fits v u) : Fits (ext8 (R := R) v []) (ext8 u 0) := by
  intro l
  simp only [ext8]
  split_ifs
  · exact h _
  · simp

/-! ### Glue and component programs -/

/-- A plain program on the glue tapes. -/
def glue (P : Prog 8) : XProg (R + 8) := .frame glueEmb (.prog P)

/-- A component on the glue tapes `p`, `q` and the scratch tapes. -/
def comp (p q : Fin 8) (hpq : p ≠ q) (c : XProg (R + 2)) : XProg (R + 8) :=
  .frame (compEmb p q hpq) c

theorem wf_glue {P : Prog 8} (h : P.WF) : (glue (R := R) P).WF := h

theorem wf_comp {p q : Fin 8} {hpq : p ≠ q} {c : XProg (R + 2)} (h : c.WF) :
    (comp p q hpq c).WF := h

namespace XProg

variable {k : ℕ}

theorem law_seq (p q : XProg k) (s : Store k) : law (seq p q) s = (law p s).bind (law q) := by
  simp [law, denote]; rfl

theorem law_seq_pure {p q : XProg k} {s t : Store k} (hp : law p s = PMF.pure t) :
    law (seq p q) s = law q t := by
  rw [law_seq, hp, PMF.pure_bind]

theorem law_ifBlank (i : Fin k) (p q : XProg k) (s : Store k) :
    law (ifBlank i p q) s = if s i = [] then law p s else law q s := by
  simp only [law, denote]; split_ifs <;> rfl

theorem law_ifBit (i : Fin k) (p q : XProg k) (s : Store k) :
    law (ifBit i p q) s = if (s i).head? = some true then law p s else law q s := by
  simp only [law, denote]; split_ifs <;> rfl

theorem law_frame {m : ℕ} (e : Fin m ↪ Fin k) (p : XProg m) (s : Store k) :
    law (frame e p) s = (law p (fun j => s (e j))).map (embedF e s) := by
  simp [law, denote]

theorem law_prog (p : Prog k) (s : Store k) : law (prog p) s = p.law s := rfl

end XProg

/-- **A glue program acts on the glue tapes.** -/
theorem law_glue (P : Prog 8) (v : Store 8) :
    XProg.law (glue (R := R) P) (ext8 v []) = (P.law v).map (fun w => ext8 w []) := by
  rw [glue, XProg.law_frame, glue_restrict, XProg.law_prog]
  congr 1
  funext w
  exact embedF_glue v w []

theorem law_glue_pure {P : Prog 8} {v w : Store 8} (h : P.law v = PMF.pure w) :
    XProg.law (glue (R := R) P) (ext8 v []) = PMF.pure (ext8 w []) := by
  rw [law_glue, h, PMF.pure_map]

/-- **A component acts on its two glue tapes.** -/
theorem law_comp (p q : Fin 8) (hpq : p ≠ q) (c : XProg (R + 2)) (v : Store 8) {β : Type}
    (μ : PMF β) (out : β → List Bool)
    (hc : XProg.law c (io2 (v p) (v q) []) = μ.map (fun r => io2 (out r) [] [])) :
    XProg.law (comp p q hpq c) (ext8 v []) =
      μ.map (fun r => ext8 (Function.update (Function.update v q []) p (out r)) []) := by
  rw [comp, XProg.law_frame, comp_restrict, hc, PMF.map_comp]
  congr 1
  funext r
  exact embedF_comp p q hpq v (out r) [] []

/-! ### Bounds -/

theorem timeBoundT_glue (P : Prog 8) (u : Fin 8 → ℕ) :
    XProg.timeBoundT (glue (R := R) P) (ext8 u 0) = P.timeBoundT u := by
  show P.timeBoundT (fun j => ext8 u 0 (glueEmb j)) = _
  rw [glue_restrict]

theorem lenBoundT_glue (P : Prog 8) (u : Fin 8 → ℕ) :
    XProg.lenBoundT (glue (R := R) P) (ext8 u 0) = ext8 (P.lenBoundT u) 0 := by
  show embedF glueEmb (ext8 u 0) (P.lenBoundT (fun j => ext8 u 0 (glueEmb j))) = _
  rw [glue_restrict, embedF_glue]

theorem timeBoundT_comp_le (p q : Fin 8) (hpq : p ≠ q) (c : XProg (R + 2)) (u : Fin 8 → ℕ)
    {A B : ℕ} (hA : u p ≤ A) (hB : u q ≤ B) :
    XProg.timeBoundT (comp p q hpq c) (ext8 u 0) ≤ XProg.timeBoundT c (io2 A B 0) := by
  show XProg.timeBoundT c (fun j => ext8 u 0 (compEmb p q hpq j)) ≤ _
  rw [comp_restrict]
  exact XProg.timeBoundT_mono c (io2_mono hA hB)

theorem lenBoundT_comp_le (p q : Fin 8) (hpq : p ≠ q) (c : XProg (R + 2)) (u : Fin 8 → ℕ)
    {A B C : ℕ} (hA : u p ≤ A) (hB : u q ≤ B) (hc : XProg.lenBoundT c (io2 A B 0) ≤ io2 C 0 0) :
    XProg.lenBoundT (comp p q hpq c) (ext8 u 0) ≤
      ext8 (Function.update (Function.update u q 0) p C) 0 := by
  show embedF (compEmb p q hpq) (ext8 u 0)
    (XProg.lenBoundT c (fun j => ext8 u 0 (compEmb p q hpq j))) ≤ _
  rw [comp_restrict, ← embedF_comp p q hpq u C 0 0]
  exact embedF_mono _ le_rfl ((XProg.lenBoundT_mono c (io2_mono hA hB)).trans hc)

end SigabaNeo.Tape
