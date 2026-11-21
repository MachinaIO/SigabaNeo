import SigabaNeo.Lib.Lattices.Homomorphic.SLP

/-!
# Building Boolean straight-line programs

Gadgets append gates to a program and return the wires of their outputs. A gadget only appends
(`Ext p p'`: `p'` is `p` followed by more gates), so the wires of `p` keep their values in `p'`
(`bv_ext`). `bv x p w` is the Boolean value of a wire, `nv x p ws` the number whose little-endian
bits are the values of the wires `ws`.

* `addNand`: one gate, with `bv_addNand`;
* `notW`, `andW`, `orW`, `xorW`, `muxW`, with their values;
* `fullAdd` and `rippleAdd`: `nv` of the sum is the sum of the `nv`s (`rippleAdd_spec`).
-/

namespace SigabaNeo.Lattices

namespace SLP

variable {ι : Type*}

/-- `p'` extends `p`. -/
def Ext (p p' : SLP ι) : Prop := ∃ q, p' = p ++ q

theorem Ext.refl (p : SLP ι) : Ext p p := ⟨[], by simp⟩

theorem Ext.trans {p p' p'' : SLP ι} (h : Ext p p') (h' : Ext p' p'') : Ext p p'' := by
  obtain ⟨a, rfl⟩ := h; obtain ⟨b, rfl⟩ := h'; exact ⟨a ++ b, by simp⟩

/-- A wire that reads only gates of `p`. -/
def Valid (p : SLP ι) : Wire ι → Prop
  | .gate n => n < p.length
  | _ => True

theorem Ext.length_le {p p' : SLP ι} (h : Ext p p') : p.length ≤ p'.length := by
  obtain ⟨q, rfl⟩ := h; simp

theorem Valid.ext {p p' : SLP ι} (h : Ext p p') {w : Wire ι} (hw : Valid p w) : Valid p' w := by
  cases w with
  | gate n => exact Nat.lt_of_lt_of_le (show n < p.length from hw) h.length_le
  | _ => trivial

/-- The Boolean value of a wire. -/
def bv (x : ι → Bool) (p : SLP ι) (w : Wire ι) : Bool := evalBool x p w

/-- `run` keeps what was computed and appends one value per gate. -/
theorem run_eq_append (inp : ι → α) (one : α) (step : α → α → α) :
    ∀ (p : SLP ι) (acc : List α), ∃ l, run inp one step p acc = acc ++ l ∧ l.length = p.length
  | [], acc => ⟨[], by simp [run]⟩
  | g :: p, acc => by
    obtain ⟨l, hl, hlen⟩ := run_eq_append inp one step p (acc ++ [step (wireVal inp one acc g.a)
      (wireVal inp one acc g.b)])
    refine ⟨[step (wireVal inp one acc g.a) (wireVal inp one acc g.b)] ++ l, ?_, ?_⟩
    · simp only [run, hl, List.append_assoc]
    · simp [hlen]

theorem run_append (inp : ι → α) (one : α) (step : α → α → α) :
    ∀ (p q : SLP ι) (acc : List α), run inp one step (p ++ q) acc = run inp one step q (run inp one step p acc)
  | [], q, acc => rfl
  | g :: p, q, acc => by simp only [List.cons_append, run]; exact run_append inp one step p q _

theorem length_values (inp : ι → α) (one : α) (step : α → α → α) (p : SLP ι) :
    (values inp one step p).length = p.length := by
  obtain ⟨l, hl, hlen⟩ := run_eq_append inp one step p []
  simp [values, hl, hlen]

/-- **Wires keep their values** when gates are appended. -/
theorem valueOf_ext (inp : ι → α) (one : α) (step : α → α → α) {p p' : SLP ι} (h : Ext p p')
    {w : Wire ι} (hw : Valid p w) : valueOf inp one step p' w = valueOf inp one step p w := by
  obtain ⟨q, rfl⟩ := h
  cases w with
  | input i => rfl
  | one => rfl
  | gate n =>
    simp only [valueOf, values, wireVal]
    rw [run_append]
    obtain ⟨l, hl, -⟩ := run_eq_append inp one step q (run inp one step p [])
    rw [hl]
    have hlen : n < (run inp one step p []).length := by
      have := length_values inp one step p; simp only [values] at this; rw [this]; exact hw
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hlen,
      List.getElem_append_left hlen]

theorem bv_ext (x : ι → Bool) {p p' : SLP ι} (h : Ext p p') {w : Wire ι} (hw : Valid p w) :
    bv x p' w = bv x p w :=
  valueOf_ext _ _ _ h hw

/-- Append one NAND gate; its output wire. -/
def addNand (p : SLP ι) (a b : Wire ι) : SLP ι × Wire ι := (p ++ [⟨a, b⟩], .gate p.length)

theorem addNand_ext (p : SLP ι) (a b : Wire ι) : Ext p (addNand p a b).1 := ⟨_, rfl⟩

theorem addNand_valid (p : SLP ι) (a b : Wire ι) : Valid (addNand p a b).1 (addNand p a b).2 := by
  simp [addNand, Valid]

theorem bv_addNand (x : ι → Bool) (p : SLP ι) (a b : Wire ι) (_ha : Valid p a) (_hb : Valid p b) :
    bv x (addNand p a b).1 (addNand p a b).2 = !(bv x p a && bv x p b) := by
  simp only [bv, evalBool, valueOf, addNand, values, wireVal]
  rw [run_append]
  simp only [run]
  have hlen : (run x true (fun a b => !(a && b)) p []).length = p.length :=
    length_values x true (fun a b => !(a && b)) p
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append, hlen, List.length_singleton]; omega),
    List.getElem_append_right (by rw [hlen]; exact Nat.le_refl _)]
  simp only [hlen, Nat.sub_self, List.getElem_singleton]
  rfl

/-! ### Logic gates -/

/-- `¬a`. -/
def notW (p : SLP ι) (a : Wire ι) : SLP ι × Wire ι := addNand p a a

/-- `a ∧ b`. -/
def andW (p : SLP ι) (a b : Wire ι) : SLP ι × Wire ι :=
  let (p₁, n) := addNand p a b
  notW p₁ n

/-- `a ∨ b`. -/
def orW (p : SLP ι) (a b : Wire ι) : SLP ι × Wire ι :=
  let (p₁, na) := notW p a
  let (p₂, nb) := notW p₁ b
  addNand p₂ na nb

/-- `a ⊕ b`. -/
def xorW (p : SLP ι) (a b : Wire ι) : SLP ι × Wire ι :=
  let (p₁, n) := addNand p a b
  let (p₂, u) := addNand p₁ a n
  let (p₃, v) := addNand p₂ b n
  addNand p₃ u v

/-- `if s then a else b`. -/
def muxW (p : SLP ι) (s a b : Wire ι) : SLP ι × Wire ι :=
  let (p₁, ns) := notW p s
  let (p₂, u) := addNand p₁ s a
  let (p₃, v) := addNand p₂ ns b
  addNand p₃ u v

/-- A gadget's specification: it extends the program, its output is valid, and has value `val`. -/
structure Spec1 (x : ι → Bool) (p : SLP ι) (r : SLP ι × Wire ι) (val : Bool) : Prop where
  ext : Ext p r.1
  valid : Valid r.1 r.2
  value : bv x r.1 r.2 = val

theorem addNand_spec (x : ι → Bool) (p : SLP ι) (a b : Wire ι) (ha : Valid p a) (hb : Valid p b) :
    Spec1 x p (addNand p a b) (!(bv x p a && bv x p b)) :=
  ⟨addNand_ext p a b, addNand_valid p a b, bv_addNand x p a b ha hb⟩

/-- Chaining: a gate on the output of a gadget. -/
theorem Spec1.addNand {x : ι → Bool} {p : SLP ι} {r : SLP ι × Wire ι} {v : Bool}
    (h : Spec1 x p r v) (a : Wire ι) (ha : Valid p a) :
    Spec1 x p (SLP.addNand r.1 a r.2) (!(bv x p a && v)) := by
  have ha' := ha.ext h.ext
  refine ⟨h.ext.trans (addNand_ext _ _ _), addNand_valid _ _ _, ?_⟩
  rw [bv_addNand x _ _ _ ha' h.valid, bv_ext x h.ext ha, h.value]

theorem notW_spec (x : ι → Bool) (p : SLP ι) (a : Wire ι) (ha : Valid p a) :
    Spec1 x p (notW p a) (!bv x p a) := by
  have := addNand_spec x p a a ha ha
  simpa [notW] using this

theorem andW_spec (x : ι → Bool) (p : SLP ι) (a b : Wire ι) (ha : Valid p a) (hb : Valid p b) :
    Spec1 x p (andW p a b) (bv x p a && bv x p b) := by
  have h1 := addNand_spec x p a b ha hb
  have h2 := notW_spec x _ _ h1.valid
  refine ⟨h1.ext.trans h2.ext, h2.valid, ?_⟩
  simp only [andW] at h2 ⊢
  rw [h2.value, h1.value, Bool.not_not]

theorem orW_spec (x : ι → Bool) (p : SLP ι) (a b : Wire ι) (ha : Valid p a) (hb : Valid p b) :
    Spec1 x p (orW p a b) (bv x p a || bv x p b) := by
  have h1 := notW_spec x p a ha
  have h2 := notW_spec x _ b (hb.ext h1.ext)
  have h3 := addNand_spec x _ _ _ (h1.valid.ext h2.ext) h2.valid
  refine ⟨h1.ext.trans (h2.ext.trans h3.ext), h3.valid, ?_⟩
  simp only [orW] at h3 ⊢
  rw [h3.value, h2.value, bv_ext x h2.ext h1.valid, h1.value, bv_ext x h1.ext hb]
  cases bv x p a <;> cases bv x p b <;> rfl

theorem xorW_spec (x : ι → Bool) (p : SLP ι) (a b : Wire ι) (ha : Valid p a) (hb : Valid p b) :
    Spec1 x p (xorW p a b) (xor (bv x p a) (bv x p b)) := by
  have h1 := addNand_spec x p a b ha hb
  have h2 := addNand_spec x _ a _ (ha.ext h1.ext) h1.valid
  have h3 := addNand_spec x _ b _ (hb.ext (h1.ext.trans h2.ext)) (h1.valid.ext h2.ext)
  have h4 := addNand_spec x _ _ _ (h2.valid.ext h3.ext) h3.valid
  refine ⟨h1.ext.trans (h2.ext.trans (h3.ext.trans h4.ext)), h4.valid, ?_⟩
  simp only [xorW] at h4 ⊢
  rw [h4.value, h3.value, bv_ext x h3.ext h2.valid, h2.value, bv_ext x h2.ext h1.valid,
    bv_ext x (h1.ext.trans h2.ext) hb, bv_ext x h1.ext ha, h1.value]
  cases bv x p a <;> cases bv x p b <;> rfl

theorem muxW_spec (x : ι → Bool) (p : SLP ι) (s a b : Wire ι) (hs : Valid p s) (ha : Valid p a)
    (hb : Valid p b) :
    Spec1 x p (muxW p s a b) (if bv x p s then bv x p a else bv x p b) := by
  have h1 := notW_spec x p s hs
  have h2 := addNand_spec x _ s a (hs.ext h1.ext) (ha.ext h1.ext)
  have h3 := addNand_spec x _ _ b (h1.valid.ext h2.ext) (hb.ext (h1.ext.trans h2.ext))
  have h4 := addNand_spec x _ _ _ (h2.valid.ext h3.ext) h3.valid
  refine ⟨h1.ext.trans (h2.ext.trans (h3.ext.trans h4.ext)), h4.valid, ?_⟩
  simp only [muxW] at h4 ⊢
  rw [h4.value, h3.value, bv_ext x h3.ext h2.valid, h2.value, bv_ext x h2.ext h1.valid, h1.value,
    bv_ext x (h1.ext.trans h2.ext) hb, bv_ext x h1.ext hs, bv_ext x h1.ext ha]
  cases bv x p s <;> cases bv x p a <;> cases bv x p b <;> rfl

end SLP

end SigabaNeo.Lattices
