import SigabaNeo.Lib.Lattices.Homomorphic.BoolArith

/-!
# Relocation of builders: the values of appended gates as local programs

A builder (`addNand`, `xorW`, `fullAdd`, `rippleAdd`, `modAdd`, …) appends gates to a program `p`
and returns wires. Under **any** evaluation semantics `valueOf inp one step` (Boolean, ring,
matrix simulations, words), the values of its output wires depend only on the values of the wires
it reads: they are a fixed function of those values, its *shadow* (`xorV`, `fullAddV`, `rippleV`,
`modAddV`, …), the local program evaluated on the values of the referenced wires.

`Sh1 p r v`/`ShN p r vs`: `r` extends `p`, its output wires are valid, and their values are `v`
(resp. the list `vs`). Each builder meets its shadow from valid input wires (`sh_addNand`,
`sh_xorW`, `sh_fullAdd`, `sh_rippleAdd`, `sh_modAdd`, `sh_modSub`, …). The wires of `p` keep
their values in the extension (`valueOf_ext`).

The shadows are what a machine computing the values of the output wires of a large program built
from these builders evaluates, gadget by gadget, without the program itself.
-/

namespace SigabaNeo.Lattices

namespace SLP

variable {ι α : Type*} (inp : ι → α) (one : α) (step : α → α → α)

/-! ### The specifications -/

/-- `r` extends `p`, its output wire is valid and has value `v`. -/
structure Sh1 (p : SLP ι) (r : SLP ι × Wire ι) (v : α) : Prop where
  ext : Ext p r.1
  valid : Valid r.1 r.2
  value : valueOf inp one step r.1 r.2 = v

/-- `r` extends `p`, its output wires are valid and have the values `vs`. -/
structure ShN (p : SLP ι) (r : SLP ι × List (Wire ι)) (vs : List α) : Prop where
  ext : Ext p r.1
  valid : AllValid r.1 r.2
  value : r.2.map (valueOf inp one step r.1) = vs

theorem valueOf_one (p : SLP ι) : valueOf inp one step p .one = one := rfl

theorem valueOf_input (p : SLP ι) (i : ι) : valueOf inp one step p (.input i) = inp i := rfl

theorem map_valueOf_ext {p p' : SLP ι} (h : Ext p p') {ws : List (Wire ι)} (hw : AllValid p ws) :
    ws.map (valueOf inp one step p') = ws.map (valueOf inp one step p) :=
  List.map_congr_left fun w hw' => valueOf_ext inp one step h (hw w hw')

theorem valueOf_getD (p : SLP ι) (ws : List (Wire ι)) (i : ℕ) :
    valueOf inp one step p (ws.getD i .one) = (ws.map (valueOf inp one step p)).getD i one := by
  by_cases h : i < ws.length
  · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map]
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem valid_getD {p : SLP ι} {ws : List (Wire ι)} (hw : AllValid p ws) (i : ℕ) :
    Valid p (ws.getD i .one) := by
  by_cases h : i < ws.length
  · rw [List.getD_eq_getElem _ _ h]; exact hw _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]; trivial

theorem AllValid.take {p : SLP ι} {ws : List (Wire ι)} (hw : AllValid p ws) (n : ℕ) :
    AllValid p (ws.take n) := fun w h => hw w (List.mem_of_mem_take h)

theorem allValid_nil (p : SLP ι) : AllValid p ([] : List (Wire ι)) := fun _ h => by simp at h

theorem AllValid.cons {p : SLP ι} {w : Wire ι} {ws : List (Wire ι)} (h : Valid p w)
    (hs : AllValid p ws) : AllValid p (w :: ws) := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact h
  · exact hs v hv

theorem AllValid.tail {p : SLP ι} {w : Wire ι} {ws : List (Wire ι)} (h : AllValid p (w :: ws)) :
    AllValid p ws := fun v hv => h v (List.mem_cons_of_mem _ hv)

theorem AllValid.head {p : SLP ι} {w : Wire ι} {ws : List (Wire ι)} (h : AllValid p (w :: ws)) :
    Valid p w := h w (List.mem_cons_self ..)

/-! ### One gate -/

/-- **The appended gate** has the value `step` of the values of its wires. -/
theorem valueOf_addNand (p : SLP ι) (a b : Wire ι) :
    valueOf inp one step (addNand p a b).1 (addNand p a b).2 =
      step (valueOf inp one step p a) (valueOf inp one step p b) := by
  simp only [valueOf, addNand, values, wireVal]
  rw [run_append]
  simp only [run]
  have hlen : (run inp one step p []).length = p.length := length_values inp one step p
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append, hlen, List.length_singleton]; omega),
    List.getElem_append_right (by rw [hlen])]
  simp only [hlen, Nat.sub_self, List.getElem_singleton]
  rfl

theorem sh_addNand (p : SLP ι) (a b : Wire ι) :
    Sh1 inp one step p (addNand p a b)
      (step (valueOf inp one step p a) (valueOf inp one step p b)) :=
  ⟨addNand_ext p a b, addNand_valid p a b, valueOf_addNand inp one step p a b⟩

/-- Chain a gadget: from `Sh1 p r v`, a gate on `r` and wires valid in `p`. -/
theorem Sh1.trans {p : SLP ι} {r r' : SLP ι × Wire ι} {v v' : α} (h : Sh1 inp one step p r v)
    (h' : Sh1 inp one step r.1 r' v') : Sh1 inp one step p r' v' :=
  ⟨h.ext.trans h'.ext, h'.valid, h'.value⟩

/-! ### Logic gates -/

/-- The shadow of `notW`. -/
def notV (a : α) : α := step one a

/-- The shadow of `andW`. -/
def andV (a b : α) : α := step one (step a b)

/-- The shadow of `orW`. -/
def orV (a b : α) : α := step (step one a) (step one b)

/-- The shadow of `xorW`. -/
def xorV (a b : α) : α := step (step a (step a b)) (step b (step a b))

/-- The shadow of `muxW`. -/
def muxV (s a b : α) : α := step (step s a) (step (step one s) b)

theorem sh_notW (p : SLP ι) (a : Wire ι) :
    Sh1 inp one step p (notW p a) (notV one step (valueOf inp one step p a)) :=
  sh_addNand inp one step p .one a

theorem sh_andW (p : SLP ι) (a b : Wire ι) :
    Sh1 inp one step p (andW p a b)
      (andV one step (valueOf inp one step p a) (valueOf inp one step p b)) := by
  have h1 := sh_addNand inp one step p a b
  have h2 := sh_notW inp one step (addNand p a b).1 (addNand p a b).2
  have hdef : andW p a b = notW (addNand p a b).1 (addNand p a b).2 := rfl
  rw [hdef]
  exact ⟨h1.ext.trans h2.ext, h2.valid, by rw [h2.value, h1.value]; rfl⟩

theorem sh_orW (p : SLP ι) (a b : Wire ι) (hb : Valid p b) :
    Sh1 inp one step p (orW p a b)
      (orV one step (valueOf inp one step p a) (valueOf inp one step p b)) := by
  set r₁ := notW p a
  set r₂ := notW r₁.1 b
  have h1 := sh_notW inp one step p a
  have h2 := sh_notW inp one step r₁.1 b
  have h3 := sh_addNand inp one step r₂.1 r₁.2 r₂.2
  refine ⟨h1.ext.trans (h2.ext.trans h3.ext), h3.valid, ?_⟩
  rw [show orW p a b = addNand r₂.1 r₁.2 r₂.2 from rfl, h3.value,
    valueOf_ext inp one step h2.ext h1.valid, h2.value, h1.value,
    valueOf_ext inp one step h1.ext hb]
  rfl

theorem sh_xorW (p : SLP ι) (a b : Wire ι) (ha : Valid p a) (hb : Valid p b) :
    Sh1 inp one step p (xorW p a b)
      (xorV step (valueOf inp one step p a) (valueOf inp one step p b)) := by
  set r₁ := addNand p a b
  set r₂ := addNand r₁.1 a r₁.2
  set r₃ := addNand r₂.1 b r₁.2
  have h1 := sh_addNand inp one step p a b
  have h2 := sh_addNand inp one step r₁.1 a r₁.2
  have h3 := sh_addNand inp one step r₂.1 b r₁.2
  have h4 := sh_addNand inp one step r₃.1 r₂.2 r₃.2
  have e12 := h1.ext.trans h2.ext
  refine ⟨e12.trans (h3.ext.trans h4.ext), h4.valid, ?_⟩
  rw [show xorW p a b = addNand r₃.1 r₂.2 r₃.2 from rfl, h4.value,
    valueOf_ext inp one step h3.ext h2.valid, h2.value, h3.value,
    valueOf_ext inp one step h2.ext h1.valid, h1.value,
    valueOf_ext inp one step h1.ext ha, valueOf_ext inp one step e12 hb]
  rfl

theorem sh_muxW (p : SLP ι) (s a b : Wire ι) (hs : Valid p s) (ha : Valid p a) (hb : Valid p b) :
    Sh1 inp one step p (muxW p s a b)
      (muxV one step (valueOf inp one step p s) (valueOf inp one step p a)
        (valueOf inp one step p b)) := by
  set r₁ := notW p s
  set r₂ := addNand r₁.1 s a
  set r₃ := addNand r₂.1 r₁.2 b
  have h1 := sh_notW inp one step p s
  have h2 := sh_addNand inp one step r₁.1 s a
  have h3 := sh_addNand inp one step r₂.1 r₁.2 b
  have h4 := sh_addNand inp one step r₃.1 r₂.2 r₃.2
  have e12 := h1.ext.trans h2.ext
  refine ⟨e12.trans (h3.ext.trans h4.ext), h4.valid, ?_⟩
  rw [show muxW p s a b = addNand r₃.1 r₂.2 r₃.2 from rfl, h4.value,
    valueOf_ext inp one step h3.ext h2.valid, h2.value, h3.value,
    valueOf_ext inp one step h2.ext h1.valid, h1.value,
    valueOf_ext inp one step h1.ext hs, valueOf_ext inp one step h1.ext ha,
    valueOf_ext inp one step e12 hb]
  rfl

/-! ### Adders -/

/-- The shadow of `fullAdd`: the sum and the carry. -/
def fullAddV (a b c : α) : α × α :=
  (xorV step (xorV step a b) c, step (step a b) (step (orV one step a b) c))

theorem sh_fullAdd (p : SLP ι) (a b c : Wire ι) (ha : Valid p a) (hb : Valid p b)
    (hc : Valid p c) :
    let r := fullAdd p a b c
    Ext p r.1 ∧ Valid r.1 r.2.1 ∧ Valid r.1 r.2.2 ∧
      (valueOf inp one step r.1 r.2.1, valueOf inp one step r.1 r.2.2) =
        fullAddV one step (valueOf inp one step p a) (valueOf inp one step p b)
          (valueOf inp one step p c) := by
  set r₁ := xorW p a b
  have h1 := sh_xorW inp one step p a b ha hb
  set r₂ := xorW r₁.1 r₁.2 c
  have h2 := sh_xorW inp one step r₁.1 r₁.2 c h1.valid (hc.ext h1.ext)
  have e12 := h1.ext.trans h2.ext
  set r₃ := addNand r₂.1 a b
  have h3 := sh_addNand inp one step r₂.1 a b
  have e13 := e12.trans h3.ext
  set r₄ := orW r₃.1 a b
  have h4 := sh_orW inp one step r₃.1 a b (hb.ext e13)
  have e14 := e13.trans h4.ext
  set r₅ := addNand r₄.1 r₄.2 c
  have h5 := sh_addNand inp one step r₄.1 r₄.2 c
  set r₆ := addNand r₅.1 r₃.2 r₅.2
  have h6 := sh_addNand inp one step r₅.1 r₃.2 r₅.2
  have e36 := h3.ext.trans (h4.ext.trans (h5.ext.trans h6.ext))
  have hfa : fullAdd p a b c = (r₆.1, r₂.2, r₆.2) := rfl
  rw [hfa]
  refine ⟨e14.trans (h5.ext.trans h6.ext), h2.valid.ext e36, h6.valid, ?_⟩
  simp only
  rw [valueOf_ext inp one step e36 h2.valid, h2.value, h6.value,
    valueOf_ext inp one step (h4.ext.trans h5.ext) h3.valid, h3.value, h5.value, h4.value, h1.value,
    valueOf_ext inp one step h1.ext hc, valueOf_ext inp one step e12 ha,
    valueOf_ext inp one step e12 hb, valueOf_ext inp one step e13 ha,
    valueOf_ext inp one step e13 hb, valueOf_ext inp one step e14 hc]
  rfl

/-- The shadow of `rippleAdd`. -/
def rippleV : List α → List α → α → List α
  | [], _, c => [c]
  | _ :: _, [], c => [c]
  | a :: as, b :: bs, c =>
    (fullAddV one step a b c).1 :: rippleV as bs (fullAddV one step a b c).2

theorem sh_rippleAdd : ∀ (p : SLP ι) (as bs : List (Wire ι)) (c : Wire ι),
    AllValid p as → AllValid p bs → Valid p c →
    ShN inp one step p (rippleAdd p as bs c)
      (rippleV one step (as.map (valueOf inp one step p)) (bs.map (valueOf inp one step p))
        (valueOf inp one step p c))
  | p, [], _, c, _, _, hc => ⟨Ext.refl p, (allValid_nil p).cons hc, rfl⟩
  | p, _ :: _, [], c, _, _, hc => ⟨Ext.refl p, (allValid_nil p).cons hc, rfl⟩
  | p, a :: as, b :: bs, c, ha, hb, hc => by
    obtain ⟨e1, hs, hk, hv⟩ := sh_fullAdd inp one step p a b c ha.head hb.head hc
    have ih := sh_rippleAdd (fullAdd p a b c).1 as bs (fullAdd p a b c).2.2
      (fun v hv => (ha.tail v hv).ext e1) (fun v hv => (hb.tail v hv).ext e1) hk
    refine ⟨e1.trans ih.ext, AllValid.cons (hs.ext ih.ext) ih.valid, ?_⟩
    have hdef : rippleAdd p (a :: as) (b :: bs) c =
        ((rippleAdd (fullAdd p a b c).1 as bs (fullAdd p a b c).2.2).1,
          (fullAdd p a b c).2.1 :: (rippleAdd (fullAdd p a b c).1 as bs (fullAdd p a b c).2.2).2) :=
      rfl
    rw [hdef, List.map_cons]
    rw [ih.value, valueOf_ext inp one step ih.ext hs, map_valueOf_ext inp one step e1 ha.tail,
      map_valueOf_ext inp one step e1 hb.tail]
    simp only [List.map_cons, rippleV]
    rw [← hv]

/-! ### Constants and bitwise operations -/

/-- The shadow of `constL`: `one` for the set bits, `zv` (the value of `z`) for the others. -/
def constV (zv : α) : ℕ → ℕ → List α
  | 0, _ => []
  | w + 1, m => (if m % 2 = 1 then one else zv) :: constV zv w (m / 2)

theorem map_constL (p : SLP ι) (z : Wire ι) :
    ∀ w m, (constL z w m).map (valueOf inp one step p) =
      constV one (valueOf inp one step p z) w m
  | 0, _ => rfl
  | w + 1, m => by
    simp only [constL, List.map_cons, constV, map_constL p z w (m / 2)]
    split_ifs <;> rfl

theorem allValid_constL {p : SLP ι} {z : Wire ι} (hz : Valid p z) :
    ∀ w m, AllValid p (constL z w m)
  | 0, _ => allValid_nil p
  | w + 1, m => by
    refine AllValid.cons ?_ (allValid_constL hz w (m / 2))
    split_ifs
    · trivial
    · exact hz

/-- The shadow of `muxL s`. -/
def muxLV (s : α) : List α → List α → List α
  | [], _ => []
  | _ :: _, [] => []
  | a :: as, b :: bs => muxV one step s a b :: muxLV s as bs

theorem sh_muxL (s : Wire ι) : ∀ (p : SLP ι) (as bs : List (Wire ι)), Valid p s →
    AllValid p as → AllValid p bs →
    ShN inp one step p (muxL s p as bs)
      (muxLV one step (valueOf inp one step p s) (as.map (valueOf inp one step p))
        (bs.map (valueOf inp one step p)))
  | p, [], _, _, _, _ => ⟨Ext.refl p, allValid_nil p, rfl⟩
  | p, _ :: _, [], _, _, _ => ⟨Ext.refl p, allValid_nil p, rfl⟩
  | p, a :: as, b :: bs, hs, ha, hb => by
    have h1 := sh_muxW inp one step p s a b hs ha.head hb.head
    have ih := sh_muxL s (muxW p s a b).1 as bs (hs.ext h1.ext)
      (fun v hv => (ha.tail v hv).ext h1.ext) (fun v hv => (hb.tail v hv).ext h1.ext)
    refine ⟨h1.ext.trans ih.ext, AllValid.cons (h1.valid.ext ih.ext) ih.valid, ?_⟩
    have hdef : muxL s p (a :: as) (b :: bs) =
        ((muxL s (muxW p s a b).1 as bs).1, (muxW p s a b).2 :: (muxL s (muxW p s a b).1 as bs).2) :=
      rfl
    rw [hdef, List.map_cons]
    rw [ih.value, valueOf_ext inp one step ih.ext h1.valid, h1.value,
      valueOf_ext inp one step h1.ext hs, map_valueOf_ext inp one step h1.ext ha.tail,
      map_valueOf_ext inp one step h1.ext hb.tail]
    rfl

/-- The shadow of `andL d`. -/
def andLV (d : α) : List α → List α
  | [] => []
  | a :: as => andV one step d a :: andLV d as

theorem sh_andL (d : Wire ι) : ∀ (p : SLP ι) (as : List (Wire ι)), Valid p d → AllValid p as →
    ShN inp one step p (andL d p as)
      (andLV one step (valueOf inp one step p d) (as.map (valueOf inp one step p)))
  | p, [], _, _ => ⟨Ext.refl p, allValid_nil p, rfl⟩
  | p, a :: as, hd, ha => by
    have h1 := sh_andW inp one step p d a
    have ih := sh_andL d (andW p d a).1 as (hd.ext h1.ext) (fun v hv => (ha.tail v hv).ext h1.ext)
    refine ⟨h1.ext.trans ih.ext, AllValid.cons (h1.valid.ext ih.ext) ih.valid, ?_⟩
    have hdef : andL d p (a :: as) =
        ((andL d (andW p d a).1 as).1, (andW p d a).2 :: (andL d (andW p d a).1 as).2) := rfl
    rw [hdef, List.map_cons]
    rw [ih.value, valueOf_ext inp one step ih.ext h1.valid, h1.value,
      valueOf_ext inp one step h1.ext hd, map_valueOf_ext inp one step h1.ext ha.tail]
    rfl

/-- The shadow of `notL`. -/
def notLV : List α → List α
  | [] => []
  | a :: as => notV one step a :: notLV as

theorem sh_notL : ∀ (p : SLP ι) (as : List (Wire ι)), AllValid p as →
    ShN inp one step p (notL p as) (notLV one step (as.map (valueOf inp one step p)))
  | p, [], _ => ⟨Ext.refl p, allValid_nil p, rfl⟩
  | p, a :: as, ha => by
    have h1 := sh_notW inp one step p a
    have ih := sh_notL (notW p a).1 as (fun v hv => (ha.tail v hv).ext h1.ext)
    refine ⟨h1.ext.trans ih.ext, AllValid.cons (h1.valid.ext ih.ext) ih.valid, ?_⟩
    have hdef : notL p (a :: as) =
        ((notL (notW p a).1 as).1, (notW p a).2 :: (notL (notW p a).1 as).2) := rfl
    rw [hdef, List.map_cons]
    rw [ih.value, valueOf_ext inp one step ih.ext h1.valid, h1.value,
      map_valueOf_ext inp one step h1.ext ha.tail]
    rfl

/-! ### Modular addition and subtraction -/

/-- The shadow of `modAdd z q w`; `zv` is the value of `z`. -/
def modAddV (zv : α) (q w : ℕ) (as bs : List α) : List α :=
  let s₁ := rippleV one step as bs zv
  let s₂ := rippleV one step s₁ (constV one zv (w + 1) (2 ^ (w + 1) - q)) zv
  (muxLV one step (s₂.getD (w + 1) one) (s₂.take (w + 1)) s₁).take w

/-- The shadow of `modSub z q w`; `zv` is the value of `z`. -/
def modSubV (zv : α) (q w : ℕ) (as bs : List α) : List α :=
  let s₁ := notLV one step bs
  let s₂ := rippleV one step as s₁ one
  let s₃ := rippleV one step (s₂.take w) (constV one zv w q) zv
  muxLV one step (s₂.getD w one) (s₂.take w) (s₃.take w)

theorem sh_modAdd (z : Wire ι) (q w : ℕ) (p : SLP ι) (as bs : List (Wire ι)) (hz : Valid p z)
    (ha : AllValid p as) (hb : AllValid p bs) :
    ShN inp one step p (modAdd z q w p as bs)
      (modAddV one step (valueOf inp one step p z) q w (as.map (valueOf inp one step p))
        (bs.map (valueOf inp one step p))) := by
  set V := valueOf inp one step
  set r₁ := rippleAdd p as bs z
  have h1 := sh_rippleAdd inp one step p as bs z ha hb hz
  set C := constL z (w + 1) (2 ^ (w + 1) - q)
  have hC := allValid_constL (hz.ext h1.ext) (w + 1) (2 ^ (w + 1) - q)
  set r₂ := rippleAdd r₁.1 r₁.2 C z
  have h2 := sh_rippleAdd inp one step r₁.1 r₁.2 C z h1.valid hC (hz.ext h1.ext)
  have hs := valid_getD h2.valid (w + 1)
  set r₃ := muxL (r₂.2.getD (w + 1) .one) r₂.1 (r₂.2.take (w + 1)) r₁.2
  have h3 := sh_muxL inp one step _ r₂.1 (r₂.2.take (w + 1)) r₁.2 hs (h2.valid.take _)
    (h1.valid.ext h2.ext)
  refine ⟨h1.ext.trans (h2.ext.trans h3.ext), h3.valid.take w, ?_⟩
  show (r₃.2.take w).map (V r₃.1) = _
  rw [List.map_take, h3.value, valueOf_getD, h2.value, List.map_take, h2.value,
    map_valueOf_ext inp one step h2.ext h1.valid, h1.value, map_constL,
    valueOf_ext inp one step h1.ext hz]
  rfl

theorem sh_modSub (z : Wire ι) (q w : ℕ) (p : SLP ι) (as bs : List (Wire ι)) (hz : Valid p z)
    (ha : AllValid p as) (hb : AllValid p bs) :
    ShN inp one step p (modSub z q w p as bs)
      (modSubV one step (valueOf inp one step p z) q w (as.map (valueOf inp one step p))
        (bs.map (valueOf inp one step p))) := by
  set V := valueOf inp one step
  set r₁ := notL p bs
  have h1 := sh_notL inp one step p bs hb
  set r₂ := rippleAdd r₁.1 as r₁.2 .one
  have h2 := sh_rippleAdd inp one step r₁.1 as r₁.2 .one (fun v hv => (ha v hv).ext h1.ext)
    h1.valid trivial
  have e12 := h1.ext.trans h2.ext
  set C := constL z w q
  have hC := allValid_constL (hz.ext e12) w q
  set r₃ := rippleAdd r₂.1 (r₂.2.take w) C z
  have h3 := sh_rippleAdd inp one step r₂.1 (r₂.2.take w) C z (h2.valid.take w) hC (hz.ext e12)
  have hs := valid_getD h2.valid w
  set r₄ := muxL (r₂.2.getD w .one) r₃.1 (r₂.2.take w) (r₃.2.take w)
  have h4 := sh_muxL inp one step _ r₃.1 (r₂.2.take w) (r₃.2.take w) (hs.ext h3.ext)
    ((h2.valid.take w).ext h3.ext) (h3.valid.take w)
  refine ⟨e12.trans (h3.ext.trans h4.ext), h4.valid, ?_⟩
  show r₄.2.map (V r₄.1) = _
  rw [h4.value, valueOf_ext inp one step h3.ext hs, valueOf_getD, h2.value,
    map_valueOf_ext inp one step h3.ext (h2.valid.take w), List.map_take, h2.value, List.map_take,
    h3.value, List.map_take, h2.value, map_constL, valueOf_ext inp one step e12 hz,
    map_valueOf_ext inp one step h1.ext ha, h1.value]
  rfl

end SLP

end SigabaNeo.Lattices
