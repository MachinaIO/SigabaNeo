import SigabaNeo.Lib.Machines.GatesSLP
import SigabaNeo.Lib.Lattices.Homomorphic.BoolCompare

/-!
# The wire indices of compiled gate lists

A straight-line program is **closed** (`SLP.Closed`) when every gate reads wires of the program.
The builders (`addNand`, `notW`, `andW`, `orW`, `geConst`, `leConst`) and the compiler of Boolean
expressions (`compile`) keep programs closed (`good_compile`). A closed program on `n` inputs has
gate lists with every wire index at most `n + |p|` (`bnd_toGates`, `bnd_predGates`).
-/

namespace SigabaNeo

open Lattices

namespace Lattices.SLP

variable {ι : Type*}

/-- Every gate of `p` reads wires of `p`. -/
def Closed (p : SLP ι) : Prop := ∀ g ∈ p, Valid p g.a ∧ Valid p g.b

/-- A builder's result `r` after `p`: closed, valid output, extending `p`. -/
def Good (p : SLP ι) (r : SLP ι × Wire ι) : Prop := Closed r.1 ∧ Valid r.1 r.2 ∧ Ext p r.1

theorem closed_nil : Closed ([] : SLP ι) := by simp [Closed]

theorem Good.refl {p : SLP ι} (hp : Closed p) (w : Wire ι) (hw : Valid p w) : Good p (p, w) :=
  ⟨hp, hw, Ext.refl p⟩

theorem Good.trans {p : SLP ι} {r s : SLP ι × Wire ι} (h : Good p r) (h' : Good r.1 s) : Good p s :=
  ⟨h'.1, h'.2.1, h.2.2.trans h'.2.2⟩

theorem good_addNand {p : SLP ι} (hp : Closed p) {a b : Wire ι} (ha : Valid p a) (hb : Valid p b) :
    Good p (addNand p a b) := by
  refine ⟨?_, addNand_valid p a b, addNand_ext p a b⟩
  have e := addNand_ext p a b
  intro g hg
  simp only [addNand, List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact ⟨(hp g hg).1.ext e, (hp g hg).2.ext e⟩
  · exact ⟨ha.ext e, hb.ext e⟩

theorem good_notW {p : SLP ι} (hp : Closed p) {a : Wire ι} (ha : Valid p a) : Good p (notW p a) :=
  good_addNand hp trivial ha

theorem good_andW {p : SLP ι} (hp : Closed p) {a b : Wire ι} (ha : Valid p a) (hb : Valid p b) :
    Good p (andW p a b) := by
  have h1 := good_addNand hp ha hb
  exact h1.trans (good_notW h1.1 h1.2.1)

theorem good_orW {p : SLP ι} (hp : Closed p) {a b : Wire ι} (ha : Valid p a) (hb : Valid p b) :
    Good p (orW p a b) := by
  have h1 := good_notW hp ha
  have h2 := good_notW h1.1 (hb.ext h1.2.2)
  exact h1.trans (h2.trans (good_addNand h2.1 (h1.2.1.ext h2.2.2) h2.2.1))

theorem good_geConst {p : SLP ι} (hp : Closed p) : ∀ (xs : List (Wire ι)) (as : List Bool),
    (∀ w ∈ xs, Valid p w) → Good p (geConst p xs as)
  | [], _, _ => by simp only [geConst]; exact Good.refl hp _ trivial
  | _ :: _, [], _ => by simp only [geConst]; exact Good.refl hp _ trivial
  | x :: xs, a :: as, hx => by
    have h := good_geConst hp xs as (fun w hw => hx w (by simp [hw]))
    have hx' : Valid (geConst p xs as).1 x := (hx x (by simp)).ext h.2.2
    simp only [geConst]
    cases a
    · exact h.trans (good_orW h.1 hx' h.2.1)
    · exact h.trans (good_andW h.1 hx' h.2.1)

theorem good_leConst {p : SLP ι} (hp : Closed p) : ∀ (xs : List (Wire ι)) (bs : List Bool),
    (∀ w ∈ xs, Valid p w) → Good p (leConst p xs bs)
  | [], _, _ => by simp only [leConst]; exact Good.refl hp _ trivial
  | _ :: _, [], _ => by simp only [leConst]; exact Good.refl hp _ trivial
  | x :: xs, b :: bs, hx => by
    have h := good_leConst hp xs bs (fun w hw => hx w (by simp [hw]))
    have hx' : Valid (leConst p xs bs).1 x := (hx x (by simp)).ext h.2.2
    have hn := good_notW h.1 hx'
    have hr : Valid (notW (leConst p xs bs).1 x).1 (leConst p xs bs).2 := h.2.1.ext hn.2.2
    simp only [leConst]
    cases b
    · exact h.trans (hn.trans (good_andW hn.1 hn.2.1 hr))
    · exact h.trans (hn.trans (good_orW hn.1 hn.2.1 hr))

/-- **Compiled expressions keep programs closed.** -/
theorem good_compile : ∀ (e : BExp ι) {p : SLP ι}, Closed p → Good p (compile p e)
  | .ge is as, p, hp => good_geConst hp _ as (fun w hw => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hw; trivial)
  | .le is bs, p, hp => good_leConst hp _ bs (fun w hw => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hw; trivial)
  | .not e, p, hp => by
    have h := good_compile e hp
    exact h.trans (good_notW h.1 h.2.1)
  | .and e f, p, hp => by
    have h := good_compile e hp
    have h' := good_compile f h.1
    exact h.trans (h'.trans (good_andW h'.1 (h.2.1.ext h'.2.2) h'.2.1))
  | .or e f, p, hp => by
    have h := good_compile e hp
    have h' := good_compile f h.1
    exact h.trans (h'.trans (good_orW h'.1 (h.2.1.ext h'.2.2) h'.2.1))

end Lattices.SLP

open Lattices.SLP

theorem wireIdx_le {n : ℕ} {p : SLP (Fin n)} {w : Wire (Fin n)} (hw : Valid p w) :
    wireIdx n w ≤ n + p.length := by
  cases w with
  | one => simp [wireIdx]
  | input i => simp only [wireIdx]; omega
  | gate m => simp only [wireIdx]; have : m < p.length := hw; omega

/-- **The wire indices of a closed program's gate list.** -/
theorem bnd_toGates {n : ℕ} {p : SLP (Fin n)} (hp : Closed p) :
    ∀ g ∈ toGates n p, g.1 ≤ n + p.length ∧ g.2 ≤ n + p.length := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hg
  exact ⟨wireIdx_le (hp x hx).1, wireIdx_le (hp x hx).2⟩

/-- **The wire indices of a predicate's gate list**: at most `n + |p| + 1`. -/
theorem bnd_predGates {n : ℕ} {p : SLP (Fin n)} {w : Wire (Fin n)} (hp : Closed p)
    (hw : Valid p w) : ∀ g ∈ predGates p w, g.1 ≤ n + (p.length + 1) ∧ g.2 ≤ n + (p.length + 1) := by
  have h : Closed (p ++ [⟨w, w⟩]) := (good_addNand hp hw hw).1
  intro g hg
  have := bnd_toGates h g hg
  simpa using this

theorem length_predGates {n : ℕ} (p : SLP (Fin n)) (w : Wire (Fin n)) :
    (predGates p w).length = p.length + 1 := by
  simp [predGates, toGates]

end SigabaNeo
