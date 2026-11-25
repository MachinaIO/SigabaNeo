import SigabaNeo.Lib.Machines.Prog.XFlat
import SigabaNeo.Lib.Machines.Prog.Sample
import SigabaNeo.Lib.Machines.Prog.Macros
import SigabaNeo.Lib.Machines.Prog.Pass
import SigabaNeo.Lib.Machines.Prog.AbsBound

/-!
# Relabelled programs with coins, and restricting a program to the tapes it mentions

`SigabaNeo.Lib.Machines.Prog.Det` relabels the tapes of a program (`Prog.map`) and computes the
pure semantics of a relabelled deterministic program. Here the **law** of a relabelled program, coins
included:

* `Prog.law_map`: for an embedding `e`, `(map e p).law s = (p.law (s ∘ e)).map (embedF e s)`;
* `Prog.tapes`: the tapes a program mentions; `Prog.map_congr`, `Prog.map_map`, `Prog.map_id'`;
* `Prog.localize`: the restriction of a program to a list of tapes containing those it mentions,
  with `Prog.map_localize : map e (localize l p) = p`.

Also: `embedF` identities, and loops as iterated kernels (`law_loop_kIter`, `kIter_map_embed`).
-/

namespace SigabaNeo.Tape

open Cslib Cslib.Probability

variable {k m : ℕ}

/-! ### `embedF` identities -/

theorem embedF_comp_self (e : Fin m ↪ Fin k) (s : Store k) (a : Store m) :
    (fun j => embedF e s a (e j)) = a := funext fun j => embedF_apply_self e s a j

theorem embedF_embedF (e : Fin m ↪ Fin k) (s : Store k) (a b : Store m) :
    embedF e (embedF e s a) b = embedF e s b := by
  rw [XProg.embedF_eq_extend, XProg.embedF_eq_extend, XProg.embedF_eq_extend,
    extend_extend e.injective]

theorem embedF_update_range (e : Fin m ↪ Fin k) (s : Store k) (i : Fin m) (w : List Bool)
    (b : Store m) : embedF e (Function.update s (e i) w) b = embedF e s b := by
  funext l
  rcases embedF_cases e (Function.update s (e i) w) b l with ⟨hl, h⟩ | ⟨j, rfl, h⟩
  · rw [h, Function.update_of_ne]
    · rcases embedF_cases e s b l with ⟨-, h'⟩ | ⟨j, rfl, h'⟩
      · exact h'.symm
      · rw [partialInv_self] at hl; simp at hl
    · rintro rfl; rw [partialInv_self] at hl; simp at hl
  · rw [h, embedF_apply_self]

/-! ### Loops as iterated kernels -/

theorem eval_iterate_kIter {σ : Type} (f : σ → ProbComp σ) :
    ∀ (n : ℕ) (s : σ), ProbComp.eval (OracleComp.iterate n f s) =
      XProg.kIter (fun t => ProbComp.eval (f t)) n s
  | 0, s => by simp [XProg.kIter]
  | n + 1, s => by
    rw [OracleComp.iterate_succ, ProbComp.eval_bind, eval_iterate_kIter f n s, XProg.kIter]

/-- Iterating a kernel on a framed sub-store. -/
theorem kIter_map_embed (e : Fin m ↪ Fin k) (Kn : Store m → PMF (Store m)) :
    ∀ (n : ℕ) (s : Store k), (XProg.kIter Kn n (fun j => s (e j))).map (embedF e s) =
      XProg.kIter (fun t => (Kn (fun j => t (e j))).map (embedF e t)) n s
  | 0, s => by simp [XProg.kIter, embedF_self]
  | n + 1, s => by
    rw [XProg.kIter, XProg.kIter, ← kIter_map_embed e Kn n s, PMF.bind_map, PMF.map_bind]
    congr 1
    funext a
    simp only [Function.comp_apply, embedF_comp_self]
    congr 1
    funext b
    exact (embedF_embedF e s a b).symm

theorem XProg.law_loop_kIter (i : Fin k) (body : XProg k) (s : Store k) :
    (XProg.loop i body).law s = XProg.kIter (fun t => body.law (tailAt i t)) (s i).length s := by
  show ProbComp.eval (OracleComp.iterate _ _ s) = _
  rw [eval_iterate_kIter]
  rfl

namespace Prog

theorem law_loop_kIter (i : Fin k) (body : Prog k) (s : Store k) :
    (loop i body).law s = XProg.kIter (fun t => body.law (tailAt i t)) (s i).length s := by
  show ProbComp.eval (OracleComp.iterate _ _ s) = _
  rw [eval_iterate_kIter]
  rfl

theorem law_coin' (i : Fin k) (s : Store k) :
    (coin i).law s = (PMF.uniformOfFintype Bool).map fun b => Function.update s i [b] := by
  simp [law, denote]

/-! ### The law of a relabelled program -/

/-- **The law of a relabelled program**, coins included. -/
theorem law_map (e : Fin m ↪ Fin k) : ∀ (p : Prog m) (s : Store k),
    (map e p).law s = (p.law (fun j => s (e j))).map (embedF e s)
  | prim p, s => by
    rw [map, law_prim, law_prim, Prim.apply_map e.injective, PMF.pure_map,
      XProg.embedF_eq_extend]
    rfl
  | coin i, s => by
    rw [map, law_coin', law_coin', PMF.map_comp]
    congr 1
    funext b
    simp only [Function.comp_apply, XProg.embedF_eq_extend]
    rw [extend_update e.injective]
    congr 1
    exact (extend_comp_self s).symm
  | seq p q, s => by
    rw [map, law_seq, law_seq, law_map e p s, PMF.bind_map, PMF.map_bind]
    congr 1
    funext a
    simp only [Function.comp_apply]
    rw [law_map e q, embedF_comp_self]
    congr 1
    funext b
    exact embedF_embedF e s a b
  | ifBlank i p q, s => by
    rw [map, law_ifBlank, law_ifBlank, law_map e p s, law_map e q s]
    split_ifs <;> rfl
  | ifBit i p q, s => by
    rw [map, law_ifBit, law_ifBit, law_map e p s, law_map e q s]
    split_ifs <;> rfl
  | loop i body, s => by
    rw [map, law_loop_kIter, law_loop_kIter, kIter_map_embed]
    show XProg.kIter _ (s (e i)).length s = _
    congr 1
    funext t
    rw [law_map e body]
    have h1 : (fun j => tailAt (e i) t (e j)) = tailAt i (fun j => t (e j)) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [tailAt]
      · simp [tailAt, Function.update_of_ne hj, Function.update_of_ne (e.injective.ne hj)]
    rw [h1]
    congr 1
    funext b
    exact embedF_update_range e t i _ b

/-! ### The tapes a program mentions -/

end Prog

namespace Prim

/-- The tapes a primitive mentions. -/
def tapes : Prim k → List (Fin k)
  | clear i | tail i | cons i _ | snoc i _ => [i]
  | copy i j | carry _ i j | pop i j | consHead i j | snocHead i j => [i, j]
  | eq i j f => [i, j, f]

theorem length_tapes_le (p : Prim k) : p.tapes.length ≤ 3 := by cases p <;> simp [tapes]

theorem map_congr {n : ℕ} {u v : Fin n → Fin k} (p : Prim n) (h : ∀ t ∈ p.tapes, u t = v t) :
    p.map u = p.map v := by
  cases p <;> simp_all [tapes, map]

theorem map_id' (p : Prim k) : p.map id = p := by cases p <;> rfl

theorem tapes_map {n : ℕ} (u : Fin n → Fin k) (p : Prim n) : (p.map u).tapes = p.tapes.map u := by
  cases p <;> rfl

end Prim

namespace Prog

/-- The tapes a program mentions. -/
def tapes : Prog k → List (Fin k)
  | prim p => p.tapes
  | coin i => [i]
  | seq p q => p.tapes ++ q.tapes
  | ifBlank i p q => i :: (p.tapes ++ q.tapes)
  | ifBit i p q => i :: (p.tapes ++ q.tapes)
  | loop i body => i :: body.tapes

theorem map_congr {n : ℕ} {u v : Fin n → Fin k} : ∀ (p : Prog n), (∀ t ∈ p.tapes, u t = v t) →
    map u p = map v p
  | prim p, h => by rw [map, map, Prim.map_congr p h]
  | coin i, h => by rw [map, map, h i (by simp [tapes])]
  | seq p q, h => by
    rw [map, map, map_congr p (fun t ht => h t (by simp [tapes, ht])),
      map_congr q (fun t ht => h t (by simp [tapes, ht]))]
  | ifBlank i p q, h => by
    rw [map, map, h i (by simp [tapes]), map_congr p (fun t ht => h t (by simp [tapes, ht])),
      map_congr q (fun t ht => h t (by simp [tapes, ht]))]
  | ifBit i p q, h => by
    rw [map, map, h i (by simp [tapes]), map_congr p (fun t ht => h t (by simp [tapes, ht])),
      map_congr q (fun t ht => h t (by simp [tapes, ht]))]
  | loop i body, h => by
    rw [map, map, h i (by simp [tapes]), map_congr body (fun t ht => h t (by simp [tapes, ht]))]

-- `Prog.map_map` (`SigabaNeo.Lib.Machines.Prog.AbsBound`): `map u (map v p) = map (u ∘ v) p`.

theorem map_id' : ∀ p : Prog k, map id p = p
  | prim p => by rw [map, Prim.map_id']
  | coin i => rfl
  | seq p q => by rw [map, map_id' p, map_id' q]
  | ifBlank i p q => by rw [map, map_id' p, map_id' q]; rfl
  | ifBit i p q => by rw [map, map_id' p, map_id' q]; rfl
  | loop i body => by rw [map, map_id' body]; rfl

/-! ### Restricting to a list of tapes -/

/-- The embedding of the positions of a duplicate-free list. -/
def listEmb (l : List (Fin k)) (hl : l.Nodup) : Fin l.length ↪ Fin k :=
  ⟨fun j => l.get j, List.nodup_iff_injective_get.mp hl⟩

/-- The position of a tape in a nonempty list (`0` if absent). -/
def listIdx (l : List (Fin k)) (hl : 0 < l.length) (t : Fin k) : Fin l.length :=
  if h : l.idxOf t < l.length then ⟨l.idxOf t, h⟩ else ⟨0, hl⟩

theorem listEmb_listIdx (l : List (Fin k)) (hl : l.Nodup) (hl0 : 0 < l.length) {t : Fin k}
    (ht : t ∈ l) : listEmb l hl (listIdx l hl0 t) = t := by
  have h : l.idxOf t < l.length := List.idxOf_lt_length_iff.mpr ht
  simp only [listEmb, listIdx, h, ↓reduceDIte, Function.Embedding.coeFn_mk, List.get_eq_getElem]
  exact List.getElem_idxOf h

/-- The program on the tapes of a list containing those it mentions. -/
def localize (l : List (Fin k)) (hl0 : 0 < l.length) (p : Prog k) : Prog l.length :=
  map (listIdx l hl0) p

theorem map_localize (l : List (Fin k)) (hl : l.Nodup) (hl0 : 0 < l.length) (p : Prog k)
    (hp : ∀ t ∈ p.tapes, t ∈ l) : map (listEmb l hl) (localize l hl0 p) = p := by
  rw [localize, map_map]
  conv_rhs => rw [← map_id' p]
  exact map_congr p fun t ht => listEmb_listIdx l hl hl0 (hp t ht)

/-- **The law of a program, from its restriction** to a list of tapes containing those it
mentions. -/
theorem law_localize (l : List (Fin k)) (hl : l.Nodup) (hl0 : 0 < l.length) (p : Prog k)
    (hp : ∀ t ∈ p.tapes, t ∈ l) (s : Store k) :
    p.law s = ((localize l hl0 p).law (fun j => s (listEmb l hl j))).map
      (embedF (listEmb l hl) s) := by
  conv_lhs => rw [← map_localize l hl hl0 p hp]
  exact law_map _ _ s

end Prog

end SigabaNeo.Tape
