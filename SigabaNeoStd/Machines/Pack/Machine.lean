import SigabaNeoStd.Machines.Pack.Tr
import SigabaNeoStd.Machines.Pack.SegPhases
import SigabaNeoStd.Machines.Prog.AppendW

/-!
# The packed machine of a framed program

The physical tapes of `packLayout K w D` (`c = 5 + w + D` tapes): `0` the packed store, `1` the
test tape, `2` the flag of the transducer phases, `3` the buffer of the replacement phase, `4` the
input/output tape, `5 … 5 + w - 1` the workspace, `5 + w …` the counters of the wide loops.

`topZ p i₀ o`: write `K` empty frames on the store tape, replace the segment `i₀` by the input
(loaded on tape `4`), run the packing translation of `p`, read the segment `o` onto tape `4`.

* **`law_topZ`**: its output law on tape `4` is the law of tape `o` after `p` from the input on
  tape `i₀`;
* **`run_packMachine`**: the explicit machine `packMachine` (with `5 + w + D` tapes) has the output
  law of `XProg.toMachineT p i₀ o n`, given a time judgment for `topZ` (`ZProg.HT`).
-/

namespace SigabaNeo.Tape.Pack

open Cslib Cslib.Probability Function

variable {K w D : ℕ}

/-! ### The concrete layout -/

/-- Tape `a` of `5 + w + D`. -/
def tp (w D a : ℕ) (h : a < 5 + w + D) : Fin (5 + w + D) := ⟨a, h⟩

/-- The workspace tapes. -/
def wEmb (w D : ℕ) : Fin w ↪ Fin (5 + w + D) :=
  ⟨fun j => ⟨5 + j, by omega⟩, fun a b h => Fin.ext (by simpa using h)⟩

/-- The counter tapes. -/
def fEmb (w D : ℕ) : Fin D ↪ Fin (5 + w + D) :=
  ⟨fun d => ⟨5 + w + d, by omega⟩, fun a b h => Fin.ext (by simpa using h)⟩

@[simp] theorem wEmb_val (j : Fin w) : (wEmb w D j).val = 5 + j := rfl
@[simp] theorem fEmb_val (d : Fin D) : (fEmb w D d).val = 5 + w + d := rfl
@[simp] theorem tp_val (a : ℕ) (h : a < 5 + w + D) : (tp w D a h).val = a := rfl

/-- The concrete layout. -/
def packLayout (w D : ℕ) : Layout (5 + w + D) w D where
  st := tp w D 0 (by omega)
  T := tp w D 1 (by omega)
  W := wEmb w D
  F := fEmb w D
  hTst := fun h => by have := congrArg Fin.val h; simp at this
  hWst := fun j h => by have := congrArg Fin.val h; simp at this
  hWT := fun j h => by have := congrArg Fin.val h; simp at this; omega
  hFst := fun d h => by have := congrArg Fin.val h; simp at this
  hFT := fun d h => by have := congrArg Fin.val h; simp at this; omega
  hWF := fun j d h => by have := congrArg Fin.val h; simp at this; omega

/-- The flag tape. -/
def flT (w D : ℕ) : Fin (5 + w + D) := tp w D 2 (by omega)
/-- The buffer tape. -/
def bufT (w D : ℕ) : Fin (5 + w + D) := tp w D 3 (by omega)
/-- The input/output tape. -/
def ioT (w D : ℕ) : Fin (5 + w + D) := tp w D 4 (by omega)

/-- The concrete segment phases. -/
noncomputable def packKit (K w D : ℕ) : Kit K (5 + w + D) (packLayout w D).st where
  get j t := getPh j t (packLayout w D).st (flT w D)
  put j t := putPh j t (packLayout w D).st (flT w D) (bufT w D)
  get_f j t P S _ hS := by rw [getPh_f, getF_pkW j t _ P S hS]
  put_f j t P S _ hS := by rw [putPh_f, putF_pkW j t _ P S hS]

/-! ### The top-level program -/

/-- The packed store of the blank store. -/
theorem pkW_blank : pkW (fun _ : Fin K => ([] : List Bool)) = List.replicate K false := by
  rw [pkW, pkL]
  simp only [List.ofFn_const, List.flatMap_replicate, Turing.MultiTapeTM.frame]
  simp

/-- **The packed program**: build the packed input store, run, read the output segment. -/
noncomputable def topZ (p : XProg K) (i₀ o : Fin K) : ZProg (5 + w + D) :=
  .seq (.xp (.prog (Prog.snocN (packLayout w D).st false K)))
    (.seq (.ph (putPh i₀ (ioT w D) (packLayout w D).st (flT w D) (bufT w D)))
      (.seq (tr (packLayout w D) (packKit K w D) (Embedding.refl _) 0 p)
        (.ph (getPh o (ioT w D) (packLayout w D).st (flT w D)))))

theorem st_ne_io : (packLayout w D).st ≠ ioT w D := by simp [packLayout, ioT, tp]

/-- **The law of the packed program.** -/
theorem law_topZ (hw : 3 ≤ w) (p : XProg K) (hp : OkX w D 0 p) (i₀ o : Fin K) (x : List Bool) :
    ((topZ (w := w) (D := D) p i₀ o).law (inputStore (ioT w D) x)).map (fun s => s (ioT w D)) =
      (p.law (inputStore i₀ x)).map (fun s => s o) := by
  set lay := packLayout w D
  set P0 : Store (5 + w + D) := inputStore (ioT w D) x
  have hst0 : P0 lay.st = [] := by simp [P0, inputStore, update_of_ne st_ne_io, lay]
  rw [topZ, ZProg.law_seq, ZProg.law_xp, XProg.law_prog,
    Prog.law_eq_run_of_coinFree _ (Prog.coinFree_snocN _ _ _), PMF.pure_bind, Prog.run_snocN,
    ZProg.law_seq, ZProg.law_ph, PMF.pure_bind, putPh_f]
  set S0 : Store K := fun _ => []
  have h1 : update P0 lay.st (P0 lay.st ++ List.replicate K false) lay.st = pkW S0 := by
    rw [update_self, hst0, List.nil_append, pkW_blank]
  rw [putF_pkW i₀ _ _ _ S0 h1]
  have hS : update S0 i₀ (update P0 lay.st (P0 lay.st ++ List.replicate K false) (ioT w D)) =
      inputStore i₀ x := by
    rw [update_of_ne (Ne.symm st_ne_io)]
    simp [S0, P0, inputStore]
  rw [hS, ZProg.law_seq]
  set P2 := update (update (update P0 lay.st (P0 lay.st ++ List.replicate K false)) lay.st
    (pkW (inputStore i₀ x))) (ioT w D) []
  have hP2 : ∀ y, y ≠ lay.st → P2 y = [] := by
    intro y hy
    by_cases hyo : y = ioT w D
    · subst hyo; simp [P2]
    · simp [P2, update_of_ne hyo, update_of_ne hy, P0, inputStore]
  have hP2st : P2 lay.st = pkW (inputStore i₀ x) := by
    simp only [P2]; rw [update_of_ne st_ne_io, update_self]
  rw [law_tr hw p hp P2 _ hP2 hP2st, PMF.bind_map, PMF.map_bind]
  simp only [Function.comp_def, ZProg.law_ph, PMF.pure_map, getPh_f]
  rw [← PMF.bind_pure_comp]
  congr 1
  funext S'
  rw [getF_pkW o _ _ _ S' (update_self _ _ _)]
  simp

/-! ### The machine -/

/-- **The packed machine** of a framed program, with `5 + w + D` tapes and the clock
`ZProg.totalTime n t lo`. -/
noncomputable def packMachine (p : XProg K) (i₀ o : Fin K) (n t lo : ℕ) : Machine :=
  (topZ (w := w) (D := D) p i₀ o).toMachineZ (ioT w D) (ioT w D) n t lo

/-- **The output law of the packed machine**: the same as that of `XProg.toMachineT p i₀ o n`,
given a time judgment `t` and an output length bound `lo`. -/
theorem run_packMachine (hw : 3 ≤ w) (p : XProg K) (hp : OkX w D 0 p) (i₀ o : Fin K)
    (n t lo : ℕ) (x : List Bool) (hx : x.length ≤ n)
    (hT : (topZ (w := w) (D := D) p i₀ o).HT (fun s => s = inputStore (ioT w D) x) t)
    (hlo : ∀ s ∈ (p.law (inputStore i₀ x)).support, (s o).length ≤ lo) :
    (packMachine (w := w) (D := D) p i₀ o n t lo).run x =
      (p.law (inputStore i₀ x)).map (fun s => s o) := by
  have hlo' : ∀ s ∈ ((topZ (w := w) (D := D) p i₀ o).law (inputStore (ioT w D) x)).support,
      (s (ioT w D)).length ≤ lo := by
    intro s hs
    have h : s (ioT w D) ∈ (PMF.map (fun s : Store (5 + w + D) => s (ioT w D))
        ((topZ (w := w) (D := D) p i₀ o).law (inputStore (ioT w D) x))).support := by
      rw [PMF.support_map]; exact ⟨s, hs, rfl⟩
    rw [law_topZ hw p hp, PMF.support_map] at h
    obtain ⟨S, hS, he⟩ := h
    rw [← he]
    exact hlo S hS
  rw [packMachine, ZProg.run_toMachineZ _ _ _ n t lo x hx hT hlo', law_topZ hw p hp]

theorem tapes_packMachine (p : XProg K) (i₀ o : Fin K) (n t lo : ℕ) :
    (packMachine (w := w) (D := D) p i₀ o n t lo).tapes = 5 + w + D := rfl

theorem states_packMachine (p : XProg K) (i₀ o : Fin K) (n t lo : ℕ) :
    (packMachine (w := w) (D := D) p i₀ o n t lo).states =
      Fintype.card (topZ (w := w) (D := D) p i₀ o).State + 4 :=
  ZProg.states_toMachineZ _ _ _ _ _ _

end SigabaNeo.Tape.Pack
