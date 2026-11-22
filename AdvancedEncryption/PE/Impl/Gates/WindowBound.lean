import PE.Impl.Gates.ProgWindow
import SigabaNeo.Lib.Machines.Prog.FrameSize

/-!
# Numeric bounds on the window predicates and the front end's table

* Every gate of a window predicate reads a wire of index at most `384` (`winGates_bnd`): the
  compiled program of `winExp` has at most `374` gates (`length_compile`, `size_winExp`) and its
  gates read only earlier gates (`RefOk`, `inv_compile`).
* So a window predicate has at most `375 · 770` bits (`length_winWord_le`) and its gate list in the
  layout of width `W ≥ 384` has `|gs| · 2W ≤ 750 W` bits.
* The table of the front end has at most `2^20 (n + 6 + 750 W) + 2` primitives
  (`lookCount_frontTbl_le`), and the front end has at most `60` states per primitive
  (`size_frontP_le`).
-/

namespace AdvancedEncryption.PE.Gates.DateWindow

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Lattices.SLP AdvancedEncryption.PE.DateWindow
  SigabaNeo.Tape SigabaNeo.Tape.Prog

/-! ### Gates read only earlier gates -/

section Refs

variable {ι : Type*}

/-- Every gate of `p` reads only gates of `p`. -/
def RefOk (p : SLP ι) : Prop := ∀ g ∈ p, Valid p g.a ∧ Valid p g.b

/-- The invariant of a builder: it extends `p`, its gates read only its gates, its output wire is
one of its wires. -/
def Inv (p : SLP ι) (r : SLP ι × Wire ι) : Prop := Ext p r.1 ∧ RefOk r.1 ∧ Valid r.1 r.2

theorem inv_addNand {p : SLP ι} (hp : RefOk p) {a b : Wire ι} (ha : Valid p a) (hb : Valid p b) :
    Inv p (addNand p a b) := by
  have he := addNand_ext p a b
  refine ⟨he, fun g hg => ?_, addNand_valid p a b⟩
  simp only [addNand, List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact ⟨(hp g hg).1.ext he, (hp g hg).2.ext he⟩
  · exact ⟨ha.ext he, hb.ext he⟩

theorem inv_notW {p : SLP ι} (hp : RefOk p) {a : Wire ι} (ha : Valid p a) : Inv p (notW p a) :=
  inv_addNand hp trivial ha

theorem inv_andW {p : SLP ι} (hp : RefOk p) {a b : Wire ι} (ha : Valid p a) (hb : Valid p b) :
    Inv p (andW p a b) := by
  obtain ⟨e1, r1, v1⟩ := inv_addNand hp ha hb
  obtain ⟨e2, r2, v2⟩ := inv_notW r1 v1
  exact ⟨e1.trans e2, r2, v2⟩

theorem inv_orW {p : SLP ι} (hp : RefOk p) {a b : Wire ι} (ha : Valid p a) (hb : Valid p b) :
    Inv p (orW p a b) := by
  obtain ⟨e1, r1, v1⟩ := inv_notW hp ha
  obtain ⟨e2, r2, v2⟩ := inv_notW r1 (hb.ext e1)
  obtain ⟨e3, r3, v3⟩ := inv_addNand r2 (v1.ext e2) v2
  exact ⟨e1.trans (e2.trans e3), r3, v3⟩

theorem inv_geConst {p : SLP ι} (hp : RefOk p) : ∀ (xs : List (Wire ι)) (as : List Bool),
    (∀ x ∈ xs, ∀ q : SLP ι, Valid q x) → Inv p (geConst p xs as)
  | [], _, _ => ⟨Ext.refl p, hp, trivial⟩
  | _ :: _, [], _ => ⟨Ext.refl p, hp, trivial⟩
  | x :: xs, a :: as, h => by
    obtain ⟨e1, r1, v1⟩ := inv_geConst hp xs as (fun y hy => h y (by simp [hy]))
    simp only [geConst]
    split
    · obtain ⟨e2, r2, v2⟩ := inv_andW r1 (h x (by simp) _) v1
      exact ⟨e1.trans e2, r2, v2⟩
    · obtain ⟨e2, r2, v2⟩ := inv_orW r1 (h x (by simp) _) v1
      exact ⟨e1.trans e2, r2, v2⟩

theorem inv_leConst {p : SLP ι} (hp : RefOk p) : ∀ (xs : List (Wire ι)) (bs : List Bool),
    (∀ x ∈ xs, ∀ q : SLP ι, Valid q x) → Inv p (leConst p xs bs)
  | [], _, _ => ⟨Ext.refl p, hp, trivial⟩
  | _ :: _, [], _ => ⟨Ext.refl p, hp, trivial⟩
  | x :: xs, b :: bs, h => by
    obtain ⟨e1, r1, v1⟩ := inv_leConst hp xs bs (fun y hy => h y (by simp [hy]))
    obtain ⟨e2, r2, v2⟩ := inv_notW (a := x) r1 (h x (by simp) _)
    simp only [leConst]
    split
    · obtain ⟨e3, r3, v3⟩ := inv_orW r2 v2 (v1.ext e2)
      exact ⟨e1.trans (e2.trans e3), r3, v3⟩
    · obtain ⟨e3, r3, v3⟩ := inv_andW r2 v2 (v1.ext e2)
      exact ⟨e1.trans (e2.trans e3), r3, v3⟩

theorem valid_input_all (is : List ι) : ∀ x ∈ is.map Wire.input, ∀ q : SLP ι, Valid q x := by
  intro x hx q
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  trivial

theorem inv_compile : ∀ (e : BExp ι) (p : SLP ι), RefOk p → Inv p (compile p e)
  | .ge is as, p, hp => inv_geConst hp _ as (valid_input_all is)
  | .le is bs, p, hp => inv_leConst hp _ bs (valid_input_all is)
  | .not e, p, hp => by
    obtain ⟨e1, r1, v1⟩ := inv_compile e p hp
    obtain ⟨e2, r2, v2⟩ := inv_notW r1 v1
    exact ⟨e1.trans e2, r2, v2⟩
  | .and e f, p, hp => by
    obtain ⟨e1, r1, v1⟩ := inv_compile e p hp
    obtain ⟨e2, r2, v2⟩ := inv_compile f _ r1
    obtain ⟨e3, r3, v3⟩ := inv_andW r2 (v1.ext e2) v2
    exact ⟨e1.trans (e2.trans e3), r3, v3⟩
  | .or e f, p, hp => by
    obtain ⟨e1, r1, v1⟩ := inv_compile e p hp
    obtain ⟨e2, r2, v2⟩ := inv_compile f _ r1
    obtain ⟨e3, r3, v3⟩ := inv_orW r2 (v1.ext e2) v2
    exact ⟨e1.trans (e2.trans e3), r3, v3⟩

end Refs

/-! ### The gates of a window predicate -/

theorem wireIdx_le {p : SLP (Fin 10)} {w : Wire (Fin 10)} (hw : Valid p w) :
    wireIdx 10 w ≤ 10 + p.length := by
  cases w with
  | one => simp [wireIdx]
  | input i => simp only [wireIdx]; omega
  | gate m =>
    have : m < p.length := hw
    simp only [wireIdx]; omega

/-- **The gates of a window predicate read wires of index at most `384`.** -/
theorem winGates_bnd (w : Window) : ∀ g ∈ winGates w, g.1 ≤ 384 ∧ g.2 ≤ 384 := by
  intro g hg
  have hl := length_compile (winExp w.1.1 w.1.2) ([] : SLP (Fin 10))
  rw [size_winExp] at hl
  simp only [List.length_nil, Nat.zero_add] at hl
  obtain ⟨-, hr, hv⟩ := inv_compile (winExp w.1.1 w.1.2) ([] : SLP (Fin 10))
    (fun g hg => by simp at hg)
  simp only [winGates, predGates, toGates, List.mem_map, List.mem_append,
    List.mem_singleton] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  rcases hg' with hg' | rfl
  · have h1 := wireIdx_le (hr g' hg').1
    have h2 := wireIdx_le (hr g' hg').2
    refine ⟨?_, ?_⟩ <;> dsimp only <;> omega
  · have h1 := wireIdx_le hv
    refine ⟨?_, ?_⟩ <;> dsimp only <;> omega

theorem parse_winWord (w : Window) : parse (winWord w) = winGates w := by
  rw [winWord, parse_unparse]

/-- **A window predicate has at most `375 · 770` bits.** -/
theorem length_winWord_le (w : Window) : (winWord w).length ≤ 375 * 770 := by
  rw [winWord, length_unparse]
  have hb : ∀ x ∈ (winGates w).map (fun g : ℕ × ℕ => g.1 + g.2 + 2), x ≤ 770 := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    have := winGates_bnd w g hg
    omega
  have h := List.sum_le_length_nsmul _ 770 hb
  rw [List.length_map, smul_eq_mul] at h
  exact h.trans (Nat.mul_le_mul_right _ (length_winGates w))

/-- The gate list of a window predicate in the layout of width `W ≥ 384`. -/
theorem length_gsW_winWord_le (w : Window) {W : ℕ} (hW : 384 ≤ W) :
    (gsW W (parse (winWord w))).length ≤ 375 * (2 * W) := by
  rw [parse_winWord, length_gsW (fun g hg => by have := winGates_bnd w g hg; omega)]
  exact Nat.mul_le_mul_right _ (length_winGates w)

/-! ### The table of the front end -/

theorem length_windows_le : windows.length ≤ 2 ^ 20 := by
  refine (List.length_filter_le _ _).trans ?_
  rw [List.length_product, allDates, List.length_product, List.length_finRange]
  norm_num

theorem length_winsN_le (n : ℕ) : (winsN n).length ≤ 2 ^ 20 :=
  (List.length_filter_le _ _).trans length_windows_le

/-- The primitives of a table whose entries are at most `B` bits together. -/
theorem lookCount_map_le {α : Type} (f : α → List Bool × List Bool) (dv : List Bool) (B : ℕ) :
    ∀ l : List α, (∀ a ∈ l, (f a).1.length + (f a).2.length + 4 ≤ B) →
      lookCount (l.map f) dv ≤ l.length * B + dv.length + 1
  | [], _ => by simp [lookCount]
  | a :: l, h => by
    have h1 := h a (by simp)
    have h2 := lookCount_map_le f dv B l (fun b hb => h b (by simp [hb]))
    simp only [List.map_cons, lookCount, List.length_cons]
    rw [Nat.succ_mul]
    omega

/-- **The primitives of the front end's table**: at most `2^20 (n + 6 + 750 W) + 2` for
`W ≥ 384`. -/
theorem lookCount_frontTbl_le (n : ℕ) {W : ℕ} (hW : 384 ≤ W) :
    lookCount (frontTbl n W) [false] ≤ 2 ^ 20 * (n + 6 + 375 * (2 * W)) + 2 := by
  have h := lookCount_map_le (fun p => (padW n (pairWord p), true :: gsW W (parse (pairWord p))))
    [false] (n + 6 + 375 * (2 * W)) (winsN n) (fun p hp => by
      have hw := mem_windows.mp (mem_winsN.mp hp).1
      have e : pairWord p = winWord (winOf p hw) := (winWord_eq_pairWord (winOf p hw)).symm
      have := length_gsW_winWord_le (winOf p hw) hW
      simp only [length_padW, List.length_cons, e]
      omega)
  unfold frontTbl
  refine h.trans ?_
  have := Nat.mul_le_mul_right (n + 6 + 375 * (2 * W)) (length_winsN_le n)
  simp only [List.length_cons, List.length_nil]
  omega

/-! ### The states of the front end -/

/-- A loop-free program has at most `60` states per primitive or branching. -/
theorem size_le_pcount {k : ℕ} : ∀ p : Prog k, p.LoopFree → p.size ≤ 60 * p.pcount
  | .prim p, _ => by
    have : p.pad ≤ 1 := by cases p <;> simp [Prim.pad]
    simp only [Prog.size, pcount]; omega
  | .coin _, _ => by simp [Prog.size, pcount]
  | .seq p q, h => by
    have := size_le_pcount p h.1; have := size_le_pcount q h.2
    simp only [Prog.size, pcount]; omega
  | .ifBlank _ p q, h => by
    have := size_le_pcount p h.1; have := size_le_pcount q h.2
    simp only [Prog.size, pcount]; omega
  | .ifBit _ p q, h => by
    have := size_le_pcount p h.1; have := size_le_pcount q h.2
    simp only [Prog.size, pcount]; omega
  | .loop _ _, h => absurd h (by simp [LoopFree])

theorem loopFree_putW' {k : ℕ} (o : Fin k) : ∀ w : List Bool, (Prog.putW o w).LoopFree
  | [] => trivial
  | _ :: w => ⟨loopFree_putW' o w, trivial⟩

theorem pcount_putW' {k : ℕ} (o : Fin k) : ∀ w : List Bool, (Prog.putW o w).pcount = w.length + 1
  | [] => rfl
  | _ :: w => by simp only [Prog.putW, pcount, pcount_putW' o w, List.length_cons]

theorem loopFree_appendP {k : ℕ} (i j : Fin k) : ∀ m, (appendP i j m).LoopFree
  | 0 => trivial
  | m + 1 => ⟨trivial, trivial, loopFree_appendP i j m⟩

theorem pcount_appendP {k : ℕ} (i j : Fin k) : ∀ m, (appendP i j m).pcount = 2 * m + 1
  | 0 => rfl
  | m + 1 => by simp only [appendP, pcount, pcount_appendP i j m]; ring

/-- **The states of the front end.** -/
theorem size_frontP_le (n W : ℕ) :
    (frontP n W).size ≤ 60 * (n + lookCount (frontTbl n W) [false] + 30) := by
  have h1 := size_le_pcount _ (loopFree_putW' (k := 1) 0 (List.replicate (n + 1) false))
  have h2 : cutCore.size ≤ 60 * 10 := size_le_pcount _ (by simp [cutCore, LoopFree])
  have h3 := size_le_pcount _ (show (lookTail 0 (frontTbl n W) [false] []).LoopFree from
    ⟨loopFree_appendP _ _ _, ⟨loopFree_lookupP _ _, loopFree_putW' _ _⟩,
      by simp [clearAll, LoopFree]⟩)
  rw [pcount_putW', List.length_replicate] at h1
  have e3 : (lookTail 0 (frontTbl n W) [false] []).pcount = lookCount (frontTbl n W) [false] + 12 := by
    simp only [lookTail, pcount, pcount_appendP, pcount_lookupP, pcount_putW', clearAll,
      List.length_nil]
    omega
  rw [e3] at h3
  show Prog.size _ + cutCore.size + (lookTail 0 (frontTbl n W) [false] []).size ≤ _
  omega

end AdvancedEncryption.PE.Gates.DateWindow
