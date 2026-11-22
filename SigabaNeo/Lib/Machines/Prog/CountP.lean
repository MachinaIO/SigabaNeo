import SigabaNeo.Lib.Machines.Prog.Lookup
import SigabaNeo.Lib.Machines.Prog.Macros

/-!
# Counting blocks of a stream

`countP m : Prog 5` appends to tape `1` one bit `false` per block of `m` bits of the stream on
tape `0` (left unchanged): `run_countP`. Tape `2` is the phase within a block, tape `3` a template
of `m − 1` bits, tape `4` the counter of the rounds. It lengthens only tape `1`, by one bit per
round at most, so its per-tape bounds are explicit (`bounds_countP`).
-/

namespace SigabaNeo.Tape

namespace Prog

/-- One round: at the start of a block, a bit out and the phase reset; otherwise the phase
advances. -/
def countBody : Prog 5 := ifBlank 2 (prim (.snoc 1 false) ⨾ cp 2 3) (tl 2)

/-- **Count the blocks of `m` bits of the stream on tape `0`** into tape `1`. -/
def countP (m : ℕ) : Prog 5 := putW 3 (List.replicate (m - 1) false) ⨾ forN 4 0 countBody ⨾ clr 3

/-- The abstract step: (bits out, phase). -/
def countStep (m : ℕ) : ℕ × ℕ → ℕ × ℕ := fun a => if a.2 = 0 then (a.1 + 1, m - 1) else (a.1, a.2 - 1)

theorem countStep_iter_phase (m c : ℕ) : ∀ j, (countStep m)^[j] (c, j) = (c, 0)
  | 0 => rfl
  | j + 1 => by
    rw [Function.iterate_succ_apply, countStep]
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    exact countStep_iter_phase m c j

theorem countStep_iter_block {m : ℕ} (hm : 0 < m) (c : ℕ) : (countStep m)^[m] (c, 0) = (c + 1, 0) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [Function.iterate_succ_apply, countStep]
  simp only [if_true, Nat.add_sub_cancel]
  exact countStep_iter_phase _ _ m'

theorem countStep_iter {m : ℕ} (hm : 0 < m) : ∀ g c, (countStep m)^[m * g] (c, 0) = (c + g, 0)
  | 0, c => by simp
  | g + 1, c => by
    rw [Nat.mul_succ, Function.iterate_add_apply, countStep_iter_block hm, countStep_iter hm g]
    congr 1; omega

/-- **The law of `countP`**: from blank tapes `2 3 4` and a stream of `m g` bits, `g` bits out. -/
theorem run_countP {m g : ℕ} (hm : 0 < m) (s : Store 5) (h0 : (s 0).length = m * g)
    (h2 : s 2 = []) (h3 : s 3 = []) (h4 : s 4 = []) :
    run (countP m) s = Function.update s 1 (s 1 ++ List.replicate g false) := by
  set s1 := Function.update s 3 (List.replicate (m - 1) false) with hs1
  let G : ℕ × ℕ → Store 5 := fun a =>
    Function.update (Function.update s1 1 (s 1 ++ List.replicate a.1 false)) 2
      (List.replicate a.2 false)
  have hstep : ∀ a w, run countBody (Function.update (G a) 4 w) =
      Function.update (G (countStep m a)) 4 w := by
    rintro ⟨c, y⟩ w
    simp only [countBody, run_ifBlank, G, countStep]
    by_cases hy : y = 0
    · subst hy
      simp only [Function.update_apply, if_true, List.replicate_zero, if_pos rfl]
      simp only [run_seq, run_prim, Prim.apply, run_copy]
      funext t
      simp only [Function.update_apply, hs1]
      fin_cases t <;> simp [List.replicate_succ', List.append_assoc]
    · have hne : List.replicate y false ≠ [] := by simp [hy]
      simp only [Function.update_apply, if_true]
      rw [if_neg (by simpa using hy), if_neg hy]
      simp only [run_tail]
      funext t
      simp only [Function.update_apply]
      fin_cases t <;> simp [List.tail_replicate]
  have hs : Function.update (run (putW 3 (List.replicate (m - 1) false)) s) 4
      ((run (putW 3 (List.replicate (m - 1) false)) s) 0) =
      Function.update (G (0, 0)) 4 ((run (putW 3 (List.replicate (m - 1) false)) s) 0) := by
    rw [run_putW]
    funext t
    simp only [G, Function.update_apply, hs1]
    fin_cases t <;> simp [h2]
  rw [countP, run_seq, run_seq, run_forN 4 0 countBody G (countStep m) hstep (0, 0) _ hs]
  rw [run_putW, Function.update_of_ne (by decide), h0, countStep_iter hm g 0, Nat.zero_add]
  simp only [run_clear, G]
  funext t
  simp only [Function.update_apply, hs1]
  fin_cases t <;> simp [h2, h3, h4]

theorem coinFree_countP (m : ℕ) : (countP m).CoinFree := by
  have h := coinFree_putW (3 : Fin 5) (List.replicate (m - 1) false)
  simp only [CoinFree] at h ⊢
  simp [countP, forN, countBody, coinFreeB, h]

theorem wf_countP (m : ℕ) : (countP m).WF :=
  ⟨wf_putW _ _, ⟨⟨trivial, wf_of_wfB rfl, preserves_of_preservesB rfl⟩, trivial⟩⟩

/-! ### Capping a count -/

/-- One round of the cap: move one bit of the count (tape `0`) to tape `1` while there is one. -/
def capBody : Prog 5 := ifBlank 0 (nop 0) (prim (.pop 0 2) ⨾ prim (.snoc 1 false) ⨾ clr 2)

/-- **Cap a count at `w`**: tape `0 := replicate (min g w) false` from `replicate g false`
(tape `1` the result under construction, `2` scratch, `3` the template `w`, `4` the counter). -/
def capP (w : ℕ) : Prog 5 :=
  putW 3 (List.replicate w false) ⨾ forN 4 3 capBody ⨾ cp 0 1 ⨾ clr 1 ⨾ clr 3

/-- The abstract step of the cap: bits moved. -/
def capStep (g : ℕ) (a : ℕ) : ℕ := if a < g then a + 1 else a

theorem capStep_iter (g : ℕ) : ∀ n, (capStep g)^[n] 0 = min g n
  | 0 => by simp
  | n + 1 => by
    rw [Function.iterate_succ_apply', capStep_iter g n, capStep]
    split_ifs with h <;> omega

theorem run_capP (w g : ℕ) (s : Store 5) (h0 : s 0 = List.replicate g false) (h1 : s 1 = [])
    (h2 : s 2 = []) (h3 : s 3 = []) (h4 : s 4 = []) :
    run (capP w) s = Function.update s 0 (List.replicate (min g w) false) := by
  set s1 := Function.update s 3 (List.replicate w false) with hs1
  let G : ℕ → Store 5 := fun a =>
    Function.update (Function.update s1 0 (List.replicate (g - a) false)) 1
      (List.replicate (min a g) false)
  have hstep : ∀ a w', run capBody (Function.update (G a) 4 w') =
      Function.update (G (capStep g a)) 4 w' := by
    intro a w'
    simp only [capBody, run_ifBlank, G, capStep]
    by_cases ha : a < g
    · have hne : List.replicate (g - a) false ≠ [] := by simp; omega
      rw [if_neg (by simpa [Function.update_apply] using hne), if_pos ha]
      simp only [run_seq, run_prim, Prim.apply, run_clear]
      funext t
      simp only [Function.update_apply, hs1]
      have e1 : g - (a + 1) = g - a - 1 := by omega
      have e2 : min (a + 1) g = min a g + 1 := by omega
      fin_cases t <;> simp [e1, e2, List.replicate_succ', h2, List.tail_replicate, hd]
    · have he : g - a = 0 := by omega
      rw [if_pos (by simp [Function.update_apply, he]), if_neg ha]
      simp only [nop, run_copy, Function.update_eq_self]
  have hs : Function.update (run (putW 3 (List.replicate w false)) s) 4
      ((run (putW 3 (List.replicate w false)) s) 3) =
      Function.update (G 0) 4 ((run (putW 3 (List.replicate w false)) s) 3) := by
    rw [run_putW]
    funext t
    simp only [G, Function.update_apply, hs1]
    fin_cases t <;> simp [h0, h1]
  rw [capP, run_seq, run_seq, run_forN 4 3 capBody G (capStep g) hstep 0 _ hs]
  rw [run_putW, Function.update_self, List.length_replicate, capStep_iter g w]
  simp only [run_seq, run_copy, run_clear, G]
  funext t
  simp only [Function.update_apply, hs1]
  have e : min (min g w) g = min g w := by omega
  fin_cases t <;> simp [e, h1, h2, h3, h4]

/-! ### Per-tape bounds -/

theorem supB_le_ofC {ℓ : Fin k → ℕ} {M : ℕ} (h : ∀ i, ℓ i ≤ M) : supB ℓ ≤ M :=
  Finset.sup_le fun i _ => h i

/-- The bound of the rounds' iterates of `countP`. -/
def countV (m S O Y : ℕ) (j : ℕ) : Fin 5 → ℕ := ![S, O + j, max Y (m - 1), m - 1, S]

theorem countBody_len (m S O Y j : ℕ) (x : Fin 5 → ℕ) (hx : x ≤ countV m S O Y j) :
    lenBoundT countBody x ≤ countV m S O Y (j + 1) := by
  have h0 : x 0 ≤ S := hx 0
  have h1 : x 1 ≤ O + j := hx 1
  have h2 : x 2 ≤ max Y (m - 1) := hx 2
  have h3 : x 3 ≤ m - 1 := hx 3
  have h4 : x 4 ≤ S := hx 4
  intro t
  simp only [countBody, lenBoundT, Prim.lenT, Function.update_apply, countV]
  fin_cases t <;> simp <;> omega

/-- The time bound of `countP` (`Mx` bounds every tape). -/
def countT (m S Mx : ℕ) : ℕ :=
  (m + 1) * (2 * (Mx + (m + 1)) + 5) + ((2 * (Mx + 1) + 3) + (S * (2 * Mx + 3 + 4 * (2 * (Mx + 4) + 5) + 1) + 2) +
    (2 * (Mx + 1) + 3))

/-- **Per-tape bounds of `countP`**: the stream kept, at most one bit out per round. -/
theorem bounds_countP (m S O Y Z Q : ℕ) (ℓ : Fin 5 → ℕ) (hℓ : ℓ ≤ ![S, O, Y, Z, Q]) :
    lenBoundT (countP m) ℓ ≤ ![S, O + S, max Y (m - 1), 0, S] ∧
      timeBoundT (countP m) ℓ ≤ countT m S (S + O + Y + Z + Q + m) := by
  have l0 : ℓ 0 ≤ S := hℓ 0
  have l1 : ℓ 1 ≤ O := hℓ 1
  have l2 : ℓ 2 ≤ Y := hℓ 2
  have l3 : ℓ 3 ≤ Z := hℓ 3
  have l4 : ℓ 4 ≤ Q := hℓ 4
  set Mx := S + O + Y + Z + Q + m with hMx
  -- the template
  set ℓ1 := lenBoundT (putW 3 (List.replicate (m - 1) false)) ℓ with hℓ1
  have e1 : ℓ1 = Function.update ℓ 3 (m - 1) := by rw [hℓ1, lenBoundT_putW]; simp
  -- the counter
  set ℓ2 := (Prim.copy (4 : Fin 5) 0).lenT ℓ1 with hℓ2
  have h2v : ℓ2 ≤ countV m S O Y 0 := by
    intro t
    simp only [hℓ2, e1, Prim.lenT, Function.update_apply, countV]
    fin_cases t <;> simp <;> omega
  have hit : ∀ j, (loopStepT 4 countBody)^[j] ℓ2 ≤ countV m S O Y j := by
    intro j
    induction j with
    | zero => exact h2v
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact countBody_len m S O Y j _ ((tailB_le 4 _).trans ih)
  have hround : ∀ j < ℓ2 4, roundTimeT (timeBoundT countBody) 4 ((loopStepT 4 countBody)^[j] ℓ2) ≤
      2 * Mx + 3 + 4 * (2 * (Mx + 4) + 5) := by
    intro j hj
    have hj' : j ≤ S := by
      have := h2v 4; simp [countV] at this; omega
    have hb : ∀ t, ((loopStepT 4 countBody)^[j] ℓ2) t ≤ Mx := fun t => by
      have := hit j t
      fin_cases t <;> simp [countV] at this ⊢ <;> omega
    simp only [roundTimeT]
    have hs := supB_le_ofC hb
    have hbody := timeBoundT_le_pcount countBody ⟨⟨trivial, trivial⟩, trivial⟩
      (tailB 4 ((loopStepT 4 countBody)^[j] ℓ2)) (M := Mx)
      (fun t => (tailB_le 4 _ t).trans (hb t))
    have : pcount countBody = 4 := rfl
    rw [this] at hbody
    omega
  have tloop := timeBoundT_loop_le 4 countBody ℓ2 hround
  have hlenloop : lenBoundT (loop 4 countBody) ℓ2 ≤ countV m S O Y S := by
    rw [lenBoundT_loop]
    refine iterSupT_le fun j hj => (hit j).trans ?_
    have : j ≤ S := by have := h2v 4; simp [countV] at this; omega
    intro t
    fin_cases t <;> simp [countV] <;> omega
  refine ⟨fun t => ?_, ?_⟩
  · show (Prim.clear (3 : Fin 5)).lenT (lenBoundT (loop 4 countBody) ℓ2) t ≤ _
    have := hlenloop t
    simp only [Prim.lenT, Function.update_apply]
    fin_cases t <;> simp [countV] at this ⊢ <;> omega
  · show timeBoundT (putW 3 (List.replicate (m - 1) false)) ℓ +
      ((2 * (supB ℓ1 + (Prim.copy (4 : Fin 5) 0).pad) + 3) + timeBoundT (loop 4 countBody) ℓ2 +
        (2 * (supB (lenBoundT (loop 4 countBody) ℓ2) + (Prim.clear (3 : Fin 5)).pad) + 3)) ≤ _
    have t1 := timeBoundT_le_pcount (putW 3 (List.replicate (m - 1) false)) (loopFree_putW _ _) ℓ
      (M := Mx) (fun t => by fin_cases t <;> simp <;> omega)
    rw [pcount_putW, List.length_replicate] at t1
    have s1 : supB ℓ1 ≤ Mx := supB_le_ofC fun t => by
      rw [e1]; fin_cases t <;> simp [Function.update_apply] <;> omega
    have s3 : supB (lenBoundT (loop 4 countBody) ℓ2) ≤ Mx := supB_le_ofC fun t => by
      have := hlenloop t; fin_cases t <;> simp [countV] at this ⊢ <;> omega
    have hS2 : ℓ2 4 ≤ S := by have := h2v 4; simp [countV] at this; omega
    have tl' : timeBoundT (loop 4 countBody) ℓ2 ≤ S * (2 * Mx + 3 + 4 * (2 * (Mx + 4) + 5) + 1) + 2 :=
      tloop.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hS2) 2)
    simp only [Prim.pad, countT]
    have : (m - 1 + 1) * (2 * (Mx + (m - 1 + 1)) + 5) ≤ (m + 1) * (2 * (Mx + (m + 1)) + 5) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega

theorem coinFree_capP (w : ℕ) : (capP w).CoinFree := by
  have h := coinFree_putW (3 : Fin 5) (List.replicate w false)
  simp only [CoinFree] at h ⊢
  simp [capP, forN, capBody, nop, coinFreeB, h]

theorem wf_capP (w : ℕ) : (capP w).WF :=
  ⟨wf_putW _ _, ⟨⟨trivial, wf_of_wfB rfl, preserves_of_preservesB rfl⟩, trivial, trivial, trivial⟩⟩

/-- The bound of the rounds' iterates of `capP`. -/
def capV (w S O X : ℕ) (j : ℕ) : Fin 5 → ℕ := ![S, O + j, max X 1, w, w]

theorem capBody_len (w S O X j : ℕ) (x : Fin 5 → ℕ) (hx : x ≤ capV w S O X j) :
    lenBoundT capBody x ≤ capV w S O X (j + 1) := by
  have h0 : x 0 ≤ S := hx 0
  have h1 : x 1 ≤ O + j := hx 1
  have h2 : x 2 ≤ max X 1 := hx 2
  have h3 : x 3 ≤ w := hx 3
  have h4 : x 4 ≤ w := hx 4
  intro t
  simp only [capBody, nop, lenBoundT, Prim.lenT, Function.update_apply, capV]
  fin_cases t <;> simp <;> omega

/-- The time bound of `capP` (`Mx` bounds every tape). -/
def capT (w Mx : ℕ) : ℕ :=
  (w + 1) * (2 * (Mx + (w + 1)) + 5) + ((2 * (Mx + 1) + 3) + (w * (2 * Mx + 3 + 5 * (2 * (Mx + 5) + 5) + 1) + 2) +
    (3 * (2 * (Mx + 3) + 5)))

/-- **Per-tape bounds of `capP`**: the count below `O + w`. -/
theorem bounds_capP (w S O X Z Q : ℕ) (ℓ : Fin 5 → ℕ) (hℓ : ℓ ≤ ![S, O, X, Z, Q]) :
    lenBoundT (capP w) ℓ ≤ ![O + w, 0, max X 1, 0, w] ∧
      timeBoundT (capP w) ℓ ≤ capT w (S + O + X + Z + Q + w + 1) := by
  have l0 : ℓ 0 ≤ S := hℓ 0
  have l1 : ℓ 1 ≤ O := hℓ 1
  have l2 : ℓ 2 ≤ X := hℓ 2
  have l3 : ℓ 3 ≤ Z := hℓ 3
  have l4 : ℓ 4 ≤ Q := hℓ 4
  set Mx := S + O + X + Z + Q + w + 1 with hMx
  set ℓ1 := lenBoundT (putW 3 (List.replicate w false)) ℓ with hℓ1
  have e1 : ℓ1 = Function.update ℓ 3 w := by rw [hℓ1, lenBoundT_putW]; simp
  set ℓ2 := (Prim.copy (4 : Fin 5) 3).lenT ℓ1 with hℓ2
  have h2v : ℓ2 ≤ capV w S O X 0 := by
    intro t
    simp only [hℓ2, e1, Prim.lenT, Function.update_apply, capV]
    fin_cases t <;> simp <;> omega
  have hit : ∀ j, (loopStepT 4 capBody)^[j] ℓ2 ≤ capV w S O X j := by
    intro j
    induction j with
    | zero => exact h2v
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact capBody_len w S O X j _ ((tailB_le 4 _).trans ih)
  have hw2 : ℓ2 4 ≤ w := by have := h2v 4; simp [capV] at this; omega
  have hround : ∀ j < ℓ2 4, roundTimeT (timeBoundT capBody) 4 ((loopStepT 4 capBody)^[j] ℓ2) ≤
      2 * Mx + 3 + 5 * (2 * (Mx + 5) + 5) := by
    intro j hj
    have hb : ∀ t, ((loopStepT 4 capBody)^[j] ℓ2) t ≤ Mx := fun t => by
      have := hit j t
      fin_cases t <;> simp [capV] at this ⊢ <;> omega
    simp only [roundTimeT]
    have hs := supB_le_ofC hb
    have hbody := timeBoundT_le_pcount capBody ⟨trivial, ⟨trivial, trivial, trivial⟩⟩
      (tailB 4 ((loopStepT 4 capBody)^[j] ℓ2)) (M := Mx)
      (fun t => (tailB_le 4 _ t).trans (hb t))
    have : pcount capBody = 5 := rfl
    rw [this] at hbody
    omega
  have tloop := timeBoundT_loop_le 4 capBody ℓ2 hround
  have hlenloop : lenBoundT (loop 4 capBody) ℓ2 ≤ capV w S O X w := by
    rw [lenBoundT_loop]
    refine iterSupT_le fun j hj => (hit j).trans ?_
    intro t
    fin_cases t <;> simp [capV] <;> omega
  refine ⟨fun t => ?_, ?_⟩
  · show (Prim.clear (3 : Fin 5)).lenT ((Prim.clear (1 : Fin 5)).lenT ((Prim.copy (0 : Fin 5) 1).lenT
      (lenBoundT (loop 4 capBody) ℓ2))) t ≤ _
    have a1 := hlenloop 1
    have a2 := hlenloop 2
    have a4 := hlenloop 4
    simp only [capV] at a1 a2 a4
    simp only [Prim.lenT, Function.update_apply]
    fin_cases t <;> simp at a1 a2 a4 ⊢ <;> omega
  · show timeBoundT (putW 3 (List.replicate w false)) ℓ +
      ((2 * (supB ℓ1 + (Prim.copy (4 : Fin 5) 3).pad) + 3) + timeBoundT (loop 4 capBody) ℓ2 +
        timeBoundT (cp 0 1 ⨾ clr 1 ⨾ clr 3) (lenBoundT (loop 4 capBody) ℓ2)) ≤ _
    have t1 := timeBoundT_le_pcount (putW 3 (List.replicate w false)) (loopFree_putW _ _) ℓ
      (M := Mx) (fun t => by fin_cases t <;> simp <;> omega)
    rw [pcount_putW, List.length_replicate] at t1
    have s1 : supB ℓ1 ≤ Mx := supB_le_ofC fun t => by
      rw [e1]; fin_cases t <;> simp [Function.update_apply] <;> omega
    have hb3 : ∀ t, lenBoundT (loop 4 capBody) ℓ2 t ≤ Mx := fun t => by
      have := hlenloop t; fin_cases t <;> simp [capV] at this ⊢ <;> omega
    have t3 := timeBoundT_le_pcount (cp 0 1 ⨾ clr 1 ⨾ clr 3 : Prog 5) ⟨trivial, trivial, trivial⟩ _ hb3
    have : pcount (cp 0 1 ⨾ clr 1 ⨾ clr 3 : Prog 5) = 3 := rfl
    rw [this] at t3
    have tl' : timeBoundT (loop 4 capBody) ℓ2 ≤ w * (2 * Mx + 3 + 5 * (2 * (Mx + 5) + 5) + 1) + 2 :=
      tloop.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hw2) 2)
    simp only [Prim.pad, capT]
    omega

end Prog

end SigabaNeo.Tape
