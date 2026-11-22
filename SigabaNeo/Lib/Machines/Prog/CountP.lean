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

/-! ### Per-tape bounds -/

theorem supB_le_of' {ℓ : Fin k → ℕ} {M : ℕ} (h : ∀ i, ℓ i ≤ M) : supB ℓ ≤ M :=
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
    have hs := supB_le_of' hb
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
    have s1 : supB ℓ1 ≤ Mx := supB_le_of' fun t => by
      rw [e1]; fin_cases t <;> simp [Function.update_apply] <;> omega
    have s3 : supB (lenBoundT (loop 4 countBody) ℓ2) ≤ Mx := supB_le_of' fun t => by
      have := hlenloop t; fin_cases t <;> simp [countV] at this ⊢ <;> omega
    have hS2 : ℓ2 4 ≤ S := by have := h2v 4; simp [countV] at this; omega
    have tl' : timeBoundT (loop 4 countBody) ℓ2 ≤ S * (2 * Mx + 3 + 4 * (2 * (Mx + 4) + 5) + 1) + 2 :=
      tloop.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hS2) 2)
    simp only [Prim.pad, countT]
    have : (m - 1 + 1) * (2 * (Mx + (m - 1 + 1)) + 5) ≤ (m + 1) * (2 * (Mx + (m + 1)) + 5) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega

end Prog

end SigabaNeo.Tape
