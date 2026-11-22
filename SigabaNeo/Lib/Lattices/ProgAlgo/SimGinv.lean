import SigabaNeo.Lib.Lattices.ProgAlgo.SimJoint
import SigabaNeo.Lib.Lattices.ProgAlgo.Spec
import SigabaNeo.Lib.Machines.Prog.Split

/-!
# Programs of `G⁻¹` for the two binary gadgets on `48` tapes

* `ginvTopP := map gT ginvP` (the top-row gadget): `0 := ginvW N K k (s 1)`; templates `2` … `5` of
  lengths `K`, `2k N`, `k`, `2k · 2k N K`, scratch `6 … 34` (`GPreTop`).
* `ginvGswP` (the Ring-GSW gadget): `0 := ginvGswW N K k (s 1)` on matrices of `2` rows: split the
  rows (`splitP`), `ginvP` on each, join the top halves (`joinP`, `ginvGswW_eq`). Templates `2` …
  `5` as above, `6` `7` of length `2k N K`, `8` blank, `9` `10` of length `k · 2k N K`; registers
  `12 … 16` and scratch `17 … 45` blank (`GPreGsw`).

Both are `GinvSpec`s (`ginvSpec_top`, `ginvSpec_gsw`), the inputs of `simStepP`.
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices SigabaNeo.Lattices.Algo

namespace Prog

open scoped Prog

/-- **A program of `G⁻¹`** on words of `Lin` bits: tape `0` the value, `1` the input; the
precondition `GPre` only looks at the tapes `2 … 47`. -/
structure GinvSpec (G : Prog 48) (Lin Lout : ℕ) (ginv : List Bool → List Bool)
    (GPre : Store 48 → Prop) : Prop where
  noGrow : G.NoGrow
  wf : G.WF
  pre_congr : ∀ s s' : Store 48, (∀ i : Fin 48, 2 ≤ i.val → s i = s' i) → GPre s → GPre s'
  run_eq : ∀ s, GPre s → (s 1).length = Lin → run G s = Function.update s 0 (ginv (s 1))
  len : ∀ a, a.length = Lin → (ginv a).length = Lout

def gT : Fin 35 → Fin 48 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]
theorem gT_inj : Function.Injective gT := by decide
def gsS : Fin 10 → Fin 48 := ![12, 13, 14, 1, 6, 7, 8, 17, 18, 19]
theorem gsS_inj : Function.Injective gsS := by decide
def gi0 : Fin 35 → Fin 48 := ![15, 12, 2, 3, 4, 5, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45]
theorem gi0_inj : Function.Injective gi0 := by decide
def gi1 : Fin 35 → Fin 48 := ![16, 13, 2, 3, 4, 5, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45]
theorem gi1_inj : Function.Injective gi1 := by decide
def gjJ : Fin 11 → Fin 48 := ![0, 15, 16, 14, 9, 10, 8, 5, 17, 18, 19]
theorem gjJ_inj : Function.Injective gjJ := by decide

/-! ### The top-row gadget -/

/-- `G̲⁻¹` on `48` tapes. -/
def ginvTopP : Prog 48 := map gT ginvP

/-- Its precondition: templates `2 … 5`, blank scratch `6 … 34`. -/
def GPreTop (N K k : ℕ) (s : Store 48) : Prop :=
  (∀ i : Fin 48, 6 ≤ i.val → i.val < 35 → s i = []) ∧ (s 2).length = K ∧
    (s 3).length = 2 * k * N ∧ (s 4).length = k ∧ (s 5).length = 2 * k * (2 * k * (N * K))

theorem ginvSpec_top (N K k : ℕ) :
    GinvSpec ginvTopP (lenA N K k 1) (2 * k * (2 * k * (N * K))) (ginvW N K k)
      (GPreTop N K k) where
  noGrow := NoGrow.map gT noGrow_ginvP
  wf := WF.map gT_inj wf_ginvP
  pre_congr := by
    rintro s s' he ⟨h0, h2, h3, h4, h5⟩
    refine ⟨fun i hi hi' => (he i (by omega)).symm.trans (h0 i hi hi'), ?_, ?_, ?_, ?_⟩
    · rw [← he 2 (by decide)]; exact h2
    · rw [← he 3 (by decide)]; exact h3
    · rw [← he 4 (by decide)]; exact h4
    · rw [← he 5 (by decide)]; exact h5
  run_eq := by
    rintro s ⟨h0, h2, h3, h4, h5⟩ h1
    exact run_ginvP_map gT_inj (K := K) (N := N) (k' := k) s
      (fun i hi => by fin_cases i <;> simp [gT] at hi ⊢ <;> exact h0 _ (by simp) (by simp))
      h2 h3 h4 h5 (by rw [show gT 1 = 1 from rfl, h1]; ring)
  len := fun a _ => length_ginvW N K k a

/-! ### The Ring-GSW gadget -/

/-- `G⁻¹` of the Ring-GSW gadget on `48` tapes. -/
def ginvGswP : Prog 48 :=
  map gsS splitP ⨾ map gi0 ginvP ⨾ map gi1 ginvP ⨾ map gjJ joinP ⨾ clr 12 ⨾ clr 13 ⨾ clr 14 ⨾
    clr 15 ⨾ clr 16

/-- Its precondition. -/
def GPreGsw (N K k : ℕ) (s : Store 48) : Prop :=
  (∀ i : Fin 48, 12 ≤ i.val → i.val < 46 → s i = []) ∧ s 8 = [] ∧ (s 2).length = K ∧
    (s 3).length = 2 * k * N ∧ (s 4).length = k ∧ (s 5).length = 2 * k * (2 * k * (N * K)) ∧
    (s 6).length = 2 * k * (N * K) ∧ (s 7).length = 2 * k * (N * K) ∧
    (s 9).length = k * (2 * k * (N * K)) ∧ (s 10).length = k * (2 * k * (N * K))

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem run_ginvGswP {N K k : ℕ} (s : Store 48) (hp : GPreGsw N K k s)
    (h1 : (s 1).length = lenA N K k 2) :
    run ginvGswP s = Function.update s 0 (ginvGswW N K k (s 1)) := by
  obtain ⟨h0, h8, h2, h3, h4, h5, h6, h7, h9, h10⟩ := hp
  have hb : ∀ i : Fin 48, 12 ≤ i.val → i.val < 46 → s i = [] := h0
  simp only [ginvGswP, run_seq, run_clear]
  rw [run_splitP_map gsS_inj _ ?_ ?_ ?_,
    run_ginvP_map gi0_inj (K := K) (N := N) (k' := k) _ ?_ ?_ ?_ ?_ ?_ ?_,
    run_ginvP_map gi1_inj (K := K) (N := N) (k' := k) _ ?_ ?_ ?_ ?_ ?_ ?_,
    run_joinP_map gjJ_inj _ ?_ ?_ ?_ ?_]
  · have hR : 2 * k * (N * K) ≤ (s 1).length := by rw [h1, lenA]; nlinarith
    have hd : ((s 1).drop (2 * k * (N * K))).length = 2 * k * (N * K) := by
      rw [List.length_drop, h1, lenA]; ring_nf; omega
    have hg : ∀ x, takeD (k * (2 * k * (N * K))) (ginvW N K k x) =
        (ginvW N K k x).take (k * (2 * k * (N * K))) := fun x =>
      takeD_eq_take (by rw [length_ginvW]; nlinarith)
    have hval : ginvGswW N K k (s 1) =
        takeD (k * (2 * k * (N * K))) (ginvW N K k (takeD (2 * k * (N * K)) (s 1))) ++
        (takeD (k * (2 * k * (N * K)))
          (ginvW N K k (takeD (2 * k * (N * K)) ((s 1).drop (2 * k * (N * K))))) ++
        takeD 0 ((s 1).drop (2 * k * (N * K) + 2 * k * (N * K)))) := by
      rw [hg, hg, takeD_eq_take hR, takeD_of_length' hd, ginvGswW_eq]
      simp [takeD]
    funext i
    fin_cases i <;> simp [gsS, gi0, gi1, gjJ, h6, h7, h8, h9, h10] <;>
      first | exact hval | exact hval.symm | (apply hb <;> decide) | (symm; apply hb <;> decide)
  all_goals first
    | (intro i hi; fin_cases i <;> simp [gsS, gi0, gi1, gjJ, hb, h8] at hi ⊢)
    | (simp [gsS, gi0, gi1, gjJ, hb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, length_ginvW]; try ring)

theorem ginvSpec_gsw (N K k : ℕ) :
    GinvSpec ginvGswP (lenA N K k 2) (2 * k * (2 * k * (N * K))) (ginvGswW N K k)
      (GPreGsw N K k) where
  noGrow := rfl
  wf := wf_of_wfB (by decide)
  pre_congr := by
    rintro s s' he ⟨h0, h8, h2, h3, h4, h5, h6, h7, h9, h10⟩
    refine ⟨fun i hi hi' => (he i (by omega)).symm.trans (h0 i hi hi'), ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · rw [← he 8 (by decide)]; exact h8
    · rw [← he 2 (by decide)]; exact h2
    · rw [← he 3 (by decide)]; exact h3
    · rw [← he 4 (by decide)]; exact h4
    · rw [← he 5 (by decide)]; exact h5
    · rw [← he 6 (by decide)]; exact h6
    · rw [← he 7 (by decide)]; exact h7
    · rw [← he 9 (by decide)]; exact h9
    · rw [← he 10 (by decide)]; exact h10
  run_eq := fun s hp h1 => run_ginvGswP s hp h1
  len := fun a _ => by
    rw [ginvGswW, length_concatN (K := N * K) fun _ _ => length_digitRW _ _ _ _]; ring

end Prog

end SigabaNeo.Tape
