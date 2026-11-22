import SigabaNeo.Lib.Lattices.ProgAlgo.SimStep

/-!
# The simulation of a straight-line program on tapes

`simStepP G` is a gate program (`stepSpec_simStepP`) for the step of the simulation on joint words
`simStepJW`, so the evaluator `slpEvalP` runs the simulation `slpSimRunW` of any program, for both
binary gadgets:

* the top-row gadget (`r = 1`, `gad = gadW`, `G = ginvTopP`): the run of `f̂` on `(B_j, W_j, ψ_j)`;
* the Ring-GSW gadget (`r = 2`, `gad = gswGadW`, `G = ginvGswP`): the run of the predicate's
  program on `(Ψᵢ, Rᵢ, xᵢ)`.

`run_slpSim`: the store ends as the joint words of the inputs, of `1` (`simOneW`) and of every gate;
the entry of a wire at its final position is the joint word of `slpSimRunW … w`
(`simValues_block`, `SimJoint`), whose middle part is the short matrix (`simValues_short`).
`timeBound_slpSim`: the time from the syntactic constants.
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices SigabaNeo.Lattices.Algo

namespace Prog

open scoped Prog

variable {k : ℕ}

theorem noGrowB_simPre : simPre.noGrowB = true := rfl
theorem noGrowB_simPost : simPost.noGrowB = true := rfl
theorem wf_simPre : simPre.WF := wf_of_wfB (by decide)
theorem wf_simPost : simPost.WF := wf_of_wfB (by decide)

theorem three_le_vG : ∀ j : Fin 48, 3 ≤ (vG j).val := by decide

/-- **`simStepP G` is a gate program** for the simulation step on joint words. -/
theorem stepSpec_simStepP {G : Prog 48} {N K k' r d : ℕ} {ginv : List Bool → List Bool}
    {GPre : Store 48 → Prop}
    (hG : GinvSpec G (lenA N K k' r) (2 * k' * (2 * k' * (N * K))) ginv GPre) {gad : List Bool}
    (hg : gad.length = lenA N K k' r) :
    StepSpec (m := 129) (simStepP G) (lenA N K k' r + lenA N K k' d + N * K)
      (simStepJW N K k' r d gad ginv) (SimPre N K k' r d gad GPre) where
  noGrow := by
    have h := NoGrow.map vG hG.noGrow
    simp only [NoGrow, simStepP, noGrowB, Bool.and_eq_true] at h ⊢
    exact ⟨noGrowB_simPre, h, noGrowB_simPost⟩
  wf := ⟨wf_simPre, WF.map vG_inj hG.wf, wf_simPost⟩
  pre_upd := by
    intro s i hi w hp
    have hne : ∀ j : Fin 132, 3 ≤ j.val → Function.update s i w j = s j := fun j hj =>
      Function.update_of_ne (fun h => by subst h; omega) _ _
    exact
      { blank := fun j h h' => (hne j (by omega)).trans (hp.blank j h h')
        h3 := by rw [hne 3 (by decide)]; exact hp.h3
        h4 := by rw [hne 4 (by decide)]; exact hp.h4
        h5 := by rw [hne 5 (by decide)]; exact hp.h5
        h6 := by rw [hne 6 (by decide)]; exact hp.h6
        h7 := by rw [hne 7 (by decide)]; exact hp.h7
        h8 := by rw [hne 8 (by decide)]; exact hp.h8
        h9 := by rw [hne 9 (by decide)]; exact hp.h9
        h10 := by rw [hne 10 (by decide)]; exact hp.h10
        h11 := by rw [hne 11 (by decide)]; exact hp.h11
        h12 := by rw [hne 12 (by decide)]; exact hp.h12
        h13 := by rw [hne 13 (by decide)]; exact hp.h13
        h14 := by rw [hne 14 (by decide)]; exact hp.h14
        h15 := by rw [hne 15 (by decide)]; exact hp.h15
        h16 := by rw [hne 16 (by decide)]; exact hp.h16
        h17 := by rw [hne 17 (by decide)]; exact hp.h17
        h19 := by rw [hne 19 (by decide)]; exact hp.h19
        h20 := by rw [hne 20 (by decide)]; exact hp.h20
        h21 := by rw [hne 21 (by decide)]; exact hp.h21
        g := hG.pre_congr _ _ (fun j _ => (hne (vG j) (three_le_vG j)).symm) hp.g }
  run_eq := fun s hp h1 h2 => run_simStepP hG hg s hp h1 h2
  len := fun a b _ _ => length_simStepJW hg ginv a b

/-- **The simulation on tapes**: from the joint words `ins` of the inputs and of `1`
(`simOneW`), the store ends as the joint words of the inputs, of `1` and of every gate of `p`. -/
theorem run_slpSim {ι : Type*} {G : Prog 48} {N K k' r d : ℕ} {ginv : List Bool → List Bool}
    {GPre : Store 48 → Prop}
    (hG : GinvSpec G (lenA N K k' r) (2 * k' * (2 * k' * (N * K))) ginv GPre) {gad : List Bool}
    (hg : gad.length = lenA N K k' r) {u : Fin 132 → Fin k} {v : Fin 15 → Fin k}
    (hpl : Placed (m := 129) u v) (s : Store k) (hclean : ∀ i : Fin 15, 5 ≤ i.val → s (v i) = [])
    (hPre : SimPre N K k' r d gad GPre (s ∘ u)) {W : ℕ}
    (hV : (s (v 3)).length = lenA N K k' r + lenA N K k' d + N * K)
    (hW : (s (v 4)).length = W) {ins : List (List Bool)}
    (hins : ∀ x ∈ ins, x.length = lenA N K k' r + lenA N K k' d + N * K) {n : ℕ}
    (hn : ins.length = n) {ix : ι → ℕ} (hix : ∀ i, ix i < n) (p : SLP ι) (hWg : n + p.length ≤ W)
    (padW : List Bool) (hpad : padW.length = p.length * (lenA N K k' r + lenA N K k' d + N * K))
    (hst : s (v 0) = padW ++ (ins ++ [simOneW N K k' d gad]).flatten)
    (hgs : s (v 1) = gatesW ix n W p 0) (hpc : (s (v 2)).length = p.length) :
    run (slpEvalP u v (simStepP G)) s = Function.update (Function.update (Function.update s (v 0)
      ((ins ++ [simOneW N K k' d gad] ++
        SLP.values (fun i => ins.getD (ix i) []) (simOneW N K k' d gad)
          (simStepJW N K k' r d gad ginv) p).flatten)) (v 1) []) (v 2) [] := by
  have hone : (simOneW N K k' d gad).length = lenA N K k' r + lenA N K k' d + N * K := by
    rw [simOneW, length_jointW, hg, length_zeroW, length_oneW]
  exact run_slpEvalP hpl (stepSpec_simStepP (d := d) hG hg) s hclean hPre hV hW hins hone hn hix
    p hWg padW hpad hst hgs hpc

/-- **Time of the simulation on tapes**, from the syntactic constants of `G`. -/
theorem timeBound_slpSim {G : Prog 48} {N K k' r d : ℕ} {ginv : List Bool → List Bool}
    {GPre : Store 48 → Prop}
    (hG : GinvSpec G (lenA N K k' r) (2 * k' * (2 * k' * (N * K))) ginv GPre) {gad : List Bool}
    (hg : gad.length = lenA N K k' r) (u : Fin 132 → Fin k) (v : Fin 15 → Fin k) (L : ℕ) :
    timeBound (slpEvalP u v (simStepP G)) L ≤
      (228 + (tbC simPre + (tbC G + tbC simPost))) *
        (L + 1) ^ (max 3 (max (tbD simPre) (max (tbD G) (tbD simPost))) + 1) := by
  have h := (timeBound_slpEvalP (u := u) (v := v) (stepSpec_simStepP (d := d) hG hg) L).1
  simpa only [simStepP, tbC, tbD, tbC_map, tbD_map] using h

/-! ### The two gadgets -/

/-- The top-row gadget: the run of a program on `(B_j, W_j, ψ_j)` words (`r = 1`). -/
theorem stepSpec_simTop (N K k' d : ℕ) :
    StepSpec (m := 129) (simStepP ginvTopP) (lenA N K k' 1 + lenA N K k' d + N * K)
      (simStepJW N K k' 1 d (gadW N K k') (ginvW N K k'))
      (SimPre N K k' 1 d (gadW N K k') (GPreTop N K k')) :=
  stepSpec_simStepP (ginvSpec_top N K k') (by rw [length_gadW, lenA]; ring)

/-- The Ring-GSW gadget: the run of a program on `(Ψᵢ, Rᵢ, xᵢ)` words (`r = 2`). -/
theorem stepSpec_simGsw (N K k' d : ℕ) :
    StepSpec (m := 129) (simStepP ginvGswP) (lenA N K k' 2 + lenA N K k' d + N * K)
      (simStepJW N K k' 2 d (gswGadW N K k') (ginvGswW N K k'))
      (SimPre N K k' 2 d (gswGadW N K k') (GPreGsw N K k')) :=
  stepSpec_simStepP (ginvSpec_gsw N K k')
    (by rw [gswGadW_eq, List.length_append, List.length_append, length_gadW, length_zeroW,
      List.length_take, length_gadW, lenA]
        rw [min_eq_left (Nat.mul_le_mul_right _ (by omega))]; ring)

end Prog

end SigabaNeo.Tape
