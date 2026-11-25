import SigabaNeoStd.Lattices.ProgAlgo.SLPTape
import SigabaNeoStd.Lattices.ProgAlgo.Spec
import SigabaNeoStd.Lattices.Algo.SLPWords

/-!
# `EvalF` of a straight-line program on tapes

The BGG+ NAND of public keys `nandP` is a gate program (`stepSpec_nandP`) on rows of `2k` ring
words, so the evaluator `slpEvalP` runs `EvalF` (`slpPKW`) of any program: from the words of the
input public keys and the gadget row `gadW` (the value of the wire `1`), the store ends as the
words of every wire (`run_slpPK`), and the block of the wire `w` at its final position is
`slpPKW N K k bj p w` (`slpPKW_block`).
-/

namespace SigabaNeo.Tape

namespace Prog

open SigabaNeo.Lattices SigabaNeo.Lattices.Algo

variable {k : ℕ}

/-- The precondition of `nandP`: the templates `3 … 11` and blank scratch `12 … 64`. -/
def NandPre (N K k' : ℕ) (s : Store 65) : Prop :=
  (∀ i : Fin 65, 12 ≤ i.val → s i = []) ∧ (s 3).length = K ∧ (s 4).length = N ∧
    (s 5).length = N * K ∧ (s 6).length = k' ∧ (s 7).length = 2 * k' ∧ (s 8).length = 1 ∧
    (s 9).length = 2 * k' * N ∧ (s 10).length = 2 * k' * (N * K) ∧
    (s 11).length = 2 * k' * (2 * k' * (N * K))

theorem length_nandPKW (N K k' : ℕ) (a b : List Bool) :
    (nandPKW N K k' a b).length = 2 * k' * (N * K) := by
  unfold nandPKW matSubW
  rw [length_concatN (K := N * K) fun p hp => length_subRW N K
    (show (rget N K p (gadW N K k')).length = N * K from
      length_block (N := 1 * (2 * k')) (by rw [length_gadW]; ring) hp) _]
  ring

/-- **`nandP` is a gate program** for `nandPKW` on rows of `2k'` ring words. -/
theorem stepSpec_nandP (N K k' : ℕ) :
    StepSpec (m := 62) nandP (2 * k' * (N * K)) (nandPKW N K k') (NandPre N K k') where
  noGrow := noGrow_nandP
  wf := wf_nandP
  pre_upd := by
    intro s i hi w ⟨h0, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    have ne : ∀ j : Fin 65, 3 ≤ j.val → j ≠ i := fun j hj h => by subst h; omega
    refine ⟨fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne (ne j (by omega))]; exact h0 j hj
    all_goals rwa [Function.update_of_ne (ne _ (by decide))]
  run_eq := fun s ⟨h0, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ ha hb =>
    run_nandP s h0 h3 h4 h5 h6 h7 h8 h9 h10 h11 ha hb
  len := fun a b _ _ => length_nandPKW N K k' a b

/-- **`EvalF` on tapes**: the store ends as the words of the inputs, of `1` (the gadget row) and of
every gate of `p`. -/
theorem run_slpPK {ι : Type*} {N K k' : ℕ} {u : Fin 65 → Fin k} {v : Fin 15 → Fin k}
    (hpl : Placed (m := 62) u v) (s : Store k) (hclean : ∀ i : Fin 15, 5 ≤ i.val → s (v i) = [])
    (hPre : NandPre N K k' (s ∘ u)) {W : ℕ} (hV : (s (v 3)).length = 2 * k' * (N * K))
    (hW : (s (v 4)).length = W) {ins : List (List Bool)}
    (hins : ∀ x ∈ ins, x.length = 2 * k' * (N * K)) {n : ℕ} (hn : ins.length = n) {ix : ι → ℕ}
    (hix : ∀ i, ix i < n) (p : SLP ι) (hWg : n + p.length ≤ W) (padW : List Bool)
    (hpad : padW.length = p.length * (2 * k' * (N * K)))
    (hst : s (v 0) = padW ++ (ins ++ [gadW N K k']).flatten) (hgs : s (v 1) = gatesW ix n W p 0)
    (hpc : (s (v 2)).length = p.length) :
    run (slpEvalP u v nandP) s = Function.update (Function.update (Function.update s (v 0)
      ((ins ++ [gadW N K k'] ++
        SLP.values (fun i => ins.getD (ix i) []) (gadW N K k') (nandPKW N K k') p).flatten))
      (v 1) []) (v 2) [] :=
  run_slpEvalP hpl (stepSpec_nandP N K k') s hclean hPre hV hW hins (length_gadW N K k') hn hix p
    hWg padW hpad hst hgs hpc

/-- **The public key of a wire** is the block at its final position in the store. -/
theorem slpPKW_block {ι : Type*} (N K k' : ℕ) {ins : List (List Bool)} {n : ℕ}
    (hn : ins.length = n) {ix : ι → ℕ} (hix : ∀ i, ix i < n) (p : SLP ι) (w : Wire ι) :
    ∃ h : wireIx ix n p.length w <
        (ins ++ [gadW N K k'] ++
          SLP.values (fun i => ins.getD (ix i) []) (gadW N K k') (nandPKW N K k') p).length,
      (ins ++ [gadW N K k'] ++
          SLP.values (fun i => ins.getD (ix i) []) (gadW N K k') (nandPKW N K k') p)[
            wireIx ix n p.length w] =
        slpPKW N K k' (fun i => ins.getD (ix i) []) p w := by
  have hlen : (SLP.values (fun i => ins.getD (ix i) []) (gadW N K k') (nandPKW N K k') p).length =
      p.length := by rw [SLP.values, length_slpRun]; simp
  have := getElem_wireIx ix ins hn hix (gadW N K k')
    (SLP.values (fun i => ins.getD (ix i) []) (gadW N K k') (nandPKW N K k') p) w
  simp only [hlen] at this
  exact this

/-- **Time of `EvalF` on tapes**: at most `2919 · (L + 1) ^ 9` steps on words at most `L` long. -/
theorem timeBound_slpPK {N K k' : ℕ} (u : Fin 65 → Fin k) (v : Fin 15 → Fin k) (L : ℕ) :
    timeBound (slpEvalP u v nandP) L ≤ 2919 * (L + 1) ^ 9 := by
  have h := (timeBound_slpEvalP (u := u) (v := v) (stepSpec_nandP N K k') L).1
  have hC : tbC nandP = 2691 := rfl
  have hD : tbD nandP = 8 := rfl
  rwa [hC, hD] at h

end Prog

end SigabaNeo.Tape
