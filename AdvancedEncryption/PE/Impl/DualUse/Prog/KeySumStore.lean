import PE.Impl.DualUse.Prog.SimKeyStore
import SigabaNeo.Lib.Lattices.ProgAlgo.KeySum

/-!
# The key matrix and `W_f` from the stores of the evaluators, on tapes

`keySumP` (`SigabaNeo.Lib.Lattices.ProgAlgo.KeySum`) reads the terms of the key-matrix sum from
the final store of an SLP evaluator, at the unary positions of the output wires of `f̂`
(`fhatPos`, in the loop order, `posW`):

* `run_keySumP_pk`: on the store of `EvalF` (`run_slpPK`) for `f̂` it writes `keyMatrixW …`, hence
  `rowW (keyMatrix mpk (predOf 10 gs))` (`run_keySumP_keyMatrix`, by `keyMatrixW_eq`);
* `run_simKeyP_store`: `simKeyP` on the stores of the two simulations (`run_slpSim`) writes
  `simKeyStoreW …`, hence `colsW … (simKeyMat …)` (`run_simKeyP_mat`, by `simKeyStoreW_eq_mat`).
-/

namespace AdvancedEncryption.DualUse.Algo

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.Prog Matrix AdvancedEncryption.RingBTVW

variable {N K k : ℕ}

/-- **The positions of the output wires of `f̂`** in the final store of an evaluator, at the bits
`(c, i, j)` of a row. -/
def fhatPos (K : ℕ) (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k)) (gs : GateList)
    (ix : Fin nA × BI N k → ℕ) (n : ℕ) (c i j : ℕ) : ℕ :=
  if h : c < 2 * k ∧ i < k ∧ j < N then
    wireIx ix n (fhatProg K ordT ordO gs).1.length
      ((fhatProg K ordT ordO gs).2 (0, colE k ⟨c, h.1⟩, ⟨i, h.2.1⟩, ⟨j, h.2.2⟩))
  else 0

theorem fhatPos_le (K : ℕ) (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (gs : GateList) {ix : Fin nA × BI N k → ℕ} {n : ℕ} (hix : ∀ j, ix j < n) (c i j : ℕ) :
    fhatPos K ordT ordO gs ix n c i j ≤ n + (fhatProg K ordT ordO gs).1.length := by
  unfold fhatPos
  split_ifs
  · exact wireIx_le ix hix _ _
  · omega

/-- **The key matrix from the store of `EvalF`**: on the final store of `slpEvalP … nandP` for
`f̂` (`run_slpPK`) and the positions of its output wires, `keySumP` writes `keyMatrixW`. -/
theorem run_keySumP_pk (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (gs : GateList) {ins : List (List Bool)} (hins : ∀ x ∈ ins, x.length = 2 * k * (N * K))
    {n : ℕ} (hn : ins.length = n) {ix : Fin nA × BI N k → ℕ} (hix : ∀ j, ix j < n) {W : ℕ}
    (hW : n + (fhatProg K ordT ordO gs).1.length ≤ W) (r : Store 86)
    (ht : KTmpl N K k 1 W (2 * k * (N * K)) 0 r) (hb : ∀ t : Fin 86, 18 ≤ t.val → r t = [])
    (h1 : r 1 = (ins ++ [gadW N K k] ++ SLP.values (fun i => ins.getD (ix i) []) (gadW N K k)
      (nandPKW N K k) (fhatProg K ordT ordO gs).1).flatten)
    (h2 : r 2 = posW W N k (fhatPos K ordT ordO gs ix n)) :
    run keySumP r = Function.update r 0
      (keyMatrixW N K k ordT ordO gs (fun j => ins.getD (ix j) [])) := by
  rw [run_keySumP r ht hb _ (fun c _ i _ j _ => (fhatPos_le K ordT ordO gs hix c i j).trans hW) h2,
    keyMatrixW, keySumW_eq_keySumMW]
  congr 1
  apply keySumMW_congr
  intro c hc i hi j hj
  have hh : c < 2 * k ∧ i < k ∧ j < N := ⟨hc, hi, hj⟩
  rw [dite_eq_left_of_eq_true (eq_true hh), h1, fhatPos, dite_eq_left_of_eq_true (eq_true hh)]
  obtain ⟨hl, e⟩ := slpPKW_block N K k hn hix (fhatProg K ordT ordO gs).1
    ((fhatProg K ordT ordO gs).2 (0, colE k ⟨c, hh.1⟩, ⟨i, hh.2.1⟩, ⟨j, hh.2.2⟩))
  have hL := store_len hins hn hix (length_gadW N K k) (nandPKW N K k)
    (fun a b _ _ => length_nandPKW N K k a b) (fhatProg K ordT ordO gs).1
  rw [readW_flatten _ hL hl (by ring_nf; omega), e, List.drop_zero]
  apply List.take_of_length_le
  rw [← e]; exact (hL _ (List.getElem_mem hl)).le.trans (by ring_nf; omega)

/-- **The key matrix of a predicate from the store of `EvalF`**: with the words of the `B_j` as
inputs, `keySumP` writes the word of `keyMatrix mpk (predOf 10 gs)`. -/
theorem run_keySumP_keyMatrix (hk : 2 ^ K < 2 ^ k) {Wd Wt : Type*} [Fintype Wd] [Fintype Wt]
    (mpk : MPK (Sdw (N := N) hk) Wd Wt) (gs : GateList) {ins : List (List Bool)}
    (hins : ∀ x ∈ ins, x.length = 2 * k * (N * K)) {n : ℕ} (hn : ins.length = n)
    {ix : Fin nA × BI N k → ℕ} (hix : ∀ j, ix j < n)
    (hB : ∀ j, ins.getD (ix j) [] = rowW N K k (mpk.Bj j)) {W : ℕ}
    (hW : n + (fhatProg K (ordT₀ N k) (ordO₀ N k) gs).1.length ≤ W) (r : Store 86)
    (ht : KTmpl N K k 1 W (2 * k * (N * K)) 0 r) (hb : ∀ t : Fin 86, 18 ≤ t.val → r t = [])
    (h1 : r 1 = (ins ++ [gadW N K k] ++ SLP.values (fun i => ins.getD (ix i) []) (gadW N K k)
      (nandPKW N K k) (fhatProg K (ordT₀ N k) (ordO₀ N k) gs).1).flatten)
    (h2 : r 2 = posW W N k (fhatPos K (ordT₀ N k) (ordO₀ N k) gs ix n)) :
    run keySumP r = Function.update r 0 (rowW N K k (keyMatrix mpk (predOf 10 gs))) := by
  rw [run_keySumP_pk _ _ gs hins hn hix hW r ht hb h1 h2, funext hB, keyMatrixW_eq hk mpk gs]

/-- **`W_f` from the stores of the two simulations**: on the final stores of the simulation of `f̂`
(`storeT`, flattened, on tape `1`) and of the predicate's program (`storeG`, on tape `86`), with the
positions of the output wires of `f̂` (`posW`) and of the predicate's output wire (tape `87`),
`simKeyP` writes `simKeyStoreW`. -/
theorem run_simKeyP_store {d : ℕ} (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (gs : GateList) {insT : List (List Bool)}
    (hinsT : ∀ x ∈ insT, x.length = lenA N K k 1 + lenA N K k d + N * K) {nT : ℕ}
    (hnT : insT.length = nT) {ixT : Fin nA × BI N k → ℕ} (hixT : ∀ j, ixT j < nT)
    {insG : List (List Bool)} (hinsG : ∀ x ∈ insG, x.length = lenA N K k 2 + lenA N K k d + N * K)
    {nG : ℕ} (hnG : insG.length = nG) {ixG : Fin 10 → ℕ} (hixG : ∀ i, ixG i < nG) {W W' : ℕ}
    (hW : nT + (fhatProg K ordT ordO gs).1.length ≤ W)
    (hW' : wireIx ixG nG (predOf 10 gs).1.length (predOf 10 gs).2 ≤ W') (r : Store 94)
    (ht : KTmpl N K k d W (lenA N K k 1 + lenA N K k d + N * K) (lenA N K k 1) (r ∘ oKs))
    (hb : ∀ t : Fin 94, 18 ≤ t.val → t.val < 86 → r t = []) (hb' : ∀ t : Fin 94, 91 ≤ t.val → r t = [])
    (h1 : r 1 = (storeT N K k d ordT ordO gs insT ixT).flatten)
    (h2 : r 2 = posW W N k (fhatPos K ordT ordO gs ixT nT))
    (h86 : r 86 = (storeG N K k d gs insG ixG).flatten)
    (h87 : r 87 = unaryW W' (wireIx ixG nG (predOf 10 gs).1.length (predOf 10 gs).2))
    (h88 : (r 88).length = W') (h89 : (r 89).length = lenA N K k 2 + lenA N K k d + N * K)
    (h90 : (r 90).length = lenA N K k 2) :
    run simKeyP r = Function.update r 0
      (simKeyStoreW N K k d ordT ordO gs insT ixT nT insG ixG nG) := by
  have hgT : (gadW N K k).length = lenA N K k 1 := by rw [length_gadW, lenA]; ring
  have hgG : (gswGadW N K k).length = lenA N K k 2 := by
    rw [gswGadW_eq, List.length_append, List.length_append, length_gadW, length_zeroW,
      List.length_take, length_gadW, lenA, min_eq_left (Nat.mul_le_mul_right _ (by omega))]; ring
  have hoT : (simOneW N K k d (gadW N K k)).length = lenA N K k 1 + lenA N K k d + N * K := by
    rw [simOneW, length_jointW, hgT, length_zeroW, length_oneW]
  have hoG : (simOneW N K k d (gswGadW N K k)).length = lenA N K k 2 + lenA N K k d + N * K := by
    rw [simOneW, length_jointW, hgG, length_zeroW, length_oneW]
  have hLT := store_len hinsT hnT hixT hoT (simStepJW N K k 1 d (gadW N K k) (ginvW N K k))
    (fun a b _ _ => length_simStepJW (d := d) hgT _ a b)
    (fhatProg K ordT ordO gs).1
  have hLG := store_len hinsG hnG hixG hoG (simStepJW N K k 2 d (gswGadW N K k) (ginvGswW N K k))
    (fun a b _ _ => length_simStepJW (d := d) hgG _ a b)
    (predOf 10 gs).1
  rw [run_simKeyP r ht hb hb' _ (fun c _ i _ j _ => (fhatPos_le K ordT ordO gs hixT c i j).trans hW)
    h2 h88 h89 h90, simKeyStoreW]
  congr 2
  · apply keySumMW_congr
    intro c hc i hi j hj
    have hh : c < 2 * k ∧ i < k ∧ j < N := ⟨hc, hi, hj⟩
    rw [dite_eq_left_of_eq_true (eq_true hh), h1, fhatPos, dite_eq_left_of_eq_true (eq_true hh), storeT]
    have hl := wireIx_lt_store hnT hixT (fun j => insT.getD (ixT j) []) (simOneW N K k d (gadW N K k))
      (simStepJW N K k 1 d (gadW N K k) (ginvW N K k)) (fhatProg K ordT ordO gs).1
      ((fhatProg K ordT ordO gs).2 (0, colE k ⟨c, hh.1⟩, ⟨i, hh.2.1⟩, ⟨j, hh.2.2⟩))
    rw [readW_flatten _ hLT hl (Nat.le_add_right _ _), List.getD_eq_getElem _ _ hl]
    rfl
  · have hl := wireIx_lt_store hnG hixG (fun i => insG.getD (ixG i) [])
      (simOneW N K k d (gswGadW N K k)) (simStepJW N K k 2 d (gswGadW N K k) (ginvGswW N K k))
      (predOf 10 gs).1 (predOf 10 gs).2
    rw [h86, h87, takeD_of_length' (length_unaryW hW'), storeG,
      readW_flatten _ hLG hl (Nat.le_add_right _ _), List.getD_eq_getElem _ _ hl]
    rfl

/-- **The word of `W_f = simKeyMat …` from the stores of the two simulations** on tapes, at the
orders of `fhatSLP` (`simKeyStoreW_eq_mat`). -/
theorem run_simKeyP_mat (hk : 2 ^ K < 2 ^ k) {d : ℕ}
    (Rm : Fin nA → Matrix (Fin d) (RingBTVW.Col k) (DualUse.Rg N K)) (x : Fin nA → Bool)
    (Wm : Fin nA × BI N k → Matrix (Fin d) (RingBTVW.Col k) (DualUse.Rg N K))
    (Ψ : Fin nA → Matrix (Fin 2) (RingBTVW.Col k) (DualUse.Rg N K))
    (Bj : Fin nA × BI N k → Matrix (Fin 1) (RingBTVW.Col k) (DualUse.Rg N K)) (gs : GateList)
    {insT : List (List Bool)}
    (hinsT : ∀ x ∈ insT, x.length = lenA N K k 1 + lenA N K k d + N * K) {nT : ℕ}
    (hnT : insT.length = nT) {ixT : Fin nA × BI N k → ℕ} (hixT : ∀ j, ixT j < nT)
    (hinsT' : ∀ j, insT.getD (ixT j) [] = jointW (rowW N K k (Bj j), colsW N K k d (Wm j),
      psiBitsW N K k (fun i => colsW N K k 2 (Ψ i)) j))
    {insG : List (List Bool)} (hinsG : ∀ x ∈ insG, x.length = lenA N K k 2 + lenA N K k d + N * K)
    {nG : ℕ} (hnG : insG.length = nG) {ixG : Fin 10 → ℕ} (hixG : ∀ i, ixG i < nG)
    (hinsG' : ∀ i, insG.getD (ixG i) [] =
      jointW (colsW N K k 2 (Ψ i), colsW N K k d (Rm i), constW N K (bitW K (x i))))
    {W W' : ℕ} (hW : nT + (fhatProg K (ordT₀ N k) (ordO₀ N k) gs).1.length ≤ W)
    (hW' : wireIx ixG nG (predOf 10 gs).1.length (predOf 10 gs).2 ≤ W') (r : Store 94)
    (ht : KTmpl N K k d W (lenA N K k 1 + lenA N K k d + N * K) (lenA N K k 1) (r ∘ oKs))
    (hb : ∀ t : Fin 94, 18 ≤ t.val → t.val < 86 → r t = []) (hb' : ∀ t : Fin 94, 91 ≤ t.val → r t = [])
    (h1 : r 1 = (storeT N K k d (ordT₀ N k) (ordO₀ N k) gs insT ixT).flatten)
    (h2 : r 2 = posW W N k (fhatPos K (ordT₀ N k) (ordO₀ N k) gs ixT nT))
    (h86 : r 86 = (storeG N K k d gs insG ixG).flatten)
    (h87 : r 87 = unaryW W' (wireIx ixG nG (predOf 10 gs).1.length (predOf 10 gs).2))
    (h88 : (r 88).length = W') (h89 : (r 89).length = lenA N K k 2 + lenA N K k d + N * K)
    (h90 : (r 90).length = lenA N K k 2) :
    run simKeyP r = Function.update r 0
      (colsW N K k d (simKeyMat (S := Sdw (N := N) hk) Rm x Wm Ψ Bj (predOf 10 gs))) := by
  rw [run_simKeyP_store _ _ gs hinsT hnT hixT hinsG hnG hixG hW hW' r ht hb hb' h1 h2 h86 h87 h88
    h89 h90, simKeyStoreW_eq_mat hk Rm x Wm Ψ Bj gs hnT hixT hinsT' hnG hixG hinsG']

end AdvancedEncryption.DualUse.Algo
