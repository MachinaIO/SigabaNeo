import PE.Impl.DualUse.Algo.SimKey
import SigabaNeo.Lib.Lattices.ProgAlgo.SimSLP

/-!
# `W_f` from the stores of the two simulations on tapes

The two evaluators `slpEvalP u v (simStepP ginvTopP)` (on `f̂`, inputs `(B_j, W_j, ψ_j)`) and
`slpEvalP u' v' (simStepP ginvGswP)` (on the predicate's program, inputs `(Ψᵢ, Rᵢ, xᵢ)`) leave their
stores as `storeT`, `storeG` (`run_slpSim`). `simKeyStoreW` reads the short matrices `W_b` of the
output wires of `f̂` and `R_f` of the predicate's output wire from these stores (the middle part of
the joint word at the wire's final position, `wireIx`) and sums as `simKeyW`.

`simKeyStoreW_eq`: it is `simKeyW`; `simKeyStoreW_eq_mat`: with the words of the matrices, it is the
word of `W_f = simKeyMat …` (`simKeyW_eq`).
-/

namespace AdvancedEncryption.DualUse.Algo

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.Prog Matrix AdvancedEncryption.RingBTVW

variable {N K k : ℕ}

/-- The final store of the simulation of `f̂` (top-row gadget). -/
def storeT (N K k d : ℕ) (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (gs : GateList) (insT : List (List Bool)) (ixT : Fin 10 × BI N k → ℕ) : List (List Bool) :=
  insT ++ [simOneW N K k d (gadW N K k)] ++
    SLP.values (fun j => insT.getD (ixT j) []) (simOneW N K k d (gadW N K k))
      (simStepJW N K k 1 d (gadW N K k) (ginvW N K k)) (fhatProg K ordT ordO gs).1

/-- The final store of the simulation of the predicate's program (Ring-GSW gadget). -/
def storeG (N K k d : ℕ) (gs : GateList) (insG : List (List Bool)) (ixG : Fin 10 → ℕ) :
    List (List Bool) :=
  insG ++ [simOneW N K k d (gswGadW N K k)] ++
    SLP.values (fun i => insG.getD (ixG i) []) (simOneW N K k d (gswGadW N K k))
      (simStepJW N K k 2 d (gswGadW N K k) (ginvGswW N K k)) (predOf 10 gs).1

/-- **`W_f` read from the two stores.** -/
def simKeyStoreW (N K k d : ℕ) (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (gs : GateList) (insT : List (List Bool)) (ixT : Fin 10 × BI N k → ℕ) (nT : ℕ)
    (insG : List (List Bool)) (ixG : Fin 10 → ℕ) (nG : ℕ) : List Bool :=
  matAddW N K (d * (2 * k))
    (keySumMW N K k d fun c i j =>
      if h : c < 2 * k ∧ i < k ∧ j < N then
        (splitJ (lenA N K k 1) (lenA N K k d) ((storeT N K k d ordT ordO gs insT ixT).getD
          (wireIx ixT nT (fhatProg K ordT ordO gs).1.length
            ((fhatProg K ordT ordO gs).2 (0, colE k ⟨c, h.1⟩, ⟨i, h.2.1⟩, ⟨j, h.2.2⟩))) [])).2.1
      else [])
    (splitJ (lenA N K k 2) (lenA N K k d) ((storeG N K k d gs insG ixG).getD
      (wireIx ixG nG (predOf 10 gs).1.length (predOf 10 gs).2) [])).2.1

theorem length_rowW' (B : Matrix (Fin 1) (Fin 2 × Fin k) (Rq N K)) :
    (rowW N K k B).length = lenA N K k 1 := length_matW _ _ _

theorem length_colsW' (m : ℕ) (M : Matrix (Fin m) (Fin 2 × Fin k) (Rq N K)) :
    (colsW N K k m M).length = lenA N K k m := length_matW _ _ _

/-- **The stores give `simKeyW`**, when the input entries are the joint words of the inputs. -/
theorem simKeyStoreW_eq {d : ℕ} (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (gs : GateList) (bjW wW : Fin 10 × BI N k → List Bool) (ψW rmW : Fin 10 → List Bool)
    (xs : Fin 10 → Bool)
    (hb : ∀ j, (bjW j).length = lenA N K k 1) (hw : ∀ j, (wW j).length = lenA N K k d)
    (hψ : ∀ i, (ψW i).length = lenA N K k 2) (hr : ∀ i, (rmW i).length = lenA N K k d)
    {insT : List (List Bool)} {nT : ℕ} (hnT : insT.length = nT) {ixT : Fin 10 × BI N k → ℕ}
    (hixT : ∀ j, ixT j < nT)
    (hinsT : ∀ j, insT.getD (ixT j) [] = jointW (bjW j, wW j, psiBitsW N K k ψW j))
    {insG : List (List Bool)} {nG : ℕ} (hnG : insG.length = nG) {ixG : Fin 10 → ℕ}
    (hixG : ∀ i, ixG i < nG)
    (hinsG : ∀ i, insG.getD (ixG i) [] = jointW (ψW i, rmW i, constW N K (bitW K (xs i)))) :
    simKeyStoreW N K k d ordT ordO gs insT ixT nT insG ixG nG =
      simKeyW N K k d ordT ordO gs bjW wW ψW rmW xs := by
  have hgT : (gadW N K k).length = lenA N K k 1 := by rw [length_gadW, lenA]; ring
  have hgG : (gswGadW N K k).length = lenA N K k 2 := by
    rw [gswGadW_eq, List.length_append, List.length_append, length_gadW, length_zeroW,
      List.length_take, length_gadW, lenA, min_eq_left (Nat.mul_le_mul_right _ (by omega))]; ring
  unfold simKeyStoreW simKeyW
  congr 1
  · congr 1
    funext c i j
    split_ifs with h
    · obtain ⟨hl, e⟩ := simValues_short (d := d) hgT (ginvW N K k) bjW wW (psiBitsW N K k ψW) hb hw
        hnT hixT hinsT (fhatProg K ordT ordO gs).1
        ((fhatProg K ordT ordO gs).2 (0, colE k ⟨c, h.1⟩, ⟨i, h.2.1⟩, ⟨j, h.2.2⟩))
      rw [storeT, List.getD_eq_getElem _ _ hl, e]
    · rfl
  · obtain ⟨hl, e⟩ := simValues_short (d := d) hgG (ginvGswW N K k) ψW rmW
      (fun i => constW N K (bitW K (xs i))) hψ hr hnG hixG hinsG (predOf 10 gs).1 (predOf 10 gs).2
    rw [storeG, List.getD_eq_getElem _ _ hl, e]

/-- **The word of `W_f` from the stores** of the two simulations on tapes, at the orders of
`fhatSLP` (`simKeyW_eq`). -/
theorem simKeyStoreW_eq_mat (hk : 2 ^ K < 2 ^ k) {d : ℕ}
    (Rm : Fin 10 → Matrix (Fin d) (RingBTVW.Col k) (DualUse.Rg N K)) (x : Fin 10 → Bool)
    (W : Fin 10 × BI N k → Matrix (Fin d) (RingBTVW.Col k) (DualUse.Rg N K))
    (Ψ : Fin 10 → Matrix (Fin 2) (RingBTVW.Col k) (DualUse.Rg N K))
    (Bj : Fin 10 × BI N k → Matrix (Fin 1) (RingBTVW.Col k) (DualUse.Rg N K)) (gs : GateList)
    {insT : List (List Bool)} {nT : ℕ} (hnT : insT.length = nT) {ixT : Fin 10 × BI N k → ℕ}
    (hixT : ∀ j, ixT j < nT)
    (hinsT : ∀ j, insT.getD (ixT j) [] = jointW (rowW N K k (Bj j), colsW N K k d (W j),
      psiBitsW N K k (fun i => colsW N K k 2 (Ψ i)) j))
    {insG : List (List Bool)} {nG : ℕ} (hnG : insG.length = nG) {ixG : Fin 10 → ℕ}
    (hixG : ∀ i, ixG i < nG)
    (hinsG : ∀ i, insG.getD (ixG i) [] =
      jointW (colsW N K k 2 (Ψ i), colsW N K k d (Rm i), constW N K (bitW K (x i)))) :
    simKeyStoreW N K k d (ordT₀ N k) (ordO₀ N k) gs insT ixT nT insG ixG nG =
      colsW N K k d (simKeyMat (S := Sdw (N := N) hk) Rm x W Ψ Bj (predOf 10 gs)) := by
  rw [simKeyStoreW_eq (ordT₀ N k) (ordO₀ N k) gs (fun j => rowW N K k (Bj j))
      (fun j => colsW N K k d (W j)) (fun i => colsW N K k 2 (Ψ i)) (fun i => colsW N K k d (Rm i))
      x (fun j => length_rowW' _) (fun j => length_colsW' _ _) (fun i => length_colsW' _ _)
      (fun i => length_colsW' _ _) hnT hixT hinsT hnG hixG hinsG,
    simKeyW_eq hk]

end AdvancedEncryption.DualUse.Algo
