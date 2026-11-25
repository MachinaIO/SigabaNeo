import PE.Impl.RingBTVW.Algo.SimKey
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

namespace AdvancedEncryption.RingBTVW.Algo

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.Prog Matrix AdvancedEncryption.RingBTVW.Fresh

variable {N K k : ℕ}

/-- The final store of the simulation of `f̂` (top-row gadget). -/
def storeT (N K k d : ℕ) (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (gs : GateList) (insT : List (List Bool)) (ixT : Fin nA × BI N k → ℕ) : List (List Bool) :=
  insT ++ [simOneW N K k d (gadW N K k)] ++
    SLP.values (fun j => insT.getD (ixT j) []) (simOneW N K k d (gadW N K k))
      (simStepJW N K k 1 d (gadW N K k) (ginvW N K k)) (fhatProg K ordT ordO gs).1

/-- The final store of the simulation of the predicate's program (Ring-GSW gadget). -/
def storeG (N K k d : ℕ) (gs : GateList) (insG : List (List Bool)) (ixG : Fin nA → ℕ) :
    List (List Bool) :=
  insG ++ [simOneW N K k d (gswGadW N K k)] ++
    SLP.values (fun i => insG.getD (ixG i) []) (simOneW N K k d (gswGadW N K k))
      (simStepJW N K k 2 d (gswGadW N K k) (ginvGswW N K k)) (predOf nA gs).1

/-- **`W_f` read from the two stores.** -/
def simKeyStoreW (N K k d : ℕ) (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (gs : GateList) (insT : List (List Bool)) (ixT : Fin nA × BI N k → ℕ) (nT : ℕ)
    (insG : List (List Bool)) (ixG : Fin nA → ℕ) (nG : ℕ) : List Bool :=
  matAddW N K (d * (2 * k))
    (keySumMW N K k d fun c i j =>
      if h : c < 2 * k ∧ i < k ∧ j < N then
        (splitJ (lenA N K k 1) (lenA N K k d) ((storeT N K k d ordT ordO gs insT ixT).getD
          (wireIx ixT nT (fhatProg K ordT ordO gs).1.length
            ((fhatProg K ordT ordO gs).2 (0, colE k ⟨c, h.1⟩, ⟨i, h.2.1⟩, ⟨j, h.2.2⟩))) [])).2.1
      else [])
    (splitJ (lenA N K k 2) (lenA N K k d) ((storeG N K k d gs insG ixG).getD
      (wireIx ixG nG (predOf nA gs).1.length (predOf nA gs).2) [])).2.1

theorem length_rowW' (B : Matrix (Fin 1) (Fin 2 × Fin k) (Rq N K)) :
    (rowW N K k B).length = lenA N K k 1 := length_matW _ _ _

theorem length_colsW' (m : ℕ) (M : Matrix (Fin m) (Fin 2 × Fin k) (Rq N K)) :
    (colsW N K k m M).length = lenA N K k m := length_matW _ _ _

/-- **The stores give `simKeyW`**, when the input entries are the joint words of the inputs. -/
theorem simKeyStoreW_eq {d : ℕ} (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (gs : GateList) (bjW wW : Fin nA × BI N k → List Bool) (ψW rmW : Fin nA → List Bool)
    (xs : Fin nA → Bool)
    (hb : ∀ j, (bjW j).length = lenA N K k 1) (hw : ∀ j, (wW j).length = lenA N K k d)
    (hψ : ∀ i, (ψW i).length = lenA N K k 2) (hr : ∀ i, (rmW i).length = lenA N K k d)
    {insT : List (List Bool)} {nT : ℕ} (hnT : insT.length = nT) {ixT : Fin nA × BI N k → ℕ}
    (hixT : ∀ j, ixT j < nT)
    (hinsT : ∀ j, insT.getD (ixT j) [] = jointW (bjW j, wW j, psiBitsW N K k ψW j))
    {insG : List (List Bool)} {nG : ℕ} (hnG : insG.length = nG) {ixG : Fin nA → ℕ}
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
      (fun i => constW N K (bitW K (xs i))) hψ hr hnG hixG hinsG (predOf nA gs).1 (predOf nA gs).2
    rw [storeG, List.getD_eq_getElem _ _ hl, e]

/-- **The word of `W_f` from the stores** of the two simulations on tapes, at the orders of
`fhatSLP` (`simKeyW_eq`). -/
theorem simKeyStoreW_eq_mat (hk : 2 ^ K < 2 ^ k) {d : ℕ}
    (Rm : Fin nA → Matrix (Fin d) (RingBTVW.Fresh.Col k) (RingBTVW.Rg N K)) (x : Fin nA → Bool)
    (W : Fin nA × BI N k → Matrix (Fin d) (RingBTVW.Fresh.Col k) (RingBTVW.Rg N K))
    (Ψ : Fin nA → Matrix (Fin 2) (RingBTVW.Fresh.Col k) (RingBTVW.Rg N K))
    (Bj : Fin nA × BI N k → Matrix (Fin 1) (RingBTVW.Fresh.Col k) (RingBTVW.Rg N K)) (gs : GateList)
    {insT : List (List Bool)} {nT : ℕ} (hnT : insT.length = nT) {ixT : Fin nA × BI N k → ℕ}
    (hixT : ∀ j, ixT j < nT)
    (hinsT : ∀ j, insT.getD (ixT j) [] = jointW (rowW N K k (Bj j), colsW N K k d (W j),
      psiBitsW N K k (fun i => colsW N K k 2 (Ψ i)) j))
    {insG : List (List Bool)} {nG : ℕ} (hnG : insG.length = nG) {ixG : Fin nA → ℕ}
    (hixG : ∀ i, ixG i < nG)
    (hinsG : ∀ i, insG.getD (ixG i) [] =
      jointW (colsW N K k 2 (Ψ i), colsW N K k d (Rm i), constW N K (bitW K (x i)))) :
    simKeyStoreW N K k d (ordT₀ N k) (ordO₀ N k) gs insT ixT nT insG ixG nG =
      colsW N K k d (simKeyMat (S := Sdw (N := N) hk) Rm x W Ψ Bj (predOf nA gs)) := by
  rw [simKeyStoreW_eq (ordT₀ N k) (ordO₀ N k) gs (fun j => rowW N K k (Bj j))
      (fun j => colsW N K k d (W j)) (fun i => colsW N K k 2 (Ψ i)) (fun i => colsW N K k d (Rm i))
      x (fun j => length_rowW' _) (fun j => length_colsW' _ _) (fun i => length_colsW' _ _)
      (fun i => length_colsW' _ _) hnT hixT hinsT hnG hixG hinsG,
    simKeyW_eq hk]

/-! ### For any predicate program

The same identities for a predicate given as a straight-line program `P` (with its output wire),
e.g. the unfolding `RP.toSLP` of a register program: `fhatProg K ordT ordO gs` is
`fhatProgP K ordT ordO (predOf nA gs)`. -/

/-- The program `f̂` of a predicate program, with the orders `ordT`, `ordO`. -/
def fhatProgP (K : ℕ) (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (P : SLP (Fin nA) × Wire (Fin nA)) : SLP (Fin nA × BI N k) × (BI N k → Wire (Fin nA × BI N k)) :=
  fhatSLPL ordT ordO (gvExp (2 ^ K)) (2 ^ K) P.1 P.2

theorem fhatProg_eq_P (K : ℕ) (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (gs : GateList) : fhatProg K ordT ordO gs = fhatProgP K ordT ordO (predOf nA gs) := rfl

/-- **`W_f` on words**, for a predicate program. -/
def simKeyWP (N K k d : ℕ) (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (P : SLP (Fin nA) × Wire (Fin nA)) (bjW wW : Fin nA × BI N k → List Bool)
    (ψW rmW : Fin nA → List Bool) (xs : Fin nA → Bool) : List Bool :=
  matAddW N K (d * (2 * k))
    (keySumMW N K k d fun c i j =>
      if h : c < 2 * k ∧ i < k ∧ j < N then
        (slpSimRunW N K k 1 d (gadW N K k) (ginvW N K k) bjW wW (psiBitsW N K k ψW)
          (fhatProgP K ordT ordO P).1
          ((fhatProgP K ordT ordO P).2 (0, colE k ⟨c, h.1⟩, ⟨i, h.2.1⟩, ⟨j, h.2.2⟩))).2.1
      else [])
    (slpSimRunW N K k 2 d (gswGadW N K k) (ginvGswW N K k) ψW rmW
      (fun i => constW N K (bitW K (xs i))) P.1 P.2).2.1

/-- **`simKeyWP` computes `W_f`** at the orders of `fhatSLP`. -/
theorem simKeyWP_eq (hk : 2 ^ K < 2 ^ k) {d : ℕ}
    (Rm : Fin nA → Matrix (Fin d) (RingBTVW.Fresh.Col k) (RingBTVW.Rg N K)) (x : Fin nA → Bool)
    (W : Fin nA × BI N k → Matrix (Fin d) (RingBTVW.Fresh.Col k) (RingBTVW.Rg N K))
    (Ψ : Fin nA → Matrix (Fin 2) (RingBTVW.Fresh.Col k) (RingBTVW.Rg N K))
    (Bj : Fin nA × BI N k → Matrix (Fin 1) (RingBTVW.Fresh.Col k) (RingBTVW.Rg N K))
    (P : SLP (Fin nA) × Wire (Fin nA)) :
    simKeyWP N K k d (ordT₀ N k) (ordO₀ N k) P (fun j => rowW N K k (Bj j))
      (fun j => colsW N K k d (W j)) (fun i => colsW N K k 2 (Ψ i)) (fun i => colsW N K k d (Rm i))
      x =
      colsW N K k d (simKeyMat (S := Sdw (N := N) hk) Rm x W Ψ Bj P) := by
  rw [simKeyWP, psiBitsW_enc hk]
  have h2 : (slpSimRunW N K k 2 d (gswGadW N K k) (ginvGswW N K k) (fun i => colsW N K k 2 (Ψ i))
      (fun i => colsW N K k d (Rm i)) (fun i => constW N K (bitW K (x i))) P.1 P.2).2.1 =
      colsW N K k d (evalSim (Sdw (N := N) hk).Γ Ψ (fun i => bitR (R := RingBTVW.Rg N K) (x i)) Rm
        ((Sdw (N := N) hk).circ P)) := by
    have hx : (fun i => constW N K (bitW K (x i))) =
        fun i => (ringEnc N K).enc (bitR (R := RingBTVW.Rg N K) (x i)) := by
      funext i; exact (enc_bitR (x i)).symm
    rw [hx]
    exact (slpSim_words (gswGadgetW hk.le) Ψ Rm _ _ _).trans
      (congrArg _ (evalSim_circuit (gswB N K k hk.le) Ψ _ Rm _ _).symm)
  rw [h2]
  have h1 : keySumMW N K k d (fun c i j =>
      if h : c < 2 * k ∧ i < k ∧ j < N then
        (slpSimRunW N K k 1 d (gadW N K k) (ginvW N K k) (fun j => rowW N K k (Bj j))
          (fun j => colsW N K k d (W j))
          (fun j => (ringEnc N K).enc (bitsOf (Sdw (N := N) hk) Ψ j))
          (fhatProgP K (ordT₀ N k) (ordO₀ N k) P).1
          ((fhatProgP K (ordT₀ N k) (ordO₀ N k) P).2 (0, colE k ⟨c, h.1⟩, ⟨i, h.2.1⟩, ⟨j, h.2.2⟩))).2.1
      else []) =
      colsW N K k d (∑ b, slpSim (Sdw (N := N) hk).Γ₁ Bj W (bitsOf (Sdw (N := N) hk) Ψ)
        ((Sdw (N := N) hk).fhat P).1 (((Sdw (N := N) hk).fhat P).2 b) *
        (Sdw (N := N) hk).Γ₁.ginv ((Sdw (N := N) hk).rowBits.V b)) := by
    refine keySumMW_enc hk.le
      (fun b => slpSim (topBin N K k hk.le) Bj W (bitsOf (Sdw (N := N) hk) Ψ)
        ((Sdw (N := N) hk).fhat P).1 (((Sdw (N := N) hk).fhat P).2 b))
      _ ?_
    intro c i j
    rw [dite_eq_left_of_eq_true (eq_true ⟨c.isLt, i.isLt, j.isLt⟩), fhatProgP, ← fhatSLP_eq_L hk]
    exact slpSim_words (topGadgetW hk.le) Bj W _ _ _
  refine (congrArg (fun z => matAddW N K (d * (2 * k)) z _) h1).trans ?_
  rw [colsW, colsW, matAddW_enc, colsW]
  rfl

/-- The final store of the simulation of `f̂`, for a predicate program. -/
def storeTP (N K k d : ℕ) (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (P : SLP (Fin nA) × Wire (Fin nA)) (insT : List (List Bool)) (ixT : Fin nA × BI N k → ℕ) :
    List (List Bool) :=
  insT ++ [simOneW N K k d (gadW N K k)] ++
    SLP.values (fun j => insT.getD (ixT j) []) (simOneW N K k d (gadW N K k))
      (simStepJW N K k 1 d (gadW N K k) (ginvW N K k)) (fhatProgP K ordT ordO P).1

/-- The final store of the simulation of a predicate program. -/
def storeGP (N K k d : ℕ) (P : SLP (Fin nA) × Wire (Fin nA)) (insG : List (List Bool))
    (ixG : Fin nA → ℕ) : List (List Bool) :=
  insG ++ [simOneW N K k d (gswGadW N K k)] ++
    SLP.values (fun i => insG.getD (ixG i) []) (simOneW N K k d (gswGadW N K k))
      (simStepJW N K k 2 d (gswGadW N K k) (ginvGswW N K k)) P.1

theorem storeT_eq_P (N K k d : ℕ) (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (gs : GateList) (insT : List (List Bool)) (ixT : Fin nA × BI N k → ℕ) :
    storeT N K k d ordT ordO gs insT ixT = storeTP N K k d ordT ordO (predOf nA gs) insT ixT := rfl

theorem storeG_eq_P (N K k d : ℕ) (gs : GateList) (insG : List (List Bool)) (ixG : Fin nA → ℕ) :
    storeG N K k d gs insG ixG = storeGP N K k d (predOf nA gs) insG ixG := rfl

/-- **`W_f` read from the two stores**, for a predicate program. -/
def simKeyStoreWP (N K k d : ℕ) (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (P : SLP (Fin nA) × Wire (Fin nA)) (insT : List (List Bool)) (ixT : Fin nA × BI N k → ℕ)
    (nT : ℕ) (insG : List (List Bool)) (ixG : Fin nA → ℕ) (nG : ℕ) : List Bool :=
  matAddW N K (d * (2 * k))
    (keySumMW N K k d fun c i j =>
      if h : c < 2 * k ∧ i < k ∧ j < N then
        (splitJ (lenA N K k 1) (lenA N K k d) ((storeTP N K k d ordT ordO P insT ixT).getD
          (wireIx ixT nT (fhatProgP K ordT ordO P).1.length
            ((fhatProgP K ordT ordO P).2 (0, colE k ⟨c, h.1⟩, ⟨i, h.2.1⟩, ⟨j, h.2.2⟩))) [])).2.1
      else [])
    (splitJ (lenA N K k 2) (lenA N K k d) ((storeGP N K k d P insG ixG).getD
      (wireIx ixG nG P.1.length P.2) [])).2.1

/-- **The stores give `simKeyWP`**, when the input entries are the joint words of the inputs. -/
theorem simKeyStoreWP_eq {d : ℕ} (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (P : SLP (Fin nA) × Wire (Fin nA)) (bjW wW : Fin nA × BI N k → List Bool)
    (ψW rmW : Fin nA → List Bool) (xs : Fin nA → Bool)
    (hb : ∀ j, (bjW j).length = lenA N K k 1) (hw : ∀ j, (wW j).length = lenA N K k d)
    (hψ : ∀ i, (ψW i).length = lenA N K k 2) (hr : ∀ i, (rmW i).length = lenA N K k d)
    {insT : List (List Bool)} {nT : ℕ} (hnT : insT.length = nT) {ixT : Fin nA × BI N k → ℕ}
    (hixT : ∀ j, ixT j < nT)
    (hinsT : ∀ j, insT.getD (ixT j) [] = jointW (bjW j, wW j, psiBitsW N K k ψW j))
    {insG : List (List Bool)} {nG : ℕ} (hnG : insG.length = nG) {ixG : Fin nA → ℕ}
    (hixG : ∀ i, ixG i < nG)
    (hinsG : ∀ i, insG.getD (ixG i) [] = jointW (ψW i, rmW i, constW N K (bitW K (xs i)))) :
    simKeyStoreWP N K k d ordT ordO P insT ixT nT insG ixG nG =
      simKeyWP N K k d ordT ordO P bjW wW ψW rmW xs := by
  have hgT : (gadW N K k).length = lenA N K k 1 := by rw [length_gadW, lenA]; ring
  have hgG : (gswGadW N K k).length = lenA N K k 2 := by
    rw [gswGadW_eq, List.length_append, List.length_append, length_gadW, length_zeroW,
      List.length_take, length_gadW, lenA, min_eq_left (Nat.mul_le_mul_right _ (by omega))]; ring
  unfold simKeyStoreWP simKeyWP
  congr 1
  · congr 1
    funext c i j
    split_ifs with h
    · obtain ⟨hl, e⟩ := simValues_short (d := d) hgT (ginvW N K k) bjW wW (psiBitsW N K k ψW) hb hw
        hnT hixT hinsT (fhatProgP K ordT ordO P).1
        ((fhatProgP K ordT ordO P).2 (0, colE k ⟨c, h.1⟩, ⟨i, h.2.1⟩, ⟨j, h.2.2⟩))
      rw [storeTP, List.getD_eq_getElem _ _ hl, e]
    · rfl
  · obtain ⟨hl, e⟩ := simValues_short (d := d) hgG (ginvGswW N K k) ψW rmW
      (fun i => constW N K (bitW K (xs i))) hψ hr hnG hixG hinsG P.1 P.2
    rw [storeGP, List.getD_eq_getElem _ _ hl, e]

/-- **The word of `W_f` from the stores**, for a predicate program. -/
theorem simKeyStoreWP_eq_mat (hk : 2 ^ K < 2 ^ k) {d : ℕ}
    (Rm : Fin nA → Matrix (Fin d) (RingBTVW.Fresh.Col k) (RingBTVW.Rg N K)) (x : Fin nA → Bool)
    (W : Fin nA × BI N k → Matrix (Fin d) (RingBTVW.Fresh.Col k) (RingBTVW.Rg N K))
    (Ψ : Fin nA → Matrix (Fin 2) (RingBTVW.Fresh.Col k) (RingBTVW.Rg N K))
    (Bj : Fin nA × BI N k → Matrix (Fin 1) (RingBTVW.Fresh.Col k) (RingBTVW.Rg N K))
    (P : SLP (Fin nA) × Wire (Fin nA))
    {insT : List (List Bool)} {nT : ℕ} (hnT : insT.length = nT) {ixT : Fin nA × BI N k → ℕ}
    (hixT : ∀ j, ixT j < nT)
    (hinsT : ∀ j, insT.getD (ixT j) [] = jointW (rowW N K k (Bj j), colsW N K k d (W j),
      psiBitsW N K k (fun i => colsW N K k 2 (Ψ i)) j))
    {insG : List (List Bool)} {nG : ℕ} (hnG : insG.length = nG) {ixG : Fin nA → ℕ}
    (hixG : ∀ i, ixG i < nG)
    (hinsG : ∀ i, insG.getD (ixG i) [] =
      jointW (colsW N K k 2 (Ψ i), colsW N K k d (Rm i), constW N K (bitW K (x i)))) :
    simKeyStoreWP N K k d (ordT₀ N k) (ordO₀ N k) P insT ixT nT insG ixG nG =
      colsW N K k d (simKeyMat (S := Sdw (N := N) hk) Rm x W Ψ Bj P) := by
  rw [simKeyStoreWP_eq (ordT₀ N k) (ordO₀ N k) P (fun j => rowW N K k (Bj j))
      (fun j => colsW N K k d (W j)) (fun i => colsW N K k 2 (Ψ i)) (fun i => colsW N K k d (Rm i))
      x (fun j => length_rowW' _) (fun j => length_colsW' _ _) (fun i => length_colsW' _ _)
      (fun i => length_colsW' _ _) hnT hixT hinsT hnG hixG hinsG,
    simKeyWP_eq hk]

end AdvancedEncryption.RingBTVW.Algo
