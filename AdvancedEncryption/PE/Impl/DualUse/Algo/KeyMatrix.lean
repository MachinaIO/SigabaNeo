import PE.Impl.DualUse.Codec
import SigabaNeo.Lib.Lattices.Algo.SLPWords
import SigabaNeo.Lib.Lattices.Algo.FhatLoop

/-!
# The key matrix of a predicate, on words

For a gate list `gs` (`predOf 10 gs`, the predicates of `KeyGen`) and the words of the public keys
`B_j`, `keyMatrixW` computes the word of `B_f̂ = keyMatrix mpk (predOf 10 gs)` by explicit
first-order loops:

1. generate the program `f̂` with `fhatSLPL` (the compiler of `fhatSLP` restated with the orders of
   its NAND blocks as parameters, `SigabaNeo.Lib.Lattices.Algo.FhatLoop`);
2. run it on the words of the `B_j` with the BGG+ NAND on words (`slpPKW`);
3. sum `PK_b · G̲⁻¹(V_b)` over the bits `b` of a row (`keySumW`).

`keyMatrixW_eq`: at the orders `ordT₀`, `ordO₀` of `fhatSLP` this is the word `rowW` of
`keyMatrix mpk (predOf 10 gs)`; `matEnc_row` identifies `rowW` with the codec's encoding of rows
(`matEnc (Fin 1) (Col k)`), so the word of each `B_j` is the block of the public key's word.

Step count: `keyMatrixSteps` with `g` the number of gates of `f̂`.
-/

namespace AdvancedEncryption.DualUse.Algo

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo Matrix
  AdvancedEncryption.RingBTVW

variable {N K k : ℕ}

/-! ### Rows in the codec -/

theorem concatN_add (n m : ℕ) (f : ℕ → List Bool) :
    concatN (n + m) f = concatN n f ++ concatN m (fun j => f (n + j)) := by
  induction m with
  | zero => simp [concatN]
  | succ m ih => rw [← Nat.add_assoc, concatN, ih, concatN, List.append_assoc]

theorem concatN_mul (a b : ℕ) (f : ℕ → List Bool) :
    concatN (a * b) f = concatN a (fun i => concatN b (fun j => f (i * b + j))) := by
  induction a with
  | zero => simp [concatN]
  | succ a ih => rw [Nat.succ_mul, concatN_add, ih, concatN]

theorem flatMap_product {α β : Type} (l₁ : List α) (l₂ : List β) (F : α × β → List Bool) :
    (l₁.product l₂).flatMap F = l₁.flatMap (fun a => l₂.flatMap (fun b => F (a, b))) := by
  induction l₁ with
  | nil => rfl
  | cons a l ih =>
    rw [show (a :: l).product l₂ = l₂.map (Prod.mk a) ++ l.product l₂ from List.product_cons a l l₂,
      List.flatMap_append, ih, List.flatMap_cons, List.flatMap_map]

/-- **The codec's word of a row** is `rowW`. -/
theorem matEnc_row (B : Matrix (Fin 1) (Col k) (DualUse.Rg N K)) :
    (matEnc (N := N) (K := K) (Fin 1) (Col k)).enc B = rowW N K k B := by
  have hl : (matEnc (N := N) (K := K) (Fin 1) (Col k)).enc B =
      ((List.finRange 2).product (List.finRange k)).flatMap
        (fun c => (ringEnc N K).enc (B 0 c)) := by
    show (([0] : List (Fin 1)).map (fun i => (B i : Col k → Rg N K))).flatMap
      (fun r => ((Enum.list (α := Col k)).map r).flatMap (ringEnc N K).enc) = _
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.flatMap_map]
    rfl
  have e : matW N K 1 (2 * k) (B.submatrix id (colE k)) =
      concatN (1 * (2 * k)) (fun p =>
        if h : p < 2 * k then (ringEnc N K).enc (B 0 (colE k ⟨p, h⟩)) else []) := by
    apply concatN_congr
    intro p hp
    have hp' : p < 2 * k := by omega
    rw [dite_eq_left_of_eq_true (eq_true hp), dite_eq_left_of_eq_true (eq_true hp')]
    simp only [submatrix_apply, id]
    congr 2
    · exact Subsingleton.elim _ _
    · exact congrArg _ (Fin.ext (Nat.mod_eq_of_lt hp'))
  rw [hl, flatMap_product, flatMap_finRange, rowW, e, Nat.one_mul, concatN_mul]
  apply concatN_congr
  intro a ha
  rw [dite_eq_left_of_eq_true (eq_true ha), flatMap_finRange]
  apply concatN_congr
  intro i hi
  have hlt : a * k + i < 2 * k := by
    have := Nat.mul_le_mul_right k (show a + 1 ≤ 2 by omega); rw [Nat.add_mul] at this; omega
  rw [dite_eq_left_of_eq_true (eq_true hi), dite_eq_left_of_eq_true (eq_true hlt), colE_apply]
  have hk : 0 < k := by omega
  congr 3
  · ext; simp only; rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hi]; simp
  · ext; simp only; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

/-! ### The key matrix -/

/-- The program `f̂` of a gate list, with the orders `ordT`, `ordO`. -/
def fhatProg (K : ℕ) (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (gs : GateList) : SLP (Fin 10 × BI N k) × (BI N k → Wire (Fin 10 × BI N k)) :=
  fhatSLPL ordT ordO (gvExp (2 ^ K)) (2 ^ K) (predOf 10 gs).1 (predOf 10 gs).2

/-- **The key matrix on words**: generate `f̂`, evaluate the public keys of its output wires, sum
`PK_b · G̲⁻¹(V_b)`. -/
def keyMatrixW (N K k : ℕ) (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (gs : GateList) (bjW : Fin 10 × BI N k → List Bool) : List Bool :=
  keySumW N K k fun c i j =>
    if h : c < 2 * k ∧ i < k ∧ j < N then
      slpPKW N K k bjW (fhatProg K ordT ordO gs).1
        ((fhatProg K ordT ordO gs).2 (0, colE k ⟨c, h.1⟩, ⟨i, h.2.1⟩, ⟨j, h.2.2⟩))
    else []

/-- **`keyMatrixW` computes the key matrix** at the orders of `fhatSLP`. -/
theorem keyMatrixW_eq (hk : 2 ^ K < 2 ^ k) {Wd Wt : Type*} [Fintype Wd] [Fintype Wt]
    (mpk : MPK (Sdw (N := N) hk) Wd Wt) (gs : GateList) :
    keyMatrixW N K k (ordT₀ N k) (ordO₀ N k) gs (fun j => rowW N K k (mpk.Bj j)) =
      rowW N K k (keyMatrix mpk (predOf 10 gs)) := by
  unfold DualUse.keyMatrix
  refine keySumW_enc hk.le
    (fun b => slpPK (topBin N K k hk.le) mpk.Bj ((Sdw (N := N) hk).fhat (predOf 10 gs)).1
      (((Sdw (N := N) hk).fhat (predOf 10 gs)).2 b)) _ ?_
  intro c i j
  rw [dite_eq_left_of_eq_true (eq_true ⟨c.isLt, i.isLt, j.isLt⟩), fhatProg, ← fhatSLP_eq_L hk]
  exact slpPKW_enc hk.le mpk.Bj _ _

/-- Steps of `keyMatrixW`, given the number `g` of gates of `f̂` and the steps `genSteps` of its
generation: the generation, `EvalF` on every gate, and the key-matrix sum. -/
def keyMatrixSteps (N K k g genSteps : ℕ) : ℕ :=
  genSteps + slpPKSteps N K k g + keySumSteps N K k

/-! ### The blocks `B_j` in the public key's word -/

/-- The length of the word of one row `B_j`. -/
abbrev rowLen (N K k : ℕ) : ℕ :=
  (Enum.list (α := Fin 1)).length * ((Enum.list (α := Col k)).length * (N * K))

/-- **The word of `B_j` is a block of the public key's word**: skip `B₀` and `B₁`, keep the family
of the `B_j`, and take the block of the `i`-th index of its enumeration. -/
theorem pkEnc_Bj (hk : 2 ^ K < 2 ^ k) (c : DualUse.Conf N K k) (m : DualUse.PK hk c) (i : ℕ)
    (hi : i < (Enum.list (α := (DualUse.Sdw (N := N) hk).Attr ×
      (DualUse.Sdw (N := N) hk).ctBits.Index)).length) :
    (((((DualUse.pkEnc hk c).enc m).drop
        ((Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K)))).drop
        ((Enum.list (α := Fin 1)).length * ((Enum.list (α := DualUse.TrapCol k)).length * (N * K))) |>.take
        ((Enum.list (α := (DualUse.Sdw (N := N) hk).Attr ×
          (DualUse.Sdw (N := N) hk).ctBits.Index)).length * rowLen N K k)).drop
        (i * rowLen N K k)).take (rowLen N K k) =
      rowW N K k (m.Bj (Enum.list (α := (DualUse.Sdw (N := N) hk).Attr ×
        (DualUse.Sdw (N := N) hk).ctBits.Index))[i]) := by
  have he : (DualUse.pkEnc hk c).enc m = ((DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).prod
      ((DualUse.matEnc (Fin 1) (DualUse.TrapCol k)).prod
      ((FixedEnc.fun (α := (DualUse.Sdw (N := N) hk).Attr × (DualUse.Sdw (N := N) hk).ctBits.Index)
        (DualUse.matEnc (Fin 1) (Col k))).prod (ringEnc N K)))).enc (m.B₀, m.B₁, m.Bj, m.p) := rfl
  rw [he]
  rw [FixedEnc.prod_drop, FixedEnc.prod_drop, FixedEnc.prod_take, FixedEnc.fun_block, matEnc_row]

/-- **The word of `B_j` at its position** in the public key's word. -/
theorem pkEnc_Bj_index (hk : 2 ^ K < 2 ^ k) (c : DualUse.Conf N K k) (m : DualUse.PK hk c)
    (j : (DualUse.Sdw (N := N) hk).Attr × (DualUse.Sdw (N := N) hk).ctBits.Index) :
    (((((DualUse.pkEnc hk c).enc m).drop
        ((Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K)))).drop
        ((Enum.list (α := Fin 1)).length * ((Enum.list (α := DualUse.TrapCol k)).length * (N * K))) |>.take
        ((Enum.list (α := (DualUse.Sdw (N := N) hk).Attr ×
          (DualUse.Sdw (N := N) hk).ctBits.Index)).length * rowLen N K k)).drop
        (Enum.index j * rowLen N K k)).take (rowLen N K k) = rowW N K k (m.Bj j) := by
  rw [pkEnc_Bj hk c m _ (Enum.index_lt j), Enum.getElem_index]

