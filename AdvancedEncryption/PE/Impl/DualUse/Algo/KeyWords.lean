import PE.Impl.DualUse.Algo.KeyMatrix
import PE.Impl.DualUse.KeyBoxes
import SigabaNeo.Lib.Lattices.Algo.BoxWords
import SigabaNeo.Lib.Lattices.Algo.Coins

/-!
# Keys and big-box elements on words

The words read and written by one try of key generation (`PE.Impl.DualUse.Algo.KeyTry`):

* `vecW`: a vector on an enumerated type, its ring entries in the order of the enumeration; the
  codec's matrices with one column or one row are vectors (`matEnc_col`, `matEnc_row1`), and so is
  a secret key (`keyEnc_eq`); vectors on the gadget columns are rows `rowW` and columns
  (`vecW_col`, `vecW_colW`);
* `dotW`: `∑ₐ uₐ vₐ` (`dotW_vecW`), `matSubW` and scalar multiples on vectors;
* `shortW`: the short part `(k₀, k₁)` of a key, the two vectors one after the other; it is also the
  word of its coefficients in the order of `Enum (Coef d Wt N)` (`shortW_coef`), so the ball test
  `ballW` on it is the membership in `keyBall` (`ballW_shortW`);
* `keyEmbE`: the big box of `KeyBoxes` with an explicit bit layout (the `B` coins of the
  coefficient `q` are the coins `B q, …, B q + B − 1`); it has the same image as `keyEmb`
  (`univ_map_keyEmbE`) and its word is `embW` (`embW_eq`).
-/

namespace AdvancedEncryption.DualUse.Algo

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo Matrix Cslib
  AdvancedEncryption.RingBTVW

variable {N K k : ℕ}

/-! ### Vectors -/

/-- **The word of a vector** on an enumerated type: its entries in the order of the enumeration. -/
def vecW (N K : ℕ) {α : Type} [Enum α] (v : α → Rq N K) : List Bool :=
  (FixedEnc.fun (ringEnc N K)).enc v

theorem length_vecW {α : Type} [Enum α] (v : α → Rq N K) :
    (vecW N K v).length = (Enum.list (α := α)).length * (N * K) :=
  (FixedEnc.fun (ringEnc N K)).length v

theorem rget_vecW {α : Type} [Enum α] (v : α → Rq N K) {i : ℕ}
    (hi : i < (Enum.list (α := α)).length) :
    rget N K i (vecW N K v) = (ringEnc N K).enc (v (Enum.list (α := α))[i]) :=
  FixedEnc.fun_block _ v i hi

theorem vecW_sum {α β : Type} [Enum α] [Enum β] (v : α ⊕ β → Rq N K) :
    vecW N K v = vecW N K (v ∘ Sum.inl) ++ vecW N K (v ∘ Sum.inr) := by
  show (((Enum.list (α := α)).map Sum.inl ++ (Enum.list (α := β)).map Sum.inr).map v).flatMap _ =
    ((Enum.list (α := α)).map (v ∘ Sum.inl)).flatMap _ ++
      ((Enum.list (α := β)).map (v ∘ Sum.inr)).flatMap _
  rw [List.map_append, List.flatMap_append, List.map_map, List.map_map]

theorem fun_fin1 {β : Type} {n : ℕ} (e : FixedEnc β n) (g : Fin 1 → β) :
    (FixedEnc.fun e).enc g = e.enc (g 0) := by
  show ((List.finRange 1).map g).flatMap e.enc = _
  simp [List.finRange_succ]

theorem vecW_fin1 (v : Fin 1 → Rq N K) : vecW N K v = (ringEnc N K).enc (v 0) := fun_fin1 _ v

/-- A matrix with one column is the vector of its column. -/
theorem matEnc_col {r : Type} [Enum r] (M : Matrix r (Fin 1) (Rq N K)) :
    (DualUse.matEnc (N := N) (K := K) r (Fin 1)).enc M = vecW N K (fun i => M i 0) := by
  show ((Enum.list (α := r)).map (fun i => (M i : Fin 1 → Rq N K))).flatMap
      (FixedEnc.fun (ringEnc N K)).enc =
    ((Enum.list (α := r)).map (fun i => M i 0)).flatMap (ringEnc N K).enc
  rw [List.flatMap_map, List.flatMap_map]
  congr 1
  funext i
  exact fun_fin1 _ _

/-- A matrix with one row is the vector of its row. -/
theorem matEnc_row1 {s : Type} [Enum s] (B : Matrix (Fin 1) s (Rq N K)) :
    (DualUse.matEnc (N := N) (K := K) (Fin 1) s).enc B = vecW N K (B 0) := fun_fin1 _ B

/-- Vectors on the gadget columns are rows. -/
theorem vecW_col (v : Col k → Rq N K) : vecW N K v = rowW N K k (Matrix.of fun _ c => v c) := by
  rw [← matEnc_row, matEnc_row1]
  rfl

/-- Vectors on the gadget columns are columns. -/
theorem vecW_colW (v : Col k → Rq N K) :
    vecW N K v = matW N K (2 * k) 1 (Matrix.of fun p _ => v (colE k p)) := by
  rw [vecW_col, rowW, matW_row_col]
  rfl

theorem concatN_zeroW (n m : ℕ) : concatN n (fun _ => zeroW m) = zeroW (n * m) := by
  induction n with
  | zero => simp [concatN, zeroW]
  | succ n ih => rw [concatN, ih, zeroW, zeroW, zeroW, ← List.replicate_add, Nat.succ_mul]

theorem vecW_zero {α : Type} [Enum α] :
    vecW N K (0 : α → Rq N K) = zeroW ((Enum.list (α := α)).length * (N * K)) := by
  rw [vecW, fun_enc_concatN, ← concatN_zeroW]
  apply concatN_congr
  intro i hi
  rw [dite_eq_left_of_eq_true (eq_true hi), Pi.zero_apply, enc_zeroR]

theorem length_product' {α β : Type} (l₁ : List α) (l₂ : List β) :
    (l₁.product l₂).length = l₁.length * l₂.length :=
  List.length_product l₁ l₂

theorem len_col : (Enum.list (α := Col k)).length = 2 * k := by
  simp [Enum.list, length_product']

theorem len_fin (n : ℕ) : (Enum.list (α := Fin n)).length = n := by simp [Enum.list]

theorem len_trapCol : (Enum.list (α := DualUse.TrapCol k)).length = 1 + (2 * k + 2 * k) := by
  show ((Enum.list (α := Fin 1)).map Sum.inl ++ ((Enum.list (α := Col k)).map Sum.inl ++
    (Enum.list (α := Col k)).map Sum.inr).map Sum.inr).length = _
  simp only [List.length_append, List.length_map, len_col, len_fin]

/-! ### Sums and products -/

open Classical in
/-- The elements of an enumerated type, as positions of its enumeration. -/
noncomputable def enumEquiv (α : Type) [Enum α] : Fin (Enum.list (α := α)).length ≃ α :=
  List.Nodup.getEquivOfForallMemList _ Enum.nodup Enum.complete

theorem enumEquiv_apply {α : Type} [Enum α] (i : Fin (Enum.list (α := α)).length) :
    enumEquiv α i = (Enum.list (α := α))[i] := rfl

/-- A sum over an enumerated type is the loop over its enumeration. -/
theorem sum_enum {α M : Type} [Enum α] [Fintype α] [AddCommMonoid M] (f : α → M) :
    ∑ a, f a = ∑ i ∈ Finset.range (Enum.list (α := α)).length,
      (if h : i < (Enum.list (α := α)).length then f (Enum.list (α := α))[i] else 0) := by
  rw [← (enumEquiv α).sum_comp, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dite_eq_left_of_eq_true (eq_true i.isLt)]
  rfl

/-- **The dot product** of two vectors of `n` ring entries. -/
def dotW (N K n : ℕ) (x y : List Bool) : List Bool :=
  sumLoop N K (fun i => mulRW N K (rget N K i x) (rget N K i y)) n

theorem dotW_vecW {α : Type} [Enum α] [Fintype α] (u v : α → Rq N K) :
    dotW N K (Enum.list (α := α)).length (vecW N K u) (vecW N K v) =
      (ringEnc N K).enc (∑ a, u a * v a) := by
  rw [sum_enum, dotW]
  exact sumLoop_enc (fun i => if h : i < (Enum.list (α := α)).length then
      u (Enum.list (α := α))[i] * v (Enum.list (α := α))[i] else 0)
    (fun i hi => by rw [rget_vecW u hi, rget_vecW v hi, mulRW_enc, dite_eq_left_of_eq_true (eq_true hi)]) _ le_rfl

theorem matSubW_vecW {α : Type} [Enum α] (u v : α → Rq N K) :
    matSubW N K (Enum.list (α := α)).length (vecW N K u) (vecW N K v) = vecW N K (u - v) := by
  conv_rhs => rw [vecW, fun_enc_concatN]
  apply concatN_congr
  intro i hi
  rw [dite_eq_left_of_eq_true (eq_true hi), rget_vecW u hi, rget_vecW v hi, subRW_enc]
  rfl

/-- The multiple `t v` of a vector by a ring element. -/
def smulVW (N K n : ℕ) (t x : List Bool) : List Bool :=
  concatN n fun i => mulRW N K t (rget N K i x)

theorem smulVW_vecW {α : Type} [Enum α] (t : Rq N K) (v : α → Rq N K) :
    smulVW N K (Enum.list (α := α)).length ((ringEnc N K).enc t) (vecW N K v) =
      vecW N K (fun a => t * v a) := by
  conv_rhs => rw [vecW, fun_enc_concatN]
  apply concatN_congr
  intro i hi
  rw [dite_eq_left_of_eq_true (eq_true hi), rget_vecW v hi, mulRW_enc]

/-! ### Secret keys -/

/-- **The word of a secret key**: the vectors `k₀`, `k₁`, `k₂`. -/
theorem keyEnc_eq (c : DualUse.Conf N K k)
    (sk : DualUse.SecretKey (Fin c.d) (DualUse.TrapCol k) (R := DualUse.Rg N K) (k := k)) :
    (DualUse.keyEnc (N := N) (K := K) c).enc sk =
      vecW N K (fun i => sk.k₀ i 0) ++ (vecW N K (fun i => sk.k₁ i 0) ++
        vecW N K (fun i => sk.k₂ i 0)) := by
  show (DualUse.matEnc (N := N) (K := K) (Fin c.d) (Fin 1)).enc sk.k₀ ++
    ((DualUse.matEnc (N := N) (K := K) (DualUse.TrapCol k) (Fin 1)).enc sk.k₁ ++
      (DualUse.matEnc (N := N) (K := K) (Col k) (Fin 1)).enc sk.k₂) = _
  rw [matEnc_col, matEnc_col, matEnc_col]

/-! ### The short part of a key -/

/-- **The word of the short part** `(k₀, k₁)`. -/
def shortW (N K : ℕ) {Wd Wt : Type} [Enum Wd] [Enum Wt] (x : DualUse.KeyShort Wd Wt (Rq N K)) :
    List Bool :=
  vecW N K x.1 ++ vecW N K x.2

theorem ringEnc_flatMap (r : Rq N K) :
    (ringEnc N K).enc r = (List.finRange N).flatMap (fun j => (zmodEnc K).enc (r.coeffs j)) := by
  rw [ringEnc_enc, flatMap_finRange]

variable {d : ℕ} {Wt : Type} [Fintype Wt] [DecidableEq Wt] [Enum Wt]

omit [Fintype Wt] [DecidableEq Wt] in
/-- **The short part is the word of its coefficients.** -/
theorem shortW_coef (x : DualUse.KeyShort (Fin d) Wt (Rq N K)) :
    shortW N K x = (FixedEnc.fun (α := DualUse.Coef d Wt N) (zmodEnc K)).enc (DualUse.keyEquiv x) := by
  show _ = ((((Enum.list (α := Fin d)).map Sum.inl ++ (Enum.list (α := Wt)).map Sum.inr).product
    (List.finRange N)).map (DualUse.keyEquiv x)).flatMap (zmodEnc K).enc
  rw [List.flatMap_map, flatMap_product, List.flatMap_append, List.flatMap_map, List.flatMap_map]
  show ((Enum.list (α := Fin d)).map x.1).flatMap (ringEnc N K).enc ++
    ((Enum.list (α := Wt)).map x.2).flatMap (ringEnc N K).enc = _
  rw [List.flatMap_map, List.flatMap_map]
  congr 1
  · congr 1; funext i; rw [ringEnc_flatMap]; rfl
  · congr 1; funext i; rw [ringEnc_flatMap]; rfl

/-- The number of coefficients of a short part. -/
abbrev nCoef (d : ℕ) (Wt : Type) [Enum Wt] (N : ℕ) : ℕ := (Enum.list (α := DualUse.Coef d Wt N)).length

omit [Fintype Wt] [DecidableEq Wt] in
theorem length_shortW (x : DualUse.KeyShort (Fin d) Wt (Rq N K)) :
    (shortW N K x).length = nCoef d Wt N * K := by
  rw [shortW_coef]; exact (FixedEnc.fun _).length _

omit [Fintype Wt] [DecidableEq Wt] in
theorem block_shortW (x : DualUse.KeyShort (Fin d) Wt (Rq N K)) {q : ℕ} (hq : q < nCoef d Wt N) :
    block K q (shortW N K x) =
      (zmodEnc K).enc (DualUse.keyEquiv x (Enum.list (α := DualUse.Coef d Wt N))[q]) := by
  rw [shortW_coef]
  exact FixedEnc.fun_block _ _ q hq

/-- **The ball test on words is the membership in `keyBall`.** -/
theorem ballW_shortW {S : ℕ} {sW : List Bool} (hs : sW.length = K) (hS : val sW = S)
    (x : DualUse.KeyShort (Fin d) Wt (Rq N K)) :
    ballW (nCoef d Wt N) K sW (shortW N K x) = decide (x ∈ DualUse.keyBall (2 ^ K) d Wt N S) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ballW_eq_true hs (length_shortW x), DualUse.mem_keyBall]
  constructor
  · intro h i
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem (Enum.complete i)
    have := h q hq
    rwa [block_shortW x hq, dec_enc, hS] at this
  · intro h q hq
    rw [block_shortW x hq, dec_enc, hS]
    exact h _

/-! ### The big box with an explicit bit layout -/

/-- The positions of the coefficients of a short part. -/
noncomputable abbrev coefEquiv (d : ℕ) (Wt : Type) [Enum Wt] (N : ℕ) : Fin (nCoef d Wt N) ≃ DualUse.Coef d Wt N :=
  enumEquiv _

/-- The coins of the big box: the coin `t` of the coefficient at position `q` is the coin
`t + B q`. -/
noncomputable def bitsOfKeyE (d : ℕ) (Wt : Type) [Enum Wt] (N B m : ℕ) (hm : nCoef d Wt N * B = m) :
    (Fin m → Bool) ≃ (DualUse.Coef d Wt N → Fin B → Bool) :=
  (Equiv.arrowCongr ((((coefEquiv d Wt N).symm.prodCongr (Equiv.refl (Fin B))).trans
    (finProdFinEquiv.trans (finCongr hm))).symm) (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

/-- **The big box** with the explicit bit layout. -/
noncomputable def keyEmbE {Q : ℕ} [NeZero Q] (B : ℕ) (hB : 2 ^ B ≤ Q) (m : ℕ) (hm : nCoef d Wt N * B = m) :
    (Fin m → Bool) ↪ DualUse.KeyShort (Fin d) Wt (Negacyclic (ZMod Q) N) :=
  (bitsOfKeyE d Wt N B m hm).toEmbedding.trans
    ((Function.Embedding.piCongrRight fun _ => cenEmb B hB).trans
      DualUse.keyEquiv.symm.toEmbedding)

omit [Fintype Wt] [DecidableEq Wt] in
theorem keyEmbE_apply {Q : ℕ} [NeZero Q] (B : ℕ) (hB : 2 ^ B ≤ Q) (m : ℕ)
    (hm : nCoef d Wt N * B = m) (bs : Fin m → Bool) :
    keyEmbE (d := d) (Wt := Wt) (N := N) B hB m hm bs = DualUse.keyEquiv.symm (fun c =>
      cenEmb B hB (fun t => bs (finCongr hm (finProdFinEquiv ((coefEquiv d Wt N).symm c, t))))) :=
  rfl

theorem univ_map_keyEmbE {Q : ℕ} [NeZero Q] (B : ℕ) (hB : 2 ^ B ≤ Q) (m : ℕ)
    (hm : nCoef d Wt N * B = m) :
    Finset.univ.map (keyEmbE (d := d) (Wt := Wt) (N := N) B hB m hm) =
      (bigBox B hB).map DualUse.keyEquiv.symm.toEmbedding := by
  rw [keyEmbE, ← Finset.map_map, ← Finset.map_map, bigBox]
  congr 2
  exact Finset.map_univ_equiv _

/-- **The big boxes of `keyEmb` and `keyEmbE` are equal.** -/
theorem univ_map_keyEmbE_eq {Q : ℕ} [NeZero Q] (B : ℕ) (hB : 2 ^ B ≤ Q) (m : ℕ)
    (hm : nCoef d Wt N * B = m) (hm' : Fintype.card (DualUse.Coef d Wt N) * B = m) :
    Finset.univ.map (keyEmbE (d := d) (Wt := Wt) (N := N) B hB m hm) =
      Finset.univ.map (DualUse.keyEmb (d := d) (Wt := Wt) (N := N) B hB m hm') := by
  rw [univ_map_keyEmbE, DualUse.univ_map_keyEmb]

omit [DecidableEq Wt] in
theorem nCoef_eq_card : nCoef d Wt N = Fintype.card (DualUse.Coef d Wt N) := by
  rw [← Fintype.card_fin (nCoef d Wt N)]
  exact Fintype.card_congr (coefEquiv d Wt N)

omit [Fintype Wt] [DecidableEq Wt] in
/-- **`embW` computes the big-box element of the coins.** -/
theorem embW_eq (B : ℕ) (hB : 2 ^ B ≤ 2 ^ K) (m : ℕ) (hm : nCoef d Wt N * B = m) (l : List Bool) :
    embW (nCoef d Wt N) B K l =
      shortW N K (keyEmbE (d := d) (Wt := Wt) (N := N) B hB m hm (SigabaNeo.Lattices.Algo.bitsOf m l)) := by
  rw [shortW_coef, fun_enc_concatN, embW]
  apply concatN_congr
  intro q hq
  rw [dite_eq_left_of_eq_true (eq_true hq), keyEmbE_apply, Equiv.apply_symm_apply, getW, cenW_enc B K hB]
  have hc : (coefEquiv d Wt N).symm (Enum.list (α := DualUse.Coef d Wt N))[q] = ⟨q, hq⟩ :=
    (Equiv.symm_apply_eq _).mpr rfl
  congr 2
  funext t
  rw [hc]
  simp only [SigabaNeo.Lattices.Algo.bitsOf, finCongr_apply, Fin.val_cast]
  show _ = l.getD (t + B * q) false
  rw [Nat.add_comm]

end AdvancedEncryption.DualUse.Algo
