import PE.Impl.DualUse.Algo.RowSim
import PE.Impl.DualUse.Algo.KeyMatrix
import PE.Impl.DualUse.Algo.KeyWords
import PE.Impl.DualUse.Algo.KeyTry
import PE.Impl.DualUse.Prog.Layout

/-!
# The crafted simulation data of `KeyGen` and `Dec`

`KeyGen` and `Dec` compute `B_f̂` and `c_f̂` with the `W_f` block of the key component, run on a
crafted `SimData` (`sdOf`): the public key, `c₀ = 0`, `Rᵢ` and `W_j` decoded from words, the given
`Ψ`, and the date `(0, 0)`. Every word of the right length encodes a matrix (`enc_decM`, by
counting), so the machines may write any data in the free rows. The last row of `W_j` is `B_j`
(resp. `c_j`), the first word of the `W_j` carries a stash `X₀` (the rest of the input).

* **`sdEnc_sdOf`**: the word of `sdOf`, in the order the machines write it;
* **`keyMatrix_sdB`**: `B_f̂ = row_{d-1} W_f + G̲` for `sdB` (`Rᵢ = 0`, `Ψ = 0`);
* **`evalCiphertext_sdC`**: `c_f̂ = row_{d-1} W_f + (row 1 of G)` for `sdC` (the last two rows of
  `Rᵢ` are those of `Ψᵢ`);
* `colsW_last`: the last row of a `colsW` word is its last `2 k N K` bits.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow
open AdvancedEncryption.DualUse.Prog

/-! ### Every word of the right length is an encoding -/

theorem FixedEnc.surj_of_card {β : Type} [Fintype β] {n : ℕ} (e : FixedEnc β n)
    (hc : Fintype.card β = 2 ^ n) (w : List Bool) (hw : w.length = n) : ∃ b, e.enc b = w := by
  let f : β → List.Vector Bool n := fun b => ⟨e.enc b, e.length b⟩
  have hf : Function.Injective f := fun a b h => e.inj (congrArg Subtype.val h)
  have hb : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, by rw [card_vector]; simp [hc]⟩
  obtain ⟨b, hb⟩ := hb.2 ⟨w, hw⟩
  exact ⟨b, congrArg Subtype.val hb⟩

variable {N K k : ℕ}

theorem card_rg : Fintype.card (Rg N K) = 2 ^ (N * K) := by
  rw [Fintype.card_congr (Cslib.Negacyclic.coeffsEquiv (R := ZMod (2 ^ K)) (n := N)), Fintype.card_fun,
    ZMod.card, Fintype.card_fin, ← pow_mul, Nat.mul_comm]

/-- The length of the word of a row. -/
abbrev rowL (N K k : ℕ) : ℕ := 2 * k * (N * K)

theorem len_matEnc_col (m : ℕ) :
    (Enum.list (α := Fin m)).length * ((Enum.list (α := Col k)).length * (N * K)) = m * rowL N K k := by
  rw [Algo.len_fin, Algo.len_col]

theorem card_mat (m : ℕ) :
    Fintype.card (Matrix (Fin m) (Col k) (Rg N K)) = 2 ^ (m * rowL N K k) := by
  show Fintype.card (Fin m → Col k → Rg N K) = _
  rw [Fintype.card_fun, Fintype.card_fun, card_rg, Fintype.card_fin, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin, ← pow_mul, ← pow_mul]
  congr 1; ring

/-- The matrix a word encodes (`0` for a word of another length). -/
noncomputable def wordMat (m : ℕ) (w : List Bool) : Matrix (Fin m) (Col k) (Rg N K) :=
  open Classical in
  if h : ∃ M, (matEnc (N := N) (K := K) (Fin m) (Col k)).enc M = w then h.choose else 0

theorem enc_decM {m : ℕ} {w : List Bool} (hw : w.length = m * rowL N K k) :
    (matEnc (N := N) (K := K) (Fin m) (Col k)).enc (wordMat m w) = w := by
  have h : ∃ M, (matEnc (N := N) (K := K) (Fin m) (Col k)).enc M = w :=
    FixedEnc.surj_of_card _ (by rw [card_mat, len_matEnc_col]) w (by rw [hw, len_matEnc_col])
  rw [wordMat, dif_pos h]
  exact h.choose_spec

/-! ### Rows of matrix words -/

theorem len_row1 : (Enum.list (α := Fin 1)).length * ((Enum.list (α := Col k)).length * (N * K)) =
    rowL N K k := by
  rw [len_matEnc_col, Nat.one_mul]

theorem length_row1 (B : Matrix (Fin 1) (Col k) (Rg N K)) :
    ((matEnc (N := N) (K := K) (Fin 1) (Col k)).enc B).length = rowL N K k := by
  rw [FixedEnc.length, len_row1]

/-- **The `i`-th block of a matrix word** is the word of row `i`. -/
theorem matEnc_block {m : ℕ} (M : Matrix (Fin m) (Col k) (Rg N K)) (i : ℕ) (hi : i < m) :
    (((matEnc (N := N) (K := K) (Fin m) (Col k)).enc M).drop (i * rowL N K k)).take (rowL N K k) =
      (matEnc (N := N) (K := K) (Fin 1) (Col k)).enc (rowAt M ⟨i, hi⟩) := by
  have h := FixedEnc.fun_block (α := Fin m) (FixedEnc.fun (α := Col k) (ringEnc N K)) M i
    (by rw [Algo.len_fin]; exact hi)
  have e : (Enum.list (α := Col k)).length * (N * K) = rowL N K k := by rw [Algo.len_col]
  rw [← e, Algo.matEnc_row1]
  show _ = (FixedEnc.fun (ringEnc N K)).enc (fun col => M ⟨i, hi⟩ col)
  rw [Enum.getElem_fin] at h
  exact h

theorem block_append {Z u r : List Bool} {L : ℕ} (hZ : Z.length = L) (hu : u.length = n) :
    ((Z ++ (u ++ r)).drop L).take n = u := by
  rw [List.drop_left' hZ, List.take_left' hu]

/-- The last row of a matrix whose word ends with the word of `v` is `v`. -/
theorem rowAt_last_of_enc {m : ℕ} (hm : 0 < m) (M : Matrix (Fin m) (Col k) (Rg N K)) (Z : List Bool)
    (v : Matrix (Fin 1) (Col k) (Rg N K)) (hZ : Z.length = (m - 1) * rowL N K k)
    (h : (matEnc (N := N) (K := K) (Fin m) (Col k)).enc M =
      Z ++ (matEnc (N := N) (K := K) (Fin 1) (Col k)).enc v) :
    rowAt M ⟨m - 1, by omega⟩ = v := by
  have hb := matEnc_block M (m - 1) (by omega)
  rw [h, ← List.append_nil ((matEnc (N := N) (K := K) (Fin 1) (Col k)).enc v),
    block_append hZ (length_row1 v)] at hb
  exact (matEnc (N := N) (K := K) (Fin 1) (Col k)).inj hb.symm

/-- The last two rows of a matrix whose word ends with the word of `P` are the rows of `P`. -/
theorem rowAt_two_of_enc {m : ℕ} (hm : 2 ≤ m) (M : Matrix (Fin m) (Col k) (Rg N K)) (Z : List Bool)
    (P : Matrix (Fin 2) (Col k) (Rg N K)) (hZ : Z.length = (m - 2) * rowL N K k)
    (h : (matEnc (N := N) (K := K) (Fin m) (Col k)).enc M =
      Z ++ (matEnc (N := N) (K := K) (Fin 2) (Col k)).enc P) :
    rowAt M ⟨m - 2, by omega⟩ = rowAt P 0 ∧ rowAt M ⟨m - 1, by omega⟩ = rowAt P 1 := by
  have hP0 := matEnc_block P 0 (by omega)
  have hP1 := matEnc_block P 1 (by omega)
  have hlP : ((matEnc (N := N) (K := K) (Fin 2) (Col k)).enc P).length = 2 * rowL N K k := by
    rw [FixedEnc.length, len_matEnc_col]
  constructor
  · have hb := matEnc_block M (m - 2) (by omega)
    rw [h, List.drop_left' hZ] at hb
    rw [Nat.zero_mul, List.drop_zero] at hP0
    exact (matEnc (N := N) (K := K) (Fin 1) (Col k)).inj (hb.symm.trans hP0)
  · have hb := matEnc_block M (m - 1) (by omega)
    rw [h, show (m - 1) * rowL N K k = (m - 2) * rowL N K k + 1 * rowL N K k by
      rw [← Nat.add_mul]; congr 1; omega, ← List.drop_drop, List.drop_left' hZ] at hb
    exact (matEnc (N := N) (K := K) (Fin 1) (Col k)).inj (hb.symm.trans hP1)

/-- **The last row of a `colsW` word** is its last `2 k N K` bits. -/
theorem colsW_last {m : ℕ} (hm : 0 < m) (M : Matrix (Fin m) (Col k) (Rg N K)) :
    (Algo.colsW N K k m M).drop ((m - 1) * rowL N K k) =
      Algo.rowW N K k (rowAt M ⟨m - 1, by omega⟩) := by
  rw [← matEnc_cols, ← Algo.matEnc_row]
  have hb := matEnc_block M (m - 1) (by omega)
  have hl : (((matEnc (N := N) (K := K) (Fin m) (Col k)).enc M).drop ((m - 1) * rowL N K k)).length =
      rowL N K k := by
    rw [List.length_drop, FixedEnc.length, len_matEnc_col]
    rw [show m * rowL N K k = (m - 1) * rowL N K k + rowL N K k by
      rw [show m = (m - 1) + 1 by omega, Nat.add_mul, Nat.one_mul]; simp]
    omega
  rw [List.take_of_length_le (le_of_eq hl)] at hb
  exact hb

/-! ### Zero words and function words -/

theorem flatMap_const_replicate {α : Type*} (l : List α) (n : ℕ) :
    l.flatMap (fun _ => List.replicate n false) = List.replicate (l.length * n) false := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, ih, List.length_cons, Nat.succ_mul, Nat.add_comm, List.replicate_add]

theorem fun_enc_eq {α β : Type} [Enum α] {n : ℕ} (e : FixedEnc β n) (f : α → β) :
    (FixedEnc.fun (α := α) e).enc f = (Enum.list (α := α)).flatMap (fun a => e.enc (f a)) := by
  show ((Enum.list (α := α)).map f).flatMap e.enc = _
  rw [List.flatMap_map]

theorem fun_enc_const {α β : Type} [Enum α] {n : ℕ} (e : FixedEnc β n) (b : β)
    (hb : e.enc b = List.replicate n false) :
    (FixedEnc.fun (α := α) e).enc (fun _ => b) =
      List.replicate ((Enum.list (α := α)).length * n) false := by
  rw [fun_enc_eq]; simp only [hb]; exact flatMap_const_replicate _ _

theorem matEnc_zero (r s : Type) [Enum r] [Enum s] :
    (matEnc (N := N) (K := K) r s).enc 0 = List.replicate
      ((Enum.list (α := r)).length * ((Enum.list (α := s)).length * (N * K))) false :=
  fun_enc_const _ _ (fun_enc_const _ _ (Algo.enc_zeroR N K))

/-! ### The crafted simulation data -/

/-- The concatenation of rows, with `X₀` before the first and `Y` before every other. -/
def wPart (X₀ Y : List Bool) : List (List Bool) → List Bool
  | [] => []
  | r :: rs => X₀ ++ r ++ wPart Y Y rs

theorem flatMap_head {α : Type*} [DecidableEq α] (X₀ Y : List Bool) (h : α → List Bool) :
    ∀ l : List α, l.Nodup →
      l.flatMap (fun j => (if l.head? = some j then X₀ else Y) ++ h j) = wPart X₀ Y (l.map h)
  | [], _ => rfl
  | a :: l, hn => by
    have hn' := List.nodup_cons.mp hn
    have hrest : ∀ l' : List α, (∀ j ∈ l', a ≠ j) →
        l'.flatMap (fun j => (if some a = some j then X₀ else Y) ++ h j) =
          wPart Y Y (l'.map h) := by
      intro l' hl'
      induction l' with
      | nil => rfl
      | cons b l' ih =>
        rw [List.flatMap_cons, List.map_cons, wPart, ih (fun j hj => hl' j (by simp [hj])),
          if_neg (by simpa using hl' b (by simp))]
    rw [List.flatMap_cons, List.map_cons, wPart, List.head?_cons, if_pos rfl,
      hrest l (fun j hj e => hn'.1 (e ▸ hj))]

variable {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

/-- The index type of the `B_j`, `c_j`, `W_j`. -/
abbrev JIx (hk : 2 ^ K < 2 ^ k) := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index

variable (hk) in
/-- The word of `W_j`: the stash `X₀` (for the first `j` of the enumeration) or `Z` zeros, then
the row `g j`. -/
noncomputable def wWord (X₀ : List Bool) (Z : ℕ) (g : JIx (N := N) hk → Matrix (Fin 1) (Col k) (Rg N K))
    (j : JIx (N := N) hk) : List Bool :=
  (if (Enum.list (α := JIx (N := N) hk)).head? = some j then X₀ else List.replicate Z false) ++
    (matEnc (N := N) (K := K) (Fin 1) (Col k)).enc (g j)

variable (hk c) in
/-- **The crafted simulation data**: `mpk`, `c₀ = 0`, the `Rᵢ` of the words `rmW i`, the `W_j` of
`wWord X₀ g`, `Ψ`, the date `(0, 0)`. -/
noncomputable def sdOf (mpk : PK hk c) (rmW : Fin 10 → List Bool)
    (Ψ : Fin 10 → Matrix (Fin 2) (Col k) (Rg N K)) (X₀ : List Bool)
    (g : JIx (N := N) hk → Matrix (Fin 1) (Col k) (Rg N K)) : SimData hk c where
  mpk := mpk
  c₀ := 0
  Rm i := wordMat c.d (rmW i)
  W j := wordMat c.d (wWord hk X₀ ((c.d - 1) * rowL N K k) g j)
  Ψ := Ψ
  x := date0

theorem length_wWord {X₀ : List Bool} {Z : ℕ} (hX : X₀.length = Z)
    (g : JIx (N := N) hk → Matrix (Fin 1) (Col k) (Rg N K)) (j : JIx (N := N) hk) :
    (wWord hk X₀ Z g j).length = Z + rowL N K k := by
  rw [wWord, List.length_append, length_row1]
  split_ifs <;> simp [hX]

theorem dateEnc_date0 : dateEnc.enc date0 = List.replicate 10 false := rfl

/-- **The word of the crafted simulation data.** -/
theorem sdEnc_sdOf (mpk : PK hk c) {rmW : Fin 10 → List Bool}
    (hrm : ∀ i, (rmW i).length = c.d * rowL N K k) (Ψ : Fin 10 → Matrix (Fin 2) (Col k) (Rg N K))
    {X₀ : List Bool} (hX : X₀.length = (c.d - 1) * rowL N K k) (hd : 0 < c.d)
    (g : JIx (N := N) hk → Matrix (Fin 1) (Col k) (Rg N K)) :
    (sdEnc hk c).enc (sdOf hk c mpk rmW Ψ X₀ g) =
      (pkEnc hk c).enc mpk ++ (List.replicate (c.d * (N * K)) false ++
        ((List.finRange 10).flatMap rmW ++
          (wPart X₀ (List.replicate ((c.d - 1) * rowL N K k) false)
              ((Enum.list (α := JIx (N := N) hk)).map
                fun j => (matEnc (N := N) (K := K) (Fin 1) (Col k)).enc (g j)) ++
            ((FixedEnc.fun (α := Fin 10) (matEnc (N := N) (K := K) (Fin 2) (Col k))).enc Ψ ++
              List.replicate 10 false)))) := by
  rw [sdEnc_enc]
  simp only [sdOf]
  congr 1
  congr 1
  · rw [matEnc_zero, Algo.len_fin, Algo.len_fin, Nat.one_mul]
  congr 1
  · show (FixedEnc.fun (α := Fin 10) (matEnc (N := N) (K := K) (Fin c.d) (Col k))).enc
      (fun i => wordMat c.d (rmW i)) = _
    rw [fun_enc_eq]
    simp only [enc_decM (hrm _)]
    rfl
  congr 1
  · rw [fun_enc_eq]
    have hw : ∀ j, (wWord hk X₀ ((c.d - 1) * rowL N K k) g j).length = c.d * rowL N K k := by
      intro j
      rw [length_wWord hX]
      rw [show c.d * rowL N K k = (c.d - 1) * rowL N K k + rowL N K k by
        rw [show c.d = (c.d - 1) + 1 from by omega, Nat.add_mul, Nat.one_mul]; simp]
    simp only [enc_decM (hw _)]
    exact flatMap_head _ _ _ _ Enum.nodup

/-! ### The key row and `c_f̂` from the crafted data -/

/-- The last row index. -/
def lastR (c : Conf N K k) (hd : 0 < c.d) : Fin c.d := ⟨c.d - 1, by omega⟩

variable (hk c) in
/-- **The crafted data of `KeyGen`**: `Rᵢ = 0`, `Ψ = 0`, the last row of `W_j` is `B_j`. -/
noncomputable def sdB (mpk : PK hk c) (X₀ : List Bool) : SimData hk c :=
  sdOf hk c mpk (fun _ => List.replicate (c.d * rowL N K k) false) (fun _ => 0) X₀ mpk.Bj

theorem rowAt_W_sdOf (hd : 0 < c.d) {X₀ : List Bool} (hX : X₀.length = (c.d - 1) * rowL N K k)
    (mpk : PK hk c) (rmW : Fin 10 → List Bool) (Ψ : Fin 10 → Matrix (Fin 2) (Col k) (Rg N K))
    (g : JIx (N := N) hk → Matrix (Fin 1) (Col k) (Rg N K)) (j : JIx (N := N) hk) :
    rowAt ((sdOf hk c mpk rmW Ψ X₀ g).W j) (lastR c hd) = g j := by
  have hw : (wWord hk X₀ ((c.d - 1) * rowL N K k) g j).length = c.d * rowL N K k := by
    rw [length_wWord hX]
    rw [show c.d * rowL N K k = (c.d - 1) * rowL N K k + rowL N K k by
      rw [show c.d = (c.d - 1) + 1 from by omega, Nat.add_mul, Nat.one_mul]; simp]
  refine rowAt_last_of_enc hd _ _ (g j) ?_ (enc_decM hw)
  split_ifs <;> simp [hX]

/-- **`B_f̂` from the crafted data**: the last row of `W_f`, plus `G̲`. -/
theorem keyMatrix_sdB (hd : 0 < c.d) (mpk : PK hk c) {X₀ : List Bool}
    (hX : X₀.length = (c.d - 1) * rowL N K k) (w : Window) :
    keyMatrix mpk (predC (winWord w)) =
      rowAt (simW (sdB hk c mpk X₀) (winWord w)) (lastR c hd) + (Sdw (N := N) hk).Γ₁.G := by
  have hR : ∀ i, rowAt ((sdB hk c mpk X₀).Rm i) (lastR c hd) = 0 := by
    intro i
    refine rowAt_last_of_enc hd _ (List.replicate ((c.d - 1) * rowL N K k) false) 0 (by simp) ?_
    rw [show (sdB hk c mpk X₀).Rm i = wordMat c.d (List.replicate (c.d * rowL N K k) false) from rfl,
      enc_decM (by simp), matEnc_zero, len_row1, ← List.replicate_add]
    congr 1
    rw [show c.d = (c.d - 1) + 1 from by omega, Nat.add_mul, Nat.one_mul]; simp
  refine (keyMatrix_eq_rowSim mpk _ (sdB hk c mpk X₀).W (lastR c hd)
    (rowAt_W_sdOf hd hX mpk (fun _ => List.replicate (c.d * rowL N K k) false) (fun _ => 0) mpk.Bj)
    hR (predC (winWord w))).trans ?_
  rw [circ_eval_date0, one_smul]
  rfl

variable (hk c) in
/-- **The crafted data of `Dec`**: the last two rows of `Rᵢ` are those of `Ψᵢ`, the ciphertext's
`Ψ`, the last row of `W_j` is `c_j`. -/
noncomputable def sdC (mpk : PK hk c) (ct : CT hk c) (X₀ : List Bool) : SimData hk c :=
  sdOf hk c mpk (fun i => List.replicate ((c.d - 2) * rowL N K k) false ++
      (matEnc (N := N) (K := K) (Fin 2) (Col k)).enc (ct.Ψ i)) ct.Ψ X₀ ct.cj

/-- **`c_f̂` from the crafted data**: the last row of `W_f`, plus the second row of `G`. -/
theorem evalCiphertext_sdC (hd : 2 ≤ c.d) (mpk : PK hk c) (ct : CT hk c) {X₀ : List Bool}
    (hX : X₀.length = (c.d - 1) * rowL N K k) (w : Window) :
    evalCiphertext mpk (predC (winWord w)) ct =
      rowAt (simW (sdC hk c mpk ct X₀) (winWord w)) (lastR c (by omega)) +
        rowAt (Sdw (N := N) hk).Γ.G 1 := by
  have hrows : ∀ i, rowAt ((sdC hk c mpk ct X₀).Rm i) ⟨c.d - 2, by omega⟩ = rowAt (ct.Ψ i) 0 ∧
      rowAt ((sdC hk c mpk ct X₀).Rm i) (lastR c (by omega)) = rowAt (ct.Ψ i) 1 := by
    intro i
    refine rowAt_two_of_enc hd _ (List.replicate ((c.d - 2) * rowL N K k) false) (ct.Ψ i) (by simp)
      (enc_decM ?_)
    rw [List.length_append, List.length_replicate, FixedEnc.length, len_matEnc_col, ← Nat.add_mul]
    congr 1; omega
  refine (evalCiphertext_eq_rowSim mpk ct _ (sdC hk c mpk ct X₀).W (lastR c (by omega))
    ⟨c.d - 2, by omega⟩ (rowAt_W_sdOf (by omega) hX mpk (fun i => List.replicate
      ((c.d - 2) * rowL N K k) false ++ (matEnc (N := N) (K := K) (Fin 2) (Col k)).enc (ct.Ψ i))
      ct.Ψ ct.cj) (fun i => (hrows i).1) (fun i => (hrows i).2)
    (predC (winWord w))).trans ?_
  rw [circ_eval_date0, one_smul]
  rfl

end AdvancedEncryption.DualUse
