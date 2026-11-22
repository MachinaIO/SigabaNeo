import PE.Impl.DualUse.Prog.EncPsi
import SigabaNeo.Lib.Lattices.ProgAlgo.BggEnc

/-!
# The bits `ψ_j` and the BGG+ encodings of `Enc` on words

* `coefBits_entry`: the bits that `coefBitsP` (`SigabaNeo.Lib.Lattices.ProgAlgo.CoefBits`) reads
  off the word of a ring element `v`, followed by the `(k − K) N` zeros, are the bits
  `testBit (v.coeffs t).val b` for `b < k`, `t < N`;
* `eStepC_list`: over a stream of ring words;
* **`coefBits_psi`**: on the word of the ten `Ψᵢ`, the register receives the bits
  `coeffBool (Ψ j.1) j.2` for `j` in the enumeration of `Attr × Index` — the bits `ψ_j` of the
  scheme (`bitsOf`).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  Matrix AdvancedEncryption.RingBTVW Cslib
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow

variable {N K k : ℕ}

theorem hd_drop_eq_getD : ∀ (l : List Bool) (m : ℕ), Tape.hd (l.drop m) = l.getD m false
  | [], m => by simp [Tape.hd]
  | b :: l, 0 => rfl
  | b :: l, m + 1 => by rw [List.drop_succ_cons, hd_drop_eq_getD l m]; rfl

/-- **A bit of a coefficient** in the word of a ring element. -/
theorem hd_drop_enc (v : Rg N K) (rest : List Bool) {b t : ℕ} (hb : b < K) (ht : t < N) :
    Tape.hd (((ringEnc N K).enc v ++ rest).drop (b + t * K)) =
      (v.coeffs ⟨t, ht⟩).val.testBit b := by
  have hpos : t * K + b < N * K := by
    have := Nat.mul_le_mul_right K (show t + 1 ≤ N from ht); rw [Nat.add_mul, one_mul] at this
    omega
  rw [hd_drop_eq_getD, List.getD_append _ _ _ _ (by rw [len_enc]; omega), Nat.add_comm]
  have hblk : ((ringEnc N K).enc v).getD (t * K + b) false =
      (block K t ((ringEnc N K).enc v)).getD b false := by
    simp [block, List.getD_eq_getElem?_getD, List.getElem?_take, hb, List.getElem?_drop]
  rw [hblk, block_ringEnc v ht, getD_enc]

/-- The bit `b` of the coefficient `t` (`false` out of range). -/
def cbit (v : Rg N K) (b t : ℕ) : Bool :=
  if h : t < N then (v.coeffs ⟨t, h⟩).val.testBit b else false

theorem map_finRange_eq_range {α : Type} (n : ℕ) (f : Fin n → α) (g : ℕ → α)
    (h : ∀ i (hi : i < n), f ⟨i, hi⟩ = g i) : (List.finRange n).map f = (List.range n).map g := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_finRange, List.getElem_range]
  exact h i (by simpa using h1)

theorem flatMap_finRange_eq_range {α : Type} (n : ℕ) (f : Fin n → List α) (g : ℕ → List α)
    (h : ∀ i (hi : i < n), f ⟨i, hi⟩ = g i) :
    (List.finRange n).flatMap f = (List.range n).flatMap g := by
  rw [List.flatMap_def, List.flatMap_def, map_finRange_eq_range n f g h]

theorem flatMap_rep {α : Type} (l : List α) (N : ℕ) :
    l.flatMap (fun _ => List.replicate N false) = List.replicate (l.length * N) false := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, ih, List.length_cons, Nat.succ_mul, Nat.add_comm, List.replicate_add]

/-- **The bits of a ring word**, then the `(k − K) N` zeros: the bits of all `k` digit
positions. -/
theorem coefBits_entry (hKk : K ≤ k) (v : Rg N K) (rest : List Bool) :
    ((List.range K).flatMap fun b => (List.range N).map fun t =>
        Tape.hd (((ringEnc N K).enc v ++ rest).drop (b + t * K))) ++
      List.replicate ((k - K) * N) false =
      (List.finRange k).flatMap fun (b : Fin k) => (List.finRange N).map fun (t : Fin N) =>
        (v.coeffs t).val.testBit b := by
  have h1 : ((List.range K).flatMap fun b => (List.range N).map fun t =>
      Tape.hd (((ringEnc N K).enc v ++ rest).drop (b + t * K))) =
      (List.range K).flatMap fun b => (List.range N).map (cbit v b) := by
    refine List.flatMap_congr fun b hb => List.map_congr_left fun t ht => ?_
    rw [List.mem_range] at hb ht
    rw [hd_drop_enc v rest hb ht, cbit, dif_pos ht]
  have h2 : List.replicate ((k - K) * N) false =
      (List.range (k - K)).flatMap fun b => (List.range N).map (cbit v (K + b)) := by
    have : ∀ b t, cbit v (K + b) t = false := by
      intro b t
      unfold cbit
      split_ifs
      · exact Nat.testBit_lt_two_pow ((ZMod.val_lt _).trans_le
          (Nat.pow_le_pow_right (by norm_num) (by omega)))
      · rfl
    rw [List.flatMap_congr (fun b _ => by rw [show (List.range N).map (cbit v (K + b)) =
      List.replicate N false by
        rw [show cbit v (K + b) = fun _ => false from funext (this b), List.map_const',
          List.length_range]]), flatMap_rep, List.length_range]
  rw [h1, h2, flatMap_finRange_eq_range k _ (fun b => (List.range N).map (cbit v b))]
  · conv_rhs => rw [show k = K + (k - K) by omega, List.range_add, List.flatMap_append,
      List.flatMap_map]
  · intro b hb
    exact map_finRange_eq_range N _ _ fun t ht => by rw [cbit, dif_pos ht]

/-- The bits of a ring element, digit position outer. -/
def entryBits (k : ℕ) (v : Rg N K) : List Bool :=
  (List.finRange k).flatMap fun (b : Fin k) => (List.finRange N).map fun (t : Fin N) =>
    (v.coeffs t).val.testBit b

theorem len_entryBits (v : Rg N K) : (entryBits k v).length = k * N := by
  rw [entryBits, Tape.Prog.length_flatMap_eq _ _ (n := N) (fun _ _ => by simp), List.length_finRange]

theorem eStepC_list (hKk : K ≤ k) : ∀ (vs : List (Rg N K)) (z rest : List Bool),
    (Tape.Prog.eStepC N K ((k - K) * N))^[vs.length] (z, vs.flatMap (ringEnc N K).enc ++ rest) =
      ((z ++ vs.flatMap (entryBits k)).drop (vs.length * (k * N)), rest)
  | [], z, rest => by simp
  | v :: vs, z, rest => by
    rw [List.length_cons, Function.iterate_succ_apply, List.flatMap_cons, List.append_assoc,
      Tape.Prog.eStepC_eq, List.append_assoc z _ (List.replicate _ false), coefBits_entry hKk,
      drop_enc_append]
    have hkN : K * N + (k - K) * N = k * N := by rw [← Nat.add_mul]; congr 1; omega
    rw [hkN]
    rw [show ((List.finRange k).flatMap fun (b : Fin k) => (List.finRange N).map fun (t : Fin N) =>
        (v.coeffs t).val.testBit b) = entryBits k v from rfl]
    rw [eStepC_list hKk vs, List.flatMap_cons, reg_shiftW _ _ _ (len_entryBits v)]

/-- The entries of the ten `Ψᵢ`, in the order of their word. -/
def psiEntries (Ψ : Fin 10 → Matrix (Fin 2) (RingBTVW.Col k) (Rg N K)) : List (Rg N K) :=
  (List.finRange 10).flatMap fun i => (List.finRange 2).flatMap fun a =>
    (Enum.list (α := RingBTVW.Col k)).map fun col => Ψ i a col

theorem psiWord_eq (Ψ : Fin 10 → Matrix (Fin 2) (RingBTVW.Col k) (Rg N K)) :
    (FixedEnc.fun (α := Fin 10) (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).enc Ψ =
      (psiEntries Ψ).flatMap (ringEnc N K).enc := by
  show ((List.finRange 10).map Ψ).flatMap (fun M => ((List.finRange 2).map (fun r => M r)).flatMap
    (fun row => ((Enum.list (α := RingBTVW.Col k)).map row).flatMap (ringEnc N K).enc)) = _
  simp only [psiEntries, List.flatMap_map, List.flatMap_assoc]

theorem len_psiEntries (Ψ : Fin 10 → Matrix (Fin 2) (RingBTVW.Col k) (Rg N K)) :
    (psiEntries Ψ).length = 10 * (2 * (2 * k)) := by
  simp [psiEntries, List.length_flatMap, len_enum_col]
  ring

variable (hk : 2 ^ K < 2 ^ k)

/-- **The bits `ψ_j`**: the coefficient bits of the ten `Ψᵢ`, entry by entry, are the bits
`coeffBool (Ψ j.1) j.2` along the enumeration of `Attr × Index`. -/
theorem psiBits_eq (Ψ : Fin 10 → Matrix (Fin 2) (RingBTVW.Col k) (Rg N K)) :
    (psiEntries Ψ).flatMap (entryBits k) =
      (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).map
        fun j => coeffBool (Ψ j.1) j.2 := by
  show _ = ((List.finRange 10).product ((List.finRange 2).product ((Enum.list (α := RingBTVW.Col k)).product
    ((List.finRange k).product (List.finRange N))))).map fun j => coeffBool (Ψ j.1) j.2
  simp only [psiEntries, List.flatMap_assoc, List.flatMap_map, entryBits, List.product, List.map_flatMap,
    List.map_map, coeffBool]
  rfl

/-! ### The BGG+ encodings -/

theorem matSubW_row (A B : Matrix (Fin 1) (Fin (2 * k)) (Rg N K)) :
    matSubW N K (2 * k) (matW N K 1 (2 * k) A) (matW N K 1 (2 * k) B) = matW N K 1 (2 * k) (A - B) := by
  have := matSubW_enc (N := N) (K := K) (m := 1) (n := 2 * k) A B
  rwa [Nat.one_mul] at this

theorem addRW_row (A B : Matrix (Fin 1) (Fin (2 * k)) (Rg N K)) :
    addRW (2 * k * N) K (matW N K 1 (2 * k) A) (matW N K 1 (2 * k) B) = matW N K 1 (2 * k) (A + B) := by
  rw [← matAddW_eq_addRW]
  have := matAddW_enc (N := N) (K := K) (m := 1) (n := 2 * k) A B
  rwa [Nat.one_mul] at this

theorem len_rowC (A : Matrix (Fin 1) (RingBTVW.Col k) (Rg N K)) :
    ((matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc A).length = 1 * (2 * k) * (N * K) := by
  rw [matEnc_cols, colsW, length_matW]

/-- One encoding on words. -/
theorem jStepE_enc (s : Rg N K) (Bj ej : Matrix (Fin 1) (RingBTVW.Col k) (Rg N K)) (z : Bool)
    (out rz rb re : List Bool) :
    Tape.Prog.jStepE N K (2 * k) ((ringEnc N K).enc s) (gadW N K k)
      (out, z :: rz, (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc Bj ++ rb,
        (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc ej ++ re) =
      ((out ++ (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc
          (scalar s * (Bj - bitR (R := Rg N K) z • (Sdw (N := N) hk).Γ₁.G) + ej)).drop
          (1 * (2 * k) * (N * K)), rz, rb, re) := by
  have hb := len_rowC (N := N) (K := K) Bj
  have he := len_rowC (N := N) (K := K) ej
  have hsw : (ringEnc N K).enc s = matW N K 1 1 (scalar s) := by rw [matW_one_one]; rfl
  have hg : gadW N K k = colsW N K k 1 (Sdw (N := N) hk).Γ₁.G := gadW_enc hk.le
  simp only [Tape.Prog.jStepE, hd_cons, List.tail_cons]
  have tb : takeD (1 * (2 * k) * (N * K))
      ((matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc Bj ++ rb) =
      (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc Bj := by
    rw [takeD_eq_take (by simp [hb]), List.take_left' hb]
  have te : takeD (1 * (2 * k) * (N * K))
      ((matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc ej ++ re) =
      (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc ej := by
    rw [takeD_eq_take (by simp [he]), List.take_left' he]
  rw [tb, te, List.drop_left' hb, List.drop_left' he]
  congr 1
  rw [matEnc_cols, matEnc_cols, matEnc_cols, hsw, hg, colsW, colsW, colsW, colsW]
  cases z
  · simp only [Bool.false_eq_true, ↓reduceIte, matMulW_enc, addRW_row, bitR, zero_smul, sub_zero]
    rw [takeD_of_length' (by rw [length_matW])]
    rfl
  · simp only [↓reduceIte, matSubW_row, matMulW_enc, addRW_row, bitR, one_smul]
    rw [takeD_of_length' (by rw [length_matW])]
    rfl

theorem bitsOf_eq (Ψ : (Sdw (N := N) hk).Attr → Matrix (Fin 2) (RingBTVW.Col k) (Rg N K))
    (j : (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index) :
    bitsOf (Sdw (N := N) hk) Ψ j = bitR (R := Rg N K) (coeffBool (Ψ j.1) j.2) :=
  coeffBits_isBoolean hk.le (Fin 2) (Ψ j.1) j.2

/-- **The encodings `c_j`**, along a list of indices. -/
theorem jStepE_list (s : Rg N K) (Ψ : (Sdw (N := N) hk).Attr → Matrix (Fin 2) (RingBTVW.Col k) (Rg N K))
    (Bj ej : (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index →
      Matrix (Fin 1) (RingBTVW.Col k) (Rg N K)) :
    ∀ (l : List ((Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)) (out rz rb re : List Bool),
      (Tape.Prog.jStepE N K (2 * k) ((ringEnc N K).enc s) (gadW N K k))^[l.length]
        (out, l.map (fun j => coeffBool (Ψ j.1) j.2) ++ rz,
          l.flatMap (fun j => (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc (Bj j)) ++ rb,
          l.flatMap (fun j => (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc (ej j)) ++ re) =
      ((out ++ l.flatMap (fun j => (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc
          (scalar s * (Bj j - bitsOf (Sdw (N := N) hk) Ψ j • (Sdw (N := N) hk).Γ₁.G) + ej j))).drop
          (l.length * (1 * (2 * k) * (N * K))), rz, rb, re)
  | [], out, rz, rb, re => by simp
  | j :: l, out, rz, rb, re => by
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.map_cons, List.flatMap_cons, List.cons_append, List.append_assoc]
    rw [jStepE_enc hk, jStepE_list s Ψ Bj ej l, reg_shiftW _ _ _ (len_rowC _), bitsOf_eq hk]

end AdvancedEncryption.DualUse.Prog
