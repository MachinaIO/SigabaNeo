import PE.Impl.RingBTVW.Prog.SchemeWords

/-!
# The words of the reductions' values, continued

* `psiBits`: the bits `ψ_j` of the `Ψᵢ`, in the order of `Attr × Index` (bit before coefficient),
  are the transposes of the `N × K` bit matrices of the entries, each followed by `(k − K) N`
  zeros;
* `psiRows`: the rows `ψ_j G̲`, blocks of `G̲` selected by those bits;
* `hash_rows`: `V W_j + E_j` for the binary matrices `W_j` (`hashW`);
* `wMat_word`: the word of the `W_j` (transposes of the bit blocks, bits expanded to ring words);
* rows of one entry and products of `1 × 1` matrices: `c0_word`, `ring_mul_word`,
  `ring_add_word`, `b1_word`, `trapU_word`, `c1_word`.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape Matrix
  AdvancedEncryption.RingBTVW.Fresh
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord

variable {N K k : ℕ}

theorem flatMap_single {α : Type} (l : List α) (f : α → Bool) : (l.flatMap fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, ih]; rfl

theorem flatMap_finRange_add {m n : ℕ} (g : Fin (m + n) → List Bool) :
    (List.finRange (m + n)).flatMap g =
      (List.finRange m).flatMap (fun b => g (Fin.castLE (by omega) b)) ++
        (List.finRange n).flatMap (fun b => g (Fin.natAdd m b)) := by
  rw [← List.ofFn_id, List.ofFn_add, List.flatMap_append, List.ofFn_eq_map, List.ofFn_eq_map,
    List.flatMap_map, List.flatMap_map]
  rfl

theorem ringEnc_bits (v : Rq N K) :
    (ringEnc N K).enc v = (List.finRange N).flatMap fun t =>
      (List.finRange K).map fun b : Fin K => (v.coeffs t).val.testBit b.val := by
  rw [ringEnc_enc, flatMap_finRange]
  refine concatN_congr fun i hi => ?_
  rw [dite_eq_left_of_eq_true (eq_true hi), dite_eq_left_of_eq_true (eq_true hi)]
  rfl

theorem enum_prod_map {α β γ : Type} [Enum α] [Enum β] (f : α × β → γ) :
    (Enum.list (α := α × β)).map f =
      (Enum.list (α := α)).flatMap fun a => (Enum.list (α := β)).map fun b => f (a, b) := by
  show ((Enum.list (α := α)).product (Enum.list (α := β))).map f = _
  induction (Enum.list (α := α)) with
  | nil => rfl
  | cons a l ih =>
    rw [show (a :: l).product (Enum.list (α := β)) =
        (Enum.list (α := β)).map (Prod.mk a) ++ l.product (Enum.list (α := β)) from
      List.product_cons a l _, List.map_append, ih, List.flatMap_cons, List.map_map]
    rfl

theorem length_flatMap_const' {α β : Type} (g : α → List β) (c : ℕ) (l : List α)
    (h : ∀ x, (g x).length = c) : (l.flatMap g).length = l.length * c := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.flatMap_cons, List.length_append, ih, h, List.length_cons]; ring

/-! ### The bits of the `Ψᵢ` -/

/-- The bit `j = (i, a, c, b, t)` of the `Ψᵢ`: the bit `b` of the coefficient `t` of the entry
`(a, c)` of `Ψᵢ`. -/
def psiBit (Ψ : Fin nA → Matrix (Fin 2) (RingBTVW.Fresh.Col k) (Rg N K))
    (j : Fin nA × (Fin 2 × (RingBTVW.Fresh.Col k × (Fin k × Fin N)))) : Bool :=
  ((Ψ j.1 j.2.1 j.2.2.1).coeffs j.2.2.2.2).val.testBit j.2.2.2.1

/-- The entries of the `Ψᵢ`, in their order. -/
def entL (k : ℕ) : List (Fin nA × (Fin 2 × RingBTVW.Fresh.Col k)) :=
  (List.finRange nA).flatMap fun i => (List.finRange 2).flatMap fun a =>
    (Enum.list (α := RingBTVW.Fresh.Col k)).map fun cc => (i, (a, cc))

theorem length_entL : (entL k).length = nA * (2 * (2 * k)) := by
  have h1 : ∀ i : Fin nA, ((List.finRange 2).flatMap fun a =>
      (Enum.list (α := RingBTVW.Fresh.Col k)).map fun cc => (i, (a, cc))).length = 2 * (2 * k) := fun i => by
    rw [length_flatMap_const' _ (2 * k) _ (fun a => by rw [List.length_map, len_col])]; simp
  rw [entL, length_flatMap_const' _ _ _ h1]; simp

theorem psi_entL (Ψ : Fin nA → Matrix (Fin 2) (RingBTVW.Fresh.Col k) (Rg N K)) :
    (FixedEnc.fun (RingBTVW.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Fresh.Col k))).enc Ψ =
      (entL k).flatMap fun q => (ringEnc N K).enc (Ψ q.1 q.2.1 q.2.2) := by
  rw [funEnc_flatMap]
  simp only [entL, List.flatMap_assoc, List.flatMap_map, matEnc_flatMap]
  rfl

theorem enum_idx (hk : 2 ^ K < 2 ^ k) :
    (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)) =
      (Enum.list (α := Fin nA × (Fin 2 × (RingBTVW.Fresh.Col k × (Fin k × Fin N))))) := rfl

theorem testBit_val_ge {K' : ℕ} (x : ZMod (2 ^ K')) {b : ℕ} (hb : K' ≤ b) : x.val.testBit b = false :=
  Nat.testBit_eq_false_of_lt ((ZMod.val_lt x).trans_le (Nat.pow_le_pow_right (by norm_num) hb))

/-- **The bits `ψ_j`**, in the order of `Attr × Index`. -/
theorem psiBits (hk : 2 ^ K < 2 ^ k) (Ψ : Fin nA → Matrix (Fin 2) (RingBTVW.Fresh.Col k) (Rg N K)) :
    trW (nA * (2 * (2 * k))) N K 1 ((k - K) * N)
        ((FixedEnc.fun (RingBTVW.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Fresh.Col k))).enc Ψ) =
      (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).map (psiBit Ψ) := by
  have hKk : K < k := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hk
  rw [psi_entL]
  simp only [ringEnc_bits, ← flatMap_single]
  have h := trW_flatMap (entL k) (List.finRange N) (List.finRange K)
    (fun q t (b : Fin K) => [((Ψ q.1 q.2.1 q.2.2).coeffs t).val.testBit b.val]) 1 ((k - K) * N)
    (fun _ _ _ => rfl)
  simp only [length_entL, List.length_finRange] at h
  rw [h, enum_idx]
  conv_rhs => simp only [enum_prod_map]
  conv_lhs => simp only [entL, List.flatMap_assoc, List.flatMap_map]
  refine congrArg₂ _ (funext fun i => ?_) rfl
  refine congrArg₂ _ (funext fun a => ?_) rfl
  refine congrArg₂ _ (funext fun cc => ?_) rfl
  obtain ⟨m, rfl⟩ : ∃ m, k = K + m := ⟨k - K, by omega⟩
  show _ = (List.finRange (K + m)).flatMap _
  rw [flatMap_finRange_add, show K + m - K = m by omega]
  congr 1
  · refine congrArg₂ _ (funext fun b => ?_) rfl
    rw [← flatMap_single]
    rfl
  · have hz : ∀ b : Fin m, ((Enum.list (α := Fin N)).map fun t =>
        psiBit Ψ (i, (a, (cc, (Fin.natAdd K b, t))))) = List.replicate N false := by
      intro b
      rw [List.map_eq_flatMap]
      have : (fun t : Fin N => [psiBit Ψ (i, (a, (cc, (Fin.natAdd K b, t))))]) =
          fun _ => List.replicate 1 false := funext fun t => by
        simp only [psiBit, Fin.natAdd]
        rw [testBit_val_ge _ (by simp)]
        rfl
      rw [this, flatMap_replicate, len_fin, Nat.mul_one]
    simp only [hz]
    rw [flatMap_replicate, List.length_finRange, Nat.mul_comm]

/-- `ψ_j` is the bit `psiBit`. -/
theorem bitsOf_psiBit (hk : 2 ^ K < 2 ^ k) (Ψ : Fin nA → Matrix (Fin 2) (RingBTVW.Fresh.Col k) (Rg N K))
    (j : (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index) :
    RingBTVW.Fresh.bitsOf (Sdw (N := N) hk) Ψ j = bitR (R := Rg N K) (psiBit Ψ j) := by
  simp only [RingBTVW.Fresh.bitsOf, Sdw, ringSetting, coeffBits, psiBit, bitR]
  split_ifs with h <;> simp [h]

/-! ### The rows `ψ_j G̲` -/

theorem len_AI (hk : 2 ^ K < 2 ^ k) :
    (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).length =
      nA * (2 * (2 * k * (k * N))) := by
  show (Enum.list (α := Fin nA × (Fin 2 × (RingBTVW.Fresh.Col k × (Fin k × Fin N))))).length = _
  simp only [Enum.length_prod, len_fin]

/-- **The rows `ψ_j G̲`**: blocks of `G̲` selected by the bits `ψ_j`. -/
theorem psiRows (hk : 2 ^ K < 2 ^ k) (Ψ : Fin nA → Matrix (Fin 2) (RingBTVW.Fresh.Col k) (Rg N K)) :
    selW (nA * (2 * (2 * k * (k * N)))) (2 * k * (N * K))
        ((Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).map (psiBit Ψ))
        (gadW N K k) [] =
      (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
        (RingBTVW.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Fresh.Col k))).enc
        fun j => RingBTVW.Fresh.bitsOf (Sdw (N := N) hk) Ψ j • (Sdw (N := N) hk).Γ₁.G := by
  have h := selW_map (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index))
    (psiBit Ψ) (2 * k * (N * K)) (gadW N K k) []
  rw [len_AI hk] at h
  refine h.trans ?_
  rw [funEnc_flatMap]
  congr 1
  funext j
  rw [bitsOf_psiBit, gadW_eq_matEnc hk]
  exact bitR_smul_word (by rw [len_fin, len_col]; ring) _ _

/-! ### `V W_j + E_j` -/

theorem enum_JC_eq (hk : 2 ^ K < 2 ^ k) :
    (Enum.list (α := RingBTVW.JC (Sdw (N := N) hk))) =
      (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).product
        (Enum.list (α := RingBTVW.Fresh.Col k)) := rfl

theorem len_JC (hk : 2 ^ K < 2 ^ k) :
    (Enum.list (α := RingBTVW.JC (Sdw (N := N) hk))).length = nA * (2 * (2 * k * (k * N))) * (2 * k) := by
  rw [Enum.length_prod, len_AI hk, len_col]

variable (c : Conf N K k)

theorem wEnc_flatMap (hk : 2 ^ K < 2 ^ k) (w : RingBTVW.JC (Sdw (N := N) hk) → (Fin c.d → Bool)) :
    (wEnc hk c).enc w = (Enum.list (α := RingBTVW.JC (Sdw (N := N) hk))).flatMap fun jc =>
      (List.finRange c.d).map (w jc) := by
  rw [wEnc, funEnc_flatMap]
  congr 1
  funext jc
  rw [funEnc_flatMap]
  exact flatMap_single _ _

theorem row_flatMap (V : Matrix (Fin 1) (Fin c.d) (Rg N K)) :
    (RingBTVW.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc V =
      (List.finRange c.d).flatMap fun a => (ringEnc N K).enc (V 0 a) := by
  rw [matEnc_flatMap, enum_fin_one, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rfl

theorem rowsC_flatMap (hk : 2 ^ K < 2 ^ k)
    (E : (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index → Matrix (Fin 1) (RingBTVW.Fresh.Col k) (Rg N K)) :
    (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
        (RingBTVW.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Fresh.Col k))).enc E =
      (Enum.list (α := RingBTVW.JC (Sdw (N := N) hk))).flatMap fun jc =>
        (ringEnc N K).enc (E jc.1 0 jc.2) := by
  rw [funEnc_flatMap, enum_JC_eq, Algo.flatMap_product]
  congr 1
  funext j
  rw [matEnc_flatMap, enum_fin_one, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- **`V W_j + E_j`** for the binary matrices `W_j` of the columns `w`. -/
theorem hash_rows (hk : 2 ^ K < 2 ^ k) (w : RingBTVW.JC (Sdw (N := N) hk) → (Fin c.d → Bool))
    (V : Matrix (Fin 1) (Fin c.d) (Rg N K))
    (E : (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index → Matrix (Fin 1) (RingBTVW.Fresh.Col k) (Rg N K)) :
    hashW (nA * (2 * (2 * k * (k * N))) * (2 * k)) c.d N K ((wEnc hk c).enc w)
        ((RingBTVW.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc V)
        ((FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
          (RingBTVW.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Fresh.Col k))).enc E) =
      (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
          (RingBTVW.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Fresh.Col k))).enc
        fun j => V * wMat w j + E j := by
  have h := hashW_flatMap (Enum.list (α := RingBTVW.JC (Sdw (N := N) hk))) c.d (fun jc => w jc)
    (fun a => V 0 a) (fun jc => E jc.1 0 jc.2)
  rw [len_JC hk] at h
  rw [wEnc_flatMap, row_flatMap, rowsC_flatMap, h, rowsC_flatMap]
  congr 1
  funext jc
  congr 1
  simp only [Matrix.add_apply, Matrix.mul_apply, wMat, Matrix.of_apply, bitVal, mul_ite, mul_one,
    mul_zero]

/-! ### The matrices `W_j` -/

/-- The positions `(j, a, c)` of the entries of the `W_j`. -/
def posW (hk : 2 ^ K < 2 ^ k) :
    List (((Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index) × (Fin c.d × RingBTVW.Fresh.Col k)) :=
  (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).flatMap fun j =>
    (List.finRange c.d).flatMap fun a => (Enum.list (α := RingBTVW.Fresh.Col k)).map fun cc => (j, (a, cc))

theorem length_posW (hk : 2 ^ K < 2 ^ k) :
    (posW c hk).length = nA * (2 * (2 * k * (k * N))) * (c.d * (2 * k)) := by
  have h1 : ∀ j : (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index,
      ((List.finRange c.d).flatMap fun a => (Enum.list (α := RingBTVW.Fresh.Col k)).map fun cc =>
        (j, (a, cc))).length = c.d * (2 * k) := fun j => by
    rw [length_flatMap_const' _ (2 * k) _ (fun a => by rw [List.length_map, len_col])]; simp
  rw [posW, length_flatMap_const' _ _ _ h1, len_AI hk]

/-- **The word of the `W_j`**: the transposes of the bit blocks of `w`, bits expanded. -/
theorem wMat_word (hk : 2 ^ K < 2 ^ k) (w : RingBTVW.JC (Sdw (N := N) hk) → (Fin c.d → Bool)) :
    selW (nA * (2 * (2 * k * (k * N))) * (c.d * (2 * k))) (N * K)
        (trW (nA * (2 * (2 * k * (k * N)))) (2 * k) c.d 1 0 ((wEnc hk c).enc w)) (oneW N K) [] =
      (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
        (RingBTVW.matEnc (N := N) (K := K) (Fin c.d) (RingBTVW.Fresh.Col k))).enc (wMat w) := by
  have hw : (wEnc hk c).enc w =
      (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).flatMap fun j =>
        (Enum.list (α := RingBTVW.Fresh.Col k)).flatMap fun cc => (List.finRange c.d).flatMap fun a =>
          [w (j, cc) a] := by
    rw [wEnc_flatMap, enum_JC_eq, Algo.flatMap_product]
    congr 1; funext j; congr 1; funext cc
    exact (flatMap_single _ _).symm
  have h := trW_flatMap (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index))
    (Enum.list (α := RingBTVW.Fresh.Col k)) (List.finRange c.d) (fun j cc a => [w (j, cc) a]) 1 0
    (fun _ _ _ => rfl)
  rw [len_AI hk, len_col, List.length_finRange] at h
  have hT : trW (nA * (2 * (2 * k * (k * N)))) (2 * k) c.d 1 0 ((wEnc hk c).enc w) =
      (posW c hk).map fun q => w (q.1, q.2.2) q.2.1 := by
    rw [hw, h, posW, List.map_flatMap]
    congr 1; funext j
    rw [List.replicate_zero, List.append_nil, List.map_flatMap]
    congr 1; funext a
    rw [List.map_map, flatMap_single]
    rfl
  have hs := selW_map (posW c hk) (fun q => w (q.1, q.2.2) q.2.1) (N * K) (oneW N K) []
  rw [length_posW] at hs
  have hone : (oneW N K).length = N * K := by rw [← enc_one]; exact (ringEnc N K).length _
  rw [hT, hs, funEnc_flatMap, posW, List.flatMap_assoc]
  congr 1; funext j
  rw [List.flatMap_assoc, matEnc_flatMap]
  congr 1; funext a
  rw [List.flatMap_map]
  congr 1; funext cc
  simp only [wMat, Matrix.of_apply, bitVal]
  cases w (j, cc) a
  · simp [takeD_nil, enc_zeroR, zeroW]
  · simp [takeD_of_length' hone, enc_one]

/-! ### Rows of one entry and products of `1 × 1` matrices -/

theorem matEnc_one_one (M : Matrix (Fin 1) (Fin 1) (Rg N K)) :
    (RingBTVW.matEnc (N := N) (K := K) (Fin 1) (Fin 1)).enc M = (ringEnc N K).enc (M 0 0) := by
  rw [matEnc_flatMap, enum_fin_one]; simp

/-- **`c₀ = s B₀ + e₀`** on words. -/
theorem c0_word (s : Rg N K) (B₀ e₀ : Matrix (Fin 1) (Fin c.d) (Rg N K)) :
    matAddW N K (1 * c.d) (matMulW N K 1 1 c.d ((ringEnc N K).enc s)
        ((RingBTVW.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc B₀))
        ((RingBTVW.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc e₀) =
      (RingBTVW.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc (RingBTVW.Fresh.scalar s * B₀ + e₀) := by
  rw [show (ringEnc N K).enc s = (RingBTVW.matEnc (N := N) (K := K) (Fin 1) (Fin 1)).enc
    (RingBTVW.Fresh.scalar s) by rw [matEnc_one_one]; rfl,
    matEnc_mul' (len_fin 1) (len_fin 1) (len_fin c.d), matAddW_matEnc' (len_fin 1) (len_fin c.d)]

/-- **Products of ring elements** on words. -/
theorem ring_mul_word (a b : Rg N K) :
    matMulW N K 1 1 1 ((ringEnc N K).enc a) ((ringEnc N K).enc b) = (ringEnc N K).enc (a * b) := by
  have := matEnc_mul' (N := N) (K := K) (len_fin 1) (len_fin 1) (len_fin 1) (RingBTVW.Fresh.scalar a)
    (RingBTVW.Fresh.scalar b)
  rw [matEnc_one_one, matEnc_one_one, matEnc_one_one] at this
  have e1 : RingBTVW.Fresh.scalar a 0 0 = a := rfl
  have e2 : RingBTVW.Fresh.scalar b 0 0 = b := rfl
  have e3 : (RingBTVW.Fresh.scalar a * RingBTVW.Fresh.scalar b) 0 0 = a * b := by
    simp [RingBTVW.Fresh.scalar, Matrix.mul_apply]
  rw [e1, e2, e3] at this
  exact this

/-- **Sums of ring elements** on words. -/
theorem ring_add_word (a b : Rg N K) :
    matAddW N K 1 ((ringEnc N K).enc a) ((ringEnc N K).enc b) = (ringEnc N K).enc (a + b) := by
  have := matAddW_matEnc' (N := N) (K := K) (len_fin 1) (len_fin 1) (RingBTVW.Fresh.scalar a)
    (RingBTVW.Fresh.scalar b)
  rw [matEnc_one_one, matEnc_one_one, matEnc_one_one] at this
  have e1 : RingBTVW.Fresh.scalar a 0 0 = a := rfl
  have e2 : RingBTVW.Fresh.scalar b 0 0 = b := rfl
  have e3 : (RingBTVW.Fresh.scalar a + RingBTVW.Fresh.scalar b) 0 0 = a + b := rfl
  rw [e1, e2, e3, Nat.mul_one] at this
  exact this

theorem len_trap : (Enum.list (α := TrapCol k)).length = 1 + (2 * k + 2 * k) := by
  show ((Enum.list (α := Fin 1)).map Sum.inl ++ (Enum.list (α := RingBTVW.Fresh.Col k ⊕ RingBTVW.Fresh.Col k)).map
    Sum.inr).length = _
  rw [List.length_append, List.length_map, List.length_map, len_fin]
  show 1 + ((Enum.list (α := RingBTVW.Fresh.Col k)).map Sum.inl ++
    (Enum.list (α := RingBTVW.Fresh.Col k)).map Sum.inr).length = _
  rw [List.length_append, List.length_map, List.length_map, len_col]

/-- **`c₁ = s B₁ + e₁`** on words. -/
theorem c1_word (s : Rg N K) (B₁ e₁ : Matrix (Fin 1) (TrapCol k) (Rg N K)) :
    matAddW N K (1 * (1 + (2 * k + 2 * k))) (matMulW N K 1 1 (1 + (2 * k + 2 * k)) ((ringEnc N K).enc s)
        ((RingBTVW.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc B₁))
        ((RingBTVW.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc e₁) =
      (RingBTVW.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc (RingBTVW.Fresh.scalar s * B₁ + e₁) := by
  rw [show (ringEnc N K).enc s = (RingBTVW.matEnc (N := N) (K := K) (Fin 1) (Fin 1)).enc
    (RingBTVW.Fresh.scalar s) by rw [matEnc_one_one]; rfl,
    matEnc_mul' (len_fin 1) (len_fin 1) len_trap, matAddW_matEnc' (len_fin 1) len_trap]

theorem length_oneW : (oneW N K).length = N * K := by rw [← enc_one]; exact (ringEnc N K).length _

/-- **The row `[1 | a | z]`** on words. -/
theorem trapU_word (a z : Matrix (Fin 1) (RingBTVW.Fresh.Col k) (Rg N K)) :
    takeD (N * K) (oneW N K) ++
        takeD (rowL N K k) ((RingBTVW.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Fresh.Col k)).enc a) ++
        takeD (rowL N K k) ((RingBTVW.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Fresh.Col k)).enc z) =
      (RingBTVW.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc (trapRowU a z) := by
  rw [Algo.matEnc_row, Algo.matEnc_row, takeD_of_length' length_oneW, takeD_of_length' (length_rowW _),
    takeD_of_length' (length_rowW _), matEnc_trap, Algo.matEnc_row, Algo.matEnc_row]
  simp only [trapRowU, Matrix.of_apply, enc_one, List.append_assoc]
  congr 3 <;> ext i c <;> simp [Subsingleton.elim i 0]

/-- **The row `toB₁ (a, b) = [1 | a | G̲ − b]`** on words. -/
theorem b1_word (hk : 2 ^ K < 2 ^ k) (ab : Inst3T N K k) :
    takeD (N * K) (oneW N K) ++
        takeD (rowL N K k) ((RingBTVW.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Fresh.Col k)).enc ab.1) ++
        takeD (rowL N K k) (matSubW N K (1 * (2 * k)) (gadW N K k)
          ((RingBTVW.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Fresh.Col k)).enc ab.2)) =
      (RingBTVW.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc (toB₁ (Sdw (N := N) hk) ab) := by
  have hsub : matSubW N K (1 * (2 * k)) (gadW N K k)
      ((RingBTVW.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Fresh.Col k)).enc ab.2) =
      (RingBTVW.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Fresh.Col k)).enc ((Sdw (N := N) hk).Γ₁.G - ab.2) := by
    rw [Algo.matEnc_row, Algo.matEnc_row, gadW_enc hk.le, rowW, rowW, matSubW_enc, rowW,
      Matrix.submatrix_sub]
    rfl
  rw [hsub, toB₁]
  exact trapU_word _ _

end AdvancedEncryption.RingBTVW.Prog
