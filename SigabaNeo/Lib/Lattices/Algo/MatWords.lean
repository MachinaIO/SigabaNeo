import SigabaNeo.Lib.Lattices.Algo.RingWords

/-!
# Matrices over `R_q` on bit words, and the binary gadget

A matrix `M ∈ R_q^{m × n}` (`R_q = ℤ_{2^K}[X]/(X^N + 1)`) is the word of its entries in row-major
order, each entry a ring word of `N · K` bits (`matW`); the entry `(i, j)` is the ring block
`i n + j` (`rget_matW`). Matrices indexed by the gadget columns `Col k = Fin 2 × Fin k` are read
through `colE : Fin (2k) ≃ Fin 2 × Fin k`, `p ↦ (p / k, p % k)` (the lexicographic order of
`SigabaNeo.Encode.Enum`): `rowW` for rows `1 × Col k`, `sqW` for `Col k × Col k`.

First-order loops, proved equal to the mathematics:

* `matAddW`, `matSubW`: entrywise (`matAddW_enc`, `matSubW_enc`);
* `matMulW`: `(A B)_{ij} = ∑_t A_{it} B_{tj}`, accumulated by `sumLoop` (`matMulW_enc`);
* `ginvW`: the decomposition `G̲⁻¹` of the binary top-row gadget, on a row: the entry `(c, col)` is
  the binary digit `c.2` of the entry `col` when `c.1 = 0`, zero otherwise (`ginvW_enc`);
* `gadW`: the gadget row `G̲` (`gadW_enc`);
* `nandPKW`: the BGG+ NAND of public keys, `G̲ − A G̲⁻¹(B)` (`nandPKW_enc`).

Step counts: `matMulSteps`, `ginvSteps`, `nandPKSteps`.
-/

namespace SigabaNeo.Lattices.Algo

open SigabaNeo.Encode Cslib Matrix

/-- The ring `ℤ_{2^K}[X]/(X^N + 1)`. -/
abbrev Rq (N K : ℕ) := Negacyclic (ZMod (2 ^ K)) N

variable {N K : ℕ}

theorem div_lt_of_lt_mul' {p m n : ℕ} (h : p < m * n) : p / n < m :=
  (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (by rintro rfl; simp at h))).mpr h

theorem mod_lt_of_lt_mul' {p m n : ℕ} (h : p < m * n) : p % n < n :=
  Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; simp at h))

theorem index_lt {m n : ℕ} (i : Fin m) (j : Fin n) : i.val * n + j.val < m * n := by
  have := Nat.mul_le_mul_right n (show i.val + 1 ≤ m from i.isLt)
  rw [Nat.add_mul] at this; omega

/-! ### Matrix words -/

/-- The ring block `p` of a word. -/
def rget (N K p : ℕ) (w : List Bool) : List Bool := block (N * K) p w

/-- **The word of a matrix**: its entries in row-major order. -/
def matW (N K m n : ℕ) (M : Matrix (Fin m) (Fin n) (Rq N K)) : List Bool :=
  concatN (m * n) fun p =>
    if h : p < m * n then (ringEnc N K).enc (M ⟨p / n, div_lt_of_lt_mul' h⟩ ⟨p % n, mod_lt_of_lt_mul' h⟩)
    else []

theorem length_matW (m n : ℕ) (M : Matrix (Fin m) (Fin n) (Rq N K)) :
    (matW N K m n M).length = m * n * (N * K) :=
  length_concatN fun p hp => by rw [dite_eq_left_of_eq_true (eq_true hp)]; exact (ringEnc N K).length _

theorem rget_matW {m n : ℕ} (M : Matrix (Fin m) (Fin n) (Rq N K)) {p : ℕ} (hp : p < m * n) :
    rget N K p (matW N K m n M) =
      (ringEnc N K).enc (M ⟨p / n, div_lt_of_lt_mul' hp⟩ ⟨p % n, mod_lt_of_lt_mul' hp⟩) := by
  rw [rget, matW, block_concatN, ite_eq_left_of_eq_true _ _ (eq_true hp), dite_eq_left_of_eq_true (eq_true hp)]
  intro q hq; rw [dite_eq_left_of_eq_true (eq_true hq)]; exact (ringEnc N K).length _

theorem rget_matW' {m n : ℕ} (M : Matrix (Fin m) (Fin n) (Rq N K)) (i : Fin m) (j : Fin n) :
    rget N K (i.val * n + j.val) (matW N K m n M) = (ringEnc N K).enc (M i j) := by
  rw [rget_matW M (index_lt i j)]
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact j.elim0)
  congr 2
  · ext; simp only
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt j.isLt, zero_add]
  · ext; simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]

/-- A loop over the entries is the word of a matrix as soon as it writes the right entries. -/
theorem concatN_eq_matW {m n : ℕ} {f : ℕ → List Bool} (M : Matrix (Fin m) (Fin n) (Rq N K))
    (h : ∀ p (hp : p < m * n),
      f p = (ringEnc N K).enc (M ⟨p / n, div_lt_of_lt_mul' hp⟩ ⟨p % n, mod_lt_of_lt_mul' hp⟩)) :
    concatN (m * n) f = matW N K m n M := by
  apply concatN_congr
  intro p hp
  rw [dite_eq_left_of_eq_true (eq_true hp), h p hp]

/-! ### Entrywise operations -/

/-- Entrywise addition of words of `L` ring entries. -/
def matAddW (N K L : ℕ) (x y : List Bool) : List Bool :=
  concatN L fun p => addRW N K (rget N K p x) (rget N K p y)

/-- Entrywise subtraction. -/
def matSubW (N K L : ℕ) (x y : List Bool) : List Bool :=
  concatN L fun p => subRW N K (rget N K p x) (rget N K p y)

theorem matAddW_enc {m n : ℕ} (A B : Matrix (Fin m) (Fin n) (Rq N K)) :
    matAddW N K (m * n) (matW N K m n A) (matW N K m n B) = matW N K m n (A + B) :=
  concatN_eq_matW _ fun p hp => by rw [rget_matW A hp, rget_matW B hp, addRW_enc]; rfl

theorem matSubW_enc {m n : ℕ} (A B : Matrix (Fin m) (Fin n) (Rq N K)) :
    matSubW N K (m * n) (matW N K m n A) (matW N K m n B) = matW N K m n (A - B) :=
  concatN_eq_matW _ fun p hp => by rw [rget_matW A hp, rget_matW B hp, subRW_enc]; rfl

/-! ### Products -/

/-- The accumulation loop `acc := 0; for t < n: acc += f t` on ring words. -/
def sumLoop (N K : ℕ) (f : ℕ → List Bool) : ℕ → List Bool
  | 0 => zeroW (N * K)
  | t + 1 => addRW N K (sumLoop N K f t) (f t)

theorem sumLoop_enc {n : ℕ} {f : ℕ → List Bool} (g : ℕ → Rq N K)
    (hf : ∀ t < n, f t = (ringEnc N K).enc (g t)) :
    ∀ t ≤ n, sumLoop N K f t = (ringEnc N K).enc (∑ t' ∈ Finset.range t, g t')
  | 0, _ => by simp [sumLoop, enc_zeroR]
  | t + 1, ht => by
    rw [sumLoop, sumLoop_enc g hf t (by omega), hf t (by omega), addRW_enc,
      Finset.sum_range_succ]

/-- **Matrix product** of an `m × n` and an `n × l` matrix word. -/
def matMulW (N K m n l : ℕ) (x y : List Bool) : List Bool :=
  concatN (m * l) fun p =>
    sumLoop N K (fun t => mulRW N K (rget N K (p / l * n + t) x) (rget N K (t * l + p % l) y)) n

theorem matMulW_enc {m n l : ℕ} (A : Matrix (Fin m) (Fin n) (Rq N K))
    (B : Matrix (Fin n) (Fin l) (Rq N K)) :
    matMulW N K m n l (matW N K m n A) (matW N K n l B) = matW N K m l (A * B) := by
  apply concatN_eq_matW
  intro p hp
  set i : Fin m := ⟨p / l, div_lt_of_lt_mul' hp⟩
  set j : Fin l := ⟨p % l, mod_lt_of_lt_mul' hp⟩
  rw [sumLoop_enc (n := n) (fun t => if h : t < n then A i ⟨t, h⟩ * B ⟨t, h⟩ j else 0)
    (fun t ht => by
      rw [dite_eq_left_of_eq_true (eq_true ht), ← mulRW_enc, ← rget_matW' A i ⟨t, ht⟩, ← rget_matW' B ⟨t, ht⟩ j]) n le_rfl]
  congr 1
  rw [Matrix.mul_apply, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [dite_eq_left_of_eq_true (eq_true t.isLt)]

/-! ### The gadget columns -/

/-- The gadget columns in the order of their enumeration: `p ↦ (p / k, p % k)`. -/
def colE (k : ℕ) : Fin (2 * k) ≃ Fin 2 × Fin k := finProdFinEquiv.symm

theorem colE_apply (k : ℕ) (p : Fin (2 * k)) :
    colE k p = (⟨p.val / k, div_lt_of_lt_mul' p.isLt⟩, ⟨p.val % k, mod_lt_of_lt_mul' p.isLt⟩) := by
  simp only [colE, finProdFinEquiv_symm_apply]
  rfl

/-- The word of a row `1 × Col k`. -/
def rowW (N K k : ℕ) (B : Matrix (Fin 1) (Fin 2 × Fin k) (Rq N K)) : List Bool :=
  matW N K 1 (2 * k) (B.submatrix id (colE k))

/-- The word of a matrix `Col k × Col k`. -/
def sqW (N K k : ℕ) (M : Matrix (Fin 2 × Fin k) (Fin 2 × Fin k) (Rq N K)) : List Bool :=
  matW N K (2 * k) (2 * k) (M.submatrix (colE k) (colE k))

theorem rget_rowW {k : ℕ} (B : Matrix (Fin 1) (Fin 2 × Fin k) (Rq N K)) {p : ℕ} (hp : p < 2 * k) :
    rget N K p (rowW N K k B) =
      (ringEnc N K).enc (B 0 (⟨p / k, div_lt_of_lt_mul' hp⟩, ⟨p % k, mod_lt_of_lt_mul' hp⟩)) := by
  have h := rget_matW' (B.submatrix id (colE k)) 0 ⟨p, hp⟩
  simp only [Fin.val_zero, zero_mul, zero_add] at h
  rw [rowW, h, submatrix_apply, id, colE_apply]

/-! ### The binary top-row gadget -/

variable (hk : 2 ^ K ≤ 2 ^ k)

/-- The binary top-row gadget `G̲ ∈ R_q^{1 × Col k}` and its decomposition. -/
noncomputable abbrev topBin (N K k : ℕ) (hk : 2 ^ K ≤ 2 ^ k) :
    GadgetMatrix (Rq N K) (Fin 1) (Fin 2 × Fin k) :=
  topRowGadget (binaryDigits N (2 ^ K) k hk)

theorem topBin_ginv_apply (A : Matrix (Fin 1) (Fin 2 × Fin k) (Rq N K)) (c col : Fin 2 × Fin k) :
    (topBin N K k hk).ginv A c col = if c.1 = 0 then binaryDigit (A 0 col) c.2 else 0 := by
  simp only [topBin, topRowGadget, gadgetOf, Matrix.of_apply, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_singleton, binaryDigits, eq_comm (a := (0 : Fin 2))]

theorem topBin_G_apply (col : Fin 2 × Fin k) :
    (topBin N K k hk).G 0 col =
      if col.1 = 0 then algebraMap (ZMod (2 ^ K)) (Rq N K) (2 ^ (col.2 : ℕ)) else 0 := by
  simp only [topBin, topRowGadget, gadgetOf, Matrix.of_apply, binaryDigits,
    eq_comm (a := (0 : Fin 2))]

/-- **`G̲⁻¹` on words**: the `Col k × Col k` matrix of the binary digits of a row. -/
def ginvW (N K k : ℕ) (b : List Bool) : List Bool :=
  concatN (2 * k * (2 * k)) fun p =>
    if p / (2 * k) / k = 0 then digitRW N K (p / (2 * k) % k) (rget N K (p % (2 * k)) b)
    else zeroW (N * K)

theorem ginvW_enc (B : Matrix (Fin 1) (Fin 2 × Fin k) (Rq N K)) :
    ginvW N K k (rowW N K k B) = sqW N K k ((topBin N K k hk).ginv B) := by
  apply concatN_eq_matW
  intro p hp
  rw [submatrix_apply, topBin_ginv_apply, colE_apply, colE_apply]
  dsimp only
  have hc := div_lt_of_lt_mul' hp
  split_ifs with h1 h2 h2
  · rw [rget_rowW B (mod_lt_of_lt_mul' hp), digitRW_enc]
  · exact absurd (Fin.ext h1) h2
  · exact absurd (congrArg Fin.val h2) h1
  · exact (enc_zeroR N K).symm

/-- **The gadget row `G̲`** on words: `2^i` (a constant) at the column `(0, i)`, zero elsewhere. -/
def gadW (N K k : ℕ) : List Bool :=
  concatN (1 * (2 * k)) fun p =>
    if p / k = 0 then constW N K (powW K (p % k)) else zeroW (N * K)

theorem gadW_enc : gadW N K k = rowW N K k (topBin N K k hk).G := by
  apply concatN_eq_matW
  intro p hp
  rw [submatrix_apply, id, show (⟨p / (2 * k), div_lt_of_lt_mul' hp⟩ : Fin 1) = 0 from
    Subsingleton.elim _ _, topBin_G_apply, colE_apply]
  dsimp only
  have hp' : p < 2 * k := by simpa using hp
  have hm : p % (2 * k) = p := Nat.mod_eq_of_lt hp'
  simp only [hm]
  split_ifs with h1 h2 h2
  · rw [enc_algebraMap, enc_pow]
  · exact absurd (Fin.ext h1) h2
  · exact absurd (congrArg Fin.val h2) h1
  · exact (enc_zeroR N K).symm

/-- **The BGG+ NAND of public keys** on words: `G̲ − A G̲⁻¹(B)`. -/
def nandPKW (N K k : ℕ) (a b : List Bool) : List Bool :=
  matSubW N K (1 * (2 * k)) (gadW N K k) (matMulW N K 1 (2 * k) (2 * k) a (ginvW N K k b))

theorem nandPKW_enc (A B : Matrix (Fin 1) (Fin 2 × Fin k) (Rq N K)) :
    nandPKW N K k (rowW N K k A) (rowW N K k B) =
      rowW N K k ((topBin N K k hk).G - A * (topBin N K k hk).ginv B) := by
  rw [nandPKW, ginvW_enc hk, gadW_enc hk]
  simp only [rowW, sqW]
  rw [matMulW_enc, matSubW_enc, submatrix_mul_equiv]
  rfl

/-! ### Step counts -/

/-- Steps of `sumLoop` over `n` terms: the zero word, then one ring addition per term. -/
def sumSteps (N K n : ℕ) : ℕ := N * K + n * addRSteps N K

/-- Steps of `matMulW`: per entry, `n` ring multiplications (with two block copies each) and
their sum. -/
def matMulSteps (N K m n l : ℕ) : ℕ :=
  m * l * (n * (2 * (N * K) + mulRSteps N K) + sumSteps N K n)

/-- Steps of `ginvW`: per entry, a block copy and either the digits (one bit copy per
coefficient bit) or a zero word. -/
def ginvSteps (N K k : ℕ) : ℕ := 2 * k * (2 * k) * (N * K + N * K)

/-- Steps of `gadW`. -/
def gadSteps (N K k : ℕ) : ℕ := 2 * k * (N * K)

/-- Steps of `nandPKW`. -/
def nandPKSteps (N K k : ℕ) : ℕ :=
  gadSteps N K k + ginvSteps N K k + matMulSteps N K 1 (2 * k) (2 * k) + addRSteps N K * (2 * k)

end SigabaNeo.Lattices.Algo
