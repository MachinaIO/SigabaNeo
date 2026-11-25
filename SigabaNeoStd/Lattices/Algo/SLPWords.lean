import SigabaNeoStd.Lattices.Algo.MatWords
import SigabaNeoStd.Lattices.Homomorphic.SLPEval

/-!
# BGG+ public keys of programs and key matrices, on words

* `slpPKW`: `EvalF` of a straight-line program on the words of the input public keys: the run
  `SLP.valueOf` (one value per gate, in order) with the NAND `nandPKW` on words
  (`slpPKW_enc : slpPKW (rowW ∘ Bj) p w = rowW (slpPK G̲ Bj p w)`).
* `keySumW`: the sum `∑_b PK_b · G̲⁻¹(V_b)` over the bits `b = (0, c, i, j)` of a row
  (`coeffBits`, with `V_b = 2^i X^j` at the column `c`), as three nested accumulation loops
  (`keySumW_enc`). With `PK_b` the public key of the output wire `b` of `f̂` this is the key matrix
  `B_f̂` (`PE/Impl/RingBTVW/Algo/KeyMatrix`).

Step counts: `slpPKSteps` (per gate), `keySumSteps`.
-/

namespace SigabaNeo.Lattices.Algo

open SigabaNeo.Encode Cslib Matrix

variable {N K k : ℕ} (hk : 2 ^ K ≤ 2 ^ k)

/-! ### `EvalF` on words -/

/-- **`EvalF` on words**: the public key of a wire, from the words of the input public keys. -/
def slpPKW {ι : Type*} (N K k : ℕ) (bj : ι → List Bool) (p : SLP ι) (w : Wire ι) : List Bool :=
  SLP.valueOf bj (gadW N K k) (nandPKW N K k) p w

theorem slpPKW_enc {ι : Type*} (Bj : ι → Matrix (Fin 1) (Fin 2 × Fin k) (Rq N K)) (p : SLP ι)
    (w : Wire ι) :
    slpPKW N K k (fun i => rowW N K k (Bj i)) p w = rowW N K k (slpPK (topBin N K k hk) Bj p w) :=
  (SLP.valueOf_map Bj _ _ _ _ _ (rowW N K k) (fun _ => rfl) (gadW_enc hk).symm
    (fun a b => (nandPKW_enc hk a b).symm) p w).symm

/-- Steps of `slpPKW` on a program of `g` gates: one NAND per gate, plus copying the two read
public keys (`2k` ring words each). -/
def slpPKSteps (N K k g : ℕ) : ℕ := g * (nandPKSteps N K k + 2 * (2 * k * (N * K)))

/-! ### Rows of zeros and sums of rows -/

theorem concatN_zeroW (n m : ℕ) : concatN n (fun _ => zeroW m) = zeroW (n * m) := by
  induction n with
  | zero => simp [concatN, zeroW]
  | succ n ih => rw [concatN, ih, Nat.succ_mul]; simp only [zeroW, List.replicate_append_replicate]

theorem rowW_zero : rowW N K k 0 = zeroW (1 * (2 * k) * (N * K)) := by
  rw [← concatN_zeroW]
  symm
  apply concatN_eq_matW
  intro p _
  exact (enc_zeroR N K).symm

/-- The accumulation loop `acc := 0; for t < n: acc += f t` on row words. -/
def rowSum (N K k : ℕ) (f : ℕ → List Bool) : ℕ → List Bool
  | 0 => zeroW (1 * (2 * k) * (N * K))
  | t + 1 => matAddW N K (1 * (2 * k)) (rowSum N K k f t) (f t)

theorem rowSum_enc {n : ℕ} {f : ℕ → List Bool} (g : ℕ → Matrix (Fin 1) (Fin 2 × Fin k) (Rq N K))
    (hf : ∀ t < n, f t = rowW N K k (g t)) :
    ∀ t ≤ n, rowSum N K k f t = rowW N K k (∑ t' ∈ Finset.range t, g t')
  | 0, _ => by simp [rowSum, rowW_zero]
  | t + 1, ht => by
    rw [rowSum, rowSum_enc g hf t (by omega), hf t (by omega), rowW, rowW, matAddW_enc,
      Finset.sum_range_succ, rowW]
    rfl

theorem rowSum_fin {n : ℕ} {f : ℕ → List Bool} (g : Fin n → Matrix (Fin 1) (Fin 2 × Fin k) (Rq N K))
    (hf : ∀ t (ht : t < n), f t = rowW N K k (g ⟨t, ht⟩)) :
    rowSum N K k f n = rowW N K k (∑ t, g t) := by
  rw [rowSum_enc (fun t => if h : t < n then g ⟨t, h⟩ else 0)
    (fun t ht => by rw [dite_eq_left_of_eq_true (eq_true ht)]; exact hf t ht) n le_rfl, ← Fin.sum_univ_eq_sum_range]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [dite_eq_left_of_eq_true (eq_true t.isLt)]

/-! ### The rows `V_b` of the bits of a row -/

/-- The word of the monomial `2^i X^j`. -/
theorem monoW_enc (i : ℕ) (j : Fin N) :
    monoW N K j (powW K i) = (ringEnc N K).enc (monomial N (2 ^ K) i j) := by
  apply eq_ringEnc
  · intro t _; split_ifs <;> simp [powW]
  · intro t ht
    simp only [monomial, Negacyclic.coeffs_ofCoeffs, Pi.single_apply, Fin.ext_iff]
    split_ifs with h
    · rw [← enc_pow, dec_enc]
    · simp [dec, val_zeroW]

/-- The word of `V_{(0,c,i,j)}`: the monomial `2^i X^j` at the column `c`. -/
def vW (N K k c i j : ℕ) : List Bool :=
  concatN (1 * (2 * k)) fun p => if p = c then monoW N K j (powW K i) else zeroW (N * K)

theorem vW_enc (c : Fin (2 * k)) (i : Fin k) (j : Fin N) :
    vW N K k c i j = rowW N K k ((coeffBits N (2 ^ K) k hk (Fin 1) (Fin 2 × Fin k)).V
      (0, colE k c, i, j)) := by
  apply concatN_eq_matW
  intro p hp
  have hp' : p < 2 * k := by simpa using hp
  simp only [submatrix_apply, id, coeffBits, Matrix.of_apply]
  have hm : p % (2 * k) = p := Nat.mod_eq_of_lt hp'
  by_cases hpc : p = c.val
  · have : (⟨p % (2 * k), mod_lt_of_lt_mul' hp⟩ : Fin (2 * k)) = c := Fin.ext (by rw [Fin.val_mk, hm, hpc])
    rw [ite_eq_left_of_eq_true _ _ (eq_true hpc), this, ite_eq_left_of_eq_true _ _ (eq_true ⟨Subsingleton.elim _ _, rfl⟩), monoW_enc]
  · have : (⟨p % (2 * k), mod_lt_of_lt_mul' hp⟩ : Fin (2 * k)) ≠ c := by
      intro h; apply hpc; rw [← h]; simp [hm]
    rw [ite_eq_right_of_eq_false _ _ (eq_false hpc),
      ite_eq_right_of_eq_false _ _ (eq_false (fun h => this ((colE k).injective h.2))), enc_zeroR]

/-! ### Key matrices -/

/-- **The key-matrix loop**: `∑_{c < 2k} ∑_{i < k} ∑_{j < N} PK_{c,i,j} · G̲⁻¹(V_{c,i,j})`. -/
def keySumW (N K k : ℕ) (pkW : ℕ → ℕ → ℕ → List Bool) : List Bool :=
  rowSum N K k (fun c => rowSum N K k (fun i => rowSum N K k (fun j =>
    matMulW N K 1 (2 * k) (2 * k) (pkW c i j) (ginvW N K k (vW N K k c i j))) N) k) (2 * k)

theorem rowW_mul_ginv (A B : Matrix (Fin 1) (Fin 2 × Fin k) (Rq N K)) :
    matMulW N K 1 (2 * k) (2 * k) (rowW N K k A) (ginvW N K k (rowW N K k B)) =
      rowW N K k (A * (topBin N K k hk).ginv B) := by
  rw [ginvW_enc hk, rowW, sqW, matMulW_enc, submatrix_mul_equiv, rowW]

/-- **The key-matrix loop computes `∑_b PK_b · G̲⁻¹(V_b)`.** -/
theorem keySumW_enc (pk : Fin 1 × (Fin 2 × Fin k) × Fin k × Fin N →
      Matrix (Fin 1) (Fin 2 × Fin k) (Rq N K))
    (pkW : ℕ → ℕ → ℕ → List Bool)
    (hpk : ∀ (c : Fin (2 * k)) (i : Fin k) (j : Fin N), pkW c i j = rowW N K k (pk (0, colE k c, i, j))) :
    keySumW N K k pkW = rowW N K k (∑ b, pk b *
      (topBin N K k hk).ginv ((coeffBits N (2 ^ K) k hk (Fin 1) (Fin 2 × Fin k)).V b)) := by
  have hsum : (∑ b, pk b *
      (topBin N K k hk).ginv ((coeffBits N (2 ^ K) k hk (Fin 1) (Fin 2 × Fin k)).V b)) =
      ∑ c : Fin (2 * k), ∑ i : Fin k, ∑ j : Fin N, pk (0, colE k c, i, j) *
        (topBin N K k hk).ginv ((coeffBits N (2 ^ K) k hk (Fin 1) (Fin 2 × Fin k)).V
          (0, colE k c, i, j)) := by
    rw [Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero,
      Fintype.sum_prod_type, ← (colE k).sum_comp]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Fintype.sum_prod_type]
  rw [hsum, keySumW]
  apply rowSum_fin
  intro c hc
  apply rowSum_fin
  intro i hi
  apply rowSum_fin
  intro j hj
  rw [hpk ⟨c, hc⟩ ⟨i, hi⟩ ⟨j, hj⟩, vW_enc hk ⟨c, hc⟩ ⟨i, hi⟩ ⟨j, hj⟩, rowW_mul_ginv hk]

/-- Steps of `vW`. -/
def vSteps (N K k : ℕ) : ℕ := 2 * k * (N * K)

/-- Steps of `keySumW`: per bit `(c, i, j)` the row `V`, its decomposition, the product, and the
addition; plus the zero rows. -/
def keySumSteps (N K k : ℕ) : ℕ :=
  2 * k * k * N * (vSteps N K k + ginvSteps N K k + matMulSteps N K 1 (2 * k) (2 * k) +
    2 * k * addRSteps N K) + (1 + 2 * k + 2 * k * k) * (2 * k * (N * K))

end SigabaNeo.Lattices.Algo
