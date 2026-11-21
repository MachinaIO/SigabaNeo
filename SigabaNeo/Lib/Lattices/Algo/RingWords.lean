import SigabaNeo.Lib.Lattices.Algo.Words
import Mathlib.Tactic.Linarith

/-!
# Negacyclic arithmetic on bit words

An element of `R_q = ℤ_{2^K}[X]/(X^N + 1)` is the word of its `N` coefficients of `K` bits
(`SigabaNeo.Encode.ringEnc`). The algorithms here are first-order loops over these words:

* `concatN n f`: the loop `for i < n: out ++= f i` (`ringEnc_enc`: the encoding is such a loop);
* `block K i w`: the `i`-th `K`-bit block of `w` (a coefficient);
* `addRW`, `subRW`: coefficient-wise addition and subtraction modulo `2^K` (`addRW_enc`, `subRW_enc`);
* `mulRW`: schoolbook negacyclic multiplication, `c_i = ∑_{j ≤ i} a_{i-j} b_j − ∑_{j > i} a_{N+i-j} b_j`,
  each coefficient an accumulation loop over `j < N` (`coefLoop`) of word products `mulW` and
  additions/subtractions (`mulRW_enc : mulRW N K (enc a) (enc b) = enc (a * b)`).

Step counts: `addRSteps`, `mulRSteps` (exact, along the recursion of the loops) with closed forms.
-/

namespace SigabaNeo.Lattices.Algo

open SigabaNeo.Encode Cslib

/-! ### Loops producing words -/

/-- The loop `for i < n: out ++= f i`. -/
def concatN : ℕ → (ℕ → List Bool) → List Bool
  | 0, _ => []
  | n + 1, f => concatN n f ++ f n

theorem concatN_congr {n : ℕ} {f g : ℕ → List Bool} (h : ∀ i < n, f i = g i) :
    concatN n f = concatN n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [concatN]
    rw [ih fun i hi => h i (by omega), h n (by omega)]

theorem length_concatN {n K : ℕ} {f : ℕ → List Bool} (h : ∀ i < n, (f i).length = K) :
    (concatN n f).length = n * K := by
  induction n with
  | zero => simp [concatN]
  | succ n ih =>
    simp only [concatN, List.length_append, ih fun i hi => h i (by omega), h n (by omega)]
    ring

theorem flatMap_finRange (n : ℕ) (f : Fin n → List Bool) :
    (List.finRange n).flatMap f = concatN n (fun i => if h : i < n then f ⟨i, h⟩ else []) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.finRange_succ_last, List.flatMap_append, List.flatMap_map, concatN]
    simp only [List.flatMap_singleton]
    rw [ih (fun i => f i.castSucc)]
    congr 1
    · apply concatN_congr
      intro i hi
      simp [hi, show i < n + 1 by omega]
    · simp [Fin.last]

/-- `Eq.mp` along an equality of lengths does not change an encoding. -/
theorem FixedEnc.enc_mp {β : Type} {n m : ℕ} (hnm : n = m) (h : FixedEnc β n = FixedEnc β m)
    (e : FixedEnc β n) : (h.mp e).enc = e.enc := by
  subst hnm; rfl

/-- The coefficient `i` of a ring element, and `0` past the last one. -/
def coefOf {N K : ℕ} (a : Negacyclic (ZMod (2 ^ K)) N) (i : ℕ) : ZMod (2 ^ K) :=
  if h : i < N then a.coeffs ⟨i, h⟩ else 0

/-- **The encoding of a ring element** is the loop writing its coefficients. -/
theorem ringEnc_enc (N K : ℕ) (a : Negacyclic (ZMod (2 ^ K)) N) :
    (ringEnc N K).enc a =
      concatN N (fun i => if h : i < N then (zmodEnc K).enc (a.coeffs ⟨i, h⟩) else []) := by
  unfold ringEnc
  simp only
  rw [FixedEnc.enc_mp (by simp [Enum.list])]
  show ((List.finRange N).map a.coeffs).flatMap (zmodEnc K).enc = _
  rw [List.flatMap_map, flatMap_finRange]

/-! ### Blocks -/

/-- The `i`-th block of `K` bits of a word. -/
def block (K i : ℕ) (w : List Bool) : List Bool := (w.drop (i * K)).take K

theorem length_block {N K i : ℕ} {w : List Bool} (hw : w.length = N * K) (hi : i < N) :
    (block K i w).length = K := by
  simp only [block, List.length_take, List.length_drop, hw]
  have : i * K + K ≤ N * K := by
    have := Nat.mul_le_mul_right K (show i + 1 ≤ N by omega); rw [Nat.add_mul] at this; simpa
  omega

theorem block_concatN {n K : ℕ} {f : ℕ → List Bool} (h : ∀ i < n, (f i).length = K) (i : ℕ) :
    block K i (concatN n f) = if i < n then f i else [] := by
  induction n with
  | zero => simp [block, concatN]
  | succ n ih =>
    have hl : (concatN n f).length = n * K := length_concatN fun j hj => h j (by omega)
    simp only [concatN, block]
    by_cases hin : i < n
    · have hle : i * K + K ≤ n * K := by
        have := Nat.mul_le_mul_right K (show i + 1 ≤ n by omega); rw [Nat.add_mul] at this; simpa
      rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length
        (by simp; omega), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      have := ih (fun j hj => h j (by omega))
      rw [ite_eq_left_of_eq_true _ _ (eq_true hin)] at this
      exact this
    · have hnK : n * K ≤ i * K := Nat.mul_le_mul_right K (by omega)
      rw [List.drop_append, hl, List.drop_eq_nil_of_le (by omega), List.nil_append]
      by_cases hn : i = n
      · subst hn
        simp [h i (by omega)]
      · have hiK : (n + 1) * K ≤ i * K := Nat.mul_le_mul_right K (by omega)
        rw [Nat.add_mul] at hiK
        rw [List.drop_eq_nil_of_le (by rw [h n (by omega)]; omega)]
        simp only [List.take_nil]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

theorem length_ringEnc (N K : ℕ) (a : Negacyclic (ZMod (2 ^ K)) N) :
    ((ringEnc N K).enc a).length = N * K := (ringEnc N K).length a

theorem block_ringEnc {N K : ℕ} (a : Negacyclic (ZMod (2 ^ K)) N) {i : ℕ} (hi : i < N) :
    block K i ((ringEnc N K).enc a) = (zmodEnc K).enc (a.coeffs ⟨i, hi⟩) := by
  rw [ringEnc_enc, block_concatN, ite_eq_left_of_eq_true _ _ (eq_true hi), dite_eq_left_of_eq_true (eq_true hi)]
  intro j hj
  simp [hj, (zmodEnc K).length]

theorem dec_block_ringEnc {N K : ℕ} (a : Negacyclic (ZMod (2 ^ K)) N) (i : ℕ) :
    dec K (block K i ((ringEnc N K).enc a)) = coefOf a i := by
  by_cases hi : i < N
  · rw [block_ringEnc a hi, dec_enc, coefOf, dite_eq_left_of_eq_true (eq_true hi)]
  · rw [ringEnc_enc, block_concatN, ite_eq_right_of_eq_false _ _ (eq_false hi), coefOf, dite_eq_right_of_eq_false (eq_false hi)]
    · simp [dec]
    · intro j hj
      simp [hj, (zmodEnc K).length]

/-- A word made of `N` blocks of `K` bits is the encoding of the element with the residues of its
blocks as coefficients. -/
theorem eq_ringEnc {N K : ℕ} {f : ℕ → List Bool} (hf : ∀ i < N, (f i).length = K)
    (a : Negacyclic (ZMod (2 ^ K)) N) (ha : ∀ i (h : i < N), dec K (f i) = a.coeffs ⟨i, h⟩) :
    concatN N f = (ringEnc N K).enc a := by
  rw [ringEnc_enc]
  apply concatN_congr
  intro i hi
  rw [dite_eq_left_of_eq_true (eq_true hi)]
  exact eq_enc_of_dec (hf i hi) (ha i hi)

/-! ### Addition and subtraction -/

/-- Coefficient-wise addition. -/
def addRW (N K : ℕ) (x y : List Bool) : List Bool :=
  concatN N (fun i => addW (block K i x) (block K i y))

/-- Coefficient-wise subtraction. -/
def subRW (N K : ℕ) (x y : List Bool) : List Bool :=
  concatN N (fun i => subW (block K i x) (block K i y))

theorem addRW_enc (N K : ℕ) (a b : Negacyclic (ZMod (2 ^ K)) N) :
    addRW N K ((ringEnc N K).enc a) ((ringEnc N K).enc b) = (ringEnc N K).enc (a + b) := by
  apply eq_ringEnc
  · intro i hi; simp [length_block (length_ringEnc N K a) hi]
  · intro i hi
    rw [dec_addW K (length_block (length_ringEnc N K a) hi), dec_block_ringEnc,
      dec_block_ringEnc, coefOf, coefOf, dite_eq_left_of_eq_true (eq_true hi), dite_eq_left_of_eq_true (eq_true hi)]
    rfl

theorem subRW_enc (N K : ℕ) (a b : Negacyclic (ZMod (2 ^ K)) N) :
    subRW N K ((ringEnc N K).enc a) ((ringEnc N K).enc b) = (ringEnc N K).enc (a - b) := by
  apply eq_ringEnc
  · intro i hi; simp [length_block (length_ringEnc N K a) hi]
  · intro i hi
    rw [dec_subW K (length_block (length_ringEnc N K a) hi)
      (length_block (length_ringEnc N K b) hi), dec_block_ringEnc,
      dec_block_ringEnc, coefOf, coefOf, dite_eq_left_of_eq_true (eq_true hi), dite_eq_left_of_eq_true (eq_true hi)]
    rfl

/-! ### Schoolbook negacyclic multiplication -/

/-- The accumulation loop of the coefficient `i` of a product, after the terms `j' < j`:
`acc += a_{i-j'} b_{j'}` if `j' ≤ i`, `acc -= a_{N+i-j'} b_{j'}` otherwise. -/
def coefLoop (N K : ℕ) (x y : List Bool) (i : ℕ) : ℕ → List Bool
  | 0 => zeroW K
  | j + 1 =>
    if j ≤ i then addW (coefLoop N K x y i j) (mulW (block K (i - j) x) (block K j y))
    else subW (coefLoop N K x y i j) (mulW (block K (N + i - j) x) (block K j y))

/-- **Schoolbook negacyclic multiplication.** -/
def mulRW (N K : ℕ) (x y : List Bool) : List Bool :=
  concatN N (fun i => coefLoop N K x y i N)

theorem length_coefLoop (N K : ℕ) (x y : List Bool) (i j : ℕ) :
    (coefLoop N K x y i j).length = K := by
  induction j with
  | zero => simp [coefLoop]
  | succ j ih => unfold coefLoop; split_ifs <;> simp [ih]

/-- The term `j` of the coefficient `i` of a negacyclic product. -/
def negaTerm (N : ℕ) {R : Type} [CommRing R] (A B : ℕ → R) (i j : ℕ) : R :=
  if j ≤ i then A (i - j) * B j else -(A (N + i - j) * B j)

theorem dec_coefLoop {N K : ℕ} (a b : Negacyclic (ZMod (2 ^ K)) N) {i : ℕ} (hi : i < N) :
    ∀ j, j ≤ N → dec K (coefLoop N K ((ringEnc N K).enc a) ((ringEnc N K).enc b) i j) =
      ∑ j' ∈ Finset.range j, negaTerm N (coefOf a) (coefOf b) i j'
  | 0, _ => by simp [coefLoop, dec_zeroW]
  | j + 1, hj => by
    have ih := dec_coefLoop a b hi j (by omega)
    rw [Finset.sum_range_succ, ← ih, coefLoop, negaTerm]
    have hacc := length_coefLoop N K ((ringEnc N K).enc a) ((ringEnc N K).enc b) i j
    split_ifs with hji
    · rw [dec_addW K hacc, dec_mulW K (length_block (length_ringEnc N K a) (by omega)),
        dec_block_ringEnc, dec_block_ringEnc]
    · rw [dec_subW K hacc (by rw [length_mulW, length_block (length_ringEnc N K a) (by omega)]),
        dec_mulW K (length_block (length_ringEnc N K a) (by omega)),
        dec_block_ringEnc, dec_block_ringEnc]
      ring

/-- The coefficients of a product, as the schoolbook sum. -/
theorem coeffs_mul_eq_sum {N K : ℕ} (a b : Negacyclic (ZMod (2 ^ K)) N) (i : ℕ) (hi : i < N) :
    (a * b).coeffs ⟨i, hi⟩ = ∑ j ∈ Finset.range N, negaTerm N (coefOf a) (coefOf b) i j := by
  rw [Negacyclic.coeffs_mul, negacyclicMul, Matrix.mulVec, dotProduct,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [rotMatrix, Matrix.of_apply, negaTerm, coefOf]
  have hj := j.isLt
  split_ifs with h1 h2 h3 <;> first | omega | simp_all

/-- **Negacyclic multiplication on words** computes the product of the ring. -/
theorem mulRW_enc (N K : ℕ) (a b : Negacyclic (ZMod (2 ^ K)) N) :
    mulRW N K ((ringEnc N K).enc a) ((ringEnc N K).enc b) = (ringEnc N K).enc (a * b) := by
  apply eq_ringEnc
  · intro i _; exact length_coefLoop _ _ _ _ _ _
  · intro i hi
    rw [dec_coefLoop a b hi N le_rfl, coeffs_mul_eq_sum a b i hi]

/-! ### Step counts -/

/-- Steps of `block`: copying `K` bits. -/
def blockSteps (K : ℕ) : ℕ := K

/-- Steps of `addRW` and `subRW`: per coefficient, two block copies and the operation. -/
def addRSteps (N K : ℕ) : ℕ := N * (2 * blockSteps K + subSteps K)

/-- Steps of `coefLoop … i j`, along its recursion. -/
def coefLoopSteps (N K i : ℕ) : ℕ → ℕ
  | 0 => K
  | j + 1 => coefLoopSteps N K i j + (2 * blockSteps K + mulSteps K) +
      (if j ≤ i then addSteps K else subSteps K)

/-- Steps of `mulRW`. -/
def mulRStepsOf (N K : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => mulRStepsOf N K i + coefLoopSteps N K i N

theorem coefLoopSteps_le (N K i j : ℕ) :
    coefLoopSteps N K i j ≤ K + j * (2 * K + mulSteps K + 2 * K) := by
  induction j with
  | zero => simp [coefLoopSteps]
  | succ j ih =>
    simp only [coefLoopSteps, blockSteps]
    have : (if j ≤ i then addSteps K else subSteps K) ≤ 2 * K := by
      split_ifs <;> simp [addSteps, subSteps] <;> omega
    nlinarith

/-- **Steps of the multiplication** of two ring elements. -/
def mulRSteps (N K : ℕ) : ℕ := mulRStepsOf N K N

/-- `mulRSteps N K ≤ N (K + N (3K² + 5K))`: quadratic in `N`, quadratic in `K`. -/
theorem mulRSteps_le (N K : ℕ) : mulRSteps N K ≤ N * (K + N * (3 * K * K + 5 * K)) := by
  have h : ∀ n, mulRStepsOf N K n ≤ n * (K + N * (3 * K * K + 5 * K)) := by
    intro n
    induction n with
    | zero => simp [mulRStepsOf]
    | succ n ih =>
      simp only [mulRStepsOf]
      have := coefLoopSteps_le N K n N
      rw [mulSteps_eq] at this
      nlinarith
  exact h N

end SigabaNeo.Lattices.Algo
