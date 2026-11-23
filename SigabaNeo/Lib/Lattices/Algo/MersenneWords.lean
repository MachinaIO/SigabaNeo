import SigabaNeo.Lib.Lattices.Algo.NegaG

/-!
# One's-complement arithmetic on bit words: `ℤ_{2^K − 1}[X]/(X^N + 1)`

A residue modulo the Mersenne number `q = 2^K − 1` is **any** `K`-bit word `w` (least significant
bit first), read as `decM K w = val w mod (2^K − 1)`: every residue has a word, `0` has two (all
zeros, all ones). The operations keep the width `K` and are correct for every representative:

* `notW` (bitwise NOT) is the negation (`decM_notW`), since `val (¬w) + val w = 2^K − 1`;
* `addMW x y`: `K`-bit addition with **end-around carry** (`decM_addMW`): the carry out of `x + y`
  is added back in (`2^K ≡ 1`), by a second addition with that carry in;
* `subMW x y = addMW x (¬y)` (`decM_subMW`);
* `rot1 w`: the rotation by one bit towards the least significant end, the multiplication by
  `2⁻¹` (`two_mul_decM_rot1`); `rot1^[K − i]` multiplies by `2^i` (`decM_rot1_iter_sub`);
* `mulMW x y`: shift-and-add over the bits `y_0, y_1, …` of `y` with a rotation after each step,
  `acc ← (acc + y_i x) / 2`, so after the `K` bits `acc = 2^{−K} x y = x y` (`decM_mulMW`).

`encM K x` is the canonical word of a residue (`decM_encM`).

A ring element is `N` blocks of `K` bits (`decRM N K w : Negacyclic (ZMod (2^K − 1)) N`, the
residues of the blocks). Ring-word identities: `decRM_addRMW`, `decRM_subRMW`, `decRM_notW`
(negation), `decRM_scRMW` (residue × ring), `decRM_rotBW` (multiplication by `2^i`, e.g.
`W⁻¹ = 2^{K − b}`, by a rotation of every block), `decRM_rho` / `decRM_rhoAdd` (`X⁻¹ e` and
`X⁻¹ (e + a)` from the word `e.drop K ++ ¬(…)`), `decRM_digitRW` / `sum_pow_digitRW` (the binary
gadget digits are the bits).
-/

namespace SigabaNeo.Lattices.Algo

open Cslib NegaG

/-! ### Residues -/

/-- The residue modulo `2^K − 1` of a word. -/
def decM (K : ℕ) (w : List Bool) : ZMod (2 ^ K - 1) := (val w : ZMod (2 ^ K - 1))

/-- `2^K = 1` modulo `2^K − 1`. -/
theorem two_pow_eq_one_M (K : ℕ) : (2 : ZMod (2 ^ K - 1)) ^ K = 1 := by
  have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have h : ((2 ^ K - 1 : ℕ) : ZMod (2 ^ K - 1)) = 0 := ZMod.natCast_self _
  have h2 : ((2 ^ K : ℕ) : ZMod (2 ^ K - 1)) = ((2 ^ K - 1 : ℕ) : ZMod (2 ^ K - 1)) + 1 := by
    rw [← Nat.cast_one (R := ZMod _), ← Nat.cast_add, Nat.sub_add_cancel h1]
  rw [h, zero_add] at h2
  exact_mod_cast h2

theorem val_append (u v : List Bool) : val (u ++ v) = val u + 2 ^ u.length * val v := by
  induction u with
  | nil => simp
  | cons b u ih => simp only [List.cons_append, val_cons, ih, List.length_cons, pow_succ]; ring

theorem decM_zeroW (K : ℕ) : decM K (zeroW K) = 0 := by simp [decM, val_zeroW]

/-- **Negation is bitwise NOT.** -/
theorem decM_notW {K : ℕ} {y : List Bool} (hy : y.length = K) : decM K (notW y) = -decM K y := by
  have h := congrArg (fun n : ℕ => (n : ZMod (2 ^ K - 1))) (val_notW y)
  simp only [Nat.cast_add, Nat.cast_one, hy, Nat.cast_pow, Nat.cast_ofNat,
    two_pow_eq_one_M] at h
  simp only [decM]
  linear_combination h

@[simp] theorem length_notW (y : List Bool) : (notW y).length = y.length := by simp [notW]

/-- The carry out of `x + y` on the width of `x`. -/
def carryW (x y : List Bool) : Bool := decide (2 ^ x.length ≤ val x + val y)

/-- **Addition with end-around carry**: `x + y + c` with `c` the carry out of `x + y`. -/
def addMW (x y : List Bool) : List Bool := addc (carryW x y) x y

@[simp] theorem length_addMW (x y : List Bool) : (addMW x y).length = x.length := length_addc _ _ _

theorem val_addMW {x y : List Bool} (hy : y.length = x.length) :
    val (addMW x y) + 2 ^ x.length * (carryW x y).toNat = val x + val y + (carryW x y).toNat := by
  have hx := val_lt x
  have hy' := val_lt y
  rw [hy] at hy'
  rw [addMW, val_addc]
  unfold carryW
  generalize 2 ^ x.length = P at hx hy' ⊢
  by_cases h : P ≤ val x + val y
  · simp only [h, decide_true, Bool.toNat_true, mul_one]
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [h, decide_false, Bool.toNat_false, mul_zero, add_zero]
    rw [Nat.mod_eq_of_lt (by omega)]

/-- **One's-complement addition** is the addition modulo `2^K − 1`. -/
theorem decM_addMW {K : ℕ} {x y : List Bool} (hx : x.length = K) (hy : y.length = K) :
    decM K (addMW x y) = decM K x + decM K y := by
  have h := congrArg (fun n : ℕ => (n : ZMod (2 ^ K - 1))) (val_addMW (hy.trans hx.symm))
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hx,
    two_pow_eq_one_M, one_mul] at h
  simp only [decM]
  linear_combination h

/-- Subtraction: `x + ¬y`. -/
def subMW (x y : List Bool) : List Bool := addMW x (notW y)

@[simp] theorem length_subMW (x y : List Bool) : (subMW x y).length = x.length := length_addc _ _ _

theorem decM_subMW {K : ℕ} {x y : List Bool} (hx : x.length = K) (hy : y.length = K) :
    decM K (subMW x y) = decM K x - decM K y := by
  rw [subMW, decM_addMW hx (by simp [hy]), decM_notW hy, sub_eq_add_neg]

/-! ### Rotations: multiplication by powers of `2` -/

/-- The rotation by one bit towards the first (least significant) bit: the multiplication by
`2⁻¹`. -/
def rot1 (w : List Bool) : List Bool := (w ++ w.take 1).tail

@[simp] theorem length_rot1 (w : List Bool) : (rot1 w).length = w.length := by
  cases w <;> simp [rot1]

@[simp] theorem length_rot1_iter (w : List Bool) (j : ℕ) : (rot1^[j] w).length = w.length := by
  induction j generalizing w with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply, ih, length_rot1]

theorem two_mul_decM_rot1 {K : ℕ} {w : List Bool} (hw : w.length = K) :
    2 * decM K (rot1 w) = decM K w := by
  cases w with
  | nil => simp [rot1, decM]
  | cons b w =>
    simp only [List.length_cons] at hw
    subst hw
    have h1 := two_pow_eq_one_M (w.length + 1)
    simp only [rot1, List.take_succ_cons, List.take_zero, List.cons_append, List.tail_cons, decM,
      val_append, val_cons, val_nil] at h1 ⊢
    push_cast
    cases b
    · simp
    · simp only [Bool.toNat_true, Nat.cast_one]
      linear_combination h1

theorem pow_mul_decM_rot1_iter {K : ℕ} {w : List Bool} (hw : w.length = K) :
    ∀ j : ℕ, 2 ^ j * decM K (rot1^[j] w) = decM K w
  | 0 => by simp
  | j + 1 => by
    rw [Function.iterate_succ_apply', pow_succ, mul_assoc,
      two_mul_decM_rot1 (by rw [length_rot1_iter, hw]), pow_mul_decM_rot1_iter hw j]

/-- `rot1^[K − i]` **multiplies by `2^i`** (`i ≤ K`). -/
theorem decM_rot1_iter_sub {K i : ℕ} {w : List Bool} (hw : w.length = K) (hi : i ≤ K) :
    decM K (rot1^[K - i] w) = 2 ^ i * decM K w := by
  rw [← pow_mul_decM_rot1_iter hw (K - i), ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hi,
    two_pow_eq_one_M, one_mul]

/-! ### Multiplication -/

/-- Shift-and-add with a rotation per bit: `acc ← (acc + y_i x) / 2`. -/
def mulAcc (x : List Bool) : List Bool → List Bool → List Bool
  | acc, [] => acc
  | acc, b :: ys => mulAcc x (rot1 (cond b (addMW acc x) acc)) ys

/-- **One's-complement multiplication**, on the width of `x`. -/
def mulMW (x y : List Bool) : List Bool := mulAcc x (zeroW x.length) y

theorem length_mulAcc (x : List Bool) :
    ∀ (ys acc : List Bool), acc.length = x.length → (mulAcc x acc ys).length = x.length
  | [], acc, h => h
  | b :: ys, acc, h => length_mulAcc x ys _ (by cases b <;> simp [h])

@[simp] theorem length_mulMW (x y : List Bool) : (mulMW x y).length = x.length :=
  length_mulAcc x y _ (by simp)

theorem decM_mulAcc {K : ℕ} {x : List Bool} (hx : x.length = K) :
    ∀ (ys acc : List Bool), acc.length = K →
      2 ^ ys.length * decM K (mulAcc x acc ys) = decM K acc + decM K x * (val ys : ZMod _)
  | [], acc, _ => by simp [mulAcc]
  | b :: ys, acc, ha => by
    have hc : (cond b (addMW acc x) acc).length = K := by cases b <;> simp [ha]
    have ih := decM_mulAcc hx ys (rot1 (cond b (addMW acc x) acc)) (by rw [length_rot1]; exact hc)
    have h2 := two_mul_decM_rot1 hc
    simp only [mulAcc, List.length_cons, pow_succ, val_cons]
    rw [mul_comm _ (2 : ZMod _), mul_assoc, ih, mul_add, h2]
    cases b
    · simp only [Bool.cond_false, Bool.toNat_false]; push_cast; ring
    · simp only [Bool.cond_true, decM_addMW ha hx, Bool.toNat_true]; push_cast; ring

/-- **The product modulo `2^K − 1`.** -/
theorem decM_mulMW {K : ℕ} {x y : List Bool} (hx : x.length = K) (hy : y.length = K) :
    decM K (mulMW x y) = decM K x * decM K y := by
  have h := decM_mulAcc hx y (zeroW x.length) (by simp [hx])
  rw [hy, two_pow_eq_one_M, one_mul, hx, decM_zeroW, zero_add] at h
  rw [mulMW, hx, h]; rfl

/-! ### The canonical word of a residue -/

/-- The canonical word of a residue: the bits of its representative in `[0, 2^K − 1)`. -/
def encM (K : ℕ) (x : ZMod (2 ^ K - 1)) : List Bool := toBits K x.val

@[simp] theorem length_encM (K : ℕ) (x : ZMod (2 ^ K - 1)) : (encM K x).length = K := by
  simp [encM]

theorem decM_encM {K : ℕ} (hK : 0 < K) (x : ZMod (2 ^ K - 1)) : decM K (encM K x) = x := by
  have : NeZero (2 ^ K - 1) := ⟨by have := Nat.one_lt_two_pow (n := K) (by omega); omega⟩
  have hlt : x.val < 2 ^ K := (ZMod.val_lt x).trans_le (Nat.sub_le _ _)
  rw [encM, decM, val_toBits, Nat.mod_eq_of_lt hlt, ZMod.natCast_zmod_val]

/-! ### Ring words -/

/-- The element of `ℤ_{2^K − 1}[X]/(X^N + 1)` read from a word: the residues of its blocks. -/
def decRM (N K : ℕ) (w : List Bool) : Negacyclic (ZMod (2 ^ K - 1)) N :=
  Negacyclic.ofCoeffs fun i => decM K (block K i w)

theorem coefG_decRM {N K : ℕ} (w : List Bool) {i : ℕ} (hi : i < N) :
    coefG (decRM N K w) i = decM K (block K i w) := by
  simp [decRM, coefG, hi]

theorem decRM_concatN {N K : ℕ} {f : ℕ → List Bool} (hf : ∀ i < N, (f i).length = K) :
    decRM N K (concatN N f) = Negacyclic.ofCoeffs fun i => decM K (f i) := by
  unfold decRM
  congr 1
  funext i
  rw [block_concatN hf, mIfT i.isLt]

/-- The canonical word of a ring element. -/
def encRM (N K : ℕ) (a : Negacyclic (ZMod (2 ^ K - 1)) N) : List Bool :=
  concatN N fun i => encM K (coefG a i)

theorem length_encRM (N K : ℕ) (a : Negacyclic (ZMod (2 ^ K - 1)) N) :
    (encRM N K a).length = N * K := length_concatN fun _ _ => length_encM _ _

theorem decRM_encRM {N K : ℕ} (hK : 0 < K) (a : Negacyclic (ZMod (2 ^ K - 1)) N) :
    decRM N K (encRM N K a) = a := by
  rw [encRM, decRM_concatN fun _ _ => length_encM _ _]
  apply ext_coefG
  intro i hi
  rw [coefG_ofCoeffs _ hi, decM_encM hK]

/-- Coefficient-wise one's-complement addition. -/
def addRMW (N K : ℕ) (x y : List Bool) : List Bool :=
  concatN N (fun i => addMW (block K i x) (block K i y))

/-- Coefficient-wise one's-complement subtraction. -/
def subRMW (N K : ℕ) (x y : List Bool) : List Bool :=
  concatN N (fun i => subMW (block K i x) (block K i y))

/-- The residue `r` times every coefficient. -/
def scRMW (N K : ℕ) (r x : List Bool) : List Bool := concatN N (fun i => mulMW (block K i x) r)

/-- Every coefficient rotated `j` times (the multiplication by `2^{−j}`). -/
def rotBW (N K j : ℕ) (x : List Bool) : List Bool := concatN N (fun i => rot1^[j] (block K i x))

theorem length_addRMW (N K : ℕ) {x : List Bool} (hx : x.length = N * K) (y : List Bool) :
    (addRMW N K x y).length = N * K :=
  length_concatN fun i hi => by rw [length_addMW, length_block hx hi]

theorem length_subRMW (N K : ℕ) {x : List Bool} (hx : x.length = N * K) (y : List Bool) :
    (subRMW N K x y).length = N * K :=
  length_concatN fun i hi => by rw [length_subMW, length_block hx hi]

theorem length_scRMW (N K : ℕ) (r : List Bool) {x : List Bool} (hx : x.length = N * K) :
    (scRMW N K r x).length = N * K :=
  length_concatN fun i hi => by rw [length_mulMW, length_block hx hi]

theorem length_rotBW (N K j : ℕ) {x : List Bool} (hx : x.length = N * K) :
    (rotBW N K j x).length = N * K :=
  length_concatN fun i hi => by rw [length_rot1_iter, length_block hx hi]

theorem decRM_addRMW {N K : ℕ} {x y : List Bool} (hx : x.length = N * K) (hy : y.length = N * K) :
    decRM N K (addRMW N K x y) = decRM N K x + decRM N K y := by
  rw [addRMW, decRM_concatN fun i hi => by rw [length_addMW, length_block hx hi]]
  apply ext_coefG
  intro i hi
  rw [coefG_ofCoeffs _ hi, coefG_add, coefG_decRM _ hi, coefG_decRM _ hi,
    decM_addMW (length_block hx hi) (length_block hy hi)]

theorem decRM_subRMW {N K : ℕ} {x y : List Bool} (hx : x.length = N * K) (hy : y.length = N * K) :
    decRM N K (subRMW N K x y) = decRM N K x - decRM N K y := by
  rw [subRMW, decRM_concatN fun i hi => by rw [length_subMW, length_block hx hi]]
  apply ext_coefG
  intro i hi
  rw [coefG_ofCoeffs _ hi, coefG_sub, coefG_decRM _ hi, coefG_decRM _ hi,
    decM_subMW (length_block hx hi) (length_block hy hi)]

theorem block_notW (K i : ℕ) (x : List Bool) : block K i (notW x) = notW (block K i x) := by
  simp [block, notW, List.map_drop, List.map_take]

/-- **Negation of a ring word is bitwise NOT.** -/
theorem decRM_notW {N K : ℕ} {x : List Bool} (hx : x.length = N * K) :
    decRM N K (notW x) = -decRM N K x := by
  apply ext_coefG
  intro i hi
  rw [coefG_neg, coefG_decRM _ hi, coefG_decRM _ hi, block_notW, decM_notW (length_block hx hi)]

/-- **Residue times ring element.** -/
theorem decRM_scRMW {N K : ℕ} {r x : List Bool} (hr : r.length = K) (hx : x.length = N * K) :
    decRM N K (scRMW N K r x) = decM K r • decRM N K x := by
  rw [scRMW, decRM_concatN fun i hi => by rw [length_mulMW, length_block hx hi]]
  apply ext_coefG
  intro i hi
  rw [coefG_ofCoeffs _ hi, coefG_of_lt _ hi, Negacyclic.coeffs_smul, Pi.smul_apply, smul_eq_mul,
    ← coefG_val, coefG_decRM _ hi, decM_mulMW (length_block hx hi) hr, mul_comm]

/-- **Multiplication by `2^i`** (`i ≤ K`) by a rotation of every coefficient: for
`W⁻¹ = 2^{K − b}`, `rotBW N K b`. -/
theorem decRM_rotBW {N K i : ℕ} {x : List Bool} (hx : x.length = N * K) (hi : i ≤ K) :
    decRM N K (rotBW N K (K - i) x) = (2 : ZMod (2 ^ K - 1)) ^ i • decRM N K x := by
  rw [rotBW, decRM_concatN fun t ht => by rw [length_rot1_iter, length_block hx ht]]
  apply ext_coefG
  intro t ht
  rw [coefG_ofCoeffs _ ht, coefG_of_lt _ ht, Negacyclic.coeffs_smul, Pi.smul_apply, smul_eq_mul,
    ← coefG_val, coefG_decRM _ ht, decM_rot1_iter_sub (length_block hx ht) hi]

/-! ### `X⁻¹` on words -/

/-- The blocks of `e.drop K ++ v`: the blocks of `e` shifted down, `v` on top. -/
theorem decRM_drop_append {N K : ℕ} (hN : 0 < N) {e v : List Bool} (he : e.length = N * K)
    (hv : v.length = K) {i : ℕ} (hi : i < N) :
    coefG (decRM N K (e.drop K ++ v)) i =
      if i + 1 < N then decM K (block K (i + 1) e) else decM K v := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hd : (e.drop K).length = M * K := by rw [List.length_drop, he]; ring_nf; omega
  have hblk : concatN M (fun i => block K (i + 1) e) = e.drop K := by
    conv_rhs => rw [← concatN_block hd]
    apply concatN_congr
    intro i _
    simp only [block, List.drop_drop]
    congr 2; ring
  have hf : concatN (M + 1) (fun i => if i + 1 < M + 1 then block K (i + 1) e else v) =
      e.drop K ++ v := by
    rw [concatN, ← hblk, mIfF (lt_irrefl _)]
    congr 1
    apply concatN_congr
    intro i hi
    rw [mIfT (by omega)]
  rw [← hf, decRM_concatN, coefG_ofCoeffs _ hi]
  · split_ifs <;> rfl
  · intro i hi'
    split_ifs with h
    · exact length_block he h
    · exact hv

theorem decRM_rho {N K : ℕ} (hN : 0 < N) {e : List Bool} (he : e.length = N * K) :
    decRM N K (e.drop K ++ notW (e.take K)) = rhoG (decRM N K e) := by
  have hK : K ≤ e.length := by rw [he]; exact Nat.le_mul_of_pos_left K hN
  apply ext_coefG
  intro i hi
  rw [decRM_drop_append hN he (by simp; omega) hi, coefG_rhoG _ hi]
  split_ifs with h
  · rw [coefG_decRM _ h]
  · rw [decM_notW (by simp; omega), coefG_decRM _ hN, show e.take K = block K 0 e by simp [block]]

theorem decRM_rhoAdd {N K : ℕ} (hN : 0 < N) {e a : List Bool} (he : e.length = N * K)
    (ha : a.length = K) :
    decRM N K (e.drop K ++ notW (addMW (e.take K) a)) =
      rhoG (decRM N K e + single0 (decM K a)) := by
  have hK : K ≤ e.length := by rw [he]; exact Nat.le_mul_of_pos_left K hN
  have hl : (e.take K).length = K := by simp; omega
  apply ext_coefG
  intro i hi
  rw [decRM_drop_append hN he (by simp [hl]) hi, coefG_rhoG _ hi]
  split_ifs with h
  · rw [coefG_add, coefG_decRM _ h, single0, coefG_ofCoeffs _ h]; simp
  · rw [decM_notW (by simp [hl]), decM_addMW hl ha, coefG_add, coefG_decRM _ hN, single0,
      coefG_ofCoeffs _ hN, show e.take K = block K 0 e by simp [block]]
    simp

/-! ### Gadget digits -/

theorem decM_bitW {K : ℕ} (hK : 0 < K) (b : Bool) :
    decM K (bitW K b) = if b then 1 else 0 := by
  obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  cases b <;> simp [bitW, decM, val_zeroW]

/-- **The binary digits are the bits of the coefficient words.** -/
theorem decRM_digitRW {N K : ℕ} (hK : 0 < K) (i : ℕ) (w : List Bool) :
    decRM N K (digitRW N K i w) =
      Negacyclic.ofCoeffs fun t => if (block K t w).getD i false then 1 else 0 := by
  rw [digitRW, decRM_concatN fun _ _ => length_bitW _ _]
  congr 1
  funext t
  rw [decM_bitW hK]

theorem val_eq_sum_getD : ∀ w : List Bool,
    val w = ∑ i ∈ Finset.range w.length, 2 ^ i * (w.getD i false).toNat
  | [] => by simp
  | b :: w => by
    rw [val_cons, val_eq_sum_getD w, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_succ, pow_zero, one_mul]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

/-- **Gadget reconstruction**: `Σ_{i < K} 2^i · digit_i(w) = w`. -/
theorem sum_pow_digitRW {N K : ℕ} (hK : 0 < K) {w : List Bool} (hw : w.length = N * K) :
    ∑ i ∈ Finset.range K, (2 : ZMod (2 ^ K - 1)) ^ i • decRM N K (digitRW N K i w) =
      decRM N K w := by
  apply ext_coefG
  intro t ht
  rw [coefG_decRM _ ht, decM, val_eq_sum_getD, length_block hw ht]
  rw [show coefG (∑ i ∈ Finset.range K, (2 : ZMod (2 ^ K - 1)) ^ i • decRM N K (digitRW N K i w)) t
      = ∑ i ∈ Finset.range K, coefG ((2 : ZMod (2 ^ K - 1)) ^ i • decRM N K (digitRW N K i w)) t
      by simp [coefG, ht, Negacyclic.coeffs_sum]]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [decRM_digitRW hK, coefG_of_lt _ ht, Negacyclic.coeffs_smul, Pi.smul_apply,
    Negacyclic.coeffs_ofCoeffs, smul_eq_mul]
  cases (block K t w).getD i false <;> simp

end SigabaNeo.Lattices.Algo
