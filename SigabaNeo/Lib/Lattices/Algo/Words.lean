import SigabaNeo.Lib.Encode.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Fixed-width arithmetic on bit words

Words are lists of bits, least significant first, as in `SigabaNeo.Encode.zmodEnc`. The operations
are first-order loops over the bits that keep the width of their first argument, so arithmetic is
modulo `2^K` by truncation:

* `addc c x y`: ripple-carry addition with carry-in `c` (`val_addc`);
* `addW x y = addc false x y`, `subW x y = addc true x (¬y)` (two's complement), `negW`;
* `shl w`: shift left by one bit, dropping the top bit;
* `mulW x y`: shift-and-add multiplication (Horner on the bits of `y`, most significant first).

On `K`-bit words they compute the ring operations of `ZMod (2^K)` on the encodings `zmodEnc K`
(`addW_enc`, `subW_enc`, `mulW_enc`). Each algorithm has a step count (`addSteps`, `mulSteps`,
…): the number of one-bit operations it performs, counted along the same recursion
(`mulWCost_eq`).

The value of a word is `val` (Horner from the most significant bit), its residue `dec`, and
`toBits K n` writes the `K` low bits of `n` (`zmodEnc_enc : (zmodEnc K).enc x = toBits K x.val`).
-/

namespace SigabaNeo.Lattices.Algo

open SigabaNeo.Encode

/-! ### Values of words -/

/-- The value of a word, least significant bit first. -/
def val : List Bool → ℕ
  | [] => 0
  | b :: w => b.toNat + 2 * val w

/-- The `K` low bits of `n`, least significant first. -/
def toBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | K + 1, n => decide (n % 2 = 1) :: toBits K (n / 2)

@[simp] theorem val_nil : val [] = 0 := rfl
@[simp] theorem val_cons (b : Bool) (w : List Bool) : val (b :: w) = b.toNat + 2 * val w := rfl

@[simp] theorem length_toBits (K n : ℕ) : (toBits K n).length = K := by
  induction K generalizing n with
  | zero => rfl
  | succ K ih => simp [toBits, ih]

theorem val_lt (w : List Bool) : val w < 2 ^ w.length := by
  induction w with
  | nil => simp
  | cons b w ih =>
    simp only [val_cons, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

/-- `s + 2m mod 2^(n+1) = s + 2 (m mod 2^n)` for a bit `s`. -/
theorem bit_add_two_mul_mod (s m n : ℕ) (hs : s < 2) :
    (s + 2 * m) % 2 ^ (n + 1) = s + 2 * (m % 2 ^ n) := by
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  have hm := Nat.mod_add_div m (2 ^ n)
  have hlt := Nat.mod_lt m hpos
  rw [pow_succ]
  have : s + 2 * m = (s + 2 * (m % 2 ^ n)) + (2 ^ n * 2) * (m / 2 ^ n) := by
    conv_lhs => rw [← hm]
    ring
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  omega

theorem val_toBits (K n : ℕ) : val (toBits K n) = n % 2 ^ K := by
  induction K generalizing n with
  | zero => simp [toBits, Nat.mod_one]
  | succ K ih =>
    simp only [toBits, val_cons, ih]
    have h2 := Nat.mod_two_eq_zero_or_one n
    have hb : (decide (n % 2 = 1)).toNat = n % 2 := by
      rcases h2 with h | h <;> simp [h]
    rw [hb, ← bit_add_two_mul_mod _ _ _ (Nat.mod_lt _ (by norm_num))]
    congr 1
    omega

theorem toBits_val (w : List Bool) : toBits w.length (val w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [List.length_cons, toBits, val_cons]
    congr 1
    · cases b <;> simp
    · convert ih using 2
      cases b <;> simp; omega

theorem toBits_mod (K n : ℕ) : toBits K (n % 2 ^ K) = toBits K n := by
  have h1 := toBits_val (toBits K n)
  rw [length_toBits, val_toBits] at h1
  exact h1

/-- Two words of the same length with the same value are equal. -/
theorem eq_of_val_eq {v w : List Bool} (hl : v.length = w.length) (h : val v = val w) : v = w := by
  rw [← toBits_val v, ← toBits_val w, hl, h]

theorem testBit_eq_toBits (K n : ℕ) :
    (List.finRange K).map (fun i : Fin K => n.testBit i.val) = toBits K n := by
  induction K generalizing n with
  | zero => rfl
  | succ K ih =>
    rw [List.finRange_succ, List.map_cons, List.map_map, toBits]
    congr 1
    · simp [Nat.testBit_zero]
    · rw [← ih (n / 2)]
      apply List.map_congr_left
      intro i _
      simp [Function.comp, Nat.testBit_succ]

/-- The encoding of residues writes the bits of the representative. -/
theorem zmodEnc_enc (K : ℕ) (x : ZMod (2 ^ K)) : (zmodEnc K).enc x = toBits K x.val :=
  testBit_eq_toBits K x.val

/-! ### Residues of words -/

/-- The residue of a word modulo `2^K`. -/
def dec (K : ℕ) (w : List Bool) : ZMod (2 ^ K) := (val w : ZMod (2 ^ K))

theorem enc_dec {K : ℕ} {w : List Bool} (hw : w.length = K) : (zmodEnc K).enc (dec K w) = w := by
  subst hw
  rw [zmodEnc_enc, dec, ZMod.val_natCast, toBits_mod, toBits_val]

theorem dec_enc (K : ℕ) (x : ZMod (2 ^ K)) : dec K ((zmodEnc K).enc x) = x := by
  rw [zmodEnc_enc, dec, val_toBits, Nat.mod_eq_of_lt (ZMod.val_lt x), ZMod.natCast_zmod_val]

theorem dec_toBits (K n : ℕ) : dec K (toBits K n) = (n : ZMod (2 ^ K)) := by
  rw [dec, val_toBits, ZMod.natCast_mod]

/-- A `K`-bit word is the encoding of a residue `x` as soon as its residue is `x`. -/
theorem eq_enc_of_dec {K : ℕ} {w : List Bool} (hw : w.length = K) {x : ZMod (2 ^ K)}
    (h : dec K w = x) : w = (zmodEnc K).enc x := by
  rw [← h, enc_dec hw]

/-! ### Addition -/

/-- **Ripple-carry addition** with carry-in `c`, on the width of `x`. -/
def addc : Bool → List Bool → List Bool → List Bool
  | _, [], _ => []
  | c, a :: x, [] => xor a c :: addc (a && c) x []
  | c, a :: x, b :: y => xor (xor a b) c :: addc ((a && b) || (c && (a || b))) x y

@[simp] theorem length_addc (c : Bool) (x y : List Bool) : (addc c x y).length = x.length := by
  induction x generalizing c y with
  | nil => rfl
  | cons a x ih => cases y <;> simp [addc, ih]

theorem val_addc (c : Bool) (x y : List Bool) :
    val (addc c x y) = (val x + val y + c.toNat) % 2 ^ x.length := by
  induction x generalizing c y with
  | nil => simp [addc, Nat.mod_one]
  | cons a x ih =>
    cases y with
    | nil =>
      simp only [addc, val_cons, ih, val_nil, List.length_cons]
      rw [← bit_add_two_mul_mod _ _ _ (by cases a <;> cases c <;> simp)]
      congr 1
      cases a <;> cases c <;> simp <;> ring
    | cons b y =>
      simp only [addc, val_cons, ih, List.length_cons]
      rw [← bit_add_two_mul_mod _ _ _ (by cases a <;> cases b <;> cases c <;> simp)]
      congr 1
      cases a <;> cases b <;> cases c <;> simp <;> ring

/-- Fixed-width addition. -/
def addW (x y : List Bool) : List Bool := addc false x y

/-- One's complement. -/
def notW (y : List Bool) : List Bool := y.map not

/-- Fixed-width subtraction: `x + ¬y + 1`. -/
def subW (x y : List Bool) : List Bool := addc true x (notW y)

/-- The all-zero word. -/
def zeroW (K : ℕ) : List Bool := List.replicate K false

@[simp] theorem length_addW (x y : List Bool) : (addW x y).length = x.length := length_addc _ _ _
@[simp] theorem length_subW (x y : List Bool) : (subW x y).length = x.length := length_addc _ _ _
@[simp] theorem length_zeroW (K : ℕ) : (zeroW K).length = K := List.length_replicate

theorem val_zeroW (K : ℕ) : val (zeroW K) = 0 := by
  induction K with
  | zero => rfl
  | succ K ih => simp [zeroW, List.replicate_succ] at ih ⊢; exact ih

theorem val_notW (y : List Bool) : val (notW y) + val y + 1 = 2 ^ y.length := by
  induction y with
  | nil => rfl
  | cons b y ih =>
    simp only [notW, List.map_cons, val_cons, List.length_cons, pow_succ] at ih ⊢
    cases b <;> simp <;> omega

theorem dec_addc (K : ℕ) (c : Bool) {x : List Bool} (hx : x.length = K) (y : List Bool) :
    dec K (addc c x y) = dec K x + dec K y + (c.toNat : ZMod (2 ^ K)) := by
  simp only [dec, val_addc, hx, Nat.cast_add, ZMod.natCast_mod]

theorem dec_addW (K : ℕ) {x : List Bool} (hx : x.length = K) (y : List Bool) :
    dec K (addW x y) = dec K x + dec K y := by
  simp [addW, dec_addc K false hx]

theorem dec_notW (K : ℕ) {y : List Bool} (hy : y.length = K) :
    dec K (notW y) = -1 - dec K y := by
  have h := congrArg (fun n : ℕ => (n : ZMod (2 ^ K))) (val_notW y)
  simp only [Nat.cast_add, Nat.cast_one, hy, Nat.cast_pow, Nat.cast_ofNat] at h
  rw [show ((2 : ZMod (2 ^ K)) ^ K) = 0 by exact_mod_cast ZMod.natCast_self (2 ^ K)] at h
  simp only [dec]
  linear_combination h

theorem dec_subW (K : ℕ) {x : List Bool} (hx : x.length = K) {y : List Bool} (hy : y.length = K) :
    dec K (subW x y) = dec K x - dec K y := by
  rw [subW, dec_addc K true hx, dec_notW K hy]
  simp
  ring

theorem dec_zeroW (K : ℕ) : dec K (zeroW K) = 0 := by simp [dec, val_zeroW]

theorem addW_enc (K : ℕ) (a b : ZMod (2 ^ K)) :
    addW ((zmodEnc K).enc a) ((zmodEnc K).enc b) = (zmodEnc K).enc (a + b) :=
  eq_enc_of_dec (by simp [(zmodEnc K).length]) (by
    rw [dec_addW K ((zmodEnc K).length a), dec_enc, dec_enc])

theorem subW_enc (K : ℕ) (a b : ZMod (2 ^ K)) :
    subW ((zmodEnc K).enc a) ((zmodEnc K).enc b) = (zmodEnc K).enc (a - b) :=
  eq_enc_of_dec (by simp [(zmodEnc K).length]) (by
    rw [dec_subW K ((zmodEnc K).length a) ((zmodEnc K).length b), dec_enc, dec_enc])

/-! ### Multiplication -/

/-- Shift left by one bit, keeping the width. -/
def shl (w : List Bool) : List Bool := (false :: w).take w.length

@[simp] theorem length_shl (w : List Bool) : (shl w).length = w.length := by simp [shl]

theorem val_take (n : ℕ) (w : List Bool) : val (w.take n) = val w % 2 ^ n := by
  induction w generalizing n with
  | nil => simp
  | cons b w ih =>
    cases n with
    | zero => simp [Nat.mod_one]
    | succ n =>
      simp only [List.take_succ_cons, val_cons, ih]
      rw [bit_add_two_mul_mod _ _ _ (by cases b <;> simp)]

theorem dec_shl (K : ℕ) {w : List Bool} (hw : w.length = K) : dec K (shl w) = 2 * dec K w := by
  simp only [dec, shl, val_take, val_cons, hw, Bool.toNat_false, zero_add, ZMod.natCast_mod]
  push_cast; ring

/-- Select: `x` if the bit is set, zero otherwise (an `AND` of every bit with `b`). -/
def selW (b : Bool) (x : List Bool) : List Bool := x.map (fun a => a && b)

@[simp] theorem length_selW (b : Bool) (x : List Bool) : (selW b x).length = x.length := by
  simp [selW]

theorem dec_selW (K : ℕ) (b : Bool) (x : List Bool) :
    dec K (selW b x) = (b.toNat : ZMod (2 ^ K)) * dec K x := by
  cases b
  · have : selW false x = zeroW x.length := by
      simp [selW, zeroW, List.map_const']
    rw [this]; simp [dec, val_zeroW]
  · simp [selW]

/-- **Shift-and-add multiplication** on the width of `x`: Horner on the bits of `y` from the most
significant one, `x · (b + 2y') = b x + 2 (x y')`. -/
def mulW (x : List Bool) : List Bool → List Bool
  | [] => zeroW x.length
  | b :: y => addW (selW b x) (shl (mulW x y))

@[simp] theorem length_mulW (x y : List Bool) : (mulW x y).length = x.length := by
  induction y with
  | nil => simp [mulW]
  | cons b y ih => simp [mulW]

theorem dec_mulW (K : ℕ) {x : List Bool} (hx : x.length = K) (y : List Bool) :
    dec K (mulW x y) = dec K x * dec K y := by
  induction y with
  | nil => subst hx; simp [mulW, dec, val_zeroW]
  | cons b y ih =>
    rw [mulW, dec_addW K (by simp [hx]), dec_selW, dec_shl K (by simp [hx]), ih]
    simp only [dec, val_cons]; push_cast; ring

theorem mulW_enc (K : ℕ) (a b : ZMod (2 ^ K)) :
    mulW ((zmodEnc K).enc a) ((zmodEnc K).enc b) = (zmodEnc K).enc (a * b) :=
  eq_enc_of_dec (by simp [(zmodEnc K).length]) (by
    rw [dec_mulW K ((zmodEnc K).length a), dec_enc, dec_enc])

/-! ### Step counts

One step is one operation on one bit (a full adder, a negation, an `AND`, a copy). -/

/-- Steps of `addc` (and `addW`) on a `K`-bit word: one full adder per bit. -/
def addSteps (K : ℕ) : ℕ := K

/-- Steps of `subW`: the negation of `y`, then the addition. -/
def subSteps (K : ℕ) : ℕ := K + addSteps K

/-- Steps of `mulW` on `K`-bit words, along its recursion on the `m` bits of `y`: the zero word,
then per bit a select, a shift and an addition. -/
def mulWCost (K : ℕ) : ℕ → ℕ
  | 0 => K
  | m + 1 => mulWCost K m + (K + K + addSteps K)

theorem mulWCost_eq (K m : ℕ) : mulWCost K m = K + 3 * K * m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [mulWCost, ih, addSteps]; ring

/-- Steps of the multiplication of two `K`-bit words. -/
def mulSteps (K : ℕ) : ℕ := mulWCost K K

theorem mulSteps_eq (K : ℕ) : mulSteps K = K + 3 * K * K := mulWCost_eq K K

end SigabaNeo.Lattices.Algo
