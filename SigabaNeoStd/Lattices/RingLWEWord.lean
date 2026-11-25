import SigabaNeoStd.Lattices.RingLWEInst
import SigabaNeoStd.Machines.Prog.FrameParse
import SigabaNeoStd.Encode.Laws

/-!
# The registry's Ring-LWE words, parsed

The registry encodes a ring-level pair `v = (a, b)` (`SigabaNeo.Lattices.encodeRing`, over
`ℤ_{2^K}[X]/(X^N + 1)`) as cslib's Module-LWE word: the framed expanded matrix of `a` (`m N` rows of
`N` entries, `rotMatrix (aᵢ)`, each a framed binary natural number), then the framed coefficients
of `b`. Here this word is the shape read by the parser `SigabaNeo.Tape.Prog.decodeP`:

* `encodeRing_eq`: the word is `frame (rows.flatMap rowW) ++ nums.flatMap frame`
  (`ringRows`, `ringNums`);
* `rows_emit`, `nums_emit`: the first entry of row `(i, j)` is the coefficient `j` of `aᵢ`
  (`rotMatrix` has the coefficients in its column `0`), so the parser's output is the codec word of
  the `aᵢ` (`ringEnc`, negated when `neg`), then that of the `bᵢ`; a binary number padded to `K` bits
  is `zmodEnc` (`encE_bits`; two's complement for the negation);
* **`decodeW_encodeRing`**: the parser's output on `encodeRing v`;
* `length_encodeRing_le`: the words are at most `encLen m N K` bits.
-/

namespace SigabaNeo.Lattices.RingLWEWord
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape Cslib
open Turing.MultiTapeTM (frame encList encNat encPair encBits)

variable {N K m : ℕ}

/-- The rows of the expanded matrix of a ring-level pair, entries in binary. -/
def ringRows (v : (Fin m → Negacyclic (ZMod (2 ^ K)) N) × (Fin m → Negacyclic (ZMod (2 ^ K)) N)) :
    List (List (List Bool)) :=
  (List.ofFn fun p : Fin (m * N) => List.ofFn fun c : Fin (1 * N) =>
    (Cslib.Crypto.expandModuleMatrix (coeffPair v).1 p c).val).map (List.map Nat.bits)

/-- The coefficients of the values of a ring-level pair, in binary. -/
def ringNums (v : (Fin m → Negacyclic (ZMod (2 ^ K)) N) × (Fin m → Negacyclic (ZMod (2 ^ K)) N)) :
    List (List Bool) :=
  (List.ofFn fun c : Fin (m * N) => (Cslib.Crypto.flattenPolyVec (coeffPair v).2 c).val).map Nat.bits

theorem encodeRing_eq (v : (Fin m → Negacyclic (ZMod (2 ^ K)) N) × (Fin m → Negacyclic (ZMod (2 ^ K)) N)) :
    encodeRing v = frame ((ringRows v).flatMap FPS.rowW) ++ (ringNums v).flatMap frame := by
  simp only [encodeRing, Cslib.Crypto.ModuleLWE.encodeSample, Turing.MultiTapeTM.encPair_apply,
    Cslib.Crypto.ModuleSIS.encodeMatrix, Cslib.Crypto.SIS.encodeMatrix, ringRows, ringNums,
    List.flatMap_map, FPS.rowW]
  rfl

/-! ### Numbers below `2^K` -/

/-- The `K` low bits of `n`, least significant first. -/
def lowBits (K n : ℕ) : List Bool := (List.finRange K).map fun i : Fin K => n.testBit i

theorem lowBits_succ (K n : ℕ) : lowBits (K + 1) n = n.testBit 0 :: lowBits K (n / 2) := by
  simp only [lowBits, List.finRange_succ, List.map_cons, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp [Nat.testBit_div_two]

theorem length_bits_le {n : ℕ} (h : n < 2 ^ K) : n.bits.length ≤ K := by
  rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr h

theorem padK_bits {n : ℕ} (h : n < 2 ^ K) : padK K n.bits = lowBits K n := by
  have hl := length_bits_le h
  apply List.ext_getElem (by simp [length_padK hl, lowBits])
  intro i h1 h2
  simp only [lowBits, List.getElem_map, List.getElem_finRange, Fin.val_cast, Nat.testBit_eq_inth, padK]
  by_cases hi : i < n.bits.length
  · rw [List.getElem_append_left hi, List.getI_eq_getElem _ hi]
  · rw [List.getElem_append_right (by omega), List.getI_eq_default _ (by omega)]
    simp

theorem negS_true_lowBits : ∀ (K n : ℕ), n < 2 ^ K → negS true (lowBits K n) = lowBits K (2 ^ K - 1 - n)
  | 0, _, _ => rfl
  | K + 1, n, h => by
    rw [lowBits_succ, negS, Bool.true_or, negS_true_lowBits K (n / 2) (by rw [pow_succ] at h; omega),
      lowBits_succ, Nat.testBit_zero, Nat.testBit_zero, pow_succ]
    have e1 : (2 ^ K * 2 - 1 - n) / 2 = 2 ^ K - 1 - n / 2 := by rw [pow_succ] at h; omega
    rw [e1]
    congr 1
    have : (2 ^ K * 2 - 1 - n) % 2 = 1 ↔ ¬ n % 2 = 1 := by rw [pow_succ] at h; omega
    by_cases hn : n % 2 = 1 <;> simp [hn, this]

theorem negS_false_lowBits_zero : ∀ (K : ℕ), negS false (lowBits K 0) = lowBits K 0
  | 0 => rfl
  | K + 1 => by
    rw [lowBits_succ, negS, Nat.zero_div, Nat.testBit_zero]
    simp [negS_false_lowBits_zero K]

theorem negS_false_lowBits : ∀ (K n : ℕ), 0 < n → n < 2 ^ K →
    negS false (lowBits K n) = lowBits K (2 ^ K - n)
  | 0, n, h0, h => by simp at h; omega
  | K + 1, n, h0, h => by
    have hP : 2 ^ (K + 1) = 2 ^ K * 2 := pow_succ 2 K
    rw [hP] at h ⊢
    rw [lowBits_succ, lowBits_succ, Nat.testBit_zero, Nat.testBit_zero]
    by_cases hn : n % 2 = 1
    · have e1 : (2 ^ K * 2 - n) / 2 = 2 ^ K - 1 - n / 2 := by omega
      have e2 : (2 ^ K * 2 - n) % 2 = 1 := by omega
      have hd : decide (n % 2 = 1) = true := by simp [hn]
      rw [negS, hd, Bool.false_or, negS_true_lowBits K (n / 2) (by omega), e1]
      simp [e2]
    · have e1 : (2 ^ K * 2 - n) / 2 = 2 ^ K - n / 2 := by omega
      have e2 : ¬ (2 ^ K * 2 - n) % 2 = 1 := by omega
      have hd : decide (n % 2 = 1) = false := by simp [hn]
      rw [negS, hd, Bool.false_or, negS_false_lowBits K (n / 2) (by omega) (by omega), e1]
      simp [e2]

theorem zmodEnc_eq (x : ZMod (2 ^ K)) : (zmodEnc K).enc x = lowBits K x.val := rfl

/-- **A residue, in binary, padded**: its word. -/
theorem encE_false_bits (x : ZMod (2 ^ K)) : encE false K x.val.bits = (zmodEnc K).enc x := by
  simp only [encE, Bool.false_eq_true, ↓reduceIte]
  rw [padK_bits (ZMod.val_lt x), zmodEnc_eq]

/-- **A residue, in binary, padded and negated**: the word of its negation. -/
theorem encE_true_bits (x : ZMod (2 ^ K)) : encE true K x.val.bits = (zmodEnc K).enc (-x) := by
  have : NeZero (2 ^ K) := ⟨by positivity⟩
  simp only [encE, ↓reduceIte]
  rw [padK_bits (ZMod.val_lt x), zmodEnc_eq, ZMod.neg_val]
  by_cases hx : x = 0
  · subst hx; simp [negS_false_lowBits_zero]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hx), negS_false_lowBits K _ (Nat.pos_of_ne_zero (by simpa using hx)) (ZMod.val_lt x)]

theorem encE_bits (neg : Bool) (x : ZMod (2 ^ K)) :
    encE neg K x.val.bits = (zmodEnc K).enc (if neg then -x else x) := by
  cases neg
  · exact encE_false_bits x
  · exact encE_true_bits x

/-! ### The emitted words of an encoded pair -/

theorem headD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (d : α) (h : 0 < n) :
    (List.ofFn f).headD d = f ⟨0, h⟩ := by
  cases n with
  | zero => omega
  | succ n => simp [List.ofFn_succ]

theorem flatMap_flatten' {α β : Type} (g : α → List β) :
    ∀ L : List (List α), L.flatten.flatMap g = L.flatMap fun l => l.flatMap g
  | [] => rfl
  | l :: L => by rw [List.flatten_cons, List.flatMap_append, flatMap_flatten' g L]; rfl

theorem flatMap_ofFn_mul {α β : Type} {m N : ℕ} (f : Fin (m * N) → α) (g : α → List β) :
    (List.ofFn f).flatMap g = (List.finRange m).flatMap fun i => (List.finRange N).flatMap fun j =>
      g (f (finProdFinEquiv (i, j))) := by
  rw [List.ofFn_mul, flatMap_flatten', List.ofFn_eq_map]
  simp only [List.flatMap_map, List.ofFn_eq_map]
  congr 1; funext i; congr 1; funext j
  congr 2
  ext
  simp [finProdFinEquiv_apply_val, Nat.mul_comm, Nat.add_comm]

variable (v : (Fin m → Negacyclic (ZMod (2 ^ K)) N) × (Fin m → Negacyclic (ZMod (2 ^ K)) N))

/-- **The first entries of the rows** of the expanded matrix, emitted: the words of the `aᵢ`
(negated when `neg`). -/
theorem rows_emit (neg : Bool) :
    (ringRows v).flatMap (fun r => encE neg K (r.headD [])) =
      (List.finRange m).flatMap fun i => (ringEnc N K).enc (if neg then -v.1 i else v.1 i) := by
  rw [ringRows, List.flatMap_map, flatMap_ofFn_mul]
  congr 1; funext i
  rw [ringEnc_flatMap', List.flatMap_map]
  congr 1; funext j
  have hN : 0 < 1 * N := by have := j.isLt; omega
  rw [List.map_ofFn, headD_ofFn _ _ hN, Function.comp_apply,
    show (⟨0, hN⟩ : Fin (1 * N)) = finProdFinEquiv ((0 : Fin 1), (⟨0, by omega⟩ : Fin N)) from
      Fin.ext (by simp [finProdFinEquiv_apply_val]),
    Cslib.Crypto.expandModuleMatrix_apply, encE_bits]
  have h0 : (⟨0, by omega⟩ : Fin N) ≤ j := Fin.mk_le_mk.mpr (Nat.zero_le _)
  cases neg <;> simp [coeffPair, rotMatrix, h0]

/-- **The values, emitted**: the words of the `bᵢ`. -/
theorem nums_emit :
    (ringNums v).flatMap (encE false K) = (List.finRange m).flatMap fun i => (ringEnc N K).enc (v.2 i) := by
  rw [ringNums, List.flatMap_map, flatMap_ofFn_mul]
  congr 1; funext i
  rw [ringEnc_flatMap', List.flatMap_map]
  congr 1; funext j
  simp [encE_false_bits, Cslib.Crypto.flattenPolyVec, coeffPair]

/-! ### The parser on the encoded pairs -/

theorem length_ringRows : (ringRows v).length = m * N := by simp [ringRows]
theorem length_ringNums : (ringNums v).length = m * N := by simp [ringNums]

theorem mem_ringRows {r : List (List Bool)} (hr : r ∈ ringRows v) :
    r.length = N ∧ ∀ u ∈ r, u.length ≤ K := by
  simp only [ringRows, List.mem_map, List.mem_ofFn] at hr
  obtain ⟨_, ⟨p, rfl⟩, rfl⟩ := hr
  refine ⟨by simp, fun u hu => ?_⟩
  simp only [List.mem_map, List.mem_ofFn] at hu
  obtain ⟨_, ⟨c, rfl⟩, rfl⟩ := hu
  exact length_bits_le (ZMod.val_lt _)

theorem mem_ringNums {u : List Bool} (hu : u ∈ ringNums v) : u.length ≤ K := by
  simp only [ringNums, List.mem_map, List.mem_ofFn] at hu
  obtain ⟨_, ⟨c, rfl⟩, rfl⟩ := hu
  exact length_bits_le (ZMod.val_lt _)

/-- **The parser on an encoded ring-level pair** (`2 m N K` output bits): `true`, the words of the
`aᵢ` (negated when `neg`), then the words of the `bᵢ`. -/
theorem decodeW_encodeRing (neg : Bool) :
    Prog.decodeW neg K (2 * m * N * K) (encodeRing v) =
      true :: ((List.finRange m).flatMap (fun i => (ringEnc N K).enc (if neg then -v.1 i else v.1 i)) ++
        (List.finRange m).flatMap fun i => (ringEnc N K).enc (v.2 i)) := by
  have hT : 2 * m * N * K = ((ringRows v).length + (ringNums v).length) * K := by
    rw [length_ringRows, length_ringNums]; ring
  rw [hT, encodeRing_eq, Prog.decodeW_word, rows_emit, nums_emit]
  · intro r hr h0
    obtain ⟨hl, _⟩ := mem_ringRows v hr
    have : 0 < (ringRows v).length := List.length_pos_of_mem hr
    rw [length_ringRows] at this
    subst h0
    simp only [List.length_nil] at hl
    subst hl
    simp at this
  · intro r hr
    obtain ⟨_, h⟩ := mem_ringRows v hr
    cases r with
    | nil => simp
    | cons u r => exact h u List.mem_cons_self
  · intro u hu; exact mem_ringNums v hu

/-! ### The length of the encoded pairs -/

theorem length_frame (u : List Bool) : (frame u).length = 2 * u.length + 1 := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    simp only [frame, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at ih ⊢
    omega

theorem length_flatMap_le {α : Type} (f : α → List Bool) (c : ℕ) :
    ∀ (l : List α), (∀ x ∈ l, (f x).length ≤ c) → (l.flatMap f).length ≤ l.length * c
  | [], _ => by simp
  | x :: l, h => by
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have := length_flatMap_le f c l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have := h x List.mem_cons_self
    omega

/-- A bound on the length of the encoded pairs. -/
def encLen (m N K : ℕ) : ℕ :=
  2 * (m * N * (2 * (N * (2 * K + 1)) + 1)) + 1 + m * N * (2 * K + 1)

theorem length_encodeRing_le : (encodeRing v).length ≤ encLen m N K := by
  rw [encodeRing_eq, List.length_append, length_frame, encLen]
  have h1 : ((ringRows v).flatMap FPS.rowW).length ≤
      (ringRows v).length * (2 * (N * (2 * K + 1)) + 1) := by
    refine length_flatMap_le _ _ _ fun r hr => ?_
    obtain ⟨hl, hu⟩ := mem_ringRows v hr
    rw [FPS.rowW, length_frame]
    have := length_flatMap_le frame (2 * K + 1) r fun u hu' => by
      rw [length_frame]; have := hu u hu'; omega
    rw [hl] at this
    omega
  have h2 : ((ringNums v).flatMap frame).length ≤ (ringNums v).length * (2 * K + 1) :=
    length_flatMap_le _ _ _ fun u hu => by rw [length_frame]; have := mem_ringNums v hu; omega
  rw [length_ringRows] at h1
  rw [length_ringNums] at h2
  omega

end SigabaNeo.Lattices.RingLWEWord