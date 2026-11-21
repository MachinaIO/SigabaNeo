import SigabaNeo.Lib.Lattices.Algo.MatWords
import SigabaNeo.Lib.Lattices.Boxes

/-!
# Box rejection on bit words

The pieces of one try of box rejection (`SigabaNeo.Lattices.Algo.boxTry`) for keys over
`R_q = ℤ_{2^K}[X]/(X^N + 1)`, as first-order loops on words, generic in the sizes:

* `getW B s l`: the `B` coins `l[s], …, l[s + B − 1]` (`false` past the end of `l`);
* `cenW B K w`: the centered residue `val w − 2^{B−1}` of `B` bits, on `K` bits
  (`cenW_enc : cenW B K (ofFn bs) = enc (cenEmb B hB bs)`);
* `embW n B K l`: `n` centered residues of `B` coins each, the coefficients of a big-box element;
* `leW`, `absLeW`, `ballW`: comparison of words, the test `|x| ≤ S` of a residue
  (`absLeW_eq : absLeW w sW = decide (zabs (dec K w) ≤ val sW)`), and the test that every
  coefficient of a word is within `S` (`ballW_eq`);
* `decW`: the binary decomposition of a ring element on the gadget columns
  (`decW_enc`, the column `G̲⁻¹(u)` of the binary top-row gadget);
* `fun_enc_concatN`: the encoding of a function on an enumerated type is the loop over the
  enumeration.

Step counts: `cenSteps`, `embSteps`, `absLeSteps`, `ballSteps`, `decSteps`.
-/

namespace SigabaNeo.Lattices.Algo

open SigabaNeo.Encode Cslib Matrix

/-! ### Encodings of functions as loops -/

theorem flatMap_eq_concatN {α : Type*} (l : List α) (g : α → List Bool) :
    l.flatMap g = concatN l.length (fun i => if h : i < l.length then g l[i] else []) := by
  conv_lhs => rw [← List.ofFn_getElem (xs := l), List.ofFn_eq_map]
  rw [List.flatMap_map, flatMap_finRange]

/-- **The encoding of a function on an enumerated type** is the loop over its enumeration. -/
theorem fun_enc_concatN {α β : Type} [Enum α] {n : ℕ} (e : FixedEnc β n) (f : α → β) :
    (FixedEnc.fun e).enc f = concatN (Enum.list (α := α)).length
      (fun i => if h : i < (Enum.list (α := α)).length then e.enc (f (Enum.list (α := α))[i])
        else []) := by
  show ((Enum.list (α := α)).map f).flatMap e.enc = _
  rw [List.flatMap_map, flatMap_eq_concatN]

/-! ### Reading coins -/

/-- The `B` coins from position `s` (`false` past the end). -/
def getW (B s : ℕ) (l : List Bool) : List Bool := List.ofFn fun t : Fin B => l.getD (s + t) false

theorem val_ofFn : ∀ (B : ℕ) (g : Fin B → Bool), val (List.ofFn g) = ∑ t, (g t).toNat * 2 ^ (t : ℕ)
  | 0, _ => by simp
  | B + 1, g => by
    rw [List.ofFn_succ, val_cons, val_ofFn B, Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    ring

theorem bitsEquiv_val (B : ℕ) (bs : Fin B → Bool) :
    ((bitsEquiv B bs : Fin (2 ^ B)) : ℕ) = ∑ t, (bs t).toNat * 2 ^ (t : ℕ) := by
  simp only [bitsEquiv, Equiv.trans_apply, finFunctionFinEquiv_apply, Equiv.arrowCongr_apply,
    Equiv.refl_symm, Equiv.coe_refl, Function.comp_apply, id]
  refine Finset.sum_congr rfl fun t _ => ?_
  cases bs t <;> rfl

theorem val_append (u v : List Bool) : val (u ++ v) = val u + 2 ^ u.length * val v := by
  induction u with
  | nil => simp
  | cons b u ih => simp only [List.cons_append, val_cons, ih, List.length_cons, pow_succ]; ring

/-! ### Centered residues -/

/-- The word `w` padded (or cut) to `K` bits. -/
def padW (K : ℕ) (w : List Bool) : List Bool := (w ++ zeroW K).take K

/-- **A centered residue**: `val w − 2^{B−1}` on `K` bits. -/
def cenW (B K : ℕ) (w : List Bool) : List Bool := subW (padW K w) (powW K (B - 1))

theorem length_padW (K : ℕ) (w : List Bool) : (padW K w).length = K := by
  simp [padW]

theorem length_cenW (B K : ℕ) (w : List Bool) : (cenW B K w).length = K := by
  simp [cenW, length_padW]

theorem dec_padW (K : ℕ) (w : List Bool) : dec K (padW K w) = (val w : ZMod (2 ^ K)) := by
  rw [dec, padW, val_take, val_append, val_zeroW, mul_zero, add_zero, ZMod.natCast_mod]

/-- **`cenW` computes `cenEmb`.** -/
theorem cenW_enc (B K : ℕ) (hB : 2 ^ B ≤ 2 ^ K) (bs : Fin B → Bool) :
    cenW B K (List.ofFn bs) = (zmodEnc K).enc (cenEmb (Q := 2 ^ K) B hB bs) := by
  refine eq_enc_of_dec (length_cenW _ _ _) ?_
  rw [cenW, dec_subW K (length_padW _ _) (by simp [powW]), dec_padW, ← enc_pow, dec_enc,
    val_ofFn, ← bitsEquiv_val]
  simp [cenEmb]

/-! ### Comparisons and absolute values -/

/-- Comparison from the least significant bit: `f` is the comparison of the bits read so far. -/
def leAux : Bool → List Bool → List Bool → Bool
  | f, [], _ => f
  | f, _ :: _, [] => f
  | f, a :: x, b :: y => leAux (if a = b then f else b) x y

theorem leAux_eq : ∀ (f : Bool) (x y : List Bool), x.length = y.length →
    leAux f x y = decide (val x < val y ∨ (val x = val y ∧ f = true))
  | f, [], [], _ => by cases f <;> simp [leAux]
  | f, a :: x, b :: y, h => by
    rw [leAux, leAux_eq _ x y (by simpa using h)]
    simp only [val_cons]
    apply decide_eq_decide.mpr
    cases a <;> cases b <;> cases f <;> simp <;> omega

/-- `val x ≤ val y`, for words of the same length. -/
def leW (x y : List Bool) : Bool := leAux true x y

theorem leW_eq {x y : List Bool} (h : x.length = y.length) : leW x y = decide (val x ≤ val y) := by
  rw [leW, leAux_eq _ _ _ h]
  simp only [and_true, decide_eq_decide]
  omega

/-- Negation modulo `2^K` on `K`-bit words. -/
def negW (w : List Bool) : List Bool := subW (zeroW w.length) w

theorem length_negW (w : List Bool) : (negW w).length = w.length := by simp [negW]

/-- **The test `|x| ≤ S`** of a residue, with `S` given by its word: `x ≤ S` or `−x ≤ S`. -/
def absLeW (w sW : List Bool) : Bool := leW w sW || leW (negW w) sW

theorem val_negW (w : List Bool) : val (negW w) = (2 ^ w.length - val w) % 2 ^ w.length := by
  have h := val_addc true (zeroW w.length) (notW w)
  have hn := val_notW w
  have hl := val_lt w
  rw [negW, subW, h, val_zeroW, length_zeroW]
  congr 1
  simp only [Bool.toNat_true]
  omega

/-- **`absLeW` tests `zabs x ≤ S`.** -/
theorem absLeW_eq {K : ℕ} {w sW : List Bool} (hw : w.length = K) (hs : sW.length = K) :
    absLeW w sW = decide (zabs (dec K w) ≤ val sW) := by
  subst hw
  have hl := val_lt w
  have hv : (dec w.length w).val = val w := by
    rw [dec, ZMod.val_natCast, Nat.mod_eq_of_lt hl]
  rw [absLeW, leW_eq hs.symm, leW_eq (by rw [length_negW, hs]), val_negW, zabs,
    ZMod.valMinAbs_natAbs_eq_min, hv]
  by_cases h0 : val w = 0
  · simp [h0]
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp [min_le_iff]

/-- The loop `for q < n: ok := ok && f q`. -/
def allN : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n + 1, f => allN n f && f n

theorem allN_eq_true {n : ℕ} {f : ℕ → Bool} : allN n f = true ↔ ∀ q < n, f q = true := by
  induction n with
  | zero => simp [allN]
  | succ n ih =>
    simp only [allN, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ q hq
      rcases Nat.lt_succ_iff_lt_or_eq.mp hq with h | rfl
      · exact h1 q h
      · exact h2
    · intro h
      exact ⟨fun q hq => h q (by omega), h n (by omega)⟩

/-- **The ball test**: every `K`-bit block of `w` among the first `n` is within `S`. -/
def ballW (n K : ℕ) (sW w : List Bool) : Bool := allN n fun q => absLeW (block K q w) sW

theorem ballW_eq_true {n K : ℕ} {sW w : List Bool} (hs : sW.length = K) (hw : w.length = n * K) :
    ballW n K sW w = true ↔ ∀ q < n, zabs (dec K (block K q w)) ≤ val sW := by
  rw [ballW, allN_eq_true]
  refine forall₂_congr fun q hq => ?_
  rw [absLeW_eq (length_block hw hq) hs, decide_eq_true_iff]

/-! ### The coefficients of a big-box element -/

/-- **The big box on words**: `n` centered residues of `B` coins each. -/
def embW (n B K : ℕ) (l : List Bool) : List Bool := concatN n fun q => cenW B K (getW B (B * q) l)

theorem length_embW (n B K : ℕ) (l : List Bool) : (embW n B K l).length = n * K :=
  length_concatN fun _ _ => length_cenW _ _ _

/-! ### The binary decomposition -/

variable {N K : ℕ}

/-- **The binary decomposition on words**: on the gadget column `(0, i)`, the binary digit `i` of
the coefficients of `u`; zero on the columns `(1, i)`. -/
def decW (N K k : ℕ) (u : List Bool) : List Bool :=
  concatN (1 * (2 * k)) fun p =>
    if p / k = 0 then digitRW N K (p % k) u else zeroW (N * K)

theorem decW_enc {k : ℕ} (hk : 2 ^ K ≤ 2 ^ k) (u : Rq N K) (c₀ : Fin 2 × Fin k) :
    decW N K k ((ringEnc N K).enc u) =
      rowW N K k (Matrix.of fun _ c => (topBin N K k hk).ginv (Matrix.of fun _ _ => u) c c₀) := by
  apply concatN_eq_matW
  intro p hp
  rw [submatrix_apply, Matrix.of_apply, topBin_ginv_apply, colE_apply]
  dsimp only
  have hp' : p < 2 * k := by simpa using hp
  have hm : p % (2 * k) = p := Nat.mod_eq_of_lt hp'
  simp only [hm, Matrix.of_apply]
  split_ifs with h1 h2 h2
  · rw [digitRW_enc]
  · exact absurd (Fin.ext h1) h2
  · exact absurd (congrArg Fin.val h2) h1
  · exact (enc_zeroR N K).symm

/-- A row word is the column word of its transpose. -/
theorem matW_row_col {n : ℕ} (A : Matrix (Fin 1) (Fin n) (Rq N K)) :
    matW N K 1 n A = matW N K n 1 Aᵀ := by
  have h1 : matW N K 1 n A = concatN (1 * n) fun p =>
      if h : p < n then (ringEnc N K).enc (A 0 ⟨p, h⟩) else [] := by
    symm
    apply concatN_eq_matW
    intro p hp
    have hp' : p < n := by simpa using hp
    rw [dite_eq_left_of_eq_true (eq_true hp')]
    congr 2
    · exact Subsingleton.elim _ _
    · ext; simp [Nat.mod_eq_of_lt hp']
  have h2 : matW N K n 1 Aᵀ = concatN (n * 1) fun p =>
      if h : p < n then (ringEnc N K).enc (A 0 ⟨p, h⟩) else [] := by
    symm
    apply concatN_eq_matW
    intro p hp
    have hp' : p < n := by simpa using hp
    rw [dite_eq_left_of_eq_true (eq_true hp'), transpose_apply]
    congr 2
    · exact Subsingleton.elim _ _
    · ext; simp
  rw [h1, h2, Nat.one_mul, Nat.mul_one]

/-! ### Step counts -/

/-- Steps of `cenW`: reading `B` coins, padding to `K` bits, the constant `2^{B−1}`, the
subtraction. -/
def cenSteps (B K : ℕ) : ℕ := B + K + K + subSteps K

/-- Steps of `embW`. -/
def embSteps (n B K : ℕ) : ℕ := n * cenSteps B K

/-- Steps of `absLeW`: two comparisons, a negation, an `OR`. -/
def absLeSteps (K : ℕ) : ℕ := K + (K + subSteps K) + K + 1

/-- Steps of `ballW`: per block, a copy, the test and an `AND`. -/
def ballSteps (n K : ℕ) : ℕ := n * (blockSteps K + absLeSteps K + 1)

/-- Steps of `decW`: per gadget column, one digit (a bit per coefficient) or a zero word. -/
def decSteps (N K k : ℕ) : ℕ := 2 * k * (N * K)

theorem absLeSteps_eq (K : ℕ) : absLeSteps K = 5 * K + 1 := by
  simp [absLeSteps, subSteps, addSteps]; ring

theorem cenSteps_eq (B K : ℕ) : cenSteps B K = B + 4 * K := by
  simp [cenSteps, subSteps, addSteps]; ring

end SigabaNeo.Lattices.Algo
