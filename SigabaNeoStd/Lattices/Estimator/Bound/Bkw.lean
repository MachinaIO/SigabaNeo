import SigabaNeoStd.Lattices.Estimator.Bound.Guess

/-!
# Coded-BKW at a huge modulus

Each candidate of coded-BKW pays for a table of `q^b` entries (`b ≥ 1`), so its cost is at least
`log₂ q` bits. When `log₂ q ≥ 1024` this exceeds the estimator's binary64 cap (`2^1024`), so every
candidate is infinite, and so is the attack (`Bkw.cost_eq_none`).
-/

namespace SigabaNeo.Lattices.Estimator

open Fx NumMisc Bkw

theorem NumMisc.search_inv_range {α : Type} (Q : Option α → Prop) (start stop : ℕ) (eval : ℕ → α)
    (smaller : α → α → Bool) (h0 : Q none) (hf : ∀ x, start ≤ x → x < stop → Q (some (eval x))) :
    Q (NumMisc.search start stop eval smaller) := by
  unfold NumMisc.search
  simp only [Id.run_bind, Id.run_pure]
  apply forIn_inv (β := ℤ × ℤ × ℤ × ℤ × Option α × List ℤ) (I := fun s => Q s.2.2.2.2.1)
  · simpa using h0
  · intro a _ s hs
    split_ifs with h1 <;> simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt,
      ge_iff_le, not_le] at h1 <;> first
      | exact hs
      | exact hf _ (by omega) (by omega)

theorem Bkw.samplesNeeded_nonneg (u : Fx) : 0 ≤ samplesNeeded u := by
  have hceil : ∀ a : Fx, 0 ≤ a → 0 ≤ ceil a := by
    intro a ha; unfold ceil
    rw [Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt ONE_pos)]
    have h1 : -a ≤ 0 := by linarith
    have : -a / ONE ≤ 0 := Int.ediv_nonpos_of_nonpos_of_neg h1 ONE_pos
    linarith
  have hln : ln (ofRat 1 50) < 0 := by decide +kernel
  unfold samplesNeeded
  split
  · decide
  split
  · apply hceil
    apply Int.ediv_nonneg
    · have : (0 : ℤ) < 2 ^ (max 53 (2 * ceil (mul u LOG2E / 2)).toNat) := by positivity
      nlinarith
    · unfold floor
      rw [Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt ONE_pos)]
      apply Int.ediv_nonneg _ (le_of_lt ONE_pos)
      have := exp2_nonneg (ofInt ↑(max 53 (2 * ceil (mul u LOG2E / 2)).toNat) - mul u LOG2E)
      have : (0 : ℤ) ≤ ONE / 2 := by decide
      linarith
  · apply hceil
    have hd : ln (ONE - exp (-u)) ≤ 0 := by
      have h0 := exp2_nonneg (mul (-u) LOG2E)
      have h1 : log2 (ONE - exp (-u)) ≤ 0 := by
        apply log2_nonpos; unfold exp; linarith
      unfold ln mul
      rw [Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt ONE_pos)]
      exact Int.ediv_nonpos_of_nonpos_of_neg (by nlinarith [show (0 : ℤ) ≤ LN2 by decide]) ONE_pos
    unfold div
    have hn : 2 * ln (ofRat 1 50) * ONE ≤ 0 := by nlinarith [ONE_pos]
    rcases lt_or_eq_of_le hd with hd | hd
    · rw [← Int.neg_fdiv_neg]
      exact Int.fdiv_nonneg (by linarith) (by linarith)
    · rw [hd]; simp

end SigabaNeo.Lattices.Estimator

namespace SigabaNeo.Lattices.Estimator

open Fx NumMisc Bkw

theorem Bkw.accum_nonneg {p : LWEParams} {se : Fx} {b n t1 top x steps : ℕ} {codes : List ℕ}
    {m half samples : ℤ} (hs : ¬ p.Xs.stddev > se) (ht1 : t1 * b ≤ p.n) (ht1s : t1 ≤ steps)
    (hm : 0 ≤ m) (hh : 0 ≤ half) (hsam : samples = steps * half + ofInt m) :
    0 ≤ accum p se b n t1 top x codes m half samples := by
  have hom : 0 ≤ ofInt m := by unfold ofInt; have := ONE_pos; positivity
  unfold accum
  simp only [hs, ite_false, Id.run_bind]
  generalize hr : (forIn (m := Id) (_ : Std.Legacy.Range) (0 : ℤ) _ : Id ℤ) = r
  have hr0 : (0 : ℤ) ≤ r := by
    rw [← hr]
    apply forIn_inv (β := ℤ) (I := fun c => 0 ≤ c)
    · exact le_rfl
    · intro i hi c hc
      simp only [Std.Legacy.Range.size, List.mem_range'_1] at hi
      show 0 ≤ c + ((p.n : ℤ) + 1 - (i : ℤ) * b) * (samples - i * half)
      have h1 : (i : ℤ) * b ≤ p.n := by
        have : i * b ≤ t1 * b := Nat.mul_le_mul_right _ (by omega)
        exact_mod_cast this.trans ht1
      have h2 : (i : ℤ) * half ≤ steps * half := Int.mul_le_mul_of_nonneg_right (by omega) hh
      nlinarith
  show 0 ≤ (forIn (m := Id) codes.zipIdx (r, top + x) _ : Id (ℤ × ℕ)).1
  apply list_forIn_inv (β := ℤ × ℕ) (I := fun s => 0 ≤ s.1)
  · exact hr0
  · intro vi _ s hs'
    obtain ⟨v, i⟩ := vi
    show 0 ≤ s.1 + 4 * (ofInt m + ((i : ℤ) + 1) * half) * v + ((s.2 + v : ℕ) : ℤ) * (ofInt m + i * half)
    have : 0 ≤ (i : ℤ) * half := by positivity
    positivity

end SigabaNeo.Lattices.Estimator

namespace SigabaNeo.Lattices.Estimator

open Fx NumMisc Bkw

theorem Bkw.finish_none {p : LWEParams} {se lq : Fx} {b top x : ℕ} {m table samples c : ℤ}
    {K : ℕ} (hc : 0 ≤ c) (hm : 0 ≤ m) (hz : 0 ≤ zOf p)
    (herf : Bkw.erf (div (zOf p) (Fx.sqrt (2 * se))) = ONE) (hlq : 0 ≤ lq)
    (htab : (2 : ℤ) ^ K ≤ table) (hK : 1024 ≤ K) :
    finish p se lq b top x m table samples c = none := by
  have hg : ONE ≤ (if top == 0 then ONE else (2 * zOf p + ONE) ^ top / ONE ^ (top - 1)) := by
    split
    · exact le_rfl
    · rename_i ht
      have ht : top ≠ 0 := by simpa using ht
      have hpos : (0 : ℤ) < ONE ^ (top - 1) := by have := ONE_pos; positivity
      rw [Int.le_ediv_iff_mul_le hpos, ← pow_succ', show top - 1 + 1 = top by omega]
      exact pow_le_pow_left₀ (le_of_lt ONE_pos) (by linarith) _
  set g := (if top == 0 then ONE else (2 * zOf p + ONE) ^ top / ONE ^ (top - 1)) with hgdef
  have hO := ONE_pos
  have htab0 : (0 : ℤ) ≤ table := le_trans (by positivity) htab
  have hmul : table * ONE ≤ mul g (table * ((b : ℤ) * lq + ONE)) := by
    unfold mul
    rw [Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt ONE_pos), Int.le_ediv_iff_mul_le ONE_pos]
    have h1 : table * ONE ≤ table * ((b : ℤ) * lq + ONE) := by
      apply Int.mul_le_mul_of_nonneg_left _ htab0; have : 0 ≤ (b : ℤ) * lq := by positivity
      linarith
    have h2 : 0 ≤ table * ((b : ℤ) * lq + ONE) := le_trans (by positivity) h1
    nlinarith
  have hc' : (2 : ℤ) ^ K * ONE ≤ c + g * m * top + ofInt (4 * m * x) +
      mul g (table * ((b : ℤ) * lq + ONE)) := by
    have : 0 ≤ g * m * top := by have : 0 ≤ g := by linarith
                                 positivity
    have : 0 ≤ ofInt (4 * m * x) := by unfold ofInt; positivity
    nlinarith
  have hlog : (K : ℤ) * ONE ≤ log2 (c + g * m * top + ofInt (4 * m * x) +
      mul g (table * ((b : ℤ) * lq + ONE))) := by
    have := log2_mono hc'
    have e : (2 : ℤ) ^ K * ONE = ofInt ((2 ^ K : ℕ) : ℤ) := by unfold ofInt; push_cast; ring
    rw [e, log2_ofInt_two_pow] at this
    exact this
  have hK' : (1024 : ℤ) * ONE ≤ K * ONE :=
    Int.mul_le_mul_of_nonneg_right (by exact_mod_cast hK) (by positivity)
  unfold finish
  simp only []
  rw [← hgdef]
  have hb : ¬ ((if (top == 0 || se == 0) = true then
      log2 (c + g * m * top + ofInt (4 * m * x) + mul g (table * ((b : ℤ) * lq + ONE)))
    else log2 (c + g * m * top + ofInt (4 * m * x) + mul g (table * ((b : ℤ) * lq + ONE))) -
      top * log2 (Bkw.erf (div (zOf p) (Fx.sqrt (2 * se))))) < 1024 * ONE) := by
    rw [herf, log2_ONE]
    split <;> (try simp only [mul_zero, sub_zero]) <;> linarith
  simp only [hb, guard]
  rfl

end SigabaNeo.Lattices.Estimator

namespace SigabaNeo.Lattices.Estimator

open Fx NumMisc Bkw

theorem Bkw.candidate_none {p : LWEParams} {se lq : Fx} {b steps e : ℕ} (hq : p.q = 2 ^ e)
    (he : 1024 ≤ e) (hb : 1 ≤ b) (hs : ¬ p.Xs.stddev > se) (hz : 0 ≤ zOf p)
    (herf : Bkw.erf (div (zOf p) (Fx.sqrt (2 * se))) = ONE) (hlq : 0 ≤ lq) :
    Bkw.candidate p se lq b steps = none := by
  have htab : (2 : ℤ) ^ e ≤ (p.q : ℤ) ^ b := by
    rw [hq]; push_cast; rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_right e hb)
  have htab1 : (1 : ℤ) ≤ (p.q : ℤ) ^ b := le_trans (one_le_pow₀ (by norm_num)) htab
  cases h : Bkw.candidate p se lq b steps with
  | none => rfl
  | some r =>
    exfalso
    unfold Bkw.candidate at h
    simp only [] at h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
    rw [Bkw.finish_none (K := e) (Bkw.accum_nonneg hs ?_ ?_ (Bkw.samplesNeeded_nonneg _) ?_ rfl)
      (Bkw.samplesNeeded_nonneg _) hz herf hlq htab he] at h
    · exact absurd h (by simp)
    · exact (Nat.mul_le_mul_right b (min_le_left _ _)).trans (Nat.div_mul_le_self _ _)
    · exact (min_le_right _ _).trans ((List.countP_le_length ..).trans (by simp))
    · apply Int.ediv_nonneg _ (by norm_num)
      exact mul_nonneg (by linarith) (le_of_lt ONE_pos)

theorem Bkw.cost_eq_none {p : LWEParams} {e : ℕ} (hq : p.q = 2 ^ e) (he : 1024 ≤ e)
    (hs : ¬ p.normalize.Xs.stddev > p.normalize.Xe.stddev) (hz : 0 ≤ zOf p.normalize)
    (herf : Bkw.erf (div (zOf p.normalize) (Fx.sqrt (2 * p.normalize.Xe.stddev))) = ONE) :
    Bkw.cost p = none := by
  have hq' : p.normalize.q = 2 ^ e := by rw [LWEParams.normalize_q, hq]
  have hjoin : ∀ budget, (NumMisc.search 2 (3 * (ceil (log2Nat p.normalize.q)).toNat)
      (fun b => (NumMisc.search 2 (max 3 (p.normalize.n / b))
        (Bkw.candidate p.normalize p.normalize.Xe.stddev (log2Nat p.normalize.q) b)
        (Bkw.smaller budget)).join) (Bkw.smaller budget)).join = none := by
    intro budget
    apply NumMisc.search_inv_range (Q := fun o => o.join = none)
    · rfl
    intro b hb _
    show (NumMisc.search 2 _ _ _).join = none
    apply NumMisc.search_inv_range (Q := fun o => o.join = none)
    · rfl
    intro steps _ _
    exact Bkw.candidate_none hq' he (by omega) hs hz herf (log2Nat_nonneg _)
  unfold Bkw.cost
  simp only []
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size]
  rw [show (p.normalize.m.getD 0 + 2 - 0 + 1 - 1) / 1 = (p.normalize.m.getD 0 + 1) + 1 by omega,
    List.range'_succ, List.forIn_cons]
  simp [hjoin]

end SigabaNeo.Lattices.Estimator
