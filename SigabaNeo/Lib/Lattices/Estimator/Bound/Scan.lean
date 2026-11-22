import SigabaNeo.Lib.Lattices.Estimator.Bound.Search

/-!
# Lower bounds for the scanning attacks (uSVP, dual)

`Usvp.cost` and `Dual.cost` scan block sizes below `maxBeta`. The modulus enters them only through
`log₂ q` (and `q = 0`), so at `q = 2^e` they are `Usvp.costQ (e·2^P)` and `Dual.costQ (e·2^P) false`,
which never compute `q` (the kernel refuses `2^(2^25)`). A lower bound on each scanned candidate,
checked by evaluation over chunks of block sizes (`allRange`), is a lower bound on the attack.
-/

namespace SigabaNeo.Lattices.Estimator

open Fx

/-- `f b` for all `b ∈ [a, a + n)`. -/
def allRange (a n : ℕ) (f : ℕ → Bool) : Bool := (List.range' a n).all f

theorem allRange_spec {a n : ℕ} {f : ℕ → Bool} (h : allRange a n f = true) :
    ∀ b, a ≤ b → b < a + n → f b = true := by
  intro b h1 h2
  unfold allRange at h
  rw [List.all_eq_true] at h
  exact h b (List.mem_range'_1.mpr ⟨h1, h2⟩)

/-- Gluing two ranges. -/
theorem range_glue {P : ℕ → Prop} {a b c : ℕ} (h1 : ∀ x, a ≤ x → x < b → P x)
    (h2 : ∀ x, b ≤ x → x < c → P x) : ∀ x, a ≤ x → x < c → P x := by
  intro x hx1 hx2
  rcases lt_or_ge x b with h | h
  · exact h1 x hx1 h
  · exact h2 x h hx2

theorem ofInt_two_pow (e : ℕ) : ofInt ((2 ^ e : ℕ) : ℤ) = ((2 ^ (e + P) : ℕ) : ℤ) := by
  unfold ofInt; rw [ONE_eq]; push_cast; ring

theorem log2_ofInt_two_pow (e : ℕ) : log2 (ofInt ((2 ^ e : ℕ) : ℤ)) = (e : ℤ) * ONE := by
  unfold log2; rw [ofInt_two_pow, Int.toNat_natCast, log2Nat_two_pow]; push_cast; ring

theorem LWEParams.normalize_q (p : LWEParams) : p.normalize.q = p.q := by
  unfold LWEParams.normalize; split
  · rfl
  · split <;> rfl

theorem foldl_min_ge {k : Fx} {α : Type} (l : List α) (g : α → Cost) {init : Cost}
    (h0 : CostGe k init) (h : ∀ x ∈ l, CostGe k (g x)) :
    CostGe k (l.foldl (fun b x => Cost.min b (g x)) init) := by
  induction l generalizing init with
  | nil => exact h0
  | cons a l ih =>
    exact ih (h0.min (h a (List.mem_cons_self ..))) fun x hx => h x (List.mem_cons_of_mem _ hx)

/-! ### uSVP -/

theorem Usvp.cost_eq_of_q {p : LWEParams} {e : ℕ} (hq : p.q = 2 ^ e) :
    Usvp.cost p = Usvp.costQ ((e : ℤ) * ONE) p := by
  unfold Usvp.cost; rw [hq, log2_ofInt_two_pow]

theorem Usvp.costQ_ge {k l2q : Fx} {p : LWEParams}
    (h : ∀ β, 40 ≤ β → β < maxBeta →
      CostGe k (Usvp.costGsaQ l2q β p.normalize (Usvp.embedM p.normalize))) :
    CostGe k (Usvp.costQ l2q p) := by
  unfold Usvp.costQ
  apply foldl_min_ge _ _ (costGe_none k)
  intro β hβ
  rw [List.mem_range'_1] at hβ
  apply h β hβ.1
  have : Usvp.scanEnd (Usvp.embedM p.normalize) ≤ maxBeta := by
    unfold Usvp.scanEnd; split
    · exact le_rfl
    · exact max_le (min_le_left _ _) (by decide)
  omega

/-! ### Dual -/

theorem Dual.cost_eq_of_q {p : LWEParams} {e : ℕ} (hq : p.q = 2 ^ e) :
    Dual.cost p = Dual.costQ ((e : ℤ) * ONE) false p := by
  unfold Dual.cost; rw [hq, log2Nat_two_pow]
  congr 1; simp

theorem Dual.costQ_ge {k lq : Fx} {p : LWEParams}
    (h : ∀ b, 40 ≤ b → b < maxBeta → CostGe k (Dual.candidate p.normalize (log2 p.normalize.Xs.stddev)
      (log2 p.normalize.Xs.stddev + lq - log2 p.normalize.Xe.stddev) b)) :
    CostGe k (Dual.costQ lq false p) := by
  unfold Dual.costQ
  simp only [Bool.or_false]
  split
  · simp
  · simp only [Id.run_bind]
    apply forIn_inv (β := Cost) (I := CostGe k)
    · simp
    · intro b hb s hs
      simp only [Std.Legacy.Range.size, List.mem_range'_1] at hb
      refine hs.min (h b (by omega) ?_)
      have : max 48 (min maxBeta (p.normalize.m.getD maxBeta)) ≤ maxBeta :=
        max_le (by decide) (min_le_left _ _)
      simp at hb; omega

end SigabaNeo.Lattices.Estimator
