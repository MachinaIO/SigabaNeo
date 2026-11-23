import SigabaNeo.Lib.Lattices.Research.Wall1.RawCenteredCount
import SigabaNeo.Lib.Lattices.Research.Wall1.RawScalarMajorant

/-! Transfer the ball estimate to the raw graph and charge scalar collisions coordinatewise. -/
noncomputable section
namespace SigabaNeo.Wall1.LongWinner.FourthMoment.RawCount
open Finset Real RawBallRounding RawScalarWeights
open scoped Classical

private lemma dimension (j : ℕ) : Fintype.card (Index j) = 506+j := by
  simp [Index,DualExit.Coord]; omega

theorem eligible_lower {j : ℕ} (hj : 0 < j) (hj' : j < 53) {r : ℝ} (hr : 1690 ≤ r)
    (hq : r ≤ 3329) : 506/1000 * (rawVolume j * r^(506+j)) ≤ (eligible j r).card := by
  let e : Index j ≃ Fin ((505+j)+1) := Fintype.equivFinOfCardEq (by rw [dimension]; omega)
  let p := e (pivot j)
  let f (z : Fin ((505+j)+1) → ℤ) := fun i ↦ z (e i)
  have hs (z : Fin ((505+j)+1) → ℤ) (hz : z ∈ allowed p r) : f z ∈ eligible j r := by
    obtain ⟨hb,hc,hn⟩ := mem_filter.mp hz
    have en := (mem_closedLifts (by linarith : 0 ≤ r) z).mp hb
    apply mem_filter.mpr
    refine ⟨(SigabaNeo.Planted.mem_integerBall (by linarith) _).2 ⟨?_,?_⟩,fun i ↦ hc (e i),hn⟩
    · exact fun eqn ↦ hn (congrFun eqn (pivot j))
    · exact (e.sum_comp (fun k ↦ (z k : ℝ)^2)).le.trans en
  have hi : Function.Injective f := fun z w he ↦ funext fun i ↦ by
    simpa [f] using congrFun he (e.symm i)
  have hcard := card_le_card_of_injOn f hs hi.injOn
  have h := (allowed_lower (505+j) (by omega) (by omega) p hr hq).trans (Nat.cast_le.mpr hcard)
  change 506/1000 * (unitVolume (506+j) * r^(506+j)) ≤ _
  simpa only [show 505+j+1 = 506+j by omega,mul_comm (r^_)] using h

private def liftEnergy (z : Lift j) : ℕ := ∑ i, (z i).natAbs^2

private lemma energy_le {z : Lift j} {r : ℝ} (hr : 0 ≤ r) (hz : z ∈ eligible j r) :
    (liftEnergy z:ℝ) ≤ r^2 := by
  have h := ((SigabaNeo.Planted.mem_integerBall hr z).mp (mem_filter.mp hz).1).2
  unfold liftEnergy
  rw [Nat.cast_sum]
  refine (le_of_eq (sum_congr rfl (fun i _ ↦ ?_))).trans h
  rw [Nat.cast_pow, ← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, sq_abs]

private lemma lift_coord {z : Lift j} (hz : z ∈ eligible j r) (i : Index j) :
    ((z i : ZMod 3329).valMinAbs) = z i := by
  apply (ZMod.valMinAbs_spec _ _).2
  have h := (mem_filter.mp hz).2.1 i
  rw [abs_le] at h
  exact ⟨rfl,by omega,by omega⟩

/-- Exponential tilting with a rational base bounds all the ordered pairs for one scalar. -/
theorem tilted_pairs {j M : ℕ} {r : ℝ} (hr : 0 ≤ r) (hM : 2*r^2 ≤ M*3072)
    (a : ZMod 3329) (ha : a ∈ scalars)
    (row_bound : ∀ b, 2 ≤ b → b < 3328 → smallRow b ≤ 93700) :
    ((scalarPairs (eligible j r) a).card : ℝ) * (15/16:ℝ)^M ≤ 190^(506+j) := by
  let P := scalarPairs (eligible j r) a
  let encode (v : Lift j × Lift j) (i : Index j) := (v.1 i : ZMod 3329)
  let w (x : ZMod 3329) : ℝ := entry a.val x.val / 1024
  have wn (x) : 0 ≤ w x := by dsimp [w]; positivity
  have point (v : Lift j × Lift j) (hv : v ∈ P) :
      (15/16:ℝ)^M ≤ ∏ i, w (encode v i) := by
    obtain ⟨hs,rel⟩ := mem_filter.mp hv
    obtain ⟨hz,hy⟩ := mem_product.mp hs
    let E (i : Index j) := (v.1 i).natAbs^2 + (v.2 i).natAbs^2
    have bounds : (∑ i, E i / 3072) * 3072 ≤ liftEnergy v.1 + liftEnergy v.2 := by
      rw [sum_mul,liftEnergy,liftEnergy,← sum_add_distrib]
      exact sum_le_sum fun i _ ↦ Nat.div_mul_le_self _ _
    have htotal : ((liftEnergy v.1 + liftEnergy v.2 : ℕ):ℝ) ≤ (M*3072:ℕ) := by
      push_cast
      linarith [energy_le hr hz, energy_le hr hy]
    have H : ∑ i, E i / 3072 ≤ M := by
      have := bounds.trans (Nat.cast_le.mp htotal)
      omega
    calc
      _ ≤ (15/16:ℝ)^(∑ i, E i / 3072) := pow_le_pow_of_le_one (by norm_num) (by norm_num) H
      _ = ∏ i, (15/16:ℝ)^(E i / 3072) := (prod_pow_eq_pow_sum ..).symm
      _ ≤ ∏ i, w (encode v i) := by
        apply prod_le_prod₀ (fun _ _ ↦ by positivity)
        intro i _
        dsimp only [encode,w]
        rw [entry_field,← rel i,lift_coord hz,lift_coord hy]
        exact pow_le_bucket _
  have inj : Set.InjOn encode P := by
    intro v hv u hu he
    obtain ⟨vs,rv⟩ := mem_filter.mp hv
    obtain ⟨us,ru⟩ := mem_filter.mp hu
    obtain ⟨v1,v2⟩ := mem_product.mp vs
    obtain ⟨u1,u2⟩ := mem_product.mp us
    have eq1 (i) : (v.1 i : ZMod 3329) = u.1 i := congrFun he i
    apply Prod.ext <;> funext i
    · rw [← lift_coord v1 i,← lift_coord u1 i,eq1]
    · rw [← lift_coord v2 i,← lift_coord u2 i,rv,ru,eq1]
  have rowNat := field_row_le a (mem_filter.mp ha).2.1 (mem_filter.mp ha).2.2.1
    (mem_filter.mp ha).2.2.2 row_bound
  have row : ∑ x, w x ≤ 190 := by
    simp only [w,← sum_div,← Nat.cast_sum]
    apply (div_le_iff₀ (by norm_num)).2
    exact_mod_cast rowNat
  have h := sum_le_sum (s := P) point
  simp only [sum_const,nsmul_eq_mul] at h
  apply h.trans
  rw [← sum_image (s := P) (f := fun x ↦ ∏ i, w (x i)) inj]
  calc
    _ ≤ ∑ x : Index j → ZMod 3329, ∏ i, w (x i) := sum_le_sum_of_subset_of_nonneg
      (subset_univ _) (fun x _ _ ↦ prod_nonneg fun i _ ↦ wn _)
    _ = (∑ x, w x)^(506+j) := by rw [← Fintype.prod_sum,prod_const,card_univ,dimension]
    _ ≤ _ := pow_le_pow_left₀ (sum_nonneg fun _ _ ↦ wn _) row _

end SigabaNeo.Wall1.LongWinner.FourthMoment.RawCount
