import SigabaNeo.Lib.Lattices.Research.Wall1.LongWinnerRawDirections

/-! Oriented lift counts and modular scalar collisions for the raw winner directions. -/
noncomputable section

namespace SigabaNeo.Wall1.LongWinner.FourthMoment
open ControlledPlane DualExit QaryMembership RawGraphVoid Finset
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

namespace RawCount

abbrev Index (j : ℕ) := Coord 400 (105+j+1)
abbrev Lift (j : ℕ) := Index j → ℤ
abbrev pivot (j : ℕ) : Index j := Sum.inr (Fin.last (105+j))

def centered (z : Lift j) : Prop := ∀ i, |z i| ≤ 1664

def eligible (j : ℕ) (r : ℝ) : Finset (Lift j) :=
  (SigabaNeo.Planted.integerBall r).filter fun z ↦ centered z ∧ z (pivot j) ≠ 0

def scalarPairs (S : Finset (Lift j)) (a : ZMod 3329) : Finset (Lift j × Lift j) :=
  (S ×ˢ S).filter fun p ↦ ∀ i, (p.2 i : ZMod 3329) = a * p.1 i

def scalars : Finset (ZMod 3329) := univ.filter fun a ↦ a ≠ 0 ∧ a ≠ 1 ∧ a ≠ -1

private def point (z : Lift j) : Direction 400 (105+j+1) 3329 :=
  (((z (pivot j) : ZMod 3329)⁻¹) • reduce 3329 (fun i ↦ z (.inl i)),
   ((z (pivot j) : ZMod 3329)⁻¹) • reduce 3329 (fun i ↦ z (.inr i)))

private lemma centered_inj {v w : ℤ} (hv : |v| ≤ 1664) (hw : |w| ≤ 1664)
    (h : (v : ZMod 3329) = w) : v = w := by
  rw [ZMod.intCast_eq_intCast_iff'] at h
  rw [abs_le] at hv hw
  omega

private lemma pivot_ne {z : Lift j} (hz : z ∈ eligible j r) :
    (z (pivot j) : ZMod 3329) ≠ 0 := fun h ↦ (mem_filter.mp hz).2.2
      (centered_inj ((mem_filter.mp hz).2.1 _) (by norm_num : |(0:ℤ)| ≤ 1664) (by simpa using h))

private lemma point_mem {z : Lift j} (hz : z ∈ eligible j r) : point z ∈ rawDirections j r :=
  mem_image.mpr ⟨z,mem_filter.mpr ⟨(mem_filter.mp hz).1,pivot_ne hz⟩,rfl⟩

private lemma norm_eq {z w : Lift j} (h : point z = point w) (i : Index j) :
    (z (pivot j) : ZMod 3329)⁻¹ * z i = (w (pivot j) : ZMod 3329)⁻¹ * w i := by
  cases i with
  | inl i => exact congrFun (congrArg Prod.fst h) i
  | inr i => exact congrFun (congrArg Prod.snd h) i

/-- Every centered eligible lift contributes to a sign pair or to an ordered modular collision.
This estimate counts collisions between distinct rational lines as well as divisible lifts. -/
theorem eligible_card_le (j : ℕ) (r : ℝ) :
    (eligible j r).card ≤ 2 * (rawDirections j r).card +
      ∑ a ∈ scalars, (scalarPairs (eligible j r) a).card := by
  let S := eligible j r
  let B := scalars.biUnion fun a ↦ (scalarPairs S a).image Prod.fst
  have bad : B.card ≤ ∑ a ∈ scalars, (scalarPairs S a).card :=
    card_biUnion_le.trans (sum_le_sum fun _ _ ↦ card_image_le)
  let code (z : Lift j) := (point z, decide (0 < z (pivot j)))
  have hg : (S \ B).card ≤ ((rawDirections j r) ×ˢ (univ : Finset Bool)).card := by
    apply card_le_card_of_injOn code
    · intro z hz
      exact mem_product.mpr ⟨point_mem (mem_sdiff.mp hz).1, mem_univ _⟩
    intro z hz w hw eqn
    obtain ⟨hz,hb⟩ := mem_sdiff.mp hz
    obtain ⟨hw,_⟩ := mem_sdiff.mp hw
    let a : ZMod 3329 := w (pivot j) * (z (pivot j) : ZMod 3329)⁻¹
    have ha : a ≠ 0 := mul_ne_zero (pivot_ne hw) (inv_ne_zero (pivot_ne hz))
    have he (i : Index j) : (w i : ZMod 3329) = a * z i := by
      dsimp [a]
      rw [mul_assoc, norm_eq (congrArg Prod.fst eqn), ← mul_assoc,
        mul_inv_cancel₀ (pivot_ne hw), one_mul]
    have hn := (mem_filter.mp hz).2
    have hm := (mem_filter.mp hw).2
    by_cases h1 : a = 1
    · exact funext fun i ↦ centered_inj (hn.1 i) (hm.1 i) (by simpa [h1] using (he i).symm)
    by_cases hm1 : a = -1
    · have neg : w (pivot j) = -z (pivot j) :=
        centered_inj (hm.1 _) (by simpa using hn.1 (pivot j)) (by simpa [hm1] using he (pivot j))
      have sign : decide (0 < z (pivot j)) = decide (0 < w (pivot j)) := congrArg Prod.snd eqn
      simp only [decide_eq_decide] at sign
      have nz := hn.2
      omega
    · have hs : a ∈ scalars := mem_filter.mpr ⟨mem_univ _,ha,h1,hm1⟩
      have hpair : (z,w) ∈ scalarPairs S a := mem_filter.mpr ⟨mem_product.mpr ⟨hz,hw⟩,he⟩
      have hf : z ∈ (scalarPairs S a).image Prod.fst :=
        mem_image.mpr ⟨(z,w), hpair,rfl⟩
      have hb' : z ∉ scalars.biUnion (fun u ↦ (scalarPairs S u).image Prod.fst) := hb
      exfalso
      apply hb'
      rw [mem_biUnion]
      exact ⟨a,hs,hf⟩
  simp only [card_product, card_univ, Fintype.card_bool] at hg
  have total := card_le_card_sdiff_add_card (s := S) (t := B)
  change S.card ≤ 2 * (rawDirections j r).card + ∑ a ∈ scalars, (scalarPairs S a).card
  omega

end RawCount
end SigabaNeo.Wall1.LongWinner.FourthMoment

#print axioms SigabaNeo.Wall1.LongWinner.FourthMoment.RawCount.eligible_card_le
