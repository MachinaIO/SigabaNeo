import SigabaNeo.Lib.Lattices.Homomorphic.Norm
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Int.Interval

/-!
# Centered boxes in `ℤ_Q`

* `cenEmb B`: `B` bits as a centered residue in `[−2^{B−1}, 2^{B−1})`, injective when `2^B ≤ Q`; every
  residue with `|x| ≤ 2^{B−1} − 1` is reached (`exists_cenEmb`).
* `ballZ r`: the residues with `|x| ≤ r`; it has `2r + 1` elements when `2r < Q` (`card_ballZ`).
* `bigBox B`, `ball r` on vectors indexed by a finite type: the images of bits and the products of
  balls, with `ball (2^{B−1} − 1) ⊆ bigBox B` and their cardinalities.
* `pow_sub_pow_le`: `a^n − (a − c)^n ≤ n c a^{n−1}`, for the abort probability of box rejection.
-/

namespace SigabaNeo.Lattices

variable {Q : ℕ} [NeZero Q]

/-- `B` bits as a natural number below `2^B`. -/
def bitsEquiv (B : ℕ) : (Fin B → Bool) ≃ Fin (2 ^ B) :=
  (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- **Centered bits**: `B` bits as the residue of `i − 2^{B−1}`. -/
def cenEmb (B : ℕ) (hB : 2 ^ B ≤ Q) : (Fin B → Bool) ↪ ZMod Q where
  toFun bs := (((bitsEquiv B bs : ℕ) : ℤ) - 2 ^ (B - 1) : ℤ)
  inj' a b h := by
    simp only at h
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
    have ha := (bitsEquiv B a).isLt
    have hb := (bitsEquiv B b).isLt
    have h0 : (((bitsEquiv B a : ℕ) : ℤ) - ((bitsEquiv B b : ℕ) : ℤ)) = 0 := by
      have := Int.eq_zero_of_abs_lt_dvd (m := (Q : ℤ))
        (x := ((bitsEquiv B b : ℕ) : ℤ) - 2 ^ (B - 1) - (((bitsEquiv B a : ℕ) : ℤ) - 2 ^ (B - 1))) h
        (by rw [abs_lt]; constructor <;> push_cast <;> omega)
      omega
    exact (bitsEquiv B).injective (Fin.ext (by omega))

theorem exists_cenEmb (B : ℕ) (hB : 2 ^ B ≤ Q) (hB1 : 1 ≤ B) (x : ZMod Q)
    (hx : zabs x ≤ 2 ^ (B - 1) - 1) : ∃ bs, cenEmb B hB bs = x := by
  have hpow : (2 : ℤ) ^ B = 2 * 2 ^ (B - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpowN : 2 ^ B ≤ Q := hB
  have hv : x.valMinAbs.natAbs ≤ 2 ^ (B - 1) - 1 := hx
  have hpos : (1 : ℤ) ≤ 2 ^ (B - 1) := one_le_pow₀ (by norm_num)
  have habs : |x.valMinAbs| ≤ 2 ^ (B - 1) - 1 := by
    have h1 : 1 ≤ 2 ^ (B - 1) := Nat.one_le_two_pow
    have := Int.ofNat_le.mpr hv
    push_cast [Nat.cast_sub h1] at this
    exact this
  rw [abs_le] at habs
  set i : ℕ := (x.valMinAbs + 2 ^ (B - 1)).toNat
  have hi : (i : ℤ) = x.valMinAbs + 2 ^ (B - 1) := by
    simp only [i]; rw [Int.toNat_of_nonneg]; linarith
  have hlt : i < 2 ^ B := by
    have : (i : ℤ) < 2 ^ B := by rw [hi, hpow]; linarith
    exact_mod_cast this
  refine ⟨(bitsEquiv B).symm ⟨i, hlt⟩, ?_⟩
  change ((((bitsEquiv B ((bitsEquiv B).symm ⟨i, hlt⟩) : ℕ) : ℤ) - 2 ^ (B - 1) : ℤ) : ZMod Q) = x
  rw [Equiv.apply_symm_apply]
  change (((i : ℤ) - 2 ^ (B - 1) : ℤ) : ZMod Q) = x
  rw [hi]
  simp

/-- The residues within `r`. -/
def ballZ (Q : ℕ) [NeZero Q] (r : ℕ) : Finset (ZMod Q) := Finset.univ.filter fun x => zabs x ≤ r

theorem card_ballZ (r : ℕ) (hr : 2 * r < Q) : (ballZ Q r).card = 2 * r + 1 := by
  have himg : ballZ Q r = (Finset.Icc (-(r : ℤ)) r).image (fun z : ℤ => (z : ZMod Q)) := by
    ext x
    simp only [ballZ, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_Icc]
    constructor
    · intro hx
      refine ⟨x.valMinAbs, ?_, ZMod.coe_valMinAbs x⟩
      have : x.valMinAbs.natAbs ≤ r := hx
      omega
    · rintro ⟨z, hz, rfl⟩
      exact (zabs_intCast_le z).trans (by omega)
  rw [himg, Finset.card_image_of_injOn]
  · simp; omega
  · intro a ha b hb h
    simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
    simp only at h
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
    have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    omega

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The vectors of centered bits. -/
def bigBox (B : ℕ) (hB : 2 ^ B ≤ Q) : Finset (ι → ZMod Q) :=
  Finset.univ.map (Function.Embedding.piCongrRight fun _ : ι => cenEmb B hB)

/-- The vectors within `r` in every coordinate. -/
def ball (Q : ℕ) [NeZero Q] (r : ℕ) : Finset (ι → ZMod Q) := Fintype.piFinset fun _ => ballZ Q r

theorem mem_ball {r : ℕ} {v : ι → ZMod Q} : v ∈ ball Q r ↔ ∀ i, zabs (v i) ≤ r := by
  simp [ball, ballZ]

theorem ball_subset_bigBox (B : ℕ) (hB : 2 ^ B ≤ Q) (hB1 : 1 ≤ B) :
    (ball Q (2 ^ (B - 1) - 1) : Finset (ι → ZMod Q)) ⊆ bigBox B hB := by
  intro v hv
  rw [mem_ball] at hv
  choose bs hbs using fun i => exists_cenEmb B hB hB1 (v i) (hv i)
  simp only [bigBox, Finset.mem_map, Finset.mem_univ, true_and]
  exact ⟨bs, funext hbs⟩

theorem card_bigBox (B : ℕ) (hB : 2 ^ B ≤ Q) :
    (bigBox (ι := ι) B hB).card = (2 ^ B) ^ Fintype.card ι := by
  simp [bigBox, Fintype.card_fun, Fintype.card_bool]

theorem card_ball (r : ℕ) (hr : 2 * r < Q) :
    (ball Q r : Finset (ι → ZMod Q)).card = (2 * r + 1) ^ Fintype.card ι := by
  simp [ball, Fintype.card_piFinset, card_ballZ r hr]

/-- `a^n − (a − c)^n ≤ n c a^{n−1}`. -/
theorem pow_sub_pow_le (a c : ℕ) (hc : c ≤ a) : ∀ n : ℕ, a ^ n - (a - c) ^ n ≤ n * c * a ^ (n - 1)
  | 0 => by simp
  | n + 1 => by
    have ih := pow_sub_pow_le a c hc n
    have h1 : (a - c) ^ n ≤ a ^ n := Nat.pow_le_pow_left (Nat.sub_le _ _) _
    -- a^{n+1} − (a−c)^{n+1} = a (a^n − (a−c)^n) + c (a−c)^n
    have key : a ^ (n + 1) - (a - c) ^ (n + 1) ≤ a * (a ^ n - (a - c) ^ n) + c * a ^ n := by
      have e1 : a ^ (n + 1) = a * a ^ n := by ring
      have e2 : (a - c) ^ (n + 1) = (a - c) * (a - c) ^ n := by ring
      rw [e1, e2, Nat.mul_sub]
      have : (a - c) * (a - c) ^ n = a * (a - c) ^ n - c * (a - c) ^ n := by
        rw [Nat.sub_mul]
      rw [this]
      have h3 : c * (a - c) ^ n ≤ a * (a - c) ^ n := Nat.mul_le_mul_right _ hc
      have h4 : c * (a - c) ^ n ≤ c * a ^ n := Nat.mul_le_mul_left _ h1
      have h5 : a * (a - c) ^ n ≤ a * a ^ n := Nat.mul_le_mul_left _ h1
      omega
    refine key.trans ((Nat.add_le_add_right (Nat.mul_le_mul_left a ih) _).trans (le_of_eq ?_))
    rcases n with _ | n
    · simp
    · simp only [Nat.add_sub_cancel, pow_succ]
      ring

end SigabaNeo.Lattices
