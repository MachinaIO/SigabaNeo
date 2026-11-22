module

public import SigabaNeo.Lib.Lattices.Research.Wall1.ThetaProfile
public import SigabaNeo.Lib.Lattices.Research.Wall1.ConditionalReduction
import all SigabaNeo.Lib.Lattices.Research.Wall1.UniquenessProbability
import all SigabaNeo.Lib.Lattices.Research.Wall1.CBDQuadratic
import all SigabaNeo.Lib.Lattices.Research.Wall1.HeightZeroFloor
import Mathlib.Tactic

public section

namespace SigabaNeo.Wall1

open SampleDeletion CBDTail Matrix InnerProductSpace CBDQuadratic Classical

variable {N d : ℕ}

/-- Excess over the zero term at height `k`, for the given length profile. -/
noncomputable def profileExcess (t : Fin d → ℝ) (k : ℝ) : ℝ :=
  (∏ i, thetaFactor ((1 / (12 * k^2)) * (t i)^2)) - 1

/-- The Cantelli charge and all height charges for a fixed block. -/
noncomputable def FinalBlock.errGeom (B : FinalBlock N d) (L : ℝ) : ℝ :=
  let a := L^2 - 1 - (3/2)*(d : ℝ)
  let v := (9/2)*(d : ℝ)
  let t i := ‖gramSchmidt ℝ B.basis i‖
  v/(v+a^2) + profileExcess t 1 +
    ∑ k ∈ Finset.Icc 2 (Nat.sqrt (9*N+1)), profileExcess t k

/-- The two numerical allowances on the terminal and prefix lengths, together with
the minimum and positive gap required by the Cantelli bound. -/
def FinalBlock.profileAccept {J : ℕ} (B : FinalBlock N d) (p : Fin J → ℝ) (L ε ℓ : ℝ) : Prop :=
  B.errGeom L ≤ ε ∧ 0 ≤ L ∧ 0 < L^2 - 1 - (3/2)*(d : ℝ) ∧
    (∀ h ∈ Submodule.span ℤ (Set.range B.basis), h ≠ (0 : B.V) → L ≤ ‖h‖) ∧
    (∑ j, 2 * Real.exp (-(p j)^2 / 12)) ≤ ℓ

private theorem collisionUnion {Ω V : Type*} [Fintype Ω] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (b : Module.Basis (Fin d) ℝ V) {s : ℝ} (hs : 0 < s)
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hit : V → Ω → Prop)
    (bound : ∀ v, (∑ x with hit v x, p x) ≤ Real.exp (-s * ‖v‖^2)) :
    (∑ x with ∃ v ∈ Submodule.span ℤ (Set.range b), v ≠ (0 : V) ∧ hit v x, p x) ≤
      (∏ i, thetaFactor (s * ‖gramSchmidt ℝ b i‖^2)) - 1 := by
  classical
  let v (c : Fin d → ℤ) : V := ∑ i, (c i : ℝ) • b i
  let F (c : Fin d → ℤ) := Real.exp (-s * ‖v c‖^2)
  let A := Finset.univ.filter fun x ↦
    ∃ h ∈ Submodule.span ℤ (Set.range b), h ≠ (0 : V) ∧ hit h x
  have witness (x) (hx : x ∈ A) : ∃ c, c ≠ 0 ∧ hit (v c) x := by
    obtain ⟨h, hh, hn, hhit⟩ := (Finset.mem_filter.mp hx).2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hh
    have eq : v c = h := by simpa [v, Int.cast_smul_eq_zsmul] using hc
    exact ⟨c, fun hz ↦ hn (by simp [← eq, hz, v]), eq.symm ▸ hhit⟩
  let pick x := if hx : x ∈ A then (witness x hx).choose else 0
  let S := A.image pick
  have spec x (hx : x ∈ A) : pick x ≠ 0 ∧ hit (v (pick x)) x := by
    simpa [pick, hx] using (witness x hx).choose_spec
  have h0 : 0 ∉ S := by
    intro h
    obtain ⟨x, hx, eq⟩ := Finset.mem_image.mp h
    exact (spec x hx).1 eq
  have mass : ∑ x ∈ A, p x ≤ ∑ c ∈ S, F c := by
    rw [← Finset.sum_fiberwise_of_maps_to (fun x hx ↦ Finset.mem_image_of_mem pick hx)]
    apply Finset.sum_le_sum
    intro c _
    apply le_trans _ (bound (v c))
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun x _ _ ↦ hp x)
    intro x hx
    obtain ⟨ha, hc⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc ▸ (spec x ha).2⟩
  obtain ⟨summ, total⟩ := latticeThetaProfile b hs
  change Summable F at summ
  change (∑' c, F c) ≤ _ at total
  have h := summ.sum_le_tsum (insert 0 S) (fun c _ ↦ (Real.exp_pos _).le)
  change (∑ c ∈ insert 0 S, F c) ≤ ∑' c, F c at h
  rw [Finset.sum_insert h0, show F 0 = 1 by simp [F, v]] at h
  change (∑ x ∈ A, p x) ≤ _
  linarith

/-- CBD(3) mass of all-heights uniqueness for a fixed projection and horizontal lattice. -/
private theorem uniquenessProfile (Q : Matrix (Fin N) (Fin N) ℝ) (hs : Q.transpose = Q)
    (hp : Q*Q = Q) (trace : Q.trace = d)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    (fixed : ∀ h : V, Q.mulVec (WithLp.ofLp h.val) = WithLp.ofLp h.val)
    (b : Module.Basis (Fin d) ℝ V) {L : ℝ} (hL : 0 ≤ L)
    (minimum : ∀ h ∈ Submodule.span ℤ (Set.range b), h ≠ (0 : V) → L ≤ ‖h‖)
    (gap : 0 < L^2 - 1 - (3/2)*(d : ℝ)) :
    let a := L^2 - 1 - (3/2)*(d : ℝ)
    let v := (9/2)*(d : ℝ)
    1 - (v/(v+a^2) + profileExcess (fun i ↦ ‖gramSchmidt ℝ b i‖) 1 +
      ∑ k ∈ Finset.Icc 2 (Nat.sqrt (9*N+1)), profileExcess (fun i ↦ ‖gramSchmidt ℝ b i‖) k) ≤
      ∑ w with allHeightsUnique (horizontalLattice V b) (projectedCBD Q w), jointWeight w := by
  classical
  intro a v
  let m := (3/2)*(d : ℝ)
  let B := Submodule.span ℤ (Set.range b)
  let y := projectedCBD Q
  let U w := allHeightsUnique (horizontalLattice V b) (y w)
  let Z w := m+a ≤ quadratic Q w
  let O w := ∃ h ∈ B, h ≠ (0 : V) ∧ ‖y w + h.val‖ ≤ ‖y w‖
  let T (k : ℕ) w := ∃ h ∈ B, h ≠ (0 : V) ∧
    ‖h.val + (k : ℝ) • y w‖^2 + (k : ℝ)^2 ≤ ‖y w‖^2 + 1
  let S := Finset.Icc 2 (Nat.sqrt (9*N+1))
  let mass (P : (Fin N → Digit 3) → Prop) := ∑ w with P w, jointWeight w
  have cover w (hz : ¬Z w) (ho : ¬O w) (ht : ∀ k ∈ S, ¬T k w) : U w := by
    apply (allHeightsUniquenessCriterion _ _).2
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨h, hh, rfl⟩ hn
      have hl := minimum h hh (fun eq ↦ hn (by simp [eq]))
      change ‖projectedCBD Q w‖^2 + 1 < ‖h‖^2
      rw [projectedCBD_norm_sq Q hs hp]
      change ¬ m+a ≤ quadratic Q w at hz
      dsimp [m,a] at hz
      nlinarith [sq_le_sq' (by linarith : -‖h‖ ≤ L) hl]
    · rintro _ ⟨h, hh, rfl⟩ hn
      have lt : ‖y w‖ < ‖y w + h.val‖ := lt_of_not_ge fun e ↦
        ho ⟨h, hh, fun eq ↦ hn (by simp [eq]), e⟩
      change ‖y w‖^2 < ‖h.val + y w‖^2
      rw [add_comm]
      exact pow_lt_pow_left₀ lt (norm_nonneg _) (by decide)
    · intro k hk hcap
      lift k to ℕ using (by omega)
      rintro _ ⟨h, hh, rfl⟩
      push_cast at hcap ⊢
      have bound : (k : ℝ)^2 ≤ 9*N+1 := by linarith [energyCap Q hs hp w]
      have mem : k ∈ S := Finset.mem_Icc.mpr ⟨by omega, Nat.le_sqrt'.mpr (by exact_mod_cast bound)⟩
      by_contra! hit
      have hit' : ‖h.val + (k : ℝ) • y w‖^2 + (k : ℝ)^2 ≤ ‖y w‖^2 + 1 := by
        rw [Nat.cast_smul_eq_nsmul ℝ]
        change ‖h.val + (k : ℤ) • y w‖^2 ≤ ‖y w‖^2 + 1 - (k : ℝ)^2 at hit
        simp only [natCast_zsmul] at hit
        linarith
      have hn := (highHit _ _ _ (by exact_mod_cast (show 2 ≤ k by omega)) hit').1
      exact ht k mem ⟨h, hh, fun eq ↦ hn (by simp [eq]), hit'⟩
  have sumBound : 1 ≤ mass U + mass Z + mass O + ∑ k ∈ S, mass (T k) := by
    rw [← joint_mass (N := N)]
    simp only [mass, Finset.sum_filter]
    rw [Finset.sum_comm (s := S)]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro w _
    have pos (P : Prop) [Decidable P] : 0 ≤ (if P then jointWeight w else 0) := by
      split <;> simp [weightNonneg]
    have nonneg := Finset.sum_nonneg (s := S) (fun k _ ↦ pos (T k w))
    by_cases hu : U w
    · simp [hu]; linarith [pos (Z w), pos (O w)]
    by_cases hz : Z w
    · simp [hu,hz]; linarith [pos (O w)]
    by_cases ho : O w
    · simp [hu,hz,ho,nonneg]
    have ex : ∃ k ∈ S, T k w := by by_contra! no; exact hu (cover w hz ho no)
    obtain ⟨k,hk,hit⟩ := ex
    simpa [hu,hz,ho,hit] using Finset.single_le_sum (fun j _ ↦ pos (T j w)) hk
  have hzero := cantelliUpper jointWeight (quadratic Q) weightNonneg joint_mass a gap
  simp only [quadratic_mean, trace] at hzero
  let var := ∑ w, jointWeight w * (quadratic Q w-m)^2
  have hv : 0 ≤ var := Finset.sum_nonneg fun w _ ↦ mul_nonneg (weightNonneg _) (sq_nonneg _)
  have hv' : var ≤ v := by simpa [var,m,v,trace] using projection_variance_le Q hs hp
  have bz : mass Z ≤ v/(v+a^2) := by
    apply (show mass Z ≤ var/(var+a^2) from hzero).trans
    apply (div_le_div_iff₀ (by positivity) (by dsimp [v]; positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hv' (sq_nonneg a)]
  have bo : mass O ≤ profileExcess (fun i ↦ ‖gramSchmidt ℝ b i‖) 1 := by
    apply collisionUnion b (s := 1 / (12 * (1 : ℝ)^2)) (by norm_num)
      jointWeight weightNonneg (fun h w ↦ ‖y w + h.val‖ ≤ ‖y w‖)
    intro h
    have t := heightOneVector Q hs h.val (fixed h)
    simp only [sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)] at t
    convert t using 2
    norm_num
    ring
  have bt := Finset.sum_le_sum (s := S) (fun k hk ↦
    (show mass (T k) ≤ profileExcess (fun i ↦ ‖gramSchmidt ℝ b i‖) k by
      have hk' : (2 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      have hkpos : (0 : ℝ) < k := by linarith
      apply collisionUnion b (s := 1 / (12 * (k : ℝ)^2)) (by positivity)
        jointWeight weightNonneg (fun h w ↦
          ‖h.val + (k : ℝ) • y w‖^2 + (k : ℝ)^2 ≤ ‖y w‖^2 + 1)
      intro h
      have t := highVector Q hs h.val (fixed h) k hk'
      apply t.trans_eq
      congr 1
      change -‖h‖^2 / _ = -(_ / _) * ‖h‖^2
      ring))
  change 1 - _ ≤ mass U
  linarith

/-- Fixed-block CBD(3) failure mass with actual Gram–Schmidt lengths at every height. -/
theorem FinalBlock.failure_le_errGeom (B : FinalBlock N d) {L : ℝ} (hL : 0 ≤ L)
    (minimum : ∀ h ∈ Submodule.span ℤ (Set.range B.basis), h ≠ (0 : B.V) → L ≤ ‖h‖)
    (gap : 0 < L^2 - 1 - (3/2)*(d : ℝ)) :
    (∑ w with ¬allHeightsUnique (horizontalLattice B.V B.basis) (projectedCBD B.Q w),
      jointWeight w) ≤ B.errGeom L := by
  have h := uniquenessProfile B.Q B.symmetric B.idempotent B.trace_eq B.V B.fixed B.basis hL
    minimum gap
  change 1 - B.errGeom L ≤ ∑ w with allHeightsUnique (horizontalLattice B.V B.basis)
    (projectedCBD B.Q w), jointWeight w at h
  have mass := joint_mass (N := N)
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun w ↦ allHeightsUnique (horizontalLattice B.V B.basis) (projectedCBD B.Q w))
    (f := jointWeight)] at mass
  linarith

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.FinalBlock.failure_le_errGeom
