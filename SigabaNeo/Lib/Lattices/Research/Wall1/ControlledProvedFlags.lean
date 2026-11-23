import SigabaNeo.Lib.Lattices.Research.Wall1.ControlledProvedProfile

/-! The last-used-coordinate tests for the unconditional log-cap envelope. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane.ProvedProfile
open Real Finset TerminalProjection TerminalProjection.Restart506 DualExit
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

def capSum (k : ℕ) : ℝ := ∑ v ∈ Icc 1 k, Real.log (cap v)

def radius (u : FlagIndex) : ℝ := planeRadius * cap (155-u.1.val-u.2.val)

def detFloor (u : FlagIndex) : ℝ :=
  let k := 155-u.1.val
  terminalLogFloor u.1.val - capSum k + capSum (k-u.2.val) - u.2.val * Real.log planeRadius

/-- Single last-coordinate Gaussian charge. The width prefactor includes
the j factors of T lost in the forced old projections. -/
def charge (u : FlagIndex) : ℝ :=
  let k := 155-u.1.val
  let p := 505-u.2.val
  let w := cap (k-u.2.val)
  let z := max 1 (w * Real.sqrt (2*Real.pi/(p+1:ℝ)))
  planeRadius^506 / 2 * Real.exp (Real.pi * w^2 / z^2 - terminalLogFloor u.1.val +
    capSum k - capSum (k-u.2.val)) * z^(p+1) * (terminalTheta (planeRadius*z))^p

private theorem cap_pos (k : ℕ) : 0 < cap k := exp_pos _

theorem initial_radius (k : ℕ) (hk : k ≤ 155) : planeRadius * cap k ≤ 2896 := by
  have cert : ∀ i : Fin 156, logCap i ≤ 4.568916 := by decide +kernel
  have hl : (logCap k : ℝ) ≤ 4.568916 := by
    simpa using (Rat.cast_le (K := ℝ)).2 (cert ⟨k,by omega⟩)
  have h := TerminalInterval.exp_upper (4.568916/8) 1.770239 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hc : cap k ≤ (1.770239:ℝ)^8 := by
    apply (exp_le_exp.mpr hl).trans
    rw [show (4.568916:ℝ) = (8:ℕ)*((4.568916/8:ℚ):ℝ) by norm_num, exp_nat_mul]
    exact pow_le_pow_left₀ (exp_pos _).le (by simpa using h) 8
  have hr : planeRadius ≤ 30.02222 := by
    unfold planeRadius areaCut
    rw [mul_div_assoc',div_div,← sq,sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    exact (sqrt_le_left (by norm_num)).mpr (by norm_num)
  exact (mul_le_mul hr hc (cap_pos _).le (by norm_num)).trans (by norm_num)

/-- The successive signed old winners in the forced suffix obey their respective
length caps, starting at tail length k. -/
def ForcedLengths {n d : ℕ} : (j k : ℕ) → ChainState n (CoordSpace (d+j)) → Prop
  | 0, _, _ => True
  | j+1, k, s => ‖s.winner‖ ≤ planeRadius * cap k ∧ ForcedLengths j (k-1) s.freeze

/-- Peeling j forced winners loses at most the log-cap difference and j copies
of the terminal log radius. -/
theorem forced_log_covolume {n d : ℕ} (j k : ℕ) (hjk : j ≤ k)
    (s : ChainState n (CoordSpace (d+j))) (h : ForcedLengths j k s) :
    log (ZLattice.covolume s.M)-capSum k+capSum (k-j)-j*log planeRadius ≤
      log (ZLattice.covolume (forceOld j s).M) := by
  induction j generalizing k with
  | zero => simp [forceOld]
  | succ j ih =>
    obtain ⟨hw,hl⟩ := h
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    have step := ih k (by omega) s.freeze hl
    rw [ChainState.freeze_covolume,log_div (ZLattice.covolume_pos s.M _).ne'
      (norm_pos_iff.mpr s.shortest.2.1).ne'] at step
    have hm := log_le_log (norm_pos_iff.mpr s.shortest.2.1) hw
    rw [log_mul (by unfold planeRadius areaCut; positivity) (cap_pos _).ne'] at hm
    have he : capSum (k+1) = capSum k+log (cap (k+1)) := sum_Icc_succ_top (by omega) _
    simp only [he, Nat.succ_sub_succ_eq_sub, Nat.cast_succ,forceOld]
    linarith

private theorem cast_covol {m a b : ℕ} (e : a = b) (s : ChainState (b+m) (CoordSpace b)) :
    let t : ChainState (a+m) (CoordSpace a) := e ▸ s
    ZLattice.covolume t.M = ZLattice.covolume s.M := by
  subst b
  rfl

/-- The explicit last-draw witness needs no separate determinant-guard proof
once its forced lengths and the incoming physical floor have been supplied. -/
theorem flagTest_of_lengths (u : FlagIndex) (h : History)
    (floor : terminalLogFloor u.1.val ≤ log (ZLattice.covolume (retained h u.1.val).M)) :
    let j := u.2.val
    let k := 155-u.1.val
    have he : 505-j+j = 505 := by dsimp [j]; omega
    let s := Eq.rec (motive := fun a _ ↦ ChainState (a+u.1.val) (CoordSpace a))
      (retained h u.1.val) he.symm
    ForcedLengths (d:=505-j) j k s →
    PositiveHit (forceOld j s).M (columnLift (forceOld j s).g (past h (105+u.1.val)))
      (radius u) → flagTest radius detFloor u h := by
  intro j k he s hl hp
  refine ⟨?_,hp⟩
  have hh := forced_log_covolume (d:=505-j) j k (by dsimp [j,k]; omega) s hl
  have hd : ZLattice.covolume s.M = ZLattice.covolume (retained h u.1.val).M :=
    cast_covol he (retained h u.1.val)
  rw [hd] at hh
  apply (exp_le_exp.mpr _).trans_eq (exp_log (ZLattice.covolume_pos (forceOld j s).M _))
  unfold detFloor
  dsimp only at *
  linarith

private theorem forced {n d m : ℕ} (Q : PhysicalSuffix m) (j l k : ℕ)
    (s : ChainState n (CoordSpace (d+j))) (hj : j < l) (hl : l ≤ m) (hm : m ≤ 155)
    (hlk : l ≤ k) (hk : k ≤ 155) (h : FollowsProfile Q.a j l s) : ForcedLengths j k s := by
  induction j generalizing l k with
  | zero => trivial
  | succ j ih =>
    exact ⟨h.1.trans (mul_le_mul_of_nonneg_left
      (physical_cap Q (by omega) hl hm hlk hk) (sqrt_nonneg _)),
      ih (l-1) (k-1) s.freeze (by omega) (by omega) (by omega) (by omega) h.2⟩

theorem cover (A : Sample) (t : ℕ) (ht : t ≤ 154)
    (hs : ‖(retained (history A) t).winner‖ ≤ planeRadius) :
    rawShort (designPrefix (by decide : 105 ≤ 512) A) 2896 ∨
      ∃ u, flagTest radius detFloor u (history A) := by
  obtain ⟨l,Q,_,h1,h2,w,hw,hn,hr⟩ | ⟨u,l,Q,_,_,hj,hl,hf,z,hz,hpos,hr⟩ :=
    physicalSuffixOrigin_of_short (history A) t ht hs
  · apply Or.inl (rawShort_of_initial A hw hn (hr.trans _))
    exact (mul_le_mul_of_nonneg_left (physical_cap Q h1 le_rfl h2 le_rfl h2)
      (sqrt_nonneg _)).trans (initial_radius l h2)
  · refine .inr ⟨u,flagTest_of_lengths u (history A)
      ((le_log_iff_exp_le (ZLattice.covolume_pos _ _)).2 (retained_floor_all _ _ (by omega)))
      (forced Q _ l _ _ hj le_rfl (by omega) hl (by omega) hf) ?_⟩
    exact ⟨z,hz,hpos,hr.trans (mul_le_mul_of_nonneg_left
      (physical_cap Q (by omega) (Nat.sub_le ..) (by omega) (Nat.sub_le_sub_right hl _)
        (by omega)) (sqrt_nonneg _))⟩

private theorem guarded_bound {n d : ℕ} (s : ChainState n (CoordSpace d)) {r l v : ℝ}
    (hr : r < 3329) (hv : 0 ≤ v)
    (hc : Real.exp l ≤ ZLattice.covolume s.M → candidateRatio s r ≤ v) :
    mass (fun c : Column ↦ Real.exp l ≤ ZLattice.covolume s.M ∧
      PositiveHit s.M (columnLift s.g c) r) ≤ v := by
  by_cases h : Real.exp l ≤ ZLattice.covolume s.M
  · simpa only [h, true_and] using (column_positive_bound s hr).trans (hc h)
  · simpa only [h, false_and, mass, filter_false, card_empty, Nat.cast_zero, zero_div] using hv

/-- With the determinant guard, the prefix ball hypothesis reduces to the
deterministic candidate count of the forced state. -/
private theorem flag_probability_of_count (u : FlagIndex) (hr : radius u < 3329)
    (hn : 0 ≤ charge u)
    (count : ∀ h : History,
      let j := u.2.val
      have hj : 505-j+j = 505 := by dsimp [j]; omega
      let s := forceOld (d := 505-j) j (hj ▸ retained h u.1.val)
      Real.exp (detFloor u) ≤ ZLattice.covolume s.M → candidateRatio s (radius u) ≤ charge u) :
    probability (fun A ↦ flagTest radius detFloor u (history A)) ≤ charge u := by
  let t : Fin 406 := ⟨u.1.val, by omega⟩
  let j := u.2.val
  have hj : 505-j+j = 505 := by dsimp [j]; omega
  let old (s : ChainState (505+t.val) (CoordSpace 505)) := forceOld (d := 505-j) j (hj ▸ s)
  let E := fun (s : ChainState (505+t.val) (CoordSpace 505)) (c : Column) ↦
    Real.exp (detFloor u) ≤ ZLattice.covolume (old s).M ∧
    PositiveHit (old s).M (columnLift (old s).g c) (radius u)
  apply adaptive_draw_bound t E
  intro h
  exact guarded_bound (old (retained h t.val)) hr hn (count h)

private theorem plane_pos : 0 < planeRadius := by unfold planeRadius areaCut; positivity

/-- The determinant guard alone suffices for the forced-state candidate estimate.
The state can be any physical state of the required dimension. -/
private theorem flag_candidate_bound (u : FlagIndex) {n : ℕ}
    (s : ChainState n (CoordSpace (505-u.2.val)))
    (h : exp (detFloor u) ≤ ZLattice.covolume s.M) :
    candidateRatio s (radius u) ≤ charge u := by
  let k := 155-u.1.val
  let j := u.2.val
  let p := 505-j
  let w := cap (k-j)
  let z := max 1 (w * sqrt (2*π/(p+1:ℝ)))
  have ht := plane_pos
  have hw : 0 < w := cap_pos _
  have hz : 0 < z := zero_lt_one.trans_le (le_max_left ..)
  have hc := candidateRatio_gaussian s (mul_pos ht hw).le (mul_pos ht hz)
  change candidateRatio s (radius u) ≤
    exp (π*(planeRadius*w)^2/(planeRadius*z)^2) / 2 * (planeRadius*z)^(p+1) *
      terminalTheta (planeRadius*z)^p / ZLattice.covolume s.M at hc
  have e : π*(planeRadius*w)^2/(planeRadius*z)^2 = π*w^2/z^2 := by field_simp
  rw [e] at hc
  have hθ : 0 ≤ terminalTheta (planeRadius*z) := (tsum_nonneg fun _ ↦ (exp_pos _).le).trans
    (integerGaussian_le_terminalTheta (mul_pos ht hz))
  apply hc.trans
  apply (div_le_div_of_nonneg_left (by positivity) (exp_pos _) h).trans_eq
  change _ = planeRadius^506 / 2 * exp (π*w^2/z^2-terminalLogFloor u.1.val +
    capSum k-capSum (k-j)) * z^(p+1) * terminalTheta (planeRadius*z)^p
  change _ / exp (terminalLogFloor u.1.val-capSum k+capSum (k-j)-j*log planeRadius) = _
  rw [exp_sub, exp_nat_mul, exp_log ht, mul_pow, exp_sub, exp_add, exp_sub, exp_add, exp_sub]
  have hj : p+1+j = 506 := by dsimp [p,j]; omega
  rw [← hj, pow_add planeRadius]
  field_simp
  ring

/-- Only the maximum physical test radius is needed to apply the uniform-column
law once the deterministic candidate estimate is in place. -/
theorem flag_probability (u : FlagIndex) :
    DualExit.probability (fun A ↦ flagTest radius detFloor u (history A)) ≤ charge u := by
  apply flag_probability_of_count u ((initial_radius _ (by omega)).trans_lt (by norm_num))
  · unfold charge
    dsimp only
    have ht := plane_pos
    have hz : 0 < max 1 (cap (155-u.1.val-u.2.val)*sqrt (2*π/((505-u.2.val:ℕ)+1:ℝ))) :=
      zero_lt_one.trans_le (le_max_left ..)
    have hθ := (tsum_nonneg fun _ ↦ (exp_pos _).le).trans
      (integerGaussian_le_terminalTheta (mul_pos ht hz))
    positivity
  · intro h
    exact flag_candidate_bound u _

end SigabaNeo.Wall1.ControlledPlane.ProvedProfile

#print axioms SigabaNeo.Wall1.ControlledPlane.ProvedProfile.cover
#print axioms SigabaNeo.Wall1.ControlledPlane.ProvedProfile.flag_probability
