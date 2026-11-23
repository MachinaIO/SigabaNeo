import SigabaNeo.Lib.Lattices.Research.Wall1.ControlledCertifiedBounds

/-! Hermite peeling of a suffix already lifted into one window. Lengths are
indexed by the number of remaining directions, with the terminal line at one. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane

open TerminalProjection TerminalProjection.Restart506 Real Finset BKZ DualExit

local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

/-- Logarithms of the successive length ratios to the terminal radius.
The sum of these logs is the log of the normalized suffix determinant. -/
structure SuffixProfile (m : ℕ) where
  a : ℕ → ℝ
  terminal : a 1 ≤ 0
  hermite (l : ℕ) : 2 ≤ l → l ≤ m →
    a l ≤ log (flagGamma l)/2 + (∑ r ∈ Icc 1 l, a r)/(l:ℝ)

private theorem gamma_pos (l : ℕ) : 0 < flagGamma l := by
  unfold flagGamma
  split <;> first | positivity | split <;> first | positivity | exact auditedGamma_pos _

/-- A physical suffix whose determinant is the product of its successive lengths
gives a profile directly from the Hermite inequalities in squared-length units. -/
def SuffixProfile.of_physical (m : ℕ) (length : ℕ → ℝ) (pos : ∀ i, 1 ≤ i → i ≤ m → 0 < length i)
    (hm : 1 ≤ m) (base : length 1 ≤ planeRadius)
    (hermite : ∀ l, 2 ≤ l → l ≤ m → length l ^ 2 ≤
      flagGamma l * (∏ r ∈ Icc 1 l, length r) ^ (2/(l:ℝ))) : SuffixProfile m where
  a i := log (length i) - log planeRadius
  terminal := sub_nonpos.mpr (log_le_log (pos 1 le_rfl hm) base)
  hermite l hl top := by
    have hl' : (0:ℝ) < l := by exact_mod_cast (show 0 < l by omega)
    have hl0 := pos l (by omega) top
    have hp := fun i (h : i ∈ Icc 1 l) ↦ pos i (mem_Icc.mp h).1 ((mem_Icc.mp h).2.trans top)
    have prodpos := prod_pos hp
    have H := log_le_log (sq_pos_of_pos hl0) (hermite l hl top)
    rw [log_pow,log_mul (gamma_pos _).ne' (rpow_pos_of_pos prodpos _).ne',log_rpow prodpos,
      log_prod (fun i h ↦ (hp i h).ne')] at H
    simp only [sum_sub_distrib,sum_const,Nat.card_Icc,nsmul_eq_mul,Nat.add_one_sub_one]
    push_cast at H
    field_simp [hl'.ne'] at H ⊢
    nlinarith

private theorem cap_mono : Monotone flagCap := monotone_nat_of_le_succ fun _ ↦ le_max_left ..

private def penalty (l : ℕ) := ∑ r ∈ Icc 2 l, log (flagGamma r)/(2*((r:ℝ)-1))

/-- The normalized geometric mean pays one factor γ_l^(1/(2(l−1))) per peel. -/
private theorem mean_cap {m : ℕ} (P : SuffixProfile m) (l : ℕ) (hl : 1 ≤ l) (hm : l ≤ m) :
    (∑ r ∈ Icc 1 l, P.a r)/(l:ℝ) ≤ penalty l := by
  induction l with
  | zero => omega
  | succ n ih =>
    by_cases h : n = 0
    · subst n; simpa [penalty] using P.terminal
    have hn : 1 ≤ n := by omega
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    have hn1 : (0:ℝ) < n+1 := by positivity
    have old := ih hn (by omega)
    have H := P.hermite (n+1) (by omega) hm
    rw [sum_Icc_succ_top (by omega),Nat.cast_succ] at H ⊢
    rw [show penalty (n+1) = penalty n + log (flagGamma (n+1))/(2*(n:ℝ)) by
      unfold penalty; rw [sum_Icc_succ_top (by omega),Nat.cast_succ]; ring_nf]
    have step : ((∑ r ∈ Icc 1 n, P.a r)+P.a (n+1))/((n:ℝ)+1) ≤
        (∑ r ∈ Icc 1 n, P.a r)/(n:ℝ) + log (flagGamma (n+1))/(2*(n:ℝ)) := by
      field_simp [hn'.ne',hn1.ne'] at H ⊢
      nlinarith
    exact step.trans (add_le_add_left old _)

theorem SuffixProfile.cap {m : ℕ} (P : SuffixProfile m) {l : ℕ} (hl : 1 ≤ l) (hm : l ≤ m) :
    exp (P.a l) ≤ flagCap l := by
  by_cases h : l = 1
  · subst l
    exact (exp_le_one_iff.mpr P.terminal).trans (cap_mono (Nat.zero_le 1) : flagCap 0 ≤ flagCap 1)
  have H := (P.hermite l (by omega) hm).trans (add_le_add_right (mean_cap P l hl hm) _)
  have prod : exp (penalty l) = ∏ i ∈ Icc 2 l, flagGamma i ^ (1/(2*((i:ℝ)-1))) := by
    rw [penalty,exp_sum]
    apply prod_congr rfl; intro i _
    rw [rpow_def_of_pos (gamma_pos _)]
    congr 1; ring
  have sq : exp (log (flagGamma l)/2) = √(flagGamma l) := by
    rw [sqrt_eq_rpow,rpow_def_of_pos (gamma_pos _)]
    congr 1; ring
  have hh := exp_le_exp.mpr H
  rw [exp_add,sq,prod] at hh
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
  exact hh.trans (le_max_right ..)

/-- The forced old-only winners have the indicated physical suffix lengths. -/
def FollowsProfile {n d : ℕ} (a : ℕ → ℝ) :
    (j l : ℕ) → ChainState n (CoordSpace (d+j)) → Prop
  | 0, _, _ => True
  | j+1, l, s => ‖s.winner‖ ≤ planeRadius * exp (a l) ∧ FollowsProfile a j (l-1) s.freeze

private theorem forced_caps {n d m : ℕ} (P : SuffixProfile m) (j l k : ℕ)
    (s : ChainState n (CoordSpace (d+j))) (hj : j < l) (hl : l ≤ m) (hk : l ≤ k)
    (hs : FollowsProfile P.a j l s) : ForcedLengths j k s := by
  induction j generalizing l k with
  | zero => trivial
  | succ j ih =>
    exact ⟨hs.1.trans (mul_le_mul_of_nonneg_left ((P.cap (by omega) hl).trans (cap_mono hk))
      (sqrt_nonneg _)), ih (l-1) (k-1) s.freeze (by omega) (by omega) (by omega) hs.2⟩

/-- The last used coordinate has an actual suffix of length l, possibly shorter
than the horizon cap. The first direction that uses it survives j forced freezes. -/
def LiftedSuffix (h : History) (u : FlagIndex) : Prop :=
  let j := u.2.val
  have he : 505-j+j = 505 := by dsimp [j]; omega
  let s := Eq.rec (motive := fun a _ ↦ ChainState (a+u.1.val) (CoordSpace a))
    (retained h u.1.val) he.symm
  ∃ (l : ℕ) (P : SuffixProfile l), j < l ∧ l ≤ 155-u.1.val ∧ FollowsProfile P.a j l s ∧
    PositiveHit (forceOld j s).M (columnLift (forceOld j s).g (past h (105+u.1.val)))
      (planeRadius * exp (P.a (l-j)))

theorem flag_of_lifted_suffix {h : History} {u : FlagIndex} (lift : LiftedSuffix h u) :
    flagTest flagRadius flagFloor u h := by
  obtain ⟨l,P,hj,hl,hs,z,hz,hp,hr⟩ := lift
  refine flagTest_of_lengths u h ((le_log_iff_exp_le (ZLattice.covolume_pos _ _)).2
    (retained_floor_all _ _ (by omega))) (forced_caps P _ l _ _ hj le_rfl hl hs) ?_
  exact ⟨z,hz,hp,hr.trans (mul_le_mul_of_nonneg_left ((P.cap (by omega) (Nat.sub_le ..)).trans
    (cap_mono (Nat.sub_le_sub_right hl _))) (sqrt_nonneg _))⟩

/-- The geometric construction still needed for inherited draws. An entirely old
suffix supplies a nonzero vector in the initial lattice. The other branch supplies
the first nonzero height in the window of the last used coordinate. -/
def InheritedSuffixLift : Prop :=
  ∀ (A : Sample) (i : ℕ), 31 ≤ i → i < 154 →
    ‖(retained (history A) (i+1)).winner‖ ≤ planeRadius → horizontalWinner (history A) i →
    ShortProjection (retained (history A) i).M (retained (history A) i).winner planeRadius →
    (∃ (l : ℕ) (P : SuffixProfile l), 1 ≤ l ∧ l ≤ 155 ∧
      ∃ w ∈ (retained (history A) 0).M, w ≠ 0 ∧ ‖w‖ ≤ planeRadius * exp (P.a l)) ∨
      ∃ u, LiftedSuffix (history A) u

theorem coverage_of_inherited_suffix_lift (lift : InheritedSuffixLift) : LastCoordinateCoverage := by
  apply coverage_iff_inherited.mpr
  intro A i h1 h2 hs hh ho
  obtain ⟨l,P,hl,hm,w,hw,hn,hr⟩ | ⟨u,hu⟩ := lift A i h1 h2 hs hh ho
  · exact .inl (rawShort_of_initial_flag l hm A hw hn (hr.trans (mul_le_mul_of_nonneg_left
      (P.cap hl le_rfl) (sqrt_nonneg _))))
  · exact .inr ⟨u,flag_of_lifted_suffix hu⟩

theorem terminal_bound_of_inherited_suffix_lift (lift : InheritedSuffixLift) :
    probability terminalHit < probability residual₁ + probability residual₂ + 6.515/(10:ℝ)^12 :=
  terminal_bound_of_coverage_floor (coverage_of_inherited_suffix_lift lift)
    HermiteWitness506.Sphere.laterDeterminantFloor

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.SuffixProfile.cap
#print axioms SigabaNeo.Wall1.ControlledPlane.flag_of_lifted_suffix
#print axioms SigabaNeo.Wall1.ControlledPlane.coverage_of_inherited_suffix_lift
#print axioms SigabaNeo.Wall1.ControlledPlane.terminal_bound_of_inherited_suffix_lift
