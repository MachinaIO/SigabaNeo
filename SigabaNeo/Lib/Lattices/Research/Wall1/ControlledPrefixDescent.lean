import SigabaNeo.Lib.Lattices.Research.Wall1.ControlledConcreteBounds

/-! Backward descent along horizontal winners in the initial segment. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane
open TerminalProjection TerminalProjection.Restart506 TerminalProjection.ChainState
open DualExit Real
set_option maxRecDepth 6000
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

private theorem descent (h : History) (i : ℕ) {r : ℝ}
    (hs : ‖(retained h (i+1)).winner‖ ≤ r) :
    ‖(retained h i).winner‖ ≤ 1.155*r ∨
      PositiveHit (retained h i).M (columnLift (retained h i).g (past h (105+i))) (1.155*r) := by
  let s := retained h i
  let c := past h (105+i)
  let w := (s.append c).winner
  have sh := (retained h (i+1)).shortest
  have hx : ∃ y ∈ (incoming s c).freeze.M, y ≠ 0 ∧ ‖y‖ ≤ r := ⟨_,sh.1,sh.2.1,hs⟩
  rw [freeze_test,incoming,reframe_winner,reframe_shortProjection,shortProjection_iff] at hx
  obtain ⟨y,hy,hn,hr⟩ := hx
  obtain ⟨_,_,_,_,hw,_⟩ := rounded_witness (s.append c).shortest hy hn hr
  have h3 : 2 ≤ 1.155 * √3 := by linarith [le_sqrt_of_sq_le (by norm_num : (1.732:ℝ)^2 ≤ 3)]
  have hlen : ‖w‖ ≤ 1.155*r := hw.trans ((div_le_iff₀ (by positivity : 0 < √(3:ℝ))).mpr
    (by nlinarith [mul_nonneg (sub_nonneg.mpr h3) (hn.le.trans hr)]))
  have hm := (s.append c).shortest.1
  by_cases ho : w.snd = 0
  · left
    have he : horizontalInclusion w.fst = w :=
      (WithLp.equiv 2 _).injective (Prod.ext rfl ho.symm)
    have hm' := (mem_append_at_height _ _ w 0 (by simpa using ho)).1 hm
    exact (s.shortest.2.2 w.fst ((Submodule.Quotient.mk_eq_zero _).mp (by simpa using hm'))
      (fun e ↦ (s.append c).shortest.2.1 (he.symm.trans ((congrArg _ e).trans (map_zero _))))).trans
        (((WithLp.norm_toLp_fst 2 _ _ w.fst).symm.trans (congrArg norm he)).le.trans hlen)
  · right
    rcases lt_or_gt_of_ne ho with hn | hp
    · exact ⟨-w,(s.append c).M.neg_mem hm,neg_pos.mpr hn,by simpa using hlen⟩
    · exact ⟨w,hm,hp,hlen⟩

/-- A short retained winner descends through horizontal draws until the first positive hit
or the initial lattice, whenever the stated radii and incoming floors cover the descent. -/
theorem coverage_of_descent_caps (A : Sample) (t : ℕ) (ht : t ≤ 154)
    (cap : ∀ i ≤ t, (1.155:ℝ)^(t-i) ≤ flagCap (155-i))
    (floor : ∀ i < t, exp (terminalLogFloor i) ≤ ZLattice.covolume (retained (history A) i).M)
    (hs : ‖(retained (history A) t).winner‖ ≤ planeRadius) :
    rawShort (designPrefix (by decide : 105 ≤ 512) A) 2885 ∨
      ∃ u, flagTest flagRadius flagFloor u (history A) := by
  let h := history A
  have hr : 0 ≤ planeRadius := sqrt_nonneg _
  suffices go : ∀ i ≤ t, ‖(retained h i).winner‖ ≤ planeRadius*1.155^(t-i) →
      rawShort (designPrefix (by decide : 105 ≤ 512) A) 2885 ∨
        ∃ u, flagTest flagRadius flagFloor u h by
    exact go t le_rfl (by simpa using hs)
  intro i
  induction i with
  | zero =>
    intro _ hw
    exact .inl (rawShort_of_initial_flag 155 le_rfl A (retained h 0).shortest.1
      (retained h 0).shortest.2.1 (hw.trans (mul_le_mul_of_nonneg_left (cap 0 (by omega)) hr)))
  | succ i ih =>
    intro hi hw
    have eq : 1.155*(planeRadius*1.155^(t-(i+1))) = planeRadius*1.155^(t-i) := by
      rw [show t-i = (t-(i+1))+1 by omega,pow_succ]; ring
    rcases descent h i hw with old | fresh
    · exact ih (by omega) (eq ▸ old)
    · right
      let u : FlagIndex := ⟨⟨i,by omega⟩,⟨0,by omega⟩⟩
      refine ⟨u,flagTest_of_lengths u h ?_ trivial ?_⟩
      · exact (le_log_iff_exp_le (ZLattice.covolume_pos _ _)).2
          (floor i (by omega))
      · obtain ⟨v,hv,hp,hn⟩ := fresh
        exact ⟨v,hv,hp,hn.trans (eq.le.trans (mul_le_mul_of_nonneg_left
          (cap i (by omega)) hr))⟩

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.coverage_of_descent_caps
