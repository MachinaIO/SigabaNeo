import SigabaNeo.Lib.Lattices.Research.Wall1.ControlledSuffixWindow
import SigabaNeo.Lib.Lattices.Research.Wall1.ControlledSuffixMordell

/-! Backward induction over the concrete chain with an increasing number of designated freezes.
When the entire suffix is horizontal, removing its last column preserves the terminal length.
Otherwise the first nonzero height gives the required forced-window test. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane

open TerminalProjection TerminalProjection.Restart506 TerminalProjection.ChainState DualExit Real
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

private def EndsShort {n : ℕ} : (m d : ℕ) → ChainState n (CoordSpace d) → Prop
  | _, 0, _ => False
  | 0, _+1, s => ‖s.winner‖ ≤ planeRadius
  | m+1, _+1, s => EndsShort m _ s.freeze

private def BoundedRun {n : ℕ} (a : ℕ → ℝ) : (m l d : ℕ) → ChainState n (CoordSpace d) → Prop
  | _, _, 0, _ => False
  | 0, l, _+1, s => ‖s.winner‖ ≤ planeRadius * exp (a l)
  | m+1, l, _+1, s => ‖s.winner‖ ≤ planeRadius * exp (a l) ∧ BoundedRun a m (l-1) _ s.freeze

/-- The designated winner of the appended window first uses the new axis after j old freezes.
The sign of that winner is immaterial for the positive-height test. -/
def FirstUsedHeight {n : ℕ} (c : Column) : (j d : ℕ) → ChainState n (CoordSpace d) → Prop
  | 0, _, s => (s.append c).winner.snd ≠ 0
  | _+1, 0, _ => False
  | j+1, _+1, s => (s.append c).winner.snd = 0 ∧ FirstUsedHeight c j _ s.freeze

private def HeightAt {n : ℕ} (a : ℕ → ℝ) (c : Column) :
    (j l d : ℕ) → ChainState n (CoordSpace d) → Prop
  | 0, l, _, s => PositiveHit s.M (columnLift s.g c) (planeRadius * exp (a l))
  | _+1, _, 0, _ => False
  | j+1, l, _+1, s => ‖s.winner‖ ≤ planeRadius * exp (a l) ∧ HeightAt a c j (l-1) _ s.freeze

private theorem terminal_length {n d : ℕ} (m : ℕ) (s : ChainState n (CoordSpace (d+1+m)))
    (h : EndsShort m _ s) : suffixLength m s 1 ≤ planeRadius := by
  induction m with
  | zero => exact h
  | succ m ih =>
    rw [suffixLength,ite_eq_right (by omega)]
    exact ih s.freeze h

private theorem bounded_physical {n d : ℕ} (m : ℕ) (s : ChainState n (CoordSpace (d+1+m)))
    (a : ℕ → ℝ) (h : ∀ r, 1 ≤ r → r ≤ m+1 → suffixLength m s r ≤ planeRadius * exp (a r)) :
    BoundedRun a m (m+1) _ s := by
  induction m with
  | zero => exact h 1 le_rfl le_rfl
  | succ m ih =>
    refine ⟨(suffixLength_head (m+1) s) ▸ h (m+2) (by omega) le_rfl,ih s.freeze ?_⟩
    intro r hr hu
    simpa only [suffixLength,ite_eq_right (show r ≠ m+2 by omega)] using h r hr (by omega)

/-- An actual single-window run ending in a short line. Its lengths are defined by the
designated winners of the stored state. -/
structure PhysicalSuffix (l : ℕ) where
  n : ℕ
  d : ℕ
  steps : ℕ
  rank_eq : steps+1 = l
  state : ChainState n (CoordSpace (d+1+steps))
  short : suffixLength steps state 1 ≤ planeRadius

def PhysicalSuffix.a {l : ℕ} (Q : PhysicalSuffix l) (r : ℕ) : ℝ :=
  log (suffixLength Q.steps Q.state r) - log planeRadius

theorem PhysicalSuffix.profile {l : ℕ} (Q : PhysicalSuffix l) (caps : ExceptionalFamilyBounds) :
    ∃ P : SuffixProfile l, P.a = Q.a := by
  rcases Q with ⟨n,d,m,rfl,s,hs⟩
  exact ⟨physicalSuffixProfile m s hs (fun r lo _ ↦ familyHermite_of_exceptional caps r lo),rfl⟩

private theorem physical_run {n d : ℕ} (m : ℕ)
    (s : ChainState n (CoordSpace d)) (hd : m < d) (hs : EndsShort m _ s) :
    ∃ Q : PhysicalSuffix (m+1), HEq Q.state s ∧ BoundedRun Q.a m (m+1) _ s := by
  obtain ⟨b,he⟩ := Nat.exists_eq_add_of_le (show m+1 ≤ d by omega)
  have he' : d = b+1+m := by omega
  clear he
  subst d
  let Q : PhysicalSuffix (m+1) := ⟨n,b,m,rfl,s,terminal_length m s hs⟩
  refine ⟨Q,HEq.rfl,bounded_physical m s Q.a ?_⟩
  intro r _ _
  change _ ≤ planeRadius * exp (log (suffixLength m s r) - log planeRadius)
  have hR : 0 < planeRadius := by unfold planeRadius areaCut; positivity
  rw [exp_sub,exp_log (suffixLength_pos ..),exp_log hR]
  exact le_of_eq (by field_simp)

/-- Scan the realized window. Each horizontal freeze preserves the realized old window,
including the ordered axes, so the recursive comparison uses the actual designated winner. -/
private theorem height_or_old {n : ℕ} (a : ℕ → ℝ) (c : Column) (m l d : ℕ) (hd : m < d)
    (s : ChainState n (CoordSpace d)) (t : ChainState (n+1) (CoordSpace (d+1)))
    (W : WindowRealization s c t) (hs : EndsShort m _ t) (hb : BoundedRun a m l _ t) :
    EndsShort m _ s ∨ ∃ j ≤ m, FirstUsedHeight c j _ s ∧ HeightAt a c j l _ s := by
  cases d with
  | zero => omega
  | succ d =>
    have hb₀ : ‖t.winner‖ ≤ planeRadius * exp (a l) := by cases m <;> first | exact hb | exact hb.1
    by_cases ho : (s.append c).winner.snd = 0
    · have hl := W.horizontal_norm ho
      cases m with
      | zero => left; exact (le_of_eq hl.symm).trans hs
      | succ m =>
        obtain ⟨W'⟩ := W.freeze_horizontal ho
        rcases height_or_old a c m (l-1) d (by omega) s.freeze t.freeze W' hs hb.2 with h | ⟨j,hj,hfirst,h⟩
        · exact .inl h
        · exact .inr ⟨j+1,by omega,⟨ho,hfirst⟩,hl ▸ hb₀,h⟩
    · right
      refine ⟨0,Nat.zero_le _,ho,?_⟩
      rw [W.winner,W.e.norm_map] at hb₀
      rcases lt_or_gt_of_ne ho with h | h
      · exact ⟨-(s.append c).winner,(s.append c).M.neg_mem (s.append c).shortest.1,
          neg_pos.mpr h,by simpa using hb₀⟩
      · exact ⟨(s.append c).winner,(s.append c).shortest.1,h,hb₀⟩
termination_by m

private theorem height_force {n d : ℕ} (a : ℕ → ℝ) (c : Column) (j l : ℕ)
    (s : ChainState n (CoordSpace (d+j))) (h : HeightAt a c j l _ s) :
    FollowsProfile a j l s ∧
      PositiveHit (forceOld j s).M (columnLift (forceOld j s).g c) (planeRadius * exp (a (l-j))) := by
  induction j generalizing l with
  | zero => exact ⟨trivial,h⟩
  | succ j ih =>
    obtain ⟨hf,hp⟩ := ih (l-1) s.freeze h.2
    exact ⟨⟨h.1,hf⟩,by simpa only [forceOld,show l-(j+1) = l-1-j by omega] using hp⟩

private theorem height_cast {D b : ℕ} (a : ℕ → ℝ) (c : Column) (j l i : ℕ)
    (s : ChainState (D+i) (CoordSpace D)) (e : b+j = D) (h : HeightAt a c j l _ s) :
    let s' := Eq.rec (motive := fun x _ ↦ ChainState (x+i) (CoordSpace x)) s e.symm
    FollowsProfile a j l s' ∧ PositiveHit (forceOld j s').M (columnLift (forceOld j s').g c)
      (planeRadius * exp (a (l-j))) := by
  subst D
  exact height_force a c j l s h

/-- Origin in the initial state or in the window of the last used coordinate,
with a physical run and its terminal length bound in both alternatives. -/
def PhysicalSuffixOrigin (h : History) : Prop :=
  (∃ (l : ℕ) (Q : PhysicalSuffix l), HEq Q.state (retained h 0) ∧ 1 ≤ l ∧ l ≤ 155 ∧
    ∃ w ∈ (retained h 0).M, w ≠ 0 ∧ ‖w‖ ≤ planeRadius * exp (Q.a l)) ∨
    ∃ u : FlagIndex,
      let j := u.2.val
      have he : 505-j+j = 505 := by dsimp [j]; omega
      let s := Eq.rec (motive := fun x _ ↦ ChainState (x+u.1.val) (CoordSpace x))
        (retained h u.1.val) he.symm
      ∃ (l : ℕ) (Q : PhysicalSuffix l), HEq Q.state (window h u.1.val) ∧
        FirstUsedHeight (past h (105+u.1.val)) j _ (retained h u.1.val) ∧ j < l ∧ l ≤ 155-u.1.val ∧ FollowsProfile Q.a j l s ∧
        PositiveHit (forceOld j s).M (columnLift (forceOld j s).g (past h (105+u.1.val)))
          (planeRadius * exp (Q.a (l-j)))

private theorem trace_origin (h : History) (i m : ℕ)
    (budget : i+m ≤ 154) (hs : EndsShort m _ (retained h i)) : PhysicalSuffixOrigin h := by
  induction i generalizing m with
  | zero =>
    obtain ⟨P,hstate,hp⟩ := physical_run m (retained h 0) (by omega) hs
    refine .inl ⟨m+1,P,hstate,by omega,by omega,_,(retained h 0).shortest.1,(retained h 0).shortest.2.1,?_⟩
    cases m <;> first | exact hp | exact hp.1
  | succ i ih =>
    let s := retained h i
    let c := past h (105+i)
    let t := incoming s c
    have ht : EndsShort (m+1) _ t := hs
    obtain ⟨P,hstate,hp⟩ := physical_run (m+1) t (by omega) ht
    rcases height_or_old P.a c (m+1) (m+2) 505 (by omega) s t (incomingRealization s c) ht hp with
      old | ⟨j,hj,hfirst,hgt⟩
    · exact ih (m+1) (by omega) old
    · let u : FlagIndex := ⟨⟨i,by omega⟩,⟨j,by change j < 155-i; omega⟩⟩
      have cert := height_cast (b:=505-j) P.a c j (m+2) i s (by omega) hgt
      exact .inr ⟨u,m+2,P,hstate,hfirst,by change j < m+2; omega,by change m+2 ≤ 155-i; omega,cert⟩

/-- Unconditional construction for all short retained winners through draw 154. -/
theorem physicalSuffixOrigin_of_short (h : History) (i : ℕ) (hi : i ≤ 154)
    (hs : ‖(retained h i).winner‖ ≤ planeRadius) : PhysicalSuffixOrigin h :=
  trace_origin h i 0 (by omega) hs

theorem inheritedSuffixLift_of_familyBounds (caps : ExceptionalFamilyBounds) : InheritedSuffixLift := by
  intro A i _ hi hs _ _
  obtain ⟨l,Q,_,h1,h2,w,hw,hn,hr⟩ | ⟨u,l,Q,_,_,hj,hl,hf,hp⟩ :=
    physicalSuffixOrigin_of_short (history A) (i+1) (by omega) hs
  · obtain ⟨P,he⟩ := Q.profile caps
    exact .inl ⟨l,P,h1,h2,w,hw,hn,he ▸ hr⟩
  · obtain ⟨P,he⟩ := Q.profile caps
    exact .inr ⟨u,l,P,hj,hl,he ▸ hf,he ▸ hp⟩

theorem terminal_bound_of_familyBounds (caps : ExceptionalFamilyBounds) :
    probability terminalHit < probability residual₁ + probability residual₂ + 6.515/(10:ℝ)^12 :=
  terminal_bound_of_inherited_suffix_lift (inheritedSuffixLift_of_familyBounds caps)

theorem inheritedSuffixLift_of_intrinsic (h5 : IntrinsicHermite 5 (flagGamma 5))
    (h6 : IntrinsicHermite 6 (flagGamma 6)) (h7 : IntrinsicHermite 7 (flagGamma 7))
    (h24 : IntrinsicHermite 24 4) : InheritedSuffixLift :=
  inheritedSuffixLift_of_familyBounds (exceptional_of_intrinsic h5 h6 h7 h24)

theorem terminal_bound_of_intrinsic (h5 : IntrinsicHermite 5 (flagGamma 5))
    (h6 : IntrinsicHermite 6 (flagGamma 6)) (h7 : IntrinsicHermite 7 (flagGamma 7))
    (h24 : IntrinsicHermite 24 4) :
    probability terminalHit < probability residual₁ + probability residual₂ + 6.515/(10:ℝ)^12 :=
  terminal_bound_of_inherited_suffix_lift (inheritedSuffixLift_of_intrinsic h5 h6 h7 h24)

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.physicalSuffixOrigin_of_short
#print axioms SigabaNeo.Wall1.ControlledPlane.inheritedSuffixLift_of_familyBounds
#print axioms SigabaNeo.Wall1.ControlledPlane.terminal_bound_of_familyBounds
#print axioms SigabaNeo.Wall1.ControlledPlane.inheritedSuffixLift_of_intrinsic
#print axioms SigabaNeo.Wall1.ControlledPlane.terminal_bound_of_intrinsic
