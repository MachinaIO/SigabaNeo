import SigabaNeo.Lib.Lattices.Research.Wall1.ControlledSuffixProfile

/-! Intrinsic Hermite bounds for the family obtained by lifting successive designated winners
through their actual quotient maps. The rank refers to the lifted family in the window. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane

open Submodule Module Real Finset TerminalProjection TerminalProjection.ChainState
open scoped RealInnerProductSpace

/-- Squared-length Hermite bound for independent families inside an ambient lattice. -/
def FamilyHermite (k : ℕ) (g : ℝ) : Prop :=
  ∀ {d : ℕ} (L : Submodule ℤ (CoordSpace d)) [DiscreteTopology L] {v : CoordSpace d},
    DecoupledDecoder.IsShortest L v → ∀ b : RankinFamily L k,
      ‖v‖^2 ≤ g * (sqrt (Matrix.gram ℝ b.vec).det) ^ (2 / (k : ℝ))

/-- Standard covolume formulation in the intrinsic rank-k Euclidean space. -/
def IntrinsicHermite (k : ℕ) (g : ℝ) : Prop :=
  ∀ (L : Submodule ℤ (CoordSpace k)) [DiscreteTopology L] [IsZLattice ℝ L],
    ∃ w : L, w ≠ 0 ∧ ‖w.val‖^2 ≤ g * ZLattice.covolume L ^ (2/(k:ℝ))

theorem familyHermite_of_intrinsic {k : ℕ} {g : ℝ} (cap : IntrinsicHermite k g) :
    FamilyHermite k g := by
  intro d L _ v hv f
  let B := Basis.span f.ind
  let e := ChainState.coord ((finrank_eq_card_basis B).trans (Fintype.card_fin k))
  let C := B.map e.toLinearEquiv
  let K := span ℤ (Set.range C)
  obtain ⟨w,hn,hw⟩ := cap K
  let T := (span ℝ (Set.range f.vec)).subtype.comp e.symm.toLinearEquiv.toLinearMap
  have hC (i : Fin k) : T (C i) = f.vec i := by simp [T,C,B]
  have hm : K.map (T.restrictScalars ℤ) ≤ L := by
    rw [Submodule.map_span]
    apply span_le.mpr
    rintro _ ⟨_, ⟨i,rfl⟩, rfl⟩
    exact hC i ▸ f.mem i
  have hnorm (x : CoordSpace k) : ‖T x‖ = ‖x‖ := e.symm.norm_map x
  have hmin := hv.2.2 (T w) (hm ⟨_,w.property,rfl⟩) (by
    intro hz
    apply hn
    apply Subtype.ext
    exact norm_eq_zero.mp ((hnorm w).symm.trans (hz ▸ norm_zero)))
  have hgram : Matrix.gram ℝ C = Matrix.gram ℝ f.vec := by
    ext i j
    simp [Matrix.gram_apply,C,B]
  have hdet := covolume_span_sq_eq_gram C
  rw [hgram] at hdet
  have he : sqrt (Matrix.gram ℝ f.vec).det = ZLattice.covolume K := by
    rw [← hdet,sqrt_sq (ZLattice.covolume_pos K _).le]
  rw [he]
  rw [hnorm] at hmin
  exact (pow_le_pow_left₀ (norm_nonneg _) hmin 2).trans hw

theorem familyHermite_blichfeldt (k : ℕ) [NeZero k] :
    FamilyHermite k (BKZ.blichfeldtConstant k) :=
  familyHermite_of_intrinsic (fun L _ _ ↦ BKZ.hermite_blichfeldt L)

theorem familyHermite_two : FamilyHermite 2 (flagGamma 2) := by
  intro d L _ v hv f
  obtain ⟨w,hw,hn,hl⟩ := short_in_span f.vec f.ind
  have incl := span_le.mpr (Set.range_subset_iff.mpr f.mem)
  have hm := pow_le_pow_left₀ (norm_nonneg _) (hv.2.2 w (incl hw) hn) 2
  have h : flagGamma 2 = 2 / √3 := by
    norm_num [flagGamma,auditedGamma,hermitePower]
    rw [div_eq_mul_inv,← rpow_def_of_pos (by norm_num : (0:ℝ)<4/3),← one_div,← sqrt_eq_rpow,
      sqrt_div (by norm_num)]
    norm_num
  rw [h]
  norm_num only [Nat.cast_ofNat,div_self (by norm_num : (2:ℝ) ≠ 0),rpow_one]
  rw [div_mul_eq_mul_div,le_div_iff₀ (by positivity)]
  linarith [mul_le_mul_of_nonneg_left hm (sqrt_nonneg 3)]

theorem familyHermite_three : FamilyHermite 3 (flagGamma 3) := by
  intro d L _ v hv f
  have h := ternary_shortest L hv f.vec f.mem f.ind
  have hp := (Matrix.posDef_gram_of_linearIndependent f.ind).det_pos
  have hg : flagGamma 3 = (2:ℝ) ^ (1/3:ℝ) := by
    norm_num [flagGamma,auditedGamma,hermitePower,rpow_def_of_pos]
    ring_nf
  rw [hg]
  apply (pow_le_pow_iff_left₀ (sq_nonneg _) (by positivity) (by decide : 3 ≠ 0)).mp
  rw [← pow_mul,mul_pow,← rpow_mul_natCast (by norm_num),← rpow_mul_natCast (sqrt_nonneg _)]
  norm_num [sq_sqrt hp.le] at *
  exact h

/-- The squared determinant of a lifted family gains exactly the squared winner length. -/
theorem lift_freeze_family {n d k : ℕ} (s : ChainState n (CoordSpace (d+1)))
    (b : RankinFamily s.freeze.M k) :
    ∃ f : RankinFamily s.M (k+1), f.vec 0 = s.winner ∧
      (Matrix.gram ℝ f.vec).det = ‖s.winner‖^2 * (Matrix.gram ℝ b.vec).det := by
  let S := (ℝ ∙ s.winner)ᗮ
  have hr : finrank ℝ S = d := by
    have hh := (ℝ ∙ s.winner).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton s.shortest.2.1,finrank_euclideanSpace_fin] at hh
    change 1 + finrank ℝ S = d+1 at hh
    omega
  let e := ChainState.coord hr
  have lift (j : Fin k) : ∃ w ∈ s.M, S.orthogonalProjectionOnto w = e.symm (b.vec j) := b.mem j
  choose w hw he using lift
  let f := Fin.cons (α := fun _ ↦ CoordSpace (d+1)) s.winner w
  have eq : (Matrix.gram ℝ f).det = ‖s.winner‖^2 * (Matrix.gram ℝ b.vec).det := by
    rw [det_gram_project_tail]
    simp only [f, Fin.cons_zero, Fin.cons_succ]
    congr 2
    ext j l
    exact (congrArg₂ (fun p q : S ↦ inner ℝ p.val q.val) (he j) (he l)).trans
      (e.symm.inner_map_map _ _)
  exact ⟨⟨f,Fin.forall_fin_succ.mpr ⟨s.shortest.1, hw⟩,
    Matrix.det_gram_ne_zero_iff_linearIndependent.mp (eq ▸ (mul_pos
      (sq_pos_of_pos (norm_pos_iff.mpr s.shortest.2.1))
      (Matrix.posDef_gram_of_linearIndependent b.ind).det_pos).ne')⟩, rfl, eq⟩

/-- Physical lengths indexed backwards from the final surviving winner. -/
def suffixLength {n d : ℕ} : (m : ℕ) → ChainState n (CoordSpace (d+1+m)) → ℕ → ℝ
  | 0, s, _ => ‖s.winner‖
  | m+1, s, l => if l = m+2 then ‖s.winner‖ else suffixLength m s.freeze l

theorem suffixLength_pos {n d : ℕ} (m : ℕ) (s : ChainState n (CoordSpace (d+1+m))) (l : ℕ) :
    0 < suffixLength m s l := by
  induction m with
  | zero => exact norm_pos_iff.mpr s.shortest.2.1
  | succ m ih =>
    simp only [suffixLength]
    split
    · exact norm_pos_iff.mpr s.shortest.2.1
    · exact ih s.freeze

theorem suffixLength_head {n d : ℕ} (m : ℕ) (s : ChainState n (CoordSpace (d+1+m))) :
    suffixLength m s (m+1) = ‖s.winner‖ := by
  cases m <;> simp [suffixLength]

private theorem suffix_prod_step {n d : ℕ} (m : ℕ) (s : ChainState n (CoordSpace (d+1+(m+1)))) :
    ∏ l ∈ Icc 1 (m+2), suffixLength (m+1) s l =
      (∏ l ∈ Icc 1 (m+1), suffixLength m s.freeze l) * ‖s.winner‖ := by
  rw [prod_Icc_succ_top (by omega),suffixLength_head]
  congr 1
  apply prod_congr rfl
  intro l hl
  have := (mem_Icc.mp hl).2
  simp [suffixLength,show l ≠ m+2 by omega]

/-- Lifting the terminal line through m freezes produces an independent family in the original
window, with the designated first vector and covolume the product of the physical lengths. -/
theorem suffix_family {n d : ℕ} (m : ℕ) (s : ChainState n (CoordSpace (d+1+m))) :
    ∃ f : RankinFamily s.M (m+1), f.vec 0 = s.winner ∧
      sqrt (Matrix.gram ℝ f.vec).det = ∏ l ∈ Icc 1 (m+1), suffixLength m s l := by
  induction m with
  | zero =>
    let f : Fin 1 → CoordSpace (d+1) := fun _ ↦ s.winner
    have hg : (Matrix.gram ℝ f).det = ‖s.winner‖^2 := by
      simp [Matrix.gram_apply,f]
    exact ⟨⟨f,fun _ ↦ s.shortest.1,Matrix.det_gram_ne_zero_iff_linearIndependent.mp
      (hg ▸ (sq_pos_of_pos (norm_pos_iff.mpr s.shortest.2.1)).ne')⟩,rfl,by
        change sqrt (Matrix.gram ℝ f).det = _
        simp [f,suffixLength]⟩
  | succ m ih =>
    obtain ⟨b,_,hb⟩ := ih s.freeze
    obtain ⟨f,hh,hg⟩ := lift_freeze_family s b
    refine ⟨f,hh,?_⟩
    rw [hg,sqrt_mul (sq_nonneg _),sqrt_sq (norm_nonneg _),hb,suffix_prod_step,mul_comm]

/-- Only ranks four through eight and rank twenty-four require further Hermite constants
for this intrinsic-volume argument. -/
def ExceptionalFamilyBounds : Prop :=
  ∀ k, (4 ≤ k ∧ k ≤ 8) ∨ k = 24 → FamilyHermite k (flagGamma k)

theorem familyHermite_of_exceptional (caps : ExceptionalFamilyBounds) (k : ℕ) (hk : 2 ≤ k) :
    FamilyHermite k (flagGamma k) := by
  by_cases ex : (4 ≤ k ∧ k ≤ 8) ∨ k = 24
  · exact caps k ex
  by_cases h2 : k = 2
  · subst k; exact familyHermite_two
  by_cases h3 : k = 3
  · subst k; exact familyHermite_three
  have : NeZero k := ⟨by omega⟩
  simpa [flagGamma,auditedGamma,show k ≠ 1 by omega,show k ≠ 24 by omega,
    show ¬(2 ≤ k ∧ k ≤ 8) by omega] using familyHermite_blichfeldt k

theorem suffix_hermite {n d : ℕ} (m : ℕ) (s : ChainState n (CoordSpace (d+1+m))) (l : ℕ)
    (lo : 2 ≤ l) (hi : l ≤ m+1) {g : ℝ} (cap : FamilyHermite l g) :
    suffixLength m s l ^ 2 ≤ g * (∏ r ∈ Icc 1 l, suffixLength m s r) ^ (2/(l:ℝ)) := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases h : l = m+2
    · subst l
      obtain ⟨f,_,hf⟩ := suffix_family (m+1) s
      simpa only [suffixLength_head,hf] using cap s.M s.shortest f
    · have e : ∏ r ∈ Icc 1 l, suffixLength (m+1) s r =
          ∏ r ∈ Icc 1 l, suffixLength m s.freeze r := by
        apply prod_congr rfl
        intro r hr
        have := (mem_Icc.mp hr).2
        simp [suffixLength,show r ≠ m+2 by omega]
      rw [e,suffixLength,ite_eq_right h]
      exact ih s.freeze (by omega)

/-- Profile for an actual run of m designated freezes in a single window. -/
def physicalSuffixProfile {n d : ℕ} (m : ℕ) (s : ChainState n (CoordSpace (d+1+m)))
    (short : suffixLength m s 1 ≤ planeRadius)
    (caps : ∀ l, 2 ≤ l → l ≤ m+1 → FamilyHermite l (flagGamma l)) : SuffixProfile (m+1) :=
  SuffixProfile.of_physical _ _ (fun l _ _ ↦ suffixLength_pos m s l) (by omega) short
    (fun l lo hi ↦ suffix_hermite m s l lo hi (caps l lo hi))

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.familyHermite_blichfeldt
#print axioms SigabaNeo.Wall1.ControlledPlane.familyHermite_two
#print axioms SigabaNeo.Wall1.ControlledPlane.familyHermite_three
#print axioms SigabaNeo.Wall1.ControlledPlane.lift_freeze_family
#print axioms SigabaNeo.Wall1.ControlledPlane.suffix_family
#print axioms SigabaNeo.Wall1.ControlledPlane.familyHermite_of_exceptional
#print axioms SigabaNeo.Wall1.ControlledPlane.suffix_hermite
#print axioms SigabaNeo.Wall1.ControlledPlane.physicalSuffixProfile
