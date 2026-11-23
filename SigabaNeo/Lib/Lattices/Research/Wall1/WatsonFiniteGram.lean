import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonWellRounded
import SigabaNeo.Lib.Lattices.Research.Wall1.ControlledSuffixDescent
import Mathlib.Analysis.Matrix.Order

/-! A finite Gram-matrix criterion for the sharp Hermite inequality in rank five. -/

noncomputable section
namespace SigabaNeo.Wall1.Watson

open Submodule Module Matrix Finset MeasureTheory TerminalProjection DecoupledDecoder ControlledPlane
open scoped RealInnerProductSpace

local notation "E" => CoordSpace 5
local notation "I" => Fin 5
local notation "Mat" => Matrix I I ℝ

/-- The squared length in the form G of a vector with integral coordinates z. -/
def gramValue (G : Mat) (z : I → ℤ) : ℝ :=
  let u : I → ℝ := fun i ↦ z i
  u ⬝ᵥ G *ᵥ u

/-- Coefficients needed for the rank-five minimum test. -/
def GramTest (z : I → ℤ) : Prop :=
  (∀ i, |z i| ≤ 1) ∨ ∃ j, |z j| = 2 ∧ ∀ i, i ≠ j → |z i| = 1

/-- The determinant problem has ten free real entries and 201 nonzero coefficient
tests up to simultaneous sign reversal. -/
def FiniteGramBound : Prop :=
  ∀ G : Mat, G.PosDef → (∀ i, G i i = 1) →
    (∀ z : I → ℤ, z ≠ 0 → GramTest z → 1 ≤ gramValue G z) → 1 ≤ 8 * G.det

private def vector (b : I → E) (z : I → ℤ) := ∑ i, (z i : ℝ) • b i

private theorem energy (b : I → E) (z : I → ℤ) :
    gramValue (gram ℝ b) z = ‖vector b z‖^2 := by
  simpa [gramValue, vector, real_inner_self_eq_norm_sq] using
    star_dotProduct_gram_mulVec b (fun i ↦ (z i : ℝ)) (fun i ↦ (z i : ℝ))

private theorem value_smul (c : ℝ) (G : Mat) (z : I → ℤ) :
    gramValue (c • G) z = c * gramValue G z := by
  simp [gramValue,smul_mulVec,dotProduct_smul]

private theorem value_add (A B : Mat) (z : I → ℤ) :
    gramValue (A+B) z = gramValue A z + gramValue B z := by
  simp [gramValue,add_mulVec,dotProduct_add]

private theorem coord (B : Basis I ℝ E) (z : I → ℤ) (i : I) :
    B.repr (vector B z) i = (z i : ℝ) := congrFun (B.repr_sum_self (fun j ↦ (z j : ℝ))) i

private theorem vector_ne (B : Basis I ℝ E) {z : I → ℤ} (hz : z ≠ 0) : vector B z ≠ 0 := by
  intro h
  apply hz
  funext i
  have hh := coord B z i
  rw [h] at hh
  simpa using hh.symm

private theorem vector_mem (B : Basis I ℝ E) (z : I → ℤ) :
    vector B z ∈ span ℤ (Set.range B) :=
  (mem_span_range_iff_exists_fun ℤ).mpr ⟨z, by simp only [vector, Int.cast_smul_eq_zsmul ℝ]⟩

/-- The only geometric input still needed after well-rounded deformation and the index-two
bound is the determinant of a real Gram matrix of a shortest integral basis. -/
theorem rank_five_of_shortest_basis
    (basisBound : ∀ B : Basis I ℝ E, (∀ i, IsShortest (span ℤ (Set.range B)) (B i)) →
      ‖B 0‖^10 ≤ 8 * (gram ℝ B).det)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] {v : E} (hv : IsShortest L v) :
    ‖v‖^10 ≤ 8 * ZLattice.covolume L^2 := by
  obtain ⟨C,B,hv',hs,vol⟩ := wellRounded_reduction L hv
  let M := span ℤ (Set.range C)
  by_contra! bad
  have gap : 8 * ZLattice.covolume M^2 < ‖v‖^10 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (ZLattice.covolume_pos M volume).le vol 2) (by norm_num)) bad
  rcases rank_five_minimal_determinants M hv' gap B hs with zero | ⟨gen,det⟩
  · exact (posDef_gram_of_linearIndependent B.linearIndependent).det_pos.ne' zero
  have h := basisBound B (fun i ↦ gen ▸ hs i)
  rw [det] at h
  exact gap.not_ge ((pow_le_pow_left₀ (norm_nonneg _) (hv'.2.2 _ (hs 0).1 (hs 0).2.1) 10).trans h)

/-- The finite coefficient tests suffice for the original arbitrary-lattice inequality. -/
theorem rank_five_of_finite_gram (cert : FiniteGramBound)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] {v : E} (hv : IsShortest L v) :
    ‖v‖^10 ≤ 8 * ZLattice.covolume L^2 := by
  apply rank_five_of_shortest_basis _ L hv
  intro B hs
  let q := ‖B 0‖^2
  have qp : 0 < q := sq_pos_of_pos (norm_pos_iff.mpr (B.ne_zero 0))
  have normEq (i : I) : ‖B i‖ = ‖B 0‖ := le_antisymm
    ((hs i).2.2 _ (hs 0).1 (hs 0).2.1) ((hs 0).2.2 _ (hs i).1 (hs i).2.1)
  have hd (i : I) : (q⁻¹ • gram ℝ B) i i = 1 := by
    simp [gram_apply,normEq,q,B.ne_zero]
  have hh := cert (q⁻¹ • gram ℝ B) ((posDef_gram_of_linearIndependent B.linearIndependent).smul
    (inv_pos.mpr qp)) hd (fun z hz _ ↦ by
      rw [value_smul,energy,← div_eq_inv_mul,le_div_iff₀ qp,one_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) ((hs 0).2.2 _ (vector_mem B z) (vector_ne B hz)) 2)
  rw [det_smul,Fintype.card_fin,inv_pow] at hh
  field_simp [qp.ne'] at hh
  dsimp [q] at hh
  nlinarith only [hh]

/-- Convert the tenth-power bound to the intrinsic convention used in suffix descent. -/
theorem intrinsic_five_of_finite_gram (cert : FiniteGramBound) : IntrinsicHermite 5 (flagGamma 5) := by
  intro L _ _
  have hn : L ≠ ⊥ := by
    intro he
    have hs := IsZLattice.span_top (K:=ℝ) (L:=L)
    simp [he] at hs
  obtain ⟨v,hv,_⟩ := exists_orderedShortest L (fun _ ↦ (0:ℕ)) hn
  refine ⟨⟨v,hv.1⟩,fun h ↦ hv.2.1 (congrArg Subtype.val h),?_⟩
  have bound := rank_five_of_finite_gram cert L hv
  have pow5 : flagGamma 5 ^ 5 = 8 := by
    change Real.exp (Real.log 8 / 5) ^ 5 = 8
    rw [← Real.exp_nat_mul]
    convert Real.exp_log (by norm_num : (0:ℝ) < 8) using 2
    ring
  apply le_of_pow_le_pow_left₀ (by decide : 5 ≠ 0)
    (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (ZLattice.covolume_pos L volume).le _))
  change (‖v‖^2)^5 ≤ (flagGamma 5 * ZLattice.covolume L ^ (2/(5:ℝ)))^5
  rw [mul_pow,pow5,← Real.rpow_mul_natCast (ZLattice.covolume_pos L volume).le]
  norm_num
  nlinarith only [bound]

/-- Realize a positive-definite five-by-five matrix in the standard Euclidean space. -/
theorem basis_with_gram (G : Mat) (pos : G.PosDef) :
    ∃ B : Basis I ℝ E, gram ℝ B = G := by
  classical
  open scoped MatrixOrder in
    obtain ⟨A, hA⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp pos.posSemidef.nonneg
  let b (i : I) : E := WithLp.toLp 2 (fun j ↦ A j i)
  have eq : gram ℝ b = G := by
    rw [hA]
    ext i j
    simp [gram_apply, b, PiLp.inner_apply, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      mul_comm]
  have ind := linearIndependent_of_posDef_gram (eq ▸ pos)
  let B := basisOfLinearIndependentOfCardEqFinrank ind (by simp [CoordSpace])
  have hb : ⇑B = b := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  exact ⟨B, hb ▸ eq⟩

/-- Hadamard's bound after replacing one column gives a coordinate bound for
every short vector in a unit basis, with no reduction assumptions. -/
private theorem coordinate_bound (B : Basis I ℝ E) (unit : ∀ i, ‖B i‖ = 1)
    (z : I → ℤ) (i : I) :
    |(z i : ℝ)| * ZLattice.covolume (span ℤ (Set.range B)) ≤ ‖vector B z‖ := by
  classical
  let o := EuclideanSpace.basisFun I ℝ
  let d := o.toBasis.det
  let b := Function.update (⇑B) i (vector B z)
  have dt : d b = (z i : ℝ) * d B := by
    unfold b vector
    rw [d.map_update_sum]
    simp_rw [d.map_update_smul]
    rw [sum_eq_single i]
    · rw [Function.update_eq_self]; rfl
    · intro j _ hn
      simp [d.map_update_self _ hn.symm]
    · simp
  have : Fact (finrank ℝ E = 5) := ⟨finrank_euclideanSpace_fin⟩
  have h := o.toBasis.orientation.abs_volumeForm_apply_le b
  rw [o.toBasis.orientation.volumeForm_robust o rfl] at h
  have norms : (fun j ↦ ‖b j‖) = Function.update (fun _ ↦ (1:ℝ)) i ‖vector B z‖ := by
    funext j
    by_cases he : j = i <;> simp [b,he,unit]
  have prod : ∏ j, ‖b j‖ = ‖vector B z‖ := by
    change ∏ j, (fun j ↦ ‖b j‖) j = _
    rw [norms,prod_update_of_mem (mem_univ _)]
    simp
  rw [← prod,minkowski_covolume_eq_abs_det,← abs_mul]
  exact dt ▸ h

private theorem id_test (z : I → ℤ) (hz : z ≠ 0) : 1 ≤ gramValue 1 z := by
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hz
  change z j ≠ 0 at hj
  have one : (1:ℤ) ≤ z j * z j := by have := sq_pos_of_ne_zero hj; nlinarith
  have h := single_le_sum (f := fun i ↦ z i * z i) (fun i _ ↦ mul_self_nonneg _) (mem_univ j)
  unfold gramValue
  simp only [one_mulVec,dotProduct]
  exact_mod_cast one.trans h

private def ones (z : I → ℤ) := univ.filter fun i ↦ |z i| = 1

private theorem value_update (B : Basis I ℝ E) (z : I → ℤ) (i : I) (a : ℤ) :
    vector B (Function.update z i a) = vector B z + ((a:ℝ) - z i) • B i := by
  classical
  unfold vector
  rw [← sum_erase_add _ _ (mem_univ i),← sum_erase_add _ (fun j ↦ (z j:ℝ) • B j) (mem_univ i)]
  simp only [Function.update_self, sub_smul]
  rw [show (∑ j ∈ univ.erase i, ((Function.update z i a j : ℤ):ℝ) • B j) =
    ∑ j ∈ univ.erase i, (z j:ℝ) • B j from sum_congr rfl fun j hj ↦ by
      rw [Function.update_of_ne (mem_erase.mp hj).1]]
  abel

/-- Round a box vector toward even coordinates. Rounding a coefficient ±1 either way
increases the mean squared length by one. A coefficient ±2 keeps both branches nonzero. -/
private theorem rounding (B : Basis I ℝ E) (unit : ∀ i, ‖B i‖ = 1)
    (ternary : ∀ z : I → ℤ, z ≠ 0 → (∀ i, |z i| ≤ 1) → 1 ≤ ‖vector B z‖^2)
    (z : I → ℤ) (box : ∀ i, |z i| ≤ 2) {j : I} (two : |z j| = 2) :
    4 ≤ ‖vector B z‖^2 + ((ones z).card : ℝ) := by
  classical
  by_cases empty : ones z = ∅
  · let u (i : I) := z i / 2
    have even (i : I) : z i = 2 * u i := by
      have h : i ∉ ones z := by simp [empty]
      simp [ones] at h
      dsimp [u]
      have hb := abs_le.mp (box i)
      rcases le_total 0 (z i) with he | he
      · rw [abs_of_nonneg he] at h
        omega
      · rw [abs_of_nonpos he] at h
        omega
    have un : u ≠ 0 := by
      intro h
      have := even j
      simp [h] at this
      simp [this] at two
    have small := ternary u un (fun i ↦ abs_le.mpr (by have := even i; have := abs_le.mp (box i); omega))
    have eq : vector B z = (2:ℝ) • vector B u := by
      simp only [vector,Finset.smul_sum,smul_smul]
      apply sum_congr rfl
      intro i _
      rw [even i,Int.cast_mul,Int.cast_ofNat]
    rw [empty,eq,norm_smul,Real.norm_eq_abs]
    norm_num
    nlinarith only [small]
  obtain ⟨i,hi⟩ := nonempty_iff_ne_empty.mpr empty
  have one : |z i| = 1 := (mem_filter.mp hi).2
  have ij : j ≠ i := by intro h; subst i; omega
  have branch (a : ℤ) (ha : |a| ≤ 2) (hna : |a| ≠ 1) :
      4 ≤ ‖vector B (Function.update z i a)‖^2 + (((ones z).card : ℝ)-1) := by
    let w := Function.update z i a
    have card : ones w = (ones z).erase i := by
      ext k
      by_cases he : k = i <;> simp [ones,w,he,hna]
    have dec : (ones w).card < (ones z).card := by rw [card]; exact card_erase_lt_of_mem hi
    have bw (k : I) : |w k| ≤ 2 := by
      by_cases he : k = i <;> simp [w,he,ha,box]
    have h := rounding B unit ternary w bw (j := j) (by simpa [w,ij] using two)
    have count : ((ones w).card : ℝ) = ((ones z).card : ℝ)-1 := by
      have hc : (ones w).card + 1 = (ones z).card := card ▸ card_erase_add_one hi
      have hc' : ((ones w).card : ℝ) + 1 = (ones z).card := by exact_mod_cast hc
      linarith
    rwa [count] at h
  have sign : z i = 1 ∨ z i = -1 := (abs_eq (by norm_num : (0:ℤ) ≤ 1)).mp one
  have p := branch (z i + 1) (by rcases sign with h | h <;> norm_num [h])
    (by rcases sign with h | h <;> norm_num [h])
  have m := branch (z i - 1) (by rcases sign with h | h <;> norm_num [h])
    (by rcases sign with h | h <;> norm_num [h])
  rw [value_update] at p m
  push_cast at p m
  have p' : (z i : ℝ) + 1 - z i = 1 := by ring
  have m' : (z i : ℝ) - 1 - z i = -1 := by ring
  rw [p',one_smul,norm_add_sq_real,unit] at p
  rw [m',neg_one_smul,← sub_eq_add_neg,norm_sub_sq_real,unit] at m
  linarith
termination_by (ones z).card

private theorem box_tests (G : Mat) (pos : G.PosDef) (diag : ∀ i, G i i = 1)
    (tests : ∀ z : I → ℤ, z ≠ 0 → GramTest z → 1 ≤ gramValue G z)
    (z : I → ℤ) (hz : z ≠ 0) (box : ∀ i, |z i| ≤ 2) : 1 ≤ gramValue G z := by
  classical
  by_cases test : GramTest z
  · exact tests z hz test
  obtain ⟨j,hj⟩ : ∃ j, 1 < |z j| := by
    by_contra! h
    exact test (.inl h)
  have two : |z j| = 2 := le_antisymm (box j) (by omega)
  have few : (ones z).card ≤ 3 := by
    by_contra! many
    have sub : ones z ⊆ univ.erase j := fun i hi ↦ mem_erase.mpr
      ⟨fun e ↦ by have := (mem_filter.mp hi).2; subst i; omega,mem_univ _⟩
    have eq := eq_of_subset_of_card_le sub (by simpa using (show 4 ≤ (ones z).card by omega))
    exact test (.inr ⟨j,two,fun i hij ↦ (mem_filter.mp (show i ∈ ones z by simp [eq,hij])).2⟩)
  obtain ⟨B,rfl⟩ := basis_with_gram G pos
  have unit (i : I) : ‖B i‖ = 1 := by
    specialize diag i
    rw [gram_apply,real_inner_self_eq_norm_sq] at diag
    nlinarith [norm_nonneg (B i)]
  have h := rounding B unit (fun w hw sm ↦ energy B w ▸ tests w hw (.inl sm)) z box two
  rw [energy]
  linarith [show ((ones z).card : ℝ) ≤ 3 by exact_mod_cast few]

private theorem from_slab
    (allL : ∀ (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (v : E),
      IsShortest L v → ‖v‖^10 ≤ 8 * ZLattice.covolume L^2)
    (G : Mat) (pos : G.PosDef) (diag : ∀ i, G i i = 1) (slab : 1/9 < G.det)
    (tests : ∀ z : I → ℤ, z ≠ 0 → (∀ i, |z i| ≤ 2) → 1 ≤ gramValue G z) :
    1 ≤ 8 * G.det := by
  obtain ⟨B,hB⟩ := basis_with_gram G pos
  let L := span ℤ (Set.range B)
  have vol : ZLattice.covolume L^2 = G.det := (covolume_span_sq_eq_gram B).trans (congrArg det hB)
  have unit (i : I) : ‖B i‖ = 1 := by
    have hh := diag i
    rw [← hB,gram_apply,real_inner_self_eq_norm_sq] at hh
    nlinarith [norm_nonneg (B i)]
  have hs : IsShortest L (B 0) := by
    refine ⟨subset_span (Set.mem_range_self _),B.ne_zero _,?_⟩
    intro w hw hn
    obtain ⟨z,rfl⟩ := (mem_span_range_iff_exists_fun ℤ).mp hw
    simp only [← Int.cast_smul_eq_zsmul ℝ] at hn ⊢
    change ‖B 0‖ ≤ ‖vector B z‖
    rw [unit]
    by_contra! small
    have hz : z ≠ 0 := by intro he; simp [he] at hn
    have bounded (i : I) : |z i| ≤ 2 := by
      by_contra! bad
      have three : (3:ℝ) ≤ |(z i : ℝ)| := by exact_mod_cast (show 3 ≤ |z i| by omega)
      have h := (mul_le_mul_of_nonneg_right three (ZLattice.covolume_pos L volume).le).trans
        (coordinate_bound B unit z i)
      have hsq := pow_lt_pow_left₀ (h.trans_lt small)
        (mul_nonneg (by norm_num) (ZLattice.covolume_pos L volume).le) (by decide : 2 ≠ 0)
      nlinarith only [hsq,vol,slab]
    have h := tests z hz bounded
    rw [← hB,energy] at h
    nlinarith [sq_lt_sq' (by linarith [norm_nonneg (vector B z)] : -(1:ℝ) < ‖vector B z‖) small]
  simpa only [unit,one_pow,vol] using allL L (B 0) hs

/-- FiniteGramBound is also necessary. Interpolation with the identity moves a hypothetical
bad matrix into the open determinant interval (1/9,1/8). There Hadamard excludes every
short vector with a coefficient of absolute value at least three. -/
theorem finite_gram_iff :
    FiniteGramBound ↔ ∀ (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (v : E),
      IsShortest L v → ‖v‖^10 ≤ 8 * ZLattice.covolume L^2 := by
  refine ⟨fun h L _ _ _ hv ↦ rank_five_of_finite_gram h L hv,?_⟩
  intro h G pos diag tests
  by_contra! bad
  let P (t : ℝ) := (1-t) • G + t • (1 : Mat)
  let r := (max G.det (1/9) + 1/8)/2
  have small : max G.det (1/9) < 1/8 := max_lt (by linarith) (by norm_num)
  have lo : 1/9 < r := by dsimp [r]; linarith [le_max_right G.det (1/9)]
  have hi : r < 1/8 := by dsimp [r]; linarith
  have start : G.det ≤ r := by dsimp [r]; linarith [le_max_left G.det (1/9)]
  have continuous : Continuous (fun t ↦ (P t).det) := by dsimp [P]; fun_prop
  obtain ⟨t,ht,eq⟩ := intermediate_value_Icc (zero_le_one : (0:ℝ) ≤ 1) continuous.continuousOn
    (show r ∈ Set.Icc (P 0).det (P 1).det by simpa [P] using And.intro start (by linarith : r ≤ 1))
  have t1 : t < 1 := lt_of_le_of_ne ht.2 (by intro he; subst t; simp [P] at eq; linarith)
  have pp := (pos.smul (sub_pos.mpr t1)).add_posSemidef
    ((PosSemidef.one : (1:Mat).PosSemidef).smul ht.1)
  have hh := from_slab h (P t) pp (fun i ↦ by simp [P,diag])
    (by rw [show (P t).det = r from eq]; exact lo) (fun z hz box ↦ by
      simp only [P,value_add,value_smul]
      nlinarith only [mul_le_mul_of_nonneg_left (box_tests G pos diag tests z hz box) (sub_nonneg.mpr ht.2),
        mul_le_mul_of_nonneg_left (id_test z hz) ht.1])
  linarith

open TerminalProjection.Restart506 DualExit
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

/-- The exceptional-rank assumptions for suffix descent, with the finite rank-five
determinant criterion in place of the full intrinsic rank-five hypothesis. -/
theorem terminal_bound_of_finite_gram (cert : FiniteGramBound)
    (h6 : IntrinsicHermite 6 (flagGamma 6)) (h7 : IntrinsicHermite 7 (flagGamma 7))
    (h24 : IntrinsicHermite 24 4) :
    probability terminalHit < probability residual₁ + probability residual₂ + 6.515/(10:ℝ)^12 :=
  terminal_bound_of_intrinsic (intrinsic_five_of_finite_gram cert) h6 h7 h24

end SigabaNeo.Wall1.Watson

#print axioms SigabaNeo.Wall1.Watson.rank_five_of_shortest_basis
#print axioms SigabaNeo.Wall1.Watson.finite_gram_iff
#print axioms SigabaNeo.Wall1.Watson.intrinsic_five_of_finite_gram
#print axioms SigabaNeo.Wall1.Watson.terminal_bound_of_finite_gram
