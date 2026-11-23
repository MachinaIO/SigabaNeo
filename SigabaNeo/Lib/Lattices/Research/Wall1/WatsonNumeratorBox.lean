import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonResidueGram

/-! Finite minimum tests in numerator coordinates. A determinant bound for the integer
frame controls the length of all coordinates, including those of points in other cosets. -/

noncomputable section
namespace SigabaNeo.Wall1.Watson.HigherGram

open Submodule Module Matrix Finset MeasureTheory TerminalProjection DecoupledDecoder ControlledPlane
variable {n : ℕ}
local notation "E" => CoordSpace n
local notation "I" => Fin n

theorem basis_with_gram [NeZero n] (G : Mat n) (pos : G.PosDef) :
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
theorem coordinate_bound (B : Basis I ℝ E) (unit : ∀ i, ‖B i‖ = 1)
    (z : I → ℤ) (i : I) :
    |(z i : ℝ)| * ZLattice.covolume (span ℤ (Set.range B)) ≤ ‖vec B z‖ := by
  classical
  let o := EuclideanSpace.basisFun I ℝ
  let d := o.toBasis.det
  let b := Function.update (⇑B) i (vec B z)
  have dt : d b = (z i : ℝ) * d B := by
    unfold b vec
    rw [d.map_update_sum]
    simp_rw [d.map_update_smul]
    rw [sum_eq_single i]
    · rw [Function.update_eq_self]; rfl
    · intro j _ hn
      simp [d.map_update_self _ hn.symm]
    · simp
  have : Fact (finrank ℝ E = n) := ⟨finrank_euclideanSpace_fin⟩
  have h := o.toBasis.orientation.abs_volumeForm_apply_le b
  rw [o.toBasis.orientation.volumeForm_robust o rfl] at h
  have norms : (fun j ↦ ‖b j‖) = Function.update (fun _ ↦ (1:ℝ)) i ‖vec B z‖ := by
    funext j
    by_cases he : j = i <;> simp [b,he,unit]
  have prod : ∏ j, ‖b j‖ = ‖vec B z‖ := by
    change ∏ j, (fun j ↦ ‖b j‖) j = _
    rw [norms,prod_update_of_mem (mem_univ _)]
    simp
  rw [← prod,minkowski_covolume_eq_abs_det,← abs_mul]
  exact dt ▸ h

private theorem id_test (z : I → ℤ) (hz : z ≠ 0) : 1 ≤ value (1 : Mat n) z := by
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hz
  change z j ≠ 0 at hj
  have one : (1:ℤ) ≤ z j * z j := by have := sq_pos_of_ne_zero hj; nlinarith
  have h := single_le_sum (f := fun i ↦ z i * z i) (fun i _ ↦ mul_self_nonneg _) (mem_univ j)
  unfold value
  simp only [one_mulVec,dotProduct]
  exact_mod_cast one.trans h


private theorem prior_bound (hn : 2 ≤ n) (B : Basis I ℝ E) [NeZero n]
    (hs : IsShortest (span ℤ (Set.range B)) (B 0)) :
    (‖B 0‖^2)^n ≤ MordellBlichfeldt.gamma n ^ n * (gram ℝ B).det := by
  let b : RankinFamily (span ℤ (Set.range B)) n :=
    ⟨B,fun i ↦ subset_span (Set.mem_range_self i),B.linearIndependent⟩
  have h := pow_le_pow_left₀ (sq_nonneg _) (MordellBlichfeldt.family n hn _ hs b) n
  rw [mul_pow,← Real.rpow_mul_natCast (Real.sqrt_nonneg _),div_mul_cancel₀ _
    (Nat.cast_ne_zero.mpr (NeZero.ne n)),Real.rpow_two] at h
  simpa [b, Real.sq_sqrt (posSemidef_gram ℝ (⇑B)).det_nonneg] using h

private theorem bound_in_slab [NeZero n] (hn : 2 ≤ n) (K : ℕ) (G : Mat n) (pos : G.PosDef)
    (diag : ∀ i, G i i = 1) (slab : 1 < ((K+1 : ℕ) : ℝ)^2 * G.det)
    (tests : ∀ z : I → ℤ, z ≠ 0 → (∀ i, |z i| ≤ (K : ℤ)) → 1 ≤ value G z) :
    1 ≤ MordellBlichfeldt.gamma n ^ n * G.det := by
  obtain ⟨B,rfl⟩ := basis_with_gram G pos
  let L := span ℤ (Set.range B)
  have unit (i : I) : ‖B i‖ = 1 := by
    specialize diag i
    rw [gram_apply,real_inner_self_eq_norm_sq] at diag
    nlinarith [norm_nonneg (B i)]
  have hs : IsShortest L (B 0) := by
    refine ⟨subset_span (Set.mem_range_self _),B.ne_zero _,?_⟩
    intro w hw hnz
    obtain ⟨z,rfl⟩ := (mem_span_range_iff_exists_fun ℤ).mp hw
    simp only [← Int.cast_smul_eq_zsmul ℝ] at hnz ⊢
    change ‖B 0‖ ≤ ‖vec B z‖
    rw [unit]
    by_contra! small
    have hz : z ≠ 0 := by intro he; simp [he] at hnz
    have bounded (i : I) : |z i| ≤ (K : ℤ) := by
      by_contra! bad
      have big : ((K+1 : ℕ) : ℝ) ≤ |(z i : ℝ)| := by
        exact_mod_cast (show ((K : ℤ)+1) ≤ |z i| by omega)
      have h := (mul_le_mul_of_nonneg_right big (ZLattice.covolume_pos L volume).le).trans
        (coordinate_bound B unit z i)
      have hh := pow_lt_pow_left₀ (h.trans_lt small) (mul_nonneg
        (Nat.cast_nonneg _) (ZLattice.covolume_pos L volume).le) (by decide : 2 ≠ 0)
      rw [mul_pow, covolume_span_sq_eq_gram B] at hh
      linarith
    have h := tests z hz bounded
    rw [energy] at h
    nlinarith [sq_lt_sq' (by linarith [norm_nonneg (vec B z)] : -(1:ℝ) < ‖vec B z‖) small]
  simpa only [unit,one_pow] using prior_bound hn B hs

/-- The frame tests alone certify the a priori determinant lower bound throughout the
positive definite chart. Interpolation with the identity uses only integer frame points. -/
theorem frame_det [NeZero n] (hn : 2 ≤ n) (K : ℕ)
    (gap : MordellBlichfeldt.gamma n ^ n < ((K+1 : ℕ) : ℝ)^2)
    (one : 1 ≤ MordellBlichfeldt.gamma n ^ n)
    (G : Mat n) (pos : G.PosDef) (diag : ∀ i, G i i = 1)
    (tests : ∀ z : I → ℤ, z ≠ 0 → (∀ i, |z i| ≤ (K : ℤ)) → 1 ≤ value G z) :
    1 ≤ MordellBlichfeldt.gamma n ^ n * G.det := by
  let p := MordellBlichfeldt.gamma n ^ n
  have pp : 0 < p := pow_pos (MordellBlichfeldt.gamma_pos _) _
  let k := ((K+1 : ℕ) : ℝ)^2
  have kp : 0 < k := pp.trans gap
  by_contra! bad
  let P (t : ℝ) := (1-t) • G + t • (1 : Mat n)
  let r := (max G.det (1/k) + 1/p)/2
  have sm : max G.det (1/k) < 1/p := max_lt ((lt_div_iff₀ pp).mpr
    (by linarith only [bad] : G.det * p < 1)) (one_div_lt_one_div_of_lt pp gap)
  have lo : 1/k < r := by dsimp only [r]; linarith [le_max_right G.det (1/k)]
  have hi : r < 1/p := by dsimp only [r]; linarith
  have start : G.det ≤ r := by dsimp only [r]; linarith [le_max_left G.det (1/k)]
  have cont : Continuous (fun t ↦ (P t).det) := by dsimp [P]; fun_prop
  have top : r < 1 := hi.trans_le ((div_le_one pp).mpr one)
  obtain ⟨t,ht,eq⟩ := intermediate_value_Icc (zero_le_one : (0:ℝ) ≤ 1) cont.continuousOn
    (show r ∈ Set.Icc (P 0).det (P 1).det by simpa [P] using And.intro start top.le)
  change (P t).det = r at eq
  have t1 : t < 1 := lt_of_le_of_ne ht.2 (by intro he; subst t; simp [P] at eq; linarith)
  have pd := (pos.smul (sub_pos.mpr t1)).add_posSemidef
    ((PosSemidef.one : (1:Mat n).PosSemidef).smul ht.1)
  have h := bound_in_slab hn K (P t) pd (fun i ↦ by simp [P,diag])
    (by change 1 < k * (P t).det; rw [eq,mul_comm]; exact (div_lt_iff₀ kp).mp lo)
    (fun z hz hb ↦ by
      have e : value (P t) z = (1-t)*value G z + t * value 1 z := by
        simp [P,value,add_mulVec,smul_mulVec,dotProduct_add,dotProduct_smul]
      rw [e]
      nlinarith only [mul_le_mul_of_nonneg_left (tests z hz hb) (sub_nonneg.mpr ht.2),
        mul_le_mul_of_nonneg_left (id_test z hz) ht.1])
  change 1 ≤ p * (P t).det at h
  rw [eq] at h
  linarith [(lt_div_iff₀ pp).mp hi]

/-- The finite frame tests exclude singular and indefinite matrices as well.
Shift the least eigenvalue to zero and interpolate that singular form with the identity.
A positive definite interpolant of small determinant would contradict `frame_det`. -/
theorem frame_pos [NeZero n] (hn : 2 ≤ n) (K : ℕ)
    (gap : MordellBlichfeldt.gamma n ^ n < ((K+1 : ℕ) : ℝ)^2)
    (one : 1 ≤ MordellBlichfeldt.gamma n ^ n)
    (G : Mat n) (sym : G.IsHermitian) (diag : ∀ i, G i i = 1)
    (tests : ∀ z : I → ℤ, z ≠ 0 → (∀ i, |z i| ≤ (K : ℤ)) → 1 ≤ value G z) :
    G.PosDef := by
  classical
  by_contra bad
  obtain ⟨i,_,least⟩ := exists_min_image univ sym.eigenvalues univ_nonempty
  let m := sym.eigenvalues i
  have ml (j : I) : m ≤ sym.eigenvalues j := least j (mem_univ _)
  have hm : m ≤ 0 := by
    by_contra! pos
    exact bad (sym.posDef_iff_eigenvalues_pos.mpr fun j ↦ pos.trans_le (ml j))
  let H := G - m • (1 : Mat n)
  have he : H = Unitary.conjStarAlgAut ℝ _ sym.eigenvectorUnitary
      (diagonal (fun j ↦ sym.eigenvalues j - m)) := by
    have deq : diagonal (fun j ↦ sym.eigenvalues j - m) =
        diagonal (RCLike.ofReal ∘ sym.eigenvalues : I → ℝ) - m • (1 : Mat n) := by
      ext j k
      by_cases e : j = k <;> simp [e]
    rw [deq,map_sub,map_smul,map_one,← sym.spectral_theorem]
  have sem : H.PosSemidef := by
    rw [he,Unitary.conjStarAlgAut_apply]
    exact (posSemidef_diagonal_iff.mpr fun j ↦ sub_nonneg.mpr (ml j)).mul_mul_conjTranspose_same _
  have singular : H.det = 0 := by
    have mem := sym.eigenvalues_mem_spectrum_real i
    have non : ¬ IsUnit (m • (1 : Mat n) - G) := by
      simpa [m,spectrum.mem_iff,Algebra.algebraMap_eq_smul_one] using mem
    by_contra nz
    exact non (by rw [← neg_sub]; exact ((Matrix.isUnit_iff_isUnit_det H).mpr
      (isUnit_iff_ne_zero.mpr nz)).neg)
  have c : 0 < 1 - m := by linarith
  let P (t : ℝ) := (1-t) • ((1-m)⁻¹ • H) + t • (1 : Mat n)
  let p := MordellBlichfeldt.gamma n ^ n
  have pp : 0 < p := pow_pos (MordellBlichfeldt.gamma_pos _) _
  let r := 1/(2*p)
  have rp : 0 < r := by dsimp [r]; positivity
  have rt : r ≤ 1 := (div_le_one (by positivity)).mpr (by change 1 ≤ 2*p; linarith)
  have cont : Continuous (fun t ↦ (P t).det) := by dsimp [P]; fun_prop
  obtain ⟨t,ht,eq⟩ := intermediate_value_Icc (zero_le_one : (0:ℝ) ≤ 1) cont.continuousOn
    (show r ∈ Set.Icc (P 0).det (P 1).det by simpa [P,det_smul,singular] using And.intro rp.le rt)
  change (P t).det = r at eq
  have tp : 0 < t := lt_of_le_of_ne ht.1 (by intro e; subst t; simp [P,singular] at eq; linarith)
  have pos : (P t).PosDef := by
    dsimp only [P]
    rw [add_comm]
    exact (PosDef.one.smul tp).add_posSemidef
      ((sem.smul (inv_pos.mpr c).le).smul (sub_nonneg.mpr ht.2))
  have D (j : I) : (P t) j j = 1 := by simp [P,H,diag,c.ne']
  have T := frame_det hn K gap one (P t) pos D (fun z hz hb ↦ by
    have e : value (P t) z =
        (1-t)*((1-m)⁻¹*(value G z - m*value 1 z)) + t*value 1 z := by
      simp [P,H,value,add_mulVec,sub_mulVec,smul_mulVec,dotProduct_add,dotProduct_sub,
        dotProduct_smul]
    have first : 1 ≤ (1-m)⁻¹*(value G z - m*value 1 z) := by
      rw [← div_eq_inv_mul,le_div_iff₀ c,one_mul]
      nlinarith only [tests z hz hb,mul_le_mul_of_nonpos_left (id_test z hz) hm]
    rw [e]
    nlinarith only [mul_le_mul_of_nonneg_left first (sub_nonneg.mpr ht.2),
      mul_le_mul_of_nonneg_left (id_test z hz) ht.1])
  change 1 ≤ p * (P t).det at T
  rw [eq] at T
  dsimp only [r] at T
  field_simp at T
  linarith

/-- In every chart of radius (K+1)*d the box tests are equivalent to
the complete minimum test on the overlattice. No enumeration of long vectors is needed. -/
theorem all_numerators [NeZero n] (hn : 2 ≤ n) {K d : ℕ} (hd : 0 < d)
    (gap : MordellBlichfeldt.gamma n ^ n < ((K+1 : ℕ) : ℝ)^2)
    (one : 1 ≤ MordellBlichfeldt.gamma n ^ n)
    (C : Code n d) {G : Mat n} (mem : G ∈ polytope d ((K+1)*d) C) :
    G.PosDef ∧ ∀ z : I → ℤ, z ≠ 0 → (fun i ↦ (z i : ZMod d)) ∈ C →
      (d : ℝ)^2 ≤ value G z := by
  obtain ⟨⟨⟨_,sym⟩,diag⟩,tests⟩ := mem
  have dp : 0 < (d : ℝ) := by exact_mod_cast hd
  have base (u : I → ℤ) (hu : u ≠ 0) (hb : ∀ i, |u i| ≤ (K : ℤ)) : 1 ≤ value G u := by
    let w (i : I) : ℤ := d * u i
    have nw : w ≠ 0 := by
      intro h
      apply hu
      funext i
      simpa [w,hd.ne'] using congrFun h i
    have h := tests w nw (fun i ↦ by
      have := mul_le_mul_of_nonneg_left (hb i) (Int.natCast_nonneg d)
      simp [w,abs_mul] at *; nlinarith) (by
      convert C.zero_mem using 1
      ext i
      simp [w])
    have eq : (fun i ↦ (w i : ℝ)) = (d : ℝ) • (fun i ↦ (u i : ℝ)) := by ext; simp [w]
    simp only [value,eq,mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul] at h
    change 1 ≤ (fun i ↦ (u i : ℝ)) ⬝ᵥ G *ᵥ (fun i ↦ (u i : ℝ))
    exact le_of_mul_le_mul_left (a := (d : ℝ)^2) (by nlinarith only [h]) (sq_pos_of_pos dp)
  have pos := frame_pos hn K gap one G sym diag base
  refine ⟨pos,fun z hz hc ↦ ?_⟩
  have low := frame_det hn K gap one G pos diag base
  obtain ⟨B,rfl⟩ := basis_with_gram G pos
  have unit (i : I) : ‖B i‖ = 1 := by
    specialize diag i
    rw [gram_apply,real_inner_self_eq_norm_sq] at diag
    nlinarith [norm_nonneg (B i)]
  by_cases box : ∀ i, |z i| ≤ (((K+1)*d : ℕ) : ℤ)
  · exact tests z hz box hc
  push Not at box
  obtain ⟨i,large⟩ := box
  have large' : (((K+1 : ℕ) : ℝ) * d) < |(z i : ℝ)| := by exact_mod_cast large
  let V := ZLattice.covolume (span ℤ (Set.range B))
  have vp : 0 < V := ZLattice.covolume_pos _ _
  have h := (mul_le_mul_of_nonneg_right large'.le vp.le).trans (coordinate_bound B unit z i)
  have vol : V^2 = (gram ℝ B).det := covolume_span_sq_eq_gram B
  rw [← vol] at low
  have hh := mul_le_mul_of_nonneg_right gap.le (sq_nonneg V)
  have vk : 1 ≤ ((K+1 : ℕ) : ℝ) * V := by
    have a : 0 ≤ ((K+1 : ℕ) : ℝ) * V := mul_nonneg (Nat.cast_nonneg _) vp.le
    nlinarith only [low,hh,a]
  have x := mul_le_mul_of_nonneg_right vk dp.le
  rw [energy]
  exact pow_le_pow_left₀ dp.le (by nlinarith only [h,x]) 2

theorem six_box {d : ℕ} (hd : 0 < d) (C : Code 6 d) {G : Mat 6}
    (mem : G ∈ polytope d (6*d) C) : G.PosDef ∧ ∀ z : Fin 6 → ℤ,
      z ≠ 0 → (fun i ↦ (z i : ZMod d)) ∈ C → (d : ℝ)^2 ≤ value G z := by
  apply all_numerators (K := 5) (by decide) hd _ _ C mem
  · exact (pow_le_pow_left₀ (MordellBlichfeldt.gamma_pos _).le
      MordellBlichfeldt.exceptional_enclosures.2.2.2.1 6).trans_lt (by norm_num)
  · exact one_le_pow₀ ((by norm_num : (1 : ℝ) ≤ 1.7817964) |>.trans
      MordellBlichfeldt.exceptional_enclosures.2.2.1)

theorem seven_box {d : ℕ} (hd : 0 < d) (C : Code 7 d) {G : Mat 7}
    (mem : G ∈ polytope d (11*d) C) : G.PosDef ∧ ∀ z : Fin 7 → ℤ,
      z ≠ 0 → (fun i ↦ (z i : ZMod d)) ∈ C → (d : ℝ)^2 ≤ value G z := by
  apply all_numerators (K := 10) (by decide) hd _ _ C mem
  · exact (pow_le_pow_left₀ (MordellBlichfeldt.gamma_pos _).le
      MordellBlichfeldt.exceptional_enclosures.2.2.2.2.2.1 7).trans_lt (by norm_num)
  · exact one_le_pow₀ ((by norm_num : (1 : ℝ) ≤ 1.9723411) |>.trans
      MordellBlichfeldt.exceptional_enclosures.2.2.2.2.1)

end SigabaNeo.Wall1.Watson.HigherGram

#print axioms SigabaNeo.Wall1.Watson.HigherGram.frame_det
#print axioms SigabaNeo.Wall1.Watson.HigherGram.all_numerators

#print axioms SigabaNeo.Wall1.Watson.HigherGram.six_box
#print axioms SigabaNeo.Wall1.Watson.HigherGram.seven_box
