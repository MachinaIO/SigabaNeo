import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonHigherIndex
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonFiniteGram

/-! Finite residue codes for overlattices of a shortest frame. In a frame of index
`d`, test the integer numerators of vectors, whose actual coordinates are divided by `d`. -/

noncomputable section
namespace SigabaNeo.Wall1.Watson.HigherGram

open Submodule Module Matrix Finset MeasureTheory TerminalProjection DecoupledDecoder ControlledPlane
variable {n : ℕ}
local notation "E" => CoordSpace n
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev Code (n d : ℕ) := AddSubgroup (Fin n → ZMod d)

def value (G : Mat n) (z : Fin n → ℤ) : ℝ :=
  let u : Fin n → ℝ := fun i ↦ z i
  u ⬝ᵥ G *ᵥ u

def vec (b : Fin n → E) (z : Fin n → ℤ) := ∑ i, (z i : ℝ) • b i

theorem energy (b : Fin n → E) (z : Fin n → ℤ) :
    value (gram ℝ b) z = ‖vec b z‖^2 := by
  simpa [value, vec, real_inner_self_eq_norm_sq] using
    star_dotProduct_gram_mulVec b (fun i ↦ (z i : ℝ)) (fun i ↦ (z i : ℝ))

theorem coord (B : Basis (Fin n) ℝ E) (z : Fin n → ℤ) (i : Fin n) :
    B.repr (vec B z) i = (z i : ℝ) := congrFun (B.repr_sum_self (fun j ↦ (z j : ℝ))) i

/-- Identify the residue code with the actual quotient of the lattice by its frame.
The membership equivalence holds for every integer numerator, in every coset. -/
theorem frame_code (B : Basis (Fin n) ℝ E) (L : Submodule ℤ E)
    (sub : span ℤ (Set.range B) ≤ L) {d : ℕ}
    (idx : (span ℤ (Set.range B)).toAddSubgroup.relIndex L.toAddSubgroup = d) (hd : 0 < d) :
    ∃ C : Code n d, Nat.card C = d ∧ ∀ z : Fin n → ℤ,
      (fun i ↦ (z i : ZMod d)) ∈ C ↔ (d : ℝ)⁻¹ • vec B z ∈ L := by
  classical
  let M := span ℤ (Set.range B)
  let K := M.toAddSubgroup.addSubgroupOf L.toAddSubgroup
  have nz : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  let mult : L →+ M :=
    { toFun := fun x ↦ ⟨d • (x : E), by
        have h := K.nsmul_index_mem x
        rw [show K.index = d from idx] at h
        exact h⟩
      map_zero' := by ext1; simp
      map_add' := fun x y ↦ by ext1; simp }
  let num := (B.restrictScalars ℤ).equivFun.toAddEquiv.toAddMonoidHom.comp mult
  have num_eq (x : L) (i : Fin n) : ((num x i : ℤ) : ℝ) = d * B.repr (x : E) i := by
    change algebraMap ℤ ℝ ((B.restrictScalars ℤ).repr (mult x) i) = _
    rw [B.restrictScalars_repr_apply ℤ]
    change B.repr (d • (x : E)) i = _
    simp [nsmul_eq_mul]
  let f : L →+ (Fin n → ZMod d) :=
    { toFun := fun x i ↦ (num x i : ZMod d)
      map_zero' := by ext; simp
      map_add' := fun x y ↦ by ext; simp }
  have iff_res (x : L) (z : Fin n → ℤ) :
      f x = (fun i ↦ (z i : ZMod d)) ↔ (d : ℝ)⁻¹ • vec B z - x.val ∈ M := by
    rw [B.mem_span_iff_repr_mem ℤ]
    constructor
    · intro he i
      obtain ⟨k,hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ d).mp (congrFun he i)
      have hh : (z i : ℝ) - (num x i : ℝ) = d * k := by exact_mod_cast hk
      refine ⟨k,?_⟩
      simp only [map_sub,map_smul,Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul,
        coord,algebraMap_int_eq, eq_intCast]
      rw [num_eq] at hh
      field_simp
      nlinarith only [hh]
    · intro h
      funext i
      obtain ⟨k,hk⟩ := h i
      simp only [map_sub,map_smul,Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul,
        coord,algebraMap_int_eq, eq_intCast] at hk
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ d).mpr
      refine ⟨k,?_⟩
      apply (Int.cast_inj (α := ℝ)).mp
      push_cast
      rw [num_eq]
      field_simp at hk
      linarith
  have ker : f.ker = K := by
    ext x
    change f x = 0 ↔ x.val ∈ M
    change (f x = fun _ ↦ 0) ↔ _
    simpa [vec] using iff_res x 0
  refine ⟨f.range,?_,fun z ↦ ⟨?_,?_⟩⟩
  · rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv,ker]
    exact idx
  · rintro ⟨x,hx⟩
    exact (sub (iff_res x z |>.mp hx)) |> fun h ↦ by simpa using L.add_mem h x.property
  · intro h
    exact ⟨⟨_,h⟩,(iff_res _ z).mpr (by simp)⟩

/-- A chart for one overlattice. The box makes the chart compact.
The quadratic value is linear in the matrix being constrained. -/
def polytope (d K : ℕ) (C : Code n d) : Set (Mat n) :=
  (Set.Icc (-1:ℝ) 1).matrix ∩ {G | G.IsHermitian} ∩ {G | ∀ i, G i i = 1} ∩
    {G | ∀ z : Fin n → ℤ, z ≠ 0 → (∀ i, |z i| ≤ (K : ℤ)) →
      (fun i ↦ (z i : ZMod d)) ∈ C → (d : ℝ)^2 ≤ value G z}

/-- A finite family of determinant problems, indexed by a bounded index and an order-d
subgroup of a finite abelian group. The radius is measured in numerator coordinates. -/
def Bound (n maxIndex : ℕ) (radius : ℕ → ℕ) (power : ℝ) : Prop :=
  ∀ d, 0 < d → d ≤ maxIndex → ∀ C : Code n d, Nat.card C = d →
    ∀ G ∈ polytope d (radius d) C, (d : ℝ)^2 ≤ power * G.det

theorem power_of_bound [NeZero n] {D : ℕ} {R : ℕ → ℕ} {p : ℝ} (hp : 0 ≤ p)
    (idx : ∀ (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
      (B : Basis (Fin n) ℝ E), (∀ i, IsShortest L (B i)) →
      (span ℤ (Set.range B)).toAddSubgroup.relIndex L.toAddSubgroup ≤ D)
    (cert : Bound n D R p) (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {v : E} (hv : IsShortest L v) : (‖v‖^2)^n ≤ p * ZLattice.covolume L^2 := by
  obtain ⟨A,B,short,hs,vol⟩ := wellRounded_reduction L hv
  let T := span ℤ (Set.range A)
  let M := span ℤ (Set.range B)
  let d := M.toAddSubgroup.relIndex T.toAddSubgroup
  have sub : M ≤ T := span_le.mpr (Set.range_subset_iff.mpr fun i ↦ (hs i).1)
  have indexVol : (d : ℝ) * ZLattice.covolume T = ZLattice.covolume M :=
    ((div_eq_iff (ZLattice.covolume_pos T volume).ne').mp
      (ZLattice.covolume_div_covolume_eq_relIndex' M T sub)).symm
  have dp : 0 < (d : ℝ) := pos_of_mul_pos_left
    (indexVol.trans_gt (ZLattice.covolume_pos M volume)) (ZLattice.covolume_pos T volume).le
  obtain ⟨C,card,mem⟩ := frame_code B T sub (d := d) rfl (by exact_mod_cast dp)
  let q := ‖v‖^2
  have qp : 0 < q := sq_pos_of_pos (norm_pos_iff.mpr hv.2.1)
  have len (i : Fin n) : ‖B i‖ = ‖v‖ := le_antisymm
    ((hs i).2.2 _ short.1 short.2.1) (short.2.2 _ (hs i).1 (hs i).2.1)
  let G := q⁻¹ • gram ℝ B
  have pd : G.PosDef :=
    (posDef_gram_of_linearIndependent B.linearIndependent).smul (inv_pos.mpr qp)
  have hG : G ∈ polytope d (R d) C := by
    refine ⟨⟨⟨?_,pd.1⟩,fun i ↦ ?_⟩,fun z hz _ hc ↦ ?_⟩
    · intro i j
      change q⁻¹ * inner ℝ (B i) (B j) ∈ Set.Icc _ _
      apply abs_le.mp
      rw [abs_mul,abs_of_pos (inv_pos.mpr qp),← div_eq_inv_mul,div_le_one qp]
      simpa [q,len,pow_two] using abs_real_inner_le_norm (B i) (B j)
    · change q⁻¹ * inner ℝ (B i) (B i) = 1
      rw [real_inner_self_eq_norm_sq,len,inv_mul_cancel₀ qp.ne']
    · have hn : vec B z ≠ 0 := by
        intro he
        apply hz
        funext i
        have hh := coord B z i
        simpa [he] using hh.symm
      have h := short.2.2 _ ((mem z).mp hc) (smul_ne_zero (inv_ne_zero dp.ne') hn)
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr dp),← div_eq_inv_mul,
        le_div_iff₀ dp] at h
      have hh := pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) dp.le) h 2
      change (d : ℝ)^2 ≤ value (q⁻¹ • gram ℝ B) z
      rw [show value (q⁻¹ • gram ℝ B) z = q⁻¹ * value (gram ℝ B) z by
        simp [value,smul_mulVec,dotProduct_smul],energy,← div_eq_inv_mul,le_div_iff₀ qp]
      nlinarith only [hh]
  have hh := cert d (by exact_mod_cast dp) (idx T B hs) C card G hG
  change (d : ℝ)^2 ≤ p * (q⁻¹ • gram ℝ B).det at hh
  rw [det_smul,Fintype.card_fin,inv_pow,← covolume_span_sq_eq_gram,← indexVol] at hh
  have h' : q^n ≤ p * ZLattice.covolume T^2 := by
    field_simp [qp.ne'] at hh
    apply le_of_mul_le_mul_left (a := (d : ℝ)^2) _ (sq_pos_of_pos dp)
    nlinarith only [hh]
  exact h'.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (ZLattice.covolume_pos T volume).le vol 2) hp)

end SigabaNeo.Wall1.Watson.HigherGram

#print axioms SigabaNeo.Wall1.Watson.HigherGram.frame_code
#print axioms SigabaNeo.Wall1.Watson.HigherGram.power_of_bound
