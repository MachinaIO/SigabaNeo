module

public import SigabaNeo.Lib.Lattices.Research.Wall1.SlideEndpoint
import all SigabaNeo.Lib.Lattices.Research.Wall1.SlideCovolume
import Mathlib.Tactic

/-! # Exact coordinate rounds at the zero design

The zero-design lattice has orthogonal axes of lengths 1 and q. A shortest line in
any of its coordinate blocks is a signed shortest axis. This applies also to the
reciprocal lengths in the marked dual block. Thus a round marks a shortest prefix
axis, inserts a shortest missing axis and proposes deleting a longest unmarked axis.
The choice inequalities below allow all ties. -/

public section

namespace SigabaNeo.Wall1.Slide

open Matrix AttackLattice
open scoped Matrix

/-- Integral coordinates of the zero-design null lattice. -/
theorem mem_zero_design_iff {N m n q : ℕ} (σ : Fin N ≃ Fin n ⊕ Fin m)
    (z : Fin N → ℤ) : intEmb N z ∈ nullLattice (q := q) 0 σ ↔
      ∀ a, (q : ℤ) ∣ z (σ.symm (.inr a)) := by
  constructor
  · rintro ⟨w, hw, he⟩ a
    have h := congrFun (AddMonoidHom.mem_ker.mp hw) a
    have hwz := congrArg (fun x : EuclideanSpace ℝ (Fin N) ↦ x (σ.symm (.inr a))) he
    change (w _ : ℝ) = (z _ : ℝ) at hwz
    have heq : w (σ.symm (.inr a)) = z (σ.symm (.inr a)) := by exact_mod_cast hwz
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa [← heq] using h)
  · intro h
    refine ⟨z, AddMonoidHom.mem_ker.mpr ?_, rfl⟩
    ext a
    simpa only [residue_apply, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (h a)

/-- For arbitrary positive squared axis lengths, testing a shortest nonzero
integer vector against the signed coordinate units forces it onto a single axis. -/
theorem shortest_diagonal_axis {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℚ)
    (hw : ∀ i, 0 < w i) (z : ι → ℤ) (hz : z ≠ 0)
    (short : ∀ i, ∑ j, w j * (z j : ℚ)^2 ≤ w i) :
    ∃ i, (z i = 1 ∨ z i = -1) ∧ (∀ j, j ≠ i → z j = 0) ∧ ∀ j, w i ≤ w j := by
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra! hh
    exact hz (funext hh)
  have one (j : ι) (hj : z j ≠ 0) : (1 : ℚ) ≤ (z j : ℚ)^2 := by
    have hp := sq_pos_of_ne_zero hj
    exact_mod_cast (show (1 : ℤ) ≤ (z j)^2 by omega)
  let term := fun j ↦ w j * (z j : ℚ)^2
  have nn j : 0 ≤ term j := mul_nonneg (hw j).le (sq_nonneg _)
  have ti : w i ≤ term i := le_mul_of_one_le_right (hw i).le (one i hi)
  have is : term i ≤ ∑ j, term j := Finset.single_le_sum (fun j _ ↦ nn j) (Finset.mem_univ i)
  have eqi : term i = w i := le_antisymm (is.trans (short i)) ti
  have hsq : (z i : ℚ)^2 = 1 := by dsimp [term] at eqi; nlinarith [hw i]
  have hsq' : (z i)^2 = (1 : ℤ) := by exact_mod_cast hsq
  refine ⟨i, ?_, ?_, fun j ↦ ti.trans (is.trans (short j))⟩
  · rcases sq_eq_one_iff.mp hsq' with h | h <;> tauto
  · intro j hji
    have hsum := Finset.sum_erase_add Finset.univ term (Finset.mem_univ i)
    have hzero : ∑ a ∈ Finset.univ.erase i, term a = 0 := by linarith [short i, eqi]
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ ↦ nn a)).mp hzero j
      (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)
    have hc : (z j : ℚ)^2 = 0 := (mul_eq_zero.mp hj).resolve_left (hw j).ne'
    exact_mod_cast (show (z j : ℚ) = 0 by simpa using hc)

variable {ι : Type*} [DecidableEq ι]

/-- Lengths in physical integer units. U consists of the secret axes. -/
def axisLength (q : ℕ) (U : Finset ι) (i : ι) : ℕ := if i ∈ U then 1 else q

/-- The three exact choices for the orthogonal coordinate lattice. -/
structure AxisRound (q : ℕ) (U P : Finset ι) where
  mark : ι
  addAxis : ι
  dropAxis : ι
  mark_mem : mark ∈ P
  mark_min : ∀ i ∈ P, axisLength q U mark ≤ axisLength q U i
  add_out : addAxis ∉ P
  add_min : ∀ i ∉ P, axisLength q U addAxis ≤ axisLength q U i
  drop_mem : dropAxis ∈ insert addAxis P
  drop_ne : dropAxis ≠ mark
  drop_max : ∀ i ∈ insert addAxis P, i ≠ mark → axisLength q U i ≤ axisLength q U dropAxis

variable {q : ℕ} {U P : Finset ι}

/-- Finite coordinate blocks admit all three required extremizations. -/
theorem axisRound_nonempty [Fintype ι] (q : ℕ) (U P : Finset ι)
    (hp : P.Nonempty) (hm : P.card < U.card) : Nonempty (AxisRound q U P) := by
  obtain ⟨a,ha,hmin⟩ := P.exists_min_image (axisLength q U) hp
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hm
  obtain ⟨b,hb,hbmin⟩ := Pᶜ.exists_min_image (axisLength q U) ⟨i, Finset.mem_compl.mpr hi⟩
  have hba : b ≠ a := fun he ↦ Finset.mem_compl.mp hb (he ▸ ha)
  obtain ⟨c,hc,hmax⟩ := ((insert b P).erase a).exists_max_image (axisLength q U)
    ⟨b, Finset.mem_erase.mpr ⟨hba, Finset.mem_insert_self _ _⟩⟩
  exact ⟨⟨a,b,c,ha,hmin,Finset.mem_compl.mp hb,fun j hj ↦ hbmin j (Finset.mem_compl.mpr hj),
    (Finset.mem_erase.mp hc).2,(Finset.mem_erase.mp hc).1,
    fun j hj hja ↦ hmax j (Finset.mem_erase.mpr ⟨hja,hj⟩)⟩⟩

theorem AxisRound.add_unit (R : AxisRound q U P) (hq : 1 < q) (hsize : P.card < U.card) :
    R.addAxis ∈ U := by
  obtain ⟨i, hi, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card hsize
  by_contra hh
  have := R.add_min i hp
  simp [axisLength, hi, hh] at this
  omega

private theorem AxisRound.long_available (R : AxisRound q U P) (hq : 1 < q)
    (hr : 2 ≤ P.card) (hl : ¬ P ⊆ U) : ∃ i ∈ P, i ≠ R.mark ∧ i ∉ U := by
  obtain ⟨i, hip, hiu⟩ := Finset.not_subset.mp hl
  by_cases h : i = R.mark
  · subst i
    have hnot : ¬ P.card ≤ 1 := by omega
    obtain ⟨j, hj, hne⟩ : ∃ j ∈ P, j ≠ R.mark := by
      by_contra! hh
      exact hnot (Finset.card_le_one.mpr fun a ha b hb ↦ (hh a ha).trans (hh b hb).symm)
    refine ⟨j,hj,hne,fun hju ↦ ?_⟩
    have := R.mark_min j hj
    simp [axisLength, hiu, hju] at this
    omega
  · exact ⟨i,hip,h,hiu⟩

/-- The strict test stops exactly when the extension comprises all unit axes. -/
theorem AxisRound.stop_iff (R : AxisRound q U P) (hq : 1 < q) (hr : 2 ≤ P.card)
    (hsize : P.card + 1 = U.card) :
    axisLength q U R.dropAxis ≤ axisLength q U R.addAxis ↔ insert R.addAxis P = U := by
  have ha := R.add_unit hq (by omega)
  constructor
  · intro stop
    have hsub : P ⊆ U := by
      by_contra h
      obtain ⟨j,hj,hn,hju⟩ := R.long_available hq hr h
      have hh := (R.drop_max j (Finset.mem_insert_of_mem hj) hn).trans stop
      simp [axisLength, hju, ha] at hh
      omega
    exact Finset.eq_of_subset_of_card_le (Finset.insert_subset ha hsub)
      (by rw [Finset.card_insert_of_notMem R.add_out, hsize])
  · intro he
    have hm := R.drop_mem
    rw [he] at hm
    simp [axisLength, hm, ha]

/-- Every acceptance deletes one long axis from the prefix. -/
theorem AxisRound.accepted_count (R : AxisRound q U P) (hq : 1 < q) (hsize : P.card < U.card)
    (improve : axisLength q U R.addAxis < axisLength q U R.dropAxis) :
    (((insert R.addAxis P).erase R.dropAxis) \ U).card + 1 = (P \ U).card := by
  have ha := R.add_unit hq hsize
  have hd : R.dropAxis ∉ U := by intro h; simp [axisLength, h, ha] at improve
  have hdp : R.dropAxis ∈ P := (Finset.mem_insert.mp R.drop_mem).resolve_left (fun he ↦ hd (he ▸ ha))
  have he : ((insert R.addAxis P).erase R.dropAxis) \ U = (P \ U).erase R.dropAxis := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
    grind
  rw [he, Finset.card_erase_add_one (Finset.mem_sdiff.mpr ⟨hdp, hd⟩)]

/-- From the qI-first prefix, exactly one long axis disappears at every accepted
round. At the first stop the extension is the full unit-coordinate lattice.
The update hypothesis only constrains the sequence while a strict change is accepted. -/
theorem qI_first_terminal [Fintype ι] (hq : 1 < q) (U : Finset ι)
    (hr : 2 ≤ Uᶜ.card) (hsize : Uᶜ.card + 1 = U.card)
    (P : ℕ → Finset ι) (R : ∀ t, AxisRound q U (P t)) (start : P 0 = Uᶜ)
    (update : ∀ t, axisLength q U (R t).addAxis < axisLength q U (R t).dropAxis →
      P (t+1) = (insert (R t).addAxis (P t)).erase (R t).dropAxis) :
    (∀ t < Uᶜ.card, axisLength q U (R t).addAxis < axisLength q U (R t).dropAxis) ∧
    insert (R Uᶜ.card).addAxis (P Uᶜ.card) = U ∧
    (∏ i ∈ insert (R Uᶜ.card).addAxis (P Uᶜ.card), axisLength q U i) = 1 := by
  have strict (t : ℕ) (hc : (P t).card = Uᶜ.card) (hpos : 0 < (P t \ U).card) :
      axisLength q U (R t).addAxis < axisLength q U (R t).dropAxis := by
    by_contra! h
    have he := ((R t).stop_iff hq (by omega) (by omega)).mp h
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    obtain ⟨hip, hiu⟩ := Finset.mem_sdiff.mp hi
    apply hiu
    rw [← he]
    exact Finset.mem_insert_of_mem hip
  have inv (t : ℕ) (ht : t ≤ Uᶜ.card) :
      (P t).card = Uᶜ.card ∧ (P t \ U).card + t = Uᶜ.card := by
    induction t with
    | zero => simp [start, Finset.sdiff_eq_self_of_disjoint (disjoint_compl_left (a := U))]
    | succ t ih =>
      obtain ⟨hc, hrem⟩ := ih (by omega)
      have hi := strict t hc (by omega)
      have hstep := (R t).accepted_count hq (by omega) hi
      rw [update t hi]
      have hcard := Finset.card_erase_add_one (R t).drop_mem
      rw [Finset.card_insert_of_notMem (R t).add_out] at hcard
      exact ⟨by omega, by omega⟩
  refine ⟨fun t ht ↦ strict t (inv t ht.le).1 (by have := (inv t ht.le).2; omega), ?_⟩
  obtain ⟨hc, hrem⟩ := inv Uᶜ.card le_rfl
  have hstop : axisLength q U (R Uᶜ.card).dropAxis ≤ axisLength q U (R Uᶜ.card).addAxis := by
    by_contra! h
    have := (R Uᶜ.card).accepted_count hq (by omega) h
    omega
  have he := ((R Uᶜ.card).stop_iff hq (by omega) (by omega)).mp hstop
  exact ⟨he, by rw [he]; exact Finset.prod_eq_one fun i hi ↦ by simp [axisLength, hi]⟩

/-- A coordinate basis, in physical units, with the unit axes indexed by U. -/
def axisFrame {N n : ℕ} (q : ℕ) (U : Finset (Fin N)) (e : Fin n ↪ Fin N) :
    Matrix (Fin N) (Fin n) ℤ := fun i j ↦ if i = e j then axisLength q U i else 0

private theorem unit_axes_gram {N n : ℕ} (q : ℕ) (U : Finset (Fin N)) (e : Fin n ↪ Fin N)
    (he : ∀ j, e j ∈ U) : (axisFrame q U e)ᵀ * axisFrame q U e = 1 := by
  ext i j
  simp [Matrix.mul_apply, Matrix.transpose_apply, axisFrame, ite_mul, he,
    axisLength, e.injective.eq_iff, Matrix.one_apply, eq_comm]

/-- Secret-coordinate units in the labelling of the graph lattice. -/
abbrev secretAxes {N m n : ℕ} (σ : Fin N ≃ Fin n ⊕ Fin m) : Finset (Fin N) :=
  Finset.univ.image fun j : Fin n ↦ σ.symm (.inl j)

private theorem secretAxes_card {N m n : ℕ} (σ : Fin N ≃ Fin n ⊕ Fin m) :
    (secretAxes σ).card = n := by
  have hi : Function.Injective (fun j : Fin n ↦ σ.symm (.inl j)) :=
    σ.symm.injective.comp Sum.inl_injective
  simp [secretAxes, Finset.card_image_of_injective _ hi]

/-- The physical basis returned at the zero design may be any unimodular
change of the terminal coordinate basis. The certificate records the actual
three exact choices, the stopping test, and the axes of the returned frame. -/
structure ZeroTerminalBasis {N m n q : ℕ} (σ : Fin N ≃ Fin n ⊕ Fin m)
    (B : Matrix (Fin N) (Fin n) ℤ) where
  prefixAxes : Finset (Fin N)
  round : AxisRound q (secretAxes σ) prefixAxes
  rank_ge_two : 2 ≤ prefixAxes.card
  extension_rank : prefixAxes.card + 1 = n
  stop : axisLength q (secretAxes σ) round.dropAxis ≤
    axisLength q (secretAxes σ) round.addAxis
  axes : Fin n ↪ Fin N
  in_extension : ∀ j, axes j ∈ insert round.addAxis prefixAxes
  changeBasis : Matrix (Fin n) (Fin n) ℤ
  unimodular : IsUnit changeBasis.det
  basis_eq : B = axisFrame q (secretAxes σ) axes * changeBasis

/-- Package the terminal frame of any qI-first exact coordinate run, with
arbitrary axis ordering and unimodular output basis. Stopping is derived from
the updates. The caller only identifies which basis the run returned. -/
def zeroTerminalBasisOfRun {N m n q : ℕ} (σ : Fin N ≃ Fin n ⊕ Fin m)
    (hq : 1 < q) (hr : 2 ≤ m) (hn : m+1 = n) (P : ℕ → Finset (Fin N))
    (R : ∀ t, AxisRound q (secretAxes σ) (P t)) (start : P 0 = (secretAxes σ)ᶜ)
    (update : ∀ t, axisLength q (secretAxes σ) (R t).addAxis <
      axisLength q (secretAxes σ) (R t).dropAxis →
      P (t+1) = (insert (R t).addAxis (P t)).erase (R t).dropAxis)
    (e : Fin n ↪ Fin N) (axes_mem : ∀ j, e j ∈ insert (R m).addAxis (P m))
    (T : Matrix (Fin n) (Fin n) ℤ) (hT : IsUnit T.det) :
    ZeroTerminalBasis (q := q) σ (axisFrame q (secretAxes σ) e * T) := by
  have hc := secretAxes_card σ
  have hN := Fintype.card_congr σ
  simp only [Fintype.card_fin, Fintype.card_sum] at hN
  have hl : (secretAxes σ)ᶜ.card = m := by rw [Finset.card_compl, hc, Fintype.card_fin]; omega
  obtain ⟨_, he, _⟩ := qI_first_terminal hq (secretAxes σ) (by omega) (by omega) P R start update
  rw [hl] at he
  have hc' := congrArg Finset.card he
  rw [Finset.card_insert_of_notMem (R m).add_out, hc] at hc'
  exact ⟨P m, R m, by omega, hc', ((R m).stop_iff hq (by omega) (by omega)).mpr he,
    e, axes_mem, T, hT, rfl⟩

theorem ZeroTerminalBasis.volume_eq_one {N m n q : ℕ} (hq : 1 < q)
    {σ : Fin N ≃ Fin n ⊕ Fin m} {B : Matrix (Fin N) (Fin n) ℤ}
    (out : ZeroTerminalBasis (q := q) σ B) : volume (frame B) = 1 := by
  let U := secretAxes σ
  have hcard : U.card = n := secretAxes_card σ
  have hstop := (out.round.stop_iff hq out.rank_ge_two (out.extension_rank.trans hcard.symm)).mp out.stop
  change insert out.round.addAxis out.prefixAxes = U at hstop
  have hu := unit_axes_gram q U out.axes (fun j ↦ hstop ▸ out.in_extension j)
  rw [volume_eq_one_iff, out.basis_eq, gramDet_mul]
  change out.changeBasis.det^2 * ((axisFrame q U out.axes)ᵀ * axisFrame q U out.axes).det = 1
  rw [hu, Matrix.det_one, mul_one]
  rcases Int.isUnit_iff.mp out.unimodular with h | h <;> simp [h]

/-- Across designs, the only reducer hypotheses are membership of its output
columns and the exact terminal coordinate certificate at zero. All oracle ties
are allowed. The conclusion is the physical, selected-frame endpoint. -/
theorem selected_unit_iff {N m n q : ℕ} [NeZero q] [Nontrivial (ZMod q)] (hq : 1 < q)
    (σ : Fin N ≃ Fin n ⊕ Fin m)
    (out : (Fin m → Fin n → ZMod q) → Matrix (Fin N) (Fin n) ℤ)
    (mem : ∀ A j, frame (out A) j ∈ nullLattice A σ)
    (atZero : ZeroTerminalBasis (q := q) σ (out 0)) (A : Fin m → Fin n → ZMod q) :
    volume (frame (out A)) = 1 ↔ A = 0 := by
  refine ⟨zero_of_unit_extension A σ _ (mem A), ?_⟩
  rintro rfl
  exact atZero.volume_eq_one hq

theorem selected_unit_mass {N m n q : ℕ} [NeZero q] [Nontrivial (ZMod q)] (hq : 1 < q)
    (σ : Fin N ≃ Fin n ⊕ Fin m)
    (out : (Fin m → Fin n → ZMod q) → Matrix (Fin N) (Fin n) ℤ)
    (mem : ∀ A j, frame (out A) j ∈ nullLattice A σ)
    (atZero : ZeroTerminalBasis (q := q) σ (out 0)) :
    MeasureTheory.Measure.uniformOfFinset Finset.univ {A | volume (frame (out A)) = 1} =
      ((q : ENNReal) ^ (m*n))⁻¹ := by
  have he : {A | volume (frame (out A)) = 1} = ({0} : Set (Fin m → Fin n → ZMod q)) :=
    Set.ext fun A ↦ selected_unit_iff hq σ out mem atZero A
  rw [he, uniform_zero_mass]

end SigabaNeo.Wall1.Slide

#print axioms SigabaNeo.Wall1.Slide.mem_zero_design_iff
#print axioms SigabaNeo.Wall1.Slide.shortest_diagonal_axis
#print axioms SigabaNeo.Wall1.Slide.AxisRound.stop_iff
#print axioms SigabaNeo.Wall1.Slide.AxisRound.accepted_count

#print axioms SigabaNeo.Wall1.Slide.axisRound_nonempty
#print axioms SigabaNeo.Wall1.Slide.qI_first_terminal
#print axioms SigabaNeo.Wall1.Slide.zeroTerminalBasisOfRun

#print axioms SigabaNeo.Wall1.Slide.ZeroTerminalBasis.volume_eq_one
#print axioms SigabaNeo.Wall1.Slide.selected_unit_iff
#print axioms SigabaNeo.Wall1.Slide.selected_unit_mass
