module

public import SigabaNeo.Lib.Lattices.Research.Wall1.RecordedGaussianConstants
public import SigabaNeo.Lib.Lattices.Research.Wall1.OneDrawCoupling
import all SigabaNeo.Lib.Lattices.Research.Wall1.GaussianCDTBounds

/-! One-draw accuracy of the finite-precision Gaussian tables on shifted residue classes. -/

@[expose] public section
noncomputable section
namespace SigabaNeo.Wall1.CDT

open Real
open scoped ENNReal
set_option exponentiation.threshold 2048
set_option maxRecDepth 5000

/-- The first eight nonnegative representatives each have Gaussian weight at least one half. -/
private theorem retained_four {q c : ℤ} {s : ℝ} {n : ℕ} {x : ℕ → ℤ}
    (hq : 0 < q) (hwidth : 32*(q:ℝ) ≤ s) (hR : 20*s ≤ 4194303)
    (box : CosetBox q c (2^22-1) n x) :
    4 ≤ weightSum (fun i ↦ gs s (x i)) (n+1) := by
  let f (j : ℕ) : ℤ := c % q + j*q
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hs : 0 < s := by linarith
  have bounds (j : ℕ) (hj : j ∈ Finset.range 8) : 0 ≤ f j ∧ f j ≤ 8*q := by
    have hj' : (j:ℤ) ≤ 7 := by exact_mod_cast (show j ≤ 7 by simp at hj; omega)
    dsimp [f]
    constructor
    · positivity [Int.emod_nonneg c hq.ne']
    · nlinarith [Int.emod_lt_of_pos c hq, mul_le_mul_of_nonneg_right hj' hq.le]
  have sub : (Finset.range 8).image f ⊆ (Finset.range (n+1)).image x := by
    intro k hk
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨h0,h1⟩ := bounds j hj
    have h2 : 8*q ≤ (4194303:ℤ) := by exact_mod_cast (show 8*(q:ℝ) ≤ 4194303 by linarith)
    apply (box.mem_iff _).mpr
    constructor
    · norm_num
      omega
    · simp [f, Int.ModEq, Int.add_emod]
  have inj : Function.Injective f := fun i j hij ↦ by
    have := mul_right_cancel₀ hq.ne' (add_left_cancel hij : (i:ℤ)*q = j*q)
    exact_mod_cast this
  calc
    (4:ℝ) = ∑ _j ∈ Finset.range 8, (1/2:ℝ) := by norm_num
    _ ≤ ∑ j ∈ Finset.range 8, gs s (f j) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨h0,h1⟩ := bounds j hj
      have hr : 0 ≤ (f j:ℝ) := by exact_mod_cast h0
      have hr' : (f j:ℝ) ≤ 8*q := by exact_mod_cast h1
      exact gs_half hs (by rw [abs_of_nonneg hr]; linarith)
    _ = ∑ k ∈ (Finset.range 8).image f, gs s k :=
      (Finset.sum_image (f := fun k : ℤ ↦ gs s k) inj.injOn).symm
    _ ≤ ∑ k ∈ (Finset.range (n+1)).image x, gs s k :=
      Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ ↦ (gs_pos _ _).le)
    _ = _ := Finset.sum_image (f := fun k : ℤ ↦ gs s k) box.inj

/-- A uniform scalar bound for the 960-bit CDT at widths of at least 32 residue spacings. -/
theorem wide_cosetTableLaw_sdist {s : ℝ} (e : GaussianConstants s) {q : ℤ}
    (hq : 0 < q) (hwidth : 32*(q:ℝ) ≤ s) (hR : 20*s ≤ 4194303) (c : ℤ) :
    sdist (cosetTableLaw q c (2^22-1) 960 1024 e.unit₁.1 e.unit₂.1) (cosetDraw s q c) ≤
      1/(2:ℝ)^933 := by
  let S := cosetSupport q c (2^22-1)
  let n := S.card-1
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hqR : q ≤ (4194303:ℤ) := by exact_mod_cast (show (q:ℝ) ≤ 4194303 by linarith)
  have hk : c % q ∈ S := mem_cosetSupport.mpr ⟨by
    have := Int.emod_nonneg c hq.ne'
    have := Int.emod_lt_of_pos c hq
    norm_num
    omega, by simp [Int.ModEq]⟩
  have hcard : 0 < S.card := Finset.card_pos.mpr ⟨_, hk⟩
  have box := sortedLabel_box (q := q) (c := c) (R := 2^22-1)
    (show S.card = n+1 by dsimp [n]; omega)
  let δ := 1/(2:ℝ)^1024 + 2 ^ ((6.4:ℝ)-1088)
  let ε := gaussianWeightError 1024 (2^22-1) δ
  have hδ : (2:ℝ) ^ ((6.4:ℝ)-1088) ≤ 1/(2:ℝ)^1024 := by
    calc _ ≤ (2:ℝ)^(-(1024:ℝ)) := rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
         _ = _ := by rw [rpow_neg (by norm_num), one_div]
                     exact congrArg Inv.inv (rpow_natCast (2:ℝ) 1024)
  have hε : ε ≤ 1/(2:ℝ)^979 := by
    calc _ ≤ (((4194303:ℝ)+2)^2/2) * (1/2^1024 + 1/2^1024 + 1/2^1024) := by
            dsimp [ε, δ, gaussianWeightError]; gcongr
         _ ≤ _ := by norm_num
  have hε0 : 0 ≤ ε := by dsimp [ε, δ, gaussianWeightError]; positivity
  have hn := count_box box
  norm_num at hn
  have hN : ((n+1:ℕ):ℝ) ≤ 8388607 := by exact_mod_cast hn
  have hU := mul_le_mul hN hε hε0 (by norm_num)
  have h := gaussianTable_sdist_le_960 (by linarith : 0 < s) hq box e.unit₁ e.unit₂
    e.error₁ e.error₂ (hU.trans_lt (by norm_num : (8388607:ℝ)*(1/2^979) < 4))
    (retained_four hq hwidth hR box)
  apply h.trans
  change (n:ℝ) * (1/2^960 + 2*(((n+1:ℕ):ℝ)*ε)/4) + cosetTailBound s q 4194303 ≤ _
  have hn' : (n:ℝ) ≤ 8388607 := by exact_mod_cast (show n ≤ 8388607 by omega)
  calc _ ≤ 8388607 * (1/2^960 + 2*(8388607*(1/(2:ℝ)^979))/4) + 1/(2:ℝ)^1100 := by
          apply add_le_add _ (tail_at_radius hq1 (by linarith) hR)
          gcongr
       _ ≤ _ := by norm_num

variable {t r : ℕ}
abbrev Vec (n : ℕ) := Fin n → ℤ

/-- Joint mass in draw order (tail, head). A head residue may depend on the whole tail. -/
def residueLaw (A : KleinDraws) (w : Vec t → Vec r) (y : Vec t × Vec r) : ℝ :=
  (∏ j, A.tail (y.1 j)) * ∏ i, A.head (w y.1 i) (y.2 i)

theorem residue_nonneg (A : KleinDraws) (w : Vec t → Vec r) (y) :
    0 ≤ residueLaw A w y :=
  mul_nonneg (Finset.prod_nonneg fun _ _ ↦ A.tail_nonneg _)
    (Finset.prod_nonneg fun _ _ ↦ A.head_nonneg _ _)

theorem residue_hasSum (A : KleinDraws) (w : Vec t → Vec r) : HasSum (residueLaw A w) 1 :=
  hasSum_bind (P₁ := fun u : Vec t ↦ ∏ j, A.tail (u j))
    (K := fun u (v : Vec r) ↦ ∏ i, A.head (w u i) (v i))
    (fun _ ↦ Finset.prod_nonneg fun _ _ ↦ A.tail_nonneg _)
    (by simpa using hasSum_pi_prod (fun (_ : Fin t) ↦ A.tail_nonneg) (fun _ ↦ A.tail_hasSum))
    (fun _ _ ↦ Finset.prod_nonneg fun _ _ ↦ A.head_nonneg _ _)
    (fun u ↦ by
      simpa using hasSum_pi_prod (fun i ↦ A.head_nonneg (w u i)) (fun i ↦ A.head_hasSum (w u i)))

private theorem product_sdist {n : ℕ} {P Q : Fin n → ℤ → ℝ} {η : ℝ}
    (hp : ∀ i k, 0 ≤ P i k) (hp' : ∀ i, HasSum (P i) 1)
    (hq : ∀ i k, 0 ≤ Q i k) (hq' : ∀ i, HasSum (Q i) 1)
    (hε : ∀ i, sdist (P i) (Q i) ≤ η) :
    sdist (fun x : Vec n ↦ ∏ i, P i (x i)) (fun x ↦ ∏ i, Q i (x i)) ≤ n * η := by
  let extend (f : Fin n → ℤ → ℝ) (m : ℕ) := if h : m < n then f ⟨m,h⟩ else dg1 1 0
  have hn (f : Fin n → ℤ → ℝ) (h0 : ∀ i k, 0 ≤ f i k) (m k) : 0 ≤ extend f m k := by
    dsimp [extend]; split <;> first | apply h0 | exact dg1_nonneg one_pos _ _
  have hm (f : Fin n → ℤ → ℝ) (h1 : ∀ i, HasSum (f i) 1) (m) : HasSum (extend f m) 1 := by
    dsimp [extend]; split <;> first | apply h1 | exact dg1_hasSum one_pos _
  have h := sdist_pi_le (hn P hp) (hm P hp') (hn Q hq) (hm Q hq') n
  simp only [extend, Fin.is_lt, dite_true, Fin.eta] at h
  apply h.trans
  calc _ ≤ ∑ _m ∈ Finset.range n, η := Finset.sum_le_sum fun m hm ↦ by
             simp only [dite_eq_left (Finset.mem_range.mp hm)]
             apply hε
       _ = _ := by simp

private theorem residue_sdist (A B : KleinDraws) (w : Vec t → Vec r) {η : ℝ}
    (ht : sdist A.tail B.tail ≤ η) (hh : ∀ c, sdist (A.head c) (B.head c) ≤ η) :
    sdist (residueLaw A w) (residueLaw B w) ≤ (t+r:ℝ)*η := by
  let p (D : KleinDraws) (u : Vec t) := ∏ j, D.tail (u j)
  let k (D : KleinDraws) (u : Vec t) (v : Vec r) := ∏ i, D.head (w u i) (v i)
  have hp (D : KleinDraws) (u) : 0 ≤ p D u := Finset.prod_nonneg fun _ _ ↦ D.tail_nonneg _
  have hp' (D : KleinDraws) : HasSum (p D) 1 := by
    simpa [p] using hasSum_pi_prod (fun (_ : Fin t) ↦ D.tail_nonneg) (fun _ ↦ D.tail_hasSum)
  have hk (D : KleinDraws) (u v) : 0 ≤ k D u v := Finset.prod_nonneg fun _ _ ↦ D.head_nonneg _ _
  have hk' (D : KleinDraws) (u) : HasSum (k D u) 1 := by
    simpa [k] using hasSum_pi_prod (fun i ↦ D.head_nonneg (w u i)) (fun i ↦ D.head_hasSum (w u i))
  have ht' : sdist (p A) (p B) ≤ t*η := product_sdist (fun _ ↦ A.tail_nonneg)
    (fun _ ↦ A.tail_hasSum) (fun _ ↦ B.tail_nonneg) (fun _ ↦ B.tail_hasSum) (fun _ ↦ ht)
  have hh' (u) : sdist (k A u) (k B u) ≤ r*η := product_sdist (fun i ↦ A.head_nonneg (w u i))
    (fun i ↦ A.head_hasSum (w u i)) (fun i ↦ B.head_nonneg (w u i))
    (fun i ↦ B.head_hasSum (w u i)) (fun i ↦ hh (w u i))
  exact (sdist_bind_le (hp A) (hp' A) (hp B) (hp' B) (hk A) (hk' A) (hk B) (hk' B) hh').trans
    (by simpa [add_mul] using add_le_add_right ht' ((r:ℝ)*η))

/-- The unnormalized Gaussian on the prescribed residue classes, in residual coordinates. -/
def residueWeight (s : ℝ) (q : ℤ) (w : Vec t → Vec r) (y : Vec t × Vec r) : ℝ :=
  if ∀ i, y.2 i ≡ w y.1 i [ZMOD q] then rhoL s y else 0

/-- Exact shifted Gaussian, normalized by the sum over the full infinite support. -/
def residueGaussian (s : ℝ) (q : ℤ) (w : Vec t → Vec r) (y : Vec t × Vec r) : ℝ :=
  residueWeight s q w y / ∑' z, residueWeight s q w z

private theorem corrected_weight {s : ℝ} {q : ℤ} (hs : 0 < s) (hq : 0 < q)
    (w : Vec t → Vec r) (y : Vec t × Vec r) :
    residueWeight s q w y =
      (residueLaw (exactKleinDraws hs hq.ne') w y * kleinWeight s q (fun i ↦ w y.1 i)) *
        (theta1 s 0 ^ t * (s/q)^r) := by
  classical
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hθ := theta1_zero_pos hs
  have hprod : 0 < ∏ i, thetaQ s q (w y.1 i) :=
    Finset.prod_pos fun _ _ ↦ thetaQ_pos hs hq'.ne' _
  simp only [residueWeight, residueLaw, exactKleinDraws, dg1, sub_zero, neg_zero, cosetDraw,
    Finset.prod_ite_zero, Finset.mem_univ, forall_const, kleinWeight_eq, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, rhoL, rhoVec]
  split_ifs
  · field_simp [hprod.ne', hθ.ne', hs.ne', hq'.ne']
  · simp

/-- Normalization and the change of marginal when the head normalizers vary with the tail. -/
private theorem residue_tilt {s : ℝ} {q : ℤ} (hs : 0 < s) (hq : 0 < q)
    (w : Vec t → Vec r) (hτ : tau (s/q) < 1) :
    HasSum (residueGaussian s q w) 1 ∧
      sdist (residueLaw (exactKleinDraws hs hq.ne') w) (residueGaussian s q w) ≤
        (1/2) * (((1+tau (s/q))/(1-tau (s/q)))^r-1) := by
  let A := exactKleinDraws hs hq.ne'
  let K := residueLaw A w
  let g (y : Vec t × Vec r) := kleinWeight s q (fun i ↦ w y.1 i)
  let Z := ∑' y, K y*g y
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hg (y : Vec t × Vec r) := kleinWeight_mem hs hq' hτ (fun i ↦ (w (Prod.fst y) i : ℝ))
  have hg0 (y) : 0 < g y := (pow_pos (sub_pos.mpr hτ) r).trans_le (hg y).1
  have hK : HasSum K 1 := residue_hasSum A w
  have hK0 := residue_nonneg A w
  have hkg : Summable (fun y ↦ K y * g y) := Summable.of_nonneg_of_le
    (fun y ↦ mul_nonneg (hK0 y) (hg0 y).le)
    (fun y ↦ mul_le_mul_of_nonneg_left (hg y).2 (hK0 y)) (hK.summable.mul_right _)
  have hZ : 0 < Z := by
    obtain ⟨y,hy⟩ : ∃ y, 0 < K y := by
      by_contra! hn
      have hz : K = fun _ ↦ 0 := funext fun y ↦ le_antisymm (hn y) (hK0 y)
      have h := hK.tsum_eq
      simp [hz] at h
    exact hkg.tsum_pos (fun y ↦ mul_nonneg (hK0 y) (hg0 y).le) y (mul_pos hy (hg0 y))
  have hC : 0 < theta1 s 0 ^ t * (s/q)^r :=
    mul_pos (pow_pos (theta1_zero_pos hs) _) (pow_pos (div_pos hs hq') _)
  have hD (y) : residueGaussian s q w y = K y*g y/Z := by
    simp only [residueGaussian, corrected_weight hs hq w, tsum_mul_right]
    exact mul_div_mul_right _ _ hC.ne'
  constructor
  · apply HasSum.congr_fun _ hD
    have hzsum : HasSum (fun y ↦ K y*g y) Z := hkg.hasSum
    simpa only [div_self hZ.ne'] using hzsum.div_const Z
  · calc sdist K (residueGaussian s q w) = (1/2)*∑' y, K y*|g y/Z-1| := by
           unfold sdist
           congr 1
           apply tsum_congr
           intro y
           rw [hD, abs_sub_comm, show K y*g y/Z-K y = K y*(g y/Z-1) by ring,
             abs_mul, abs_of_nonneg (hK0 y)]
         _ ≤ _ := klein_sd_le hs hq' hτ hK0 hK (fun y i ↦ (w y.1 i:ℝ))

/-- Convert the half-L1 distance of normalized real masses to the one-sided excess. -/
theorem excess_eq_sdist {α : Type*} {P Q : α → ℝ} (hp : HasSum P 1) (hq : HasSum Q 1) :
    ∑' x, (P x - Q x)⁺ = sdist P Q := by
  have h := (hp.sub hq).add (summable_abs_sub hp.summable hq.summable).hasSum
  have h' := h.div_const 2
  have he (x) : (P x - Q x)⁺ = ((P x-Q x) + |P x-Q x|)/2 := by
    rw [add_abs_eq_two_nsmul_posPart, two_nsmul]; ring
  rw [tsum_congr he, h'.tsum_eq, sdist]
  ring

/-- At the stated precision and smoothing, any residue rule works, including affine shifts. -/
theorem table_residue_excess {s : ℝ} {q : ℤ} (e : GaussianConstants s) (hq : 0 < q)
    (hw : 32*(q:ℝ) ≤ s) (hR : 20*s ≤ 4194303) (hτ : tau (s/q) ≤ 1/(2:ℝ)^1024)
    (w : Vec t → Vec r) (hd : t+r ≤ 638) :
    let A := tableDraws q (2^22-1) 960 1024 e.unit₁.1 e.unit₂.1
    ∑' y, (residueLaw A w y - residueGaussian s q w y)⁺ ≤ 1/(2:ℝ)^923 := by
  intro A
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hs : 0 < s := by linarith
  let B := exactKleinDraws hs hq.ne'
  have ht : sdist A.tail B.tail ≤ 1/(2:ℝ)^933 := by
    rw [show B.tail = cosetDraw s 1 0 from (cosetDraw_one_zero s).symm]
    exact wide_cosetTableLaw_sdist e (by decide) (by norm_num; linarith) hR 0
  have hh := wide_cosetTableLaw_sdist e hq hw hR
  have hK := residue_sdist A B w ht hh
  obtain ⟨hD,hbias⟩ := residue_tilt hs hq w (hτ.trans_lt (by norm_num))
  have hr : (r:ℝ) ≤ 638 := by exact_mod_cast (show r ≤ 638 by omega)
  have hdim : (t:ℝ)+r ≤ 638 := by exact_mod_cast hd
  have hb := half_ratio_pow_sub_one_le (tau_nonneg _) hτ (by norm_num)
    (r := r) (by calc (r:ℝ)*(1/2^1024) ≤ 638*(1/2^1024) := by gcongr
                      _ ≤ 1/1000 := by norm_num)
  rw [excess_eq_sdist (residue_hasSum A w) hD]
  apply (sdist_triangle (residue_hasSum A w).summable (residue_hasSum B w).summable
    hD.summable).trans
  calc _ ≤ ((t:ℝ)+r)*(1/2^933) + (101/100)*r*(1/2^1024) := add_le_add hK (hbias.trans hb)
       _ ≤ 638*(1/2^933) + (101/100)*638*(1/2^1024) := by gcongr
       _ ≤ _ := by norm_num

/-- Run zero uses the rank-647 width even for the smaller affine graph. -/
private theorem runZero_width :
    32*3329 ≤ recordedWidth 647 0 ∧ tau (recordedWidth 647 0 / 3329) ≤ 1/(2:ℝ)^1024 := by
  let v := sqrt (647 * log 1298 / π)
  have hv : recordedWidth 647 0 = 3329*v := by norm_num [recordedWidth, v]
  have hl : 10 * log 2 ≤ log 1298 := by
    simpa only [log_pow, Nat.cast_ofNat] using
      log_le_log (by positivity : (0:ℝ) < 2^10) (by norm_num : (2:ℝ)^10 ≤ 1298)
  have hv32 : 32 ≤ v := by
    unfold v
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    apply (le_div_iff₀ pi_pos).mpr
    linarith [log_two_gt_d9, pi_lt_four]
  rw [hv, show 3329*v/3329 = v by ring]
  refine ⟨by linarith, (tau_le (by linarith : 0 < v)).trans ?_⟩
  have hpow : π*v^2 = 647*log 1298 := by
    dsimp [v]
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hlarge : 1026 * log 2 ≤ π*v^2 := by rw [hpow]; linarith [log_two_gt_d9]
  have hdec : exp (-(π*v^2)) ≤ 1/(2:ℝ)^1026 := by
    rw [exp_neg, one_div]
    apply inv_anti₀ (by positivity)
    rw [← Real.exp_log (by positivity : (0:ℝ) < 2^1026), exp_le_exp, log_pow]
    exact hlarge
  have hdec' : exp (-3*(π*v^2)) ≤ 1/2 := by
    calc _ ≤ exp (-(π*v^2)) := exp_le_exp.mpr (by linarith [log_two_gt_d9])
         _ ≤ _ := hdec.trans (by norm_num)
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- The actual rank-647 constants and tables at run zero. -/
def runZeroDraws : KleinDraws :=
  let e := recordedGaussianConstants (d := 647) (j := 0) (Or.inr rfl) (by decide)
  tableDraws 3329 (2^22-1) 960 1024 e.unit₁.1 e.unit₂.1

/-- No accuracy hypotheses: the exact affine Gaussian and the finite table law for any A,b. -/
theorem shifted_table_excess (M : Matrix (Fin 127) (Fin 511) ℤ) (b : Vec 127) :
    let w := fun u ↦ M.mulVec u - b
    ∑' y, (residueLaw runZeroDraws w y - residueGaussian (recordedWidth 647 0) 3329 w y)⁺ ≤
      1/(2:ℝ)^923 :=
  table_residue_excess (recordedGaussianConstants (Or.inr rfl) (by decide))
    (by decide) (by simpa using runZero_width.1)
    (recordedWidth_bounds (Or.inr rfl) (by decide)).2 (by simpa using runZero_width.2) _ (by decide)

/-- Form a PMF from nonnegative, normalized real masses. -/
def pmfOfMass {α : Type*} (p : α → ℝ) (hp : ∀ x, 0 ≤ p x) (h : HasSum p 1) : PMF α :=
  ⟨fun x ↦ ENNReal.ofReal (p x), CompleteLattice.summable.hasSum_iff.mpr (by
    rw [← ENNReal.ofReal_tsum_of_nonneg hp h.summable, h.tsum_eq, ENNReal.ofReal_one])⟩

/-- The table output as a PMF on tail and head coordinates. -/
def runZeroTablePMF (w : Vec t → Vec r) : PMF (Vec t × Vec r) :=
  pmfOfMass _ (residue_nonneg runZeroDraws w) (residue_hasSum runZeroDraws w)

theorem residueGaussian_nonneg (s : ℝ) (q : ℤ) (w : Vec t → Vec r) (y) :
    0 ≤ residueGaussian s q w y := by
  have hw (z) : 0 ≤ residueWeight s q w z := by
    unfold residueWeight rhoL
    split
    · exact mul_nonneg (rhoVec_pos _ _).le (rhoVec_pos _ _).le
    · rfl
  exact div_nonneg (hw y) (tsum_nonneg hw)

theorem runZeroGaussian_hasSum (w : Vec t → Vec r) :
    HasSum (residueGaussian (recordedWidth 647 0) 3329 w) 1 := by
  have hτ : tau (recordedWidth 647 0/(3329:ℤ)) < 1 := runZero_width.2.trans_lt (by norm_num)
  have hs : 0 < recordedWidth 647 0 := (by norm_num : (0:ℝ) < 32*3329).trans_le runZero_width.1
  exact (residue_tilt hs (by decide) w hτ).1

/-- The normalized Gaussian as a PMF in the same residual coordinates. -/
def runZeroGaussianPMF (w : Vec t → Vec r) : PMF (Vec t × Vec r) :=
  pmfOfMass _ (residueGaussian_nonneg _ _ w) (runZeroGaussian_hasSum w)

/-- ENNReal subtraction is the positive part, as used in the one-draw coupling theorem. -/
theorem shifted_table_pmf_excess (M : Matrix (Fin 127) (Fin 511) ℤ) (b : Vec 127) :
    let w := fun u ↦ M.mulVec u - b
    ∑' y, (runZeroTablePMF w y - runZeroGaussianPMF w y) ≤ ENNReal.ofReal (1/(2:ℝ)^923) := by
  intro w
  let P := runZeroTablePMF w
  let Q := runZeroGaussianPMF w
  let p := residueLaw runZeroDraws w
  let q := residueGaussian (recordedWidth 647 0) 3329 w
  have hq (y) : 0 ≤ q y := residueGaussian_nonneg _ _ w y
  have hm (y) : P y - Q y = ENNReal.ofReal ((p y - q y)⁺) := by
    change ENNReal.ofReal (p y) - ENNReal.ofReal (q y) = _
    rw [← ENNReal.ofReal_sub _ (hq y)]
    simp only [posPart_def, ENNReal.ofReal_max, ENNReal.ofReal_zero]
    exact (max_eq_left (show 0 ≤ ENNReal.ofReal (p y - q y) from bot_le)).symm
  have hs : Summable (fun y ↦ (p y-q y)⁺) := Summable.of_nonneg_of_le (fun _ ↦ posPart_nonneg _)
    (fun y ↦ sup_le (sub_le_self _ (hq y)) (residue_nonneg _ _ y)) (residue_hasSum _ w).summable
  rw [tsum_congr hm, ← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ posPart_nonneg _) hs]
  exact ENNReal.ofReal_le_ofReal (shifted_table_excess M b)

/-- A coupling attaining the excess for the two concrete coordinate PMFs. -/
theorem shifted_table_coupling (M : Matrix (Fin 127) (Fin 511) ℤ) (b : Vec 127) :
    let w := fun u ↦ M.mulVec u - b
    ∃ J : PMF ((Vec 511 × Vec 127) × (Vec 511 × Vec 127)),
      J.map Prod.fst = runZeroTablePMF w ∧ J.map Prod.snd = runZeroGaussianPMF w ∧
        J.toOuterMeasure {z | z.1 ≠ z.2} ≤ ENNReal.ofReal (1/(2:ℝ)^923) := by
  intro w
  obtain ⟨J,hP,hQ,h⟩ := exists_coupling_of_excess (runZeroTablePMF w) (runZeroGaussianPMF w)
  exact ⟨J,hP,hQ,h.le.trans (shifted_table_pmf_excess M b)⟩

end SigabaNeo.Wall1.CDT

#print axioms SigabaNeo.Wall1.CDT.table_residue_excess
#print axioms SigabaNeo.Wall1.CDT.shifted_table_excess
#print axioms SigabaNeo.Wall1.CDT.shifted_table_pmf_excess
#print axioms SigabaNeo.Wall1.CDT.shifted_table_coupling
