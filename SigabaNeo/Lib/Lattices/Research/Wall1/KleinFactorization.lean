module

public import SigabaNeo.Lib.Lattices.Research.Wall1.GaussianSmoothing1D
import all SigabaNeo.Lib.Lattices.Research.Wall1.GaussianSmoothing1D

/-!
# Klein's sampler versus `D_{L,s}` on `L_M` (Wall 1, Part 141 Lemmas 1–2)

* `hasSum_pi_prod`: for nonnegative `f i` with `HasSum (f i) (S i)`,
  `∑_{x : Fin r → β} ∏ᵢ f i (x i) = ∏ᵢ S i`.
* `latticeM q M = {(h,u) ∈ ℤ^r × ℤ^t : h ≡ M u (mod q)}` and its parametrization
  `paramM q M (u, k) = (q k + M u, u)` (injective with range `latticeM q M`).
* `discGauss s q M` is `D_{L,s}` (`∝ exp (-π ‖x‖² / s²)` on `L_M`), `kleinLaw s q M` is the Klein law
  `K(h,u) = p(u) ∏ᵢ exp (-π hᵢ² / s²) / ρ_s(qℤ + (M u)ᵢ)` with `p = pTail s = D_{ℤ,s}^{⊗t}`.
* `pTail_hasSum`, `discGauss_hasSum`, `kleinLaw_hasSum`: all three are probabilities.
* `discGauss_eq_kleinLaw_mul`: `D(y) = K(y) · g(u) / E_p[g]` with `g = kleinWeight`.
* `sdist_kleinLaw_discGauss_le`: `SD(K, D_{L,s}) ≤ ½ (((1+τ)/(1-τ))^r - 1)`, `τ = τ(s/q)`.
* `sdist_kleinLaw_discGauss_lt_of_ge`: at `s/q ≥ 38.39`, `r ≤ 512`: `SD < 2^{-6669}`;
  `sdist_kleinLaw_discGauss_lt_of_ge_134`: `r ≤ 134` gives `SD < 2^{-6671}`.
-/

@[expose] public section

namespace SigabaNeo.Wall1

open Real Function Matrix

noncomputable section

/-! ### Products of sums over `Fin r → β` -/

/-- **Product of nonnegative sums.** If `f i ≥ 0` and `HasSum (f i) (S i)` for every `i : Fin r`,
then `∑_{x : Fin r → β} ∏ᵢ f i (x i) = ∏ᵢ S i`. -/
theorem hasSum_pi_prod {β : Type*} : ∀ {r : ℕ} {f : Fin r → β → ℝ} {S : Fin r → ℝ},
    (∀ i b, 0 ≤ f i b) → (∀ i, HasSum (f i) (S i)) →
      HasSum (fun x : Fin r → β ↦ ∏ i, f i (x i)) (∏ i, S i)
  | 0, f, S, _, _ => by
    simp
  | n + 1, f, S, h0, hS => by
    have ih := hasSum_pi_prod (f := fun i : Fin n ↦ f i.succ) (S := fun i ↦ S i.succ)
      (fun i b ↦ h0 _ b) (fun i ↦ hS _)
    have hn0 : ∀ y : Fin n → β, 0 ≤ ∏ i : Fin n, f i.succ (y i) :=
      fun y ↦ Finset.prod_nonneg fun i _ ↦ h0 _ _
    have hmul := (hS 0).mul ih
      ((hS 0).summable.mul_of_nonneg ih.summable (fun b ↦ h0 0 b) hn0)
    rw [Fin.prod_univ_succ]
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) ↦ β).hasSum_iff]
    convert hmul using 2 with x
    simp [Fin.consEquiv, Fin.prod_univ_succ]

/-- Fiberwise summation of a nonnegative function on a product. -/
theorem hasSum_prod_of_nonneg {α β : Type*} {F : α × β → ℝ} {G : α → ℝ} {S : ℝ}
    (hF : 0 ≤ F) (hfib : ∀ a, HasSum (fun b ↦ F (a, b)) (G a)) (hG : HasSum G S) :
    HasSum F S := by
  have hsum : Summable F := (summable_prod_of_nonneg hF).2
    ⟨fun a ↦ (hfib a).summable, by simpa only [(hfib _).tsum_eq] using hG.summable⟩
  have h := hsum.hasSum.prod_fiberwise fun a ↦ (hfib a).summable.hasSum
  have : ∑' p, F p = S := by
    have := h.unique (by simpa only [(hfib _).tsum_eq] using hG)
    exact this
  rw [← this]; exact hsum.hasSum

/-! ### One-dimensional Gaussians -/

/-- The one-dimensional Gaussian weight `ρ_s(x) = exp (-π x² / s²)`. -/
def gs (s x : ℝ) : ℝ := Real.exp (-π * x ^ 2 / s ^ 2)

theorem gs_pos (s x : ℝ) : 0 < gs s x := Real.exp_pos _

/-- `k ↦ ρ_s(q k + c)` sums to `thetaQ s q c = ρ_s(qℤ + c)`. -/
theorem hasSum_coset {s q : ℝ} (hs : 0 < s) (hq : q ≠ 0) (c : ℝ) :
    HasSum (fun k : ℤ ↦ gs s (q * k + c)) (thetaQ s q c) := by
  have ha : 0 < π * q ^ 2 / (2 * s ^ 2) := by positivity
  have hsum : Summable (fun k : ℤ ↦ gs s (q * k + c)) := by
    refine Summable.of_nonneg_of_le (fun _ ↦ (gs_pos _ _).le) (fun k ↦ ?_)
      ((summable_int_gauss ha).mul_left (Real.exp (π * c ^ 2 / s ^ 2)))
    rw [gs, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hs2 : 0 < s ^ 2 := by positivity
    have key : (q * k) ^ 2 ≤ 2 * (q * k + c) ^ 2 + 2 * c ^ 2 := by
      nlinarith [sq_nonneg (q * k + 2 * c)]
    rw [show -π * (q * k + c) ^ 2 / s ^ 2 = -(π / s ^ 2) * (q * k + c) ^ 2 by ring,
      show π * c ^ 2 / s ^ 2 + -(π * q ^ 2 / (2 * s ^ 2)) * (k : ℝ) ^ 2 =
        (π / s ^ 2) * (c ^ 2 - (q * k) ^ 2 / 2) by ring]
    have : 0 < π / s ^ 2 := by positivity
    nlinarith
  exact hsum.hasSum

theorem theta1_zero_eq (s : ℝ) : theta1 s 0 = thetaQ s 1 0 := by
  unfold theta1 thetaQ; simp

/-- `∑_{k ∈ ℤ} ρ_s(k) = ρ_s(ℤ) = theta1 s 0`. -/
theorem hasSum_gs_int {s : ℝ} (hs : 0 < s) : HasSum (fun k : ℤ ↦ gs s k) (theta1 s 0) := by
  rw [theta1_zero_eq]; simpa using hasSum_coset hs one_ne_zero 0

theorem thetaQ_pos {s q : ℝ} (hs : 0 < s) (hq : q ≠ 0) (c : ℝ) : 0 < thetaQ s q c := by
  rw [← (hasSum_coset hs hq c).tsum_eq]
  exact (hasSum_coset hs hq c).summable.tsum_pos (fun _ ↦ (gs_pos _ _).le) 0 (gs_pos _ _)

theorem theta1_zero_pos {s : ℝ} (hs : 0 < s) : 0 < theta1 s 0 := by
  rw [theta1_zero_eq]; exact thetaQ_pos hs one_ne_zero 0

/-! ### The lattice `L_M` and its parametrization -/

variable {r t : ℕ}

/-- `L_M = {(h, u) ∈ ℤ^r × ℤ^t : h ≡ M u (mod q)}`. -/
def latticeM (q : ℤ) (M : Matrix (Fin r) (Fin t) ℤ) : Set ((Fin r → ℤ) × (Fin t → ℤ)) :=
  {y | ∀ i, y.1 i ≡ (M *ᵥ y.2) i [ZMOD q]}

/-- The parametrization `(u, k) ↦ (q k + M u, u)` of `L_M`. -/
def paramM (q : ℤ) (M : Matrix (Fin r) (Fin t) ℤ) (p : (Fin t → ℤ) × (Fin r → ℤ)) :
    (Fin r → ℤ) × (Fin t → ℤ) :=
  (fun i ↦ q * p.2 i + (M *ᵥ p.1) i, p.1)

theorem paramM_injective {q : ℤ} (hq : q ≠ 0) (M : Matrix (Fin r) (Fin t) ℤ) :
    Injective (paramM q M) := by
  rintro ⟨u, k⟩ ⟨u', k'⟩ h
  simp only [paramM, Prod.mk.injEq] at h
  obtain ⟨h1, rfl⟩ := h
  refine Prod.ext rfl (funext fun i ↦ ?_)
  have := congrFun h1 i
  simp only [add_left_inj] at this
  exact mul_left_cancel₀ hq this

theorem range_paramM (q : ℤ) (M : Matrix (Fin r) (Fin t) ℤ) :
    Set.range (paramM q M) = latticeM q M := by
  ext ⟨h, u⟩
  constructor
  · rintro ⟨⟨u', k⟩, he⟩
    simp only [paramM, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    intro i
    simp only
    exact (Int.modEq_iff_dvd.mpr ⟨-k i, by ring⟩)
  · intro hm
    refine ⟨(u, fun i ↦ (h i - (M *ᵥ u) i) / q), ?_⟩
    simp only [paramM, Prod.mk.injEq, and_true]
    funext i
    have hd : q ∣ h i - (M *ᵥ u) i := (hm i).symm.dvd
    rw [Int.mul_ediv_cancel' hd]; ring

/-! ### Gaussian weights on vectors -/

/-- `ρ_s(v) = ∏ᵢ exp (-π vᵢ² / s²)` for an integer vector. -/
def rhoVec {n : ℕ} (s : ℝ) (v : Fin n → ℤ) : ℝ := ∏ i, gs s (v i)

theorem rhoVec_eq {n : ℕ} (s : ℝ) (v : Fin n → ℤ) :
    rhoVec s v = Real.exp (-π * (∑ i, ((v i : ℝ)) ^ 2) / s ^ 2) := by
  rw [rhoVec, Finset.mul_sum, Finset.sum_div, Real.exp_sum]; rfl

theorem rhoVec_pos {n : ℕ} (s : ℝ) (v : Fin n → ℤ) : 0 < rhoVec s v :=
  Finset.prod_pos fun _ _ ↦ gs_pos _ _

theorem hasSum_rhoVec {n : ℕ} {s : ℝ} (hs : 0 < s) :
    HasSum (fun v : Fin n → ℤ ↦ rhoVec s v) (theta1 s 0 ^ n) := by
  have := hasSum_pi_prod (f := fun (_ : Fin n) (k : ℤ) ↦ gs s k) (S := fun _ ↦ theta1 s 0)
    (fun _ _ ↦ (gs_pos _ _).le) (fun _ ↦ hasSum_gs_int hs)
  simpa [rhoVec] using this

/-- `ρ_s(h, u) = exp (-π ‖(h, u)‖² / s²)`. -/
def rhoL (s : ℝ) (y : (Fin r → ℤ) × (Fin t → ℤ)) : ℝ := rhoVec s y.1 * rhoVec s y.2

theorem rhoL_eq (s : ℝ) (y : (Fin r → ℤ) × (Fin t → ℤ)) :
    rhoL s y = Real.exp (-π * (∑ i, ((y.1 i : ℝ)) ^ 2 + ∑ j, ((y.2 j : ℝ)) ^ 2) / s ^ 2) := by
  rw [rhoL, rhoVec_eq, rhoVec_eq, ← Real.exp_add]; congr 1; ring

/-! ### The three laws -/

/-- The real centres `w(u) = M u`. -/
def centre (M : Matrix (Fin r) (Fin t) ℤ) (u : Fin t → ℤ) : Fin r → ℝ :=
  fun i ↦ ((M *ᵥ u) i : ℝ)

/-- The normalizer `ρ_s(L_M) = ∑_{y ∈ L_M} ρ_s(y)`. -/
def zL (s : ℝ) (q : ℤ) (M : Matrix (Fin r) (Fin t) ℤ) : ℝ :=
  ∑' y, (latticeM q M).indicator (rhoL s) y

/-- The discrete Gaussian `D_{L_M,s}(y) = 1_{L_M}(y) ρ_s(y) / ρ_s(L_M)`. -/
def discGauss (s : ℝ) (q : ℤ) (M : Matrix (Fin r) (Fin t) ℤ)
    (y : (Fin r → ℤ) × (Fin t → ℤ)) : ℝ :=
  (latticeM q M).indicator (rhoL s) y / zL s q M

/-- The tail law `p = D_{ℤ,s}^{⊗t}`, `p(u) = ∏ⱼ ρ_s(uⱼ) / ρ_s(ℤ)`. -/
def pTail (s : ℝ) (u : Fin t → ℤ) : ℝ := ∏ j, gs s (u j) / theta1 s 0

/-- The Klein law `K(h,u) = 1_{L_M}(h,u) · p(u) · ∏ᵢ ρ_s(hᵢ) / ρ_s(qℤ + (M u)ᵢ)`. -/
def kleinLaw (s : ℝ) (q : ℤ) (M : Matrix (Fin r) (Fin t) ℤ)
    (y : (Fin r → ℤ) × (Fin t → ℤ)) : ℝ :=
  (latticeM q M).indicator
    (fun y ↦ pTail s y.2 * ∏ i, gs s (y.1 i) / thetaQ s q (centre M y.2 i)) y

/-- `E_p[g]` for the Klein weight `g(u) = kleinWeight s q (M u)`. -/
def kleinMean (s : ℝ) (q : ℤ) (M : Matrix (Fin r) (Fin t) ℤ) : ℝ :=
  ∑' u, pTail s u * kleinWeight s q (centre M u)

/-- Statistical distance `½ ∑ |P - Q|`. -/
def sdist {α : Type*} (P Q : α → ℝ) : ℝ := (1 / 2) * ∑' y, |P y - Q y|

/-! ### Sums over the parametrization -/

/-- Transfer a sum on the parameter space to a sum on `ℤ^r × ℤ^t`. -/
theorem hasSum_of_paramM {q : ℤ} (hq : q ≠ 0) {M : Matrix (Fin r) (Fin t) ℤ}
    {F : (Fin r → ℤ) × (Fin t → ℤ) → ℝ} {S : ℝ} (hF : ∀ y, y ∉ latticeM q M → F y = 0)
    (h : HasSum (fun p ↦ F (paramM q M p)) S) : HasSum F S := by
  refine ((paramM_injective hq M).hasSum_iff fun y hy ↦ hF y ?_).mp h
  rwa [range_paramM] at hy

theorem paramM_mem (q : ℤ) (M : Matrix (Fin r) (Fin t) ℤ) (p) : paramM q M p ∈ latticeM q M := by
  rw [← range_paramM]; exact ⟨p, rfl⟩

theorem paramM_fst_cast (q : ℤ) (M : Matrix (Fin r) (Fin t) ℤ) (p : (Fin t → ℤ) × (Fin r → ℤ))
    (i : Fin r) : ((paramM q M p).1 i : ℝ) = (q : ℝ) * (p.2 i : ℝ) + centre M p.1 i := by
  simp [paramM, centre]

theorem hasSum_coset_vec {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : q ≠ 0)
    (M : Matrix (Fin r) (Fin t) ℤ) (u : Fin t → ℤ) :
    HasSum (fun k : Fin r → ℤ ↦ ∏ i, gs s ((q : ℝ) * k i + centre M u i))
      (∏ i, thetaQ s q (centre M u i)) :=
  hasSum_pi_prod (f := fun (i : Fin r) (k : ℤ) ↦ gs s ((q : ℝ) * k + centre M u i))
    (S := fun i ↦ thetaQ s q (centre M u i)) (fun _ _ ↦ (gs_pos _ _).le)
    (fun i ↦ hasSum_coset hs (Int.cast_ne_zero.mpr hq) (centre M u i))

/-- The unnormalized `u`-marginal of `D_{L,s}`: `ρ_s(u) ∏ᵢ ρ_s(qℤ + (M u)ᵢ)`. -/
def margW (s : ℝ) (q : ℤ) (M : Matrix (Fin r) (Fin t) ℤ) (u : Fin t → ℤ) : ℝ :=
  rhoVec s u * ∏ i, thetaQ s q (centre M u i)

theorem margW_pos {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : q ≠ 0) (M : Matrix (Fin r) (Fin t) ℤ)
    (u : Fin t → ℤ) : 0 < margW s q M u :=
  mul_pos (rhoVec_pos _ _)
    (Finset.prod_pos fun _ _ ↦ thetaQ_pos hs (by exact_mod_cast hq) _)

theorem summable_margW {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : 0 < q) (M : Matrix (Fin r) (Fin t) ℤ) :
    Summable (margW s q M) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  refine Summable.of_nonneg_of_le (fun u ↦ (margW_pos hs hq.ne' M u).le) (fun u ↦ ?_)
    ((hasSum_rhoVec hs).summable.mul_right (((s / q) * (1 + tau (s / q))) ^ r))
  unfold margW
  gcongr with i
  · exact (rhoVec_pos _ _).le
  · calc ∏ i, thetaQ s q (centre M u i) ≤ ∏ _i : Fin r, (s / q) * (1 + tau (s / q)) :=
          Finset.prod_le_prod₀ (fun i _ ↦ (thetaQ_pos hs hq'.ne' _).le)
            (fun i _ ↦ (thetaQ_mem hs hq' _).2)
      _ = _ := by simp

theorem hasSum_indicator_rhoL {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : 0 < q)
    (M : Matrix (Fin r) (Fin t) ℤ) :
    HasSum ((latticeM q M).indicator (rhoL s)) (∑' u, margW s q M u) := by
  refine hasSum_of_paramM hq.ne' (fun y hy ↦ Set.indicator_of_notMem hy _) ?_
  refine hasSum_prod_of_nonneg (G := margW s q M)
    (fun p ↦ Set.indicator_nonneg (fun y _ ↦ (mul_pos (rhoVec_pos _ _) (rhoVec_pos _ _)).le) _)
    (fun u ↦ ?_) (summable_margW hs hq M).hasSum
  have := (hasSum_coset_vec hs hq.ne' M u).mul_right (rhoVec s u)
  convert this using 1
  · funext k
    rw [Set.indicator_of_mem (paramM_mem q M _), rhoL, rhoVec]
    simp only [paramM_fst_cast]
    rfl
  · rw [margW, mul_comm]

theorem zL_eq {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : 0 < q) (M : Matrix (Fin r) (Fin t) ℤ) :
    zL s q M = ∑' u, margW s q M u :=
  (hasSum_indicator_rhoL hs hq M).tsum_eq

theorem zL_pos {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : 0 < q) (M : Matrix (Fin r) (Fin t) ℤ) :
    0 < zL s q M := by
  rw [zL_eq hs hq]
  exact (summable_margW hs hq M).tsum_pos (fun u ↦ (margW_pos hs hq.ne' M u).le) 0
    (margW_pos hs hq.ne' M 0)

/-! ### Probabilities -/

theorem pTail_nonneg (s : ℝ) (u : Fin t → ℤ) : 0 ≤ pTail s u :=
  Finset.prod_nonneg fun _ _ ↦ div_nonneg (gs_pos _ _).le (by
    unfold theta1; exact tsum_nonneg fun _ ↦ (Real.exp_pos _).le)

/-- `p = D_{ℤ,s}^{⊗t}` is a probability. -/
theorem pTail_hasSum {s : ℝ} (hs : 0 < s) : HasSum (pTail (t := t) s) 1 := by
  have h0 := theta1_zero_pos hs
  have := hasSum_pi_prod (f := fun (_ : Fin t) (k : ℤ) ↦ gs s k / theta1 s 0)
    (S := fun _ ↦ 1) (fun _ _ ↦ div_nonneg (gs_pos _ _).le h0.le)
    (fun _ ↦ by simpa [div_self h0.ne'] using (hasSum_gs_int hs).div_const (theta1 s 0))
  show HasSum (fun u ↦ pTail s u) 1
  simpa only [pTail, Finset.prod_const_one] using this

theorem pTail_eq {s : ℝ} (u : Fin t → ℤ) : pTail s u = rhoVec s u / theta1 s 0 ^ t := by
  simp [pTail, rhoVec, Finset.prod_div_distrib]

theorem discGauss_nonneg {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : 0 < q) (M : Matrix (Fin r) (Fin t) ℤ)
    (y : (Fin r → ℤ) × (Fin t → ℤ)) : 0 ≤ discGauss s q M y :=
  div_nonneg (Set.indicator_nonneg (fun _ _ ↦ (mul_pos (rhoVec_pos _ _) (rhoVec_pos _ _)).le) _)
    (zL_pos hs hq M).le

/-- `D_{L_M,s}` is a probability. -/
theorem discGauss_hasSum {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : 0 < q)
    (M : Matrix (Fin r) (Fin t) ℤ) : HasSum (discGauss s q M) 1 := by
  have h := (hasSum_indicator_rhoL hs hq M).div_const (zL s q M)
  rwa [← zL_eq hs hq, div_self (zL_pos hs hq M).ne'] at h

theorem kleinLaw_nonneg {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : 0 < q) (M : Matrix (Fin r) (Fin t) ℤ)
    (y : (Fin r → ℤ) × (Fin t → ℤ)) : 0 ≤ kleinLaw s q M y :=
  Set.indicator_nonneg (fun _ _ ↦ mul_nonneg (pTail_nonneg _ _)
    (Finset.prod_nonneg fun i _ ↦ div_nonneg (gs_pos _ _).le
      (thetaQ_pos hs (by exact_mod_cast hq.ne') _).le)) _

/-- Fibers of the Klein law: `∑ₖ K(q k + M u, u) = p(u)`. -/
theorem hasSum_kleinLaw_fiber {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : 0 < q)
    (M : Matrix (Fin r) (Fin t) ℤ) (u : Fin t → ℤ) :
    HasSum (fun k ↦ kleinLaw s q M (paramM q M (u, k))) (pTail s u) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have h := hasSum_pi_prod
    (f := fun (i : Fin r) (k : ℤ) ↦ gs s ((q : ℝ) * k + centre M u i) / thetaQ s q (centre M u i))
    (S := fun _ ↦ 1) (fun i _ ↦ div_nonneg (gs_pos _ _).le (thetaQ_pos hs hq' _).le)
    (fun i ↦ by
      simpa [div_self (thetaQ_pos hs hq' (centre M u i)).ne'] using
        (hasSum_coset hs hq' (centre M u i)).div_const (thetaQ s q (centre M u i)))
  have := h.mul_left (pTail s u)
  simp only [Finset.prod_const_one, mul_one] at this
  convert this using 2 with k
  rw [kleinLaw, Set.indicator_of_mem (paramM_mem q M _)]
  simp only [paramM_fst_cast]
  rfl

/-- The Klein law is a probability. -/
theorem kleinLaw_hasSum {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : 0 < q)
    (M : Matrix (Fin r) (Fin t) ℤ) : HasSum (kleinLaw s q M) 1 := by
  refine hasSum_of_paramM hq.ne' (fun y hy ↦ Set.indicator_of_notMem hy _) ?_
  exact hasSum_prod_of_nonneg (fun p ↦ kleinLaw_nonneg hs hq M _)
    (hasSum_kleinLaw_fiber hs hq M) (pTail_hasSum hs)

/-! ### Factorization (Part 141 Lemma 1) -/

theorem kleinWeight_eq {s q : ℝ} (w : Fin r → ℝ) :
    kleinWeight s q w = (∏ i, thetaQ s q (w i)) / (s / q) ^ r := by
  simp [kleinWeight, Finset.prod_div_distrib, div_pow]

theorem pTail_mul_kleinWeight (s : ℝ) (q : ℤ) (M : Matrix (Fin r) (Fin t) ℤ) (u : Fin t → ℤ) :
    pTail s u * kleinWeight s q (centre M u) =
      margW s q M u / (theta1 s 0 ^ t * (s / q) ^ r) := by
  rw [pTail_eq, kleinWeight_eq, margW, div_mul_div_comm]

theorem summable_pTail_mul_kleinWeight {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : 0 < q)
    (M : Matrix (Fin r) (Fin t) ℤ) :
    Summable (fun u ↦ pTail s u * kleinWeight s q (centre M u)) := by
  simpa only [pTail_mul_kleinWeight] using (summable_margW hs hq M).div_const _

/-- `E_p[g] = ρ_s(L_M) / (ρ_s(ℤ)^t (s/q)^r)`. -/
theorem kleinMean_eq {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : 0 < q) (M : Matrix (Fin r) (Fin t) ℤ) :
    kleinMean s q M = zL s q M / (theta1 s 0 ^ t * (s / q) ^ r) := by
  rw [kleinMean, zL_eq hs hq, ← tsum_div_const]
  exact tsum_congr fun u ↦ pTail_mul_kleinWeight s q M u

theorem kleinMean_pos {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : 0 < q) (M : Matrix (Fin r) (Fin t) ℤ) :
    0 < kleinMean s q M := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [kleinMean_eq hs hq]
  exact div_pos (zL_pos hs hq M)
    (mul_pos (pow_pos (theta1_zero_pos hs) _) (pow_pos (div_pos hs hq') _))

/-- **Factorization.** For every `y = (h, u)`,
`D_{L_M,s}(y) = K(y) · g(u) / E_p[g]` with `g(u) = kleinWeight s q (M u)`. -/
theorem discGauss_eq_kleinLaw_mul {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : 0 < q)
    (M : Matrix (Fin r) (Fin t) ℤ) (y : (Fin r → ℤ) × (Fin t → ℤ)) :
    discGauss s q M y =
      kleinLaw s q M y * (kleinWeight s q (centre M y.2) / kleinMean s q M) := by
  by_cases hy : y ∈ latticeM q M
  · have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hA : 0 < ∏ i, thetaQ s q (centre M y.2 i) :=
      Finset.prod_pos fun _ _ ↦ thetaQ_pos hs hq'.ne' _
    have hθ := theta1_zero_pos hs
    have hz := zL_pos hs hq M
    have hsq : 0 < s / q := div_pos hs hq'
    rw [discGauss, kleinLaw, Set.indicator_of_mem hy, Set.indicator_of_mem hy, kleinMean_eq hs hq,
      kleinWeight_eq, pTail_eq, rhoL, Finset.prod_div_distrib]
    change rhoVec s y.1 * rhoVec s y.2 / zL s q M = rhoVec s y.2 / theta1 s 0 ^ t *
      (rhoVec s y.1 / ∏ i, thetaQ s q (centre M y.2 i)) *
      ((∏ i, thetaQ s q (centre M y.2 i)) / (s / q) ^ r /
        (zL s q M / (theta1 s 0 ^ t * (s / q) ^ r)))
    field_simp
  · simp [discGauss, kleinLaw, Set.indicator_of_notMem hy]

/-- **Pointwise ratio.** On `L_M`, `D_{L_M,s}(y) / K(y) = g(u) / E_p[g]`. -/
theorem discGauss_div_kleinLaw {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : 0 < q)
    (M : Matrix (Fin r) (Fin t) ℤ) {y : (Fin r → ℤ) × (Fin t → ℤ)} (hy : y ∈ latticeM q M) :
    discGauss s q M y / kleinLaw s q M y = kleinWeight s q (centre M y.2) / kleinMean s q M := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hK : 0 < kleinLaw s q M y := by
    rw [kleinLaw, Set.indicator_of_mem hy]
    refine mul_pos (Finset.prod_pos fun _ _ ↦ div_pos (gs_pos _ _) (theta1_zero_pos hs))
      (Finset.prod_pos fun _ _ ↦ div_pos (gs_pos _ _) (thetaQ_pos hs hq'.ne' _))
  rw [discGauss_eq_kleinLaw_mul hs hq, mul_div_cancel_left₀ _ hK.ne']

/-! ### Statistical distance (Part 141 Lemma 2) -/

/-- `SD(K, D_{L_M,s}) = ½ E_p |g / E_p[g] - 1|`. -/
theorem sdist_kleinLaw_discGauss_eq {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : 0 < q)
    (M : Matrix (Fin r) (Fin t) ℤ) :
    sdist (kleinLaw s q M) (discGauss s q M) =
      (1 / 2) * ∑' u, pTail s u * |kleinWeight s q (centre M u) / kleinMean s q M - 1| := by
  set E := kleinMean s q M
  set c : (Fin t → ℤ) → ℝ := fun u ↦ |kleinWeight s q (centre M u) / E - 1| with hc
  have hE := kleinMean_pos hs hq M
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hpt (y : (Fin r → ℤ) × (Fin t → ℤ)) :
      |kleinLaw s q M y - discGauss s q M y| = kleinLaw s q M y * c y.2 := by
    rw [discGauss_eq_kleinLaw_mul hs hq, show ∀ a b : ℝ, a - a * b = a * (1 - b) by
      intros; ring, abs_mul, abs_of_nonneg (kleinLaw_nonneg hs hq M y), abs_sub_comm]
  have hg0 (u : Fin t → ℤ) : 0 ≤ kleinWeight s q (centre M u) := by
    rw [kleinWeight_eq]
    exact div_nonneg (Finset.prod_nonneg fun _ _ ↦ (thetaQ_pos hs hq'.ne' _).le)
      (pow_nonneg (div_pos hs hq').le _)
  have hGs : Summable (fun u ↦ pTail s u * c u) := by
    refine Summable.of_nonneg_of_le (fun u ↦ mul_nonneg (pTail_nonneg _ _) (abs_nonneg _))
      (fun u ↦ ?_) (((summable_pTail_mul_kleinWeight hs hq M).div_const E).add
        (pTail_hasSum hs).summable)
    have h1 : c u ≤ kleinWeight s q (centre M u) / E + 1 := by
      rw [hc]
      have := div_nonneg (hg0 u) hE.le
      rw [abs_le]; constructor <;> linarith
    calc pTail s u * c u ≤ pTail s u * (kleinWeight s q (centre M u) / E + 1) :=
          mul_le_mul_of_nonneg_left h1 (pTail_nonneg _ _)
      _ = _ := by ring
  have hsum : HasSum (fun y ↦ |kleinLaw s q M y - discGauss s q M y|)
      (∑' u, pTail s u * c u) := by
    simp only [hpt]
    refine hasSum_of_paramM (M := M) hq.ne' (fun y hy ↦ by
      simp [kleinLaw, Set.indicator_of_notMem hy]) ?_
    exact hasSum_prod_of_nonneg
      (fun p ↦ mul_nonneg (kleinLaw_nonneg hs hq M _) (abs_nonneg _))
      (fun u ↦ (hasSum_kleinLaw_fiber hs hq M u).mul_right (c u)) hGs.hasSum
  rw [sdist, hsum.tsum_eq]

/-- **Part 141 Lemma 2 on `L_M`.** With `τ = τ(s/q) < 1`,
`SD(K, D_{L_M,s}) ≤ ½ (((1+τ)/(1-τ))^r - 1)`, for every integer matrix `M`. -/
theorem sdist_kleinLaw_discGauss_le {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : 0 < q)
    (M : Matrix (Fin r) (Fin t) ℤ) (hτ : tau (s / q) < 1) :
    sdist (kleinLaw s q M) (discGauss s q M) ≤
      (1 / 2) * (((1 + tau (s / q)) / (1 - tau (s / q))) ^ r - 1) := by
  rw [sdist_kleinLaw_discGauss_eq hs hq M]
  exact klein_sd_le hs (by exact_mod_cast hq) hτ (pTail_nonneg s) (pTail_hasSum hs) (centre M)

/-! ### Elementary numerics -/

/-- `(1 + x)^n ≤ 1 + n x + (n x)²` when `0 ≤ x` and `n x ≤ 1`. -/
theorem one_add_pow_le_quad {x : ℝ} (hx : 0 ≤ x) :
    ∀ n : ℕ, (n : ℝ) * x ≤ 1 → (1 + x) ^ n ≤ 1 + n * x + (n * x) ^ 2
  | 0, _ => by simp
  | n + 1, h => by
    push_cast at h ⊢
    have h1 : (n : ℝ) * x ≤ 1 := by nlinarith
    have ih := one_add_pow_le_quad hx n h1
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have h2 : (n : ℝ) ^ 2 * x ≤ n + 1 := by nlinarith
    rw [pow_succ]
    calc (1 + x) ^ n * (1 + x) ≤ (1 + n * x + (n * x) ^ 2) * (1 + x) :=
          mul_le_mul_of_nonneg_right ih (by linarith)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg x)]

/-- For small `τ ≤ δ`: `½ (((1+τ)/(1-τ))^r - 1) ≤ 1.01 · r · δ`. -/
theorem half_ratio_pow_sub_one_le {τ δ : ℝ} {r : ℕ} (h0 : 0 ≤ τ) (hτ : τ ≤ δ)
    (hδ : δ ≤ 1 / 1000) (hr : (r : ℝ) * δ ≤ 1 / 1000) :
    (1 / 2) * (((1 + τ) / (1 - τ)) ^ r - 1) ≤ (101 / 100) * r * δ := by
  have h1τ : 0 < 1 - τ := by linarith
  set X := (1 + τ) / (1 - τ) - 1 with hX
  have hXe : X = 2 * τ / (1 - τ) := by rw [hX]; field_simp; ring
  have hX0 : 0 ≤ X := by rw [hXe]; positivity
  have hX1 : X ≤ 2 * δ * (1 + 2 * δ) := by
    rw [hXe, div_le_iff₀ h1τ]
    have : 2 * τ ≤ 2 * τ * (1 + 2 * τ) * (1 - τ) := by nlinarith [sq_nonneg τ, mul_nonneg h0 h0]
    have hm : 2 * τ * (1 + 2 * τ) ≤ 2 * δ * (1 + 2 * δ) := by nlinarith
    nlinarith
  have hrn : (0 : ℝ) ≤ r := r.cast_nonneg
  have hδ0 : 0 ≤ δ := h0.trans hτ
  have hY : (r : ℝ) * X ≤ (2004 / 1000) * (r * δ) := by
    have : 2 * δ * (1 + 2 * δ) ≤ (2004 / 1000) * δ := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left (hX1.trans this) hrn]
  have hY0 : 0 ≤ (r : ℝ) * X := mul_nonneg hrn hX0
  have hpow := one_add_pow_le_quad hX0 r (by nlinarith)
  rw [show (1 + τ) / (1 - τ) = 1 + X by rw [hX]; ring]
  have hY2 : ((r : ℝ) * X) ^ 2 ≤ (2004 / 1000000) * ((r : ℝ) * X) := by
    have : (r : ℝ) * X ≤ 2004 / 1000000 := by nlinarith
    nlinarith
  nlinarith

/-- A sharpened form of `tau_lt_of_ge`: at `s/q ≥ 38.39`, `τ(s/q) < (2/3) · 2^{-6678}`. -/
theorem tau_lt_of_ge' {x : ℝ} (hx : 38.39 ≤ x) : tau x < (2 / 3) / 2 ^ 6678 := by
  set y := π * x ^ 2 with hy
  have hy0 : 4630.05 ≤ y := by
    have hx2 : (38.39 : ℝ) ^ 2 ≤ x ^ 2 := by gcongr
    nlinarith [pi_gt_d6, pi_pos]
  have hx0 : 0 < x := by linarith
  have h3 : Real.exp (-3 * y) ≤ 1 / 13891 := by
    have := Real.add_one_le_exp (3 * y)
    rw [show -3 * y = -(3 * y) by ring, Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hden : (13890 : ℝ) / 13891 ≤ 1 - Real.exp (-3 * y) := by linarith
  have hlog := log_two_lt_d9
  have hexp : Real.exp (Real.log 2 - y) * Real.exp (6678 * Real.log 2) ≤ Real.exp (-0.5) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; norm_num at hlog ⊢; nlinarith
  have h05 : Real.exp (-0.5) ≤ 1 / 1.6 := by
    have := Real.quadratic_le_exp_of_nonneg (x := 0.5) (by norm_num)
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by norm_num at this ⊢; linarith)
  have h2pow : (2 : ℝ) ^ 6678 = Real.exp (6678 * Real.log 2) := by
    have := Real.exp_nat_mul (Real.log 2) 6678
    rw [Real.exp_log two_pos] at this
    rw [← this]; norm_num
  calc tau x ≤ 2 * Real.exp (-y) / (1 - Real.exp (-3 * y)) := tau_le hx0
    _ ≤ 2 * Real.exp (-y) / (13890 / 13891) := by
        gcongr
    _ = (13891 / 13890) * Real.exp (Real.log 2 - y) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_log two_pos]; ring
    _ < (2 / 3) / 2 ^ 6678 := by
        rw [h2pow, lt_div_iff₀ (Real.exp_pos _), mul_assoc]
        have hp := Real.exp_pos (Real.log 2 - y)
        nlinarith

/-! ### The recorded instance: `s/q ≥ 38.39` -/

/-- At `s/q ≥ 38.39` and `r ≤ 2^20`: `SD(K, D_{L_M,s}) ≤ 1.01 · r · (2/3) · 2^{-6678}`. -/
theorem sdist_kleinLaw_discGauss_le_of_ge {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : 0 < q)
    (M : Matrix (Fin r) (Fin t) ℤ) (hsq : 38.39 ≤ s / q) (hr : r ≤ 2 ^ 20) :
    sdist (kleinLaw s q M) (discGauss s q M) ≤ (101 / 100) * r * ((2 / 3) / 2 ^ 6678) := by
  have hτ := tau_lt_of_ge' hsq
  have hE : (2 : ℝ) ^ 30 ≤ 2 ^ 6678 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hδ : (2 / 3 : ℝ) / 2 ^ 6678 ≤ 1 / 2 ^ 30 := by
    calc (2 / 3 : ℝ) / 2 ^ 6678 ≤ 1 / 2 ^ 6678 := by gcongr; norm_num
      _ ≤ 1 / 2 ^ 30 := one_div_le_one_div_of_le (by positivity) hE
  have hr' : (r : ℝ) ≤ 2 ^ 20 := by exact_mod_cast hr
  have h30 : (2 : ℝ) ^ 20 * (1 / 2 ^ 30) ≤ 1 / 1000 := by norm_num
  refine (sdist_kleinLaw_discGauss_le hs hq M (hτ.trans (by
    have : (1 / 2 ^ 30 : ℝ) < 1 := by norm_num
    linarith))).trans ?_
  refine half_ratio_pow_sub_one_le (tau_nonneg _) hτ.le (hδ.trans (by norm_num)) ?_
  calc (r : ℝ) * ((2 / 3) / 2 ^ 6678) ≤ 2 ^ 20 * (1 / 2 ^ 30) :=
        mul_le_mul hr' hδ (by positivity) (by positivity)
    _ ≤ 1 / 1000 := h30

/-- **Instance bound, `r ≤ 512`.** At `s/q ≥ 38.39`: `SD(K, D_{L_M,s}) < 2^{-6669}`. -/
theorem sdist_kleinLaw_discGauss_lt_of_ge {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : 0 < q)
    (M : Matrix (Fin r) (Fin t) ℤ) (hsq : 38.39 ≤ s / q) (hr : r ≤ 512) :
    sdist (kleinLaw s q M) (discGauss s q M) < 1 / 2 ^ 6669 := by
  refine (sdist_kleinLaw_discGauss_le_of_ge hs hq M hsq (hr.trans (by norm_num))).trans_lt ?_
  have hr' : (r : ℝ) ≤ 512 := by exact_mod_cast hr
  rw [show (2 : ℝ) ^ 6678 = 2 ^ 6669 * 512 by rw [show (512 : ℝ) = 2 ^ 9 by norm_num, ← pow_add]]
  have hF : (0 : ℝ) < 2 ^ 6669 := by positivity
  rw [show (101 / 100 : ℝ) * r * (2 / 3 / (2 ^ 6669 * 512)) = ((101 / 100) * r * (2 / 3) / 512) *
    (1 / 2 ^ 6669) by field_simp]
  have : (101 / 100 : ℝ) * r * (2 / 3) / 512 < 1 := by
    rw [div_lt_one (by norm_num)]; nlinarith
  have h1 : (0 : ℝ) < 1 / 2 ^ 6669 := by positivity
  nlinarith

/-- **Instance bound, `r ≤ 134`** (covering the recorded `r = 133`). At `s/q ≥ 38.39`:
`SD(K, D_{L_M,s}) < 2^{-6671}`. -/
theorem sdist_kleinLaw_discGauss_lt_of_ge_134 {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : 0 < q)
    (M : Matrix (Fin r) (Fin t) ℤ) (hsq : 38.39 ≤ s / q) (hr : r ≤ 134) :
    sdist (kleinLaw s q M) (discGauss s q M) < 1 / 2 ^ 6671 := by
  refine (sdist_kleinLaw_discGauss_le_of_ge hs hq M hsq (hr.trans (by norm_num))).trans_lt ?_
  have hr' : (r : ℝ) ≤ 134 := by exact_mod_cast hr
  rw [show (2 : ℝ) ^ 6678 = 2 ^ 6671 * 128 by rw [show (128 : ℝ) = 2 ^ 7 by norm_num, ← pow_add]]
  rw [show (101 / 100 : ℝ) * r * (2 / 3 / (2 ^ 6671 * 128)) = ((101 / 100) * r * (2 / 3) / 128) *
    (1 / 2 ^ 6671) by field_simp]
  have : (101 / 100 : ℝ) * r * (2 / 3) / 128 < 1 := by
    rw [div_lt_one (by norm_num)]; nlinarith
  have h1 : (0 : ℝ) < 1 / 2 ^ 6671 := by positivity
  nlinarith

/-- The recorded head dimension `r = 133`. -/
theorem sdist_kleinLaw_discGauss_lt_r133 {t : ℕ} {s : ℝ} (hs : 0 < s) {q : ℤ} (hq : 0 < q)
    (M : Matrix (Fin 133) (Fin t) ℤ) (hsq : 38.39 ≤ s / q) :
    sdist (kleinLaw s q M) (discGauss s q M) < 1 / 2 ^ 6671 :=
  sdist_kleinLaw_discGauss_lt_of_ge_134 hs hq M hsq (by norm_num)

end

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.hasSum_pi_prod
#print axioms SigabaNeo.Wall1.range_paramM
#print axioms SigabaNeo.Wall1.pTail_hasSum
#print axioms SigabaNeo.Wall1.discGauss_hasSum
#print axioms SigabaNeo.Wall1.kleinLaw_hasSum
#print axioms SigabaNeo.Wall1.discGauss_eq_kleinLaw_mul
#print axioms SigabaNeo.Wall1.discGauss_div_kleinLaw
#print axioms SigabaNeo.Wall1.sdist_kleinLaw_discGauss_eq
#print axioms SigabaNeo.Wall1.sdist_kleinLaw_discGauss_le
#print axioms SigabaNeo.Wall1.tau_lt_of_ge'
#print axioms SigabaNeo.Wall1.sdist_kleinLaw_discGauss_lt_of_ge
#print axioms SigabaNeo.Wall1.sdist_kleinLaw_discGauss_lt_of_ge_134
#print axioms SigabaNeo.Wall1.sdist_kleinLaw_discGauss_lt_r133
