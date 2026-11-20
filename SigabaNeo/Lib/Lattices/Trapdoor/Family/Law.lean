import SigabaNeo.Lib.Lattices.Trapdoor.Family.Gadget

/-!
# Trapdoor sampler: the laws

* `vecLaw_apply`: `k` independent draws form the product law.
* `gaussVec`: `D_{Z^m,τ}` as `m` independent draws of `D_{Z,τ}`; `gaussVec_apply`.
* `colLaw Ā R u`: draw `y ← D_{Z^m,τ}` and output `y + xPre R (u − B y)`, a point of the coset
  `{x : B x = u}`. Its mass at `x` is `Σ_v D_{Z^m,τ}(x − xPre R v)` (`colLaw_apply`): the points
  `y` sent to `x` are exactly `x − xPre R v`, one for each syndrome `v`.
* `cosetGauss_apply`: the mass of the coset Gaussian is `ρ_τ(x) / M` on the coset.
-/

namespace SigabaNeo.Lattices.Trapdoor.Family

open SigabaNeo.Lattices ZLattice ProbabilityTheory
open scoped ENNReal Matrix

/-! ### Products and injective maps -/

theorem map_cons_apply {α : Type} [DecidableEq α] {k : ℕ} (p : PMF (Fin k → α)) (a : α) (y : Fin (k + 1) → α) :
    (p.map (Fin.cons a)) y = if y 0 = a then p (Fin.tail y) else 0 := by
  rw [PMF.map_apply, tsum_eq_single (Fin.tail y)]
  · by_cases h : y 0 = a
    · rw [if_pos h, if_pos]; rw [← h, Fin.cons_self_tail]
    · rw [if_neg h, if_neg]; intro h'; apply h; rw [h']; simp
  · intro t ht
    rw [if_neg]
    intro h; apply ht; rw [h]; simp

theorem vecLaw_apply {α : Type} [Inhabited α] [DecidableEq α] (d : PMF α) :
    ∀ (k : ℕ) (y : Fin k → α),
      ((sampleList d k).map (fun l (j : Fin k) => l.getD j default)) y = ∏ j, d (y j)
  | 0, y => by
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    unfold sampleList
    rw [PMF.pure_map, PMF.pure_apply, if_pos (Subsingleton.elim _ _)]
  | k + 1, y => by
    have h : (sampleList d (k + 1)).map (fun l (j : Fin (k + 1)) => l.getD j default) =
        d.bind fun a => ((sampleList d k).map (fun l (j : Fin k) => l.getD j default)).map
          (Fin.cons a) := by
      show ((d.bind fun a => (sampleList d k).map (a :: ·)).map _) = _
      rw [PMF.map_bind]
      congr 1; funext a
      rw [PMF.map_comp, PMF.map_comp]
      congr 1
      funext l j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp
    rw [h, PMF.bind_apply, tsum_eq_single (y 0)]
    · rw [map_cons_apply, if_pos rfl, vecLaw_apply d k, Fin.prod_univ_succ]; rfl
    · intro a ha
      rw [map_cons_apply, if_neg (Ne.symm ha), mul_zero]

/-- The mass of an injective image. -/
theorem map_apply_of_injective {α β : Type} (p : PMF α) {f : α → β} (hf : Function.Injective f)
    (a : α) : (p.map f) (f a) = p a := by
  rw [PMF.map_apply, tsum_eq_single a]
  · simp
  · intro b hb; rw [if_neg]; intro h; exact hb (hf h.symm)

theorem map_apply_of_not_mem {α β : Type} (p : PMF α) {f : α → β} (b : β) (hb : ∀ a, f a ≠ b) :
    (p.map f) b = 0 := by
  rw [PMF.map_apply]
  exact ENNReal.tsum_eq_zero.mpr fun a => by rw [if_neg (fun h => hb a h.symm)]

section
variable (κ : ℕ)

/-- `ρ_τ(x) = exp(−π ‖x‖²/τ²)` on integer vectors. -/
noncomputable def rhoV (x : Fin (m κ) → ℤ) : ℝ := ∏ j, gw (τ κ) (x j)

/-- `D_{Z^m,τ}`. -/
noncomputable def gaussVec : PMF (Fin (m κ) → ℤ) :=
  (sampleList (gaussZ (τ κ) (τ_pos κ)) (m κ)).map (fun l (j : Fin (m κ)) => l.getD j default)

theorem gaussVec_apply (y : Fin (m κ) → ℤ) :
    gaussVec κ y = ENNReal.ofReal (rhoV κ y) / ENNReal.ofReal (Mz (τ κ)) ^ m κ := by
  unfold gaussVec rhoV
  rw [vecLaw_apply]
  simp only [gaussZ_apply (τ_pos κ), ENNReal.div_eq_inv_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.inv_pow]
  rw [ENNReal.ofReal_prod_of_nonneg (f := fun j => gw (τ κ) (y j))
    (fun j _ => (Real.exp_pos _).le)]

/-- `B y` over `Z_q`. -/
noncomputable def castV (y : Fin (m κ) → ℤ) : Fin (m κ) → ZMod (q κ) := fun j => (y j : ZMod (q κ))

/-- Send `y` into the coset `u`. -/
noncomputable def gsyn (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (u : Fin (n κ) → ZMod (q κ))
    (y : Fin (m κ) → ℤ) : Fin (m κ) → ℤ :=
  y + xPre κ R (u - Bmat κ Abar R *ᵥ castV κ y)

/-- The ideal column sampler. -/
noncomputable def colLaw (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (u : Fin (n κ) → ZMod (q κ)) :
    PMF (Fin (m κ) → ℤ) :=
  (gaussVec κ).map (gsyn κ Abar R u)

theorem castV_add (a b : Fin (m κ) → ℤ) : castV κ (a + b) = castV κ a + castV κ b := by
  funext j; simp [castV]

theorem castV_sub (a b : Fin (m κ) → ℤ) : castV κ (a - b) = castV κ a - castV κ b := by
  funext j; simp [castV]

theorem B_xPre (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (v : Fin (n κ) → ZMod (q κ)) :
    Bmat κ Abar R *ᵥ castV κ (xPre κ R v) = v := Bmat_mulVec_xPre κ Abar R v

theorem B_gsyn (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (u : Fin (n κ) → ZMod (q κ)) (y : Fin (m κ) → ℤ) :
    Bmat κ Abar R *ᵥ castV κ (gsyn κ Abar R u y) = u := by
  unfold gsyn
  rw [castV_add, Matrix.mulVec_add, B_xPre]
  abel

theorem gsyn_preimage (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (u : Fin (n κ) → ZMod (q κ)) (x : Fin (m κ) → ℤ)
    (hx : Bmat κ Abar R *ᵥ castV κ x = u) (v : Fin (n κ) → ZMod (q κ)) :
    gsyn κ Abar R u (x - xPre κ R v) = x := by
  unfold gsyn
  rw [castV_sub, Matrix.mulVec_sub, B_xPre, hx, sub_sub_cancel, sub_add_cancel]

theorem colLaw_apply (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (u : Fin (n κ) → ZMod (q κ)) (x : Fin (m κ) → ℤ)
    (hx : Bmat κ Abar R *ᵥ castV κ x = u) :
    colLaw κ Abar R u x = ∑ v : Fin (n κ) → ZMod (q κ), gaussVec κ (x - xPre κ R v) := by
  classical
  have hinj : Function.Injective fun v : Fin (n κ) → ZMod (q κ) => x - xPre κ R v := by
    intro v v' h
    have h' : xPre κ R v = xPre κ R v' := by simpa using h
    rw [← B_xPre κ Abar R v, ← B_xPre κ Abar R v', h']
  unfold colLaw
  rw [PMF.map_apply, tsum_eq_sum (s := Finset.univ.image fun v => x - xPre κ R v)]
  · rw [Finset.sum_image fun a _ b _ h => hinj h]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [if_pos (gsyn_preimage κ Abar R u x hx v).symm]
  · intro y hy
    rw [if_neg]
    intro h
    apply hy
    refine Finset.mem_image.mpr ⟨u - Bmat κ Abar R *ᵥ castV κ y, Finset.mem_univ _, ?_⟩
    rw [h]; unfold gsyn; abel

theorem colLaw_apply_off (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (u : Fin (n κ) → ZMod (q κ)) (x : Fin (m κ) → ℤ)
    (hx : Bmat κ Abar R *ᵥ castV κ x ≠ u) : colLaw κ Abar R u x = 0 :=
  map_apply_of_not_mem _ x fun y h => hx (h ▸ B_gsyn κ Abar R u y)

end

/-! ### The coset Gaussian -/

section
variable {n m q : ℕ}

theorem cosetGauss_apply (B : Matrix (Fin n) (Fin m) (ZMod q)) (u : Fin n → ZMod q) {τ : ℝ}
    (hτ : 0 < τ) {p : PMF (Fin m → ℤ)} (hp : cosetGauss B u τ hτ = some p) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : Fin m → ℤ, p x =
      if B *ᵥ (fun i => (x i : ZMod q)) = u then
        ENNReal.ofReal (gaussianWeight τ (embed m x)) / ENNReal.ofReal M else 0 := by
  classical
  unfold cosetGauss at hp
  split_ifs at hp with h
  obtain rfl := Option.some.inj hp
  set x0 := h.choose
  refine ⟨gaussianMass (perp B) τ (-(embed m x0)), gaussianMass_pos _ τ hτ _, fun x => ?_⟩
  have hb : (ZLattice.discreteGaussian (perp B) τ hτ (-(embed m x0)) >>= fun a =>
      pure (a : EuclideanSpace ℝ (Fin m))) =
      (ZLattice.discreteGaussian (perp B) τ hτ (-(embed m x0))).map Subtype.val := rfl
  rw [hb, PMF.map_comp]
  have hinj : Function.Injective ((fun z => x0 + toInt z) ∘ (Subtype.val :
      perp B → EuclideanSpace ℝ (Fin m))) := by
    intro a b hab
    simp only [Function.comp_apply, add_right_inj] at hab
    obtain ⟨ya, -, hya⟩ := Submodule.mem_map.mp a.2
    obtain ⟨yb, -, hyb⟩ := Submodule.mem_map.mp b.2
    apply Subtype.ext
    rw [← hya, ← hyb, toInt_embed, toInt_embed] at hab
    rw [← hya, ← hyb, hab]
  split_ifs with hx
  · have hmem : embed m (x - x0) ∈ perp B := by
      refine Submodule.mem_map.mpr ⟨x - x0, ?_, rfl⟩
      show B *ᵥ (fun i => ((x - x0) i : ZMod q)) = 0
      have : (fun i => ((x - x0) i : ZMod q)) = (fun i => (x i : ZMod q)) - fun i => (x0 i : ZMod q) := by
        funext i; simp
      rw [this, Matrix.mulVec_sub, hx, h.choose_spec, sub_self]
    have hx' : x = ((fun z => x0 + toInt z) ∘ (Subtype.val : perp B → EuclideanSpace ℝ (Fin m)))
        ⟨_, hmem⟩ := by
      show x = x0 + toInt (embed m (x - x0)); rw [toInt_embed, add_sub_cancel]
    rw [hx', map_apply_of_injective _ hinj, discreteGaussian_apply]
    congr 2
    rw [← hx']
    simp only [sub_neg_eq_add, ← map_add, sub_add_cancel]
  · refine map_apply_of_not_mem _ x fun z hz => hx ?_
    obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.mp z.2
    simp only [Function.comp_apply] at hz
    rw [← hz, ← hyz, toInt_embed]
    have hk : B *ᵥ (fun i => (y i : ZMod q)) = 0 := hy
    have : (fun i => ((x0 + y) i : ZMod q)) = (fun i => (x0 i : ZMod q)) + fun i => (y i : ZMod q) := by
      funext i; simp
    rw [this, Matrix.mulVec_add, h.choose_spec, hk, add_zero]

end

end SigabaNeo.Lattices.Trapdoor.Family
