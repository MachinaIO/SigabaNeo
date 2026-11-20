import Solution.Pre2Hyb
import Definitions.Def_EvLWE_LWE
/-!
# Pre2 from LWE samples

From an LWE pair `(A, b)` and `h, R, T`, the reduction forms the Pre2 word
`hybLWE (A, b) h R T = (2Aᵀ + h·R, 2bᵀ − 2T)`.

* `real_hyb`: on a real pair (`b = A s + e`) this is `Yd h true`: `P = 2Aᵀ` is uniform, `S = sᵀ`,
  `E = eᵀ`, and `2bᵀ = S·P + 2E`.
* `rand_hyb`: on a uniform pair it is a uniform pair `(P, aux)`, whatever `h`, `R`, `T` are.
-/

namespace TestCase.EvLWE

open SigabaNeo.Lattices

open TestCase TestCase.EvLWE Cslib Cslib.Crypto Cslib.Probability
open scoped ENNReal Matrix

/-! ### The LWE samples -/

/-- An LWE pair `(A, b)` at ring degree 1. -/
abbrev LWEPair (κ : ℕ) : Type := LWE.Pair (k κ) (n κ) (q κ)

/-- The encoding of `lwe`: `q`, then `Aᵀ` row-major, then `b`. -/
noncomputable def encLWE (κ : ℕ) (pair : LWEPair κ) : List Bool := LWE.encodePub (W κ) (q κ) pair

/-- The encoded real samples. -/
noncomputable def lweReal (κ : ℕ) : PMF (List Bool) :=
  (ModuleLWE.sampleLaw (lweSecret κ) (lweError κ)).map (encLWE κ)

/-- The encoded uniform samples. -/
noncomputable def lweRandom (κ : ℕ) : PMF (List Bool) :=
  (PMF.uniformOfFintype (LWEPair κ)).map (encLWE κ)

theorem lwe_iff : lwe ↔ ComputationallyIndistinguishable lweReal lweRandom := Iff.rfl

section
variable {α β : Type*}

theorem ev_uniform_equiv [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (e : α ≃ β)
    (f : β → ℝ≥0∞) :
    ev (PMF.uniformOfFintype α) (fun a => f (e a)) = ev (PMF.uniformOfFintype β) f := by
  rw [← PMF.uniformOfFintype_map_equiv e, ev_map]; rfl

theorem ev_uniform_prod [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (f : α × β → ℝ≥0∞) :
    ev (PMF.uniformOfFintype (α × β)) f =
      ev (PMF.uniformOfFintype α) fun a => ev (PMF.uniformOfFintype β) fun b => f (a, b) := by
  rw [← PMF.uniformOfFintype_prod, ev_bind]
  congr 1; funext a
  rw [ev_map]; rfl

theorem ev_const_of_eq (p : PMF α) {f : α → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ a, f a = c) : ev p f = c := by
  rw [show f = fun _ => c from funext h, ev_const]

theorem pmf_ext_ev {p p' : PMF α} (h : ∀ f, ev p f = ev p' f) : p = p' := by
  ext a; rw [← ev_point, ← ev_point, h]

end

section
variable (κ : ℕ)

theorem q_gt_nat : 2 ^ w κ < q κ := (exists_q κ).choose_spec.2.1

theorem two_ne_zero_q : (2 : ZMod (q κ)) ≠ 0 := by
  have h : ¬ q κ ∣ 2 := fun hd => by
    have h1 := Nat.le_of_dvd (by norm_num) hd
    have h2 := q_gt_nat κ
    have h3 : 2 ≤ 2 ^ w κ := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ w κ := Nat.pow_le_pow_right (by norm_num) (by unfold w; omega)
    omega
  have := (ZMod.natCast_eq_zero_iff 2 (q κ)).not.mpr h
  exact_mod_cast this

/-- `A ↦ 2Aᵀ`. -/
noncomputable def pofEquiv : Matrix (Fin (k κ)) (Fin (n κ)) (Fin 1 → ZMod (q κ)) ≃ PMat κ where
  toFun A := fun i j => 2 * A j i 0
  invFun P := fun j i _ => 2⁻¹ * P i j
  left_inv A := by
    funext j i x
    obtain rfl : x = 0 := Subsingleton.elim _ _
    simp [← mul_assoc, inv_mul_cancel₀ (two_ne_zero_q κ)]
  right_inv P := by
    funext i j
    simp [← mul_assoc, mul_inv_cancel₀ (two_ne_zero_q κ)]

/-- `b ↦ 2bᵀ`. -/
noncomputable def bEquiv : (Fin (k κ) → Fin 1 → ZMod (q κ)) ≃ Row κ where
  toFun b := fun _ j => 2 * b j 0
  invFun a := fun j _ => 2⁻¹ * a default j
  left_inv b := by
    funext j x
    obtain rfl : x = 0 := Subsingleton.elim _ _
    simp [← mul_assoc, inv_mul_cancel₀ (two_ne_zero_q κ)]
  right_inv a := by
    funext i j
    obtain rfl : i = default := Subsingleton.elim _ _
    simp [← mul_assoc, mul_inv_cancel₀ (two_ne_zero_q κ)]

/-- The Pre2 word the reduction forms. -/
noncomputable def hybLWE (pair : LWEPair κ) (h : Bool) (R : RMat κ) (T : TMat κ) : List Bool :=
  pre2Word κ (pofEquiv κ pair.1 + if h then Rq κ R else 0)
    (bEquiv κ pair.2 - (2 : ZMod (q κ)) • Tq κ T)

/-- The reduction's draws of `R` and `T`. -/
noncomputable def inner (pair : LWEPair κ) (h : Bool) : PMF (List Bool) :=
  (PMF.uniformOfFintype (RMat κ)).bind fun R =>
    (PMF.uniformOfFintype (TMat κ)).bind fun T => PMF.pure (hybLWE κ pair h R T)

/-- `(P + h·R, Sq·P + 2Eq − 2T)` with `Sq`, `Eq` over `Z_q`. -/
noncomputable def hybq (h : Bool) (P : PMat κ) (Sq : Matrix (Fin (ell κ)) (Fin (n κ)) (ZMod (q κ)))
    (Eq : Row κ) (R : RMat κ) (T : TMat κ) : List Bool :=
  pre2Word κ (P + if h then Rq κ R else 0)
    (Sq * P + (2 : ZMod (q κ)) • Eq - (2 : ZMod (q κ)) • Tq κ T)

def sToRow (s : Fin (n κ) → Fin 1 → ZMod (q κ)) : Matrix (Fin (ell κ)) (Fin (n κ)) (ZMod (q κ)) :=
  fun _ i => s i 0

def eToRow (e : Fin (k κ) → Fin 1 → ZMod (q κ)) : Row κ := fun _ j => e j 0

theorem negacyclicMul_one {R : Type*} [Ring R] (a b : Fin 1 → R) :
    negacyclicMul a b 0 = a 0 * b 0 := by
  simp [negacyclicMul, rotMatrix, Matrix.mulVec, dotProduct]

theorem pofEquiv_apply (A : Matrix (Fin (k κ)) (Fin (n κ)) (Fin 1 → ZMod (q κ))) (i : Fin (n κ))
    (j : Fin (k κ)) : pofEquiv κ A i j = 2 * A j i 0 := rfl

theorem bEquiv_apply (b : Fin (k κ) → Fin 1 → ZMod (q κ)) (i : Fin (ell κ)) (j : Fin (k κ)) :
    bEquiv κ b i j = 2 * b j 0 := rfl

theorem sample_apply {kk nn : ℕ} (A : Matrix (Fin kk) (Fin nn) (Fin 1 → ZMod (q κ)))
    (s : Fin nn → Fin 1 → ZMod (q κ)) (e : Fin kk → Fin 1 → ZMod (q κ)) (j : Fin kk) :
    ModuleLWE.sample A s e j 0 = (∑ x, A j x 0 * s x 0) + e j 0 := by
  simp [ModuleLWE.sample, moduleSISMap, Finset.sum_apply, negacyclicMul_one]

theorem hybLWE_sample (A : Matrix (Fin (k κ)) (Fin (n κ)) (Fin 1 → ZMod (q κ)))
    (s : Fin (n κ) → Fin 1 → ZMod (q κ)) (e : Fin (k κ) → Fin 1 → ZMod (q κ)) (h : Bool)
    (R : RMat κ) (T : TMat κ) :
    hybLWE κ (A, ModuleLWE.sample A s e) h R T =
      hybq κ h (pofEquiv κ A) (sToRow κ s) (eToRow κ e) R T := by
  unfold hybLWE hybq
  congr 2
  ext i j
  dsimp only
  rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, bEquiv_apply,
    sample_apply]
  simp only [pofEquiv_apply, sToRow, eToRow]
  rw [mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem fin_ell_val (i : Fin (ell κ)) : i.val = 0 := by
  have := i.isLt; simp only [ell] at this; omega

theorem sampleMat_eq {α : Type} [Inhabited α] (d : PMF α) (r c : ℕ) :
    sampleMat d r c = (sampleList d (r * c)).map (fun l => Matrix.of fun (i : Fin r) (j : Fin c) =>
      l.getD (i.val * c + j.val) default) := rfl

theorem gaussS_map :
    (gaussMat κ (ell κ) (n κ)).map (fun S => S.map (Int.cast : ℤ → ZMod (q κ))) =
      (lweSecret κ).map (sToRow κ) := by
  unfold gaussMat lweSecret LWE.gaussVec ModuleLWE.gaussVec
  rw [sampleMat_eq, sampleMat_eq, PMF.map_comp, PMF.map_comp, PMF.map_comp,
    show ell κ * n κ = n κ * 1 by simp [ell]]
  congr 1
  funext l
  ext i j
  simp [sToRow, fin_ell_val κ i]

theorem gaussE_map :
    (gaussMat κ (ell κ) (k κ)).map (intMod (q κ)) = (lweError κ).map (eToRow κ) := by
  unfold gaussMat lweError LWE.gaussVec ModuleLWE.gaussVec
  rw [sampleMat_eq, sampleMat_eq, PMF.map_comp, PMF.map_comp, PMF.map_comp,
    show ell κ * k κ = k κ * 1 by simp [ell]]
  congr 1
  funext l
  ext i j
  simp [eToRow, intMod, fin_ell_val κ i]

/-- A real LWE pair gives the hybrid with the error. -/
theorem real_hyb (h : Bool) :
    (ModuleLWE.sampleLaw (lweSecret κ) (lweError κ)).bind (fun pair => inner κ pair h) =
      Yd κ h true := by
  refine pmf_ext_ev fun f => ?_
  have hY : ev (Yd κ h true) f = ev (PMF.uniformOfFintype (PMat κ)) fun P =>
      ev ((gaussMat κ (ell κ) (n κ)).map fun S => S.map (Int.cast : ℤ → ZMod (q κ))) fun Sq =>
        ev ((gaussMat κ (ell κ) (k κ)).map (intMod (q κ))) fun Eq =>
          ev (PMF.uniformOfFintype (RMat κ)) fun R =>
            ev (PMF.uniformOfFintype (TMat κ)) fun T => f (hybq κ h P Sq Eq R T) := by
    unfold Yd
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, ev_bind, ev_pure, ev_map, ite_true]
    rfl
  rw [hY, gaussS_map, gaussE_map]
  unfold ModuleLWE.sampleLaw inner
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, ev_bind, ev_pure, ev_map,
    PMF.bind_bind, PMF.pure_bind, Function.comp_def, hybLWE_sample]
  rw [← ev_uniform_equiv (pofEquiv κ), ev_comm]

/-- A Pre2 word with uniform entries. -/
noncomputable def Zu : PMF (List Bool) :=
  (PMF.uniformOfFintype (PMat κ)).bind fun P => (PMF.uniformOfFintype (Row κ)).map (pre2Word κ P)

/-- A uniform LWE pair gives a uniform Pre2 word, whatever `h` is. -/
theorem rand_hyb (h : Bool) :
    (PMF.uniformOfFintype (LWEPair κ)).bind (fun pair => inner κ pair h) = Zu κ := by
  refine pmf_ext_ev fun f => ?_
  unfold inner Zu
  simp only [ev_bind, ev_pure, ev_map]
  rw [ev_comm]
  refine ev_const_of_eq _ fun R => ?_
  rw [ev_comm]
  refine ev_const_of_eq _ fun T => ?_
  have he := ev_uniform_equiv ((pofEquiv κ).trans (Equiv.addRight (if h then Rq κ R else 0))
    |>.prodCongr ((bEquiv κ).trans (Equiv.subRight ((2 : ZMod (q κ)) • Tq κ T))))
    (fun x : PMat κ × Row κ => f (pre2Word κ x.1 x.2))
  exact he.trans (ev_uniform_prod _)

end

end TestCase.EvLWE
