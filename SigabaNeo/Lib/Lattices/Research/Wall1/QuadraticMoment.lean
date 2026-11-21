import SigabaNeo.Lib.Lattices.Research.Wall1.FixedProjection

namespace SigabaNeo.Wall1.QuadraticMoment

abbrev Bits := Fin 4 → Bool
private noncomputable def value (b : Bits) : ℝ := (∑ j, if b j then 1 else 0) - 2

private theorem moment (e : ℕ) (he : e ∈ [1,2,3,4]) :
    ∑ b, value b ^ e = 16 * (if e = 2 then 1 else if e = 4 then 5/2 else 0) := by
  have h := cbd2_bit_moments
  dsimp only at h
  rcases h with ⟨h₁,h₂,h₃,h₄⟩
  simp at he
  let x := fun (b : Bits) ↦ (∑ j, if b j then (1 : ℚ) else 0) - 2
  have hx (b : Bits) : value b = (x b : ℝ) := by simp [x, value]
  have castSum (n : ℕ) : (∑ b, value b ^ n) = ((∑ b, x b ^ n : ℚ) : ℝ) := by
    simp [hx, Rat.cast_sum]
  change ∑ b, x b = 0 at h₁
  change ∑ b, x b ^ 2 = 16 at h₂
  change ∑ b, x b ^ 3 = 0 at h₃
  change ∑ b, x b ^ 4 = 40 at h₄
  rw [castSum]
  rcases he with rfl | rfl | rfl | rfl <;> norm_num [h₁,h₂,h₃,h₄]

variable {N : ℕ}
private theorem peel (i : Fin N) (e : ℕ) (m : ℝ) (hm : ∑ b, value b ^ e = 16*m)
    (f : (Fin N → Bits) → ℝ)
    (hf : ∀ w w' : Fin N → Bits, (∀ j, j ≠ i → w j = w' j) → f w = f w') :
    (∑ w, value (w i) ^ e * f w) = m * ∑ w, f w := by
  let E := (Equiv.funSplitAt i Bits).symm
  let g := fun (r : {j : Fin N // j ≠ i} → Bits) ↦ f (E (fun _ ↦ false, r))
  have hh (b : Bits) (r : {j : Fin N // j ≠ i} → Bits) : f (E (b,r)) = g r := by
    apply hf
    intro j hj
    simp [E, Equiv.funSplitAt, Equiv.piSplitAt, hj]
  rw [← E.sum_comp, ← E.sum_comp f, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [hh]
  have hi (b : Bits) (r : {j : Fin N // j ≠ i} → Bits) : E (b,r) i = b := by
    simp [E, Equiv.funSplitAt, Equiv.piSplitAt]
  simp only [hi, ← Finset.mul_sum, ← Finset.sum_mul, hm, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  norm_num [Bits, Fintype.card_pi]
  ring

private noncomputable def mu (e : ℕ) : ℝ := (∑ b, value b ^ e) / 16

private theorem mu_small (e : ℕ) (he : e ∈ [1,2,3,4]) :
    mu e = (if e = 2 then 1 else if e = 4 then 5/2 else 0) := by
  unfold mu
  rw [moment e he]
  ring

private theorem joint (s : List (Fin N × ℕ)) (hs : (s.map Prod.fst).Nodup) :
    (∑ w : Fin N → Bits, (s.map (fun p ↦ value (w p.1) ^ p.2)).prod) =
    (Fintype.card (Fin N → Bits) : ℝ) * (s.map (fun p ↦ mu p.2)).prod := by
  induction s with
  | nil => simp
  | cons p s ih =>
    rcases p with ⟨i,e⟩
    simp only [List.map_cons, List.nodup_cons] at hs
    simp only [List.map_cons, List.prod_cons]
    rw [peel i e (mu e) (by unfold mu; ring), ih hs.2]
    · ring
    · intro w w' h
      congr 1
      apply List.map_congr_left
      intro p hp
      rw [h p.1 (fun he ↦ hs.1 (List.mem_map.mpr ⟨p,hp,he⟩))]

private abbrev C (N : ℕ) : ℝ := Fintype.card (Fin N → Bits)
private noncomputable def d (i j : Fin N) : ℝ := if i = j then 1 else 0

local macro "evalJoint" s:term : tactic => `(tactic|
   (calc
     _ = _ := Finset.sum_congr rfl (fun w _ ↦ by
       show _ = (List.map (fun p : Fin _ × ℕ ↦ value (w p.1) ^ p.2) $s).prod
       simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one]
       <;> ring)
     _ = _ := joint $s (by simp_all [ne_comm])
     _ = _ := by simp_all [C, d, mu_small, eq_comm] <;> ring_nf <;> simp))

private theorem two (i j : Fin N) :
    (∑ w : Fin N → Bits, value (w i) * value (w j)) = C N * d i j := by
  by_cases hji : j = i
  · subst j
    evalJoint [(i,2)]
  · evalJoint [(i,1), (j,1)]
private theorem four (i j k l : Fin N) :
    (∑ w : Fin N → Bits, value (w i) * value (w j) * value (w k) * value (w l)) = C N * (d i j * d k l + d i k * d j l + d i l * d j k - d i j * d i k * d i l / 2) := by
  by_cases hji : j = i
  · subst j
    by_cases hki : k = i
    · subst k
      by_cases hli : l = i
      · subst l
        evalJoint [(i,4)]
      · evalJoint [(i,3), (l,1)]
    · by_cases hli : l = i
      · subst l
        evalJoint [(i,3), (k,1)]
      · by_cases hlk : l = k
        · subst l
          evalJoint [(i,2), (k,2)]
        · evalJoint [(i,2), (k,1), (l,1)]
  · by_cases hki : k = i
    · subst k
      by_cases hli : l = i
      · subst l
        evalJoint [(i,3), (j,1)]
      · by_cases hlj : l = j
        · subst l
          evalJoint [(i,2), (j,2)]
        · evalJoint [(i,2), (j,1), (l,1)]
    · by_cases hkj : k = j
      · subst k
        by_cases hli : l = i
        · subst l
          evalJoint [(i,2), (j,2)]
        · by_cases hlj : l = j
          · subst l
            evalJoint [(i,1), (j,3)]
          · evalJoint [(i,1), (j,2), (l,1)]
      · by_cases hli : l = i
        · subst l
          evalJoint [(i,2), (j,1), (k,1)]
        · by_cases hlj : l = j
          · subst l
            evalJoint [(i,1), (j,2), (k,1)]
          · by_cases hlk : l = k
            · subst l
              evalJoint [(i,1), (j,1), (k,2)]
            · evalJoint [(i,1), (j,1), (k,1), (l,1)]

private noncomputable def z (w : Fin N → Bits) (i j : Fin N) := value (w i) * value (w j) - d i j

private theorem cov (i j k l : Fin N) :
    (∑ w, z w i j * z w k l) =
    C N * (d i k * d j l + d i l * d j k - d i j * d i k * d i l / 2) := by
  simp only [z, sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← mul_assoc, four, two, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp_rw [mul_assoc (d i j), ← Finset.mul_sum, two]
  unfold C
  ring

private theorem sumSquare {α β : Type} [Fintype α] [Fintype β] (p : β → ℝ) (f : α → β → ℝ) :
    (∑ w, (∑ i, p i * f w i)^2) = ∑ i, p i * ∑ j, p j * ∑ w, f w i * f w j := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext i
  rw [Finset.sum_comm]
  congr 1
  funext j
  exact Finset.sum_congr rfl (fun _ _ ↦ by ring)

theorem quadraticSecondMoment (N : ℕ) (P : Matrix (Fin N) (Fin N) ℝ)
    (symm : P.transpose = P) :
    let x := fun (ω : Fin N → Fin 4 → Bool) (i : Fin N) ↦
      (∑ j, if ω i j then (1 : ℝ) else 0) - 2
    (∑ ω, ((∑ i, x ω i * (∑ j, P i j * x ω j)) - P.trace)^2) =
      (Fintype.card (Fin N → Fin 4 → Bool) : ℝ) *
        (2 * (∑ i, ∑ j, P i j ^ 2) - (∑ i, P i i ^ 2) / 2) := by
  let p := fun a : Fin N × Fin N ↦ P a.1 a.2
  let f := fun (w : Fin N → Bits) (a : Fin N × Fin N) ↦ z w a.1 a.2
  have expand (w : Fin N → Bits) :
      (∑ i, value (w i) * ∑ j, P i j * value (w j)) - P.trace = ∑ a, p a * f w a := by
    simp [p, f, z, d, Matrix.trace, Fintype.sum_prod_type, mul_sub, Finset.sum_sub_distrib,
      Finset.mul_sum, mul_ite, mul_left_comm]
  change (∑ w : Fin N → Bits, ((∑ i, value (w i) * ∑ j, P i j * value (w j)) - P.trace)^2) = _
  simp_rw [expand]
  rw [sumSquare]
  simp only [f, p, Fintype.sum_prod_type, cov]
  have sym (i j : Fin N) : P j i = P i j := congrFun (congrFun symm i) j
  have contract (i j : Fin N) :
      (∑ k, ∑ l, P k l * (C N * (d i k * d j l + d i l * d j k -
        d i j * d i k * d i l / 2))) =
      C N * (2 * P i j - (if i = j then P i i / 2 else 0)) := by
    have pairing (a b : Fin N) : (∑ k, d a k * ∑ l, d b l * P k l) = P a b := by
      simp [d, ite_mul]
    have distribute (k l : Fin N) :
        P k l * (C N * (d i k * d j l + d i l * d j k - d i j * d i k * d i l / 2)) =
        C N * (d i k * (d j l * P k l) + d j k * (d i l * P k l) -
          (d i j / 2) * (d i k * (d i l * P k l))) := by ring
    simp only [distribute, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      pairing]
    rw [sym i j]
    by_cases h : i = j <;> simp [d, h] <;> ring
  simp_rw [contract]
  change _ = C N * _
  have distribute (i j : Fin N) :
      P i j * (C N * (2 * P i j - (if i = j then P i i / 2 else 0))) =
      C N * (2 * P i j ^ 2 - (if i = j then P i i ^ 2 else 0) / 2) := by
    split_ifs with h <;> subst_vars <;> ring
  simp only [distribute, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end SigabaNeo.Wall1.QuadraticMoment
