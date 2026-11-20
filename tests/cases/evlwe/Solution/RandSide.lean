import Solution.RealSide
import Mathlib.Algebra.Field.ZMod

/-!
# The attack rejects random samples often

`rand_count`: fix `S`, `P` and `K` with every column `K_j ≠ 0 (mod q)`. Over uniform `C` and `T`,
the attack accepts at most a `7/8 + 2/(h + 1)` fraction of the samples `(C, K, S·P − 2T)`,
`h = (q − 1)/2`.

The dependency `u` depends only on `K`. Pick `j0 ∈ u`. Only `T[j0] = t` moves
`w_{j0} = (v + 2t) mod q`, `v = C·K_{j0} − (S·P)_{j0}`: the values `t ≤ s = ⌊(2h − v)/2⌋` give
the parity of `v`, the others the opposite parity, so at most `M(v) = max(s + 1, h − s)` of the
`h + 1` values of `t` are accepted. `C·K_{j0}` is uniform over `Z_q`, and the average of `M` is
about `(7/8)(h + 1)`.
-/

namespace TestCase.EvLWE

open SigabaNeo.Lattices

open TestCase TestCase.EvLWE

/-! ### Counting one coordinate -/

/-- The larger parity class of `(v + 2t) mod q`, `t ≤ h`. -/
def Mv (h v : ℕ) : ℕ := max ((2 * h - v) / 2 + 1) (h - (2 * h - v) / 2)

theorem card_parity_le (h v R : ℕ) (hv : v ≤ 2 * h) :
    ((Finset.range (h + 1)).filter fun t => ((v + 2 * t) % (2 * h + 1) + R) % 2 = 0).card ≤
      Mv h v := by
  set s := (2 * h - v) / 2 with hs
  have hsh : s ≤ h := by omega
  have hmod : ∀ t ∈ Finset.range (h + 1), (v + 2 * t) % (2 * h + 1) =
      if t ≤ s then v + 2 * t else v + 2 * t - (2 * h + 1) := by
    intro t ht
    rw [Finset.mem_range] at ht
    split_ifs with h1
    · exact Nat.mod_eq_of_lt (by omega)
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  by_cases hp : (v + R) % 2 = 0
  · calc _ ≤ ((Finset.range (h + 1)).filter fun t => t ≤ s).card := by
          apply Finset.card_le_card
          intro t ht
          simp only [Finset.mem_filter] at ht ⊢
          refine ⟨ht.1, ?_⟩
          by_contra h1
          have := ht.2
          rw [hmod t ht.1, if_neg h1] at this
          omega
      _ = s + 1 := by
          rw [show ((Finset.range (h + 1)).filter fun t => t ≤ s) = Finset.range (s + 1) by
            ext t; simp only [Finset.mem_filter, Finset.mem_range]; omega]
          simp
      _ ≤ Mv h v := le_max_left _ _
  · calc _ ≤ ((Finset.range (h + 1)).filter fun t => s < t).card := by
          apply Finset.card_le_card
          intro t ht
          simp only [Finset.mem_filter] at ht ⊢
          refine ⟨ht.1, ?_⟩
          by_contra h1
          have := ht.2
          rw [hmod t ht.1, if_pos (by omega)] at this
          omega
      _ = h - s := by
          rw [show ((Finset.range (h + 1)).filter fun t => s < t) = Finset.Ioo s (h + 1) by
            ext t; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]; omega]
          simp; omega
      _ ≤ Mv h v := le_max_right _ _

/-- The average of `Mv` over `v < q` is at most `(7/8)(h + 1) + 2`. -/
theorem sum_Mv_le (h : ℕ) :
    8 * ∑ v ∈ Finset.range (2 * h + 1), Mv h v ≤ 7 * (2 * h + 1) * (h + 1) + 16 * (2 * h + 1) := by
  set q := 2 * h + 1
  let mid : ℕ → Prop := fun v => h / 2 ≤ v ∧ v ≤ 3 * h / 2
  have hpt : ∀ v ∈ Finset.range q, Mv h v ≤ if mid v then 3 * h / 4 + 2 else h + 1 := by
    intro v hv
    rw [Finset.mem_range] at hv
    unfold Mv mid
    split_ifs <;> omega
  have hcard : ((Finset.range q).filter mid).card = 3 * h / 2 + 1 - h / 2 := by
    rw [show (Finset.range q).filter mid = Finset.Icc (h / 2) (3 * h / 2) by
      ext v; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, mid]; omega]
    simp
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.range q) mid
  rw [Finset.card_range] at hsplit
  have hsum : ∑ v ∈ Finset.range q, (if mid v then 3 * h / 4 + 2 else h + 1) =
      ((Finset.range q).filter mid).card * (3 * h / 4 + 2) +
        ((Finset.range q).filter fun v => ¬ mid v).card * (h + 1) := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
  have hle := Finset.sum_le_sum hpt
  rw [hsum, hcard] at hle
  set N := 3 * h / 2 + 1 - h / 2
  set N' := ((Finset.range q).filter fun v => ¬ mid v).card
  have hN : h ≤ N := by omega
  have hNq : N + N' = q := by rw [← hcard]; exact hsplit
  have h34 : 4 * (3 * h / 4) ≤ 3 * h := by omega
  set x := 3 * h / 4
  have hq : q = 2 * h + 1 := rfl
  have e1 : 8 * (N * x) ≤ 6 * (N * h) := by nlinarith
  have e2 : h * h ≤ N * h := Nat.mul_le_mul_right h hN
  have e3 : N' * h + N * h = q * h := by rw [← add_mul, add_comm, hNq]
  have e4 : q * h = 2 * (h * h) + h := by rw [hq]; ring
  have hle' : ∑ i ∈ Finset.range q, Mv h i ≤ N * x + 2 * N + (N' * h + N') := by
    have : N * (x + 2) + N' * (h + 1) = N * x + 2 * N + (N' * h + N') := by ring
    omega
  have e5 : 7 * q * (h + 1) + 16 * q = 7 * (q * h) + 23 * q := by ring
  rw [e5]
  omega

/-! ### Balanced maps -/

/-- If every shift of the values of `φ` is realized by a permutation of the domain, the values
are equidistributed: `|G| · Σ_x F(φ x) = |α| · Σ_g F g`. -/
theorem sum_balanced {α G : Type*} [Fintype α] [DecidableEq G] [Fintype G] [AddCommGroup G]
    (φ : α → G) (hφ : ∀ δ : G, ∃ e : α ≃ α, ∀ x, φ (e x) = φ x + δ) (F : G → ℕ) :
    Fintype.card G * ∑ x, F (φ x) = Fintype.card α * ∑ g, F g := by
  classical
  have hfib : ∀ g, (Finset.univ.filter fun x => φ x = g).card =
      (Finset.univ.filter fun x => φ x = 0).card := by
    intro g
    obtain ⟨e, he⟩ := hφ g
    refine (Finset.card_bij (fun x _ => e.symm x) ?_ ?_ ?_).symm.symm
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have h1 := he (e.symm x)
      rw [Equiv.apply_symm_apply, hx] at h1
      simpa using h1.symm
    · intro a _ b _ h; exact e.symm.injective h
    · intro y hy
      refine ⟨e y, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [he, hy, zero_add]
  have hsum : ∑ x, F (φ x) = ∑ g, (Finset.univ.filter fun x => φ x = g).card * F g := by
    rw [← Finset.sum_fiberwise Finset.univ φ (fun x => F (φ x))]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2], Finset.sum_const,
      smul_eq_mul]
  have hcard : Fintype.card α = Fintype.card G * (Finset.univ.filter fun x => φ x = 0).card := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := φ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    simp only [hfib, Finset.sum_const, smul_eq_mul, Finset.card_univ]
  rw [hsum, hcard]
  simp only [hfib, ← Finset.mul_sum]
  ring

theorem sum_zmod_val (q : ℕ) [NeZero q] (f : ℕ → ℕ) :
    ∑ a : ZMod q, f a.val = ∑ i ∈ Finset.range q, f i := by
  refine Finset.sum_bij (fun a _ => a.val) (fun a _ => Finset.mem_range.mpr (ZMod.val_lt a))
    (fun a _ b _ h => ZMod.val_injective q h) (fun i hi => ⟨(i : ZMod q), Finset.mem_univ _, ?_⟩)
    (fun _ _ => rfl)
  exact ZMod.val_cast_of_lt (Finset.mem_range.mp hi)

theorem card_fin_filter (N : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    (Finset.univ.filter fun t : Fin N => Q t.val).card = ((Finset.range N).filter Q).card := by
  refine Finset.card_bij (fun t _ => t.val) ?_ (fun a _ b _ h => Fin.ext h) ?_
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at ht ⊢
    exact ⟨t.isLt, ht⟩
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨⟨i, hi.1⟩, by simpa using hi.2, rfl⟩

/-! ### The dependency depends only on `K` -/

section
variable {κ : ℕ}

theorem kBit_postWord_eq (C C' : Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ)))
    (Kq : Matrix (Fin (m κ)) (Fin (k κ)) (ZMod (q κ)))
    (A A' : Matrix (Fin (ell κ)) (Fin (k κ)) (ZMod (q κ))) {r j : ℕ} (hr : r < m κ)
    (hj : j < k κ) : kBit κ (postWord C Kq A) r j = kBit κ (postWord C' Kq A') r j := by
  have h1 : kAt κ (postWord C Kq A) r j = (Kq ⟨r, hr⟩ ⟨j, hj⟩).val :=
    kAt_postWord C Kq A ⟨r, hr⟩ ⟨j, hj⟩
  have h2 : kAt κ (postWord C' Kq A') r j = (Kq ⟨r, hr⟩ ⟨j, hj⟩).val :=
    kAt_postWord C' Kq A' ⟨r, hr⟩ ⟨j, hj⟩
  unfold kBit
  rw [qOf_postWord, qOf_postWord, h1, h2]

theorem depMask_postWord_eq (C C' : Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ)))
    (Kq : Matrix (Fin (m κ)) (Fin (k κ)) (ZMod (q κ)))
    (A A' : Matrix (Fin (ell κ)) (Fin (k κ)) (ZMod (q κ))) :
    depMask κ (postWord C Kq A) = depMask κ (postWord C' Kq A') := by
  have hcol : ∀ j < m κ + 1, colVec κ (postWord C Kq A) j = colVec κ (postWord C' Kq A') j := by
    intro j hj
    unfold colVec
    congr 1
    refine List.map_congr_left fun r hr => ?_
    rw [kBit_postWord_eq C C' Kq A A' (List.mem_range.mp hr) hj]
  have key : ∀ (l : List ℕ) (st : List (ℕ × ℕ × ℕ) × ℕ), (∀ j ∈ l, j < m κ + 1) →
      l.foldl (elimStep κ (postWord C Kq A)) st = l.foldl (elimStep κ (postWord C' Kq A')) st := by
    intro l
    induction l with
    | nil => intro st _; rfl
    | cons j l ih =>
      intro st hl
      simp only [List.foldl_cons]
      have he : elimStep κ (postWord C Kq A) st j = elimStep κ (postWord C' Kq A') st j := by
        unfold elimStep; rw [hcol j (hl j (List.mem_cons_self ..))]
      rw [he]
      exact ih _ fun i hi => hl i (List.mem_cons_of_mem _ hi)
  unfold depMask
  rw [key _ _ fun j hj => List.mem_range.mp hj]

/-- The attack's `wAt` on a Post sample. -/
theorem wAt_val (C : Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ)))
    (Kq : Matrix (Fin (m κ)) (Fin (k κ)) (ZMod (q κ)))
    (A : Matrix (Fin (ell κ)) (Fin (k κ)) (ZMod (q κ))) (j : Fin (k κ)) :
    wAt κ (postWord C Kq A) j = ((∑ r, C (i0 κ) r * Kq r j) - A (i0 κ) j).val := by
  have hq : 0 < q κ := Nat.pos_of_ne_zero (NeZero.ne _)
  have hsum : ((List.range (m κ)).map fun r =>
      cAt κ (postWord C Kq A) r * kAt κ (postWord C Kq A) r j).sum =
      ∑ r : Fin (m κ), (C (i0 κ) r).val * (Kq r j).val := by
    rw [listSum_range', Finset.sum_range]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [cAt_postWord, kAt_postWord]
  have haux := auxAt_postWord C Kq A j
  have hlt : auxAt κ (postWord C Kq A) j ≤ q κ := haux ▸ (ZMod.val_lt _).le
  unfold wAt
  rw [qOf_postWord, hsum]
  set n := (∑ r : Fin (m κ), (C (i0 κ) r).val * (Kq r j).val +
    (q κ - auxAt κ (postWord C Kq A) j)) % q κ
  have hn : (n : ZMod (q κ)) = (∑ r, C (i0 κ) r * Kq r j) - A (i0 κ) j := by
    rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub hlt, haux, Nat.cast_sum]
    simp [ZMod.natCast_val, sub_eq_add_neg]
  rw [← hn, ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.mod_lt _ hq)]

theorem parityOut_eq (word : List Bool) :
    parityOut κ word = decide ((∑ j : Fin (k κ),
      if (depMask κ word).testBit j then wAt κ word j else 0) % 2 = 0) := by
  unfold parityOut
  rw [listSum_range', show m κ + 1 = k κ from rfl, Finset.sum_range]

end

/-! ### The count -/

section
variable {κ : ℕ}

/-- `aux = S·P − 2T`, as in `Draw.aux`. -/
noncomputable def auxOf (S : Matrix (Fin (ell κ)) (Fin (n κ)) ℤ)
    (P : Matrix (Fin (n κ)) (Fin (k κ)) (ZMod (q κ)))
    (T : Matrix (Fin (ell κ)) (Fin (k κ)) (Fin ((q κ - 1) / 2 + 1))) :
    Matrix (Fin (ell κ)) (Fin (k κ)) (ZMod (q κ)) :=
  (S.map fun a => (a : ZMod (q κ))) * P - (2 : ZMod (q κ)) • T.map fun t => ((t : ℕ) : ZMod (q κ))

theorem aux_eq_auxOf (d : Draw κ) : d.aux = auxOf d.S d.P d.T := rfl

theorem eq_i0 (i : Fin (ell κ)) : i = i0 κ := Fin.ext (by have := i.isLt; simp [ell] at this; simp [i0]; omega)

/-- Set entry `j0` of `T`. -/
def upd (j0 : Fin (k κ)) (T : Matrix (Fin (ell κ)) (Fin (k κ)) (Fin ((q κ - 1) / 2 + 1)))
    (t : Fin ((q κ - 1) / 2 + 1)) : Matrix (Fin (ell κ)) (Fin (k κ)) (Fin ((q κ - 1) / 2 + 1)) :=
  Matrix.of fun i j => if j = j0 then t else T i j

/-- `(h + 1) · #{T | Q T} = Σ_T #{t | Q (T with entry j0 set to t)}`. -/
theorem card_upd (j0 : Fin (k κ))
    (Q : Matrix (Fin (ell κ)) (Fin (k κ)) (Fin ((q κ - 1) / 2 + 1)) → Prop) [DecidablePred Q] :
    ((q κ - 1) / 2 + 1) * (Finset.univ.filter Q).card =
      ∑ T, (Finset.univ.filter fun t => Q (upd j0 T t)).card := by
  classical
  let e : Matrix (Fin (ell κ)) (Fin (k κ)) (Fin ((q κ - 1) / 2 + 1)) × Fin ((q κ - 1) / 2 + 1) ≃
      Matrix (Fin (ell κ)) (Fin (k κ)) (Fin ((q κ - 1) / 2 + 1)) × Fin ((q κ - 1) / 2 + 1) :=
    { toFun := fun p => (upd j0 p.1 p.2, p.1 (i0 κ) j0)
      invFun := fun p => (upd j0 p.1 p.2, p.1 (i0 κ) j0)
      left_inv := fun p => by
        ext i j <;> simp only [upd, Matrix.of_apply]
        · split_ifs with h
          · subst h; rw [eq_i0 i]
          · rfl
        · simp
      right_inv := fun p => by
        ext i j <;> simp only [upd, Matrix.of_apply]
        · split_ifs with h
          · subst h; rw [eq_i0 i]
          · rfl
        · simp }
  have h1 : ∑ T, (Finset.univ.filter fun t => Q (upd j0 T t)).card =
      ∑ p : _ × Fin ((q κ - 1) / 2 + 1), if Q (e p).1 then 1 else 0 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.card_filter]
    rfl
  rw [h1, Equiv.sum_comp e (fun p => if Q p.1 then 1 else 0), Fintype.sum_prod_type,
    Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  split_ifs <;> simp [mul_comm]

theorem q_eq_two_h (κ : ℕ) : q κ = 2 * ((q κ - 1) / 2) + 1 := by have := q_odd κ; omega

/-- Over uniform `C` and `T`, the attack accepts at most a `7/8 + 2/(h + 1)` fraction. -/
theorem rand_count (S : Matrix (Fin (ell κ)) (Fin (n κ)) ℤ)
    (P : Matrix (Fin (n κ)) (Fin (k κ)) (ZMod (q κ)))
    (Kq : Matrix (Fin (m κ)) (Fin (k κ)) (ZMod (q κ))) (hK : ∀ j, (fun r => Kq r j) ≠ 0) :
    8 * ((q κ - 1) / 2 + 1) *
      (Finset.univ.filter fun x : Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ)) ×
        Matrix (Fin (ell κ)) (Fin (k κ)) (Fin ((q κ - 1) / 2 + 1)) =>
          parityOut κ (postWord x.1 Kq (auxOf S P x.2)) = true).card ≤
      (7 * ((q κ - 1) / 2 + 1) + 16) *
        (Fintype.card (Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ))) *
          Fintype.card (Matrix (Fin (ell κ)) (Fin (k κ)) (Fin ((q κ - 1) / 2 + 1)))) := by
  classical
  set h := (q κ - 1) / 2 with hh
  have hq : q κ = 2 * h + 1 := q_eq_two_h κ
  set u := depMask κ (postWord 0 Kq 0) with hudef
  have hu : ∀ C A, depMask κ (postWord C Kq A) = u := fun C A => depMask_postWord_eq C 0 Kq A 0
  obtain ⟨hu0, hu1, -⟩ := depMask_spec κ (postWord 0 Kq 0)
  obtain ⟨j0n, hj0⟩ := Nat.exists_testBit_of_ne_zero hu0
  have hj0lt : j0n < k κ := by
    by_contra hc
    have : u < 2 ^ j0n := lt_of_lt_of_le hu1 (Nat.pow_le_pow_right (by norm_num) (by
      rw [k_eq] at hc; omega))
    rw [Nat.testBit_eq_false_of_lt this] at hj0; exact absurd hj0 (by simp)
  set j0 : Fin (k κ) := ⟨j0n, hj0lt⟩
  obtain ⟨r0, hr0'⟩ := Function.ne_iff.mp (hK j0)
  have hr0 : Kq r0 j0 ≠ 0 := by simpa using hr0'
  set c0 := ((S.map fun a => (a : ZMod (q κ))) * P) (i0 κ) j0
  let v : Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ)) → ZMod (q κ) :=
    fun C => (∑ r, C (i0 κ) r * Kq r j0) - c0
  let R : Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ)) →
      Matrix (Fin (ell κ)) (Fin (k κ)) (Fin (h + 1)) → ℕ := fun C T =>
    ∑ j ∈ Finset.univ.erase j0, if u.testBit j then wAt κ (postWord C Kq (auxOf S P T)) j else 0
  -- the acceptance condition
  have hacc : ∀ C T, parityOut κ (postWord C Kq (auxOf S P T)) = true ↔
      (((v C).val + 2 * (T (i0 κ) j0).val) % q κ + R C T) % 2 = 0 := by
    intro C T
    rw [parityOut_eq, hu, decide_eq_true_iff, ← Finset.add_sum_erase _ _ (Finset.mem_univ j0)]
    have hw : wAt κ (postWord C Kq (auxOf S P T)) j0 = ((v C).val + 2 * (T (i0 κ) j0).val) % q κ := by
      rw [wAt_val]
      have : (∑ r, C (i0 κ) r * Kq r j0) - auxOf S P T (i0 κ) j0 =
          v C + ((2 * (T (i0 κ) j0).val : ℕ) : ZMod (q κ)) := by
        simp only [auxOf, v, c0, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
        push_cast; ring
      have h2t : 2 * (T (i0 κ) j0).val < q κ := by have := (T (i0 κ) j0).isLt; omega
      rw [this, ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt h2t]
    rw [show (j0 : ℕ) = j0n from rfl, if_pos hj0] at *
    rw [hw]
  -- entries other than `j0` do not move `R`
  have hR : ∀ C T t, R C (upd j0 T t) = R C T := by
    intro C T t
    refine Finset.sum_congr rfl fun j hj => ?_
    have hne := Finset.ne_of_mem_erase hj
    rw [wAt_val, wAt_val]
    congr 3
    simp only [auxOf, upd, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply,
      if_neg hne]
  have hupd0 : ∀ T t, (upd j0 T t) (i0 κ) j0 = t := fun T t => by simp [upd]
  -- per `C`
  have hC : ∀ C, (h + 1) * (Finset.univ.filter fun T : Matrix (Fin (ell κ)) (Fin (k κ))
      (Fin (h + 1)) => parityOut κ (postWord C Kq (auxOf S P T)) = true).card ≤
      Fintype.card (Matrix (Fin (ell κ)) (Fin (k κ)) (Fin (h + 1))) * Mv h (v C).val := by
    intro C
    rw [card_upd j0, ← smul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    refine Finset.sum_le_sum fun T _ => ?_
    have e1 : (Finset.univ.filter fun t => parityOut κ (postWord C Kq (auxOf S P (upd j0 T t)))
        = true) = Finset.univ.filter fun t : Fin (h + 1) =>
          (((v C).val + 2 * t.val) % (2 * h + 1) + R C T) % 2 = 0 := by
      ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hacc, hR, hupd0, ← hq]
    rw [e1, card_fin_filter (h + 1) (fun t => (((v C).val + 2 * t) % (2 * h + 1) + R C T) % 2 = 0)]
    exact card_parity_le h _ _ (by have := ZMod.val_lt (v C); omega)
  -- the uniform `C`
  have hbal : q κ * ∑ C, Mv h (v C).val =
      Fintype.card (Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ))) *
        ∑ i ∈ Finset.range (q κ), Mv h i := by
    have := sum_balanced v ?_ (fun a => Mv h a.val)
    · rw [ZMod.card, sum_zmod_val] at this; exact this
    intro δ
    let D : Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ)) :=
      Matrix.of fun _ r => if r = r0 then δ / Kq r0 j0 else 0
    refine ⟨Equiv.addRight D, fun C => ?_⟩
    simp only [v, Equiv.coe_addRight, Matrix.add_apply, add_mul, Finset.sum_add_distrib, D,
      Matrix.of_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      div_mul_cancel₀ _ hr0]
    ring
  have hsumC := Finset.sum_le_sum fun C (_ : C ∈ Finset.univ) => hC C
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hsumC
  have htot : (Finset.univ.filter fun x : Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ)) ×
        Matrix (Fin (ell κ)) (Fin (k κ)) (Fin (h + 1)) =>
          parityOut κ (postWord x.1 Kq (auxOf S P x.2)) = true).card =
      ∑ C, (Finset.univ.filter fun T : Matrix (Fin (ell κ)) (Fin (k κ)) (Fin (h + 1)) =>
        parityOut κ (postWord C Kq (auxOf S P T)) = true).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    simp only [Finset.card_filter]
  have hM := sum_Mv_le h
  rw [← hq] at hM
  set NT := Fintype.card (Matrix (Fin (ell κ)) (Fin (k κ)) (Fin (h + 1)))
  set NC := Fintype.card (Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ)))
  set cnt := (Finset.univ.filter fun x : Matrix (Fin (ell κ)) (Fin (m κ)) (ZMod (q κ)) ×
        Matrix (Fin (ell κ)) (Fin (k κ)) (Fin (h + 1)) =>
          parityOut κ (postWord x.1 Kq (auxOf S P x.2)) = true).card
  set SM := ∑ C, Mv h (v C).val
  set SR := ∑ i ∈ Finset.range (q κ), Mv h i
  -- `q (h+1) cnt ≤ NT · q · SM = NT · NC · SR`
  have h1 : (h + 1) * cnt ≤ NT * SM := by rw [htot]; exact hsumC
  have hqpos : 0 < q κ := by omega
  have h2 : q κ * (8 * (h + 1) * cnt) ≤ q κ * ((7 * (h + 1) + 16) * (NC * NT)) := by
    calc q κ * (8 * (h + 1) * cnt) = 8 * NT * 0 + 8 * (q κ * ((h + 1) * cnt)) := by ring
      _ ≤ 8 * (q κ * (NT * SM)) := by nlinarith
      _ = NT * (8 * (q κ * SM)) := by ring
      _ = NT * (NC * (8 * SR)) := by rw [hbal]; ring
      _ ≤ NT * (NC * (7 * q κ * (h + 1) + 16 * q κ)) := by gcongr
      _ = q κ * ((7 * (h + 1) + 16) * (NC * NT)) := by ring
  exact Nat.le_of_mul_le_mul_left h2 hqpos

end

end TestCase.EvLWE
