import SigabaNeo.Lib.Machines.Prog.LenEq
import SigabaNeo.Lib.Machines.Prog.UBP

/-!
# Per-tape bounds of the append macros

Bounds on `timeBoundT` and `lenBoundT` (from per-tape bounds `ℓ`, all below `S`) of `appT`,
`dropT`, `natU` and `lenEqP`, and a loop lemma over a family of bounds (`loop_family`): a loop of at
most `R` rounds whose round `j` maps the bounds `γ j` into `γ (j + 1)`.
-/

namespace SigabaNeo.Tape

namespace Prog

open scoped Prog

variable {k : ℕ}

/-- **A loop along a family of bounds.** -/
theorem loop_family (c : Fin k) (body : Prog k) (γ : ℕ → Fin k → ℕ) (R T : ℕ) (ℓ : Fin k → ℕ)
    (h0 : ℓ ≤ γ 0) (hc : ℓ c ≤ R)
    (hstep : ∀ j < R, lenBoundT body (tailB c (γ j)) ≤ γ (j + 1))
    (htime : ∀ j < R, 2 * supB (γ j) + 3 + timeBoundT body (tailB c (γ j)) ≤ T)
    (hmono : ∀ j ≤ R, γ j ≤ γ R) :
    timeBoundT (loop c body) ℓ ≤ R * (T + 1) + 2 ∧ lenBoundT (loop c body) ℓ ≤ γ R := by
  have hit : ∀ j, j ≤ R → (loopStepT c body)^[j] ℓ ≤ γ j := by
    intro j
    induction j with
    | zero => intro _; simpa using h0
    | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply']
      exact (lenBoundT_mono body (tailB_mono c (ih (by omega)))).trans (hstep j (by omega))
  refine ⟨?_, ?_⟩
  · refine (timeBoundT_loop_le c body ℓ (R := T) fun j hj => ?_).trans ?_
    · have h1 := hit j (by omega)
      show 2 * supB _ + 3 + timeBoundT body _ ≤ _
      have h2 := supB_mono h1
      have h3 := timeBoundT_mono body (tailB_mono c h1)
      have := htime j (by omega)
      omega
    · have := Nat.mul_le_mul_right (T + 1) hc
      omega
  · rw [lenBoundT_loop]
    exact iterSupT_le fun j hj => (hit j (by omega)).trans (hmono j (by omega))

theorem supB_le_of {ℓ : Fin k → ℕ} {S : ℕ} (h : ∀ t, ℓ t ≤ S) : supB ℓ ≤ S :=
  Finset.sup_le fun t _ => h t

/-- **The bounds of `appT`** (`x` may be `o`). -/
theorem appT_bounds {o x a b : Fin k} (hoa : o ≠ a) (hob : o ≠ b) (hab : a ≠ b) (hxa : x ≠ a)
    (hxb : x ≠ b) (ℓ : Fin k → ℕ) {S : ℕ} (hS : ∀ t, ℓ t ≤ S) (hS' : ℓ o + ℓ x ≤ S) :
    timeBoundT (appT o x a b) ℓ ≤ (4 * ℓ x + 6) * (2 * S + 5) ∧
      ∀ t, lenBoundT (appT o x a b) ℓ t ≤
        if t = o then ℓ o + ℓ x else if t = a then ℓ x else if t = b then 0 else ℓ t := by
  set q := ℓ x with hq
  set p := ℓ o with hp
  let ℓ1 : Fin k → ℕ := Function.update ℓ b q
  let ℓ2 : Fin k → ℕ := Function.update ℓ1 a q
  have e1 : lenBoundT (prim (.copy b x)) ℓ = ℓ1 := rfl
  have e2 : lenBoundT (prim (.copy a x)) ℓ1 = ℓ2 := by
    show Function.update ℓ1 a (ℓ1 x) = _
    simp only [ℓ1, ℓ2, Function.update_of_ne hxb]; rfl
  let γ : ℕ → Fin k → ℕ := fun j => Function.update ℓ2 o (p + j)
  have hγ : ∀ j t, j ≤ q → γ j t ≤ S := by
    intro j t hj
    simp only [γ, ℓ2, ℓ1, Function.update_apply]
    split_ifs <;> first | omega | exact hS t
  have hl := loop_family a (appBody o b) γ q (3 * (2 * S + 5)) ℓ2
    (fun t => by
      simp only [γ, ℓ2, ℓ1, Function.update_apply]
      split_ifs with h1 h2 <;> (try subst_vars) <;> simp_all)
    (by simp [ℓ2])
    (fun j hj t => by
      show Prim.lenT (.tail b) (Prim.lenT (.snocHead o b) (tailB a (γ j))) t ≤ γ (j + 1) t
      simp only [Prim.lenT, tailB, γ, ℓ2, ℓ1, Function.update_apply]
      split_ifs <;> omega)
    (fun j hj => by
      show 2 * supB (γ j) + 3 + (2 * (supB (tailB a (γ j)) + 1) + 3 +
        (2 * (supB (Prim.lenT (.snocHead o b) (tailB a (γ j))) + 0) + 3)) ≤ _
      have h1 := supB_le_of fun t => hγ j t (by omega)
      have h2 : supB (tailB a (γ j)) ≤ S := supB_le_of fun t => (tailB_le a _ t).trans (hγ j t (by omega))
      have h3 : supB (Prim.lenT (.snocHead o b) (tailB a (γ j))) ≤ S := supB_le_of fun t => by
        simp only [Prim.lenT, tailB, γ, ℓ2, ℓ1, Function.update_apply]
        split_ifs <;> first | omega | exact hS t
      omega)
    (fun j hj t => by
      simp only [γ, Function.update_apply]; split_ifs <;> omega)
  have hS0 := supB_le_of hS
  have hℓ1 : ∀ t, ℓ1 t ≤ S := fun t => by
    simp only [ℓ1, Function.update_apply]; split_ifs <;> first | omega | exact hS t
  have hL : ∀ t, lenBoundT (loop a (appBody o b)) ℓ2 t ≤ S := fun t =>
    (hl.2 t).trans (hγ q t le_rfl)
  have t1 : timeBoundT (prim (.copy b x)) ℓ ≤ 2 * S + 5 := by
    show 2 * (supB ℓ + 0) + 3 ≤ _; omega
  have t2 : timeBoundT (prim (.copy a x)) ℓ1 ≤ 2 * S + 5 := by
    show 2 * (supB ℓ1 + 0) + 3 ≤ _; have := supB_le_of hℓ1; omega
  have t4 : timeBoundT (prim (.clear b)) (lenBoundT (loop a (appBody o b)) ℓ2) ≤ 2 * S + 5 := by
    show 2 * (supB _ + 0) + 3 ≤ _; have := supB_le_of hL; omega
  refine ⟨?_, fun t => ?_⟩
  · show timeBoundT (prim (.copy b x)) ℓ + ((timeBoundT (prim (.copy a x)) (lenBoundT (prim (.copy b x)) ℓ) +
      timeBoundT (loop a (appBody o b)) (lenBoundT (prim (.copy a x)) (lenBoundT (prim (.copy b x)) ℓ))) +
      timeBoundT (prim (.clear b)) (lenBoundT (loop a (appBody o b))
        (lenBoundT (prim (.copy a x)) (lenBoundT (prim (.copy b x)) ℓ)))) ≤ _
    rw [e1, e2]
    have := hl.1
    nlinarith
  · show Prim.lenT (.clear b) (lenBoundT (loop a (appBody o b))
      (lenBoundT (prim (.copy a x)) (lenBoundT (prim (.copy b x)) ℓ))) t ≤ _
    rw [e1, e2]
    have h := hl.2 t
    simp only [Prim.lenT, Function.update_apply] at h ⊢
    simp only [γ, ℓ2, ℓ1, Function.update_apply] at h
    split_ifs at h ⊢ <;> first | omega | (subst_vars; omega) | simp_all

/-- **The bounds of `dropT`.** -/
theorem dropT_bounds {t x a : Fin k} (hta : t ≠ a) (hxa : x ≠ a) (ℓ : Fin k → ℕ) {S : ℕ}
    (hS : ∀ u, ℓ u ≤ S) :
    timeBoundT (dropT t x a) ℓ ≤ (3 * ℓ x + 3) * (2 * S + 5) ∧
      lenBoundT (dropT t x a) ℓ ≤ Function.update ℓ a (ℓ x) := by
  let ℓ1 : Fin k → ℕ := Function.update ℓ a (ℓ x)
  have hℓ1 : ∀ u, ℓ1 u ≤ S := fun u => by
    simp only [ℓ1, Function.update_apply]; split_ifs <;> exact hS _
  have hl := loop_family a (tl t) (fun _ => ℓ1) (ℓ x) (2 * (2 * S + 5)) ℓ1 le_rfl
    (by simp [ℓ1]) (fun j _ u => by
      show Prim.lenT (.tail t) (tailB a ℓ1) u ≤ ℓ1 u
      simp only [Prim.lenT, tailB, Function.update_apply]; split_ifs <;> subst_vars <;> omega)
    (fun j _ => by
      show 2 * supB ℓ1 + 3 + (2 * (supB (tailB a ℓ1) + 0) + 3) ≤ _
      have := supB_le_of hℓ1
      have : supB (tailB a ℓ1) ≤ S := supB_le_of fun u => (tailB_le a _ u).trans (hℓ1 u)
      omega) (fun _ _ => le_rfl)
  have e1 : lenBoundT (prim (.copy a x)) ℓ = ℓ1 := rfl
  refine ⟨?_, ?_⟩
  · show timeBoundT (prim (.copy a x)) ℓ + timeBoundT (loop a (tl t)) (lenBoundT (prim (.copy a x)) ℓ) ≤ _
    rw [e1]
    have : timeBoundT (prim (.copy a x)) ℓ ≤ 2 * S + 5 := by
      show 2 * (supB ℓ + 0) + 3 ≤ _; have := supB_le_of hS; omega
    nlinarith [hl.1]
  · show lenBoundT (loop a (tl t)) (lenBoundT (prim (.copy a x)) ℓ) ≤ _
    rw [e1]; exact hl.2

/-- **The bounds of `natU`.** -/
theorem natU_bounds {o a b : Fin k} (hoa : o ≠ a) (hob : o ≠ b) (hab : a ≠ b) {S : ℕ} :
    ∀ (n : ℕ) (ℓ : Fin k → ℕ), (∀ u, ℓ u ≤ S) → n ≤ S →
      timeBoundT (natU o a b n) ℓ ≤ (12 * n + 100) * (2 * S + 5) ∧
        ∀ u, lenBoundT (natU o a b n) ℓ u ≤
          if u = o then n else if u = a ∨ u = b then max (ℓ u) n else ℓ u
  | 0, ℓ, hS, _ => by
    rw [natU]
    refine ⟨?_, fun u => ?_⟩
    · show 2 * (supB ℓ + 0) + 3 ≤ _; have := supB_le_of hS; nlinarith
    · show Prim.lenT (.clear o) ℓ u ≤ _
      simp only [Prim.lenT, Function.update_apply]; split_ifs <;> omega
  | n + 1, ℓ, hS, hn => by
    rw [natU]
    split_ifs with h
    · have ih := natU_bounds hoa hob hab ((n + 1) / 2) ℓ hS (by omega)
      let B : Fin k → ℕ := fun u =>
        if u = o then (n + 1) / 2 else if u = a ∨ u = b then max (ℓ u) ((n + 1) / 2) else ℓ u
      have hB : ∀ u, B u ≤ S := fun u => by
        simp only [B]; split_ifs <;> first | omega | exact max_le (hS u) (by omega) | exact hS u
      have hap := appT_bounds hoa hob hab hoa hob B hB (by simp [B]; omega)
      refine ⟨?_, fun u => ?_⟩
      · show timeBoundT (natU o a b ((n + 1) / 2)) ℓ +
          timeBoundT (appT o o a b) (lenBoundT (natU o a b ((n + 1) / 2)) ℓ) ≤ _
        have h1 := timeBoundT_mono (appT o o a b) (show lenBoundT (natU o a b ((n + 1) / 2)) ℓ ≤ B
          from fun u => ih.2 u)
        have hBo : B o = (n + 1) / 2 := by simp [B]
        have h2 := hap.1
        rw [hBo] at h2
        have h3 := ih.1
        have hm : 16 * ((n + 1) / 2) + 106 ≤ 12 * (n + 1) + 100 := by omega
        have := Nat.mul_le_mul_right (2 * S + 5) hm
        calc _ ≤ (12 * ((n + 1) / 2) + 100) * (2 * S + 5) + (4 * ((n + 1) / 2) + 6) * (2 * S + 5) :=
              Nat.add_le_add h3 (h1.trans h2)
          _ = (16 * ((n + 1) / 2) + 106) * (2 * S + 5) := by ring
          _ ≤ _ := this
      · show lenBoundT (appT o o a b) (lenBoundT (natU o a b ((n + 1) / 2)) ℓ) u ≤ _
        refine (lenBoundT_mono (appT o o a b) (fun u => ih.2 u) u).trans ((hap.2 u).trans ?_)
        simp only [B]
        split_ifs <;> first | omega | simp_all | (exact le_max_left _ _)
    · have ih := natU_bounds hoa hob hab n ℓ hS (by omega)
      refine ⟨?_, fun u => ?_⟩
      · show timeBoundT (natU o a b n) ℓ + (2 * (supB (lenBoundT (natU o a b n) ℓ) + 1) + 3) ≤ _
        have : supB (lenBoundT (natU o a b n) ℓ) ≤ S := supB_le_of fun u => (ih.2 u).trans (by
          split_ifs <;> first | omega | exact max_le (hS u) (by omega) | exact hS u)
        nlinarith [ih.1]
      · show Prim.lenT (.snoc o true) (lenBoundT (natU o a b n) ℓ) u ≤ _
        have := ih.2 u
        simp only [Prim.lenT, Function.update_apply]
        split_ifs at this ⊢ <;> first | omega | simp_all
  decreasing_by all_goals omega

/-! ### Relabelled macros -/

theorem map_appT {n : ℕ} (u : Fin n → Fin k) (o x a b : Fin n) :
    Prog.map u (appT o x a b) = appT (u o) (u x) (u a) (u b) := rfl

theorem map_dropT {n : ℕ} (u : Fin n → Fin k) (t x a : Fin n) :
    Prog.map u (dropT t x a) = dropT (u t) (u x) (u a) := rfl

theorem map_natU {n : ℕ} (u : Fin n → Fin k) (o a b : Fin n) :
    ∀ m, Prog.map u (natU o a b m) = natU (u o) (u a) (u b) m
  | 0 => by rw [natU, natU]; rfl
  | m + 1 => by
    rw [natU, natU]
    split_ifs
    · show seq (Prog.map u (natU o a b ((m + 1) / 2))) (Prog.map u (appT o o a b)) = _
      rw [map_natU u o a b ((m + 1) / 2), map_appT]
    · show seq (Prog.map u (natU o a b m)) (prim (Prim.map u (.snoc o true))) = _
      rw [map_natU u o a b m]; rfl
  decreasing_by all_goals omega

/-- **The relabelled length test.** -/
theorem map_lenEqP (u : Fin 6 → Fin k) (n : ℕ) :
    Prog.map u (lenEqP n) = natU (u 2) (u 4) (u 5) n ⨾ cp (u 3) (u 0) ⨾ dropT (u 3) (u 2) (u 4) ⨾
      ifBlank (u 3) (dropT (u 2) (u 0) (u 4) ⨾ ifBlank (u 2) (setB (u 1) true) (setB (u 1) false))
        (setB (u 1) false) ⨾ clr (u 2) ⨾ clr (u 3) := by
  show seq (Prog.map u (natU 2 4 5 n)) _ = _
  rw [map_natU]; rfl

/-- **Moving `n` bits** one at a time (`iter`). -/
theorem iter_mv_bounds {src dst t : Fin k} (z : Fin k) (hsd : src ≠ dst) (hst : src ≠ t)
    (hdt : dst ≠ t) {S : ℕ} : ∀ (n : ℕ) (ℓ : Fin k → ℕ), (∀ u, ℓ u ≤ S) → ℓ dst + n ≤ S → 1 ≤ S →
      timeBoundT (iter z (pp src t ⨾ prim (.snocHead dst t) ⨾ clr t) n) ℓ ≤ (3 * n + 1) * (2 * S + 5) ∧
        ∀ u, lenBoundT (iter z (pp src t ⨾ prim (.snocHead dst t) ⨾ clr t) n) ℓ u ≤
          if u = dst then ℓ dst + n else if u = t then max (ℓ t) 1 else ℓ u
  | 0, ℓ, hS, _, _ => by
    refine ⟨?_, fun u => ?_⟩
    · show 2 * (supB ℓ + 0) + 3 ≤ _; have := supB_le_of hS; omega
    · show Prim.lenT (.copy z z) ℓ u ≤ _
      simp only [Prim.lenT, Function.update_apply]
      split_ifs <;> subst_vars <;> omega
  | n + 1, ℓ, hS, hn, h1 => by
    let ℓ' : Fin k → ℕ := Function.update (Function.update ℓ dst (ℓ dst + 1)) t 0
    have hb : lenBoundT (pp src t ⨾ prim (.snocHead dst t) ⨾ clr t) ℓ ≤ ℓ' := fun u => by
      show Prim.lenT (.clear t) (Prim.lenT (.snocHead dst t) (Prim.lenT (.pop src t) ℓ)) u ≤ _
      simp only [Prim.lenT, ℓ', Function.update_apply]
      split_ifs <;> subst_vars <;> first | omega | simp_all
    have hℓ' : ∀ u, ℓ' u ≤ S := fun u => by
      simp only [ℓ', Function.update_apply]; split_ifs <;> first | omega | exact hS u
    have ih := iter_mv_bounds z hsd hst hdt n ℓ' hℓ' (by simp [ℓ', Function.update_of_ne hdt]; omega) h1
    have hT : timeBoundT (pp src t ⨾ prim (.snocHead dst t) ⨾ clr t) ℓ ≤ 3 * (2 * S + 5) := by
      show 2 * (supB ℓ + 0) + 3 + (2 * (supB (Prim.lenT (.pop src t) ℓ) + 1) + 3 +
        (2 * (supB (Prim.lenT (.snocHead dst t) (Prim.lenT (.pop src t) ℓ)) + 0) + 3)) ≤ _
      have := supB_le_of hS
      have : supB (Prim.lenT (.pop src t) ℓ) ≤ S := supB_le_of fun u => by
        simp only [Prim.lenT, Function.update_apply]
        split_ifs <;> subst_vars <;> first | omega | (have := hS u; omega) | (have := hS src; omega)
      have : supB (Prim.lenT (.snocHead dst t) (Prim.lenT (.pop src t) ℓ)) ≤ S := supB_le_of fun u => by
        simp only [Prim.lenT, Function.update_apply]
        split_ifs <;> subst_vars <;> first | omega | (have := hS u; omega)
      omega
    refine ⟨?_, fun u => ?_⟩
    · show timeBoundT (pp src t ⨾ prim (.snocHead dst t) ⨾ clr t) ℓ +
        timeBoundT (iter z (pp src t ⨾ prim (.snocHead dst t) ⨾ clr t) n)
          (lenBoundT (pp src t ⨾ prim (.snocHead dst t) ⨾ clr t) ℓ) ≤ _
      have := (timeBoundT_mono _ hb).trans ih.1
      nlinarith
    · show lenBoundT (iter z (pp src t ⨾ prim (.snocHead dst t) ⨾ clr t) n)
        (lenBoundT (pp src t ⨾ prim (.snocHead dst t) ⨾ clr t) ℓ) u ≤ _
      refine (lenBoundT_mono _ hb u).trans ((ih.2 u).trans ?_)
      simp only [ℓ', Function.update_apply]
      split_ifs <;> subst_vars <;> first | omega | simp_all

end Prog

end SigabaNeo.Tape
