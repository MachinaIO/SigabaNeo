import PE.Impl.DualUse.Prog.RowSimP
import PE.Impl.DualUse.Prog.UBLoop
import SigabaNeo.Lib.Machines.Prog.PhaseB
import PE.Impl.DualUse.Prog.KeyPTime

/-!
# Per-tape bounds of the helper programs

Phases (`XProg.Ph X β T β'`: from per-tape bounds below `β`, at most `T` steps, bounds below `β'`
afterwards) for the blocks of `bfX`, `cfX` and the front of `KeyGen`, `Dec`:

* `ph_of_ub_ws`: a uniform bound (`UB`) on the tapes a program writes, the others kept;
* `ph_loop_iter`: a loop from per-round bounds `B j`;
* `ph_moveP`, `ph_zerosP`, `ph_dropP`: the counted moves (the target grows by the counter);
* `ph_wLoopP`, `ph_skipLoopP`: the row loops;
* `ph_ifBlank`, `ph_ifBit`, `ph_clearL`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

variable {k : ℕ}

/-- **A uniform bound on the tapes written**, the other tapes kept. -/
theorem ph_of_ub_ws {X : XProg k} (ws : List (Fin k)) (hpres : ∀ i, i ∉ ws → X.Preserves i)
    {M T M' : ℕ} (hub : UB X M T M') {β : Fin k → ℕ} (hβ : ∀ i, β i ≤ M) :
    Ph X β T (fun i => if i ∈ ws then M' else β i) := fun ℓ hℓ => by
  have h := hub ℓ (fun i => (hℓ i).trans (hβ i))
  refine ⟨h.1, fun i => ?_⟩
  by_cases hi : i ∈ ws
  · simp only [hi, if_true]; exact h.2 i
  · simp only [hi, if_false]
    rw [lenBoundT_of_preserves X i (hpres i hi) ℓ]; exact hℓ i

theorem supB_update_le (β : Fin k → ℕ) (i : Fin k) (v : ℕ) :
    supB (Function.update β i v) ≤ max (supB β) v := by
  refine supB_le_of fun j => ?_
  rw [Function.update_apply]; split_ifs
  · exact le_max_right _ _
  · exact (le_supB β j).trans (le_max_left _ _)

/-- **A loop from per-round bounds**: round `j` runs from below `B j` to below `B (j + 1)`. -/
theorem ph_loop_iter {X : XProg k} (i : Fin k) {β : Fin k → ℕ} (B : ℕ → Fin k → ℕ)
    (Bf : Fin k → ℕ) (Tb R : ℕ) (h0 : β ≤ B 0)
    (hstep : ∀ j < β i, Ph X (B j) Tb (B (j + 1))) (hfin : ∀ j ≤ β i, B j ≤ Bf)
    (hR : ∀ j < β i, 2 * supB (B j) + 3 + Tb ≤ R) :
    Ph (.loop i X) β (β i * (R + 1) + 2) Bf := fun ℓ hℓ => by
  have hℓi : ℓ i ≤ β i := hℓ i
  have hit : ∀ j ≤ ℓ i, (loopStepT i X)^[j] ℓ ≤ B j := by
    intro j hj
    induction j with
    | zero => exact hℓ.trans h0
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      have hj' : j < β i := by omega
      exact (hstep j hj' _ ((tailB_le i _).trans (ih (by omega)))).2
  refine ⟨?_, ?_⟩
  · refine (timeBoundT_loop_le i X ℓ (R := R) fun j hj => ?_).trans ?_
    · have hj' : j < β i := by omega
      have h1 := hit j (by omega)
      have h2 := (hstep j hj' _ ((tailB_le i _).trans h1)).1
      have h3 := supB_mono h1
      have := hR j hj'
      simp only [Prog.roundTimeT]
      omega
    · exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hℓi) 2
  · exact iterSupT_le fun j hj => (hit j hj).trans (hfin j (by omega))

theorem ph_ifBlank' {X Y : XProg k} {β β1 β2 : Fin k → ℕ} {T U : ℕ} (i : Fin k)
    (hX : Ph X β T β1) (hY : Ph Y β U β2) :
    Ph (.ifBlank i X Y) β (max T U + 1) (fun t => max (β1 t) (β2 t)) := fun ℓ hℓ =>
  ⟨Nat.add_le_add_right (max_le_max (hX ℓ hℓ).1 (hY ℓ hℓ).1) 1,
    fun t => max_le_max ((hX ℓ hℓ).2 t) ((hY ℓ hℓ).2 t)⟩

theorem ph_ifBit' {X Y : XProg k} {β β1 β2 : Fin k → ℕ} {T U : ℕ} (i : Fin k)
    (hX : Ph X β T β1) (hY : Ph Y β U β2) :
    Ph (.ifBit i X Y) β (max T U + 1) (fun t => max (β1 t) (β2 t)) := fun ℓ hℓ =>
  ⟨Nat.add_le_add_right (max_le_max (hX ℓ hℓ).1 (hY ℓ hℓ).1) 1,
    fun t => max_le_max ((hX ℓ hℓ).2 t) ((hY ℓ hℓ).2 t)⟩

/-! ### Counted moves -/

/-- The bound of a counted move: the counter `c` at `β t`, the target `r` grown by `β t`. -/
def mvB (β : Fin k → ℕ) (r c t : Fin k) : Fin k → ℕ :=
  Function.update (Function.update β c (β t)) r (β r + β t)

/-- The time of a counted move. -/
def mvT (β : Fin k → ℕ) (t : Fin k) : ℕ := (β t + 1) * (6 * (supB β + β t) + 20)

/-- A counted loop whose body appends one bit to `r` (and may shorten other tapes). -/
theorem ph_cntLoop {body : XProg k} {r c t : Fin k} (hrc : r ≠ c) (hct : c ≠ t)
    (hb : ∀ γ : Fin k → ℕ, Ph body γ (4 * supB γ + 12) (Function.update γ r (γ r + 1)))
    (β : Fin k → ℕ) :
    Ph (forN c t body) β (mvT β t) (mvB β r c t) := by
  have hprim := ph_prim (.copy c t) β
  set β1 := (Prim.copy c t).lenT β with hβ1
  have e1 : β1 = Function.update β c (β t) := rfl
  have hβ1t : β1 c = β t := by rw [e1]; simp
  let B : ℕ → Fin k → ℕ := fun j => Function.update β1 r (β1 r + j)
  have hBr : β1 r = β r := by rw [e1, Function.update_of_ne hrc]
  have hsup : ∀ j ≤ β t, supB (B j) ≤ supB β + β t := by
    intro j hj
    refine (supB_update_le _ _ _).trans (max_le ?_ ?_)
    · rw [e1]; refine (supB_update_le _ _ _).trans (max_le (by omega) ?_)
      have := le_supB β t; omega
    · rw [hBr]; have := le_supB β r; omega
  have hl := ph_loop_iter (X := body) c (β := β1) B (B (β t)) (4 * (supB β + β t) + 12)
    (6 * (supB β + β t) + 15) (fun x => by simp [B]) (fun (j : ℕ) hj => by
      refine (hb (B j)).mono le_rfl ?_ ?_
      · have := hsup j (by omega); omega
      · intro x; simp only [B, Function.update_apply]; split_ifs <;> omega)
    (fun (j : ℕ) hj x => by simp only [B, Function.update_apply]; split_ifs <;> omega)
    (fun (j : ℕ) hj => by have := hsup j (by rw [hβ1t] at hj; omega); omega)
  refine (hprim.seq hl).mono le_rfl ?_ ?_
  · rw [hβ1t, mvT]
    have : supB β ≤ supB β + β t := by omega
    nlinarith
  · intro x
    simp only [B, mvB, e1, Function.update_apply]
    split_ifs <;> simp_all

theorem ph_twoPrims (p q : Prim k) (hp : p.pad ≤ 1) (hq : q.pad ≤ 1) {r : Fin k}
    (hlen : ∀ γ : Fin k → ℕ, q.lenT (p.lenT γ) ≤ Function.update γ r (γ r + 1))
    (hgrow : ∀ γ : Fin k → ℕ, supB (p.lenT γ) ≤ supB γ + 1) (γ : Fin k → ℕ) :
    Ph (.seq (.prog (.prim p)) (.prog (.prim q))) γ (4 * supB γ + 12) (Function.update γ r (γ r + 1)) :=
  ((ph_prim p γ).seq (ph_prim q _)).mono le_rfl (by have := hgrow γ; omega) (hlen γ)

/-- **A counted move** `r := r ++ take |t| S`. -/
theorem ph_moveP {r S c t : Fin k} (hrS : r ≠ S) (hrc : r ≠ c) (hSc : S ≠ c) (hct : c ≠ t)
    (β : Fin k → ℕ) : Ph (moveP r S c t) β (mvT β t) (mvB β r c t) := by
  refine ph_cntLoop hrc hct (fun γ => ph_twoPrims _ _ (by simp [Prim.pad]) (by simp [Prim.pad])
    (fun γ x => ?_) (fun γ => ?_) γ) β
  · simp only [Prim.lenT, Function.update_apply]
    by_cases h1 : x = S
    · subst h1; simp [hrS.symm]
    · by_cases h2 : x = r
      · subst h2; simp [hrS]
      · simp [h1, h2]
  · refine supB_le_of fun j => ?_
    simp only [Prim.lenT, Function.update_apply]; split_ifs
    · have := le_supB γ r; omega
    · have := le_supB γ j; omega

/-- **Counted zeros** `r := r ++ replicate |t| false`. -/
theorem ph_zerosP {r c t : Fin k} (hrc : r ≠ c) (hct : c ≠ t) (β : Fin k → ℕ) :
    Ph (zerosP r c t) β (mvT β t) (mvB β r c t) := by
  refine ph_cntLoop hrc hct (fun γ => ((ph_prim (.snoc r false) γ).mono le_rfl
    (by simp [Prim.pad]; omega) (fun x => le_rfl))) β

theorem mvT_mono {β γ : Fin k → ℕ} (h : β ≤ γ) (t : Fin k) : mvT β t ≤ mvT γ t := by
  have h1 : supB β ≤ supB γ := supB_mono h
  have h2 : β t ≤ γ t := h t
  unfold mvT
  exact Nat.mul_le_mul (by omega) (by omega)

theorem mvB_le {β : Fin k → ℕ} {r c t : Fin k} {G : Fin k → ℕ} (hβ : β ≤ G)
    (hc : β t ≤ G c) (hr : β r + β t ≤ G r) : mvB β r c t ≤ G := by
  intro x
  simp only [mvB, Function.update_apply]
  split_ifs with h1 h2
  · subst h1; exact hr
  · subst h2; exact hc
  · exact hβ x

/-! ### The row loops -/

/-- The per-round bound of `wLoopP`. -/
def wB (β : Fin k → ℕ) (out x c c' tn tz tr : Fin k) (j : ℕ) : Fin k → ℕ :=
  fun t => if t = out then β out + j * (β tz + β tr)
    else if t = x then max (β x) (β tz)
    else if t = c' then max (β c') (max (β tz) (β tr))
    else if t = c then β tn else β t

/-- The largest bound of `wLoopP`. -/
def wS (β : Fin k → ℕ) (tn tz tr : Fin k) : ℕ := supB β + β tn * (β tz + β tr) + β tz + β tr

/-- The time of one move of `wLoopP`. -/
def wQ (β : Fin k → ℕ) (tn tz tr : Fin k) : ℕ :=
  (β tz + β tr + 1) * (6 * (wS β tn tz tr + 2 * (β tz + β tr)) + 20)

/-- The time of `wLoopP`. -/
def wT (β : Fin k → ℕ) (tn tz tr : Fin k) : ℕ :=
  (β tn + 1) * (3 * wQ β tn tz tr + 4 * wS β tn tz tr + 2 * (β tz + β tr) + 12)

theorem wB_le_S {β : Fin k → ℕ} {out x c c' tn tz tr : Fin k} {j : ℕ} (hj : j ≤ β tn) (t : Fin k) :
    wB β out x c c' tn tz tr j t ≤ wS β tn tz tr := by
  have h1 := le_supB β t
  have h2 := le_supB β out
  have h3 := le_supB β x
  have h4 := le_supB β c'
  have h5 := le_supB β tn
  have h6 : j * (β tz + β tr) ≤ β tn * (β tz + β tr) := Nat.mul_le_mul_right _ hj
  simp only [wB, wS]
  split_ifs <;> omega

theorem mvT_le_of {γ : Fin k → ℕ} {t : Fin k} {X v : ℕ} (hγ : ∀ s, γ s ≤ X) (ht : γ t = v) {E : ℕ}
    (hv : v ≤ E) : mvT γ t ≤ (E + 1) * (6 * (X + E) + 20) := by
  unfold mvT
  have := supB_le_of hγ
  rw [ht]
  exact Nat.mul_le_mul (by omega) (by omega)

/-- **The `W`-part loop**: the output grows by `|tz| + |tr|` per round. -/
theorem ph_wLoopP {out f x c c' tn tz tr : Fin k} (hd : [out, f, x, c, c', tn, tz, tr].Nodup)
    (β : Fin k → ℕ) :
    Ph (wLoopP out f x c c' tn tz tr) β (wT β tn tz tr) (wB β out x c c' tn tz tr (β tn)) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h03, h04, h05, h06, h07⟩, ⟨h12, h13, h14, h15, h16, h17⟩,
    ⟨h23, h24, h25, h26, h27⟩, ⟨h34, h35, h36, h37⟩, ⟨h45, h46, h47⟩, ⟨h56, h57⟩, h67, -⟩ := hd
  set S := wS β tn tz tr with hSdef
  set E := β tz + β tr with hEdef
  set Q := wQ β tn tz tr with hQdef
  have hprim := ph_prim (.copy c tn) β
  have e1 : (Prim.copy c tn).lenT β = Function.update β c (β tn) := rfl
  have hB0 : (Prim.copy c tn).lenT β ≤ wB β out x c c' tn tz tr 0 := by
    intro t; rw [e1]; simp only [wB, Function.update_apply]
    split_ifs <;> simp_all
  have hc1 : (Prim.copy c tn).lenT β c = β tn := by rw [e1, Function.update_self]
  have hstep : ∀ j < (Prim.copy c tn).lenT β c, Ph (XProg.seq (XProg.moveP out x c' tz)
      (XProg.seq (XProg.prog (.prim (.clear x))) (XProg.seq (XProg.zerosP x c' tz)
        (XProg.moveP out f c' tr)))) (wB β out x c c' tn tz tr j)
      (3 * Q + 2 * (S + E + 1) + 3) (wB β out x c c' tn tz tr (j + 1)) := by
    intro j hj
    rw [hc1] at hj
    set γ := wB β out x c c' tn tz tr j with hγ
    have gz : γ tz = β tz := by simp [γ, wB, Ne.symm h06, Ne.symm h26, Ne.symm h46, Ne.symm h36]
    have gr : γ tr = β tr := by simp [γ, wB, Ne.symm h07, Ne.symm h27, Ne.symm h47, Ne.symm h37]
    have go : γ out = β out + j * E := by
      show wB β out x c c' tn tz tr j out = _
      simp only [wB, ↓reduceIte]
      rfl
    have hS : ∀ t, γ t ≤ S := wB_le_S (by omega)
    have hjE : j * E + E ≤ β tn * E := by
      have := Nat.mul_le_mul_right E (show j + 1 ≤ β tn by omega); rw [Nat.add_mul] at this; omega
    have hSo : β out + β tn * E ≤ S := by
      have := le_supB β out; simp only [hSdef, wS, hEdef]; omega
    set γ1 := mvB γ out c' tz
    set γ2 := (Prim.clear x).lenT γ1
    set γ3 := mvB γ2 x c' tz
    have g1 : ∀ t, γ1 t ≤ S + E := by
      intro t; simp only [γ1, mvB, Function.update_apply]
      split_ifs with h1 h2
      · subst h1; rw [go, gz]; omega
      · rw [gz]; omega
      · have := hS t; omega
    have g2 : ∀ t, γ2 t ≤ S + E := by
      intro t; simp only [γ2, Prim.lenT, Function.update_apply]; split_ifs
      · omega
      · exact g1 t
    have g3 : ∀ t, γ3 t ≤ S + E := by
      intro t; simp only [γ3, mvB, Function.update_apply]
      have z2 : γ2 tz = β tz := by
        simp [γ2, γ1, mvB, Prim.lenT, Function.update_apply, Ne.symm h26, Ne.symm h46, Ne.symm h06, gz]
      have x2 : γ2 x = 0 := by simp [γ2, Prim.lenT]
      split_ifs with h1 h2
      · subst h1; rw [x2, z2]; omega
      · rw [z2]; omega
      · exact g2 t
    have p1 := ph_moveP h02 h04 h24 h46 γ
    have p2 := ph_prim (Prim.clear x) γ1
    have p3 := ph_zerosP h24 h46 γ2
    have p4 := ph_moveP h01 h04 h14 h47 γ3
    refine (p1.seq (p2.seq (p3.seq p4))).mono le_rfl ?_ ?_
    · have q1 : mvT γ tz ≤ Q := by
        refine (mvT_le_of (X := S + E) (fun t => (hS t).trans (by omega)) gz (E := E)
          (by omega)).trans ?_
        simp only [hQdef, wQ, ← hSdef, ← hEdef]; exact Nat.mul_le_mul le_rfl (by omega)
      have q3 : mvT γ2 tz ≤ Q := by
        have z2 : γ2 tz = β tz := by
          simp [γ2, γ1, mvB, Prim.lenT, Function.update_apply, Ne.symm h26, Ne.symm h46,
            Ne.symm h06, gz]
        refine (mvT_le_of g2 z2 (E := E) (by omega)).trans ?_
        simp only [hQdef, wQ, ← hSdef, ← hEdef]; exact Nat.mul_le_mul le_rfl (by omega)
      have q4 : mvT γ3 tr ≤ Q := by
        have r3 : γ3 tr = β tr := by
          simp [γ3, γ2, γ1, mvB, Prim.lenT, Function.update_apply, Ne.symm h27, Ne.symm h47,
            Ne.symm h07, gr]
        refine (mvT_le_of g3 r3 (E := E) (by omega)).trans ?_
        simp only [hQdef, wQ, ← hSdef, ← hEdef]; exact Nat.mul_le_mul le_rfl (by omega)
      have s1 := supB_le_of g1
      omega
    · intro t
      have z2 : γ2 tz = β tz := by
        simp [γ2, γ1, mvB, Prim.lenT, Function.update_apply, Ne.symm h26, Ne.symm h46, Ne.symm h06, gz]
      have r3 : γ3 tr = β tr := by
        simp [γ3, γ2, γ1, mvB, Prim.lenT, Function.update_apply, Ne.symm h27, Ne.symm h47,
          Ne.symm h07, gr]
      have v3 : γ3 out = β out + j * E + β tz := by
        simp only [γ3, γ2, γ1, mvB, Prim.lenT, Function.update_apply, if_neg h02, if_neg h04,
          ↓reduceIte, go, gz]
      have x3 : γ3 x = β tz := by
        simp only [γ3, mvB, Function.update_apply, ↓reduceIte, z2]
        simp [γ2, Prim.lenT]
      have o3 : ∀ s, s ≠ out → s ≠ x → s ≠ c' → γ3 s = γ s := by
        intro s hs1 hs2 hs3
        simp only [γ3, γ2, γ1, mvB, Prim.lenT, Function.update_apply, if_neg hs1, if_neg hs2,
          if_neg hs3]
      simp only [mvB, Function.update_apply]
      by_cases ho : t = out
      · rw [if_pos ho, ho, v3, r3]
        simp only [wB, ↓reduceIte]
        have e1 : j * E = j * (β tz + β tr) := rfl
        have e2 : (j + 1) * (β tz + β tr) = j * (β tz + β tr) + (β tz + β tr) := by ring
        omega
      · rw [if_neg ho]
        by_cases hc' : t = c'
        · rw [if_pos hc', r3, hc']
          simp only [wB, if_neg (Ne.symm h04), if_neg (Ne.symm h24), ↓reduceIte]
          omega
        · rw [if_neg hc']
          by_cases hx : t = x
          · rw [hx, x3]
            simp only [wB, if_neg (Ne.symm h02), ↓reduceIte]
            omega
          · rw [o3 t ho hx hc']
            simp only [γ, wB, if_neg ho, if_neg hx, if_neg hc']
            exact le_rfl
  have hl := ph_loop_iter c (β := (Prim.copy c tn).lenT β) (wB β out x c c' tn tz tr)
    (wB β out x c c' tn tz tr (β tn)) _ (2 * S + 3 + (3 * Q + 2 * (S + E + 1) + 3)) hB0 hstep
    (fun j hj t => by
      rw [hc1] at hj
      have : j * (β tz + β tr) ≤ β tn * (β tz + β tr) := Nat.mul_le_mul_right _ hj
      simp only [wB]; split_ifs <;> omega)
    (fun j hj => by
      rw [hc1] at hj
      have := supB_le_of (wB_le_S (β := β) (out := out) (x := x) (c := c) (c' := c') (tn := tn)
        (tz := tz) (tr := tr) (j := j) (by omega))
      omega)
  refine (hprim.seq hl).mono le_rfl ?_ le_rfl
  rw [hc1]
  have : supB β ≤ S := by simp only [hSdef, wS]; omega
  simp only [wT, ← hSdef, ← hEdef, ← hQdef]
  nlinarith

/-! ### Clearing and reading blocks -/

theorem ph_clearL [NeZero k] (l : List (Fin k)) (β : Fin k → ℕ) :
    Ph (clearL l) β (l.length * (2 * (supB β + 1) + 3) + (2 * (supB β + 1) + 3))
      (fun t => if t ∈ l then 0 else β t) := fun ℓ hℓ =>
  ⟨((ub_clearL (supB β) l) ℓ (fun i => (hℓ i).trans (le_supB β i))).1,
    fun t => (lenBoundT_clearL_le l ℓ t).trans (by
      have h' : ℓ t ≤ β t := hℓ t
      split_ifs <;> simp_all)⟩

theorem preserves_iter {z t : Fin k} {p : Prog k} (hp : p.Preserves t) (hz : z ≠ t) :
    ∀ n, (Prog.iter z p n).Preserves t
  | 0 => by simp [Prog.iter, Prog.Preserves, Prim.writes, Ne.symm hz]
  | n + 1 => ⟨hp, preserves_iter hp hz n⟩

theorem preserves_tailsP {i t : Fin k} (h : i ≠ t) : ∀ n, (Prog.tailsP i n).Preserves t
  | 0 => by simp [Prog.tailsP, Prog.Preserves, Prim.writes, Ne.symm h]
  | n + 1 => ⟨by simp [Prog.Preserves, Prim.writes, Ne.symm h], preserves_tailsP h n⟩

theorem preserves_prefP {P : ℕ} {src dst a b t : Fin k} (ha : a ≠ t) (hd : dst ≠ t) (hb : b ≠ t) :
    (prefP P src dst a b).Preserves t := by
  refine ⟨by simp [XProg.Preserves, Prog.Preserves, Prim.writes, Ne.symm ha], ?_,
    by simp [XProg.Preserves, Prog.Preserves, Prim.writes, Ne.symm ha]⟩
  show (Prog.iter a (Prog.stepF a dst b) P).Preserves t
  refine preserves_iter ?_ ha P
  exact ⟨by simp [Prog.Preserves, Prim.writes, Ne.symm ha, Ne.symm hb],
    by simp [Prog.Preserves, Prim.writes, Ne.symm hd], by simp [Prog.Preserves, Prim.writes, Ne.symm hb]⟩

/-- The time of `getAt`. -/
def getT (o L M : ℕ) : ℕ :=
  (2 * (M + 1) + 3) + (o + 1) * (2 * (M + 1) + 3) + prefT L M + (2 * (M + 1 + L + 1) + 3)

theorem ub_getAt (o L : ℕ) (src dst tmp a b : Fin k) (M : ℕ) :
    UB (getAt o L src dst tmp a b) M (getT o L M) (M + 1 + L) := by
  have h1 : UB (XProg.prog (Prog.seq (.prim (.copy tmp src)) (Prog.tailsP tmp o))) M
      ((2 * (M + 1) + 3) + (o + 1) * (2 * (M + 1) + 3)) M := fun ℓ hℓ => by
    have u := (Prog.ubp_prim0 (.copy tmp src) rfl M).seq (Prog.ubp_tailsP tmp o M) ℓ hℓ
    exact u
  have u := h1.seq ((ub_prefP L tmp dst a b M).seq (ub_clear tmp (M + 1 + L)))
  exact u.mono (by simp only [getT]; omega) le_rfl

/-- **Reading a block**, per tape: the four tapes written below `supB β + 1 + L`. -/
theorem ph_getAt (o L : ℕ) {src dst tmp a b : Fin k} (h1 : tmp ≠ a) (h2 : tmp ≠ b)
    (β : Fin k → ℕ) :
    Ph (getAt o L src dst tmp a b) β (getT o L (supB β))
      (fun i => if i ∈ [tmp, dst, a, b] then supB β + 1 + L else β i) := by
  refine ph_of_ub_ws _ (fun i hi => ?_) (ub_getAt o L src dst tmp a b (supB β)) (le_supB β)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
  obtain ⟨n1, n2, n3, n4⟩ := hi
  refine ⟨⟨by simp [Prog.Preserves, Prim.writes, n1], preserves_tailsP (Ne.symm n1) o⟩,
    preserves_prefP (Ne.symm n3) (Ne.symm n2) (Ne.symm n4),
    by simp [XProg.Preserves, Prog.Preserves, Prim.writes, n1]⟩

/-! ### The reading loop -/

/-- The per-round bound of `skipLoopP`. -/
def skB (β : Fin k → ℕ) (out c c' tn tz tr : Fin k) (j : ℕ) : Fin k → ℕ :=
  fun t => if t = out then β out + j * β tr
    else if t = c' then max (β c') (max (β tz) (β tr))
    else if t = c then β tn else β t

/-- The largest bound of `skipLoopP`. -/
def skS (β : Fin k → ℕ) (tn tz tr : Fin k) : ℕ := supB β + β tn * β tr + β tz + β tr

/-- The time of `skipLoopP`. -/
def skT (β : Fin k → ℕ) (tn tz tr : Fin k) : ℕ :=
  (β tn + 1) * (2 * ((β tz + β tr + 1) * (6 * (skS β tn tz tr + 2 * (β tz + β tr)) + 20)) +
    4 * skS β tn tz tr + 2 * (β tz + β tr) + 12)

/-- A counted drop. -/
theorem ph_dropP {S c t : Fin k} (hSc : S ≠ c) (hct : c ≠ t) (β : Fin k → ℕ) :
    Ph (dropP S c t) β (mvT β t) (Function.update β c (β t)) := by
  have hprim := ph_prim (.copy c t) β
  have e1 : (Prim.copy c t).lenT β = Function.update β c (β t) := rfl
  have hl := ph_loop_iter c (β := (Prim.copy c t).lenT β) (fun _ => Function.update β c (β t))
    (Function.update β c (β t)) (2 * (supB β + β t) + 5) (4 * (supB β + β t) + 8)
    (by rw [e1]) (fun j hj => ((ph_prim (.tail S) _).mono le_rfl ?_ ?_))
    (fun j hj => le_rfl) (fun j hj => ?_)
  · refine (hprim.seq hl).mono le_rfl ?_ le_rfl
    rw [mvT, show (Prim.copy c t).lenT β c = β t by rw [e1, Function.update_self]]
    nlinarith
  · have := supB_update_le β c (β t); have := le_supB β t
    have : supB (Function.update β c (β t)) ≤ supB β + β t := by omega
    omega
  · intro x; simp only [Prim.lenT, Function.update_apply]; split_ifs <;> simp_all
  · have := supB_update_le β c (β t); have := le_supB β t; omega

end AdvancedEncryption.DualUse.Prog
