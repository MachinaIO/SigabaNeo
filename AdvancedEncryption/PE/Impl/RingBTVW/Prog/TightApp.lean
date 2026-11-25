import PE.Impl.RingBTVW.Prog.UBLoop
import PE.Impl.RingBTVW.Prog.SetupP
import SigabaNeoStd.Machines.Prog.VecBound

/-!
# Per-tape bounds of appends

`appendTapeP r a S c` (append tape `a` to `r`) and `frameApP r a S c` (append the frame of `a`) are
loops of `|a|` rounds whose body lengthens `r` by one resp. two bits and shortens the stream `S` by
one. Their iterated per-tape bounds are computed exactly (`iter_app`, `iter_fr`), so:

* `vb_appendTapeP`: from per-tape bounds `ℓ` with every tape and `ℓ r + ℓ a` at most `M`, the
  append costs at most `4 (2M + 3) + ℓ a · (6M + 12) + 2` and ends with `r ↦ ℓ r + ℓ a`,
  `S, a ↦ 0`, `c ↦ ℓ a`, every other tape unchanged;
* `vb_frameApP`: the same with `r ↦ ℓ r + 2 ℓ a + 1` (and `a` unchanged), at most
  `3 (2M + 3) + (2M + 5) + ℓ a · (8M + 17) + 2`, where `ℓ r + 2 ℓ a + 1 ≤ M`.

Here `VB p ℓin T ℓout` (`SigabaNeoStd.Machines.Prog.VecBound`) is the per-tape bound transformer.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

variable {k : ℕ}

/-- A bound proved at the largest input is a `VB` (monotonicity). -/
theorem vb_of_top {p : XProg k} {ℓin ℓout : Fin k → ℕ} {T : ℕ} (hT : timeBoundT p ℓin ≤ T)
    (hL : lenBoundT p ℓin ≤ ℓout) : VB p ℓin T ℓout := fun ℓ hℓ =>
  ⟨(timeBoundT_mono p hℓ).trans hT, (lenBoundT_mono p hℓ).trans hL⟩

theorem supB_le' {ℓ : Fin k → ℕ} {M : ℕ} (h : ∀ t, ℓ t ≤ M) : supB ℓ ≤ M := supB_le_of h

/-! ### Appending a tape -/

/-- The body of the append. -/
abbrev appBody (r S : Fin k) : XProg k :=
  seq (prog (.prim (.snocHead r S))) (prog (.prim (.tail S)))

theorem len_appBody (r S : Fin k) (v : Fin k → ℕ) :
    lenBoundT (appBody r S) v = Function.update (Function.update v r (v r + 1)) S
      (Function.update v r (v r + 1) S - 1) := rfl

theorem iter_app {r S c : Fin k} (hrS : r ≠ S) (hrc : r ≠ c) (hSc : S ≠ c) (ℓ : Fin k → ℕ) :
    ∀ j, (loopStepT c (appBody r S))^[j] ℓ =
      Function.update (Function.update (Function.update ℓ r (ℓ r + j)) S (ℓ S - j)) c (ℓ c - j)
  | 0 => by
    funext t
    simp only [Function.iterate_zero, id, Nat.add_zero, Nat.sub_zero, Function.update_apply]
    split_ifs <;> subst_vars <;> rfl
  | j + 1 => by
    rw [Function.iterate_succ_apply', iter_app hrS hrc hSc ℓ j, loopStepT, len_appBody, tailB]
    funext t
    simp only [Function.update_apply]
    by_cases h1 : t = c
    · subst h1; simp [hrc.symm, hSc.symm]; omega
    · by_cases h2 : t = S
      · subst h2; simp [hrS.symm, hSc]; omega
      · by_cases h3 : t = r
        · subst h3; simp [hrS, hrc]; omega
        · simp [h1, h2, h3]

theorem time_appBody {r S : Fin k} (v : Fin k → ℕ) {M : ℕ} (hv : ∀ t, v t ≤ M)
    (hr : v r + 1 ≤ M) : timeBoundT (appBody r S) v ≤ (2 * (M + 1) + 3) + (2 * M + 3) := by
  show 2 * (supB v + 1) + 3 + (2 * (supB (Function.update v r (v r + 1)) + 0) + 3) ≤ _
  have h1 := supB_le' hv
  have h2 : supB (Function.update v r (v r + 1)) ≤ M := supB_le' fun t => by
    simp only [Function.update_apply]; split_ifs <;> [omega; exact hv t]
  omega

/-- The bounds after the append (`r` grows by `ℓ a`, the scratch stream and `a` cleared, the
counter at `ℓ a`). -/
def appOut (r a S c : Fin k) (ℓ : Fin k → ℕ) : Fin k → ℕ :=
  Function.update (Function.update (Function.update (Function.update ℓ r (ℓ r + ℓ a)) S 0) a 0)
    c (ℓ a)

/-- The time of an append from tapes below `M`, `n` rounds. -/
def appT' (M n : ℕ) : ℕ := 4 * (2 * M + 3) + (n * (6 * M + 12) + 2)

set_option maxHeartbeats 1000000 in
theorem vb_appendTapeP {r a S c : Fin k} (hra : r ≠ a) (hrS : r ≠ S) (hrc : r ≠ c) (haS : a ≠ S)
    (hac : a ≠ c) (hSc : S ≠ c) (ℓ : Fin k → ℕ) {M : ℕ} (hM : ∀ t, ℓ t ≤ M)
    (hr : ℓ r + ℓ a ≤ M) :
    VB (appendTapeP r a S c) ℓ (appT' M (ℓ a)) (appOut r a S c ℓ) := by
  apply vb_of_top
  · -- the two copies
    set ℓ1 := Function.update ℓ S (ℓ a) with hℓ1
    set ℓ2 := Function.update ℓ1 c (ℓ1 a) with hℓ2
    have h1 : ∀ t, ℓ1 t ≤ M := fun t => by
      simp only [hℓ1, Function.update_apply]; split_ifs <;> [exact hM a; exact hM t]
    have h2 : ∀ t, ℓ2 t ≤ M := fun t => by
      simp only [hℓ2, Function.update_apply]; split_ifs <;> [exact h1 a; exact h1 t]
    have e2a : ℓ2 a = ℓ a := by simp [hℓ2, hℓ1, haS, hac]
    have e2c : ℓ2 c = ℓ a := by simp [hℓ2, hℓ1, haS]
    have e2S : ℓ2 S = ℓ a := by simp [hℓ2, hℓ1, hSc]
    have e2r : ℓ2 r = ℓ r := by simp [hℓ2, hℓ1, hrS, hrc]
    -- the iterates
    have hit := iter_app hrS hrc hSc ℓ2
    have hj : ∀ j, j ≤ ℓ a → ∀ t, ((loopStepT c (appBody r S))^[j] ℓ2) t ≤ M := by
      intro j hj t
      rw [hit j]
      simp only [Function.update_apply]
      split_ifs <;> first | omega | exact h2 t
    have hloopT : timeBoundT (loop c (appBody r S)) ℓ2 ≤ ℓ a * (6 * M + 11 + 1) + 2 := by
      rw [← e2c]
      refine timeBoundT_loop_le c _ ℓ2 fun j hjn => ?_
      rw [e2c] at hjn
      unfold Prog.roundTimeT
      have hs := supB_le' (hj j hjn.le)
      have hv : ∀ t, tailB c ((loopStepT c (appBody r S))^[j] ℓ2) t ≤ M :=
        fun t => (tailB_le c _ t).trans (hj j hjn.le t)
      have hr' : tailB c ((loopStepT c (appBody r S))^[j] ℓ2) r + 1 ≤ M := by
        rw [tailB, Function.update_of_ne hrc, hit j]
        simp [hrS, hrc, e2r]; omega
      have := time_appBody (S := S) _ hv hr'
      omega
    have hloopL : lenBoundT (loop c (appBody r S)) ℓ2 ≤ fun t => M := by
      intro t
      exact iterSupT_le (fun j hj' => fun t => hj j (by rw [e2c] at hj'; exact hj') t) t
    show 2 * (supB ℓ + 0) + 3 + (2 * (supB ℓ1 + 0) + 3 + timeBoundT (loop c (appBody r S)) ℓ2 +
      (2 * (supB (lenBoundT (loop c (appBody r S)) ℓ2) + 0) + 3 +
        (2 * (supB (Function.update (lenBoundT (loop c (appBody r S)) ℓ2) S 0) + 0) + 3))) ≤ _
    rw [show 6 * M + 11 + 1 = 6 * M + 12 by omega] at hloopT
    have s0 := supB_le' hM
    have s1 := supB_le' h1
    have s2 := supB_le' hloopL
    have s3 : supB (Function.update (lenBoundT (loop c (appBody r S)) ℓ2) S 0) ≤ M :=
      supB_le' fun t => by
        simp only [Function.update_apply]; split_ifs <;> [omega; exact hloopL t]
    unfold appT'
    omega
  · -- the per-tape bound afterwards
    set ℓ1 := Function.update ℓ S (ℓ a) with hℓ1
    set ℓ2 := Function.update ℓ1 c (ℓ1 a) with hℓ2
    have e2a : ℓ2 a = ℓ a := by simp [hℓ2, hℓ1, haS, hac]
    have e2c : ℓ2 c = ℓ a := by simp [hℓ2, hℓ1, haS]
    have e2S : ℓ2 S = ℓ a := by simp [hℓ2, hℓ1, hSc]
    have e2r : ℓ2 r = ℓ r := by simp [hℓ2, hℓ1, hrS, hrc]
    have hit := iter_app hrS hrc hSc ℓ2
    have hloopL : lenBoundT (loop c (appBody r S)) ℓ2 ≤
        Function.update (Function.update (Function.update ℓ2 r (ℓ r + ℓ a)) S (ℓ a)) c (ℓ a) := by
      refine iterSupT_le fun j hj' => fun t => ?_
      rw [e2c] at hj'
      show ((loopStepT c (appBody r S))^[j] ℓ2) t ≤ _
      rw [hit j]
      simp only [Function.update_apply]
      split_ifs <;> omega
    intro t
    show Function.update (Function.update (lenBoundT (loop c (appBody r S)) ℓ2) S 0) a 0 t ≤ _
    have := hloopL t
    simp only [appOut, Function.update_apply] at this ⊢
    by_cases h1 : t = c
    · subst h1; simp [hac.symm, hSc.symm, hrc.symm] at this ⊢; exact this
    · by_cases h2 : t = a
      · subst h2; simp [h1]
      · by_cases h3 : t = S
        · subst h3; simp [h1, h2]
        · by_cases h4 : t = r
          · subst h4; simp [h1, h2, h3] at this ⊢; exact this
          · simp [h1, h2, h3, h4, hℓ2, hℓ1] at this ⊢; exact this

/-! ### Appending the frame of a tape -/

/-- The body of the framed append. -/
abbrev frBody (r S : Fin k) : XProg k :=
  seq (prog (.prim (.snoc r true))) (seq (prog (.prim (.snocHead r S))) (prog (.prim (.tail S))))

theorem len_frBody (r S : Fin k) (v : Fin k → ℕ) :
    lenBoundT (frBody r S) v =
      let v1 := Function.update v r (v r + 1)
      let v2 := Function.update v1 r (v1 r + 1)
      Function.update v2 S (v2 S - 1) := rfl

theorem iter_fr {r S c : Fin k} (hrS : r ≠ S) (hrc : r ≠ c) (hSc : S ≠ c) (ℓ : Fin k → ℕ) :
    ∀ j, (loopStepT c (frBody r S))^[j] ℓ =
      Function.update (Function.update (Function.update ℓ r (ℓ r + 2 * j)) S (ℓ S - j)) c
        (ℓ c - j)
  | 0 => by
    funext t
    simp only [Function.iterate_zero, id, Nat.mul_zero, Nat.add_zero, Nat.sub_zero,
      Function.update_apply]
    split_ifs <;> subst_vars <;> rfl
  | j + 1 => by
    rw [Function.iterate_succ_apply', iter_fr hrS hrc hSc ℓ j, loopStepT, len_frBody, tailB]
    funext t
    simp only [Function.update_apply]
    by_cases h1 : t = c
    · subst h1; simp [hrc.symm, hSc.symm]; omega
    · by_cases h2 : t = S
      · subst h2; simp [hrS.symm, hSc]; omega
      · by_cases h3 : t = r
        · subst h3; simp [hrS, hrc]; omega
        · simp [h1, h2, h3]

theorem time_frBody {r S : Fin k} (v : Fin k → ℕ) {M : ℕ} (hv : ∀ t, v t ≤ M)
    (hr : v r + 2 ≤ M) :
    timeBoundT (frBody r S) v ≤ (2 * (M + 1) + 3) + ((2 * (M + 1) + 3) + (2 * M + 3)) := by
  show 2 * (supB v + 1) + 3 + (2 * (supB (Function.update v r (v r + 1)) + 1) + 3 +
    (2 * (supB (Function.update (Function.update v r (v r + 1)) r
      (Function.update v r (v r + 1) r + 1)) + 0) + 3)) ≤ _
  have h1 := supB_le' hv
  have h2 : supB (Function.update v r (v r + 1)) ≤ M := supB_le' fun t => by
    simp only [Function.update_apply]; split_ifs <;> [omega; exact hv t]
  have h3 : supB (Function.update (Function.update v r (v r + 1)) r
      (Function.update v r (v r + 1) r + 1)) ≤ M := supB_le' fun t => by
    simp only [Function.update_apply]; split_ifs <;> [simp; exact hv t] <;> omega
  omega

/-- The bounds after the framed append (`r` grows by `2 ℓ a + 1`, the stream cleared, the counter
at `ℓ a`). -/
def frOut (r a S c : Fin k) (ℓ : Fin k → ℕ) : Fin k → ℕ :=
  Function.update (Function.update (Function.update ℓ r (ℓ r + 2 * ℓ a + 1)) S 0) c (ℓ a)

/-- The time of a framed append from tapes below `M`, `n` rounds. -/
def frT' (M n : ℕ) : ℕ := 3 * (2 * M + 3) + (2 * M + 5) + (n * (8 * M + 17) + 2)

set_option maxHeartbeats 1000000 in
theorem vb_frameApP {r a S c : Fin k} (hra : r ≠ a) (hrS : r ≠ S) (hrc : r ≠ c) (haS : a ≠ S)
    (hac : a ≠ c) (hSc : S ≠ c) (ℓ : Fin k → ℕ) {M : ℕ} (hM : ∀ t, ℓ t ≤ M)
    (hr : ℓ r + 2 * ℓ a + 1 ≤ M) :
    VB (frameApP r a S c) ℓ (frT' M (ℓ a)) (frOut r a S c ℓ) := by
  set ℓ1 := Function.update ℓ S (ℓ a) with hℓ1
  set ℓ2 := Function.update ℓ1 c (ℓ1 a) with hℓ2
  have h1 : ∀ t, ℓ1 t ≤ M := fun t => by
    simp only [hℓ1, Function.update_apply]; split_ifs <;> [exact hM a; exact hM t]
  have h2 : ∀ t, ℓ2 t ≤ M := fun t => by
    simp only [hℓ2, Function.update_apply]; split_ifs <;> [exact h1 a; exact h1 t]
  have e2c : ℓ2 c = ℓ a := by simp [hℓ2, hℓ1, haS]
  have e2S : ℓ2 S = ℓ a := by simp [hℓ2, hℓ1, hSc]
  have e2r : ℓ2 r = ℓ r := by simp [hℓ2, hℓ1, hrS, hrc]
  have hit := iter_fr hrS hrc hSc ℓ2
  have hloopL : lenBoundT (loop c (frBody r S)) ℓ2 ≤
      Function.update (Function.update (Function.update ℓ2 r (ℓ r + 2 * ℓ a)) S (ℓ a)) c (ℓ a) := by
    refine iterSupT_le fun j hj' => fun t => ?_
    rw [e2c] at hj'
    show ((loopStepT c (frBody r S))^[j] ℓ2) t ≤ _
    rw [hit j]
    simp only [Function.update_apply]
    split_ifs <;> omega
  have hL : ∀ t, lenBoundT (loop c (frBody r S)) ℓ2 t ≤ M := fun t => by
    have := hloopL t
    simp only [Function.update_apply] at this
    split_ifs at this <;> first | omega | exact this.trans (h2 t)
  apply vb_of_top
  · have hj : ∀ j, j ≤ ℓ a → ∀ t, ((loopStepT c (frBody r S))^[j] ℓ2) t ≤ M := by
      intro j hj t
      rw [hit j]
      simp only [Function.update_apply]
      split_ifs <;> first | omega | exact h2 t
    have hloopT : timeBoundT (loop c (frBody r S)) ℓ2 ≤ ℓ a * (8 * M + 16 + 1) + 2 := by
      rw [← e2c]
      refine timeBoundT_loop_le c _ ℓ2 fun j hjn => ?_
      rw [e2c] at hjn
      unfold Prog.roundTimeT
      have hs := supB_le' (hj j hjn.le)
      have hv : ∀ t, tailB c ((loopStepT c (frBody r S))^[j] ℓ2) t ≤ M :=
        fun t => (tailB_le c _ t).trans (hj j hjn.le t)
      have hr' : tailB c ((loopStepT c (frBody r S))^[j] ℓ2) r + 2 ≤ M := by
        rw [tailB, Function.update_of_ne hrc, hit j]
        simp [hrS, hrc, e2r]; omega
      have := time_frBody (S := S) _ hv hr'
      omega
    rw [show 8 * M + 16 + 1 = 8 * M + 17 by omega] at hloopT
    show 2 * (supB ℓ + 0) + 3 + (2 * (supB ℓ1 + 0) + 3 + timeBoundT (loop c (frBody r S)) ℓ2 +
      (2 * (supB (lenBoundT (loop c (frBody r S)) ℓ2) + 1) + 3 +
        (2 * (supB (Function.update (lenBoundT (loop c (frBody r S)) ℓ2) r
          (lenBoundT (loop c (frBody r S)) ℓ2 r + 1)) + 0) + 3))) ≤ _
    have s0 := supB_le' hM
    have s1 := supB_le' h1
    have s2 := supB_le' hL
    have s3 : supB (Function.update (lenBoundT (loop c (frBody r S)) ℓ2) r
        (lenBoundT (loop c (frBody r S)) ℓ2 r + 1)) ≤ M := supB_le' fun t => by
      have hr2 := hloopL r
      simp only [Function.update_apply, hrS, hrc, ite_true, ite_false] at hr2
      simp only [Function.update_apply]; split_ifs <;> [omega; exact hL t]
    unfold frT'
    omega
  · intro t
    show Function.update (Function.update (lenBoundT (loop c (frBody r S)) ℓ2) r
      (lenBoundT (loop c (frBody r S)) ℓ2 r + 1)) S 0 t ≤ _
    have := hloopL t
    have hr2 := hloopL r
    simp only [Function.update_apply, hrS, hrc, ite_true, ite_false] at hr2
    simp only [frOut, Function.update_apply] at this ⊢
    by_cases h1 : t = c
    · subst h1; simp [hSc.symm, hrc.symm] at this ⊢; exact this
    · by_cases h3 : t = S
      · subst h3; simp [h1]
      · by_cases h4 : t = r
        · subst h4; simp [h1, h3]; omega
        · simp [h1, h3, h4, hℓ2, hℓ1] at this ⊢; exact this

/-! ### Frames -/

theorem embedF_le {m : ℕ} {e : Fin m ↪ Fin k} {a c : Fin k → ℕ} {b : Fin m → ℕ}
    (hb : ∀ j, b j ≤ c (e j)) (ha : ∀ t, a t ≤ c t) : embedF e a b ≤ c := by
  intro t
  rcases embedF_cases e a b t with ⟨-, h⟩ | ⟨j, rfl, h⟩
  · rw [h]; exact ha t
  · rw [h]; exact hb j

open SigabaNeo.Tape.Sym in
/-- **A framed plain program with a checked certificate**: the claimed bounds on the first
`claim.length` tapes of the frame, the top on the others, the tapes outside the frame unchanged. -/
theorem vb_frameChk {m fuel : ℕ} {p : Prog m} {σ claim : Asg} {w : Poly}
    (h : check fuel p σ claim w = true) (ρ : List ℕ) (e : Fin m ↪ Fin k) {a b : Fin k → ℕ}
    (hin : ∀ j, a (e j) ≤ pEval ρ (aGet σ j.val)) (hM : ∀ j, a (e j) ≤ top ρ)
    (hout : ∀ j : Fin m, j.val < claim.length → pEval ρ (aGet claim j.val) ≤ b (e j))
    (hscr : ∀ j : Fin m, claim.length ≤ j.val → top ρ ≤ b (e j))
    (hrest : ∀ t, a t ≤ b t) :
    VB (frame e (prog p)) a ((2 * top ρ + 3) * pEval ρ w) b := by
  intro ℓ hℓ
  obtain ⟨h1, h2, h3⟩ := bounds_of_check h ρ (ℓ := fun j => ℓ (e j))
    (fun j => (hℓ (e j)).trans (hin j)) (fun j => (hℓ (e j)).trans (hM j))
  refine ⟨h3, embedF_le (fun j => ?_) (fun t => (hℓ t).trans (hrest t))⟩
  by_cases hj : j.val < claim.length
  · exact (h1 j hj).trans (hout j hj)
  · exact (h2 j).trans (hscr j (by omega))

/-- **A framed sampler with a shape bound**: the output tape `e 0` grows by `B.a`, the other
tapes of the frame stay below `S + B.s`. -/
theorem vb_smp (e : Fin 7 ↪ Fin k) {p : XProg 7} {B : Bnd} (h : ATBb p B) {ℓ c : Fin k → ℕ}
    {x S : ℕ} (hx : ℓ (e 0) ≤ x) (hS : ∀ j : Fin 7, j ≠ 0 → ℓ (e j) ≤ S) (hS₀ : B.S₀ ≤ S)
    (hc0 : x + B.a ≤ c (e 0)) (hcj : ∀ j : Fin 7, j ≠ 0 → S + B.s ≤ c (e j))
    (hcr : ∀ t, ℓ t ≤ c t) : VB (frame e p) ℓ (B.T x S) c := by
  intro ℓ' hℓ'
  have hsh : (fun j => ℓ' (e j)) ≤ shp (0 : Fin 7) x S := fun j => by
    simp only [shp]
    split_ifs with hj
    · subst hj; exact (hℓ' _).trans hx
    · exact (hℓ' _).trans (hS j hj)
  refine ⟨ATB.time h hS₀ hsh, embedF_le (fun j => ?_) (fun t => (hℓ' t).trans (hcr t))⟩
  have := ((lenBoundT_mono p hsh).trans ((show ATB p 0 B.S₀ B.a B.s B.T from h) x S hS₀).2) j
  simp only [shp] at this
  split_ifs at this with hj
  · subst hj; exact this.trans hc0
  · exact this.trans (hcj j hj)

/-! ### Appending a copy (`appC`) -/

/-- **`appC r a`**: copy `a` to `88`, append `88` to `r`. -/
theorem vb_appC {r a : Fin 96} (h88 : r ≠ 88) (h89 : r ≠ 89) (h90 : r ≠ 90) (ℓ : Fin 96 → ℕ)
    {M : ℕ} (hM : ∀ t, ℓ t ≤ M) (hr : ℓ r + ℓ a ≤ M) :
    VB (appC r a) ℓ ((2 * M + 3) + appT' M (ℓ a))
      (appOut r 88 89 90 (Function.update ℓ 88 (ℓ a))) := by
  have hc : VB (prog (.prim (.copy 88 a))) ℓ (2 * M + 3) (Function.update ℓ 88 (ℓ a)) :=
    vb_of_top (by
      show 2 * (supB ℓ + 0) + 3 ≤ _
      have := supB_le' hM; omega) le_rfl
  have hM' : ∀ t, Function.update ℓ 88 (ℓ a) t ≤ M := fun t => by
    simp only [Function.update_apply]; split_ifs <;> [exact hM a; exact hM t]
  have e88 : Function.update ℓ 88 (ℓ a) 88 = ℓ a := by simp
  have er : Function.update ℓ 88 (ℓ a) r = ℓ r := by simp [h88]
  have := vb_appendTapeP (r := r) (a := 88) (S := 89) (c := 90) h88 h89 h90 (by decide)
    (by decide) (by decide) (Function.update ℓ 88 (ℓ a)) hM' (by rw [e88, er]; exact hr)
  rw [e88] at this
  exact hc.seq this

end AdvancedEncryption.RingBTVW.Prog
