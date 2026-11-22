import SigabaNeo.Lib.Machines.Prog.Sample

/-!
# Time bounds of sampling programs

Explicit per-tape time bounds (`XProg.timeBoundT`) for programs that append to one output tape
`r` and use counters built from nothing (`natP`, `withCount`) on scratch tapes.

* `natP_bounds`: building the counter `replicate n false` costs at most `(2n + 1)(4M + 12)` from
  bounds below `M ≥ n`, and leaves the counter's tape at `n` (`natB`).
* **Shape bounds** `ATB p r S₀ a s T`: from the bound vector `shp r x S` (`x` on the output tape,
  `S ≥ S₀` on every other tape) the program costs at most `T x S` and ends below
  `shp r (x + a) (S + s)`: it appends at most `a` bits and its scratch grows by at most `s`.
  They compose: `ATB.seq`, `ATB.ifBit`, `ATB.ifBlank`, `ATB.mono`, primitives (`ATB.prim`) and
  coins (`ATB.coin`), and **counted loops** `ATB.count`: `withCount t c n (forN c t body)` costs
  `countT n a s T x S` and appends `n · a` bits.
-/

namespace SigabaNeo.Tape

namespace XProg

variable {k : ℕ}

/-! ### Bound vectors -/

theorem supB_le_of {ℓ : Fin k → ℕ} {M : ℕ} (h : ∀ i, ℓ i ≤ M) : supB ℓ ≤ M :=
  Finset.sup_le fun i _ => h i

/-- `x` on tape `r`, `S` elsewhere. -/
def shp (r : Fin k) (x S : ℕ) : Fin k → ℕ := fun i => if i = r then x else S

theorem supB_shp (r : Fin k) (x S : ℕ) : supB (shp r x S) ≤ x + S :=
  supB_le_of fun i => by unfold shp; split_ifs <;> omega

theorem shp_mono {r : Fin k} {x x' S S' : ℕ} (hx : x ≤ x') (hS : S ≤ S') :
    shp r x S ≤ shp r x' S' := fun i => by unfold shp; split_ifs <;> omega

theorem timeBoundT_prim (p : Prim k) (ℓ : Fin k → ℕ) :
    timeBoundT (prog (.prim p)) ℓ = 2 * (supB ℓ + p.pad) + 3 := rfl

theorem lenBoundT_prim (p : Prim k) (ℓ : Fin k → ℕ) :
    lenBoundT (prog (.prim p)) ℓ = p.lenT ℓ := rfl

theorem pad_le (p : Prim k) : p.pad ≤ 1 := by cases p <;> simp [Prim.pad]

/-! ### Counters -/

/-- The bounds after building the counter `t` (scratch `c`). -/
def natB (t c : Fin k) (n : ℕ) (ℓ : Fin k → ℕ) : Fin k → ℕ :=
  fun i => if i = t then n else if i = c then max (ℓ c) n else ℓ i

theorem dblP_bounds {t c : Fin k} (hct : c ≠ t) (ℓ : Fin k → ℕ) (m M : ℕ) (ht : ℓ t ≤ m)
    (hM : ∀ i, ℓ i ≤ M) (h2m : 2 * m ≤ M) :
    lenBoundT (dblP t c) ℓ ≤ (fun i => if i = t then 2 * m else if i = c then max (ℓ c) m else ℓ i) ∧
      timeBoundT (dblP t c) ℓ ≤ m * (4 * M + 9) + 2 * M + 5 := by
  set ℓ1 := Function.update ℓ c (ℓ t) with hℓ1
  set g := loopStepT c (bitAp t false)
  -- the iterates
  have hit : ∀ j, j ≤ ℓ t → g^[j] ℓ1 ≤
      fun i => if i = t then ℓ t + j else if i = c then ℓ t else ℓ i := by
    intro j
    induction j with
    | zero =>
      intro _ i
      simp only [Function.iterate_zero, id, hℓ1, Function.update_apply]
      split_ifs <;> simp_all
    | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply']
      have h1 := ih (by omega)
      generalize g^[j] ℓ1 = L at h1 ⊢
      intro i
      have hLt := h1 t
      have hLc := h1 c
      have hLi := h1 i
      simp only [if_true, if_neg hct, Nat.add_zero] at hLt hLc
      show (Prim.snoc t false).lenT (tailB c L) i ≤ _
      simp only [Prim.lenT, tailB]
      by_cases hi : i = t
      · subst hi
        simp only [Function.update_self, Function.update_of_ne hct.symm, if_true]
        omega
      · by_cases hc : i = c
        · subst hc
          simp only [Function.update_of_ne hi, Function.update_self, if_neg hi, if_true]
          omega
        · simp only [Function.update_of_ne hi, Function.update_of_ne hc, if_neg hi, if_neg hc]
          simpa [hi, hc] using hLi
  have hbnd : ∀ j, j ≤ ℓ t → ∀ i, (g^[j] ℓ1) i ≤ M := by
    intro j hj i
    have := hit j hj i
    have h1 := hM i
    have h2 := hM t
    simp only at this
    split_ifs at this <;> omega
  refine ⟨?_, ?_⟩
  · show lenBoundT (loop c (bitAp t false)) ℓ1 ≤ _
    refine iterSupT_le fun j hj i => ?_
    change (g^[j] ℓ1) i ≤ _
    have hj' : j ≤ ℓ t := by simpa [hℓ1] using hj
    have := hit j hj' i
    simp only at this ⊢
    split_ifs at this ⊢ <;> omega
  · show timeBoundT (prog (.prim (.copy c t))) ℓ + timeBoundT (loop c (bitAp t false)) ℓ1 ≤ _
    rw [timeBoundT_prim]
    have hcopy : supB ℓ ≤ M := supB_le_of hM
    have hloop := timeBoundT_loop_le c (bitAp t false) ℓ1 (R := 4 * M + 8) (fun j hj => by
      have hj' : j ≤ ℓ t := by simp [hℓ1] at hj; omega
      show 2 * supB (g^[j] ℓ1) + 3 + timeBoundT (bitAp t false) (tailB c (g^[j] ℓ1)) ≤ _
      rw [bitAp, timeBoundT_prim]
      have h1 : supB (g^[j] ℓ1) ≤ M := supB_le_of (hbnd j hj')
      have h2 : supB (tailB c (g^[j] ℓ1)) ≤ M :=
        (supB_mono (tailB_le c _)).trans h1
      simp only [Prim.pad]
      omega)
    have hc1 : ℓ1 c ≤ m := by simp [hℓ1]; omega
    have : ℓ1 c * (4 * M + 8 + 1) ≤ m * (4 * M + 9) := Nat.mul_le_mul_right _ hc1
    simp only [Prim.pad] at *
    omega

/-- **Building a counter.** -/
theorem natP_bounds {t c : Fin k} (hct : c ≠ t) : ∀ (n : ℕ) (ℓ : Fin k → ℕ) (M : ℕ),
    (∀ i, ℓ i ≤ M) → n ≤ M →
    lenBoundT (natP t c n) ℓ ≤ natB t c n ℓ ∧ timeBoundT (natP t c n) ℓ ≤ (2 * n + 1) * (4 * M + 12)
  | 0, ℓ, M, hM, _ => by
    rw [natP]
    refine ⟨fun i => ?_, ?_⟩
    · simp only [lenBoundT_prim, Prim.lenT, natB, Function.update_apply]
      split_ifs <;> first | omega | simp_all
    · rw [timeBoundT_prim]; have := supB_le_of hM; simp only [Prim.pad]; omega
  | n + 1, ℓ, M, hM, hn => by
    have ih := natP_bounds hct ((n + 1) / 2) ℓ M hM (by omega)
    set m := (n + 1) / 2
    have hB : ∀ i, natB t c m ℓ i ≤ M := fun i => by
      simp only [natB]; split_ifs
      · omega
      · exact max_le (hM c) (by omega)
      · exact hM i
    have hd := dblP_bounds hct (natB t c m ℓ) m M (by simp [natB]) hB (by omega)
    have hlen1 : lenBoundT (dblP t c) (lenBoundT (natP t c m) ℓ) ≤ _ :=
      (lenBoundT_mono _ ih.1).trans hd.1
    have htime1 : timeBoundT (dblP t c) (lenBoundT (natP t c m) ℓ) ≤ _ :=
      (timeBoundT_mono _ ih.1).trans hd.2
    have hA : 4 * M + 9 ≤ 4 * M + 12 := by omega
    rw [natP]
    split_ifs with h
    · refine ⟨fun i => ?_, ?_⟩
      · refine (hlen1 i).trans ?_
        simp only [natB]
        split_ifs <;> first | omega | (simp; omega)
      · show timeBoundT (natP t c m) ℓ + timeBoundT (dblP t c) (lenBoundT (natP t c m) ℓ) ≤ _
        have h1 := ih.2
        have h2 : m * (4 * M + 9) ≤ m * (4 * M + 12) := Nat.mul_le_mul_left _ hA
        have hm : 1 ≤ m := by omega
        have e : 2 * (n + 1) + 1 = (2 * m + 1) + m + m := by omega
        rw [e, Nat.add_mul, Nat.add_mul]
        have h3 : 2 * M + 5 ≤ 1 * (4 * M + 12) := by omega
        have h4 : 1 * (4 * M + 12) ≤ m * (4 * M + 12) := Nat.mul_le_mul_right _ hm
        omega
    · refine ⟨fun i => ?_, ?_⟩
      · show (Prim.snoc t false).lenT (lenBoundT (dblP t c) (lenBoundT (natP t c m) ℓ)) i ≤ _
        simp only [Prim.lenT, Function.update_apply]
        have := hlen1 i
        have ht := hlen1 t
        simp only [natB] at this ht ⊢
        split_ifs at this ht ⊢ <;> first | omega | (simp at *; omega)
      · show timeBoundT (natP t c m) ℓ + timeBoundT (dblP t c) (lenBoundT (natP t c m) ℓ) +
          timeBoundT (bitAp t false) (lenBoundT (dblP t c) (lenBoundT (natP t c m) ℓ)) ≤ _
        rw [bitAp, timeBoundT_prim]
        have hs : supB (lenBoundT (dblP t c) (lenBoundT (natP t c m) ℓ)) ≤ M := by
          refine supB_le_of fun i => (hlen1 i).trans ?_
          simp only
          split_ifs
          · omega
          · exact max_le (hB c) (by omega)
          · exact hB i
        have h1 := ih.2
        have h2 : m * (4 * M + 9) ≤ m * (4 * M + 12) := Nat.mul_le_mul_left _ hA
        have e : 2 * (n + 1) + 1 = (2 * m + 1) + m + (m + 2) := by omega
        rw [e, Nat.add_mul, Nat.add_mul]
        have h3 : 2 * (4 * M + 12) ≤ (m + 2) * (4 * M + 12) := Nat.mul_le_mul_right _ (by omega)
        simp only [Prim.pad]
        omega

/-! ### Shape bounds -/

/-- **`p` appends at most `a` bits to `r` and grows its scratch by at most `s`, within `T`.** -/
def ATB (p : XProg k) (r : Fin k) (S₀ a s : ℕ) (T : ℕ → ℕ → ℕ) : Prop :=
  ∀ x S, S₀ ≤ S → timeBoundT p (shp r x S) ≤ T x S ∧ lenBoundT p (shp r x S) ≤ shp r (x + a) (S + s)

variable {r : Fin k}

theorem ATB.time {p : XProg k} {S₀ a s : ℕ} {T : ℕ → ℕ → ℕ} (h : ATB p r S₀ a s T) {ℓ : Fin k → ℕ}
    {x S : ℕ} (hS : S₀ ≤ S) (hℓ : ℓ ≤ shp r x S) : timeBoundT p ℓ ≤ T x S :=
  (timeBoundT_mono p hℓ).trans (h x S hS).1

theorem ATB.seq {p q : XProg k} {S₀ a s b u : ℕ} {T U : ℕ → ℕ → ℕ} (hp : ATB p r S₀ a s T)
    (hq : ATB q r S₀ b u U) :
    ATB (XProg.seq p q) r S₀ (a + b) (s + u) (fun x S => T x S + U (x + a) (S + s)) := by
  intro x S hS
  obtain ⟨hp1, hp2⟩ := hp x S hS
  obtain ⟨hq1, hq2⟩ := hq (x + a) (S + s) (by omega)
  refine ⟨?_, ?_⟩
  · show timeBoundT p _ + timeBoundT q (lenBoundT p _) ≤ _
    exact Nat.add_le_add hp1 ((timeBoundT_mono q hp2).trans hq1)
  · show lenBoundT q (lenBoundT p _) ≤ _
    refine ((lenBoundT_mono q hp2).trans hq2).trans ?_
    exact shp_mono (by omega) (by omega)

theorem ATB.mono {p : XProg k} {S₀ a s S₀' a' s' : ℕ} {T T' : ℕ → ℕ → ℕ} (h : ATB p r S₀ a s T)
    (hS : S₀ ≤ S₀') (ha : a ≤ a') (hs : s ≤ s') (hT : ∀ x S, S₀' ≤ S → T x S ≤ T' x S) :
    ATB p r S₀' a' s' T' := fun x S hS' =>
  ⟨(h x S (hS.trans hS')).1.trans (hT x S hS'),
    (h x S (hS.trans hS')).2.trans (shp_mono (by omega) (by omega))⟩

theorem ATB.ifBit {p q : XProg k} (i : Fin k) {S₀ a s : ℕ} {T U : ℕ → ℕ → ℕ}
    (hp : ATB p r S₀ a s T) (hq : ATB q r S₀ a s U) :
    ATB (XProg.ifBit i p q) r S₀ a s (fun x S => max (T x S) (U x S) + 1) := fun x S hS =>
  ⟨Nat.add_le_add_right (max_le_max (hp x S hS).1 (hq x S hS).1) 1,
    fun t => max_le ((hp x S hS).2 t) ((hq x S hS).2 t)⟩

theorem ATB.ifBlank {p q : XProg k} (i : Fin k) {S₀ a s : ℕ} {T U : ℕ → ℕ → ℕ}
    (hp : ATB p r S₀ a s T) (hq : ATB q r S₀ a s U) :
    ATB (XProg.ifBlank i p q) r S₀ a s (fun x S => max (T x S) (U x S) + 1) := fun x S hS =>
  ⟨Nat.add_le_add_right (max_le_max (hp x S hS).1 (hq x S hS).1) 1,
    fun t => max_le ((hp x S hS).2 t) ((hq x S hS).2 t)⟩

/-- A primitive whose bound stays in the shape. -/
theorem ATB.prim (p : Prim k) {S₀ a s : ℕ}
    (h : ∀ x S, S₀ ≤ S → p.lenT (shp r x S) ≤ shp r (x + a) (S + s)) :
    ATB (prog (.prim p)) r S₀ a s (fun x S => 2 * (x + S + 1) + 3) := fun x S hS =>
  ⟨by rw [timeBoundT_prim]; have := supB_shp r x S; have := pad_le p; show _ ≤ 2 * (x + S + 1) + 3; omega,
    h x S hS⟩

/-- A coin on a scratch tape. -/
theorem ATB.coin {i : Fin k} (hi : i ≠ r) :
    ATB (prog (.coin i)) r 1 0 0 (fun x S => 2 * (x + S) + 4) := fun x S hS =>
  ⟨by show 2 * supB _ + 4 ≤ 2 * (x + S) + 4; have := supB_shp r x S; omega,
    fun t => by
      show Function.update (shp r x S) i 1 t ≤ _
      simp only [Function.update_apply, shp]
      split_ifs <;> omega⟩

/-! ### Counted loops -/

/-- The time of a counted loop of `n` rounds of a body within `T`, appending `a` bits and growing
its scratch by `s` per round. -/
def countT (n a s : ℕ) (T : ℕ → ℕ → ℕ) (x S : ℕ) : ℕ :=
  (2 * n + 1) * (4 * (x + S) + 12) + (2 * (x + S) + 3) +
    (n * (2 * (x + n * a + (S + n * s)) + 3 + T (x + n * a) (S + n * s) + 1) + 2) +
    (2 * (x + n * a + (S + n * s)) + 3)

/-- **A counted loop**: `n` rounds of the body, with the counter built from nothing. -/
theorem ATB.count {t c : Fin k} (htr : t ≠ r) (hcr : c ≠ r) (hct : c ≠ t) {body : XProg k}
    {S₀ a s : ℕ} {T : ℕ → ℕ → ℕ} (hb : ATB body r S₀ a s T) (hc : body.Preserves c)
    (hT : ∀ x x' S S', x ≤ x' → S ≤ S' → T x S ≤ T x' S') (n : ℕ) :
    ATB (withCount t c n (forN c t body)) r (max S₀ n) (n * a) (n * s) (countT n a s T) := by
  intro x S hS
  have hS₀ : S₀ ≤ S := le_of_max_le_left hS
  have hn : n ≤ S := le_of_max_le_right hS
  set ℓ0 := shp r x S
  have hM : ∀ i, ℓ0 i ≤ x + S := fun i => by simp only [ℓ0, shp]; split_ifs <;> omega
  obtain ⟨hN1, hN2⟩ := natP_bounds hct n ℓ0 (x + S) hM (by omega)
  have hB1 : natB t c n ℓ0 ≤ shp r x S := fun i => by
    simp only [natB, ℓ0, shp]; split_ifs <;> first | omega | simp_all
  set L0 := Function.update (shp r x S) c n
  set g := loopStepT c body
  -- the iterates of the loop
  have hit : ∀ j, j ≤ n → g^[j] L0 ≤ Function.update (shp r (x + j * a) (S + j * s)) c (n - j) := by
    intro j
    induction j with
    | zero => intro _; simp [L0]
    | succ j ih =>
      intro hj i
      rw [Function.iterate_succ_apply']
      have h1 := ih (by omega)
      have htl : tailB c (g^[j] L0) ≤ shp r (x + j * a) (S + j * s) := fun i' => by
        have := h1 i'
        simp only [tailB, Function.update_apply] at this ⊢
        split_ifs at this ⊢ with h
        · subst h; simp only [shp, if_neg hcr]; omega
        · exact this
      generalize g^[j] L0 = L at h1 htl ⊢
      show lenBoundT body (tailB c L) i ≤ _
      by_cases hic : i = c
      · subst hic
        rw [lenBoundT_of_preserves body i hc, tailB, Function.update_self, Function.update_self]
        have := h1 i; simp at this; omega
      · simp only [Function.update_apply, if_neg hic]
        refine ((lenBoundT_mono body htl) i).trans (((hb _ _ (by nlinarith)).2 i).trans ?_)
        simp only [shp]; split_ifs
        · rw [Nat.succ_mul]; omega
        · rw [Nat.succ_mul]; omega
  have hitS : ∀ j, j ≤ n → g^[j] L0 ≤ shp r (x + n * a) (S + n * s) := by
    intro j hj i
    refine (hit j hj i).trans ?_
    have h1 : j * a ≤ n * a := Nat.mul_le_mul_right _ hj
    have h2 : j * s ≤ n * s := Nat.mul_le_mul_right _ hj
    simp only [Function.update_apply, shp]
    split_ifs <;> omega
  -- the store after the counter and the copy
  have hcopy : lenBoundT (prog (.prim (.copy c t))) (lenBoundT (natP t c n) ℓ0) ≤ L0 := by
    intro i
    rw [lenBoundT_prim]
    simp only [Prim.lenT, Function.update_apply, L0]
    split_ifs with h
    · have := hN1 t; simp [natB] at this; exact this
    · exact (hN1 i).trans (hB1 i)
  have hloopT : timeBoundT (loop c body) L0 ≤
      n * (2 * (x + n * a + (S + n * s)) + 3 + T (x + n * a) (S + n * s) + 1) + 2 := by
    have := timeBoundT_loop_le c body L0
      (R := 2 * (x + n * a + (S + n * s)) + 3 + T (x + n * a) (S + n * s)) (fun j hj => by
        have hj' : j < n := by simpa [L0] using hj
        have hs1 := supB_mono (hitS j hj'.le)
        have hs2 := supB_shp r (x + n * a) (S + n * s)
        have htl : tailB c (g^[j] L0) ≤ shp r (x + j * a) (S + j * s) := fun i' => by
          have := hit j hj'.le i'
          simp only [tailB, Function.update_apply] at this ⊢
          split_ifs at this ⊢ with h
          · subst h; simp only [shp, if_neg hcr]; omega
          · exact this
        have hbt := (hb.time (by nlinarith) htl).trans
          (hT _ _ _ _ (Nat.add_le_add_left (Nat.mul_le_mul_right a hj'.le) x)
            (Nat.add_le_add_left (Nat.mul_le_mul_right s hj'.le) S))
        show 2 * supB (g^[j] L0) + 3 + timeBoundT body (tailB c (g^[j] L0)) ≤ _
        omega)
    simpa [L0] using this
  have hloopL : lenBoundT (loop c body) L0 ≤ shp r (x + n * a) (S + n * s) :=
    iterSupT_le fun j hj => hitS j (by simpa [L0] using hj)
  refine ⟨?_, ?_⟩
  · show timeBoundT (natP t c n) ℓ0 + (timeBoundT (prog (.prim (.copy c t))) (lenBoundT (natP t c n) ℓ0) +
      timeBoundT (loop c body) (lenBoundT (prog (.prim (.copy c t))) (lenBoundT (natP t c n) ℓ0)) +
      timeBoundT (prog (.prim (.clear t))) (lenBoundT (loop c body)
        (lenBoundT (prog (.prim (.copy c t))) (lenBoundT (natP t c n) ℓ0)))) ≤ _
    have e1 := (timeBoundT_mono (loop c body) hcopy).trans hloopT
    have hcp : timeBoundT (prog (.prim (.copy c t))) (lenBoundT (natP t c n) ℓ0) ≤ 2 * (x + S) + 3 := by
      rw [timeBoundT_prim]
      have := supB_mono (hN1.trans hB1)
      have := supB_shp r x S
      simp only [Prim.pad]; omega
    have hcl : timeBoundT (prog (.prim (.clear t))) (lenBoundT (loop c body)
        (lenBoundT (prog (.prim (.copy c t))) (lenBoundT (natP t c n) ℓ0))) ≤
        2 * (x + n * a + (S + n * s)) + 3 := by
      rw [timeBoundT_prim]
      have := supB_mono ((lenBoundT_mono (loop c body) hcopy).trans hloopL)
      have := supB_shp r (x + n * a) (S + n * s)
      simp only [Prim.pad]; omega
    unfold countT
    omega
  · show (Prim.clear t).lenT (lenBoundT (loop c body)
      (lenBoundT (prog (.prim (.copy c t))) (lenBoundT (natP t c n) ℓ0))) ≤ _
    intro i
    simp only [Prim.lenT, Function.update_apply]
    split_ifs
    · omega
    · exact ((lenBoundT_mono (loop c body) hcopy).trans hloopL) i

end XProg

end SigabaNeo.Tape
