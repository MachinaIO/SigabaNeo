import SigabaNeoStd.Machines.Prog.VecBound

/-!
# Shape bounds with appends depending on the scratch bound

`ATB p r S₀ a s T` (`SigabaNeoStd.Machines.Prog.SampleTime`) bounds programs that append a fixed
number `a` of bits to the output tape `r`. Copying a scratch tape onto `r` appends as many bits as
the scratch holds, so here the append is a monotone function of the scratch bound:

  `ATS p r a s T`: from `shp r x S` (`x` on `r`, `S` elsewhere), `p` costs at most `T x S` and ends
  below `shp r (x + a S) (S + s)`.

They compose (`ATS.seq`, `ATS.ifBit`, `ATS.ifBlank`, `ATS.mono`), with primitives (`ATS.prim`),
loops over a scratch tape (`ATS.forN`, the counter at most the scratch bound) and counted loops
(`ATS.count`, `withCount t c n (forN c t body)`).
-/

namespace SigabaNeo.Tape

namespace XProg

variable {k : ℕ} {r : Fin k}

/-- **A shape bound with an append depending on the scratch bound.** -/
def ATS (p : XProg k) (r : Fin k) (a : ℕ → ℕ) (s : ℕ) (T : ℕ → ℕ → ℕ) : Prop :=
  ∀ x S, timeBoundT p (shp r x S) ≤ T x S ∧ lenBoundT p (shp r x S) ≤ shp r (x + a S) (S + s)

theorem ATS.time {p : XProg k} {a : ℕ → ℕ} {s : ℕ} {T : ℕ → ℕ → ℕ} (h : ATS p r a s T)
    {ℓ : Fin k → ℕ} {x S : ℕ} (hℓ : ℓ ≤ shp r x S) : timeBoundT p ℓ ≤ T x S :=
  (timeBoundT_mono p hℓ).trans (h x S).1

theorem ATS.len {p : XProg k} {a : ℕ → ℕ} {s : ℕ} {T : ℕ → ℕ → ℕ} (h : ATS p r a s T)
    {ℓ : Fin k → ℕ} {x S : ℕ} (hℓ : ℓ ≤ shp r x S) : lenBoundT p ℓ ≤ shp r (x + a S) (S + s) :=
  (lenBoundT_mono p hℓ).trans (h x S).2

theorem ATS.mono {p : XProg k} {a a' : ℕ → ℕ} {s s' : ℕ} {T T' : ℕ → ℕ → ℕ} (h : ATS p r a s T)
    (ha : ∀ S, a S ≤ a' S) (hs : s ≤ s') (hT : ∀ x S, T x S ≤ T' x S) : ATS p r a' s' T' :=
  fun x S => ⟨(h x S).1.trans (hT x S), (h x S).2.trans (shp_mono (by have := ha S; omega)
    (by omega))⟩

theorem ATS.seq {p q : XProg k} {a b : ℕ → ℕ} {s u : ℕ} {T U : ℕ → ℕ → ℕ} (hp : ATS p r a s T)
    (hq : ATS q r b u U) :
    ATS (XProg.seq p q) r (fun S => a S + b (S + s)) (s + u)
      (fun x S => T x S + U (x + a S) (S + s)) := fun x S => by
  beta_reduce
  obtain ⟨h1, h2⟩ := hp x S
  refine ⟨Nat.add_le_add h1 (hq.time h2), ((hq.len h2)).trans (shp_mono (by omega) (by omega))⟩

theorem ATS.ifBit {p q : XProg k} (i : Fin k) {a b : ℕ → ℕ} {s u : ℕ} {T U : ℕ → ℕ → ℕ}
    (hp : ATS p r a s T) (hq : ATS q r b u U) :
    ATS (XProg.ifBit i p q) r (fun S => max (a S) (b S)) (max s u)
      (fun x S => max (T x S) (U x S) + 1) := fun x S => by
  beta_reduce
  exact ⟨Nat.add_le_add_right (max_le_max (hp x S).1 (hq x S).1) 1, fun t =>
    max_le (((hp x S).2 t).trans (shp_mono (by have := le_max_left (a S) (b S); omega)
        (by have := le_max_left s u; omega) t))
      (((hq x S).2 t).trans (shp_mono (by have := le_max_right (a S) (b S); omega)
        (by have := le_max_right s u; omega) t))⟩

theorem ATS.ifBlank {p q : XProg k} (i : Fin k) {a b : ℕ → ℕ} {s u : ℕ} {T U : ℕ → ℕ → ℕ}
    (hp : ATS p r a s T) (hq : ATS q r b u U) :
    ATS (XProg.ifBlank i p q) r (fun S => max (a S) (b S)) (max s u)
      (fun x S => max (T x S) (U x S) + 1) := fun x S => by
  beta_reduce
  exact ⟨Nat.add_le_add_right (max_le_max (hp x S).1 (hq x S).1) 1, fun t =>
    max_le (((hp x S).2 t).trans (shp_mono (by have := le_max_left (a S) (b S); omega)
        (by have := le_max_left s u; omega) t))
      (((hq x S).2 t).trans (shp_mono (by have := le_max_right (a S) (b S); omega)
        (by have := le_max_right s u; omega) t))⟩

theorem ATS.prim (p : Prim k) {a s : ℕ}
    (h : ∀ x S, p.lenT (shp r x S) ≤ shp r (x + a) (S + s)) :
    ATS (prog (.prim p)) r (fun _ => a) s (fun x S => 2 * (x + S + 1) + 3) := fun x S => by
  beta_reduce
  exact ⟨by rw [timeBoundT_prim]; have := supB_shp r x S; have := pad_le p; omega, h x S⟩

/-- A primitive that writes a scratch tape `i ≠ r` with a word of at most `S + s` bits. -/
theorem ATS.prim' (p : Prim k) {s : ℕ} (hr : r ∉ p.writes)
    (h : ∀ x S, p.lenT (shp r x S) ≤ shp r x (S + s)) :
    ATS (prog (.prim p)) r (fun _ => 0) s (fun x S => 2 * (x + S + 1) + 3) :=
  ATS.prim p fun x S => by simpa using h x S

/-- **A loop over a scratch tape** of at most `m ≤ S` bits. -/
theorem ats_forN {t c : Fin k} (hcr : c ≠ r) {body : XProg k} {a : ℕ → ℕ} {s : ℕ}
    {T : ℕ → ℕ → ℕ} (hb : ATS body r a s T) (hc : body.Preserves c) (ha : Monotone a)
    (hT : ∀ x x' S S', x ≤ x' → S ≤ S' → T x S ≤ T x' S') {ℓ : Fin k → ℕ} {x S m : ℕ}
    (hm : m ≤ S) (hℓ : ℓ ≤ shp r x S) (ht : ℓ t ≤ m) :
    timeBoundT (forN c t body) ℓ ≤ (2 * (x + S) + 3) +
      (m * (2 * (x + m * a (S + m * s) + (S + m * s)) + 3 +
        T (x + m * a (S + m * s)) (S + m * s) + 1) + 2) ∧
    lenBoundT (forN c t body) ℓ ≤ shp r (x + m * a (S + m * s)) (S + m * s) := by
  set A := a (S + m * s)
  set L0 := Function.update (shp r x S) c m
  set g := loopStepT c body
  have hit : ∀ j, j ≤ m → g^[j] L0 ≤ Function.update (shp r (x + j * A) (S + j * s)) c (m - j) := by
    intro j
    induction j with
    | zero => intro _; simp [L0]
    | succ j ih =>
      intro hj i
      rw [Function.iterate_succ_apply']
      have h1 := ih (by omega)
      have htl : tailB c (g^[j] L0) ≤ shp r (x + j * A) (S + j * s) := fun i' => by
        have := h1 i'
        simp only [tailB, Function.update_apply] at this ⊢
        split_ifs at this ⊢ with h
        · subst h; simp only [shp, if_neg hcr]; omega
        · exact this
      generalize g^[j] L0 = L at h1 htl ⊢
      show lenBoundT body (tailB c L) i ≤ _
      have hA : a (S + j * s) ≤ A := ha (by have := Nat.mul_le_mul_right s (show j ≤ m by omega); omega)
      by_cases hic : i = c
      · subst hic
        rw [lenBoundT_of_preserves body i hc, tailB, Function.update_self, Function.update_self]
        have := h1 i; simp at this; omega
      · simp only [Function.update_apply, if_neg hic]
        refine (hb.len htl i).trans ?_
        simp only [shp]; split_ifs
        · rw [Nat.succ_mul]; omega
        · rw [Nat.succ_mul]; omega
  have hitS : ∀ j, j ≤ m → g^[j] L0 ≤ shp r (x + m * A) (S + m * s) := by
    intro j hj i
    refine (hit j hj i).trans ?_
    have h1 : j * A ≤ m * A := Nat.mul_le_mul_right _ hj
    have h2 : j * s ≤ m * s := Nat.mul_le_mul_right _ hj
    simp only [Function.update_apply, shp]
    split_ifs <;> omega
  have hcopy : lenBoundT (prog (.prim (.copy c t))) ℓ ≤ L0 := by
    intro i
    rw [lenBoundT_prim]
    simp only [Prim.lenT, Function.update_apply, L0]
    split_ifs
    · exact ht
    · exact hℓ i
  have hloopT : timeBoundT (loop c body) L0 ≤
      m * (2 * (x + m * A + (S + m * s)) + 3 + T (x + m * A) (S + m * s) + 1) + 2 := by
    have := timeBoundT_loop_le c body L0
      (R := 2 * (x + m * A + (S + m * s)) + 3 + T (x + m * A) (S + m * s)) (fun j hj => by
        have hj' : j < m := by simpa [L0] using hj
        have hs1 := supB_mono (hitS j hj'.le)
        have hs2 := supB_shp r (x + m * A) (S + m * s)
        have htl : tailB c (g^[j] L0) ≤ shp r (x + j * A) (S + j * s) := fun i' => by
          have := hit j hj'.le i'
          simp only [tailB, Function.update_apply] at this ⊢
          split_ifs at this ⊢ with h
          · subst h; simp only [shp, if_neg hcr]; omega
          · exact this
        have hbt := (hb.time htl).trans
          (hT _ _ _ _ (Nat.add_le_add_left (Nat.mul_le_mul_right A hj'.le) x)
            (Nat.add_le_add_left (Nat.mul_le_mul_right s hj'.le) S))
        show 2 * supB (g^[j] L0) + 3 + timeBoundT body (tailB c (g^[j] L0)) ≤ _
        omega)
    simpa [L0] using this
  have hloopL : lenBoundT (loop c body) L0 ≤ shp r (x + m * A) (S + m * s) :=
    iterSupT_le fun j hj => hitS j (by simpa [L0] using hj)
  refine ⟨?_, ?_⟩
  · show timeBoundT (prog (.prim (.copy c t))) ℓ +
      timeBoundT (loop c body) (lenBoundT (prog (.prim (.copy c t))) ℓ) ≤ _
    have e1 := (timeBoundT_mono (loop c body) hcopy).trans hloopT
    have hcp : timeBoundT (prog (.prim (.copy c t))) ℓ ≤ 2 * (x + S) + 3 := by
      rw [timeBoundT_prim]
      have := supB_mono hℓ
      have := supB_shp r x S
      simp only [Prim.pad]; omega
    omega
  · exact (lenBoundT_mono (loop c body) hcopy).trans hloopL

/-- **A loop over a scratch tape** (`t ≠ r`) whose body leaves the scratch bound alone: at most
`S` rounds. -/
theorem ATS.forN {t c : Fin k} (hcr : c ≠ r) (htr : t ≠ r) {body : XProg k} {a : ℕ → ℕ}
    {T : ℕ → ℕ → ℕ} (hb : ATS body r a 0 T) (hc : body.Preserves c) (ha : Monotone a)
    (hT : ∀ x x' S S', x ≤ x' → S ≤ S' → T x S ≤ T x' S') :
    ATS (XProg.forN c t body) r (fun S => S * a S) 0
      (fun x S => (2 * (x + S) + 3) + (S * (2 * (x + S * a S + S) + 3 + T (x + S * a S) S + 1) + 2)) :=
  fun x S => by
    beta_reduce
    have h := ats_forN hcr hb hc ha hT (t := t) (m := S) (x := x) (S := S) le_rfl le_rfl
      (by simp only [shp, if_neg htr]; exact le_rfl)
    simp only [Nat.mul_zero, Nat.add_zero] at h
    exact h

/-- **A counted loop** of `n` rounds, the counter built from nothing (`n ≤ S`). -/
theorem ats_count {t c : Fin k} (htr : t ≠ r) (hcr : c ≠ r) (hct : c ≠ t) {body : XProg k}
    {a : ℕ → ℕ} {s : ℕ} {T : ℕ → ℕ → ℕ} (hb : ATS body r a s T) (hc : body.Preserves c)
    (ha : Monotone a) (hT : ∀ x x' S S', x ≤ x' → S ≤ S' → T x S ≤ T x' S') (n : ℕ) {x S : ℕ}
    (hn : n ≤ S) :
    timeBoundT (withCount t c n (forN c t body)) (shp r x S) ≤
        (2 * n + 1) * (4 * (x + S) + 12) + ((2 * (x + S) + 3) +
          (n * (2 * (x + n * a (S + n * s) + (S + n * s)) + 3 +
            T (x + n * a (S + n * s)) (S + n * s) + 1) + 2) +
          (2 * (x + n * a (S + n * s) + (S + n * s)) + 3)) ∧
      lenBoundT (withCount t c n (forN c t body)) (shp r x S) ≤
        shp r (x + n * a (S + n * s)) (S + n * s) := by
  have hM : ∀ i, shp r x S i ≤ x + S := fun i => by simp only [shp]; split_ifs <;> omega
  obtain ⟨hN1, hN2⟩ := natP_bounds hct n (shp r x S) (x + S) hM (by omega)
  have hB1 : natB t c n (shp r x S) ≤ shp r x S := fun i => by
    simp only [natB, shp]; split_ifs <;> first | omega | simp_all
  have hF := ats_forN hcr hb hc ha hT (t := t) (m := n) hn (hN1.trans hB1)
    (by have := hN1 t; simpa [natB] using this)
  have hcl : ∀ ℓ, ℓ ≤ shp r (x + n * a (S + n * s)) (S + n * s) →
      timeBoundT (prog (.prim (.clear t))) ℓ ≤ 2 * (x + n * a (S + n * s) + (S + n * s)) + 3 ∧
        lenBoundT (prog (.prim (.clear t))) ℓ ≤ shp r (x + n * a (S + n * s)) (S + n * s) :=
    fun ℓ hℓ => ⟨by
      rw [timeBoundT_prim]
      have := supB_mono hℓ
      have := supB_shp r (x + n * a (S + n * s)) (S + n * s)
      simp only [Prim.pad]; omega, fun i => by
      rw [lenBoundT_prim]; simp only [Prim.lenT, Function.update_apply]; split_ifs
      · exact Nat.zero_le _
      · exact hℓ i⟩
  refine ⟨?_, ?_⟩
  · show timeBoundT (natP t c n) _ + (timeBoundT (forN c t body) _ +
      timeBoundT (prog (.prim (.clear t))) _) ≤ _
    exact Nat.add_le_add hN2 (Nat.add_le_add hF.1 (hcl _ hF.2).1)
  · exact (hcl _ hF.2).2

theorem ATS.count {t c : Fin k} (htr : t ≠ r) (hcr : c ≠ r) (hct : c ≠ t) {body : XProg k}
    {a : ℕ → ℕ} {s : ℕ} {T : ℕ → ℕ → ℕ} (hb : ATS body r a s T) (hc : body.Preserves c)
    (ha : Monotone a) (hT : ∀ x x' S S', x ≤ x' → S ≤ S' → T x S ≤ T x' S') (n : ℕ) :
    ATS (withCount t c n (XProg.forN c t body)) r (fun S => n * a (max S n + n * s)) (n * s + n)
      (fun x S => (2 * n + 1) * (4 * (x + max S n) + 12) + ((2 * (x + max S n) + 3) +
          (n * (2 * (x + n * a (max S n + n * s) + (max S n + n * s)) + 3 +
            T (x + n * a (max S n + n * s)) (max S n + n * s) + 1) + 2) +
          (2 * (x + n * a (max S n + n * s) + (max S n + n * s)) + 3))) := fun x S => by
  beta_reduce
  have h := ats_count htr hcr hct hb hc ha hT n (x := x) (S := max S n) (le_max_right _ _)
  have hle : shp r x S ≤ shp r x (max S n) := shp_mono le_rfl (le_max_left _ _)
  exact ⟨(timeBoundT_mono _ hle).trans h.1, (lenBoundT_mono _ hle).trans (h.2.trans
    (shp_mono le_rfl (by have := le_max_left S n; have := le_max_right S n; omega)))⟩

end XProg

end SigabaNeo.Tape
