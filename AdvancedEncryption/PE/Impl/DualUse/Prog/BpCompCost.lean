import PE.Impl.DualUse.Prog.BpCompLaw

/-!
# The compiler of branching programs: cost

Per-tape bounds of `bpCompP` (`Prog.timeBoundT`, `Prog.lenBoundT`). Every tape but the output stays
small (`S0 = 128` bits) or below the input bound `L` (`IN`, `CUR`, `TT`); the output grows. A piece
of code satisfies `TB M L p n g` when, from bounds at most `bnd L a` (output `a`), it takes at most
`n` units `Uc M L = 2 (M + L + S0) + 5` (a sweep of every tape) and ends below `bnd L (a + g)`, as
long as `a + g ≤ M`. These compose (`TB.seq`), loops multiply (`tb_loop`), and the tree code gets
`nT m` units and growth `gT m` by induction (`tb_treeP`).
-/

namespace AdvancedEncryption.DualUse.BpComp

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog
open scoped Prog

/-- The bound of the small tapes. -/
abbrev S0 : ℕ := 128

/-- The per-tape bounds: output `a`, `IN`, `CUR`, `TT` at `L`, the rest at `S0`. -/
def bnd (L a : ℕ) : Fin 64 → ℕ := fun t =>
  if t = tO then a else if t = tIN ∨ t = tCUR ∨ t = tTT then L else S0

/-- One unit: a sweep of every tape. -/
def Uc (M L : ℕ) : ℕ := 2 * (M + L + S0) + 5

/-- **A cost triple.** -/
def TB (M L : ℕ) (p : Prog 64) (n g : ℕ) : Prop :=
  ∀ a, a + g ≤ M → ∀ ℓ, ℓ ≤ bnd L a →
    timeBoundT p ℓ ≤ n * Uc M L ∧ lenBoundT p ℓ ≤ bnd L (a + g)

variable {M L : ℕ}

theorem bnd_mono {a a' : ℕ} (h : a ≤ a') : bnd L a ≤ bnd L a' := by
  intro t; simp only [bnd]; split_ifs <;> omega

theorem supB_bnd_le {a : ℕ} (ha : a ≤ M) {ℓ : Fin 64 → ℕ} (hℓ : ℓ ≤ bnd L a) :
    supB ℓ ≤ M + L + S0 :=
  Finset.sup_le fun t _ => (hℓ t).trans (by simp only [bnd]; split_ifs <;> omega)

theorem two_le_Uc : 2 ≤ Uc M L := by unfold Uc; omega

theorem TB.mono {p : Prog 64} {n g n' g' : ℕ} (h : TB M L p n g) (hn : n ≤ n') (hg : g ≤ g') :
    TB M L p n' g' := fun a ha ℓ hℓ =>
  ⟨(h a (by omega) ℓ hℓ).1.trans (Nat.mul_le_mul_right _ hn),
    (h a (by omega) ℓ hℓ).2.trans (bnd_mono (by omega))⟩

theorem TB.seq {p q : Prog 64} {n g n' g' : ℕ} (hp : TB M L p n g) (hq : TB M L q n' g') :
    TB M L (p ⨾ q) (n + n') (g + g') := by
  intro a ha ℓ hℓ
  obtain ⟨h1, h2⟩ := hp a (by omega) ℓ hℓ
  obtain ⟨h3, h4⟩ := hq (a + g) (by omega) _ h2
  refine ⟨?_, ?_⟩
  · rw [timeBoundT_seq]; rw [Nat.add_mul]; omega
  · show lenBoundT q (lenBoundT p ℓ) ≤ _
    rw [← Nat.add_assoc]; exact h4

/-- A primitive whose bound stays in shape. -/
theorem tb_prim (q : Prim 64) (g : ℕ) (h : ∀ a, q.lenT (bnd L a) ≤ bnd L (a + g)) :
    TB M L (prim q) 1 g := by
  intro a ha ℓ hℓ
  refine ⟨?_, (Prim.lenT_mono q hℓ).trans (h a)⟩
  show 2 * (supB ℓ + q.pad) + 3 ≤ 1 * Uc M L
  have := supB_bnd_le (M := M) (by omega) hℓ
  have : q.pad ≤ 1 := by cases q <;> simp [Prim.pad]
  unfold Uc; omega

/-- Check the shape of a primitive's bound. -/
macro "lenT_tac" : tactic =>
  `(tactic| (intro a t; simp +decide only [Prim.lenT, bnd, Function.update_apply]; split_ifs <;> simp_all +decide <;> omega))

theorem tb_snoc_O (b : Bool) : TB M L (prim (.snoc tO b)) 1 1 := tb_prim _ 1 (by lenT_tac)

theorem tb_snocHead_O (x : Fin 64) : TB M L (prim (.snocHead tO x)) 1 1 := tb_prim _ 1 (by lenT_tac)

theorem tb_clear (t : Fin 64) : TB M L (prim (.clear t)) 1 0 := tb_prim _ 0 fun a u => by
  simp only [Prim.lenT, Function.update_apply, Nat.add_zero]; split_ifs
  · exact Nat.zero_le _
  · exact le_rfl

theorem tb_tail (t : Fin 64) : TB M L (prim (.tail t)) 1 0 := tb_prim _ 0 fun a u => by
  simp only [Prim.lenT, Function.update_apply, Nat.add_zero]; split_ifs with h
  · subst h; exact Nat.sub_le _ _
  · exact le_rfl

/-- The small tapes. -/
def Small (t : Fin 64) : Prop := t ≠ tO ∧ t ≠ tIN ∧ t ≠ tCUR ∧ t ≠ tTT

theorem bnd_small {t : Fin 64} (h : Small t) (a : ℕ) : bnd L a t = S0 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp [bnd, h1, h2, h3, h4]

theorem tb_copy_small {t x : Fin 64} (ht : Small t) (hx : Small x) : TB M L (prim (.copy t x)) 1 0 :=
  tb_prim _ 0 fun a u => by
    simp only [Prim.lenT, Function.update_apply, Nat.add_zero]
    split_ifs with h
    · subst h; rw [bnd_small ht, bnd_small hx]
    · exact le_rfl

theorem tb_copy_big {t x : Fin 64} (ht : t = tIN ∨ t = tCUR ∨ t = tTT)
    (hx : x = tIN ∨ x = tCUR ∨ x = tTT) : TB M L (prim (.copy t x)) 1 0 :=
  tb_prim _ 0 fun a u => by
    simp only [Prim.lenT, Function.update_apply, Nat.add_zero]
    split_ifs with h
    · subst h
      have h1 : bnd L a x = L := by
        rcases hx with rfl | rfl | rfl <;> simp +decide [bnd]
      have h2 : bnd L a u = L := by
        rcases ht with rfl | rfl | rfl <;> simp +decide [bnd]
      omega
    · exact le_rfl

theorem tb_pop_small {t b : Fin 64} (hb : Small b) : TB M L (prim (.pop t b)) 1 0 :=
  tb_prim _ 0 fun a u => by
    simp only [Prim.lenT, Function.update_apply, Nat.add_zero]
    split_ifs with h h'
    · subst h; rw [bnd_small hb a]; exact (min_le_left _ _).trans (by norm_num)
    · subst h'; exact Nat.sub_le _ _
    · exact le_rfl

theorem tb_nop (t : Fin 64) : TB M L (nop t) 1 0 := tb_prim _ 0 fun a u => by
  simp only [Prim.lenT, Function.update_apply, Nat.add_zero]; split_ifs with h
  · subst h; exact le_rfl
  · exact le_rfl

/-- **A loop** of at most `R` rounds. -/
theorem tb_loop_core {c : Fin 64} {body : Prog 64} {n g R : ℕ} (hb : TB M L body n g) (a : ℕ)
    (ha : a + R * g ≤ M) (ℓ : Fin 64 → ℕ) (hℓ : ℓ ≤ bnd L a) (hc : ℓ c ≤ R) :
    timeBoundT (loop c body) ℓ ≤ (R * (n + 2) + 1) * Uc M L ∧
      lenBoundT (loop c body) ℓ ≤ bnd L (a + R * g) := by
  have hit : ∀ j, j ≤ R → (loopStepT c body)^[j] ℓ ≤ bnd L (a + j * g) := by
    intro j
    induction j with
    | zero => intro _; simpa using hℓ
    | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply']
      have h1 := ih (by omega)
      have h2 := (hb (a + j * g) (by nlinarith) _ ((tailB_le c _).trans h1)).2
      exact h2.trans (bnd_mono (by rw [Nat.succ_mul]; omega))
  have hU := two_le_Uc (M := M) (L := L)
  refine ⟨?_, ?_⟩
  · refine (timeBoundT_loop_le c body ℓ (R := (n + 1) * Uc M L) fun j hj => ?_).trans ?_
    · have h1 := hit j (by omega)
      have hj' : a + j * g ≤ M := by nlinarith
      show 2 * supB _ + 3 + timeBoundT body _ ≤ _
      have h2 := supB_bnd_le hj' h1
      have h3 := (hb (a + j * g) (by nlinarith) _ ((tailB_le c _).trans h1)).1
      rw [Nat.add_mul, Nat.one_mul]; unfold Uc at *; omega
    · have := Nat.mul_le_mul_right ((n + 1) * Uc M L + 1) hc
      calc ℓ c * ((n + 1) * Uc M L + 1) + 2 ≤ R * ((n + 1) * Uc M L + 1) + 2 := by omega
        _ ≤ (R * (n + 2) + 1) * Uc M L := by nlinarith
  · rw [lenBoundT_loop]
    exact iterSupT_le fun j hj => (hit j (by omega)).trans (bnd_mono (by nlinarith))

theorem update_le_bnd {ℓ : Fin 64 → ℕ} {a : ℕ} (hℓ : ℓ ≤ bnd L a) {c : Fin 64} (hc : Small c)
    {v : ℕ} (hv : v ≤ S0) : Function.update ℓ c v ≤ bnd L a := by
  intro t; simp only [Function.update_apply]; split_ifs with h
  · subst h; rw [bnd_small hc]; exact hv
  · exact hℓ t

/-- **A counted loop** on a copy of a small tape. -/
theorem tb_forN {c x : Fin 64} (hc : Small c) (hx : Small x) {body : Prog 64} {n g : ℕ}
    (hb : TB M L body n g) : TB M L (forN c x body) (S0 * (n + 2) + 2) (S0 * g) := by
  intro a ha ℓ hℓ
  have hcp := (tb_copy_small (M := M) (L := L) hc hx) a (by omega) ℓ hℓ
  have h1 : lenBoundT (prim (.copy c x)) ℓ = Function.update ℓ c (ℓ x) := rfl
  have h2 : Function.update ℓ c (ℓ x) ≤ bnd L a :=
    update_le_bnd hℓ hc ((hℓ x).trans (bnd_small hx a).le)
  have h3 := tb_loop_core (R := S0) hb a ha _ h2 (by
    rw [Function.update_self]; exact (hℓ x).trans (bnd_small hx a).le)
  refine ⟨?_, ?_⟩
  · show timeBoundT (prim (.copy c x) ⨾ loop c body) ℓ ≤ _
    rw [timeBoundT_seq, h1]
    have := hcp.1
    nlinarith [h3.1]
  · show lenBoundT (loop c body) (lenBoundT (prim (.copy c x)) ℓ) ≤ _
    rw [h1]; exact h3.2

theorem small_A : Small tA := by unfold Small; decide
theorem small_B : Small tB := by unfold Small; decide

/-- **Appending a small tape** to the output. -/
theorem tb_appT {x : Fin 64} (hx : Small x) : TB M L (appT tO x tA tB) (S0 * 4 + 4) S0 := by
  have hb : TB M L (appBody tO tB) 2 1 := (tb_snocHead_O tB).seq (tb_tail tB)
  have := ((tb_copy_small small_B hx).seq ((tb_forN small_A hx hb).seq (tb_clear tB)))
  exact this.mono (by omega) (by omega)

/-- **Dropping by a small tape.** -/
theorem tb_dropT (t : Fin 64) {x : Fin 64} (hx : Small x) : TB M L (dropT t x tA) (S0 * 3 + 2) 0 :=
  (tb_forN small_A hx (tb_tail t)).mono (by omega) (by omega)

theorem tb_snocN_O (b : Bool) : ∀ n, TB M L (snocN tO b n) (n + 1) n
  | 0 => tb_nop tO
  | n + 1 => ((tb_snocN_O b n).seq (tb_snoc_O b)).mono (by omega) (by omega)

theorem tb_emitU (j : ℕ) : TB M L (emitU tO 512 j) (j + 1 + (512 - j + 1)) (j + (512 - j)) :=
  (tb_snocN_O true j).seq (tb_snocN_O false (512 - j))

theorem tb_appL {xs : List (Fin 64)} (hxs : ∀ x ∈ xs, Small x) :
    TB M L (appL tO tA tB xs) (xs.length * (S0 * 4 + 4) + 1) (xs.length * S0) := by
  induction xs with
  | nil => exact tb_nop tO
  | cons x xs ih =>
    have := (tb_appT (M := M) (L := L) (hxs x (by simp))).seq (ih fun y hy => hxs y (by simp [hy]))
    exact this.mono (by simp [Nat.succ_mul]; omega) (by simp [Nat.succ_mul]; omega)

theorem tb_dynE (a b : ℕ) {xs : List (Fin 64)} (hxs : ∀ x ∈ xs, Small x) :
    TB M L (dynE tO tA tB a xs b) (a + 1 + (xs.length * (S0 * 4 + 4) + 1) + (b + 1))
      (a + xs.length * S0 + b) :=
  (tb_snocN_O true a).seq ((tb_appL hxs).seq (tb_snocN_O false b)) |>.mono (by omega) (by omega)

theorem lenBoundT_snocN (c : Fin 64) (b : Bool) : ∀ (n : ℕ) (ℓ : Fin 64 → ℕ),
    lenBoundT (snocN c b n) ℓ = Function.update ℓ c (ℓ c + n)
  | 0, ℓ => by
    show Prim.lenT (.copy c c) ℓ = _
    simp [Prim.lenT]
  | n + 1, ℓ => by
    show Prim.lenT (.snoc c b) (lenBoundT (snocN c b n) ℓ) = _
    rw [lenBoundT_snocN c b n ℓ]
    simp only [Prim.lenT, Function.update_self, Function.update_idem]
    congr 1

theorem timeBoundT_snocN_small {c : Fin 64} (hc : Small c) (b : Bool) {a : ℕ} (ha : a ≤ M) :
    ∀ (n : ℕ) (ℓ : Fin 64 → ℕ), ℓ ≤ bnd L a → ℓ c + n ≤ S0 →
      timeBoundT (snocN c b n) ℓ ≤ (n + 1) * Uc M L
  | 0, ℓ, hℓ, _ => by
    show 2 * (supB ℓ + 0) + 3 ≤ _
    have := supB_bnd_le ha hℓ; unfold Uc; omega
  | n + 1, ℓ, hℓ, hn => by
    show timeBoundT (snocN c b n) ℓ + (2 * (supB (lenBoundT (snocN c b n) ℓ) + 1) + 3) ≤ _
    have h1 := timeBoundT_snocN_small hc b ha n ℓ hℓ (by omega)
    rw [lenBoundT_snocN]
    have h2 := supB_bnd_le ha (update_le_bnd hℓ hc (v := ℓ c + n) (by omega))
    have hU : 2 * (supB (Function.update ℓ c (ℓ c + n)) + 1) + 3 ≤ Uc M L := by unfold Uc; omega
    rw [show (n + 1 + 1) * Uc M L = (n + 1) * Uc M L + Uc M L by ring]; omega

theorem lenBoundT_clear (c : Fin 64) (ℓ : Fin 64 → ℕ) :
    lenBoundT (prim (.clear c)) ℓ = Function.update ℓ c 0 := rfl

theorem timeBoundT_seq3 (p q r : Prog 64) (ℓ : Fin 64 → ℕ) :
    timeBoundT (p ⨾ q ⨾ r) ℓ =
      timeBoundT p ℓ + (timeBoundT q (lenBoundT p ℓ) + timeBoundT r (lenBoundT q (lenBoundT p ℓ))) :=
  rfl

/-- **A constant word on a small tape**, then the rest. -/
theorem tb_setN {c : Fin 64} (hc : Small c) (b : Bool) {R : ℕ} (hR : R ≤ S0) {rest : Prog 64}
    {n g : ℕ} (hr : TB M L rest n g) : TB M L (clr c ⨾ snocN c b R ⨾ rest) (n + R + 2) g := by
  intro a ha ℓ hℓ
  have e1 : lenBoundT (snocN c b R) (lenBoundT (prim (.clear c)) ℓ) = Function.update ℓ c R := by
    rw [lenBoundT_snocN, lenBoundT_clear]; simp
  have h0 : Function.update ℓ c 0 ≤ bnd L a := update_le_bnd hℓ hc (Nat.zero_le _)
  have h2 := hr a ha (Function.update ℓ c R) (update_le_bnd hℓ hc hR)
  have h3 := (tb_clear (M := M) (L := L) c a (by omega) ℓ hℓ).1
  have h4 := timeBoundT_snocN_small (M := M) (L := L) hc b (a := a) (by omega) R _ h0 (by simp; omega)
  refine ⟨?_, ?_⟩
  · rw [timeBoundT_seq3, e1]
    have e0 : lenBoundT (clr c) ℓ = Function.update ℓ c 0 := rfl
    rw [e0]
    have := h2.1
    have h3' : timeBoundT (clr c) ℓ ≤ 1 * Uc M L := h3
    nlinarith
  · show lenBoundT rest (lenBoundT (snocN c b R) (lenBoundT (prim (.clear c)) ℓ)) ≤ _
    rw [e1]; exact h2.2

/-- **A loop on a counter set to `R`**, then the rest. -/
theorem tb_setLoop {c : Fin 64} (hc : Small c) {R : ℕ} (hR : R ≤ S0) {body rest : Prog 64}
    {n g n' g' : ℕ} (hb : TB M L body n g) (hr : TB M L rest n' g') :
    TB M L (clr c ⨾ snocN c true R ⨾ loop c body ⨾ rest) (R * (n + 2) + 1 + n' + R + 2)
      (R * g + g') := by
  intro a ha ℓ hℓ
  have e0 : lenBoundT (clr c) ℓ = Function.update ℓ c 0 := rfl
  have e1 : lenBoundT (snocN c true R) (Function.update ℓ c 0) = Function.update ℓ c R := by
    rw [lenBoundT_snocN]; simp
  have h0 : Function.update ℓ c 0 ≤ bnd L a := update_le_bnd hℓ hc (Nat.zero_le _)
  have hl := tb_loop_core (c := c) (R := R) hb a (by nlinarith) (Function.update ℓ c R) (update_le_bnd hℓ hc hR)
    (by simp)
  have hr' := hr (a + R * g) (by omega) _ hl.2
  have h3 : timeBoundT (clr c) ℓ ≤ 1 * Uc M L := (tb_clear c a (by omega) ℓ hℓ).1
  have h4 := timeBoundT_snocN_small (M := M) (L := L) hc true (a := a) (by omega) R _ h0
    (by simp; omega)
  refine ⟨?_, ?_⟩
  · rw [timeBoundT_seq, timeBoundT_seq, timeBoundT_seq, e0, e1]
    nlinarith [hl.1, hr'.1]
  · show lenBoundT rest (lenBoundT (loop c body) (lenBoundT (snocN c true R) (lenBoundT (clr c) ℓ)))
      ≤ _
    rw [e0, e1]; exact hr'.2.trans (bnd_mono (by omega))

theorem tb_ifBit {i : Fin 64} {p q : Prog 64} {n g : ℕ} (hp : TB M L p n g) (hq : TB M L q n g) :
    TB M L (ifBit i p q) (n + 1) g := fun a ha ℓ hℓ => by
  have h1 := hp a ha ℓ hℓ; have h2 := hq a ha ℓ hℓ
  have := two_le_Uc (M := M) (L := L)
  refine ⟨?_, fun t => max_le (h1.2 t) (h2.2 t)⟩
  show max _ _ + 1 ≤ _
  rw [Nat.add_mul, Nat.one_mul]; have := max_le h1.1 h2.1; omega

theorem tb_ifBlank {i : Fin 64} {p q : Prog 64} {n g : ℕ} (hp : TB M L p n g) (hq : TB M L q n g) :
    TB M L (ifBlank i p q) (n + 1) g := fun a ha ℓ hℓ => by
  have h1 := hp a ha ℓ hℓ; have h2 := hq a ha ℓ hℓ
  have := two_le_Uc (M := M) (L := L)
  refine ⟨?_, fun t => max_le (h1.2 t) (h2.2 t)⟩
  show max _ _ + 1 ≤ _
  rw [Nat.add_mul, Nat.one_mul]; have := max_le h1.1 h2.1; omega

/-! ### The tree -/

/-- Units of an emitter. -/
abbrev NE : ℕ := 2604
/-- Units of a part of a node. -/
abbrev NP : ℕ := 2606
/-- Growth of an emitter. -/
abbrev EG : ℕ := 1024

/-- `omega` after unfolding the constants. -/
macro "om" : tactic => `(tactic| first | omega | (simp only [NE, NP, EG, S0] at *; omega))


theorem tb_emitU514 {j : ℕ} (hj : j ≤ 512) : TB M L (emitU tO 512 j) 514 512 :=
  (tb_emitU j).mono (by omega) (by omega)

theorem tb_emitU' {j : ℕ} (hj : j ≤ 512) : TB M L (emitU tO 512 j) NE EG :=
  (tb_emitU j).mono (by om) (by om)

/-- The slots of a tree fit. -/
def SLay.Fits (Y : SLay) : Prop :=
  Y.zero ≤ 512 ∧ Y.x1 ≤ 512 ∧ Y.x2 ≤ 512 ∧ ∀ ℓ, Y.lo ℓ ≤ 512 ∧ Y.hi ℓ ≤ 512

theorem tb_nodeP (sE nsE : ℕ → Prog 64) (Y : SLay) (hY : Y.Fits) (ℓ : ℕ) {loE hiE dE : Prog 64}
    (hs : TB M L (sE ℓ) NP EG) (hns : TB M L (nsE ℓ) NP EG) (hlo : TB M L loE NP EG)
    (hhi : TB M L hiE NP EG) (hd : TB M L dE NP EG) :
    TB M L (nodeP sE nsE Y ℓ loE hiE dE) (9 * NP) (9 * EG) := by
  have e1 : TB M L (emitU tO 512 Y.x1) NP EG := (tb_emitU' hY.2.1).mono (by om) le_rfl
  have e2 : TB M L (emitU tO 512 Y.x2) NP EG := (tb_emitU' hY.2.2.1).mono (by om) le_rfl
  exact (e1.seq <| hs.seq <| hhi.seq <| e2.seq <| hns.seq <| hlo.seq <| hd.seq <| e1.seq e2).mono
    (by om) (by om)

theorem small_b {b : Fin 64} (h : b = tb0 ∨ b = tb1 ∨ b = tb2 ∨ b = tb3) : Small b := by
  rcases h with rfl | rfl | rfl | rfl <;> (unfold Small; decide)

theorem tb_readL {b : Fin 64} (hb : Small b) : TB M L (readL b) 773 0 :=
  ((tb_dropT tTT (by unfold Small; decide)).seq <| (tb_pop_small hb).seq
    (tb_dropT tTT (by unfold Small; decide))).mono (by om) le_rfl

/-- Units of the tree of `m + 2` levels. -/
def nT : ℕ → ℕ
  | 0 => 4 * 773 + 9 * NP + 4
  | m + 1 => 2 * (nT m + 2) + 1 + 9 * NP + 2 + 2

/-- Growth of the output by the tree of `m + 2` levels. -/
def gT : ℕ → ℕ
  | 0 => 9 * EG
  | m + 1 => 2 * gT m + 9 * EG

theorem small_tc (m : ℕ) : Small (tc m) :=
  ⟨tc_ne (by decide), tc_ne (by decide), tc_ne (by decide), tc_ne (by decide)⟩

/-- **The cost of the tree code.** -/
theorem tb_treeP (sE nsE : ℕ → Prog 64) (Y : SLay) (hY : Y.Fits)
    (hs : ∀ ℓ, TB M L (sE ℓ) NE EG) (hns : ∀ ℓ, TB M L (nsE ℓ) NE EG) :
    ∀ m dE, TB M L dE NE EG → TB M L (treeP sE nsE Y m dE) (nT m) (gT m)
  | 0, dE, hd => by
    have hsrc : ∀ b b', TB M L (srcP sE nsE Y b b') NP EG := fun b b' =>
      tb_ifBit (tb_ifBit (tb_emitU' (by om)) (hns 1)) (tb_ifBit (hs 1) (tb_emitU' hY.1))
    have hn := tb_nodeP sE nsE Y hY 2 ((hs 2).mono (by om) le_rfl) ((hns 2).mono (by om) le_rfl)
      (hsrc tb0 tb1) (hsrc tb2 tb3) (hd.mono (by om) le_rfl)
    have := (tb_readL (M := M) (L := L) (small_b (Or.inl rfl))).seq <|
      (tb_readL (small_b (Or.inr (Or.inl rfl)))).seq <|
      (tb_readL (small_b (Or.inr (Or.inr (Or.inl rfl))))).seq <|
      (tb_readL (small_b (Or.inr (Or.inr (Or.inr rfl))))).seq <| hn.seq <|
      (tb_clear tb0).seq <| (tb_clear tb1).seq <| (tb_clear tb2).seq (tb_clear tb3)
    exact this.mono (by simp only [nT]; omega) (by simp [gT])
  | m + 1, dE, hd => by
    have hsub := tb_treeP sE nsE Y hY hs hns m _
      ((tb_ifBlank (i := tc m) (tb_emitU514 (hY.2.2.2 (m + 2)).2)
        (tb_emitU514 (hY.2.2.2 (m + 2)).1)).mono (by om) (by om))
    have hn := tb_nodeP sE nsE Y hY (m + 3) ((hs _).mono (by om) le_rfl)
      ((hns _).mono (by om) le_rfl) ((tb_emitU' (hY.2.2.2 (m + 2)).1).mono (by om) le_rfl)
      ((tb_emitU' (hY.2.2.2 (m + 2)).2).mono (by om) le_rfl) (hd.mono (by om) le_rfl)
    exact (tb_setLoop (small_tc m) (R := 2) (by om) hsub hn).mono (by simp only [nT]; om)
      (by simp [gT])

end AdvancedEncryption.DualUse.BpComp
