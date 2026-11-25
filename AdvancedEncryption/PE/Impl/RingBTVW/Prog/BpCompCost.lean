import PE.Impl.RingBTVW.Prog.BpCompLaw
import PE.Impl.RingBTVW.Prog.AuthBP
import SigabaNeoStd.Machines.Prog.AppendWCost

/-!
# The compiler of branching programs: cost

Per-tape bounds of `bpCompP` (`Prog.timeBoundT`, `Prog.lenBoundT`). Every tape but the output stays
small (`S0 = 128` bits) or below the input bound `L` (`IN`, `CUR`, `TT`); the output grows. A piece
of code satisfies `TB M L p n g` when, from bounds at most `bnd L a` (output `a`), it takes at most
`n` units `Uc M L` (a sweep of every tape) and ends below `bnd L (a + g)`, as long as `a + g ≤ M`.
These compose (`TB.seq`), loops multiply (`tb_loop_core`), and the tree code gets `nT m` units and
growth `gT m` by induction (`tb_treeP`).

* **`bounds_bpCompC`**: on inputs of at most `211 · 2^22` bits, at most `2^126` steps and every tape
  at most `2^62` bits (`allN_Uc_le`, `allG_le` by `decide +kernel` on numerals); generic in the input
  bound: `bounds_bpCompP`. **`size_bpCompC`**: at most `2^27` states.
* The authorization program: bounds `βA S` (small tapes exactly, `U`, `TB` at `2^26`, the rest at
  `S`), cost triples `TA`, the doubling of the offset along a family of bounds (`offBody_bounds`,
  `ta_dbl`); **`bounds_authBPC`**: on predicate words of at most `2^49` bits, at most `2^108` steps,
  every tape at most `2^49` bits (generic: `bounds_authBP`); **`size_authBPC`**: at most `2^17`.
-/

namespace AdvancedEncryption.RingBTVW.BpComp

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog
open scoped Prog

/-- The bound of the small tapes. -/
abbrev S0 : ℕ := 128

/-- The per-tape bounds: output `a`, `IN`, `CUR`, `TT` at `L + a`, the rest at `S0`. -/
def bnd (L a : ℕ) : Fin 64 → ℕ := fun t =>
  if t = tO then a else if t = tIN ∨ t = tCUR ∨ t = tTT then L + a else S0

/-- One unit: a sweep of every tape. -/
def Uc (M L : ℕ) : ℕ := 2 * (M + (L + M) + S0) + 5

/-- **A cost triple.** -/
def TB (M L : ℕ) (p : Prog 64) (n g : ℕ) : Prop :=
  ∀ a, a + g ≤ M → ∀ ℓ, ℓ ≤ bnd L a →
    timeBoundT p ℓ ≤ n * Uc M L ∧ lenBoundT p ℓ ≤ bnd L (a + g)

variable {M L : ℕ}

theorem bnd_mono {a a' : ℕ} (h : a ≤ a') : bnd L a ≤ bnd L a' := by
  intro t; simp only [bnd]; split_ifs <;> omega

theorem supB_bnd_le {a : ℕ} (ha : a ≤ M) {ℓ : Fin 64 → ℕ} (hℓ : ℓ ≤ bnd L a) :
    supB ℓ ≤ M + (L + M) + S0 :=
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
      have h1 : bnd L a x = L + a := by
        rcases hx with rfl | rfl | rfl <;> simp +decide [bnd]
      have h2 : bnd L a u = L + a := by
        rcases ht with rfl | rfl | rfl <;> simp +decide [bnd]
      omega
    · exact le_rfl

/-- The output copied to tape `0`. -/
theorem tb_copy_IN_O : TB M L (prim (.copy tIN tO)) 1 0 :=
  tb_prim _ 0 fun a u => by
    simp only [Prim.lenT, Function.update_apply, Nat.add_zero]
    split_ifs with h
    · subst h; simp +decide [bnd]
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
    (hs : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 22 → TB M L (sE ℓ) NE EG)
    (hns : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 22 → TB M L (nsE ℓ) NE EG) :
    ∀ m, m ≤ 20 → ∀ dE, TB M L dE NE EG → TB M L (treeP sE nsE Y m dE) (nT m) (gT m)
  | 0, _, dE, hd => by
    have hsrc : ∀ b b', TB M L (srcP sE nsE Y b b') NP EG := fun b b' =>
      tb_ifBit (tb_ifBit (tb_emitU' (by om)) (hns 1 le_rfl (by om)))
        (tb_ifBit (hs 1 le_rfl (by om)) (tb_emitU' hY.1))
    have hn := tb_nodeP sE nsE Y hY 2 ((hs 2 (by om) (by om)).mono (by om) le_rfl)
      ((hns 2 (by om) (by om)).mono (by om) le_rfl)
      (hsrc tb0 tb1) (hsrc tb2 tb3) (hd.mono (by om) le_rfl)
    have := (tb_readL (M := M) (L := L) (small_b (Or.inl rfl))).seq <|
      (tb_readL (small_b (Or.inr (Or.inl rfl)))).seq <|
      (tb_readL (small_b (Or.inr (Or.inr (Or.inl rfl))))).seq <|
      (tb_readL (small_b (Or.inr (Or.inr (Or.inr rfl))))).seq <| hn.seq <|
      (tb_clear tb0).seq <| (tb_clear tb1).seq <| (tb_clear tb2).seq (tb_clear tb3)
    exact this.mono (by simp only [nT]; omega) (by simp [gT])
  | m + 1, hm, dE, hd => by
    have hsub := tb_treeP sE nsE Y hY hs hns m (by omega) _
      ((tb_ifBlank (i := tc m) (tb_emitU514 (hY.2.2.2 (m + 2)).2)
        (tb_emitU514 (hY.2.2.2 (m + 2)).1)).mono (by om) (by om))
    have hn := tb_nodeP sE nsE Y hY (m + 3) ((hs _ (by omega) (by omega)).mono (by om) le_rfl)
      ((hns _ (by omega) (by omega)).mono (by om) le_rfl) ((tb_emitU' (hY.2.2.2 (m + 2)).1).mono (by om) le_rfl)
      ((tb_emitU' (hY.2.2.2 (m + 2)).2).mono (by om) le_rfl) (hd.mono (by om) le_rfl)
    exact (tb_setLoop (small_tc m) (R := 2) (by om) hsub hn).mono (by simp only [nT]; om)
      (by simp [gT])

/-! ### The emitters of the compiler -/

/-- The register slots fit in `512` bits. -/
def RL.Fits (R : RL) : Prop :=
  rs R.zero ≤ 512 ∧ rs R.x1 ≤ 512 ∧ rs R.x2 ≤ 512 ∧ rs R.out ≤ 512 ∧ rs (R.na + 8) ≤ 512 ∧
    rs (R.nz + 14) ≤ 512 ∧ ∀ ℓ, rs (R.lo ℓ) ≤ 512 ∧ rs (R.hi ℓ) ≤ 512

theorem SY_fits (R : RL) (hF : R.Fits) (i : ℕ) : (SY R i).Fits :=
  ⟨hF.1, hF.2.1, hF.2.2.1, fun ℓ => hF.2.2.2.2.2.2 ℓ⟩

theorem small_tapes : Small tIB ∧ Small tIZ ∧ Small tPB ∧ Small tPZ ∧ Small tQB ∧ Small tQZ ∧
    Small tJB ∧ Small tJZ ∧ Small tJC ∧ Small tSC ∧ Small tT31 ∧ Small tT120 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (unfold Small; decide)

theorem tb_dynE' {a b : ℕ} {xs : List (Fin 64)} (hxs : ∀ x ∈ xs, Small x) (hl : xs.length ≤ 4)
    (hab : a + b ≤ 512) : TB M L (dynE tO tA tB a xs b) NE EG := by
  refine (tb_dynE a b hxs).mono ?_ ?_
  · have := Nat.mul_le_mul_right (S0 * 4 + 4) hl; simp only [NE, S0] at *; omega
  · have := Nat.mul_le_mul_right S0 hl; simp only [EG, S0] at *; omega

theorem tb_sEd (R : RL) (hR : R.Ok) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ 22) :
    TB M L (sEd R ℓ) NE EG := by
  have hz := hR.z
  unfold sEd inE zE; split_ifs
  · exact tb_dynE' (by simp [small_tapes]) (by simp) (by omega)
  · exact tb_dynE' (by simp [small_tapes]) (by simp) (by simp only [rs] at *; omega)

theorem tb_nsEd (R : RL) (hF : R.Fits) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ 22) :
    TB M L (nsEd R ℓ) NE EG := by
  obtain ⟨-, -, -, -, h5, h6, -⟩ := hF
  unfold nsEd nselS; split_ifs
  · exact tb_emitU' (by simp only [rs] at *; omega)
  · exact tb_emitU' (by simp only [rs] at *; omega)

theorem tb_rootE (R : RL) (hR : R.Ok) : TB M L (rootE R) NE EG := by
  have hz := hR.z
  exact tb_dynE' (by simp [small_tapes]) (by simp) (by simp only [rs] at *; omega)

theorem tb_treeS (R : RL) (hR : R.Ok) (hF : R.Fits) {dE : Prog 64} (hd : TB M L dE NE EG) :
    TB M L (treeS R dE) (nT 20) (gT 20) :=
  tb_treeP _ _ _ (SY_fits R hF 0) (tb_sEd R hR) (tb_nsEd R hF) 20 le_rfl dE hd

theorem tb_insP {d a b : Prog 64} {n g : ℕ} (hd : TB M L d n g) (ha : TB M L a n g)
    (hb : TB M L b n g) : TB M L (insP d a b) (3 * n) (3 * g) :=
  (hd.seq (ha.seq hb)).mono (by omega) (by omega)

theorem tb_insL_map (f : ℕ → Prog 64) {n g : ℕ} (rest : List (Prog 64)) {n' g' : ℕ}
    (hr : TB M L (insL rest) n' g') :
    ∀ l : List ℕ, (∀ j ∈ l, TB M L (f j) n g) →
      TB M L (insL (l.map f ++ rest)) (l.length * n + n') (l.length * g + g')
  | [], _ => by simpa using hr
  | j :: l, h => by
    rw [List.map_cons, List.cons_append, insL]
    exact ((h j (by simp)).seq (tb_insL_map f rest hr l fun j' hj' => h j' (by simp [hj']))).mono
      (by simp [Nat.succ_mul]; omega) (by simp [Nat.succ_mul]; omega)

theorem tb_proP (R : RL) (hR : R.Ok) (hF : R.Fits) :
    TB M L (proP R) (22 * (3 * NE) + 1) (22 * (3 * EG)) := by
  obtain ⟨-, -, -, -, h5, h6, -⟩ := hF
  have hz := hR.z
  have h32 := tb_insL_map (M := M) (L := L)
    (fun j => insP (emitU tO 512 (rs (R.nz + j))) (zE R j) (zE R j)) (n := 3 * NE) (g := 3 * EG) []
    (tb_nop tO) (List.range 14) fun j hj => by
      have := List.mem_range.mp hj
      exact tb_insP (tb_emitU' (by simp only [rs] at *; omega))
        (tb_dynE' (by simp [small_tapes]) (by simp) (by simp only [rs] at *; omega))
        (tb_dynE' (by simp [small_tapes]) (by simp) (by simp only [rs] at *; omega))
  have h8 := tb_insL_map (M := M) (L := L)
    (fun m => insP (emitU tO 512 (rs (R.na + m))) (inE m) (inE m)) (n := 3 * NE) (g := 3 * EG) _ h32
    (List.range 8) fun m hm => by
      have := List.mem_range.mp hm
      exact tb_insP (tb_emitU' (by simp only [rs] at *; omega))
        (tb_dynE' (by simp [small_tapes]) (by simp) (by omega))
        (tb_dynE' (by simp [small_tapes]) (by simp) (by omega))
  simpa [proP, Nat.mul_comm, Nat.mul_assoc, Nat.add_mul] using
    h8.mono (n' := 22 * (3 * NE) + 1) (g' := 22 * (3 * EG)) (by simp; omega) (by simp; omega)

theorem tb_gProP (R : RL) (hR : R.Ok) (hF : R.Fits) :
    TB M L (gProP R) (3 * NE + (14 * (3 * NE) + 1)) (3 * EG + 14 * (3 * EG)) := by
  have hz := hR.z
  have h0 := hF.1
  have h32 := tb_insL_map (M := M) (L := L)
    (fun j => insP (emitU tO 512 (zS R 0 j)) (emitU tO 512 0) (emitU tO 512 0)) (n := 3 * NE)
    (g := 3 * EG) [] (tb_nop tO) (List.range 14) fun j hj => by
      have := List.mem_range.mp hj
      exact tb_insP (tb_emitU' (by simp only [zS, rs] at *; omega)) (tb_emitU' (by omega))
        (tb_emitU' (by omega))
  have h := (tb_insP (M := M) (L := L) (tb_emitU' h0) (tb_emitU' (j := 0) (by omega))
    (tb_emitU' (j := 0) (by omega))).seq h32
  simpa [gProP, insL] using h

theorem tb_tlN (t : Fin 64) : ∀ n, TB M L (tlN t n) (n + 1) 0
  | 0 => tb_nop t
  | n + 1 => ((tb_tlN t n).seq (tb_tail t)).mono (by omega) le_rfl

theorem tb_swapP : TB M L swapP 7 0 := by
  obtain ⟨-, -, hPB, hPZ, hQB, hQZ, hJB, -⟩ := small_tapes
  exact ((tb_copy_small hJB hPB).seq <| (tb_copy_small hPB hQB).seq <| (tb_copy_small hQB hJB).seq <|
    (tb_copy_small hJB hPZ).seq <| (tb_copy_small hPZ hQZ).seq <| (tb_copy_small hQZ hJB).seq
    (tb_clear tJB)).mono le_rfl le_rfl

/-- Units of one round of the loop over the state bits. -/
def jN : ℕ := nT 20 + 389

theorem tb_jBody (R : RL) (hR : R.Ok) (hF : R.Fits) : TB M L (jBody R) jN (gT 20) := by
  obtain ⟨-, -, -, -, -, -, hJB, hJZ, -, -, h31, -⟩ := small_tapes
  exact ((tb_copy_big (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl))).seq <|
    (tb_treeS R hR hF (tb_rootE R hR)).seq <| (tb_tail tJZ).seq <| (tb_copy_small hJB h31).seq
    (tb_dropT tJB hJZ)).mono (by have : jN = nT 20 + 389 := rfl; have : S0 = 128 := rfl; omega)
    (by omega)

/-- Units of a step. -/
def stepN : ℕ := 22 * (3 * NE) + 1 + 1 + (14 * (jN + 2) + 1 + 407 + 14 + 2 + 13 + 2)

/-- Growth of the output in a step. -/
def stepG : ℕ := 22 * (3 * EG) + 14 * gT 20

theorem tb_stepP (R : RL) (hR : R.Ok) (hF : R.Fits) : TB M L (stepP R) stepN stepG := by
  obtain ⟨hIB, hIZ, -, -, -, -, hJB, hJZ, hJC, -, -, h120⟩ := small_tapes
  have hrest : TB M L (cp tCUR tTT ⨾ clr tTT ⨾ clr tJB ⨾ clr tJZ ⨾ tlN tIZ 8 ⨾ cp tIB tT120 ⨾
      dropT tIB tIZ tA ⨾ swapP) 407 0 :=
    ((tb_copy_big (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))).seq <| (tb_clear tTT).seq <|
      (tb_clear tJB).seq <| (tb_clear tJZ).seq <| (tb_tlN tIZ 8).seq <|
      (tb_copy_small hIB h120).seq <| (tb_dropT tIB hIZ).seq tb_swapP).mono
      (by have : S0 = 128 := rfl; omega) le_rfl
  have h := (tb_proP R hR hF).seq <| (tb_clear tJB).seq <|
    tb_setN hJZ false (R := 13) (by decide) <|
    tb_setLoop hJC (R := 14) (by decide) (tb_jBody R hR hF) hrest
  have e1 : stepN = 22 * (3 * NE) + 1 + 1 + (14 * (jN + 2) + 1 + 407 + 14 + 2 + 13 + 2) := rfl
  have e2 : stepG = 22 * (3 * EG) + 14 * gT 20 := rfl
  exact h.mono (by omega) (by omega)

/-- Units of the last step. -/
def lastN : ℕ := 22 * (3 * NE) + 1 + 1 + nT 20 + 1

theorem tb_lastP (R : RL) (hR : R.Ok) (hF : R.Fits) :
    TB M L (lastP R) lastN (22 * (3 * EG) + gT 20) := by
  have h := (tb_proP (M := M) (L := L) R hR hF).seq <|
    (tb_copy_big (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl))).seq <|
    (tb_treeS R hR hF (tb_emitU' hF.2.2.2.1)).seq (tb_clear tTT)
  have e1 : lastN = 22 * (3 * NE) + 1 + 1 + nT 20 + 1 := rfl
  exact h.mono (by omega) (by omega)

/-- Units of the compiler. -/
def allN : ℕ :=
  3 * NE + (14 * (3 * NE) + 1) + 1 + 1 + (120 + 2) + (14 + 2) + (14 + 2) + (13 + 2) + (120 + 2) +
    (15 * (stepN + 2) + 1 + (lastN + 13) + 15 + 2)

/-- Growth of the output: the length bound of the instruction stream. -/
def allG : ℕ := 3 * EG + 14 * (3 * EG) + (15 * stepG + (22 * (3 * EG) + gT 20))

/-- **The cost of the compiler** in units. -/
theorem tb_bpCompP (R : RL) (hR : R.Ok) (hF : R.Fits) : TB M L (bpCompP R) allN allG := by
  obtain ⟨hIB, hIZ, hPB, hPZ, hQB, hQZ, -, -, -, hSC, h31, h120⟩ := small_tapes
  have hfin : TB M L (cp tIN tO ⨾ clr tO ⨾ clr tCUR ⨾ clr tIB ⨾ clr tIZ ⨾ clr tPB ⨾ clr tPZ ⨾
      clr tQB ⨾ clr tQZ ⨾ clr tT31 ⨾ clr tT120) 11 0 :=
    (tb_copy_IN_O.seq <| (tb_clear tO).seq <| (tb_clear tCUR).seq <| (tb_clear tIB).seq <|
      (tb_clear tIZ).seq <| (tb_clear tPB).seq <| (tb_clear tPZ).seq <| (tb_clear tQB).seq <|
      (tb_clear tQZ).seq <| (tb_clear tT31).seq (tb_clear tT120)).mono le_rfl le_rfl
  have h := (tb_gProP (M := M) (L := L) R hR hF).seq <|
    (tb_copy_big (Or.inr (Or.inl rfl)) (Or.inl rfl)).seq <| (tb_clear tIN).seq <|
    tb_setN hIZ false (R := 120) (by decide) <| tb_setN hPZ false (R := 14) (by decide) <|
    tb_setN hQB true (R := 14) (by decide) <| tb_setN h31 true (R := 13) (by decide) <|
    tb_setN h120 true (R := 120) (by decide) <|
    tb_setLoop hSC (R := 15) (by decide) (tb_stepP R hR hF) ((tb_lastP R hR hF).seq hfin)
  have e1 : allN = 3 * NE + (14 * (3 * NE) + 1) + 1 + 1 + (120 + 2) + (14 + 2) + (14 + 2) +
    (13 + 2) + (120 + 2) + (15 * (stepN + 2) + 1 + (lastN + 13) + 15 + 2) := rfl
  have e2 : allG = 3 * EG + 14 * (3 * EG) + (15 * stepG + (22 * (3 * EG) + gT 20)) := rfl
  exact h.mono (by omega) (by omega)

/-- The bounds of the input store: `L` bits on tape `0`. -/
def inB (L : ℕ) : Fin 64 → ℕ := Function.update (fun _ => 0) tIN L

theorem inB_le (L : ℕ) : inB L ≤ bnd L 0 := by
  intro t; simp only [inB, bnd, Function.update_apply]; split_ifs <;> simp_all

/-- **The time and tape bounds of the compiler** for inputs of at most `L` bits. -/
theorem bounds_bpCompP (R : RL) (hR : R.Ok) (hF : R.Fits) (L : ℕ) :
    timeBoundT (bpCompP R) (inB L) ≤ allN * Uc allG L ∧
      ∀ t, lenBoundT (bpCompP R) (inB L) t ≤ L + allG + S0 := by
  obtain ⟨h1, h2⟩ := tb_bpCompP (M := allG) (L := L) R hR hF 0 (by omega) (inB L) (inB_le L)
  refine ⟨h1, fun t => (h2 t).trans ?_⟩
  simp only [bnd, Nat.zero_add]; split_ifs <;> omega

/-! ### The numbers for predicate words of `211 · 2^22` bits -/

theorem allN_Uc_le : allN * Uc allG bpLenA ≤ 2 ^ 126 := by decide +kernel

theorem allG_le : bpLenA + allG + S0 ≤ 2 ^ 62 := by decide +kernel

/-- **The compiler at the predicate length**: at most `2^126` steps, every tape at most `2^62`
bits, for inputs of at most `bpLenA = 211 · 2^22` bits. -/
theorem bounds_bpCompP_conf (R : RL) (hR : R.Ok) (hF : R.Fits) :
    timeBoundT (bpCompP R) (inB bpLenA) ≤ 2 ^ 126 ∧
      ∀ t, lenBoundT (bpCompP R) (inB bpLenA) t ≤ 2 ^ 62 := by
  obtain ⟨h1, h2⟩ := bounds_bpCompP R hR hF bpLenA
  exact ⟨h1.trans allN_Uc_le, fun t => (h2 t).trans allG_le⟩

theorem Rbp_fits : Rbp.Fits :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    fun ℓ => ⟨by simp only [rs, Rbp]; omega, by simp only [rs, Rbp]; omega⟩⟩

/-- **The bounds of the compiler** `bpCompC` on inputs of at most `211 · 2^22` bits: at most `2^126`
steps, every tape at most `2^62` bits. -/
theorem bounds_bpCompC :
    timeBoundT bpCompC (inB bpLenA) ≤ 2 ^ 126 ∧ ∀ t, lenBoundT bpCompC (inB bpLenA) t ≤ 2 ^ 62 :=
  bounds_bpCompP_conf Rbp Rbp_ok Rbp_fits

/-! ### The size (states of the compiled machine) -/

theorem size_prim_le (q : Prim 64) : size (prim q) ≤ 60 := by
  cases q <;> simp [size, Prim.pad]

theorem size_seq (p q : Prog 64) : size (p ⨾ q) = size p + size q := rfl

theorem size_loop (c : Fin 64) (p : Prog 64) : size (loop c p) = size p + 39 := rfl

theorem size_snocN (o : Fin 64) (b : Bool) : ∀ n, size (snocN o b n) ≤ 60 * n + 60
  | 0 => size_prim_le _
  | n + 1 => by
    have := size_snocN o b n; have := size_prim_le (.snoc o b)
    show size (snocN o b n) + size (prim (.snoc o b)) ≤ _; omega

/-- A bound on the size of every emitter. -/
abbrev SE : ℕ := 33000

theorem size_emitU {j : ℕ} (hj : j ≤ 512) : size (emitU tO 512 j) ≤ SE := by
  have h1 := size_snocN tO true j; have h2 := size_snocN tO false (512 - j)
  show size (snocN tO true j) + size (snocN tO false (512 - j)) ≤ _
  have : SE = 33000 := rfl; omega

theorem size_appT (o x a b : Fin 64) : size (appT o x a b) ≤ 400 := by
  have := size_prim_le (.copy b x); have := size_prim_le (.copy a x)
  have := size_prim_le (.snocHead o b); have := size_prim_le (.tail b); have := size_prim_le (.clear b)
  show size (prim _) + ((size (prim _) + (size (prim _ ⨾ prim _) + 39)) + size (prim _)) ≤ _
  rw [size_seq]; omega

theorem size_appL (o a b : Fin 64) : ∀ xs : List (Fin 64), size (appL o a b xs) ≤ 400 * xs.length + 60
  | [] => size_prim_le _
  | x :: xs => by
    have := size_appT o x a b; have := size_appL o a b xs
    show size (appT o x a b) + size (appL o a b xs) ≤ _; simp; omega

theorem size_dynE {a b : ℕ} {xs : List (Fin 64)} (hl : xs.length ≤ 4) (hab : a + b ≤ 512) :
    size (dynE tO tA tB a xs b) ≤ SE := by
  have h1 := size_snocN tO true a; have h2 := size_snocN tO false b
  have h3 := size_appL tO tA tB xs
  show size (snocN tO true a) + (size (appL tO tA tB xs) + size (snocN tO false b)) ≤ _
  have : SE = 33000 := rfl; omega

/-- A bound on the size of a part of a node. -/
abbrev SP : ℕ := 4 * SE + 3

theorem size_dropT (t x a : Fin 64) : size (dropT t x a) ≤ 200 := by
  have := size_prim_le (.copy a x); have := size_prim_le (.tail t)
  show size (prim _) + (size (prim _) + 39) ≤ _; omega

theorem size_readL (b : Fin 64) : size (readL b) ≤ 500 := by
  have := size_dropT tTT tJZ tA; have := size_dropT tTT tJB tA; have := size_prim_le (.pop tTT b)
  show size (dropT tTT tJZ tA) + (size (prim _) + size (dropT tTT tJB tA)) ≤ _; omega

theorem size_nodeP (sE nsE : ℕ → Prog 64) (Y : SLay) (hY : Y.Fits) (ℓ : ℕ) {loE hiE dE : Prog 64}
    (hs : size (sE ℓ) ≤ SP) (hns : size (nsE ℓ) ≤ SP) (hlo : size loE ≤ SP) (hhi : size hiE ≤ SP)
    (hd : size dE ≤ SP) : size (nodeP sE nsE Y ℓ loE hiE dE) ≤ 9 * SP := by
  have e1 := size_emitU hY.2.1; have e2 := size_emitU hY.2.2.1
  simp only [nodeP, size_seq]
  have : SP = 4 * SE + 3 := rfl
  omega

theorem SE_le_SP : SE ≤ SP := by decide

/-- A bound on the size of the tree code of `m + 2` levels. -/
def szT : ℕ → ℕ
  | 0 => 4 * 500 + 9 * SP + 4 * 60
  | m + 1 => 60 + 180 + (szT m + 39) + 9 * SP

theorem size_treeP (sE nsE : ℕ → Prog 64) (Y : SLay) (hY : Y.Fits)
    (hs : ∀ ℓ, ℓ ≤ 22 → size (sE ℓ) ≤ SE) (hns : ∀ ℓ, ℓ ≤ 22 → size (nsE ℓ) ≤ SE) :
    ∀ m, m ≤ 20 → ∀ dE, size dE ≤ SP → size (treeP sE nsE Y m dE) ≤ szT m
  | 0, _, dE, hd => by
    have hsrc : ∀ b b', size (srcP sE nsE Y b b') ≤ SP := fun b b' => by
      have := size_emitU (j := 0) (by omega); have := size_emitU hY.1
      have := hs 1 (by omega); have := hns 1 (by omega)
      simp only [srcP, size]; have : SP = 4 * SE + 3 := rfl; omega
    have hn := size_nodeP sE nsE Y hY 2 ((hs 2 (by omega)).trans SE_le_SP)
      ((hns 2 (by omega)).trans SE_le_SP)
      (hsrc tb0 tb1) (hsrc tb2 tb3) hd
    have := size_readL tb0; have := size_readL tb1; have := size_readL tb2; have := size_readL tb3
    have : size (clr tb0) ≤ 60 := size_prim_le _; have : size (clr tb1) ≤ 60 := size_prim_le _
    have : size (clr tb2) ≤ 60 := size_prim_le _; have : size (clr tb3) ≤ 60 := size_prim_le _
    simp only [treeP, size_seq, szT]
    have : SP = 4 * SE + 3 := rfl
    omega
  | m + 1, hm, dE, hd => by
    have hsub := size_treeP sE nsE Y hY hs hns m (by omega)
      (ifBlank (tc m) (emitU tO 512 (Y.hi (m + 2))) (emitU tO 512 (Y.lo (m + 2)))) (by
        have := size_emitU (hY.2.2.2 (m + 2)).1
        have := size_emitU (hY.2.2.2 (m + 2)).2
        simp only [size]; have : SP = 4 * SE + 3 := rfl; omega)
    have hn := size_nodeP sE nsE Y hY (m + 3) ((hs _ (by omega)).trans SE_le_SP)
      ((hns _ (by omega)).trans SE_le_SP)
      ((size_emitU (hY.2.2.2 (m + 2)).1).trans SE_le_SP)
      ((size_emitU (hY.2.2.2 (m + 2)).2).trans SE_le_SP) hd
    have : size (clr (tc m)) ≤ 60 := size_prim_le _; have := size_snocN (tc m) true 2
    simp only [treeP, size_seq, szT, size_loop]
    have : SP = 4 * SE + 3 := rfl
    omega

theorem size_insL {n : ℕ} : ∀ l : List (Prog 64), (∀ p ∈ l, size p ≤ n) →
    size (insL l) ≤ l.length * n + 60
  | [], _ => by show size (prim (.copy tO tO)) ≤ _; simp [size, Prim.pad]
  | p :: l, h => by
    have := h p (by simp); have := size_insL l fun q hq => h q (by simp [hq])
    show size p + size (insL l) ≤ _; simp [Nat.succ_mul]; omega

theorem size_insP {d a b : Prog 64} {n : ℕ} (hd : size d ≤ n) (ha : size a ≤ n) (hb : size b ≤ n) :
    size (insP d a b) ≤ 3 * n := by
  show size d + (size a + size b) ≤ _; omega

theorem size_proP (R : RL) (hR : R.Ok) (hF : R.Fits) : size (proP R) ≤ 22 * (3 * SE) + 60 := by
  obtain ⟨-, -, -, -, h5, h6, -⟩ := hF
  have hz := hR.z
  unfold proP
  refine (size_insL (n := 3 * SE) _ fun p hp => ?_).trans (by simp)
  · simp only [List.mem_append, List.mem_map, List.mem_range] at hp
    rcases hp with ⟨m, hm, rfl⟩ | ⟨j, hj, rfl⟩
    · exact size_insP (size_emitU (by simp only [rs] at *; omega)) (size_dynE (by simp) (by omega))
        (size_dynE (by simp) (by omega))
    · exact size_insP (size_emitU (by simp only [rs] at *; omega))
        (size_dynE (by simp) (by simp only [rs] at *; omega))
        (size_dynE (by simp) (by simp only [rs] at *; omega))

theorem size_gProP (R : RL) (hR : R.Ok) (hF : R.Fits) : size (gProP R) ≤ 15 * (3 * SE) + 60 := by
  have hz := hR.z; have h0 := hF.1
  unfold gProP
  refine (size_insL (n := 3 * SE) _ fun p hp => ?_).trans (by simp)
  · simp only [List.mem_cons, List.mem_map, List.mem_range] at hp
    rcases hp with rfl | ⟨j, hj, rfl⟩
    · exact size_insP (size_emitU h0) (size_emitU (by omega)) (size_emitU (by omega))
    · exact size_insP (size_emitU (by simp only [zS, rs] at *; omega)) (size_emitU (by omega))
        (size_emitU (by omega))

theorem size_treeS (R : RL) (hR : R.Ok) (hF : R.Fits) {dE : Prog 64} (hd : size dE ≤ SE) :
    size (treeS R dE) ≤ szT 20 := by
  have hz := hR.z
  have h5 := hF.2.2.2.2.1; have h6 := hF.2.2.2.2.2.1
  refine size_treeP _ _ _ (SY_fits R hF 0) (fun ℓ hℓ => ?_) (fun ℓ hℓ => ?_) 20 le_rfl dE
    (hd.trans SE_le_SP)
  · unfold sEd inE zE; split_ifs
    · exact size_dynE (by simp) (by omega)
    · exact size_dynE (by simp) (by simp only [rs] at *; omega)
  · unfold nsEd nselS; split_ifs
    · exact size_emitU (by simp only [rs] at *; omega)
    · exact size_emitU (by simp only [rs] at *; omega)

theorem size_tlN (t : Fin 64) : ∀ n, size (tlN t n) ≤ 60 * n + 60
  | 0 => size_prim_le _
  | n + 1 => by
    have := size_tlN t n; have := size_prim_le (.tail t)
    show size (tlN t n) + size (prim _) ≤ _; omega

theorem size_jBody (R : RL) (hR : R.Ok) (hF : R.Fits) : size (jBody R) ≤ szT 20 + 400 := by
  have h1 := size_treeS R hR hF (dE := rootE R) (by
    unfold rootE; exact size_dynE (by simp) (by have := hR.z; omega))
  have h2 := size_dropT tJB tJZ tA
  rw [jBody, size_seq, size_seq, size_seq, size_seq]
  have : size (cp tTT tCUR) ≤ 60 := size_prim_le _; have : size (tl tJZ) ≤ 60 := size_prim_le _
  have : size (cp tJB tT31) ≤ 60 := size_prim_le _
  omega

theorem size_stepP (R : RL) (hR : R.Ok) (hF : R.Fits) :
    size (stepP R) ≤ 22 * (3 * SE) + szT 20 + 8000 := by
  have h1 := size_proP R hR hF; have h2 := size_jBody R hR hF
  have h3 := size_snocN tJZ false 13; have h4 := size_snocN tJC true 14
  have h5 := size_tlN tIZ 8; have h6 := size_dropT tIB tIZ tA
  rw [stepP]
  repeat rw [size_seq]
  rw [size_loop, swapP]
  repeat rw [size_seq]
  have : size (clr tJB) ≤ 60 := size_prim_le _; have : size (clr tJZ) ≤ 60 := size_prim_le _
  have : size (clr tJC) ≤ 60 := size_prim_le _; have : size (cp tCUR tTT) ≤ 60 := size_prim_le _
  have : size (clr tTT) ≤ 60 := size_prim_le _; have : size (cp tIB tT120) ≤ 60 := size_prim_le _
  have : size (cp tJB tPB) ≤ 60 := size_prim_le _; have : size (cp tPB tQB) ≤ 60 := size_prim_le _
  have : size (cp tQB tJB) ≤ 60 := size_prim_le _; have : size (cp tJB tPZ) ≤ 60 := size_prim_le _
  have : size (cp tPZ tQZ) ≤ 60 := size_prim_le _; have : size (cp tQZ tJB) ≤ 60 := size_prim_le _
  omega

theorem size_lastP (R : RL) (hR : R.Ok) (hF : R.Fits) :
    size (lastP R) ≤ 22 * (3 * SE) + szT 20 + 200 := by
  have h1 := size_proP R hR hF
  have h2 := size_treeS R hR hF (size_emitU (j := rs R.out) hF.2.2.2.1)
  rw [lastP, size_seq, size_seq, size_seq]
  have : size (cp tTT tCUR) ≤ 60 := size_prim_le _; have : size (clr tTT) ≤ 60 := size_prim_le _
  omega

/-- **The size of the compiler** (states of its machine): at most `2^27`. -/
theorem size_bpCompC : size bpCompC ≤ 2 ^ 27 := by
  have h1 := size_gProP Rbp Rbp_ok Rbp_fits; have h2 := size_stepP Rbp Rbp_ok Rbp_fits
  have h3 := size_lastP Rbp Rbp_ok Rbp_fits
  have h4 := size_snocN tIZ false 120; have h5 := size_snocN tPZ false 14
  have h6 := size_snocN tQB true 14; have h7 := size_snocN tT31 true 13
  have h8 := size_snocN tT120 true 120; have h9 := size_snocN tSC true 15
  have hT : szT 20 ≤ 50000000 := by decide +kernel
  rw [bpCompC, bpCompP]
  repeat rw [size_seq]
  rw [size_loop]
  have : size (cp tCUR tIN) ≤ 60 := size_prim_le _; have : size (clr tIN) ≤ 60 := size_prim_le _
  have : size (clr tIZ) ≤ 60 := size_prim_le _; have : size (clr tPZ) ≤ 60 := size_prim_le _
  have : size (clr tQB) ≤ 60 := size_prim_le _; have : size (clr tT31) ≤ 60 := size_prim_le _
  have : size (clr tT120) ≤ 60 := size_prim_le _; have : size (clr tSC) ≤ 60 := size_prim_le _
  have : size (cp tIN tO) ≤ 60 := size_prim_le _; have : size (clr tO) ≤ 60 := size_prim_le _
  have : size (clr tCUR) ≤ 60 := size_prim_le _; have : size (clr tIB) ≤ 60 := size_prim_le _
  have : size (clr tPB) ≤ 60 := size_prim_le _; have : size (clr tQZ) ≤ 60 := size_prim_le _
  have : SE = 33000 := rfl
  omega

/-! ### The cost of the authorization program -/

/-- The bounds of its tapes: the small ones exactly, `U` at `2^26`, the rest at `S`. -/
def βA (S : ℕ) : Fin 16 → ℕ := fun t =>
  if t = tZB ∨ t = tE then 14 else if t = tK ∨ t = tKC then 22 else if t = tS2 then 15 else
    if t = tU ∨ t = tTB then 2 ^ 26 else S

/-- A cost triple of the authorization program: from `βA S` to `βA S` in `n` sweeps. -/
def TA (S : ℕ) (p : Prog 16) (n : ℕ) : Prop :=
  ∀ ℓ, ℓ ≤ βA S → timeBoundT p ℓ ≤ n * (2 * S + 5) ∧ lenBoundT p ℓ ≤ βA S

variable {S : ℕ}

theorem βA_le (hS : 2 ^ 49 ≤ S) (t : Fin 16) : βA S t ≤ S := by
  simp only [βA]; split_ifs <;> omega

theorem supB_βA (hS : 2 ^ 49 ≤ S) {ℓ : Fin 16 → ℕ} (h : ℓ ≤ βA S) : supB ℓ ≤ S :=
  supB_le_of fun t => (h t).trans (βA_le hS t)

theorem TA.seq {p q : Prog 16} {n m : ℕ} (hp : TA S p n) (hq : TA S q m) : TA S (p ⨾ q) (n + m) :=
  fun ℓ hℓ => by
    have h1 := hp ℓ hℓ; have h2 := hq _ h1.2
    exact ⟨by rw [timeBoundT_seq, Nat.add_mul]; omega, h2.2⟩

theorem TA.mono {p : Prog 16} {n m : ℕ} (hp : TA S p n) (h : n ≤ m) : TA S p m := fun ℓ hℓ =>
  ⟨(hp ℓ hℓ).1.trans (Nat.mul_le_mul_right _ h), (hp ℓ hℓ).2⟩

theorem TA.ifBit {i : Fin 16} {p q : Prog 16} {n : ℕ} (hp : TA S p n) (hq : TA S q n) :
    TA S (ifBit i p q) (n + 1) := fun ℓ hℓ => by
  have h1 := hp ℓ hℓ; have h2 := hq ℓ hℓ
  refine ⟨?_, fun t => max_le (h1.2 t) (h2.2 t)⟩
  show max _ _ + 1 ≤ _; rw [Nat.add_mul, Nat.one_mul]; have := max_le h1.1 h2.1; omega

theorem TA.ifBlank {i : Fin 16} {p q : Prog 16} {n : ℕ} (hp : TA S p n) (hq : TA S q n) :
    TA S (ifBlank i p q) (n + 1) := fun ℓ hℓ => by
  have h1 := hp ℓ hℓ; have h2 := hq ℓ hℓ
  refine ⟨?_, fun t => max_le (h1.2 t) (h2.2 t)⟩
  show max _ _ + 1 ≤ _; rw [Nat.add_mul, Nat.one_mul]; have := max_le h1.1 h2.1; omega

theorem ta_prim (hS : 2 ^ 49 ≤ S) (q : Prim 16) (h : q.lenT (βA S) ≤ βA S) : TA S (prim q) 1 :=
  fun ℓ hℓ => by
    refine ⟨?_, (Prim.lenT_mono q hℓ).trans h⟩
    show 2 * (supB ℓ + q.pad) + 3 ≤ _
    have := supB_βA hS hℓ; have : q.pad ≤ 1 := by cases q <;> simp [Prim.pad]
    omega

/-- Check a primitive keeps the bounds. -/
macro "βA_tac" : tactic =>
  `(tactic| (intro t; simp only [Prim.lenT, Function.update_apply]; split_ifs <;> subst_vars <;>
    first | exact le_rfl | exact Nat.zero_le _ | (simp +decide [βA]; omega) | simp +decide [βA]))

theorem ta_loop (hS : 2 ^ 49 ≤ S) (c : Fin 16) {body : Prog 16} {n : ℕ} (hb : TA S body n) :
    TA S (loop c body) (βA S c * (n + 2) + 1) := fun ℓ hℓ => by
  have hl := loop_family c body (fun _ => βA S) (βA S c) (n * (2 * S + 5) + (2 * S + 3)) ℓ hℓ
    (hℓ c) (fun j _ => (hb _ ((tailB_le c _).trans le_rfl)).2)
    (fun j _ => by
      have := supB_βA hS (le_refl (βA S))
      have := (hb _ ((tailB_le c _).trans le_rfl)).1
      omega) (fun _ _ => le_rfl)
  refine ⟨hl.1.trans ?_, hl.2⟩
  have := Nat.zero_le (βA S c)
  nlinarith

theorem ta_dropT (hS : 2 ^ 49 ≤ S) {t x : Fin 16} (hta : t ≠ tA2) (hxa : x ≠ tA2) :
    TA S (dropT t x tA2) (3 * βA S x + 3) := fun ℓ hℓ => by
  have h := dropT_bounds hta hxa ℓ (S := S) fun u => (hℓ u).trans (βA_le hS u)
  have hx : ℓ x ≤ βA S x := hℓ x
  refine ⟨h.1.trans (Nat.mul_le_mul_right (2 * S + 5)
    (show 3 * ℓ x + 3 ≤ 3 * βA S x + 3 by omega)), h.2.trans fun u => ?_⟩
  simp only [Function.update_apply]; split_ifs with hu
  · subst hu; have := βA_le hS x; simp +decide only [βA, ↓reduceIte]; omega
  · exact hℓ u

theorem le_βA_iff {ℓ : Fin 16 → ℕ} : ℓ ≤ βA S ↔ ∀ t, ℓ t ≤ βA S t := Iff.rfl

theorem ta_natU (hS : 2 ^ 49 ≤ S) {o : Fin 16} (hoa : o ≠ tA2) (hob : o ≠ tB2) {n : ℕ}
    (hn : n ≤ βA S o) : TA S (natU o tA2 tB2 n) (12 * n + 100) := fun ℓ hℓ => by
  have h := natU_bounds hoa hob (by decide) n ℓ (S := S) (fun u => (hℓ u).trans (βA_le hS u))
    (hn.trans (βA_le hS o))
  refine ⟨h.1, fun u => (h.2 u).trans ?_⟩
  have hu : ℓ u ≤ βA S u := hℓ u
  split_ifs with h1 h2
  · subst h1; exact hn
  · have e : βA S u = S := by rcases h2 with rfl | rfl <;> simp +decide only [βA, ↓reduceIte]
    have := hn.trans (βA_le hS o); rw [e]; exact max_le (hu.trans (βA_le hS u)) (by omega)
  · exact hu

/-- Moving `n` bits into a small tape `dst` whose bound is `c`, from `c − n`. -/
theorem ta_mv (hS : 2 ^ 49 ≤ S) {src dst t z : Fin 16} (hsd : src ≠ dst) (hst : src ≠ t)
    (hdt : dst ≠ t) (n : ℕ) (ht : βA S t = S) {rest : Prog 16} {m : ℕ} (hr : TA S rest m)
    (ℓ : Fin 16 → ℕ) (hℓ : ℓ ≤ βA S) (hd : ℓ dst + n ≤ βA S dst) :
    timeBoundT (iter z (pp src t ⨾ prim (.snocHead dst t) ⨾ clr t) n ⨾ rest) ℓ ≤
        (3 * n + 1 + m) * (2 * S + 5) ∧
      lenBoundT (iter z (pp src t ⨾ prim (.snocHead dst t) ⨾ clr t) n ⨾ rest) ℓ ≤ βA S := by
  have h := iter_mv_bounds z hsd hst hdt n ℓ (S := S) (fun u => (hℓ u).trans (βA_le hS u))
    (hd.trans (βA_le hS dst)) (by omega)
  have hle : lenBoundT (iter z (pp src t ⨾ prim (.snocHead dst t) ⨾ clr t) n) ℓ ≤ βA S := fun u => by
    refine (h.2 u).trans ?_
    have hu : ℓ u ≤ βA S u := hℓ u
    split_ifs with h1 h2
    · subst h1; exact hd
    · subst h2; rw [ht]; exact max_le (hu.trans (βA_le hS u)) (by omega)
    · exact hu
  have h2 := hr _ hle
  exact ⟨by rw [timeBoundT_seq]; nlinarith [h.1, h2.1], h2.2⟩

/-- The bounds in round `j` of the doubling: `U` at `14 (2^j − 1)`. -/
def γU (S j : ℕ) : Fin 16 → ℕ := Function.update (βA S) tU (14 * 2 ^ j - 14)

theorem γU_le {j : ℕ} (hj : j ≤ 22) (t : Fin 16) : γU S j t ≤ βA S t := by
  have : 2 ^ j ≤ 2 ^ 22 := Nat.pow_le_pow_right (by norm_num) hj
  simp only [γU, Function.update_apply]; split_ifs with h
  · subst h; simp +decide only [βA, ↓reduceIte]; omega
  · exact le_rfl

/-- One round of the doubling. -/
theorem offBody_bounds (hS : 2 ^ 49 ≤ S) (j : ℕ) (hj : j < 22) (ℓ0 : Fin 16 → ℕ) (h0 : ℓ0 ≤ γU S j) :
    timeBoundT (pp tK tBit ⨾ appT tU tU tA2 tB2 ⨾ ifBit tBit (appT tU tE tA2 tB2) (nop tU) ⨾
        clr tBit) ℓ0 ≤ (4 * 2 ^ 26 + 150) * (2 * S + 5) ∧
      lenBoundT (pp tK tBit ⨾ appT tU tU tA2 tB2 ⨾ ifBit tBit (appT tU tE tA2 tB2) (nop tU) ⨾
        clr tBit) ℓ0 ≤ γU S (j + 1) := by
  have hP1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have hP : 2 ^ j ≤ 2 ^ 22 := Nat.pow_le_pow_right (by norm_num) hj.le
  have hP2 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
  have hγ : ∀ t, γU S j t ≤ S := fun t => (γU_le hj.le t).trans (βA_le hS t)
  have hγU : γU S j tU = 14 * 2 ^ j - 14 := by simp [γU]
  have hγE : γU S j tE = 14 := by simp +decide [γU, βA]
  let ℓa : Fin 16 → ℕ := Prim.lenT (.pop tK tBit) ℓ0
  have hℓa : ∀ t, ℓa t ≤ γU S j t := fun t => by
    have h1 : ℓ0 t ≤ γU S j t := h0 t
    have h2 : ℓ0 tK ≤ γU S j tK := h0 tK
    have hK : γU S j tK = 22 := by simp +decide [γU, βA]
    have hB : γU S j tBit = S := by simp +decide [γU, βA]
    simp only [ℓa, Prim.lenT, Function.update_apply]
    split_ifs with h3 h4 <;> subst_vars <;> omega
  have hS0 : ∀ t, ℓa t ≤ S := fun t => (hℓa t).trans (hγ t)
  have hUa : ℓa tU ≤ 14 * 2 ^ j - 14 := hγU ▸ hℓa tU
  have hEa : ℓa tE ≤ 14 := hγE ▸ hℓa tE
  have ap1 := appT_bounds (o := tU) (x := tU) (a := tA2) (b := tB2) (by decide) (by decide)
    (by decide) (by decide) (by decide) ℓa (S := S) hS0 (by omega)
  let B1 : Fin 16 → ℕ := fun u =>
    if u = tU then ℓa tU + ℓa tU else if u = tA2 then ℓa tU else if u = tB2 then 0 else ℓa u
  have hB1 : ∀ u, B1 u ≤ S := fun u => by
    simp only [B1]; split_ifs <;> first | omega | exact hS0 u
  have ap2 := appT_bounds (o := tU) (x := tE) (a := tA2) (b := tB2) (by decide) (by decide)
    (by decide) (by decide) (by decide) B1 (S := S) hB1 (by simp +decide [B1]; omega)
  have hB1E : B1 tE = ℓa tE := by simp +decide [B1]
  have hB1U : B1 tU = ℓa tU + ℓa tU := by simp [B1]
  -- the bounds after the first append, the branch, the last clear
  let ℓb := lenBoundT (appT tU tU tA2 tB2) ℓa
  have hb : ℓb ≤ B1 := fun u => ap1.2 u
  have hnop : lenBoundT (nop tU) ℓb = ℓb := by
    show Prim.lenT (.copy tU tU) ℓb = ℓb; simp [Prim.lenT]
  let B2 : Fin 16 → ℕ := fun u =>
    if u = tU then B1 tU + B1 tE else if u = tA2 then B1 tE else if u = tB2 then 0 else B1 u
  have hc : lenBoundT (ifBit tBit (appT tU tE tA2 tB2) (nop tU)) ℓb ≤ fun u => max (B2 u) (B1 u) :=
    fun u => max_le_max ((lenBoundT_mono _ hb u).trans (ap2.2 u)) (by rw [hnop]; exact hb u)
  have hcS : ∀ u, max (B2 u) (B1 u) ≤ S := fun u => max_le (by
    simp only [B2]; split_ifs <;> first | omega | exact hB1 u) (hB1 u)
  have hSB : ∀ {ℓ : Fin 16 → ℕ}, (∀ u, ℓ u ≤ S) → 2 * (supB ℓ + 0) + 3 ≤ 2 * S + 5 := fun h => by
    have := supB_le_of h; omega
  refine ⟨?_, fun t => ?_⟩
  · show timeBoundT (prim (.pop tK tBit)) ℓ0 + (timeBoundT (appT tU tU tA2 tB2) ℓa +
      (timeBoundT (ifBit tBit (appT tU tE tA2 tB2) (nop tU)) ℓb +
        timeBoundT (prim (.clear tBit)) (lenBoundT (ifBit tBit (appT tU tE tA2 tB2) (nop tU)) ℓb))) ≤ _
    have t1 : timeBoundT (prim (.pop tK tBit)) ℓ0 ≤ 2 * S + 5 :=
      hSB fun u => (h0 u).trans (hγ u)
    have t2 : timeBoundT (appT tU tU tA2 tB2) ℓa ≤ (4 * 2 ^ 26 + 6) * (2 * S + 5) :=
      ap1.1.trans (Nat.mul_le_mul_right _ (by omega))
    have t3 : timeBoundT (ifBit tBit (appT tU tE tA2 tB2) (nop tU)) ℓb ≤ 135 * (2 * S + 5) := by
      show max _ _ + 1 ≤ _
      have a1 := (timeBoundT_mono _ hb).trans ap2.1
      rw [hB1E] at a1
      have a2 : timeBoundT (nop tU) ℓb ≤ 2 * S + 5 := hSB fun u => (hb u).trans (hB1 u)
      have : (4 * ℓa tE + 6) * (2 * S + 5) ≤ 134 * (2 * S + 5) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have t4 : timeBoundT (prim (.clear tBit))
        (lenBoundT (ifBit tBit (appT tU tE tA2 tB2) (nop tU)) ℓb) ≤ 2 * S + 5 :=
      hSB fun u => (hc u).trans (hcS u)
    nlinarith
  · show Prim.lenT (.clear tBit) (lenBoundT (ifBit tBit (appT tU tE tA2 tB2) (nop tU)) ℓb) t ≤ _
    have h := hc t
    simp only [Prim.lenT, Function.update_apply]
    split_ifs with ht
    · exact Nat.zero_le _
    · refine h.trans (max_le ?_ ?_)
      · simp only [B2]
        split_ifs with h1 h2 h3
        · subst h1; simp only [γU, Function.update_self]; rw [hB1U, hB1E, hP2]; omega
        · subst h2; simp +decide only [γU, βA, Function.update_apply, ↓reduceIte]; omega
        · exact Nat.zero_le _
        · simp only [B1, h1, h2, h3, ↓reduceIte]
          have := hℓa t
          simp only [γU, Function.update_apply, h1, ↓reduceIte] at this ⊢; exact this
      · simp only [B1]
        split_ifs with h1 h2 h3
        · subst h1; simp only [γU, Function.update_self]; rw [hP2]; omega
        · subst h2; simp +decide only [γU, βA, Function.update_apply, ↓reduceIte]; omega
        · exact Nat.zero_le _
        · have := hℓa t
          simp only [γU, Function.update_apply, h1, ↓reduceIte] at this ⊢; exact this

/-- **The doubling loop** of `offP`. -/
theorem ta_dbl (hS : 2 ^ 49 ≤ S) :
    TA S (clr tU ⨾ forN tKC tK (pp tK tBit ⨾ appT tU tU tA2 tB2 ⨾
      ifBit tBit (appT tU tE tA2 tB2) (nop tU) ⨾ clr tBit)) (22 * (4 * 2 ^ 26 + 152) + 45) :=
  fun ℓ hℓ => by
  let ℓ1 : Fin 16 → ℕ := Function.update ℓ tU 0
  let ℓ2 : Fin 16 → ℕ := Function.update ℓ1 tKC (ℓ1 tK)
  have hK : ℓ tK ≤ 22 := by have := hℓ tK; simpa +decide [βA] using this
  have h2 : ℓ2 ≤ γU S 0 := fun t => by
    have := hℓ t
    simp only [ℓ2, ℓ1, γU, Function.update_apply]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all +decide [βA]
  have hl := loop_family tKC _ (γU S) 22 ((4 * 2 ^ 26 + 150) * (2 * S + 5) + (2 * S + 3)) ℓ2 h2
    (by simp only [ℓ2, ℓ1, Function.update_self]; simp +decide; omega)
    (fun j hj => (offBody_bounds hS j hj _ (tailB_le _ _)).2)
    (fun j hj => by
      have := (offBody_bounds hS j hj _ (tailB_le tKC (γU S j))).1
      have := supB_le_of fun t => (γU_le (S := S) (j := j) (by omega) t).trans (βA_le hS t)
      omega)
    (fun j hj t => by
      have h1 : 2 ^ j ≤ 2 ^ 22 := Nat.pow_le_pow_right (by norm_num) hj
      simp only [γU, Function.update_apply]; split_ifs <;> omega)
  have hS0 : ∀ {ℓ' : Fin 16 → ℕ}, ℓ' ≤ βA S → 2 * (supB ℓ' + 0) + 3 ≤ 2 * S + 5 := fun h => by
    have := supB_βA hS h; omega
  have h1le : ℓ1 ≤ βA S := fun t => by
    have := hℓ t; simp only [ℓ1, Function.update_apply]; split_ifs <;> omega
  refine ⟨?_, ?_⟩
  · show timeBoundT (prim (.clear tU)) ℓ + (timeBoundT (prim (.copy tKC tK)) ℓ1 +
      timeBoundT (loop tKC _) ℓ2) ≤ _
    have t1 : timeBoundT (prim (.clear tU)) ℓ ≤ 2 * S + 5 := hS0 hℓ
    have t2 : timeBoundT (prim (.copy tKC tK)) ℓ1 ≤ 2 * S + 5 := hS0 h1le
    have t3 := hl.1
    have e : (22 * (4 * 2 ^ 26 + 152) + 45) * (2 * S + 5) =
      22 * ((4 * 2 ^ 26 + 150) * (2 * S + 5)) + 89 * (2 * S + 5) := by ring
    omega
  · show lenBoundT (loop tKC _) ℓ2 ≤ _
    exact hl.2.trans fun t => γU_le le_rfl t

theorem ta_offP (hS : 2 ^ 49 ≤ S) : TA S offP (1 + (3 * 8 + 1 + (22 * (4 * 2 ^ 26 + 152) + 45))) :=
  fun ℓ hℓ => by
  let ℓ1 : Fin 16 → ℕ := Function.update ℓ tK (ℓ tZB)
  have hZ : ℓ tZB ≤ 14 := by have := hℓ tZB; simpa +decide [βA] using this
  have h1 : ℓ1 ≤ βA S := fun t => by
    have := hℓ t; simp only [ℓ1, Function.update_apply]; split_ifs with h
    · subst h; simp +decide [βA]; omega
    · exact this
  have hm := ta_mv hS (src := tX) (dst := tK) (t := tBit) (z := tK) (by decide) (by decide)
    (by decide) 8 (by simp +decide [βA]) (ta_dbl hS) ℓ1 h1
    (by simp only [ℓ1, Function.update_self]; simp +decide [βA]; omega)
  have t0 : timeBoundT (prim (.copy tK tZB)) ℓ ≤ 2 * S + 5 := by
    show 2 * (supB ℓ + 0) + 3 ≤ _; have := supB_βA hS hℓ; omega
  refine ⟨?_, hm.2⟩
  show timeBoundT (prim (.copy tK tZB)) ℓ + timeBoundT _ ℓ1 ≤ _
  nlinarith [hm.1]

/-- A constant word on a tape after clearing it. -/
theorem ta_setN (hS : 2 ^ 49 ≤ S) {c : Fin 16} (b : Bool) {n : ℕ} (hn : n ≤ βA S c)
    {rest : Prog 16} {m : ℕ} (hr : TA S rest m) : TA S (clr c ⨾ snocN c b n ⨾ rest) (1 + (n + 1 + m)) :=
  fun ℓ hℓ => by
  let ℓ1 : Fin 16 → ℕ := Function.update ℓ c 0
  have hS1 : ∀ t, ℓ1 t ≤ S := fun t => by
    simp only [ℓ1, Function.update_apply]; split_ifs
    · exact Nat.zero_le _
    · exact (hℓ t).trans (βA_le hS t)
  have hsn := snocN_bounds c b n ℓ1 hS1 (by simp [ℓ1]; exact hn.trans (βA_le hS c))
  have hle : Function.update ℓ1 c (ℓ1 c + n) ≤ βA S := fun t => by
    simp only [ℓ1, Function.update_apply]; split_ifs with h
    · subst h; simp; exact hn
    · exact hℓ t
  have hr' := hr _ hle
  refine ⟨?_, ?_⟩
  · show timeBoundT (prim (.clear c)) ℓ + (timeBoundT (snocN c b n) ℓ1 +
      timeBoundT rest (lenBoundT (snocN c b n) ℓ1)) ≤ _
    rw [hsn.2]
    have : timeBoundT (prim (.clear c)) ℓ ≤ 2 * S + 5 := by
      show 2 * (supB ℓ + 0) + 3 ≤ _; have := supB_βA hS hℓ; omega
    nlinarith [hsn.1, hr'.1]
  · show lenBoundT rest (lenBoundT (snocN c b n) ℓ1) ≤ _
    rw [hsn.2]; exact hr'.2

/-- Writing one bit on a tape. -/
theorem ta_setB (hS : 2 ^ 49 ≤ S) {c : Fin 16} (b : Bool) (hc : 1 ≤ βA S c) : TA S (setB c b) 2 :=
  fun ℓ hℓ => by
  let ℓ1 : Fin 16 → ℕ := Function.update ℓ c 0
  have h1 : ℓ1 ≤ βA S := fun t => by
    simp only [ℓ1, Function.update_apply]; split_ifs
    · exact Nat.zero_le _
    · exact hℓ t
  have h2 : Prim.lenT (.snoc c b) ℓ1 ≤ βA S := fun t => by
    simp only [ℓ1, Prim.lenT, Function.update_apply]; split_ifs with h
    · subst h; simp; exact hc
    · exact hℓ t
  refine ⟨?_, h2⟩
  show 2 * (supB ℓ + 0) + 3 + (2 * (supB ℓ1 + 1) + 3) ≤ _
  have := supB_βA hS hℓ; have := supB_βA hS h1; omega

/-- Clear a tape and write one bit, then the rest. -/
theorem ta_clrSnoc (hS : 2 ^ 49 ≤ S) {c : Fin 16} (b : Bool) (hc : 1 ≤ βA S c) {rest : Prog 16}
    {m : ℕ} (hr : TA S rest m) : TA S (clr c ⨾ prim (.snoc c b) ⨾ rest) (2 + m) := fun ℓ hℓ => by
  have h := (ta_setB hS b hc) ℓ hℓ
  have h2 := hr _ h.2
  refine ⟨?_, h2.2⟩
  show timeBoundT (prim (.clear c)) ℓ + (timeBoundT (prim (.snoc c b)) (lenBoundT (prim (.clear c)) ℓ) +
    timeBoundT rest (lenBoundT (prim (.snoc c b)) (lenBoundT (prim (.clear c)) ℓ))) ≤ _
  have h1 : timeBoundT (prim (.clear c)) ℓ + timeBoundT (prim (.snoc c b))
      (lenBoundT (prim (.clear c)) ℓ) ≤ 2 * (2 * S + 5) := h.1
  have h3 : timeBoundT rest (lenBoundT (prim (.snoc c b)) (lenBoundT (prim (.clear c)) ℓ)) ≤
      m * (2 * S + 5) := h2.1
  nlinarith

theorem ta_mv32 (hS : 2 ^ 49 ≤ S) {rest : Prog 16} {m : ℕ} (hr : TA S rest m) :
    TA S (clr tZB ⨾ iter tT2 (pp tT2 tBit ⨾ prim (.snocHead tZB tBit) ⨾ clr tBit) 14 ⨾ rest)
      (1 + (3 * 14 + 1 + m)) := fun ℓ hℓ => by
  let ℓ1 : Fin 16 → ℕ := Function.update ℓ tZB 0
  have h1 : ℓ1 ≤ βA S := fun t => by
    simp only [ℓ1, Function.update_apply]; split_ifs
    · exact Nat.zero_le _
    · exact hℓ t
  have hm := ta_mv hS (src := tT2) (dst := tZB) (t := tBit) (z := tT2) (by decide) (by decide)
    (by decide) 14 (by simp +decide [βA]) hr ℓ1 h1 (by simp +decide [ℓ1, βA])
  refine ⟨?_, hm.2⟩
  show timeBoundT (prim (.clear tZB)) ℓ + timeBoundT _ ℓ1 ≤ _
  have : timeBoundT (prim (.clear tZB)) ℓ ≤ 2 * S + 5 := by
    show 2 * (supB ℓ + 0) + 3 ≤ _; have := supB_βA hS hℓ; omega
  nlinarith [hm.1]

/-- Units of the offset computation. -/
abbrev offN : ℕ := 1 + (3 * 8 + 1 + (22 * (4 * 2 ^ 26 + 152) + 45))

/-- Units of a step of the authorization program. -/
abbrev stepAN : ℕ := offN + (1 + ((3 * 2 ^ 26 + 3) + (1 + (3 * 14 + 1 + (1 + ((3 * 2 ^ 26 + 3) + 1))))))

theorem ta_stepA (hS : 2 ^ 49 ≤ S) : TA S stepA stepAN := by
  have hU : βA S tU = 2 ^ 26 := by simp +decide [βA]
  have hTB : βA S tTB = 2 ^ 26 := by simp +decide [βA]
  have := (ta_offP hS).seq <| (ta_prim hS (.copy tT2 tCU) (by βA_tac)).seq <|
    ((ta_dropT hS (t := tT2) (x := tU) (by decide) (by decide)).seq <| ta_mv32 hS <|
      (ta_prim hS (.clear tT2) (by βA_tac)).seq <|
      (ta_dropT hS (t := tCU) (x := tTB) (by decide) (by decide)).seq
        (ta_prim hS (.clear tU) (by βA_tac)))
  rw [hU, hTB] at this
  exact this

theorem ta_initA (hS : 2 ^ 49 ≤ S) :
    TA S initA ((12 * tblW + 100) + ((12 * 14 + 100) + (1 + (1 + (14 + 1 + (12 * 15 + 100)))))) :=
  (ta_natU hS (o := tTB) (by decide) (by decide) (n := tblW) (by simp +decide [βA, tblW])).seq <|
    (ta_natU hS (o := tE) (by decide) (by decide) (n := 14) (by simp +decide [βA])).seq <|
    (ta_prim hS (.copy tCU tC) (by βA_tac)).seq <|
    ta_setN hS false (c := tZB) (n := 14) (by simp +decide [βA])
      (ta_natU hS (o := tS2) (by decide) (by decide) (n := 15) (by simp +decide [βA]))

theorem ta_lenA (hS : 2 ^ 49 ≤ S) :
    TA S (Prog.map uL (lenEqP bpLenA)) ((12 * bpLenA + 100) + (1 + ((3 * S + 3) +
      (((3 * S + 3) + (2 + 1) + 1) + (1 + 1))))) := by
  have hLT : βA S tLT = S := by simp +decide [βA]
  have hbp : bpLenA ≤ βA S tLT := by rw [hLT]; simp only [bpLenA]; omega
  have hC : βA S tC = S := by simp +decide [βA]
  have h1 : 1 ≤ βA S tF := by simp +decide [βA]; omega
  have hB : TA S (dropT tLT tC tA2 ⨾ ifBlank tLT (setB tF true) (setB tF false)) ((3 * S + 3) + (2 + 1)) := by
    have := (ta_dropT hS (t := tLT) (x := tC) (by decide) (by decide)).seq
      (TA.ifBlank (i := tLT) (ta_setB hS true h1) (ta_setB hS false h1))
    rwa [hC] at this
  have h := (ta_natU hS (o := tLT) (by decide) (by decide) hbp).seq <|
    (ta_prim hS (.copy tT2 tC) (by βA_tac)).seq <|
    ((ta_dropT hS (t := tT2) (x := tLT) (by decide) (by decide)).seq <|
      (TA.ifBlank (i := tT2) hB ((ta_setB hS false h1).mono (by omega))).seq <|
      (ta_prim hS (.clear tLT) (by βA_tac)).seq (ta_prim hS (.clear tT2) (by βA_tac)))
  rw [hLT] at h
  rw [map_lenEqP]
  exact h

theorem ta_lastA (hS : 2 ^ 49 ≤ S) :
    TA S lastA (2 + (offN + (1 + ((3 * 2 ^ 26 + 3) + 1)))) := by
  have hU : βA S tU = 2 ^ 26 := by simp +decide [βA]
  have := ta_clrSnoc hS true (c := tE) (by simp +decide [βA]) <|
    (ta_offP hS).seq <| (ta_prim hS (.copy tT2 tCU) (by βA_tac)).seq <|
      (ta_dropT hS (t := tT2) (x := tU) (by decide) (by decide)).seq
        (ta_prim hS (.pop tT2 tBit) (by βA_tac))
  rw [hU] at this
  exact this

theorem ta_outA (hS : 2 ^ 49 ≤ S) : TA S outA' (1 + (2 + 1 + 1)) := by
  have h1 : 1 ≤ βA S tC := by simp +decide [βA]; omega
  exact (ta_prim hS (.clear tC) (by βA_tac)).seq
    (TA.ifBit (TA.ifBit (ta_setB hS false h1) (ta_setB hS true h1)) ((ta_setB hS false h1).mono (by omega)))

theorem ta_clrA (hS : 2 ^ 49 ≤ S) : TA S clrA 10 := by
  have := (ta_prim hS (.clear tX) (by βA_tac)).seq <| (ta_prim hS (.clear tCU) (by βA_tac)).seq <|
    (ta_prim hS (.clear tZB) (by βA_tac)).seq <| (ta_prim hS (.clear tK) (by βA_tac)).seq <|
    (ta_prim hS (.clear tU) (by βA_tac)).seq <| (ta_prim hS (.clear tE) (by βA_tac)).seq <|
    (ta_prim hS (.clear tT2) (by βA_tac)).seq <| (ta_prim hS (.clear tTB) (by βA_tac)).seq <|
    (ta_prim hS (.clear tBit) (by βA_tac)).seq (ta_prim hS (.clear tF) (by βA_tac))
  exact this

/-- Units of the authorization program for tapes of at most `S` bits. -/
def authN (S : ℕ) : ℕ :=
  ((12 * bpLenA + 100) + (1 + ((3 * S + 3) + (((3 * S + 3) + (2 + 1) + 1) + (1 + 1))))) +
    (((12 * tblW + 100) + ((12 * 14 + 100) + (1 + (1 + (14 + 1 + (12 * 15 + 100)))))) +
      ((15 * (stepAN + 2) + 1) + ((2 + (offN + (1 + ((3 * 2 ^ 26 + 3) + 1)))) +
        ((1 + (2 + 1 + 1)) + 10))))

theorem ta_authBP (hS : 2 ^ 49 ≤ S) : TA S authBP (authN S) := by
  have hS2 : βA S tS2 = 15 := by simp +decide [βA]
  have hl := ta_loop hS tS2 (ta_stepA hS)
  rw [hS2] at hl
  exact (ta_lenA hS).seq <| (ta_initA hS).seq <| hl.seq <| (ta_lastA hS).seq <|
    (ta_outA hS).seq (ta_clrA hS)

/-- The bounds of the input store: `L` bits on tape `0`, `128` on tape `1`. -/
def inBA (L : ℕ) : Fin 16 → ℕ := Function.update (Function.update (fun _ => 0) tC L) tX 128

/-- **The bounds of the authorization program** for predicate words of at most `L ≤ S` bits. -/
theorem bounds_authBP (hS : 2 ^ 49 ≤ S) {L : ℕ} (hL : L ≤ S) :
    timeBoundT authBP (inBA L) ≤ authN S * (2 * S + 5) ∧ ∀ t, lenBoundT authBP (inBA L) t ≤ S := by
  have h := ta_authBP hS (inBA L) fun t => by
    simp only [inBA, Function.update_apply]
    split_ifs with h1 h2
    · subst h1; simp +decide [βA]; omega
    · subst h2; simp +decide [βA]; omega
    · exact Nat.zero_le _
  exact ⟨h.1, fun t => (h.2 t).trans (βA_le hS t)⟩

theorem authN_le : authN (2 ^ 49) * (2 * 2 ^ 49 + 5) ≤ 2 ^ 108 := by decide +kernel

/-- **The authorization program** `authBPC` on predicate words of at most `2^49` bits (the class
has `211 · 2^22`): at most `2^108` steps, every tape at most `2^49` bits. -/
theorem bounds_authBPC {L : ℕ} (hL : L ≤ 2 ^ 49) :
    timeBoundT authBPC (inBA L) ≤ 2 ^ 108 ∧ ∀ t, lenBoundT authBPC (inBA L) t ≤ 2 ^ 49 := by
  obtain ⟨h1, h2⟩ := bounds_authBP (S := 2 ^ 49) le_rfl hL
  exact ⟨h1.trans authN_le, h2⟩

/-! ### The size of the authorization program -/

theorem size_prim16 (q : Prim 16) : size (prim q) ≤ 60 := size_prim_le' q

theorem size_iter16 (z : Fin 16) (p : Prog 16) : ∀ n, size (iter z p n) ≤ n * size p + 60
  | 0 => by show size (prim (.copy z z)) ≤ _; have := size_prim16 (.copy z z); omega
  | n + 1 => by
    have := size_iter16 z p n
    show size p + size (iter z p n) ≤ _; rw [Nat.succ_mul]; omega

theorem size_snocN16 (o : Fin 16) (b : Bool) : ∀ n, size (snocN o b n) ≤ 60 * n + 60
  | 0 => size_prim16 _
  | n + 1 => by
    have := size_snocN16 o b n; have := size_prim16 (.snoc o b)
    show size (snocN o b n) + size (prim (.snoc o b)) ≤ _; omega

theorem log2_lt_of {n k : ℕ} (h : n < 2 ^ k) : Nat.log2 n ≤ k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact ((Nat.log2_lt (by omega)).mpr h).le

theorem size_offP : size offP ≤ 3000 := by
  have hmv : size (pp tX tBit ⨾ prim (.snocHead tK tBit) ⨾ clr tBit) ≤ 180 := by
    have : size (pp tX tBit) ≤ 60 := size_prim16 _
    have : size (prim (.snocHead tK tBit)) ≤ 60 := size_prim16 _
    have : size (clr tBit) ≤ 60 := size_prim16 _
    show size _ + (size _ + size _) ≤ _; omega
  have hi := size_iter16 tK (pp tX tBit ⨾ prim (.snocHead tK tBit) ⨾ clr tBit) 8
  have a1 := size_appT_le tU tU tA2 tB2; have a2 := size_appT_le tU tE tA2 tB2
  have : size (cp tK tZB) ≤ 60 := size_prim16 _
  have : size (clr tU) ≤ 60 := size_prim16 _
  have : size (cp tKC tK) ≤ 60 := size_prim16 _
  have : size (pp tK tBit) ≤ 60 := size_prim16 _
  have : size (nop tU) ≤ 60 := size_prim16 _
  have : size (clr tBit) ≤ 60 := size_prim16 _
  show size (cp tK tZB) + (size (iter tK (pp tX tBit ⨾ prim (.snocHead tK tBit) ⨾ clr tBit) 8) +
    (size (clr tU) + (size (cp tKC tK) + (size (pp tK tBit) + (size (appT tU tU tA2 tB2) +
      ((size (appT tU tE tA2 tB2) + size (nop tU) + 1) + size (clr tBit))) + 39)))) ≤ _
  omega

theorem size_dropT16 (t x a : Fin 16) : size (dropT t x a) ≤ 200 := by
  have := size_prim16 (.copy a x); have := size_prim16 (.tail t)
  show size (prim _) + (size (prim _) + 39) ≤ _; omega

theorem size_stepA : size stepA ≤ 10000 := by
  have := size_offP
  have hmv : size (pp tT2 tBit ⨾ prim (.snocHead tZB tBit) ⨾ clr tBit) ≤ 180 := by
    have : size (pp tT2 tBit) ≤ 60 := size_prim16 _
    have : size (prim (.snocHead tZB tBit)) ≤ 60 := size_prim16 _
    have : size (clr tBit) ≤ 60 := size_prim16 _
    show size _ + (size _ + size _) ≤ _; omega
  have hi := size_iter16 tT2 (pp tT2 tBit ⨾ prim (.snocHead tZB tBit) ⨾ clr tBit) 14
  have := size_dropT16 tT2 tU tA2; have := size_dropT16 tCU tTB tA2
  have : size (cp tT2 tCU) ≤ 60 := size_prim16 _
  have : size (clr tZB) ≤ 60 := size_prim16 _
  have : size (clr tT2) ≤ 60 := size_prim16 _
  have : size (clr tU) ≤ 60 := size_prim16 _
  show size offP + (size (cp tT2 tCU) + (size (dropT tT2 tU tA2) + (size (clr tZB) +
    (size (iter tT2 (pp tT2 tBit ⨾ prim (.snocHead tZB tBit) ⨾ clr tBit) 14) + (size (clr tT2) +
      (size (dropT tCU tTB tA2) + size (clr tU))))))) ≤ _
  omega

/-- **The size of the authorization program**: at most `2^17` states. -/
theorem size_authBPC : size authBPC ≤ 2 ^ 17 := by
  have hl : size (Prog.map uL (lenEqP bpLenA)) ≤ 500 * 49 + 2000 := by
    rw [size_map]
    have := size_lenEqP bpLenA
    have : Nat.log2 bpLenA ≤ 49 := log2_lt_of (by simp only [bpLenA]; norm_num)
    omega
  have hTB : Nat.log2 tblW ≤ 46 := log2_lt_of (by simp only [tblW]; norm_num)
  have h1 := size_natU tTB tA2 tB2 tblW; have h2 := size_natU tE tA2 tB2 14
  have h3 := size_natU tS2 tA2 tB2 15
  have h32 : Nat.log2 14 ≤ 6 := log2_lt_of (by norm_num)
  have h15 : Nat.log2 15 ≤ 4 := log2_lt_of (by norm_num)
  have hz := size_snocN16 tZB false 14
  have hs := size_stepA; have ho := size_offP
  have hd := size_dropT16 tT2 tU tA2
  have hsB : ∀ b, size (setB tC b) ≤ 120 := fun b => by
    have := size_prim16 (.clear tC); have := size_prim16 (.snoc tC b)
    show size (prim _) + size (prim _) ≤ _; omega
  have := hsB true; have := hsB false
  have : size (cp tCU tC) ≤ 60 := size_prim16 _
  have : size (clr tZB) ≤ 60 := size_prim16 _
  have : size (clr tE) ≤ 60 := size_prim16 _
  have : size (prim (.snoc tE true)) ≤ 60 := size_prim16 _
  have : size (cp tT2 tCU) ≤ 60 := size_prim16 _
  have : size (pp tT2 tBit) ≤ 60 := size_prim16 _
  have : size (clr tC) ≤ 60 := size_prim16 _
  have hc : size clrA ≤ 600 := by
    have hcl : ∀ t : Fin 16, size (clr t) ≤ 60 := fun t => size_prim16 _
    have := hcl tX; have := hcl tCU; have := hcl tZB; have := hcl tK; have := hcl tU
    have := hcl tE; have := hcl tT2; have := hcl tTB; have := hcl tBit; have := hcl tF
    show size (clr tX) + (size (clr tCU) + (size (clr tZB) + (size (clr tK) + (size (clr tU) +
      (size (clr tE) + (size (clr tT2) + (size (clr tTB) + (size (clr tBit) + size (clr tF))))))))) ≤ _
    omega
  have g1 : ∀ p q : Prog 16, size (p ⨾ q) = size p + size q := fun _ _ => rfl
  have g2 : ∀ (c : Fin 16) (p : Prog 16), size (loop c p) = size p + 39 := fun _ _ => rfl
  have g3 : ∀ (c : Fin 16) (p q : Prog 16), size (ifBit c p q) = size p + size q + 1 :=
    fun _ _ _ => rfl
  simp only [authBPC, authBP, initA, lastA, outA', g1, g2, g3]
  omega

end AdvancedEncryption.RingBTVW.BpComp
