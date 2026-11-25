import SigabaNeo.Lib.Machines.Pack.Flat

/-!
# Absolute clocks of packed programs, with wide loops and branches

`FXa w T σ p Pre Post t`: from every bound `L` with `Pre L` (all tapes at most `T`) the bound after
`p` satisfies `Post` (all tapes at most `T`), and `ptime w σ d p L M ≤ t` for every depth `d` and
counters `M ≤ K (2T + 1)`. Unlike `FX` it does not mention the old clock, so it also covers wide
loops, whose packed clock is charged at the loop invariant (`iterSupT`, which is the bound after
the loop, `iterSupT_gX`).

* `FXa.of_FX` (from a flat judgment and a bound on the old clock), `FXa.seq`, `FXa.mono`;
* **`FXa.loop`**: a wide loop on a counter of at most `c` bits, its body within `Rb` from the bound
  after the loop: `6Λ + 16 + c · (loopOv Λ T + Rb) + 2`, `Λ = K (2T + 1)`;
* `FXa.ifBlank`, `FXa.ifBit`: a wide branch, `6Λ + 16 + (2Λ + 3 + max + 1)`;
* **`time_packMachineT_le'`**: the clock of the packed machine from `FXa`.
-/

namespace SigabaNeo.Tape.Pack

open Function

variable {K : ℕ}

/-! ### The invariant of a wide loop is the bound after it -/

theorem embedF_update_range' {k : ℕ} (σ : Fin k ↪ Fin K) (E : Fin K → ℕ) (i : Fin k) (v : ℕ)
    (Y : Fin k → ℕ) : embedF σ (Function.update E (σ i) v) Y = embedF σ E Y := by
  funext l
  rcases embedF_cases σ (Function.update E (σ i) v) Y l with ⟨hl, h⟩ | ⟨j, rfl, h⟩
  · rw [h]
    have hne : l ≠ σ i := fun he => by subst he; rw [partialInv_self] at hl; simp at hl
    rw [Function.update_of_ne hne]
    simp only [embedF, hl, Option.elim]
  · simp

theorem gX_iterate {k : ℕ} (σ : Fin k ↪ Fin K) (i : Fin k) (b : XProg k) (L : Fin K → ℕ) :
    ∀ m : ℕ, (gX σ i b)^[m] L =
      embedF σ L ((fun ℓ' => b.lenBoundT (tailB i ℓ'))^[m] (fun j => L (σ j)))
  | 0 => (embedF_self σ L).symm
  | m + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', gX_iterate σ i b L m]
    set X := (fun ℓ' => b.lenBoundT (tailB i ℓ'))^[m] (fun j => L (σ j))
    simp only [gX, Lafter]
    rw [tailB_comp, embedF_comp_self', tailB, embedF_update_range', embedF_embedF']

/-- **The invariant bound of a wide loop is the bound after it.** -/
theorem iterSupT_gX {k : ℕ} (σ : Fin k ↪ Fin K) (i : Fin k) (b : XProg k) (L : Fin K → ℕ) :
    iterSupT (gX σ i b) (L (σ i)) L = Lafter σ (.loop i b) L := by
  funext t
  simp only [Lafter, XProg.lenBoundT]
  conv_lhs => simp only [iterSupT, gX_iterate]
  rcases embedF_cases σ L (iterSupT (fun ℓ' => b.lenBoundT (tailB i ℓ')) (L (σ i))
      (fun j => L (σ j))) t with ⟨hn, h⟩ | ⟨j, rfl, h⟩
  · rw [h]
    have : ∀ X : Fin k → ℕ, embedF σ L X t = L t := fun X => by simp only [embedF, hn, Option.elim]
    simp only [this]
    exact Finset.sup_const ⟨0, by simp⟩ _
  · rw [h]
    simp only [embedF_apply_self, iterSupT]

/-! ### Absolute clocks -/

variable (w T : ℕ)

/-- **An absolute clock of a placed framed program.** -/
def FXa {k : ℕ} (σ : Fin k ↪ Fin K) (p : XProg k) (Pre Post : (Fin K → ℕ) → Prop) (t : ℕ) :
    Prop :=
  ∀ L, Pre L → Le T L ∧ Le T (Lafter σ p L) ∧ Post (Lafter σ p L) ∧
    ∀ d M, M ≤ K * (2 * T + 1) → ptime w σ d p L M ≤ t

/-- The overhead of one round of a wide loop, besides its body. -/
def loopOv (Λ T : ℕ) : ℕ := (2 * Λ + 3) + ((6 * Λ + 16) + ((2 * Λ + 3) + putTime Λ T)) + 1

variable {w T}

theorem FXa.mono {k : ℕ} {σ : Fin k ↪ Fin K} {p : XProg k} {Pre Pre' Post Post' : (Fin K → ℕ) → Prop}
    {t t' : ℕ} (h : FXa w T σ p Pre Post t) (hpre : ∀ L, Pre' L → Pre L)
    (hpost : ∀ L, Post L → Post' L) (ht : t ≤ t') : FXa w T σ p Pre' Post' t' := fun L hL =>
  have h' := h L (hpre L hL)
  ⟨h'.1, h'.2.1, hpost _ h'.2.2.1, fun d M hM => (h'.2.2.2 d M hM).trans ht⟩

theorem FXa.of_FX {k : ℕ} {σ : Fin k ↪ Fin K} {p : XProg k} {Pre Post : (Fin K → ℕ) → Prop}
    {n t₀ : ℕ} (h : FX w T σ p Pre Post n)
    (ht : ∀ L, Pre L → p.timeBoundT (fun j => L (σ j)) ≤ t₀) :
    FXa w T σ p Pre Post (t₀ + n * ovT w K T) := fun L hL =>
  have h' := h.2 L hL
  ⟨h'.1, h'.2.1, h'.2.2.1, fun d M hM => (h'.2.2.2 d M hM).trans
    (Nat.add_le_add_right (ht L hL) _)⟩

theorem FXa.seq {k : ℕ} (hk : ¬ k ≤ w) {σ : Fin k ↪ Fin K} {p q : XProg k}
    {Pre Mid Post : (Fin K → ℕ) → Prop} {a b : ℕ} (hp : FXa w T σ p Pre Mid a)
    (hq : FXa w T σ q Mid Post b) : FXa w T σ (.seq p q) Pre Post (a + b) := fun L hL => by
  obtain ⟨a1, a2, a3, a4⟩ := hp L hL
  obtain ⟨b1, b2, b3, b4⟩ := hq _ a3
  rw [Lafter_seq]
  refine ⟨a1, b2, b3, fun d M hM => ?_⟩
  have e : ptime w σ d (.seq p q) L M = ptime w σ d p L M + ptime w σ d q (Lafter σ p L) M := by
    simp only [ptime, orLeafT, if_neg hk]
  rw [e]
  exact Nat.add_le_add (a4 d M hM) (b4 d M hM)

theorem FXa.prog {k : ℕ} (hk : ¬ k ≤ w) {σ : Fin k ↪ Fin K} {q : Prog k}
    {Pre Post : (Fin K → ℕ) → Prop} {t : ℕ}
    (h : ∀ L, Pre L → Le T L ∧ Le T (Lafter σ (.prog q) L) ∧ Post (Lafter σ (.prog q) L) ∧
      ∀ d M, M ≤ K * (2 * T + 1) → ptimeP w σ d q L M ≤ t) :
    FXa w T σ (.prog q) Pre Post t := fun L hL => by
  obtain ⟨a1, a2, a3, a4⟩ := h L hL
  refine ⟨a1, a2, a3, fun d M hM => ?_⟩
  have e : ptime w σ d (.prog q) L M = ptimeP w σ d q L M := by
    simp only [ptime, orLeafT, if_neg hk]
  rw [e]
  exact a4 d M hM

theorem T_le_Lam {T : ℕ} (hK : 0 < K) : T ≤ K * (2 * T + 1) := by nlinarith

/-- **A wide loop**: `c` rounds at most, each the loop overhead and the body from the bound after
the loop. -/
theorem FXa.loop {k : ℕ} (hk : ¬ k ≤ w) {σ : Fin k ↪ Fin K} {i : Fin k} {b : XProg k}
    {Pre Post Q Q' : (Fin K → ℕ) → Prop} {c Rb : ℕ}
    (hc : ∀ L, Pre L → L (σ i) ≤ c)
    (hpre : ∀ L, Pre L → Le T L ∧ Le T (Lafter σ (.loop i b) L) ∧
      Post (Lafter σ (.loop i b) L) ∧ Q (Lafter σ (.loop i b) L))
    (hb : FXa w T σ b Q Q' Rb) :
    FXa w T σ (.loop i b) Pre Post
      ((6 * (K * (2 * T + 1)) + 16) + (c * (loopOv (K * (2 * T + 1)) T + Rb) + 2)) := by
  intro L hL
  obtain ⟨a1, a2, a3, a4⟩ := hpre L hL
  refine ⟨a1, a2, a3, fun d M hM => ?_⟩
  have hK : 0 < K := Fin.pos (σ i)
  set Λ := K * (2 * T + 1)
  have e : ptime w σ d (.loop i b) L M = loopT (σ i) L (iterSupT (gX σ i b) (L (σ i)) L)
      (max M (L (σ i))) (ptime w σ (d + 1) b (iterSupT (gX σ i b) (L (σ i)) L)
        (max M (L (σ i)))) := by
    simp only [ptime, orLeafT, if_neg hk]
  rw [e, iterSupT_gX]
  have hM' : max M (L (σ i)) ≤ Λ := max_le hM ((a1 _).trans (T_le_Lam hK))
  have hRb := (hb _ a4).2.2.2 (d + 1) _ hM'
  have h1 : Lam L ≤ Λ := Lam_le_const a1
  have h2 : Lam (Lafter σ (.loop i b) L) ≤ Λ := Lam_le_const a2
  have h3 : Lafter σ (.loop i b) L (σ i) ≤ T := a2 _
  have hTL := T_le_Lam (T := T) hK
  have h4 : tailZT (σ i) (Lafter σ (.loop i b) L) (max M (L (σ i))) ≤
      (6 * Λ + 16) + ((2 * Λ + 3) + putTime Λ T) := by
    unfold tailZT
    have := putTime_mono h2 h3
    have : max (max (Lam (Lafter σ (.loop i b) L)) (max M (L (σ i))))
        (Lafter σ (.loop i b) L (σ i)) ≤ Λ := max_le (max_le h2 hM') (h3.trans hTL)
    omega
  have h5 : (2 * max (Lam (Lafter σ (.loop i b) L)) (max M (L (σ i))) + 3) +
      (tailZT (σ i) (Lafter σ (.loop i b) L) (max M (L (σ i))) +
        ptime w σ (d + 1) b (Lafter σ (.loop i b) L) (max M (L (σ i)))) + 1 ≤
      loopOv Λ T + Rb := by
    unfold loopOv
    have : max (Lam (Lafter σ (.loop i b) L)) (max M (L (σ i))) ≤ Λ := max_le h2 hM'
    omega
  unfold loopT
  have := Nat.mul_le_mul (hc L hL) h5
  omega

/-- **A wide branch on a blank test.** -/
theorem FXa.ifBlank {k : ℕ} (hk : ¬ k ≤ w) {σ : Fin k ↪ Fin K} {i : Fin k} {p q : XProg k}
    {Pre Post : (Fin K → ℕ) → Prop} {a b : ℕ}
    (hpre : ∀ L, Pre L → Le T (Lafter σ (.ifBlank i p q) L) ∧ Post (Lafter σ (.ifBlank i p q) L))
    (hp : FXa w T σ p Pre (fun _ => True) a) (hq : FXa w T σ q Pre (fun _ => True) b) :
    FXa w T σ (.ifBlank i p q) Pre Post
      ((6 * (K * (2 * T + 1)) + 16) + ((2 * (K * (2 * T + 1)) + 3 + max a b) + 1)) := by
  intro L hL
  obtain ⟨a1, -, -, a4⟩ := hp L hL
  obtain ⟨-, -, -, b4⟩ := hq L hL
  refine ⟨a1, (hpre L hL).1, (hpre L hL).2, fun d M hM => ?_⟩
  have hK : 0 < K := Fin.pos (σ i)
  have e : ptime w σ d (.ifBlank i p q) L M =
      testT (σ i) L M (max (ptime w σ d p L M) (ptime w σ d q L M)) := by
    simp only [ptime, orLeafT, if_neg hk]
  rw [e]
  unfold testT
  have h1 := Lam_le_const a1
  have : max (max (Lam L) M) (L (σ i)) ≤ K * (2 * T + 1) :=
    max_le (max_le h1 hM) ((a1 _).trans (T_le_Lam hK))
  have := max_le_max (a4 d M hM) (b4 d M hM)
  omega

/-- **A wide branch on a bit test.** -/
theorem FXa.ifBit {k : ℕ} (hk : ¬ k ≤ w) {σ : Fin k ↪ Fin K} {i : Fin k} {p q : XProg k}
    {Pre Post : (Fin K → ℕ) → Prop} {a b : ℕ}
    (hpre : ∀ L, Pre L → Le T (Lafter σ (.ifBit i p q) L) ∧ Post (Lafter σ (.ifBit i p q) L))
    (hp : FXa w T σ p Pre (fun _ => True) a) (hq : FXa w T σ q Pre (fun _ => True) b) :
    FXa w T σ (.ifBit i p q) Pre Post
      ((6 * (K * (2 * T + 1)) + 16) + ((2 * (K * (2 * T + 1)) + 3 + max a b) + 1)) := by
  intro L hL
  obtain ⟨a1, -, -, a4⟩ := hp L hL
  obtain ⟨-, -, -, b4⟩ := hq L hL
  refine ⟨a1, (hpre L hL).1, (hpre L hL).2, fun d M hM => ?_⟩
  have hK : 0 < K := Fin.pos (σ i)
  have e : ptime w σ d (.ifBit i p q) L M =
      testT (σ i) L M (max (ptime w σ d p L M) (ptime w σ d q L M)) := by
    simp only [ptime, orLeafT, if_neg hk]
  rw [e]
  unfold testT
  have h1 := Lam_le_const a1
  have : max (max (Lam L) M) (L (σ i)) ≤ K * (2 * T + 1) :=
    max_le (max_le h1 hM) ((a1 _).trans (T_le_Lam hK))
  have := max_le_max (a4 d M hM) (b4 d M hM)
  omega

variable {D : ℕ}

/-- **The clock of the packed machine**, from an absolute clock at the input bound. -/
theorem time_packMachineT_le' (p : XProg K) (i₀ o : Fin K) (n : ℕ)
    {Post : (Fin K → ℕ) → Prop} {t : ℕ}
    (h : FXa w T (Embedding.refl _) p (fun L => L = Prog.inputBound i₀ n) Post t) :
    (packMachineT w D p i₀ o n).time ≤
      (2 * n + 2) + (K + 1) * (2 * (n + K) + 5) + putTime K n + t +
        (6 * (K * (2 * T + 1)) + 16) + (2 * XProg.lenBoundT p (Prog.inputBound i₀ n) o + 2) := by
  rw [time_packMachineT]
  obtain ⟨-, h2, -, h4⟩ := h _ rfl
  have hp := h4 0 0 (Nat.zero_le _)
  have hl := Lam_le_const h2
  have hs : Prog.timeBoundT (Prog.snocN (packLayout w D).st false K)
      (fun y => if y = ioT w D then n else 0) ≤ (K + 1) * (2 * (n + K) + 5) := by
    refine (timeBoundT_snocN_le _ _ _ K).trans (Nat.mul_le_mul_left _ ?_)
    have : supB (fun y : Fin (5 + w + D) => if y = ioT w D then n else 0) ≤ n :=
      Finset.sup_le fun y _ => by split_ifs <;> omega
    omega
  unfold topTime
  omega

end SigabaNeo.Tape.Pack
