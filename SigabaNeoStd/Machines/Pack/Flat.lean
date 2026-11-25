import SigabaNeoStd.Machines.Pack.MapBound
import SigabaNeoStd.Machines.Pack.Det

/-!
# The clock of the packed machine for programs that are flat at the wide level

When every logical tape stays at most `T` long, a leaf group of width at most `w` costs its old
clock (`timeBoundT`) plus the overhead `ovT w K T` (reading and writing back its segments through
the packed store, `≤ K (2T + 1)` bits). So for a program whose wide nodes are only sequences, frames
and `prog` wrappers (every loop and branch is inside a narrow leaf), the packed clock `ptime` is the
old clock plus one overhead per leaf.

* `FX w T σ p Pre Post n` (`FP` for plain programs): from every bound `L` with `Pre L` (all tapes at
  most `T`), the bound after `p` satisfies `Post` (all tapes at most `T`), and
  `ptime w σ d p L M ≤ timeBoundT p (L ∘ σ) + n · ovT w K T` for every depth `d` and counters
  `M ≤ K (2T + 1)`.
* Rules: **`FX.leaf`** (a narrow framed program, `k ≤ w`), **`FP.narrow`** (a `Prog` leaf
  mentioning at most `w` tapes), `FX.seq`, `FP.seq`, `FX.frame`, `FX.prog`, `FX.mono`, `FP.mono`.
* **`time_packMachineT_le`**: the clock of the packed machine from `FX` at the input bound.
* **`descLen_packMachineT_le`**: the description length from a bound on `p.size`.
-/

namespace SigabaNeo.Tape.Pack

open Function

variable {K : ℕ}

/-! ### The overhead of a leaf group -/

/-- The overhead of one leaf group of width at most `w` when every logical tape is at most `T`
long (and the counters at most `K (2T + 1)`). -/
def ovT (w K T : ℕ) : ℕ :=
  w * (6 * (K * (2 * T + 1)) + 16) + w * putTime (K * (2 * T + 1)) T + 2 * (K * (2 * T + 1)) + 3

/-- Every tape at most `T`. -/
def Le (T : ℕ) (L : Fin K → ℕ) : Prop := ∀ t, L t ≤ T

theorem Lam_le_const {L : Fin K → ℕ} {T : ℕ} (h : Le T L) : Lam L ≤ K * (2 * T + 1) := by
  unfold Lam
  calc ∑ i, (2 * L i + 1) ≤ ∑ _i : Fin K, (2 * T + 1) :=
        Finset.sum_le_sum fun i _ => by have := h i; omega
    _ = K * (2 * T + 1) := by simp

theorem Lafter_apply_self {k : ℕ} (σ : Fin k ↪ Fin K) (p : XProg k) (L : Fin K → ℕ) (j : Fin k) :
    Lafter σ p L (σ j) = p.lenBoundT (fun j => L (σ j)) j :=
  embedF_apply_self _ _ _ _

theorem Lafter_comp {k : ℕ} (σ : Fin k ↪ Fin K) (p : XProg k) (L : Fin K → ℕ) :
    (fun j => Lafter σ p L (σ j)) = p.lenBoundT (fun j => L (σ j)) :=
  funext fun j => Lafter_apply_self σ p L j

theorem Lafter_seq {k : ℕ} (σ : Fin k ↪ Fin K) (p q : XProg k) (L : Fin K → ℕ) :
    Lafter σ (.seq p q) L = Lafter σ q (Lafter σ p L) := by
  simp only [Lafter, XProg.lenBoundT]
  rw [embedF_comp_self', embedF_embedF']

theorem Lafter_seqP {k : ℕ} (σ : Fin k ↪ Fin K) (p q : Prog k) (L : Fin K → ℕ) :
    Lafter σ (.prog (.seq p q)) L = Lafter σ (.prog q) (Lafter σ (.prog p) L) :=
  Lafter_seq σ (.prog p) (.prog q) L

theorem Lafter_frame {k m : ℕ} (σ : Fin k ↪ Fin K) (e : Fin m ↪ Fin k) (q : XProg m)
    (L : Fin K → ℕ) : Lafter σ (.frame e q) L = Lafter (e.trans σ) q L := by
  simp only [Lafter, XProg.lenBoundT]
  exact embedF_trans' e σ L _

theorem Lafter_localize {k : ℕ} (σ : Fin k ↪ Fin K) (q : Prog k) (h : NarrowP w q)
    (L : Fin K → ℕ) :
    Lafter ((Prog.listEmb _ (List.nodup_dedup _)).trans σ)
      (.prog (Prog.localize _ h.2 q)) L = Lafter σ (.prog q) L := by
  have hq := Prog.map_localize q.tapes.dedup (List.nodup_dedup _) h.2 q
    (fun t ht => List.mem_dedup.mpr ht)
  conv_rhs => rw [← hq]
  simp only [Lafter, XProg.lenBoundT]
  rw [Prog.lenBoundT_map]
  exact (embedF_trans' _ σ L _).symm

/-- **The overhead of a leaf group.** -/
theorem leafT_le {w T M m : ℕ} (hm : m ≤ w) (σ : Fin m ↪ Fin K) (p : XProg m) {L : Fin K → ℕ}
    (hL : Le T L) (hA : Le T (Lafter σ p L)) (hM : M ≤ K * (2 * T + 1)) :
    leafT σ p L M ≤ p.timeBoundT (fun j => L (σ j)) + ovT w K T := by
  have h1 : Lam L ≤ K * (2 * T + 1) := Lam_le_const hL
  have h2 : Lam (L ⊔ Lafter σ p L) ≤ K * (2 * T + 1) :=
    Lam_le_const (fun t => by simp only [Pi.sup_apply]; exact sup_le (hL t) (hA t))
  have h3 : Lam (Lafter σ p L) ≤ K * (2 * T + 1) := Lam_le_const hA
  have h4 : supB (p.lenBoundT fun j => L (σ j)) ≤ T :=
    Finset.sup_le fun j _ => by rw [← Lafter_apply_self]; exact hA _
  have h5 := putTime_mono h2 h4
  have h6 : m * (6 * Lam L + 16) ≤ w * (6 * (K * (2 * T + 1)) + 16) :=
    Nat.mul_le_mul hm (by omega)
  have h7 : m * putTime (Lam (L ⊔ Lafter σ p L)) (supB (p.lenBoundT fun j => L (σ j))) ≤
      w * putTime (K * (2 * T + 1)) T := Nat.mul_le_mul hm h5
  have h8 : max (Lam (Lafter σ p L)) M ≤ K * (2 * T + 1) := max_le h3 hM
  unfold leafT ovT
  omega

/-! ### Unfolding the packed clock -/

theorem ptime_of_le {w k : ℕ} (hk : k ≤ w) (σ : Fin k ↪ Fin K) (d : ℕ) (p : XProg k)
    (L : Fin K → ℕ) (M : ℕ) : ptime w σ d p L M = leafT σ p L M := by
  cases p <;> simp only [ptime, orLeafT, if_pos hk]

theorem ptimeP_of_narrow {w k : ℕ} (σ : Fin k ↪ Fin K) (d : ℕ) (q : Prog k) (h : NarrowP w q)
    (L : Fin K → ℕ) (M : ℕ) : ptimeP w σ d q L M =
      leafT ((Prog.listEmb _ (List.nodup_dedup _)).trans σ) (.prog (Prog.localize _ h.2 q)) L M := by
  cases q <;> simp only [ptimeP, orNarrowT, dif_pos h]

/-- A narrow `Prog` leaf: its old clock plus one overhead. -/
theorem ptimeP_narrow_le {w T k : ℕ} (σ : Fin k ↪ Fin K) (d : ℕ) (q : Prog k) (h : NarrowP w q)
    {L : Fin K → ℕ} {M : ℕ} (hL : Le T L) (hA : Le T (Lafter σ (.prog q) L))
    (hM : M ≤ K * (2 * T + 1)) :
    ptimeP w σ d q L M ≤ q.timeBoundT (fun j => L (σ j)) + ovT w K T := by
  rw [ptimeP_of_narrow σ d q h]
  have hA' := hA
  rw [← Lafter_localize σ q h L] at hA'
  refine (leafT_le h.1 _ _ hL hA' hM).trans (Nat.add_le_add_right ?_ _)
  have hq := Prog.map_localize q.tapes.dedup (List.nodup_dedup _) h.2 q
    (fun t ht => List.mem_dedup.mpr ht)
  have := Prog.timeBoundT_le_map (Prog.listEmb _ (List.nodup_dedup _)) (Prog.localize _ h.2 q)
    (fun j => L (σ j))
  rw [hq] at this
  exact this

/-! ### The judgments -/

variable (w T : ℕ)

/-- **A flat framed program placed by `σ`**: from `Pre`, it ends in `Post` (all tapes at most
`T` before and after), and its packed clock is its old clock plus `n` overheads. -/
def FX {k : ℕ} (σ : Fin k ↪ Fin K) (p : XProg k) (Pre Post : (Fin K → ℕ) → Prop) (n : ℕ) :
    Prop :=
  1 ≤ n ∧ ∀ L, Pre L → Le T L ∧ Le T (Lafter σ p L) ∧ Post (Lafter σ p L) ∧
    ∀ d M, M ≤ K * (2 * T + 1) →
      ptime w σ d p L M ≤ p.timeBoundT (fun j => L (σ j)) + n * ovT w K T

/-- **A flat plain program placed by `σ`.** -/
def FP {k : ℕ} (σ : Fin k ↪ Fin K) (q : Prog k) (Pre Post : (Fin K → ℕ) → Prop) (n : ℕ) :
    Prop :=
  1 ≤ n ∧ ∀ L, Pre L → Le T L ∧ Le T (Lafter σ (.prog q) L) ∧ Post (Lafter σ (.prog q) L) ∧
    ∀ d M, M ≤ K * (2 * T + 1) →
      ptimeP w σ d q L M ≤ q.timeBoundT (fun j => L (σ j)) + n * ovT w K T

variable {w T}

theorem FX.mono {k : ℕ} {σ : Fin k ↪ Fin K} {p : XProg k} {Pre Pre' Post Post' : (Fin K → ℕ) → Prop}
    {n n' : ℕ} (h : FX w T σ p Pre Post n) (hpre : ∀ L, Pre' L → Pre L)
    (hpost : ∀ L, Post L → Post' L) (hn : n ≤ n') : FX w T σ p Pre' Post' n' := by
  refine ⟨h.1.trans hn, fun L hL => ?_⟩
  obtain ⟨a, b, c, e⟩ := h.2 L (hpre L hL)
  exact ⟨a, b, hpost _ c, fun d M hM =>
    (e d M hM).trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hn) _)⟩

theorem FP.mono {k : ℕ} {σ : Fin k ↪ Fin K} {q : Prog k} {Pre Pre' Post Post' : (Fin K → ℕ) → Prop}
    {n n' : ℕ} (h : FP w T σ q Pre Post n) (hpre : ∀ L, Pre' L → Pre L)
    (hpost : ∀ L, Post L → Post' L) (hn : n ≤ n') : FP w T σ q Pre' Post' n' := by
  refine ⟨h.1.trans hn, fun L hL => ?_⟩
  obtain ⟨a, b, c, e⟩ := h.2 L (hpre L hL)
  exact ⟨a, b, hpost _ c, fun d M hM =>
    (e d M hM).trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hn) _)⟩

/-- **A narrow framed program** (`k ≤ w`) is one leaf group. -/
theorem FX.leaf {k : ℕ} (hk : k ≤ w) (σ : Fin k ↪ Fin K) (p : XProg k)
    {Pre Post : (Fin K → ℕ) → Prop}
    (h : ∀ L, Pre L → Le T L ∧ Le T (Lafter σ p L) ∧ Post (Lafter σ p L)) :
    FX w T σ p Pre Post 1 := by
  refine ⟨le_rfl, fun L hL => ⟨(h L hL).1, (h L hL).2.1, (h L hL).2.2, fun d M hM => ?_⟩⟩
  rw [ptime_of_le hk, Nat.one_mul]
  exact leafT_le hk σ p (h L hL).1 (h L hL).2.1 hM

/-- **A narrow `Prog` leaf** (mentioning at most `w` tapes) is one leaf group. -/
theorem FP.narrow {k : ℕ} (σ : Fin k ↪ Fin K) (q : Prog k) (hq : NarrowP w q)
    {Pre Post : (Fin K → ℕ) → Prop}
    (h : ∀ L, Pre L → Le T L ∧ Le T (Lafter σ (.prog q) L) ∧ Post (Lafter σ (.prog q) L)) :
    FP w T σ q Pre Post 1 := by
  refine ⟨le_rfl, fun L hL => ⟨(h L hL).1, (h L hL).2.1, (h L hL).2.2, fun d M hM => ?_⟩⟩
  rw [Nat.one_mul]
  exact ptimeP_narrow_le σ d q hq (h L hL).1 (h L hL).2.1 hM

theorem FP.seq {k : ℕ} {σ : Fin k ↪ Fin K} {p q : Prog k} {Pre Mid Post : (Fin K → ℕ) → Prop}
    {a b : ℕ} (hp : FP w T σ p Pre Mid a) (hq : FP w T σ q Mid Post b) :
    FP w T σ (.seq p q) Pre Post (a + b) := by
  refine ⟨by have := hp.1; omega, fun L hL => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := hp.2 L hL
  obtain ⟨b1, b2, b3, b4⟩ := hq.2 _ a3
  rw [Lafter_seqP]
  refine ⟨a1, b2, b3, fun d M hM => ?_⟩
  have htb : (Prog.seq p q).timeBoundT (fun j => L (σ j)) = p.timeBoundT (fun j => L (σ j)) +
      q.timeBoundT (fun j => Lafter σ (.prog p) L (σ j)) := by
    rw [Lafter_comp]; rfl
  by_cases hn : NarrowP w (Prog.seq p q)
  · refine (ptimeP_narrow_le σ d _ hn a1 (by rw [Lafter_seqP]; exact b2) hM).trans ?_
    have := hp.1
    have : ovT w K T ≤ (a + b) * ovT w K T := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · have e : ptimeP w σ d (.seq p q) L M =
        ptimeP w σ d p L M + ptimeP w σ d q (Lafter σ (.prog p) L) M := by
      simp only [ptimeP, orNarrowT, dif_neg hn]
    rw [e, htb, Nat.add_mul]
    have := a4 d M hM
    have := b4 d M hM
    omega

theorem FX.prog {k : ℕ} {σ : Fin k ↪ Fin K} {q : Prog k} {Pre Post : (Fin K → ℕ) → Prop} {n : ℕ}
    (h : FP w T σ q Pre Post n) : FX w T σ (.prog q) Pre Post n := by
  refine ⟨h.1, fun L hL => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := h.2 L hL
  refine ⟨a1, a2, a3, fun d M hM => ?_⟩
  by_cases hk : k ≤ w
  · rw [ptime_of_le hk]
    refine (leafT_le hk σ _ a1 a2 hM).trans ?_
    have := h.1
    have : ovT w K T ≤ n * ovT w K T := Nat.le_mul_of_pos_left _ (by omega)
    exact Nat.add_le_add_left this _
  · have e : ptime w σ d (.prog q) L M = ptimeP w σ d q L M := by
      simp only [ptime, orLeafT, if_neg hk]
    rw [e]
    exact a4 d M hM

theorem FX.frame {k m : ℕ} {σ : Fin k ↪ Fin K} {e : Fin m ↪ Fin k} {q : XProg m}
    {Pre Post : (Fin K → ℕ) → Prop} {n : ℕ} (h : FX w T (e.trans σ) q Pre Post n) :
    FX w T σ (.frame e q) Pre Post n := by
  refine ⟨h.1, fun L hL => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := h.2 L hL
  rw [Lafter_frame]
  refine ⟨a1, a2, a3, fun d M hM => ?_⟩
  by_cases hk : k ≤ w
  · rw [ptime_of_le hk]
    refine (leafT_le hk σ _ a1 (by rw [Lafter_frame]; exact a2) hM).trans ?_
    have := h.1
    have : ovT w K T ≤ n * ovT w K T := Nat.le_mul_of_pos_left _ (by omega)
    exact Nat.add_le_add_left this _
  · have e' : ptime w σ d (.frame e q) L M = ptime w (e.trans σ) d q L M := by
      simp only [ptime, orLeafT, if_neg hk]
    rw [e']
    exact a4 d M hM

theorem FX.seq {k : ℕ} {σ : Fin k ↪ Fin K} {p q : XProg k} {Pre Mid Post : (Fin K → ℕ) → Prop}
    {a b : ℕ} (hp : FX w T σ p Pre Mid a) (hq : FX w T σ q Mid Post b) :
    FX w T σ (.seq p q) Pre Post (a + b) := by
  refine ⟨by have := hp.1; omega, fun L hL => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := hp.2 L hL
  obtain ⟨b1, b2, b3, b4⟩ := hq.2 _ a3
  rw [Lafter_seq]
  refine ⟨a1, b2, b3, fun d M hM => ?_⟩
  have htb : (XProg.seq p q).timeBoundT (fun j => L (σ j)) = p.timeBoundT (fun j => L (σ j)) +
      q.timeBoundT (fun j => Lafter σ p L (σ j)) := by
    rw [Lafter_comp]; rfl
  by_cases hk : k ≤ w
  · rw [ptime_of_le hk]
    refine (leafT_le hk σ _ a1 (by rw [Lafter_seq]; exact b2) hM).trans ?_
    have := hp.1
    have : ovT w K T ≤ (a + b) * ovT w K T := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · have e : ptime w σ d (.seq p q) L M = ptime w σ d p L M + ptime w σ d q (Lafter σ p L) M := by
      simp only [ptime, orLeafT, if_neg hk]
    rw [e, htb, Nat.add_mul]
    have := a4 d M hM
    have := b4 d M hM
    omega

/-! ### The machine -/

theorem lenBoundT_snocN_le {k : ℕ} (o : Fin k) (b : Bool) (ℓ : Fin k → ℕ) :
    ∀ m (t : Fin k), (Prog.snocN o b m).lenBoundT ℓ t ≤ ℓ t + m
  | 0, t => by
    simp only [Prog.snocN, Prog.nop, Prog.lenBoundT, Prim.lenT, Function.update_apply]
    split_ifs with h <;> [subst h; skip] <;> omega
  | m + 1, t => by
    simp only [Prog.snocN, Prog.lenBoundT, Prim.lenT, Function.update_apply]
    split_ifs with h
    · have := lenBoundT_snocN_le o b ℓ m t; subst h; omega
    · have := lenBoundT_snocN_le o b ℓ m t; omega

theorem timeBoundT_snocN_le {k : ℕ} (o : Fin k) (b : Bool) (ℓ : Fin k → ℕ) :
    ∀ m, (Prog.snocN o b m).timeBoundT ℓ ≤ (m + 1) * (2 * (supB ℓ + m) + 5)
  | 0 => by
    simp only [Prog.snocN, Prog.nop, Prog.timeBoundT, Prim.pad]
    omega
  | m + 1 => by
    have ih := timeBoundT_snocN_le o b ℓ m
    have hs : supB ((Prog.snocN o b m).lenBoundT ℓ) ≤ supB ℓ + m :=
      Finset.sup_le fun t _ => (lenBoundT_snocN_le o b ℓ m t).trans
        (Nat.add_le_add_right (le_supB ℓ t) m)
    simp only [Prog.snocN, Prog.timeBoundT, Prim.pad]
    have : (m + 1) * (2 * (supB ℓ + m) + 5) ≤ (m + 1) * (2 * (supB ℓ + (m + 1)) + 5) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith

variable {D : ℕ}

/-- **The clock of the packed machine**, from a flat judgment at the input bound. -/
theorem time_packMachineT_le (p : XProg K) (i₀ o : Fin K) (n : ℕ)
    {Post : (Fin K → ℕ) → Prop} {N : ℕ}
    (h : FX w T (Embedding.refl _) p (fun L => L = Prog.inputBound i₀ n) Post N) :
    (packMachineT w D p i₀ o n).time ≤
      (2 * n + 2) + (K + 1) * (2 * (n + K) + 5) + putTime K n +
        (p.timeBoundT (Prog.inputBound i₀ n) + N * ovT w K T) + (6 * (K * (2 * T + 1)) + 16) +
          (2 * XProg.lenBoundT p (Prog.inputBound i₀ n) o + 2) := by
  rw [time_packMachineT]
  obtain ⟨-, h2, -, h4⟩ := h.2 _ rfl
  have hp := h4 0 0 (Nat.zero_le _)
  have hl := Lam_le_const h2
  have hs : Prog.timeBoundT (Prog.snocN (packLayout w D).st false K)
      (fun y => if y = ioT w D then n else 0) ≤ (K + 1) * (2 * (n + K) + 5) := by
    refine (timeBoundT_snocN_le _ _ _ K).trans (Nat.mul_le_mul_left _ ?_)
    have : supB (fun y : Fin (5 + w + D) => if y = ioT w D then n else 0) ≤ n :=
      Finset.sup_le fun y _ => by split_ifs <;> omega
    omega
  have hpt : ptime w (Embedding.refl _) 0 p (Prog.inputBound i₀ n) 0 ≤
      p.timeBoundT (Prog.inputBound i₀ n) + N * ovT w K T := hp
  unfold topTime
  omega

/-- **The description length of the packed machine**, from a bound `S` on `p.size` and a bound
`B < 2^m` on the states. -/
theorem descLen_packMachineT_le (p : XProg K) (i₀ o : Fin K) (n : ℕ) {S B m : ℕ}
    (hS : p.size ≤ S) (hB : stA w K * S + 96 * K + 254 ≤ B) (hm : B < 2 ^ m) :
    (packMachineT w D p i₀ o n).descLen ≤ 6 * B * 3 ^ (5 + w + D) * (4 + 4 * (5 + w + D) + m) := by
  have hst : (packMachineT w D p i₀ o n).states ≤ B :=
    (states_packMachineT_le (w := w) (D := D) p i₀ o n).trans
      ((Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left _ hS) _) _).trans hB)
  have hsz : Nat.size (packMachineT w D p i₀ o n).states ≤ m :=
    Nat.size_le.mpr (lt_of_le_of_lt hst hm)
  unfold Machine.descLen Machine.entryBits
  rw [tapes_packMachineT]
  simp only [pow_zero, mul_one, Nat.mul_zero, Nat.add_zero, Nat.size_zero]
  gcongr

end SigabaNeo.Tape.Pack
