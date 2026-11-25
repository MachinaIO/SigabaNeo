import SigabaNeo.Lib.Machines.Pack.FlatLoop
import SigabaNeo.Lib.Machines.Prog.Lookup

/-!
# Leaves of the packing translation: narrowness, loop depth, length closure

Tools to apply the clock judgments (`FX`, `FP`, `FXa`) and the depth condition (`OkX`) to concrete
programs without evaluating them:

* `narrowP_of_subset`: a program whose tapes lie in a list of at most `w` tapes is narrow;
  `tapes_map`, `narrowP_map` (a relabelled `Prog n`, `n ≤ w`), `tapes_putW`;
* `loopDepth_map`, `loopDepth_putW`;
* `BndP T q`: `q` keeps every tape at most `T` (`bndP_noGrow`, `bndP_putW`, `bndP_seq`,
  `bndP_map`), and **`FP.leafB`**: a narrow leaf keeping the tapes at most `T` is one leaf group
  from `Le T` to `Le T`; `FP.eraseLike`-style sequences by `FP.seq`.
-/

namespace SigabaNeo.Tape.Pack

open Function

variable {K : ℕ}

/-! ### Narrowness -/

theorem narrowP_of_subset {w k : ℕ} {q : Prog k} (l : List (Fin k)) (hl : l.length ≤ w)
    (hs : ∀ t ∈ q.tapes, t ∈ l) (hne : q.tapes ≠ []) : NarrowP w q := by
  refine ⟨?_, ?_⟩
  · have hsub : q.tapes.dedup ⊆ l := fun t ht => hs t (List.mem_dedup.mp ht)
    exact ((List.nodup_dedup _).subperm hsub).length_le.trans hl
  · obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ hne
    exact List.length_pos_of_mem (List.mem_dedup.mpr ht)

theorem Prog.tapes_map {n k : ℕ} (u : Fin n → Fin k) :
    ∀ p : Prog n, (Prog.map u p).tapes = p.tapes.map u
  | .prim a => Prim.tapes_map u a
  | .coin _ => rfl
  | .seq p q => by simp only [Prog.map, Prog.tapes, List.map_append, Prog.tapes_map u p,
      Prog.tapes_map u q]
  | .ifBlank _ p q => by simp only [Prog.map, Prog.tapes, List.map_cons, List.map_append,
      Prog.tapes_map u p, Prog.tapes_map u q]
  | .ifBit _ p q => by simp only [Prog.map, Prog.tapes, List.map_cons, List.map_append,
      Prog.tapes_map u p, Prog.tapes_map u q]
  | .loop _ b => by simp only [Prog.map, Prog.tapes, List.map_cons, Prog.tapes_map u b]

theorem Prog.tapes_ne_nil {k : ℕ} : ∀ p : Prog k, p.tapes ≠ []
  | .prim a => by cases a <;> simp [Prog.tapes, Prim.tapes]
  | .coin _ => by simp [Prog.tapes]
  | .seq p _ => by simp [Prog.tapes, Prog.tapes_ne_nil p]
  | .ifBlank _ _ _ => by simp [Prog.tapes]
  | .ifBit _ _ _ => by simp [Prog.tapes]
  | .loop _ _ => by simp [Prog.tapes]

/-- **A relabelled program on at most `w` tapes is narrow.** -/
theorem narrowP_map {w n k : ℕ} (hn : n ≤ w) (u : Fin n → Fin k) (p : Prog n) :
    NarrowP w (Prog.map u p) :=
  narrowP_of_subset ((List.finRange n).map u) (by simpa using hn)
    (fun t ht => by
      rw [Prog.tapes_map] at ht
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp ht
      exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    (by rw [Prog.tapes_map]; simpa using Prog.tapes_ne_nil p)

theorem tapes_putW {k : ℕ} (o : Fin k) : ∀ (w : List Bool), ∀ t ∈ (Prog.putW o w).tapes, t = o
  | [] => by simp [Prog.putW, Prog.tapes, Prim.tapes]
  | b :: w => by
    intro t ht
    simp only [Prog.putW, Prog.tapes, List.mem_append, Prim.tapes, List.mem_singleton] at ht
    rcases ht with ht | ht
    · exact tapes_putW o w t ht
    · exact ht

/-! ### Loop depth -/

theorem loopDepth_map {n k : ℕ} (u : Fin n → Fin k) :
    ∀ p : Prog n, Prog.loopDepth (Tape.Prog.map u p) = Prog.loopDepth p
  | .prim _ | .coin _ => rfl
  | .seq p q | .ifBlank _ p q | .ifBit _ p q => by
    simp only [Tape.Prog.map, Prog.loopDepth, loopDepth_map u p, loopDepth_map u q]
  | .loop _ b => by simp only [Tape.Prog.map, Prog.loopDepth, loopDepth_map u b]

theorem loopDepth_putW {k : ℕ} (o : Fin k) : ∀ w : List Bool, Prog.loopDepth (Tape.Prog.putW o w) = 0
  | [] => rfl
  | b :: w => by simp only [Tape.Prog.putW, Prog.loopDepth, loopDepth_putW o w]; rfl

/-! ### Keeping every tape below a bound -/

/-- `q` keeps every tape at most `T`. -/
def BndP {k : ℕ} (T : ℕ) (q : Prog k) : Prop :=
  ∀ ℓ : Fin k → ℕ, (∀ t, ℓ t ≤ T) → ∀ t, q.lenBoundT ℓ t ≤ T

theorem bndP_noGrow {k T : ℕ} {q : Prog k} (h : q.NoGrow) : BndP T q :=
  fun _ hℓ t => Sym.lenBoundT_le_const q h hℓ t

theorem bndP_putW {k T : ℕ} (o : Fin k) (w : List Bool) (hw : w.length ≤ T) :
    BndP T (Tape.Prog.putW o w) := by
  intro ℓ hℓ t
  rw [Prog.lenBoundT_putW, Function.update_apply]
  split_ifs
  · exact hw
  · exact hℓ t

theorem bndP_seq {k T : ℕ} {p q : Prog k} (hp : BndP T p) (hq : BndP T q) :
    BndP T (.seq p q) :=
  fun ℓ hℓ t => hq _ (hp ℓ hℓ) t

theorem bndP_map {n k T : ℕ} (e : Fin n ↪ Fin k) {p : Prog n} (h : BndP T p) :
    BndP T (Tape.Prog.map e p) := by
  intro ℓ hℓ t
  rw [Tape.Prog.lenBoundT_map]
  rcases embedF_cases e ℓ (p.lenBoundT fun j => ℓ (e j)) t with ⟨-, h'⟩ | ⟨j, rfl, h'⟩
  · rw [h']; exact hℓ t
  · rw [h']; exact h _ (fun j => hℓ (e j)) j

theorem le_Lafter_of_bndP {w k T : ℕ} {σ : Fin k ↪ Fin K} {q : Prog k} (h : BndP T q)
    {L : Fin K → ℕ} (hL : Le T L) : Le T (Lafter σ (.prog q) L) := by
  intro t
  simp only [Lafter, XProg.lenBoundT]
  rcases embedF_cases σ L (q.lenBoundT fun j => L (σ j)) t with ⟨-, h'⟩ | ⟨j, rfl, h'⟩
  · rw [h']; exact hL t
  · rw [h']; exact h _ (fun j => hL (σ j)) j

/-- **A narrow leaf keeping every tape at most `T`.** -/
theorem FP.leafB {w T k : ℕ} (σ : Fin k ↪ Fin K) {q : Prog k} (hq : NarrowP w q)
    (hb : BndP T q) : FP w T σ q (Le T) (Le T) 1 :=
  FP.narrow σ q hq fun L hL => ⟨hL, le_Lafter_of_bndP (w := w) hb hL,
    le_Lafter_of_bndP (w := w) hb hL⟩

theorem FP.post {w T k : ℕ} {σ : Fin k ↪ Fin K} {q : Prog k} {Pre Post Post' : (Fin K → ℕ) → Prop}
    {n : ℕ} (h : FP w T σ q Pre Post n) (h' : ∀ L, Pre L → Post' (Lafter σ (.prog q) L)) :
    FP w T σ q Pre Post' n :=
  ⟨h.1, fun L hL => ⟨(h.2 L hL).1, (h.2 L hL).2.1, h' L hL, (h.2 L hL).2.2.2⟩⟩

theorem FX.post {w T k : ℕ} {σ : Fin k ↪ Fin K} {p : XProg k} {Pre Post Post' : (Fin K → ℕ) → Prop}
    {n : ℕ} (h : FX w T σ p Pre Post n) (h' : ∀ L, Pre L → Post' (Lafter σ p L)) :
    FX w T σ p Pre Post' n :=
  ⟨h.1, fun L hL => ⟨(h.2 L hL).1, (h.2 L hL).2.1, h' L hL, (h.2 L hL).2.2.2⟩⟩

theorem Lafter_refl {k : ℕ} (p : XProg k) (L : Fin k → ℕ) :
    Lafter (Embedding.refl _) p L = p.lenBoundT L := by
  funext t
  exact embedF_apply_self (Embedding.refl _) L (p.lenBoundT fun j => L j) t

/-! ### Primitive leaves and narrow plain leaves at the framed level -/

theorem Prim.pad_le_one {k : ℕ} (a : Prim k) : a.pad ≤ 1 := by cases a <;> simp [Prim.pad]

theorem supB_comp_le_of_Le {k T : ℕ} (σ : Fin k ↪ Fin K) {L : Fin K → ℕ} (hL : Le T L) :
    supB (fun j => L (σ j)) ≤ T :=
  Finset.sup_le fun j _ => hL (σ j)

/-- **A narrow plain leaf at the framed level**, with a bound on its old clock. -/
theorem FXa.narrowProg {w T k : ℕ} (σ : Fin k ↪ Fin K) {q : Prog k} (hq : NarrowP w q)
    {Pre Post : (Fin K → ℕ) → Prop}
    (h : ∀ L, Pre L → Le T L ∧ Le T (Lafter σ (.prog q) L) ∧ Post (Lafter σ (.prog q) L))
    {t₀ : ℕ} (ht : ∀ L, Pre L → q.timeBoundT (fun j => L (σ j)) ≤ t₀) :
    FXa w T σ (.prog q) Pre Post (t₀ + ovT w K T) :=
  (FXa.of_FX (FX.prog (FP.narrow σ q hq h)) ht).mono (fun _ h => h) (fun _ h => h)
    (by rw [Nat.one_mul])

/-- **A primitive at the framed level.** -/
theorem FXa.prim {w T k : ℕ} (hw : 3 ≤ w) (σ : Fin k ↪ Fin K) (a : Prim k)
    {Pre Post : (Fin K → ℕ) → Prop}
    (h : ∀ L, Pre L → Le T L ∧ Le T (Lafter σ (.prog (.prim a)) L) ∧
      Post (Lafter σ (.prog (.prim a)) L)) :
    FXa w T σ (.prog (.prim a)) Pre Post (2 * (T + 1) + 3 + ovT w K T) :=
  FXa.narrowProg σ (narrowP_prim hw a) h fun L hL => by
    have h1 := supB_comp_le_of_Le σ (h L hL).1
    have h2 := Prim.pad_le_one a
    simp only [Prog.timeBoundT]
    omega

/-- Iterating a map raising every tape by at most `c`. -/
theorem iterate_le_add {k : ℕ} {g : (Fin k → ℕ) → (Fin k → ℕ)} {c : ℕ}
    (hg : ∀ ℓ t, g ℓ t ≤ ℓ t + c) (ℓ : Fin k → ℕ) : ∀ m t, (g^[m] ℓ) t ≤ ℓ t + c * m
  | 0, t => by simp
  | m + 1, t => by
    rw [Function.iterate_succ_apply']
    have := hg (g^[m] ℓ) t
    have := iterate_le_add hg ℓ m t
    rw [Nat.mul_succ]
    omega

theorem iterSupT_le_add {k : ℕ} {g : (Fin k → ℕ) → (Fin k → ℕ)} {c : ℕ}
    (hg : ∀ ℓ t, g ℓ t ≤ ℓ t + c) (n : ℕ) (ℓ : Fin k → ℕ) (t : Fin k) :
    iterSupT g n ℓ t ≤ ℓ t + c * n :=
  Finset.sup_le fun m hm => (iterate_le_add hg ℓ m t).trans (by
    have : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have := Nat.mul_le_mul_left c this
    omega)

/-! ### Tapes within a list -/

/-- Every tape of `q` is in `l`. -/
def SubT {k : ℕ} (l : List (Fin k)) (q : Prog k) : Prop := ∀ t ∈ q.tapes, t ∈ l

theorem subT_seq {k : ℕ} {l : List (Fin k)} {p q : Prog k} (hp : SubT l p) (hq : SubT l q) :
    SubT l (.seq p q) := fun t ht => by
  simp only [Prog.tapes, List.mem_append] at ht
  rcases ht with h | h
  · exact hp t h
  · exact hq t h

theorem subT_prim {k : ℕ} {l : List (Fin k)} (a : Prim k) (h : ∀ t ∈ a.tapes, t ∈ l) :
    SubT l (.prim a) := h

theorem subT_putW {k : ℕ} {l : List (Fin k)} (o : Fin k) (w : List Bool) (ho : o ∈ l) :
    SubT l (Tape.Prog.putW o w) := fun t ht => by rw [tapes_putW o w t ht]; exact ho

theorem subT_map {n k : ℕ} {l : List (Fin k)} (u : Fin n → Fin k) (p : Prog n)
    (h : ∀ j, u j ∈ l) : SubT l (Tape.Prog.map u p) := fun t ht => by
  rw [Prog.tapes_map] at ht
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp ht
  exact h j

theorem narrowP_of_subT {w k : ℕ} {q : Prog k} (l : List (Fin k)) (hl : l.length ≤ w)
    (hs : SubT l q) : NarrowP w q :=
  narrowP_of_subset l hl hs (Prog.tapes_ne_nil q)

/-- A primitive raises every tape by at most one. -/
theorem lenT_le_succ {k B : ℕ} (a : Prim k) {L : Fin k → ℕ} (h : ∀ t, L t ≤ B) (t : Fin k) :
    a.lenT L t ≤ B + 1 := by
  cases a <;> simp only [Prim.lenT, Function.update_apply] <;> (try split_ifs) <;>
    first
    | omega
    | exact Nat.le_succ_of_le (h _)
    | exact Nat.succ_le_succ (h _)
    | exact (Nat.sub_le _ _).trans (Nat.le_succ_of_le (h _))
    | exact (min_le_left _ _).trans (by omega)

/-! ### Wide frames and branches -/

theorem FXa.frame {w T k m : ℕ} (hk : ¬ k ≤ w) {σ : Fin k ↪ Fin K} {e : Fin m ↪ Fin k}
    {q : XProg m} {Pre Post : (Fin K → ℕ) → Prop} {t : ℕ} (h : FXa w T (e.trans σ) q Pre Post t) :
    FXa w T σ (.frame e q) Pre Post t := fun L hL => by
  obtain ⟨a1, a2, a3, a4⟩ := h L hL
  rw [Lafter_frame]
  refine ⟨a1, a2, a3, fun d M hM => ?_⟩
  have e' : ptime w σ d (.frame e q) L M = ptime w (e.trans σ) d q L M := by
    simp only [ptime, orLeafT, if_neg hk]
  rw [e']
  exact a4 d M hM

theorem Lafter_ifBit {k : ℕ} (σ : Fin k ↪ Fin K) (i : Fin k) (p q : XProg k) (L : Fin K → ℕ)
    (t : Fin K) : Lafter σ (.ifBit i p q) L t = max (Lafter σ p L t) (Lafter σ q L t) := by
  simp only [Lafter, XProg.lenBoundT]
  rcases embedF_cases σ L (fun t => max (p.lenBoundT (fun j => L (σ j)) t)
      (q.lenBoundT (fun j => L (σ j)) t)) t with ⟨hn, h⟩ | ⟨j, rfl, h⟩
  · rw [h]
    have : ∀ X : Fin k → ℕ, embedF σ L X t = L t := fun X => by simp only [embedF, hn, Option.elim]
    rw [this, this, max_self]
  · rw [h]; simp only [embedF_apply_self]

end SigabaNeo.Tape.Pack
