import SigabaNeo.Lib.Machines.Pack.TimeTr

/-!
# The time bound of the packing translation

`ptime w D σ d p L M` (and `ptimeP` for plain programs) follows `tr` node by node, and
**`ht_tr`**: from every physical store of depth `d` whose logical store fits `L` (counters at most
`M` long), `tr (packLayout w D) (packKit K w D) σ d p` halts within `ptime w D σ d p L M` steps.
-/

namespace SigabaNeo.Tape.Pack

open Cslib Function

variable {K : ℕ}

/-- The bound after one round of a wide loop of a plain program. -/
def gP {k : ℕ} (σ : Fin k ↪ Fin K) (i : Fin k) (b : Prog k) (L : Fin K → ℕ) : Fin K → ℕ :=
  Lafter σ (.prog b) (tailB (σ i) L)

/-- The bound after one round of a wide loop of a framed program. -/
def gX {k : ℕ} (σ : Fin k ↪ Fin K) (i : Fin k) (b : XProg k) (L : Fin K → ℕ) : Fin K → ℕ :=
  Lafter σ b (tailB (σ i) L)

/-- `leafT` of the restriction if the leaf is narrow, otherwise `alt`. -/
def orNarrowT (w : ℕ) {k : ℕ} (σ : Fin k ↪ Fin K) (q : Prog k) (alt : ℕ) (L : Fin K → ℕ)
    (M : ℕ) : ℕ :=
  if h : NarrowP w q then
    leafT ((Prog.listEmb _ (List.nodup_dedup _)).trans σ) (.prog (Prog.localize _ h.2 q)) L M
  else alt

/-- **The time of the translation of a plain program.** -/
def ptimeP (w : ℕ) {k : ℕ} (σ : Fin k ↪ Fin K) : ℕ → Prog k → (Fin K → ℕ) → ℕ → ℕ
  | _, .prim a, L, M => orNarrowT w σ (.prim a) 0 L M
  | _, .coin i, L, M => orNarrowT w σ (.coin i) 0 L M
  | d, .seq p q, L, M => orNarrowT w σ (.seq p q)
      (ptimeP w σ d p L M + ptimeP w σ d q (Lafter σ (.prog p) L) M) L M
  | d, .ifBlank i p q, L, M => orNarrowT w σ (.ifBlank i p q)
      (testT (σ i) L M (max (ptimeP w σ d p L M) (ptimeP w σ d q L M))) L M
  | d, .ifBit i p q, L, M => orNarrowT w σ (.ifBit i p q)
      (testT (σ i) L M (max (ptimeP w σ d p L M) (ptimeP w σ d q L M))) L M
  | d, .loop i b, L, M => orNarrowT w σ (.loop i b)
      (loopT (σ i) L (iterSupT (gP σ i b) (L (σ i)) L) (max M (L (σ i)))
        (ptimeP w σ (d + 1) b (iterSupT (gP σ i b) (L (σ i)) L) (max M (L (σ i))))) L M

/-- `leafT` if the program is narrow (`k ≤ w`), otherwise `alt`. -/
def orLeafT (w : ℕ) {k : ℕ} (σ : Fin k ↪ Fin K) (p : XProg k) (alt : ℕ) (L : Fin K → ℕ)
    (M : ℕ) : ℕ :=
  if k ≤ w then leafT σ p L M else alt

/-- **The time of the packing translation.** -/
def ptime (w : ℕ) : {k : ℕ} → (Fin k ↪ Fin K) → ℕ → XProg k → (Fin K → ℕ) → ℕ → ℕ
  | _, σ, d, .prog q, L, M => orLeafT w σ (.prog q) (ptimeP w σ d q L M) L M
  | _, σ, d, .frame e q, L, M => orLeafT w σ (.frame e q) (ptime w (e.trans σ) d q L M) L M
  | _, σ, d, .seq p q, L, M => orLeafT w σ (.seq p q)
      (ptime w σ d p L M + ptime w σ d q (Lafter σ p L) M) L M
  | _, σ, d, .ifBlank i p q, L, M => orLeafT w σ (.ifBlank i p q)
      (testT (σ i) L M (max (ptime w σ d p L M) (ptime w σ d q L M))) L M
  | _, σ, d, .ifBit i p q, L, M => orLeafT w σ (.ifBit i p q)
      (testT (σ i) L M (max (ptime w σ d p L M) (ptime w σ d q L M))) L M
  | _, σ, d, .loop i b, L, M => orLeafT w σ (.loop i b)
      (loopT (σ i) L (iterSupT (gX σ i b) (L (σ i)) L) (max M (L (σ i)))
        (ptime w σ (d + 1) b (iterSupT (gX σ i b) (L (σ i)) L) (max M (L (σ i))))) L M

variable {w D : ℕ}

theorem ht_orNarrow {d k : ℕ} (σ : Fin k ↪ Fin K) (q : Prog k) (hq : q.WF) (L : Fin K → ℕ)
    (M : ℕ) {alt : ZProg (5 + w + D)} {talt : ℕ}
    (halt : ¬ NarrowP w q → alt.HT (Phys d M L) talt) :
    (orNarrow (packLayout w D) (packKit K w D) σ q alt).HT (Phys d M L)
      (orNarrowT w σ q talt L M) := by
  unfold orNarrow orNarrowT
  split_ifs with h
  · exact ht_leaf _ h.1 _ (by simp only [XProg.WF]; exact wf_localize q h hq) d M L
  · exact halt h

/-- **The time of the translation of a plain program.** -/
theorem ht_trP (hw : 3 ≤ w) {k : ℕ} (σ : Fin k ↪ Fin K) :
    ∀ (d : ℕ) (q : Prog k), OkP w D d q → q.WF → ∀ (L : Fin K → ℕ) (M : ℕ),
      (trP (packLayout w D) (packKit K w D) σ d q).HT (Phys d M L) (ptimeP w σ d q L M)
  | _, .prim a, _, hq, L, M => ht_orNarrow σ _ hq L M (fun h => absurd (narrowP_prim hw a) h)
  | _, .coin i, _, hq, L, M => ht_orNarrow σ _ hq L M (fun h => absurd (narrowP_coin hw i) h)
  | d, .seq p q, ⟨hp, hq⟩, hwf, L, M => ht_orNarrow σ _ hwf L M (fun _ =>
      ZProg.HT.seq' (ht_trP hw σ d p hp hwf.1 L M)
        (fun P hP P' hP' => phys_post (p := XProg.prog p) (sim_trP hw σ d p hp) hP hP')
        (ht_trP hw σ d q hq hwf.2 _ M))
  | d, .ifBlank i p q, ⟨hp, hq⟩, hwf, L, M => ht_orNarrow σ _ hwf L M (fun _ =>
      ht_testZ (σ i) false ((ht_trP hw σ d p hp hwf.1 L M).mono (fun _ h => h) (le_max_left _ _))
        ((ht_trP hw σ d q hq hwf.2 L M).mono (fun _ h => h) (le_max_right _ _)))
  | d, .ifBit i p q, ⟨hp, hq⟩, hwf, L, M => ht_orNarrow σ _ hwf L M (fun _ =>
      ht_testZ (σ i) true ((ht_trP hw σ d p hp hwf.1 L M).mono (fun _ h => h) (le_max_left _ _))
        ((ht_trP hw σ d q hq hwf.2 L M).mono (fun _ h => h) (le_max_right _ _)))
  | d, .loop i b, ⟨hd, hb⟩, hwf, L, M => ht_orNarrow σ _ hwf L M (fun _ => by
      unfold loopAt
      rw [dif_pos hd]
      exact ht_loopZ (d := d) (M := M) (L := L) (σ i) ⟨d, hd⟩ rfl (sim_trP hw σ (d + 1) b hb)
        (gP σ i b)
        (fun L' S hS S' hS' => fits_lift σ (.prog b) (fits_tailAt hS (σ i)) hS')
        (ht_trP hw σ (d + 1) b hb hwf.1 _ _))

theorem ht_orLeaf {d k : ℕ} (σ : Fin k ↪ Fin K) (p : XProg k) (hp : p.WF)
    (L : Fin K → ℕ) (M : ℕ) {alt : ZProg (5 + w + D)} {talt : ℕ}
    (halt : ¬ k ≤ w → alt.HT (Phys d M L) talt) :
    (orLeaf (packLayout w D) (packKit K w D) σ p alt).HT (Phys d M L) (orLeafT w σ p talt L M) := by
  unfold orLeaf orLeafT
  split_ifs with h
  · exact ht_leaf σ h p hp d M L
  · exact halt h

/-- **The time of the packing translation.** -/
theorem ht_tr (hw : 3 ≤ w) : ∀ {k : ℕ} (σ : Fin k ↪ Fin K) (d : ℕ) (p : XProg k),
    OkX w D d p → p.WF → ∀ (L : Fin K → ℕ) (M : ℕ),
      (tr (packLayout w D) (packKit K w D) σ d p).HT (Phys d M L) (ptime w σ d p L M)
  | _, σ, d, .prog q, h, hwf, L, M => ht_orLeaf σ _ hwf L M (fun hk =>
      ht_trP hw σ d q (h.resolve_left hk) hwf L M)
  | _, σ, d, .frame e q, h, hwf, L, M => ht_orLeaf σ _ hwf L M (fun hk =>
      ht_tr hw (e.trans σ) d q (h.resolve_left hk) hwf L M)
  | _, σ, d, .seq p q, h, hwf, L, M => ht_orLeaf σ _ hwf L M (fun hk =>
      have h' := h.resolve_left hk
      ZProg.HT.seq' (ht_tr hw σ d p h'.1 hwf.1 L M)
        (fun P hP P' hP' => phys_post (sim_tr hw σ d p h'.1) hP hP')
        (ht_tr hw σ d q h'.2 hwf.2 _ M))
  | _, σ, d, .ifBlank i p q, h, hwf, L, M => ht_orLeaf σ _ hwf L M (fun hk =>
      have h' := h.resolve_left hk
      ht_testZ (σ i) false ((ht_tr hw σ d p h'.1 hwf.1 L M).mono (fun _ h => h) (le_max_left _ _))
        ((ht_tr hw σ d q h'.2 hwf.2 L M).mono (fun _ h => h) (le_max_right _ _)))
  | _, σ, d, .ifBit i p q, h, hwf, L, M => ht_orLeaf σ _ hwf L M (fun hk =>
      have h' := h.resolve_left hk
      ht_testZ (σ i) true ((ht_tr hw σ d p h'.1 hwf.1 L M).mono (fun _ h => h) (le_max_left _ _))
        ((ht_tr hw σ d q h'.2 hwf.2 L M).mono (fun _ h => h) (le_max_right _ _)))
  | _, σ, d, .loop i b, h, hwf, L, M => ht_orLeaf σ _ hwf L M (fun hk => by
      have h' := h.resolve_left hk
      unfold loopAt
      rw [dif_pos h'.1]
      exact ht_loopZ (d := d) (M := M) (L := L) (σ i) ⟨d, h'.1⟩ rfl (sim_tr hw σ (d + 1) b h'.2)
        (gX σ i b)
        (fun L' S hS S' hS' => fits_lift σ b (fits_tailAt hS (σ i)) hS')
        (ht_tr hw σ (d + 1) b h'.2 hwf.1 _ _))

end SigabaNeo.Tape.Pack
