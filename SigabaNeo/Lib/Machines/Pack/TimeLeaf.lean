import SigabaNeo.Lib.Machines.Pack.Machine

/-!
# Time of the packed machine: helpers and leaf groups

The time judgments (`ZProg.HT`) of the packed programs, for the concrete layout `packLayout w D`
and segment phases `packKit K w D`. A physical store of depth `d` is described by `Phys d M L`: the
store tape holds `pkW S` for a logical store `S` fitting the per-tape bounds `L`, the loop counters
are at most `M` long, every other tape is blank. Then every physical tape is at most
`max (Lam L) M` long, where `Lam L = Σ (2 L i + 1)` bounds `|pkW S|`.

* `ht_seqL_ph`: a sequence of phases followed by a program;
* `leafT σ p L M` and **`ht_leaf`**: the time of a leaf group: the reads (`6 Lam L + 16` each), the
  compiled narrow program (`timeBoundT p (L ∘ σ)`), the replacements (`putTime`), a final sweep.
-/

namespace SigabaNeo.Tape.Pack

open Cslib Function

variable {K w D : ℕ}

/-! ### Generic helpers -/

/-- The bound `Σ (2 L i + 1)` on the packed store of a store fitting `L`. -/
def Lam (L : Fin K → ℕ) : ℕ := ∑ i, (2 * L i + 1)

theorem length_pkW_le {S : Store K} {L : Fin K → ℕ} (h : Fits S L) : (pkW S).length ≤ Lam L := by
  rw [length_pkW, Lam]
  exact Finset.sum_le_sum fun i _ => by have := h i; omega

theorem Lam_mono {L L' : Fin K → ℕ} (h : L ≤ L') : Lam L ≤ Lam L' :=
  Finset.sum_le_sum fun i _ => Nat.add_le_add_right (Nat.mul_le_mul_left 2 (h i)) 1

theorem putTime_mono {E E' U U' : ℕ} (hE : E ≤ E') (hU : U ≤ U') : putTime E U ≤ putTime E' U' := by
  unfold putTime; omega

namespace ZProg

variable {k : ℕ}

theorem HT.xp' {p : XProg k} {Pre : Store k → Prop} {ℓ : Fin k → ℕ} (hw : p.WF)
    (h : ∀ s, Pre s → Fits s ℓ) : (ZProg.xp p).HT Pre (p.timeBoundT ℓ) := ⟨hw, ℓ, h, le_rfl⟩

theorem HT.ph' {P : Phase k} {Pre : Store k → Prop} {t : ℕ}
    (h : ∀ s, Pre s → P.pre s ∧ P.time s ≤ t) : (ZProg.ph P).HT Pre t := h

theorem HT.seq' {p q : ZProg k} {Pre Mid : Store k → Prop} {t₁ t₂ : ℕ} (h₁ : p.HT Pre t₁)
    (hm : ∀ s, Pre s → ∀ s' ∈ (p.law s).support, Mid s') (h₂ : q.HT Mid t₂) :
    (ZProg.seq p q).HT Pre (t₁ + t₂) := ⟨Mid, t₁, t₂, h₁, hm, h₂, le_rfl⟩

end ZProg

/-- **A sequence of phases**, each within `τ` steps, followed by `q`. -/
theorem ht_seqL_ph {c : ℕ} (Ps : List (Phase c)) (τ : ℕ) (q : ZProg c) :
    ∀ (Pre : Store c → Prop) (tq : ℕ),
    (∀ P, Pre P → ∀ i (hi : i < Ps.length),
      Ps[i].pre ((Ps.take i).foldl (fun P Ph => Ph.f P) P) ∧
      Ps[i].time ((Ps.take i).foldl (fun P Ph => Ph.f P) P) ≤ τ) →
    q.HT (fun P' => ∃ P, Pre P ∧ P' = Ps.foldl (fun P Ph => Ph.f P) P) tq →
    (seqL (Ps.map ZProg.ph) q).HT Pre (Ps.length * τ + tq) := by
  induction Ps with
  | nil =>
    intro Pre tq _ hq
    simpa [seqL] using hq.mono (fun P hP => ⟨P, hP, rfl⟩) le_rfl
  | cons Ph Ps ih =>
    intro Pre tq hP hq
    have h0 := fun P hP' => hP P hP' 0 (by simp)
    simp only [List.take_zero, List.foldl_nil, List.getElem_cons_zero] at h0
    have h := ZProg.HT.seq' (Mid := fun P' => ∃ P, Pre P ∧ P' = Ph.f P)
      (ZProg.HT.ph' (t := τ) (fun P hP' => h0 P hP'))
      (fun P hP' P' hP'' => by
        rw [ZProg.law_ph, PMF.support_pure, Set.mem_singleton_iff] at hP''
        exact ⟨P, hP', hP''⟩)
      (ih _ tq (fun P' ⟨P, hP', he⟩ i hi => by
        have := hP P hP' (i + 1) (by simp; omega)
        simpa [he] using this)
        (hq.mono (fun P' ⟨P'', ⟨P, hP', he⟩, he'⟩ => ⟨P, hP', by simp [he', he]⟩) le_rfl))
    refine (show (seqL ((Ph :: Ps).map ZProg.ph) q) = .seq (.ph Ph) (seqL (Ps.map ZProg.ph) q)
      from rfl) ▸ h.mono (fun _ h => h) ?_
    simp only [List.length_cons]
    ring_nf
    omega

/-! ### The concrete layout -/


@[simp] theorem val_st : ((packLayout w D).st : Fin (5 + w + D)).val = 0 := rfl
@[simp] theorem val_T : ((packLayout w D).T : Fin (5 + w + D)).val = 1 := rfl
theorem val_W (j : Fin w) : ((packLayout w D).W j : Fin (5 + w + D)).val = 5 + j := rfl
theorem val_F (e : Fin D) : ((packLayout w D).F e : Fin (5 + w + D)).val = 5 + w + e := rfl
@[simp] theorem val_fl : (flT w D).val = 2 := rfl
@[simp] theorem val_buf : (bufT w D).val = 3 := rfl

/-- A tape the read and replacement phases may target. -/
def Tgt (t : Fin (5 + w + D)) : Prop := t.val = 1 ∨ 5 ≤ t.val

theorem tgt_W (j : Fin w) : Tgt ((packLayout w D).W j) := Or.inr (by rw [val_W]; omega)
theorem tgt_T : Tgt (w := w) (D := D) (packLayout w D).T := Or.inl rfl
theorem tgt_F (e : Fin D) : Tgt ((packLayout w D).F e) := Or.inr (by rw [val_F]; omega)

theorem get_ok {t : Fin (5 + w + D)} (ht : Tgt t) : t ≠ (packLayout w D).st ∧ t ≠ flT w D ∧ (packLayout w D).st ≠ flT w D := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    have := congrArg Fin.val h <;> simp only [val_st, val_fl] at this <;> rcases ht with h' | h' <;>
    omega

theorem put_ok {t : Fin (5 + w + D)} (ht : Tgt t) : [(packLayout w D).st, t, flT w D, bufT w D].Nodup := by
  have h1 : t.val ≠ 0 := by rcases ht with h | h <;> omega
  have h2 : t.val ≠ 2 := by rcases ht with h | h <;> omega
  have h3 : t.val ≠ 3 := by rcases ht with h | h <;> omega
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true]
  refine ⟨⟨fun h => ?_, fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩ <;>
    have := congrArg Fin.val h <;> simp only [val_st, val_fl, val_buf] at this <;> omega

theorem kit_get_pre {j : Fin K} {t : Fin (5 + w + D)} (ht : Tgt t) (P : Store (5 + w + D))
    (h1 : P t = []) (h2 : P (flT w D) = []) : ((packKit K w D).get j t).pre P :=
  getPh_pre (get_ok ht) P h1 h2

theorem kit_get_time {j : Fin K} {t : Fin (5 + w + D)} (ht : Tgt t) (P : Store (5 + w + D)) :
    ((packKit K w D).get j t).time P = 6 * (P (packLayout w D).st).length + 16 :=
  getPh_time (get_ok ht) P

theorem kit_put_pre {j : Fin K} {t : Fin (5 + w + D)} (ht : Tgt t) (P : Store (5 + w + D))
    (h1 : P (flT w D) = []) (h2 : P (bufT w D) = []) : ((packKit K w D).put j t).pre P :=
  putPh_pre (put_ok ht) P h1 h2

theorem kit_put_time {j : Fin K} {t : Fin (5 + w + D)} (ht : Tgt t) (P : Store (5 + w + D)) :
    ((packKit K w D).put j t).time P = putTime (P (packLayout w D).st).length (P t).length :=
  putPh_time (put_ok ht) P

/-! ### Physical stores -/

/-- The physical stores of depth `d` whose logical store fits `L`, with counters at most `M`. -/
def Phys (d M : ℕ) (L : Fin K → ℕ) (P : Store (5 + w + D)) : Prop :=
  Clean (packLayout w D) d P ∧ (∀ e : Fin D, (P ((packLayout w D).F e)).length ≤ M) ∧ ∃ S : Store K, P (packLayout w D).st = pkW S ∧ Fits S L

theorem fl_clean {d : ℕ} {P : Store (5 + w + D)} (h : Clean (packLayout w D) d P) : P (flT w D) = [] :=
  h _ (fun h => by have := congrArg Fin.val h; simp [val_st, val_fl] at this)
    (fun e _ h => by have := congrArg Fin.val h; rw [val_F, val_fl] at this; omega)

theorem buf_clean {d : ℕ} {P : Store (5 + w + D)} (h : Clean (packLayout w D) d P) : P (bufT w D) = [] :=
  h _ (fun h => by have := congrArg Fin.val h; simp [val_st, val_buf] at this)
    (fun e _ h => by have := congrArg Fin.val h; rw [val_F, val_buf] at this; omega)

/-- Every tape of a physical store is at most `max (Lam L) M` long. -/
theorem Phys.length_le {d M : ℕ} {L : Fin K → ℕ} {P : Store (5 + w + D)} (h : Phys d M L P)
    (x : Fin (5 + w + D)) : (P x).length ≤ max (Lam L) M := by
  obtain ⟨hc, hF, S, hS, hL⟩ := h
  by_cases hx : x = (packLayout w D).st
  · subst hx; rw [hS]; exact (length_pkW_le hL).trans (le_max_left _ _)
  · by_cases hF' : ∃ e : Fin D, x = (packLayout w D).F e
    · obtain ⟨e, rfl⟩ := hF'; exact (hF e).trans (le_max_right _ _)
    · rw [hc x hx (fun e _ h => hF' ⟨e, h⟩)]; simp

theorem Phys.fits {d M : ℕ} {L : Fin K → ℕ} {P : Store (5 + w + D)} (h : Phys d M L P) :
    Fits P (fun _ => max (Lam L) M) := fun x => h.length_le x

/-- The bound after a program placed by `σ`. -/
def Lafter {k : ℕ} (σ : Fin k ↪ Fin K) (p : XProg k) (L : Fin K → ℕ) : Fin K → ℕ :=
  embedF σ L (p.lenBoundT fun j => L (σ j))

theorem Fits.embedF' {k : ℕ} {σ : Fin k ↪ Fin K} {S : Store K} {L : Fin K → ℕ} {a : Store k}
    {ℓ : Fin k → ℕ} (hS : Fits S L) (ha : Fits a ℓ) : Fits (embedF σ S a) (embedF σ L ℓ) :=
  Fits.embedF hS ha

theorem fits_lift {k : ℕ} (σ : Fin k ↪ Fin K) (p : XProg k) {S S' : Store K} {L : Fin K → ℕ}
    (hS : Fits S L) (hS' : S' ∈ (lift σ p.law S).support) : Fits S' (Lafter σ p L) := by
  rw [lift, PMF.support_map] at hS'
  obtain ⟨a, ha, rfl⟩ := hS'
  exact Fits.embedF hS (XProg.lenBoundT_spec p _ _ (fun j => hS (σ j)) a ha)

/-- **After a simulating program**, the physical store is again physical, for the bound after. -/
theorem phys_post {d M : ℕ} {L : Fin K → ℕ} {k : ℕ} {σ : Fin k ↪ Fin K} {p : XProg k}
    {q : ZProg (5 + w + D)} (hq : Sim (packLayout w D) d q (lift σ p.law)) {P : Store (5 + w + D)}
    (hP : Phys d M L P) {P' : Store (5 + w + D)} (hP' : P' ∈ (q.law P).support) :
    Phys d M (Lafter σ p L) P' := by
  obtain ⟨hc, hF, S, hS, hL⟩ := hP
  rw [hq P S hc hS, PMF.support_map] at hP'
  obtain ⟨S', hS', rfl⟩ := hP'
  refine ⟨hc.update_st _, fun e => ?_, S', by simp, fits_lift σ p hL hS'⟩
  dsimp only
  rw [update_of_ne ((packLayout w D).hFst e)]
  exact hF e

/-! ### Leaf groups -/

theorem supB_const (B : ℕ) : supB (fun _ : Fin (5 + w + D) => B) = B :=
  Finset.sup_const ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ B

theorem not_mem_take_finRange {m i : ℕ} (hi : i < m) :
    (⟨i, hi⟩ : Fin m) ∉ (List.finRange m).take i := by
  intro h
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp h
  simp only [List.getElem_take, List.getElem_finRange, Fin.ext_iff, List.length_take,
    List.length_finRange] at he hj
  simp at he
  omega

theorem nodup_take_finRange (m i : ℕ) : ((List.finRange m).take i).Nodup :=
  (List.nodup_finRange m).sublist (List.take_sublist _ _)

theorem fl_ne_W (j : Fin w) : flT w D ≠ (packLayout w D).W j := fun h => by
  have := congrArg Fin.val h; rw [val_W, val_fl] at this; omega

theorem buf_ne_W (j : Fin w) : bufT w D ≠ (packLayout w D).W j := fun h => by
  have := congrArg Fin.val h; rw [val_W, val_buf] at this; omega

theorem fl_ne_st : flT w D ≠ (packLayout w D).st := fun h => by
  have := congrArg Fin.val h; simp at this

theorem buf_ne_st : bufT w D ≠ (packLayout w D).st := fun h => by
  have := congrArg Fin.val h; simp at this

/-- A logical store updated at some places of `σ` by words fitting `ℓ'` fits `L ⊔ L'`. -/
theorem fits_foldl_update {m : ℕ} (σ : Fin m ↪ Fin K) (S : Store K) (L : Fin K → ℕ)
    (a : Store m) (ℓ' : Fin m → ℕ) (hS : Fits S L) (ha : Fits a ℓ') (l : List (Fin m))
    (hl : l.Nodup) :
    Fits (l.foldl (fun S j => update S (σ j) (a j)) S) (L ⊔ embedF σ L ℓ') := by
  obtain ⟨h1, h2⟩ := foldl_update_spec σ σ.injective a l hl S
  intro x
  by_cases hx : ∃ j ∈ l, σ j = x
  · obtain ⟨j, hj, rfl⟩ := hx
    rw [h1 j hj]
    exact (ha j).trans ((embedF_apply_self σ L ℓ' j).ge.trans (le_sup_right (a := L) _))
  · rw [h2 x (fun j hj he => hx ⟨j, hj, he⟩)]
    exact (hS x).trans (le_sup_left (b := embedF σ L ℓ') x)

/-- The time of a leaf group. -/
def leafT {m : ℕ} (σ : Fin m ↪ Fin K) (p : XProg m) (L : Fin K → ℕ) (M : ℕ) : ℕ :=
  m * (6 * Lam L + 16) +
    (p.timeBoundT (fun j => L (σ j)) +
      (m * putTime (Lam (L ⊔ Lafter σ p L)) (supB (p.lenBoundT fun j => L (σ j))) +
        (2 * (max (Lam (Lafter σ p L)) M + 0) + 3)))

/-- **The time of a leaf group.** -/
theorem ht_leaf {m : ℕ} (σ : Fin m ↪ Fin K) (h : m ≤ w) (p : XProg m) (hp : p.WF) (d M : ℕ)
    (L : Fin K → ℕ) :
    (leaf (packLayout w D) (packKit K w D) σ h p).HT (Phys d M L) (leafT σ p L M) := by
  set W' := wsE (packLayout w D) h
  set ℓ := fun j => L (σ j)
  set ℓ' := p.lenBoundT ℓ
  have hg : ((List.finRange m).map fun j =>
      ZProg.ph ((packKit K w D).get (σ j) (wsE (packLayout w D) h j))) =
      ((List.finRange m).map fun j => (packKit K w D).get (σ j) (W' j)).map ZProg.ph := by
    simp [List.map_map, W']
  have hp' : ((List.finRange m).map fun j =>
      ZProg.ph ((packKit K w D).put (σ j) (wsE (packLayout w D) h j))) =
      ((List.finRange m).map fun j => (packKit K w D).put (σ j) (W' j)).map ZProg.ph := by
    simp [List.map_map, W']
  have hW'st : ∀ j, W' j ≠ (packLayout w D).st := fun j => wsE_ne_st _ h j
  -- the stores after the reads
  have hgets : ∀ (P : Store (5 + w + D)) (S : Store K), P (packLayout w D).st = pkW S →
      ∀ l : List (Fin m), (l.map fun j => (packKit K w D).get (σ j) (W' j)).foldl
        (fun P Ph => Ph.f P) P = l.foldl (fun P j => update P (W' j) (S (σ j))) P := by
    intro P S hS l
    rw [List.foldl_map]
    exact gets_fold (kit := packKit K w D) σ h S l P hS
  unfold leaf
  rw [hg]
  refine (ht_seqL_ph _ (6 * Lam L + 16) _ _
    (p.timeBoundT ℓ + (m * putTime (Lam (L ⊔ Lafter σ p L)) (supB ℓ') +
      (2 * (max (Lam (Lafter σ p L)) M + 0) + 3))) ?_ ?_).mono (fun _ h => h)
    (by simp [leafT, ℓ, ℓ'])
  · intro P hP i hi
    obtain ⟨hc, hF, S, hS, hL⟩ := hP
    simp only [List.length_map, List.length_finRange] at hi
    rw [← List.map_take, hgets P S hS]
    obtain ⟨-, h2⟩ := foldl_update_spec W' W'.injective (fun j => S (σ j))
      ((List.finRange m).take i) (nodup_take_finRange m i) P
    simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk]
    refine ⟨kit_get_pre (show Tgt (W' ⟨i, hi⟩) from tgt_W _) _ ?_ ?_, ?_⟩
    · rw [h2 _ (fun j hj he => not_mem_take_finRange hi (by have := W'.injective he; subst this; exact hj))]
      exact hc.W _
    · rw [h2 _ (fun j _ he => fl_ne_W _ he.symm)]
      exact fl_clean hc
    · rw [kit_get_time (show Tgt (W' ⟨i, hi⟩) from tgt_W _), h2 _ (fun j _ he => hW'st j he), hS]
      have := length_pkW_le hL
      omega
  · -- the narrow program, the replacements, the final sweep
    set Mid : Store (5 + w + D) → Prop := fun P2 => ∃ P S a, Phys d M L P ∧
      P (packLayout w D).st = pkW S ∧ Fits S L ∧ Fits a ℓ' ∧ P2 = embedF W' P a
    refine ZProg.HT.seq' (Mid := Mid)
      ((ZProg.HT.xp' (ℓ := embedF W' (fun _ => max (Lam L) M) ℓ) (p := XProg.frame W' p) hp ?_).mono
        (fun _ h => h) (le_of_eq (by
          rw [XProg.timeBoundT_frame]; congr 1; funext j; exact embedF_apply_self _ _ _ _))) ?_ ?_
    · rintro P1 ⟨P, ⟨hc, hF, S, hS, hL⟩, rfl⟩
      rw [hgets P S hS, foldl_update_finRange]
      exact Fits.embedF (Phys.fits ⟨hc, hF, S, hS, hL⟩) (fun j => hL (σ j))
    · rintro P1 ⟨P, ⟨hc, hF, S, hS, hL⟩, rfl⟩ P2 hP2
      rw [hgets P S hS, foldl_update_finRange, ZProg.law_xp, XProg.law_frame, embedF_comp_self,
        PMF.support_map] at hP2
      obtain ⟨a, ha, rfl⟩ := hP2
      exact ⟨P, S, a, ⟨hc, hF, S, hS, hL⟩, hS, hL,
        XProg.lenBoundT_spec p ℓ _ (fun j => hL (σ j)) a ha, embedF_embedF _ _ _ _⟩
    · rw [hp']
      refine (ht_seqL_ph _ (putTime (Lam (L ⊔ Lafter σ p L)) (supB ℓ')) _ _
        (2 * (max (Lam (Lafter σ p L)) M + 0) + 3) ?_ ?_).mono (fun _ h => h) (by simp)
      · rintro P2 ⟨P, S, a, ⟨hc, hF, -⟩, hS, hL, ha, rfl⟩ i hi
        simp only [List.length_map, List.length_finRange] at hi
        have hst2 : embedF W' P a (packLayout w D).st = pkW S := by
          rcases embedF_cases W' P a (packLayout w D).st with ⟨-, h'⟩ | ⟨j, hj, -⟩
          · rw [h', hS]
          · exact absurd hj (hW'st j)
        rw [← List.map_take, List.foldl_map,
          puts_fold (kit := packKit K w D) σ h a _ (nodup_take_finRange m i) _ S hst2
            (fun j _ => embedF_apply_self _ _ _ j)]
        obtain ⟨-, h2⟩ := foldl_update_spec W' W'.injective (fun _ => ([] : List Bool))
          ((List.finRange m).take i) (nodup_take_finRange m i) (embedF W' P a)
        have hout : ∀ x, x ≠ (packLayout w D).st → (∀ j, W' j ≠ x) → embedF W' P a x = P x :=
          fun x _ hx => by
            rcases embedF_cases W' P a x with ⟨-, h'⟩ | ⟨j, hj, -⟩
            · exact h'
            · exact absurd hj (hx j)
        simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk]
        refine ⟨kit_put_pre (show Tgt (W' ⟨i, hi⟩) from tgt_W _) _ ?_ ?_, ?_⟩
        · rw [update_of_ne fl_ne_st, h2 _ (fun j _ he => fl_ne_W _ he.symm),
            hout _ fl_ne_st (fun j he => fl_ne_W _ he.symm)]
          exact fl_clean hc
        · rw [update_of_ne buf_ne_st, h2 _ (fun j _ he => buf_ne_W _ he.symm),
            hout _ buf_ne_st (fun j he => buf_ne_W _ he.symm)]
          exact buf_clean hc
        · rw [kit_put_time (show Tgt (W' ⟨i, hi⟩) from tgt_W _), update_self, update_of_ne (hW'st _),
            h2 _ (fun j hj he => not_mem_take_finRange hi (by have := W'.injective he; subst this; exact hj)),
            embedF_apply_self]
          apply putTime_mono
          · exact length_pkW_le (fits_foldl_update σ S L a ℓ' hL ha _ (nodup_take_finRange m i))
              |>.trans le_rfl
          · exact (ha _).trans (le_supB ℓ' _)
      · refine (ZProg.HT.xp' (ℓ := fun _ => max (Lam (Lafter σ p L)) M)
          (p := XProg.prog (.prim (.clear (packLayout w D).T))) trivial ?_).mono
          (fun _ h => h) ?_
        · rintro P3 ⟨P2, ⟨P, S, a, ⟨hc, hF, -⟩, hS, hL, ha, rfl⟩, rfl⟩
          have hst2 : embedF W' P a (packLayout w D).st = pkW S := by
            rcases embedF_cases W' P a (packLayout w D).st with ⟨-, h'⟩ | ⟨j, hj, -⟩
            · rw [h', hS]
            · exact absurd hj (hW'st j)
          rw [List.foldl_map, puts_fold (kit := packKit K w D) σ h a _ (List.nodup_finRange m) _ S
            hst2 (fun j _ => embedF_apply_self _ _ _ j), foldl_update_finRange,
            foldl_update_finRange, embedF_embedF]
          have hblank : embedF W' P (fun _ => []) = P := by
            funext x
            rcases embedF_cases W' P (fun _ => []) x with ⟨-, h'⟩ | ⟨j, rfl, h'⟩
            · exact h'
            · rw [h']; exact (hc.W _).symm
          rw [hblank]
          intro x
          by_cases hx : x = (packLayout w D).st
          · subst hx
            rw [update_self]
            exact (length_pkW_le (Fits.embedF hL ha)).trans (le_max_left _ _)
          · rw [update_of_ne hx]
            by_cases hF' : ∃ e : Fin D, x = (packLayout w D).F e
            · obtain ⟨e, rfl⟩ := hF'; exact (hF e).trans (le_max_right _ _)
            · rw [hc x hx (fun e _ he => hF' ⟨e, he⟩)]; simp
        · simp only [XProg.timeBoundT, Prog.timeBoundT, Prim.pad, supB_const]
          omega

end SigabaNeo.Tape.Pack
