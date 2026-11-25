import SigabaNeoStd.Machines.Pack.TimeLeaf

/-!
# Time of the packed machine: the translation

`ptime σ d p L M` bounds the steps of `tr (packLayout w D) (packKit K w D) σ d p` from every
physical store `Phys d M L` (**`ht_tr`**). It follows the translation: leaf groups cost `leafT`
(the old per-tape time `timeBoundT` of the narrow program plus segment reads/replacements linear in
`Lam L = Σ (2 L i + 1)`), tests `testT`, `tailZ` `tailZT`, loops `L (σ i)` rounds charged at the
invariant bound `iterSupT` of the logical round bound (as `XProg.timeBoundT` does).
-/

namespace SigabaNeo.Tape.Pack

open Cslib Function

variable {K w D : ℕ}

/-! ### Well-formedness of a restriction -/

theorem Prog.wf_of_map {n k : ℕ} {u : Fin n → Fin k} (hu : Injective u) :
    ∀ {p : Prog n}, (Prog.map u p).WF → p.WF
  | .prim _, _ | .coin _, _ => trivial
  | .seq _ _, h | .ifBlank _ _ _, h | .ifBit _ _ _, h =>
    ⟨Prog.wf_of_map hu h.1, Prog.wf_of_map hu h.2⟩
  | .loop i _, h => ⟨Prog.wf_of_map hu h.1, (Prog.preserves_map hu i _).mp h.2⟩

theorem wf_localize {k : ℕ} (q : Prog k) (h : NarrowP w q) (hq : q.WF) :
    (Prog.localize _ h.2 q).WF := by
  refine Prog.wf_of_map (Prog.listEmb _ (List.nodup_dedup _)).injective ?_
  rw [Prog.map_localize _ _ _ _ (fun t ht => List.mem_dedup.mpr ht)]
  exact hq

/-! ### Tests -/

/-- The time of a test of the segment `j` before a branch taking `t` steps. -/
def testT (j : Fin K) (L : Fin K → ℕ) (M t : ℕ) : ℕ :=
  (6 * Lam L + 16) + ((2 * (max (max (Lam L) M) (L j) + 0) + 3 + t) + 1)

theorem phys_update_T {d M : ℕ} {L : Fin K → ℕ} {P : Store (5 + w + D)} (hP : Phys d M L P)
    {S : Store K} (hS : P (packLayout w D).st = pkW S) (hL : Fits S L) (j : Fin K) :
    Fits (update P (packLayout w D).T (S j)) (fun _ => max (max (Lam L) M) (L j)) := by
  intro x
  by_cases hx : x = (packLayout w D).T
  · subst hx; rw [update_self]; exact (hL j).trans (le_max_right _ _)
  · rw [update_of_ne hx]; exact (hP.length_le x).trans (le_max_left _ _)

theorem ht_testZ {d M : ℕ} {L : Fin K → ℕ} (j : Fin K) (bit : Bool) {p q : ZProg (5 + w + D)}
    {t : ℕ} (hp : p.HT (Phys d M L) t) (hq : q.HT (Phys d M L) t) :
    (testZ (packLayout w D) (packKit K w D) j bit p q).HT (Phys d M L) (testT j L M t) := by
  set Mid : Store (5 + w + D) → Prop := fun P1 => ∃ P S, Phys d M L P ∧
    P (packLayout w D).st = pkW S ∧ Fits S L ∧ P1 = update P (packLayout w D).T (S j)
  have hget : (ZProg.ph ((packKit K w D).get j (packLayout w D).T)).HT (Phys d M L)
      (6 * Lam L + 16) := ZProg.HT.ph' fun P ⟨hc, hF, S, hS, hL⟩ =>
    ⟨kit_get_pre tgt_T P hc.T (fl_clean hc), by
      rw [kit_get_time tgt_T, hS]; have := length_pkW_le hL; omega⟩
  have hmid : ∀ P, Phys d M L P → ∀ P' ∈ ((ZProg.ph ((packKit K w D).get j
      (packLayout w D).T)).law P).support, Mid P' := by
    rintro P ⟨hc, hF, S, hS, hL⟩ P' hP'
    rw [ZProg.law_ph, PMF.support_pure, Set.mem_singleton_iff] at hP'
    exact ⟨P, S, ⟨hc, hF, S, hS, hL⟩, hS, hL, by
      rw [hP']; exact (packKit K w D).get_f j _ P S (packLayout w D).hTst hS⟩
  -- a branch: clear the test tape, then run the branch
  have hbr : ∀ r : ZProg (5 + w + D), r.HT (Phys d M L) t → ∀ Q : Store (5 + w + D) → Prop,
      (∀ P, Q P → Mid P) →
      (ZProg.seq (clrT (packLayout w D)) r).HT Q (2 * (max (max (Lam L) M) (L j) + 0) + 3 + t) := by
    intro r hr Q hQ
    refine ZProg.HT.seq' (Mid := Phys d M L)
      ((ZProg.HT.xp' (ℓ := fun _ => max (max (Lam L) M) (L j))
        (p := .prog (.prim (.clear (packLayout w D).T))) trivial ?_).mono (fun _ h => h) ?_) ?_ hr
    · intro P1 hP1
      obtain ⟨P, S, hP, hS, hL, rfl⟩ := hQ P1 hP1
      exact phys_update_T hP hS hL j
    · simp only [XProg.timeBoundT, Prog.timeBoundT, Prim.pad, supB_const, le_refl]
    · intro P1 hP1 P2 hP2
      obtain ⟨P, S, hP, hS, hL, rfl⟩ := hQ P1 hP1
      rw [clrT, ZProg.law_xp, XProg.law_prim, PMF.support_pure, Set.mem_singleton_iff] at hP2
      simp only [Prim.apply, update_idem] at hP2
      rw [hP2, update_self_of_eq _ _ _ hP.1.T]
      exact hP
  refine (ZProg.HT.seq' (t₂ := (2 * (max (max (Lam L) M) (L j) + 0) + 3 + t) + 1) hget hmid ?_).mono
    (fun _ h => h) le_rfl
  cases bit
  · exact ⟨_, hbr p hp _ (fun P h => h.1), hbr q hq _ (fun P h => h.1), le_rfl⟩
  · exact ⟨_, hbr p hp _ (fun P h => h.1), hbr q hq _ (fun P h => h.1), le_rfl⟩

/-! ### Dropping the first bit of a segment -/

/-- The time of `tailZ j`. -/
def tailZT (j : Fin K) (L : Fin K → ℕ) (M : ℕ) : ℕ :=
  (6 * Lam L + 16) + ((2 * (max (max (Lam L) M) (L j) + 0) + 3) + putTime (Lam L) (L j))

theorem ht_tailZ {d M : ℕ} {L : Fin K → ℕ} (j : Fin K) :
    (tailZ (packLayout w D) (packKit K w D) j).HT (Phys d M L) (tailZT j L M) := by
  have hget : (ZProg.ph ((packKit K w D).get j (packLayout w D).T)).HT (Phys d M L) (6 * Lam L + 16) :=
    ZProg.HT.ph' fun P ⟨hc, hF, S, hS, hL⟩ =>
      ⟨kit_get_pre tgt_T P hc.T (fl_clean hc), by
        rw [kit_get_time tgt_T, hS]; have := length_pkW_le hL; omega⟩
  set Mid1 : Store (5 + w + D) → Prop := fun P1 => ∃ P S, Phys d M L P ∧
    P (packLayout w D).st = pkW S ∧ Fits S L ∧ P1 = update P (packLayout w D).T (S j)
  set Mid2 : Store (5 + w + D) → Prop := fun P2 => ∃ P S, Phys d M L P ∧
    P (packLayout w D).st = pkW S ∧ Fits S L ∧ P2 = update P (packLayout w D).T (S j).tail
  refine (ZProg.HT.seq' (Mid := Mid1) hget ?_ (ZProg.HT.seq' (Mid := Mid2)
    ((ZProg.HT.xp' (ℓ := fun _ => max (max (Lam L) M) (L j))
      (p := .prog (.prim (.tail (packLayout w D).T))) trivial ?_).mono (fun _ h => h) ?_) ?_
    (ZProg.HT.ph' (t := putTime (Lam L) (L j)) ?_))).mono (fun _ h => h) (le_of_eq rfl)
  · rintro P ⟨hc, hF, S, hS, hL⟩ P' hP'
    rw [ZProg.law_ph, PMF.support_pure, Set.mem_singleton_iff] at hP'
    exact ⟨P, S, ⟨hc, hF, S, hS, hL⟩, hS, hL, by
      rw [hP']; exact (packKit K w D).get_f j _ P S (packLayout w D).hTst hS⟩
  · rintro P1 ⟨P, S, hP, hS, hL, rfl⟩
    exact phys_update_T hP hS hL j
  · simp only [XProg.timeBoundT, Prog.timeBoundT, Prim.pad, supB_const, le_refl]
  · rintro P1 ⟨P, S, hP, hS, hL, rfl⟩ P2 hP2
    rw [ZProg.law_xp, XProg.law_prim, PMF.support_pure, Set.mem_singleton_iff] at hP2
    simp only [Prim.apply, update_idem, update_self] at hP2
    exact ⟨P, S, hP, hS, hL, hP2⟩
  · rintro P2 ⟨P, S, ⟨hc, hF, -⟩, hS, hL, rfl⟩
    refine ⟨kit_put_pre tgt_T _ ?_ ?_, ?_⟩
    · rw [update_of_ne (fun h => by
        have := congrArg Fin.val h; simp at this)]
      exact fl_clean hc
    · rw [update_of_ne (fun h => by
        have := congrArg Fin.val h; simp at this)]
      exact buf_clean hc
    · rw [kit_put_time tgt_T, update_of_ne (packLayout w D).hTst.symm, update_self, hS]
      apply putTime_mono (length_pkW_le hL)
      rw [List.length_tail]
      have := hL j
      omega

/-! ### Loops -/

/-- The time of a wide loop on the segment `j` (`n = L j` rounds), its body taking `Rb` steps from
the invariant bound `Ls` with counters at most `M'`. -/
def loopT (j : Fin K) (L Ls : Fin K → ℕ) (M' Rb : ℕ) : ℕ :=
  (6 * Lam L + 16) + (L j * ((2 * max (Lam Ls) M' + 3) + (tailZT j Ls M' + Rb) + 1) + 2)

theorem ht_loopZ {d M : ℕ} {L : Fin K → ℕ} (j : Fin K) (e : Fin D) (he : (e : ℕ) = d)
    {body : ZProg (5 + w + D)} {μ : Store K → PMF (Store K)}
    (hbS : Sim (packLayout w D) (d + 1) body μ) (g : (Fin K → ℕ) → (Fin K → ℕ))
    (hg : ∀ (L' : Fin K → ℕ) (S : Store K), Fits S L' →
      ∀ S' ∈ (μ (tailAt j S)).support, Fits S' (g L'))
    {Rb : ℕ} (hbT : body.HT (Phys (d + 1) (max M (L j)) (iterSupT g (L j) L)) Rb) :
    (loopZ (lay := packLayout w D) (kit := packKit K w D) j e body).HT (Phys d M L)
      (loopT j L (iterSupT g (L j) L) (max M (L j)) Rb) := by
  set n := L j
  set Ls := iterSupT g n L
  set M' := max M (L j)
  set Fd := (packLayout w D).F e
  set st := (packLayout w D).st
  have hFst : Fd ≠ st := (packLayout w D).hFst e
  have hget : (ZProg.ph ((packKit K w D).get j Fd)).HT (Phys d M L) (6 * Lam L + 16) :=
    ZProg.HT.ph' fun P ⟨hc, hF, S, hS, hL⟩ =>
      ⟨kit_get_pre (tgt_F e) P (hc.F e (by omega)) (fl_clean hc), by
        rw [kit_get_time (tgt_F e), hS]; have := length_pkW_le hL; omega⟩
  -- the invariant of the loop
  set Inv : Store (5 + w + D) → Prop := fun P => Clean (packLayout w D) (d + 1) P ∧
    (∀ e' : Fin D, (P ((packLayout w D).F e')).length ≤ M') ∧
    ∃ S m, P st = pkW S ∧ Fits S (g^[m] L) ∧ (P Fd).length + m ≤ n
  have hInvPhys : ∀ P, Inv P → Phys (d + 1) M' Ls P := by
    rintro P ⟨hc, hF, S, m, hS, hL, hm⟩
    exact ⟨hc, hF, S, hS, hL.mono (le_iterSupT g (by omega) L)⟩
  have hloop : (ZProg.loop Fd (.seq (tailZ (packLayout w D) (packKit K w D) j) body)).HT
      (fun P1 => ∃ P S, Phys d M L P ∧ P st = pkW S ∧ Fits S L ∧ P1 = update P Fd (S j))
      (n * ((2 * max (Lam Ls) M' + 3) + (tailZT j Ls M' + Rb) + 1) + 2) := by
    refine ⟨Inv, n, max (Lam Ls) M', tailZT j Ls M' + Rb, ?_, ?_, ?_, ?_, le_rfl⟩
    · rintro P1 ⟨P, S, ⟨hc, hF, -⟩, hS, hL, rfl⟩
      refine ⟨⟨?_, ?_, S, 0, by rw [update_of_ne hFst.symm, hS], hL, by
        rw [update_self]; have := hL j; simp; omega⟩, by rw [update_self]; exact hL j⟩
      · intro x hx hF'
        rw [update_of_ne (fun h => hF' e (by omega) h)]
        exact hc x hx fun e' he' => hF' e' (by omega)
      · intro e'
        by_cases he' : e' = e
        · subst he'; rw [update_self]; exact (hL j).trans (le_max_right _ _)
        · rw [update_of_ne ((packLayout w D).F.injective.ne he')]
          exact (hF e').trans (le_max_left _ _)
    · intro P hP
      rw [maxLen_le_iff]
      exact (hInvPhys P hP).length_le
    · refine (ZProg.HT.seq' (Mid := Phys (d + 1) M' Ls) (ht_tailZ (d := d + 1) (M := M') (L := Ls) j)
        ?_ hbT).mono ?_ le_rfl
      · intro P hP P' hP'
        obtain ⟨hc, hF, S, hS, hL⟩ := hP
        rw [sim_tailZ (lay := packLayout w D) (kit := packKit K w D) j P S hc hS, PMF.pure_map,
          PMF.support_pure, Set.mem_singleton_iff] at hP'
        subst hP'
        refine ⟨hc.update_st _, fun e' => ?_, _, update_self _ _ _, fits_tailAt hL j |>.mono
          (tailB_le _ _)⟩
        rw [update_of_ne ((packLayout w D).hFst e')]
        exact hF e'
      · rintro u ⟨P, hP, hne, rfl⟩
        obtain ⟨hc, hF, S, m, hS, hL, hm⟩ := hP
        refine ⟨?_, fun e' => ?_, S, ?_, hL.mono (le_iterSupT g (by omega) L)⟩
        · intro x hx hF'
          simp only [tailAt]
          by_cases hxF : x = Fd
          · exact absurd hxF (hF' e (by omega))
          · rw [update_of_ne hxF]; exact hc x hx hF'
        · simp only [tailAt]
          by_cases he' : e' = e
          · subst he'; rw [update_self, List.length_tail]; have := hF e'; omega
          · rw [update_of_ne ((packLayout w D).F.injective.ne he')]; exact hF e'
        · simp only [tailAt]; rw [update_of_ne hFst.symm, hS]
    · intro P hP hne P' hP'
      obtain ⟨hc, hF, S, m, hS, hL, hm⟩ := hP
      have hsb := sim_seq (sim_tailZ (lay := packLayout w D) (kit := packKit K w D) (d := d + 1) j)
        hbS
      have hcl : Clean (packLayout w D) (d + 1) (tailAt Fd P) := by
        intro x hx hF'
        simp only [tailAt]
        by_cases hxF : x = Fd
        · exact absurd hxF (hF' e (by omega))
        · rw [update_of_ne hxF]; exact hc x hx hF'
      rw [hsb _ S hcl (by simp only [tailAt]; rw [update_of_ne hFst.symm, hS]), PMF.support_map]
        at hP'
      obtain ⟨S'', hS'', rfl⟩ := hP'
      simp only [PMF.pure_bind] at hS''
      have hfit := hg _ S hL S'' hS''
      have hlen : (P Fd).length ≠ 0 := by rw [Ne, List.length_eq_zero_iff]; exact hne
      refine ⟨⟨?_, fun e' => ?_, S'', m + 1, update_self _ _ _, ?_, ?_⟩, ?_⟩ <;> try dsimp only
      · intro x hx hF'
        rw [update_of_ne hx]
        simp only [tailAt]
        by_cases hxF : x = Fd
        · exact absurd hxF (hF' e (by omega))
        · rw [update_of_ne hxF]; exact hc x hx hF'
      · rw [update_of_ne ((packLayout w D).hFst e')]
        simp only [tailAt]
        by_cases he' : e' = e
        · subst he'; rw [update_self, List.length_tail]; have := hF e'; omega
        · rw [update_of_ne ((packLayout w D).F.injective.ne he')]; exact hF e'
      · rw [Function.iterate_succ_apply']; exact hfit
      · rw [update_of_ne hFst, tailAt, update_self, List.length_tail]; omega
      · rw [update_of_ne hFst, tailAt, update_self]
  refine (ZProg.HT.seq' hget ?_ hloop).mono (fun _ h => h) le_rfl
  rintro P ⟨hc, hF, S, hS, hL⟩ P' hP'
  rw [ZProg.law_ph, PMF.support_pure, Set.mem_singleton_iff] at hP'
  exact ⟨P, S, ⟨hc, hF, S, hS, hL⟩, hS, hL, by
    rw [hP']; exact (packKit K w D).get_f j _ P S hFst hS⟩

end SigabaNeo.Tape.Pack
