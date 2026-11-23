import PE.Impl.DualUse.Prog.BpComp

/-!
# The compiler of branching programs: laws

* `run_readL`: reading one leaf advances the cursor by one entry;
* **`run_treeP`**: the tree code appends `treeW` and advances the cursor by `2^(m+2)` entries,
  leaving every other tape as it was (scratch, leaf bits, inner counters blank again).
-/

namespace AdvancedEncryption.DualUse.BpComp

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog
open scoped Prog

/-- The leaf `u` of a table `T` of entries of `w` bits: the bit after `d1` bits of entry `u`. -/
def lfT (d1 w : ℕ) (T : List Bool) (u : ℕ) : Bool := hd (T.drop (u * w + d1))

/-- The tapes the tree code of `m + 2` levels writes. -/
def TW (m : ℕ) (t : Fin 64) : Prop :=
  t = tO ∨ t = tTT ∨ t = tA ∨ t = tB ∨ t = tb0 ∨ t = tb1 ∨ t = tb2 ∨ t = tb3 ∨ ∃ j < m, t = tc j

/-- A predicate on the frozen tapes, with blank scratch. -/
def Pq (Q : Store 64 → Prop) (s : Store 64) : Prop := Q s ∧ s tA = [] ∧ s tB = []

theorem Pq_ostable {Q : Store 64 → Prop} (hQ : OStable Q) : OStable (Pq Q) := by
  intro s w ⟨h1, h2, h3⟩
  exact ⟨hQ s w h1, by rw [Function.update_of_ne (by decide)]; exact h2,
    by rw [Function.update_of_ne (by decide)]; exact h3⟩

/-! ### Reading a leaf -/

theorem drop_take_one_hd (l : List Bool) : hd (l.take 1) = hd l := by
  cases l <;> rfl

/-- Close the goals of a pointwise comparison of updated stores. -/
macro "upd" : tactic => `(tactic| (simp +decide only [Function.update_apply] <;>
  split_ifs <;> subst_vars <;> first | rfl | (simp_all +decide; done) |
    (simp_all [Fin.ext_iff, eq_comm]; done)))

theorem run_readL (b : Fin 64) (hbT : b ≠ tTT) (hbA : b ≠ tA) (hbB : b ≠ tJB)
    (s : Store 64) (hA : s tA = []) {d1 d2 : ℕ} (h1 : (s tJZ).length = d1)
    (h2 : (s tJB).length = d2) (T0 : List Bool) (u : ℕ)
    (hT : s tTT = T0.drop (u * (d1 + 1 + d2))) :
    run (readL b) s = Function.update (Function.update s tTT (T0.drop ((u + 1) * (d1 + 1 + d2))))
      b ((T0.drop (u * (d1 + 1 + d2) + d1)).take 1) := by
  rw [readL, run_seq, run_seq, run_dropT_blank (by decide) _ hA, run_pop,
    run_dropT_blank (by decide) _ (by upd)]
  have e2 : (Function.update (Function.update (Function.update s tTT ((s tTT).drop (s tJZ).length))
      tTT ((Function.update s tTT ((s tTT).drop (s tJZ).length)) tTT).tail) b
      (((Function.update s tTT ((s tTT).drop (s tJZ).length)) tTT).take 1)) tJB = s tJB := by
    upd
  rw [e2]
  simp only [Function.update_self, hT, h1, h2, List.drop_drop, List.tail_drop]
  have e3 : (u + 1) * (d1 + 1 + d2) = u * (d1 + 1 + d2) + d1 + 1 + d2 := by ring
  rw [e3]
  funext t
  upd

/-! ### Emission of a node -/

theorem Em.congr {E : Prog 64} {P : Store 64 → Prop} {v v' : List Bool} (h : Em E P v)
    (e : v = v') : Em E P v' := e ▸ h

theorem em_srcP (Y : SLay) (sE nsE : ℕ → Prog 64) {P : Store 64 → Prop} (b b' : Fin 64) (c c' : Bool)
    (hs : Em (sE 1) P (blk (Y.s 1))) (hns : Em (nsE 1) P (blk (Y.ns 1))) :
    Em (srcP sE nsE Y b b') (fun s => P s ∧ hd (s b) = c ∧ hd (s b') = c')
      (blk (if c then (if c' then 0 else Y.ns 1) else (if c' then Y.s 1 else Y.zero))) := by
  intro s ⟨hP, hc, hc'⟩
  simp only [srcP, run_ifBit, hc, hc']
  cases c <;> cases c' <;>
    simp only [ite_true, ite_false, Bool.false_eq_true, hs s hP, hns s hP, run_emitU] <;> rfl

theorem em_nodeP (Y : SLay) (sE nsE : ℕ → Prog 64) {P : Store 64 → Prop} (hP : OStable P)
    (ℓ : ℕ) {loE hiE dE : Prog 64} {lo hi d : ℕ}
    (hs : Em (sE ℓ) P (blk (Y.s ℓ))) (hns : Em (nsE ℓ) P (blk (Y.ns ℓ)))
    (hlo : Em loE P (blk lo)) (hhi : Em hiE P (blk hi)) (hd : Em dE P (blk d)) :
    Em (nodeP sE nsE Y ℓ loE hiE dE) P (nodeW Y ℓ lo hi d) := by
  have h := (em_emitU P Y.x1).seq hP <| hs.seq hP <| hhi.seq hP <| (em_emitU P Y.x2).seq hP <|
    hns.seq hP <| hlo.seq hP <| hd.seq hP <| (em_emitU P Y.x1).seq hP (em_emitU P Y.x2)
  exact h.congr (by simp only [nodeW, insW, List.append_assoc])

/-! ### The tree -/

theorem tc_ne_TW0 (m : ℕ) : tc m ≠ tO ∧ tc m ≠ tTT ∧ tc m ≠ tA ∧ tc m ≠ tB ∧ tc m ≠ tb0 ∧
    tc m ≠ tb1 ∧ tc m ≠ tb2 ∧ tc m ≠ tb3 ∧ tc m ≠ tJZ ∧ tc m ≠ tJB :=
  ⟨tc_ne (by decide), tc_ne (by decide), tc_ne (by decide), tc_ne (by decide), tc_ne (by decide),
    tc_ne (by decide), tc_ne (by decide), tc_ne (by decide), tc_ne (by decide), tc_ne (by decide)⟩

theorem not_TW_tc {m : ℕ} (hm : m < 38) : ¬ TW m (tc m) := by
  rintro (h | h | h | h | h | h | h | h | ⟨j, hj, h⟩)
  all_goals first
    | exact (tc_ne (by decide) h) | exact absurd (tc_inj hm (by omega) h) (by omega)

theorem TW_mono {m m' : ℕ} (h : m ≤ m') {t : Fin 64} (ht : TW m t) : TW m' t := by
  rcases ht with h | h | h | h | h | h | h | h | ⟨j, hj, h⟩
  all_goals first
    | exact Or.inl h | exact Or.inr (Or.inl h) | exact Or.inr (Or.inr (Or.inl h))
    | exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨j, by omega, h⟩)))))))

theorem TW_O (m : ℕ) : TW m tO := Or.inl rfl
theorem TW_TT (m : ℕ) : TW m tTT := Or.inr (Or.inl rfl)
theorem TW_b0 (m : ℕ) : TW m tb0 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
theorem TW_b1 (m : ℕ) : TW m tb1 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
theorem TW_b2 (m : ℕ) : TW m tb2 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
theorem TW_b3 (m : ℕ) : TW m tb3 :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))

/-- The leaf bit `u` as a word of one bit. -/
def lb (d1 w : ℕ) (T0 : List Bool) (u : ℕ) : List Bool := (T0.drop (u * w + d1)).take 1

theorem hd_lb (d1 w : ℕ) (T0 : List Bool) (u : ℕ) : hd (lb d1 w T0 u) = lfT d1 w T0 u :=
  drop_take_one_hd _

/-- Reading four leaves. -/
theorem run_read4 (s : Store 64) (hA : s tA = []) {d1 d2 : ℕ} (hZ : (s tJZ).length = d1)
    (hJ : (s tJB).length = d2) (T0 : List Bool) (base : ℕ)
    (hT : s tTT = T0.drop (base * (d1 + 1 + d2))) :
    run (readL tb3) (run (readL tb2) (run (readL tb1) (run (readL tb0) s))) =
      Function.update (Function.update (Function.update (Function.update (Function.update s
        tTT (T0.drop ((base + 4) * (d1 + 1 + d2)))) tb0 (lb d1 (d1 + 1 + d2) T0 base))
        tb1 (lb d1 (d1 + 1 + d2) T0 (base + 1))) tb2 (lb d1 (d1 + 1 + d2) T0 (base + 2)))
        tb3 (lb d1 (d1 + 1 + d2) T0 (base + 3)) := by
  rw [run_readL tb0 (by decide) (by decide) (by decide) s hA hZ hJ T0 base hT,
    run_readL tb1 (by decide) (by decide) (by decide) _ (d1 := d1) (d2 := d2) (by upd) (by upd) (by upd) T0 (base + 1)
      (by upd),
    run_readL tb2 (by decide) (by decide) (by decide) _ (d1 := d1) (d2 := d2) (by upd) (by upd) (by upd) T0 (base + 2)
      (by upd),
    run_readL tb3 (by decide) (by decide) (by decide) _ (d1 := d1) (d2 := d2) (by upd) (by upd) (by upd) T0 (base + 3)
      (by upd)]
  funext t
  simp only [lb]
  upd

/-- **The law of the tree code.** -/
theorem run_treeP (Y : SLay) (sE nsE : ℕ → Prog 64) (d1 d2 : ℕ) (T0 : List Bool) :
    ∀ (m : ℕ), m < 38 → ∀ (Q : Store 64 → Prop), (∀ s t w, TW m t → Q s → Q (Function.update s t w)) →
    (∀ ℓ, Em (sE ℓ) (Pq Q) (blk (Y.s ℓ))) → (∀ ℓ, Em (nsE ℓ) (Pq Q) (blk (Y.ns ℓ))) →
    ∀ (dE : Prog 64) (d : ℕ), Em dE (Pq Q) (blk d) →
    ∀ (base : ℕ) (s : Store 64), Q s → s tA = [] → s tB = [] → s tb0 = [] → s tb1 = [] →
      s tb2 = [] → s tb3 = [] → (∀ j < m, s (tc j) = []) → (s tJZ).length = d1 →
      (s tJB).length = d2 → s tTT = T0.drop (base * (d1 + 1 + d2)) →
      run (treeP sE nsE Y m dE) s = Function.update (Function.update s tO
        (s tO ++ treeW Y (lfT d1 (d1 + 1 + d2) T0) m base d)) tTT
        (T0.drop ((base + 2 ^ (m + 2)) * (d1 + 1 + d2)))
  | 0, _, Q, hQ, hs, hns, dE, d, hdE, base, s, hQs, hA, hB, h0, h1, h2, h3, _, hZ, hJ, hT => by
    set w := d1 + 1 + d2 with hw
    set lf := lfT d1 w T0 with hlf
    simp only [treeP, run_seq]
    rw [run_read4 s hA hZ hJ T0 base hT]
    let P4 : Store 64 → Prop := fun t => Pq Q t ∧ hd (t tb0) = lf base ∧
      hd (t tb1) = lf (base + 1) ∧ hd (t tb2) = lf (base + 2) ∧ hd (t tb3) = lf (base + 3)
    have hQO : OStable Q := fun t v ht => hQ t tO v (TW_O 0) ht
    have hP4 : OStable P4 := by
      intro t v ⟨h, h0, h1, h2, h3⟩
      refine ⟨Pq_ostable hQO t v h, ?_, ?_, ?_, ?_⟩ <;>
        rw [Function.update_of_ne (by decide)] <;> assumption
    have hlo : Em (srcP sE nsE Y tb0 tb1) P4 (blk (src1W Y lf base)) :=
      (em_srcP Y sE nsE (P := Pq Q) tb0 tb1 (lf base) (lf (base + 1)) (hs 1) (hns 1)).mono
        (fun t ht => ⟨ht.1, ht.2.1, ht.2.2.1⟩)
    have hhi : Em (srcP sE nsE Y tb2 tb3) P4 (blk (src1W Y lf (base + 2))) :=
      (em_srcP Y sE nsE (P := Pq Q) tb2 tb3 (lf (base + 2)) (lf (base + 2 + 1)) (hs 1)
        (hns 1)).mono (fun t ht => ⟨ht.1, ht.2.2.2.1, ht.2.2.2.2⟩)
    rw [em_nodeP Y sE nsE hP4 2 ((hs 2).mono fun t ht => ht.1) ((hns 2).mono fun t ht => ht.1)
      hlo hhi (hdE.mono fun t ht => ht.1) _ ?h4]
    case h4 =>
      refine ⟨⟨?_, by upd, by upd⟩, ?_, ?_, ?_, ?_⟩
      · exact hQ _ _ _ (TW_b3 0) <| hQ _ _ _ (TW_b2 0) <| hQ _ _ _ (TW_b1 0) <|
          hQ _ _ _ (TW_b0 0) <| hQ _ _ _ (TW_TT 0) hQs
      all_goals simp only [Function.update_apply]; split_ifs <;> first | (exfalso; simp_all [Fin.ext_iff]; done) | simp [hd_lb, hlf, w]
    simp only [run_clear, treeW]
    have e4 : base + 2 ^ (0 + 2) = base + 4 := by norm_num
    rw [e4]
    generalize nodeW Y 2 (src1W Y lf base) (src1W Y lf (base + 2)) d = V
    generalize List.drop ((base + 4) * w) T0 = X
    generalize lb d1 (d1 + 1 + d2) T0 base = a0
    generalize lb d1 (d1 + 1 + d2) T0 (base + 1) = a1
    generalize lb d1 (d1 + 1 + d2) T0 (base + 2) = a2
    generalize lb d1 (d1 + 1 + d2) T0 (base + 3) = a3
    clear hlo hhi hP4 hdE hs hns
    clear_value P4 lf w
    clear hQO P4 hQ hQs hT hZ hJ hlf hw
    funext t
    upd
  | m + 1, hm, Q, hQ, hs, hns, dE, d, hdE, base, s, hQs, hA, hB, h0, h1, h2, h3, hc, hZ, hJ, hT => by
    have hm' : m < 38 := by omega
    set c := tc m with hcdef
    have hc0 : s c = [] := hc m (by omega)
    have hcTW : ∀ t, TW m t → t ≠ c := fun t ht e => not_TW_tc hm' (by rw [← hcdef, ← e]; exact ht)
    -- the sub-tree under a fixed counter word
    have sub : ∀ (v : List Bool) (lohi : ℕ) (b' : ℕ) (s' : Store 64), (if v = [] then Y.hi (m + 2)
        else Y.lo (m + 2)) = lohi → Q s' → s' c = v → s' tA = [] → s' tB = [] → s' tb0 = [] →
        s' tb1 = [] → s' tb2 = [] → s' tb3 = [] → (∀ j < m, s' (tc j) = []) →
        (s' tJZ).length = d1 → (s' tJB).length = d2 → s' tTT = T0.drop (b' * (d1 + 1 + d2)) →
        run (treeP sE nsE Y m (ifBlank c (emitU tO 512 (Y.hi (m + 2)))
          (emitU tO 512 (Y.lo (m + 2))))) s' = Function.update (Function.update s' tO
          (s' tO ++ treeW Y (lfT d1 (d1 + 1 + d2) T0) m b' lohi)) tTT
          (T0.drop ((b' + 2 ^ (m + 2)) * (d1 + 1 + d2))) := by
      intro v lohi b' s' hlh hQ' hv hA' hB' h0' h1' h2' h3' hc' hZ' hJ' hT'
      refine run_treeP Y sE nsE d1 d2 T0 m hm' (fun t => Q t ∧ t c = v) ?_
        (fun ℓ => (hs ℓ).mono fun t ht => ⟨ht.1.1, ht.2⟩)
        (fun ℓ => (hns ℓ).mono fun t ht => ⟨ht.1.1, ht.2⟩) _ lohi ?_ b' s' ⟨hQ', hv⟩
        hA' hB' h0' h1' h2' h3' hc' hZ' hJ' hT'
      · intro t u w hu ⟨h1, h2⟩
        exact ⟨hQ t u w (TW_mono (by omega) hu) h1, by rw [Function.update_of_ne (hcTW u hu).symm]; exact h2⟩
      · rw [← hlh]
        refine (em_ifBlank c v (P := Pq Q) (em_emitU _ _) (em_emitU _ _)).mono ?_ |>.congr ?_
        · intro t ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h3, h4⟩, h2⟩
        · split_ifs <;> rfl
    have hcO : c ≠ tO := tc_ne (by decide)
    have hcT : c ≠ tTT := tc_ne (by decide)
    have hcA : c ≠ tA := tc_ne (by decide)
    have hcB : c ≠ tB := tc_ne (by decide)
    have hc0' : c ≠ tb0 := tc_ne (by decide)
    have hc1' : c ≠ tb1 := tc_ne (by decide)
    have hc2' : c ≠ tb2 := tc_ne (by decide)
    have hc3' : c ≠ tb3 := tc_ne (by decide)
    have hcZ : c ≠ tJZ := tc_ne (by decide)
    have hcJ : c ≠ tJB := tc_ne (by decide)
    have hcj : ∀ j < m, tc j ≠ c := fun j hj e => by
      have := tc_inj (by omega) hm' e; omega
    have hTWc : TW (m + 1) c := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨m, by omega, rfl⟩)))))))
    simp only [treeP, run_seq]
    rw [← hcdef]
    have e0 : run (prim (.cons c true)) (run (prim (.cons c true)) s) =
        Function.update s c [true, true] := by
      simp only [run_prim, Prim.apply, Function.update_self, Function.update_idem, hc0]
    rw [e0, run_loop, Function.update_self]
    simp only [List.length_cons, List.length_nil, Nat.zero_add, Function.iterate_succ_apply,
      Function.iterate_zero_apply, tailAt, Function.update_self, Function.update_idem,
      List.tail_cons]
    rw [sub [true] (Y.lo (m + 2)) base _ (by simp) (hQ _ _ _ hTWc hQs) (by simp)
      (by rw [Function.update_of_ne hcA.symm]; exact hA) (by rw [Function.update_of_ne hcB.symm]; exact hB)
      (by rw [Function.update_of_ne hc0'.symm]; exact h0) (by rw [Function.update_of_ne hc1'.symm]; exact h1)
      (by rw [Function.update_of_ne hc2'.symm]; exact h2) (by rw [Function.update_of_ne hc3'.symm]; exact h3)
      (fun j hj => by rw [Function.update_of_ne (hcj j hj)]; exact hc j (by omega))
      (by rw [Function.update_of_ne hcZ.symm]; exact hZ) (by rw [Function.update_of_ne hcJ.symm]; exact hJ)
      (by rw [Function.update_of_ne hcT.symm]; exact hT)]
    have eR1 : (Function.update (Function.update (Function.update s c [true]) tO
        (Function.update s c [true] tO ++ treeW Y (lfT d1 (d1 + 1 + d2) T0) m base (Y.lo (m + 2))))
        tTT (List.drop ((base + 2 ^ (m + 2)) * (d1 + 1 + d2)) T0)) c = [true] := by
      rw [Function.update_of_ne hcT, Function.update_of_ne hcO, Function.update_self]
    rw [eR1, List.tail_cons]
    rw [sub [] (Y.hi (m + 2)) (base + 2 ^ (m + 2)) _ (by simp)
      (hQ _ _ _ hTWc <| hQ _ _ _ (TW_TT _) <| hQ _ _ _ (TW_O _) <| hQ _ _ _ hTWc hQs)
      (by simp) (by upd) (by upd) (by upd) (by upd) (by upd) (by upd)
      (fun j hj => by
        have := hc j (by omega); have := hcj j hj
        have : tc j ≠ tO := tc_ne (by decide)
        have : tc j ≠ tTT := tc_ne (by decide)
        simp only [Function.update_apply]; split_ifs <;> simp_all)
      (by upd) (by upd) (by upd)]
    rw [em_nodeP Y sE nsE (Pq_ostable fun t v ht => hQ t tO v (TW_O _) ht) (m + 3) (hs _) (hns _)
      (em_emitU _ _) (em_emitU _ _) hdE _ ?hP]
    case hP =>
      refine ⟨?_, by upd, by upd⟩
      exact hQ _ _ _ (TW_TT _) <| hQ _ _ _ (TW_O _) <| hQ _ _ _ hTWc <| hQ _ _ _ (TW_TT _) <|
        hQ _ _ _ (TW_O _) <| hQ _ _ _ hTWc hQs
    have e4 : base + 2 ^ (m + 1 + 2) = base + 2 ^ (m + 2) + 2 ^ (m + 2) := by
      rw [show m + 1 + 2 = (m + 2) + 1 by omega, pow_succ]; omega
    rw [treeW, e4]
    generalize treeW Y (lfT d1 (d1 + 1 + d2) T0) m base (Y.lo (m + 2)) = A
    generalize treeW Y (lfT d1 (d1 + 1 + d2) T0) m (base + 2 ^ (m + 2)) (Y.hi (m + 2)) = B
    generalize nodeW Y (m + 3) (Y.lo (m + 2)) (Y.hi (m + 2)) d = V
    generalize List.drop ((base + 2 ^ (m + 2)) * (d1 + 1 + d2)) T0 = X
    generalize List.drop ((base + 2 ^ (m + 2) + 2 ^ (m + 2)) * (d1 + 1 + d2)) T0 = X'
    clear sub hQ hQs hs hns hdE
    funext t
    upd

end AdvancedEncryption.DualUse.BpComp
