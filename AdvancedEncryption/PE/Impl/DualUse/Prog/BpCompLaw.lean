import PE.Impl.DualUse.Prog.BpComp
import PE.Impl.Gates.BPWord

/-!
# The compiler of branching programs: laws

* `run_readL`: reading one leaf advances the cursor by one entry;
* **`run_treeP`**: the tree code appends `treeW` and advances the cursor by `2^(m+2)` entries,
  leaving every other tape as it was (scratch, leaf bits, inner counters blank again);
* `run_jBody`, `run_jLoop`: the `14` trees of a step; `run_stepP`: a step `i < 15` on the step
  store `iSt` (`SV.enc`: the tapes of a step, every other tape blank); `run_steps`: the `15` steps;
  `run_lastP`: the output table;
* **`run_bpCompP`**, **`law_bpCompP`**: from `C` on tape `0` (`inp C`), the compiler ends in
  `inp (compW R C)`, for every word `C` (no length condition);
* `good_bpCompP`: coin-free and well formed;
* **`rpW_bpRP`**: `rpW 512 (bpRP (tablesOf C)) = compW Rbp C` for every word `C` (`Rbp` the register
  layout of `BPCircuit`), through `rpW_tree` (a `MuxTree.tree` as words is `treeW`) and the leaves
  `leafStep_tablesOf`, `leafOut_tablesOf`;
* **`law_bpCompC`**: the compiler `bpCompC = bpCompP Rbp` writes `rpW 512 (bpRP (tablesOf C))`.
-/

namespace AdvancedEncryption.DualUse.BpComp

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Lattices
open AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates.BPCircuit
  AdvancedEncryption.PE.Gates.BPWord
open scoped Prog


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

theorem not_TW_tc {m : ℕ} (hm : m < 20) : ¬ TW m (tc m) := by
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

set_option maxHeartbeats 1000000 in
/-- **The law of the tree code.** -/
theorem run_treeP (Y : SLay) (sE nsE : ℕ → Prog 64) (d1 d2 : ℕ) (T0 : List Bool) :
    ∀ (m : ℕ), m ≤ 20 → ∀ (Q : Store 64 → Prop), (∀ s t w, TW m t → Q s → Q (Function.update s t w)) →
    (∀ ℓ, 1 ≤ ℓ → ℓ ≤ m + 2 → Em (sE ℓ) (Pq Q) (blk (Y.s ℓ))) →
    (∀ ℓ, 1 ≤ ℓ → ℓ ≤ m + 2 → Em (nsE ℓ) (Pq Q) (blk (Y.ns ℓ))) →
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
      (em_srcP Y sE nsE (P := Pq Q) tb0 tb1 (lf base) (lf (base + 1)) (hs 1 (by omega) (by omega))
        (hns 1 (by omega) (by omega))).mono
        (fun t ht => ⟨ht.1, ht.2.1, ht.2.2.1⟩)
    have hhi : Em (srcP sE nsE Y tb2 tb3) P4 (blk (src1W Y lf (base + 2))) :=
      (em_srcP Y sE nsE (P := Pq Q) tb2 tb3 (lf (base + 2)) (lf (base + 2 + 1))
        (hs 1 (by omega) (by omega)) (hns 1 (by omega) (by omega))).mono (fun t ht => ⟨ht.1, ht.2.2.2.1, ht.2.2.2.2⟩)
    rw [em_nodeP Y sE nsE hP4 2 ((hs 2 (by omega) (by omega)).mono fun t ht => ht.1)
      ((hns 2 (by omega) (by omega)).mono fun t ht => ht.1)
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
    have hm' : m < 20 := by omega
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
      refine run_treeP Y sE nsE d1 d2 T0 m (by omega) (fun t => Q t ∧ t c = v) ?_
        (fun ℓ h1 h2 => (hs ℓ h1 (by omega)).mono fun t ht => ⟨ht.1.1, ht.2⟩)
        (fun ℓ h1 h2 => (hns ℓ h1 (by omega)).mono fun t ht => ⟨ht.1.1, ht.2⟩) _ lohi ?_ b' s' ⟨hQ', hv⟩
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
    have e0 : run (snocN c true 2) (run (clr c) s) = Function.update s c [true, true] := by
      rw [run_snocN, run_clear, Function.update_self, Function.update_idem]; rfl
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
    rw [em_nodeP Y sE nsE (Pq_ostable fun t v ht => hQ t tO v (TW_O _) ht) (m + 3) (hs (m + 3) (by omega) (by omega)) (hns (m + 3) (by omega) (by omega))
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

/-! ### Emitters of the steps -/

/-- The tapes of the selector and root emitters in step `i` (parity `i mod 2`). -/
def FS (i : ℕ) (s : Store 64) : Prop :=
  s tIB = List.replicate (8 * i) true ∧ s tIZ = List.replicate (120 - 8 * i) false ∧
    s tPB = List.replicate (14 * (i % 2)) true ∧ s tPZ = List.replicate (14 - 14 * (i % 2)) false ∧
    s tQB = List.replicate (14 - 14 * (i % 2)) true ∧ s tQZ = List.replicate (14 * (i % 2)) false

/-- The layout fits: every register slot below `512`. -/
structure RL.Ok (R : RL) : Prop where
  z : rs R.z0 + 28 ≤ 512

theorem rep_app_rep_app (n m : ℕ) (a : Bool) (l : List Bool) :
    List.replicate n a ++ (List.replicate m a ++ l) = List.replicate (n + m) a ++ l := by
  rw [← List.append_assoc, List.replicate_append_replicate]

theorem blk_of {x y j : ℕ} (hx : x = j) (hy : y = 512 - j) :
    List.replicate x true ++ List.replicate y false = blk j := by
  rw [hx, hy]; rfl

/-- Normalize a concatenation of runs into `x` ones then `y` zeros. -/
macro "runs" : tactic => `(tactic| simp only [List.append_nil, List.append_assoc, rep_app_rep_app,
  List.replicate_append_replicate])

theorem em_inE {P : Store 64 → Prop} (i m : ℕ) (hi : i ≤ 15) (hm : m ≤ 8)
    (hP : ∀ s, P s → Pq (FS i) s) : Em (inE m) P (blk (1 + 8 * i + m)) := by
  intro s hs
  obtain ⟨⟨hIB, hIZ, -⟩, hA, hB⟩ := hP s hs
  rw [inE, run_dynE (by decide) (by decide) (by decide) _ _ _ s hA hB (by decide)]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hIB, hIZ]
  runs
  rw [blk_of (j := 1 + 8 * i + m) (by omega) (by omega)]

theorem em_zE (R : RL) (hR : R.Ok) {P : Store 64 → Prop} (i j : ℕ) (hj : j < 14)
    (hP : ∀ s, P s → Pq (FS i) s) : Em (zE R j) P (blk (zS R (i % 2) j)) := by
  intro s hs
  obtain ⟨⟨-, -, hPB, hPZ, -⟩, hA, hB⟩ := hP s hs
  have hz := hR.z
  have h2 : i % 2 < 2 := Nat.mod_lt _ (by omega)
  rw [zE, run_dynE (by decide) (by decide) (by decide) _ _ _ s hA hB (by decide)]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hPB, hPZ]
  runs
  rw [blk_of (j := zS R (i % 2) j) (by simp only [zS, rs]; omega)
    (by simp only [zS, rs] at hz ⊢; omega)]

/-- The tapes of the root emitter: bit `j` of the other bank. -/
def FJ (j : ℕ) (s : Store 64) : Prop :=
  s tJB = List.replicate j true ∧ s tJZ = List.replicate (13 - j) false

theorem em_rootE (R : RL) (hR : R.Ok) {P : Store 64 → Prop} (i j : ℕ) (hj : j < 14)
    (hP : ∀ s, P s → Pq (FS i) s ∧ FJ j s) : Em (rootE R) P (blk (zS R ((i + 1) % 2) j)) := by
  intro s hs
  obtain ⟨⟨⟨-, -, -, -, hQB, hQZ⟩, hA, hB⟩, hJB, hJZ⟩ := hP s hs
  have hz := hR.z
  have h2 : i % 2 < 2 := Nat.mod_lt _ (by omega)
  have hp : (i + 1) % 2 = 1 - i % 2 := by omega
  rw [rootE, run_dynE (by decide) (by decide) (by decide) _ _ _ s hA hB (by decide)]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hQB, hQZ, hJB, hJZ]
  runs
  rw [blk_of (j := zS R ((i + 1) % 2) j) (by simp only [zS, rs]; omega)
    (by simp only [zS, rs] at hz ⊢; omega)]

/-! ### Lists of instructions -/

theorem em_insP {P : Store 64 → Prop} (hP : OStable P) {d a b : Prog 64} {vd va vb : List Bool}
    (hd : Em d P vd) (ha : Em a P va) (hb : Em b P vb) : Em (insP d a b) P (vd ++ va ++ vb) :=
  (hd.seq hP (ha.seq hP hb)).congr (by simp [List.append_assoc])

theorem em_insL_nil (P : Store 64 → Prop) : Em (insL []) P [] := by
  intro s _; simp [insL]

theorem em_insL_map {P : Store 64 → Prop} (hP : OStable P) (f : ℕ → Prog 64) (g : ℕ → List Bool)
    (rest : List (Prog 64)) (vr : List Bool) (hr : Em (insL rest) P vr) :
    ∀ l : List ℕ, (∀ j ∈ l, Em (f j) P (g j)) → Em (insL (l.map f ++ rest)) P (l.flatMap g ++ vr)
  | [], _ => by simpa using hr
  | j :: l, h => by
    rw [List.map_cons, List.cons_append, insL, List.flatMap_cons, List.append_assoc]
    exact (h j (by simp)).seq hP (em_insL_map hP f g rest vr hr l fun j' hj' => h j' (by simp [hj']))

theorem FS_ostable (i : ℕ) : OStable (FS i) := by
  intro s w h
  simp only [FS] at h ⊢
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
  exact h

/-- **The prologue of a step.** -/
theorem em_proP (R : RL) (hR : R.Ok) (i : ℕ) (hi : i ≤ 15) : Em (proP R) (Pq (FS i)) (proW R i) := by
  have hP := Pq_ostable (FS_ostable i)
  have h32 := em_insL_map hP (fun j => insP (emitU tO 512 (rs (R.nz + j))) (zE R j) (zE R j))
    (fun j => insW (rs (R.nz + j)) (zS R (i % 2) j) (zS R (i % 2) j)) [] [] (em_insL_nil _)
    (List.range 14)
    (fun j hj => em_insP hP (em_emitU _ _) (em_zE R hR i j (List.mem_range.mp hj) fun _ h => h)
      (em_zE R hR i j (List.mem_range.mp hj) fun _ h => h))
  have h8 := em_insL_map hP (fun m => insP (emitU tO 512 (rs (R.na + m))) (inE m) (inE m))
    (fun m => insW (rs (R.na + m)) (1 + 8 * i + m) (1 + 8 * i + m)) _ _ h32 (List.range 8)
    (fun m hm => em_insP hP (em_emitU _ _) (em_inE i m hi (by have := List.mem_range.mp hm; omega) fun _ h => h)
      (em_inE i m hi (by have := List.mem_range.mp hm; omega) fun _ h => h))
  simpa [proP, proW] using h8

/-- **The global prologue.** -/
theorem em_gProP (R : RL) (P : Store 64 → Prop) (hP : OStable P) : Em (gProP R) P (gProW R) := by
  have h := em_insL_map hP (fun j => insP (emitU tO 512 (zS R 0 j)) (emitU tO 512 0)
    (emitU tO 512 0)) (fun j => insW (zS R 0 j) 0 0) [] [] (em_insL_nil _) (List.range 14)
    (fun j _ => em_insP hP (em_emitU _ _) (em_emitU _ _) (em_emitU _ _))
  have h2 := (em_insP hP (em_emitU P (rs R.zero)) (em_emitU P 0) (em_emitU P 0)).seq hP h
  simpa [gProP, gProW, insL, insW] using h2

/-! ### The store of a step -/

/-- The tapes of a step. -/
structure SV where
  o : List Bool
  cur : List Bool
  tt : List Bool
  ib : List Bool
  iz : List Bool
  pb : List Bool
  pz : List Bool
  qb : List Bool
  qz : List Bool
  jb : List Bool
  jz : List Bool
  jc : List Bool
  sc : List Bool
  ia : List Bool
  t31 : List Bool
  t120 : List Bool

/-- Its store: every other tape blank. -/
def SV.enc (v : SV) : Store 64 := fun t =>
  if t = tO then v.o else
  if t = tCUR then v.cur else
  if t = tTT then v.tt else
  if t = tIB then v.ib else
  if t = tIZ then v.iz else
  if t = tPB then v.pb else
  if t = tPZ then v.pz else
  if t = tQB then v.qb else
  if t = tQZ then v.qz else
  if t = tJB then v.jb else
  if t = tJZ then v.jz else
  if t = tJC then v.jc else
  if t = tSC then v.sc else
  if t = tIN then v.ia else
  if t = tT31 then v.t31 else
  if t = tT120 then v.t120 else []

theorem SV.enc_o (v : SV) : v.enc tO = v.o := by unfold SV.enc; rfl
theorem SV.enc_cur (v : SV) : v.enc tCUR = v.cur := by unfold SV.enc; rfl
theorem SV.enc_tt (v : SV) : v.enc tTT = v.tt := by unfold SV.enc; rfl
theorem SV.enc_ib (v : SV) : v.enc tIB = v.ib := by unfold SV.enc; rfl
theorem SV.enc_iz (v : SV) : v.enc tIZ = v.iz := by unfold SV.enc; rfl
theorem SV.enc_pb (v : SV) : v.enc tPB = v.pb := by unfold SV.enc; rfl
theorem SV.enc_pz (v : SV) : v.enc tPZ = v.pz := by unfold SV.enc; rfl
theorem SV.enc_qb (v : SV) : v.enc tQB = v.qb := by unfold SV.enc; rfl
theorem SV.enc_qz (v : SV) : v.enc tQZ = v.qz := by unfold SV.enc; rfl
theorem SV.enc_jb (v : SV) : v.enc tJB = v.jb := by unfold SV.enc; rfl
theorem SV.enc_jz (v : SV) : v.enc tJZ = v.jz := by unfold SV.enc; rfl
theorem SV.enc_jc (v : SV) : v.enc tJC = v.jc := by unfold SV.enc; rfl
theorem SV.enc_sc (v : SV) : v.enc tSC = v.sc := by unfold SV.enc; rfl
theorem SV.enc_ia (v : SV) : v.enc tIN = v.ia := by unfold SV.enc; rfl
theorem SV.enc_t31 (v : SV) : v.enc tT31 = v.t31 := by unfold SV.enc; rfl
theorem SV.enc_t120 (v : SV) : v.enc tT120 = v.t120 := by unfold SV.enc; rfl
theorem SV.upd_o (v : SV) (x : List Bool) :
    Function.update v.enc tO x = { v with o := x }.enc := by
  funext t; by_cases h : t = tO
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, SV.enc.eq_1, SV.enc.eq_1]; simp only [h, ite_false]
theorem SV.upd_cur (v : SV) (x : List Bool) :
    Function.update v.enc tCUR x = { v with cur := x }.enc := by
  funext t; by_cases h : t = tCUR
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, SV.enc.eq_1, SV.enc.eq_1]; simp only [h, ite_false]
theorem SV.upd_tt (v : SV) (x : List Bool) :
    Function.update v.enc tTT x = { v with tt := x }.enc := by
  funext t; by_cases h : t = tTT
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, SV.enc.eq_1, SV.enc.eq_1]; simp only [h, ite_false]
theorem SV.upd_ib (v : SV) (x : List Bool) :
    Function.update v.enc tIB x = { v with ib := x }.enc := by
  funext t; by_cases h : t = tIB
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, SV.enc.eq_1, SV.enc.eq_1]; simp only [h, ite_false]
theorem SV.upd_iz (v : SV) (x : List Bool) :
    Function.update v.enc tIZ x = { v with iz := x }.enc := by
  funext t; by_cases h : t = tIZ
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, SV.enc.eq_1, SV.enc.eq_1]; simp only [h, ite_false]
theorem SV.upd_pb (v : SV) (x : List Bool) :
    Function.update v.enc tPB x = { v with pb := x }.enc := by
  funext t; by_cases h : t = tPB
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, SV.enc.eq_1, SV.enc.eq_1]; simp only [h, ite_false]
theorem SV.upd_pz (v : SV) (x : List Bool) :
    Function.update v.enc tPZ x = { v with pz := x }.enc := by
  funext t; by_cases h : t = tPZ
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, SV.enc.eq_1, SV.enc.eq_1]; simp only [h, ite_false]
theorem SV.upd_qb (v : SV) (x : List Bool) :
    Function.update v.enc tQB x = { v with qb := x }.enc := by
  funext t; by_cases h : t = tQB
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, SV.enc.eq_1, SV.enc.eq_1]; simp only [h, ite_false]
theorem SV.upd_qz (v : SV) (x : List Bool) :
    Function.update v.enc tQZ x = { v with qz := x }.enc := by
  funext t; by_cases h : t = tQZ
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, SV.enc.eq_1, SV.enc.eq_1]; simp only [h, ite_false]
theorem SV.upd_jb (v : SV) (x : List Bool) :
    Function.update v.enc tJB x = { v with jb := x }.enc := by
  funext t; by_cases h : t = tJB
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, SV.enc.eq_1, SV.enc.eq_1]; simp only [h, ite_false]
theorem SV.upd_jz (v : SV) (x : List Bool) :
    Function.update v.enc tJZ x = { v with jz := x }.enc := by
  funext t; by_cases h : t = tJZ
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, SV.enc.eq_1, SV.enc.eq_1]; simp only [h, ite_false]
theorem SV.upd_jc (v : SV) (x : List Bool) :
    Function.update v.enc tJC x = { v with jc := x }.enc := by
  funext t; by_cases h : t = tJC
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, SV.enc.eq_1, SV.enc.eq_1]; simp only [h, ite_false]
theorem SV.upd_sc (v : SV) (x : List Bool) :
    Function.update v.enc tSC x = { v with sc := x }.enc := by
  funext t; by_cases h : t = tSC
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, SV.enc.eq_1, SV.enc.eq_1]; simp only [h, ite_false]
theorem SV.upd_ia (v : SV) (x : List Bool) :
    Function.update v.enc tIN x = { v with ia := x }.enc := by
  funext t; by_cases h : t = tIN
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, SV.enc.eq_1, SV.enc.eq_1]; simp only [h, ite_false]
theorem SV.upd_t31 (v : SV) (x : List Bool) :
    Function.update v.enc tT31 x = { v with t31 := x }.enc := by
  funext t; by_cases h : t = tT31
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, SV.enc.eq_1, SV.enc.eq_1]; simp only [h, ite_false]
theorem SV.upd_t120 (v : SV) (x : List Bool) :
    Function.update v.enc tT120 x = { v with t120 := x }.enc := by
  funext t; by_cases h : t = tT120
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, SV.enc.eq_1, SV.enc.eq_1]; simp only [h, ite_false]

theorem tc_eq_false {j : ℕ} {t : Fin 64} (h : t.val < 22) : (tc j = t) ↔ False :=
  ⟨tc_ne h, False.elim⟩

theorem SV.enc_tc (v : SV) (j : ℕ) : v.enc (tc j) = [] := by
  simp (disch := decide) only [SV.enc, tc_eq_false, ite_false]

theorem treeP_congr (sE nsE : ℕ → Prog 64) {Y Y' : SLay} (h0 : Y.zero = Y'.zero) (h1 : Y.x1 = Y'.x1)
    (h2 : Y.x2 = Y'.x2) (hl : Y.lo = Y'.lo) (hh : Y.hi = Y'.hi) :
    ∀ m dE, treeP sE nsE Y m dE = treeP sE nsE Y' m dE
  | 0, dE => by simp only [treeP, nodeP, srcP, h0, h1, h2]
  | m + 1, dE => by simp only [treeP, nodeP, h1, h2, hl, hh, treeP_congr sE nsE h0 h1 h2 hl hh m]

theorem treeS_eq (R : RL) (i : ℕ) (dE : Prog 64) :
    treeS R dE = treeP (sEd R) (nsEd R) (SY R i) 20 dE :=
  treeP_congr _ _ rfl rfl rfl rfl rfl 20 dE

/-- The selector emitters of step `i`. -/
theorem em_sEd (R : RL) (hR : R.Ok) {P : Store 64 → Prop} (i : ℕ) (hi : i ≤ 15)
    (hP : ∀ s, P s → Pq (FS i) s) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ 22) :
    Em (sEd R ℓ) P (blk ((SY R i).s ℓ)) := by
  simp only [sEd, SY, selS]
  split_ifs with h
  · exact (em_inE i (8 - ℓ) hi (by omega) hP).congr (by congr 1)
  · exact em_zE R hR i (ℓ - 9) (by omega) hP

theorem TW_val {m : ℕ} {t : Fin 64} (h : TW m t) : t.val < 9 ∨ 22 ≤ t.val := by
  rcases h with h | h | h | h | h | h | h | h | ⟨j, -, h⟩ <;> subst h <;> simp [tc_val]

theorem TW_ne {m : ℕ} {t u : Fin 64} (h : TW m t) (hu1 : 9 ≤ u.val) (hu2 : u.val < 22) : u ≠ t :=
  fun e => by subst e; have := TW_val h; omega

/-- Normalize updates of a step store. -/
macro "encs" : tactic => `(tactic| simp only [SV.upd_o, SV.upd_cur, SV.upd_tt, SV.upd_ib, SV.upd_iz, SV.upd_pb, SV.upd_pz, SV.upd_qb, SV.upd_qz, SV.upd_jb, SV.upd_jz, SV.upd_jc, SV.upd_sc, SV.upd_ia, SV.upd_t31, SV.upd_t120, SV.enc_o, SV.enc_cur, SV.enc_tt, SV.enc_ib, SV.enc_iz, SV.enc_pb, SV.enc_pz, SV.enc_qb, SV.enc_qz, SV.enc_jb, SV.enc_jz, SV.enc_jc, SV.enc_sc, SV.enc_ia, SV.enc_t31, SV.enc_t120])

/-- The step tapes are those of step `i`. -/
def SV.Ok (v : SV) (i : ℕ) : Prop :=
  v.ib = List.replicate (8 * i) true ∧ v.iz = List.replicate (120 - 8 * i) false ∧
    v.pb = List.replicate (14 * (i % 2)) true ∧ v.pz = List.replicate (14 - 14 * (i % 2)) false ∧
    v.qb = List.replicate (14 - 14 * (i % 2)) true ∧ v.qz = List.replicate (14 * (i % 2)) false

/-- **One round of the loop over the state bits.** -/
theorem run_jBody (R : RL) (hR : R.Ok) (i j : ℕ) (hi : i ≤ 15) (hj : j < 14) (v : SV) (hv : v.Ok i)
    (hjb : v.jb = List.replicate j true) (hjz : v.jz = List.replicate (13 - j) false)
    (h31 : v.t31 = List.replicate 13 true) (w : List Bool) :
    run (jBody R) (Function.update v.enc tJC w) = Function.update
      { v with o := v.o ++ treeW (SY R i) (lfT (13 - j) 14 v.cur) 20 0 (zS R ((i + 1) % 2) j),
               tt := v.cur.drop tblW, jb := List.replicate (13 - (13 - (j + 1))) true,
               jz := v.jz.tail }.enc tJC w := by
  obtain ⟨hib, hiz, hpb, hpz, hqb, hqz⟩ := hv
  let Q : Store 64 → Prop := fun s => FS i s ∧ FJ j s
  have hw : 13 - j + 1 + j = 14 := by omega
  rw [jBody, run_seq, run_copy, run_seq, treeS_eq R i]
  rw [run_treeP (SY R i) (sEd R) (nsEd R) (13 - j) j v.cur 20 le_rfl Q ?hQ
    (fun ℓ h1 h2 => em_sEd R hR i hi (fun s hs => ⟨hs.1.1, hs.2⟩) ℓ h1 (by omega))
    (fun ℓ _ _ => em_emitU _ _) (rootE R) _
    (em_rootE R hR i j hj fun s hs => ⟨⟨hs.1.1, hs.2⟩, hs.1.2⟩) 0 _ ?hQs (by upd) (by upd) (by upd)
    (by upd) (by upd) (by upd) ?hc ?hZ ?hJ ?hT]
  case hQ =>
    intro s t u ht ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7, h8⟩
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
      rw [Function.update_of_ne (TW_ne ht (by decide) (by decide))] <;> assumption
  case hQs =>
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> simp +decide [SV.enc, *]
  case hc =>
    intro j' _
    rw [Function.update_of_ne (tc_ne (by decide)), Function.update_of_ne (tc_ne (by decide)),
      SV.enc_tc]
  case hZ => simp +decide [SV.enc, hjz]
  case hJ => simp +decide [SV.enc, hjb]
  case hT => simp +decide [SV.enc]
  rw [hw, show 0 + 2 ^ (20 + 2) = 2 ^ 22 by norm_num, show 2 ^ 22 * 14 = tblW from rfl]
  generalize treeW (SY R i) (lfT (13 - j) 14 v.cur) 20 0 (zS R ((i + 1) % 2) j) = X
  rw [run_seq, run_tail]; encs
  rw [run_seq, run_copy]; encs
  rw [run_dropT_blank (by decide) _ (by unfold SV.enc; rfl)]; encs
  congr 1
  simp only [SV.mk.injEq, h31, hjz, List.length_tail, List.length_replicate, List.drop_replicate]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, ?_,
    trivial, trivial, trivial, trivial, trivial, trivial⟩
  rw [show 13 - j - 1 = 13 - (j + 1) by omega]

/-- The trees of step `i` on the table at `cur`, for the state bits `j < n`. -/
def treesW (R : RL) (i : ℕ) (cur : List Bool) (n : ℕ) : List Bool :=
  (List.range n).flatMap fun j => treeW (SY R i) (lfT (13 - j) 14 cur) 20 0 (zS R ((i + 1) % 2) j)

theorem treesW_succ (R : RL) (i : ℕ) (cur : List Bool) (n : ℕ) :
    treesW R i cur (n + 1) =
      treesW R i cur n ++ treeW (SY R i) (lfT (13 - n) 14 cur) 20 0 (zS R ((i + 1) % 2) n) := by
  simp [treesW, List.range_succ, List.flatMap_append]

theorem pq_enc (v : SV) (i : ℕ) (hv : v.Ok i) : Pq (FS i) v.enc := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> simp +decide [SV.enc, *]

/-- The state of the loop over the state bits before round `j`. -/
def jSt (v : SV) (R : RL) (i : ℕ) (o0 : List Bool) (j : ℕ) : SV :=
  { v with o := o0 ++ treesW R i v.cur j, tt := if j = 0 then [] else v.cur.drop tblW,
           jb := List.replicate (13 - (13 - j)) true, jz := List.replicate (13 - j) false, jc := [] }

/-- **The loop over the state bits.** -/
theorem run_jLoop (R : RL) (hR : R.Ok) (i : ℕ) (hi : i ≤ 15) (v : SV) (hv : v.Ok i)
    (ht31 : v.t31 = List.replicate 13 true) (o0 : List Bool) :
    run (loop tJC (jBody R)) { jSt v R i o0 0 with jc := List.replicate 14 true }.enc =
      (jSt v R i o0 14).enc := by
  have h := run_loop_count tJC (jBody R) (fun j => (jSt v R i o0 j).enc) 14 ?_
    (List.replicate 14 true) 0 (by simp)
  · simp only [SV.upd_jc, List.length_replicate, Nat.zero_add] at h
    rw [h]
    congr 1
  · intro j hj w
    rw [run_jBody R hR i j hi hj (jSt v R i o0 j) hv (by simp only [jSt]; congr 1; omega) rfl ht31 w]
    congr 1
    simp only [jSt, treesW_succ, List.append_assoc, Nat.add_one_ne_zero,
      ite_false]
    rw [List.tail_replicate, show 13 - j - 1 = 13 - (j + 1) by omega]

theorem run_jLoop' (R : RL) (hR : R.Ok) (i : ℕ) (hi : i ≤ 15) (u : SV) (hu : u.Ok i)
    (htt : u.tt = []) (hjb : u.jb = []) (hjz : u.jz = List.replicate 13 false)
    (hjc : u.jc = List.replicate 14 true) (ht31 : u.t31 = List.replicate 13 true) :
    run (loop tJC (jBody R)) u.enc = SV.enc
      { u with o := u.o ++ treesW R i u.cur 14, tt := u.cur.drop tblW,
               jb := List.replicate 13 true, jz := [], jc := [] } := by
  have h := run_jLoop R hR i hi u hu ht31 u.o
  have e : { jSt u R i u.o 0 with jc := List.replicate 14 true } = u := by
    cases u; simp_all [jSt, treesW]
  rw [e] at h
  rw [h]
  simp [jSt]

/-- The state before step `i`. -/
def iSt (C o0 : List Bool) (i : ℕ) (w : List Bool) : SV :=
  { o := o0, cur := C.drop (i * tblW), tt := [], ib := List.replicate (8 * i) true,
    iz := List.replicate (120 - 8 * i) false, pb := List.replicate (14 * (i % 2)) true,
    pz := List.replicate (14 - 14 * (i % 2)) false, qb := List.replicate (14 - 14 * (i % 2)) true,
    qz := List.replicate (14 * (i % 2)) false, jb := [], jz := [], jc := [], sc := w, ia := [],
    t31 := List.replicate 13 true, t120 := List.replicate 120 true }

theorem iSt_ok (C o0 : List Bool) (i : ℕ) (w : List Bool) : (iSt C o0 i w).Ok i :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **One step** `i < 15`. -/
theorem run_stepP (R : RL) (hR : R.Ok) (C o0 : List Bool) (i : ℕ) (hi : i < 15) (w : List Bool) :
    run (stepP R) (iSt C o0 i w).enc = (iSt C (o0 ++ stepW R C i) (i + 1) w).enc := by
  simp only [stepP, run_seq]
  rw [em_proP R hR i (by omega) _ (pq_enc _ i (iSt_ok C o0 i w))]
  simp only [run_clear, run_snocN]
  encs
  rw [run_jLoop' R hR i (by omega) _ ?ok ?tt ?jb ?jz ?jc ?t31]
  case ok => exact iSt_ok C o0 i w
  case tt => rfl
  case jb => rfl
  case jz => simp
  case jc => simp
  case t31 => rfl
  simp only [swapP, run_seq, run_copy, run_clear, run_tlN]
  encs
  rw [run_dropT_blank (t := tIB) (x := tIZ) (by decide) _ (by unfold SV.enc; rfl)]
  encs
  congr 1
  simp only [iSt, SV.mk.injEq]
  have h2 : i % 2 = 0 ∨ i % 2 = 1 := Nat.mod_two_eq_zero_or_one i
  have h3 : (i + 1) % 2 = 1 - i % 2 := by omega
  refine ⟨by simp [stepW, treesW, List.append_assoc], ?_, trivial, ?_, ?_, ?_, ?_, ?_, ?_,
    trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  · rw [List.drop_drop, Nat.add_mul, Nat.one_mul, Nat.add_comm]
  · rw [List.drop_replicate]; simp only [List.length_drop, List.length_replicate]; congr 1; omega
  · rw [List.drop_replicate]; congr 1
  all_goals rw [h3]; rcases h2 with h | h <;> rw [h]

/-- A store with the word `x` on tape `0`, every other tape blank. -/
def inp (x : List Bool) : Store 64 := Function.update (fun _ => []) tIN x

/-- The blank step store. -/
def SV.blank : SV := ⟨[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []⟩

theorem inp_eq (x : List Bool) : inp x = { SV.blank with ia := x }.enc := by
  have : (fun _ : Fin 64 => ([] : List Bool)) = SV.blank.enc := by
    funext t; rw [SV.enc.eq_1]; simp only [SV.blank, ite_self]
  rw [inp, this, SV.upd_ia]

/-- **The steps `0 … 14`.** -/
theorem run_steps (R : RL) (hR : R.Ok) (C o0 : List Bool) :
    run (loop tSC (stepP R)) (iSt C o0 0 (List.replicate 15 true)).enc =
      (iSt C (o0 ++ (List.range 15).flatMap (stepW R C)) 15 []).enc := by
  have h := run_loop_count tSC (stepP R)
    (fun i => (iSt C (o0 ++ (List.range i).flatMap (stepW R C)) i []).enc) 15
    (fun i hi w => by
      simp only [SV.upd_sc]
      have e : ∀ o i w, { iSt C o i [] with sc := w } = iSt C o i w := fun _ _ _ => rfl
      rw [e, e, run_stepP R hR C _ i hi w, List.range_succ, List.flatMap_append,
        List.flatMap_singleton, List.append_assoc])
    (List.replicate 15 true) 0 (by simp)
  simp only [SV.upd_sc, List.length_replicate, Nat.zero_add, List.range_zero, List.flatMap_nil,
    List.append_nil] at h
  exact h

theorem run_steps' (R : RL) (hR : R.Ok) (C o0 : List Bool) (u : SV) (h1 : u.o = o0)
    (h2 : u.cur = C) (h3 : u.tt = []) (h4 : u.ib = []) (h5 : u.iz = List.replicate 120 false)
    (h6 : u.pb = []) (h7 : u.pz = List.replicate 14 false) (h8 : u.qb = List.replicate 14 true)
    (h9 : u.qz = []) (h10 : u.jb = []) (h11 : u.jz = []) (h12 : u.jc = [])
    (h13 : u.sc = List.replicate 15 true) (h14 : u.ia = [])
    (h15 : u.t31 = List.replicate 13 true) (h16 : u.t120 = List.replicate 120 true) :
    run (loop tSC (stepP R)) u.enc =
      (iSt C (o0 ++ (List.range 15).flatMap (stepW R C)) 15 []).enc := by
  have e : u = iSt C o0 0 (List.replicate 15 true) := by cases u; simp_all [iSt]
  rw [e]; exact run_steps R hR C o0

theorem SV.eq_iSt (C o0 : List Bool) (i : ℕ) (w : List Bool) (u : SV) (h1 : u.o = o0)
    (h2 : u.cur = C.drop (i * tblW)) (h3 : u.tt = []) (h4 : u.ib = List.replicate (8 * i) true)
    (h5 : u.iz = List.replicate (120 - 8 * i) false) (h6 : u.pb = List.replicate (14 * (i % 2)) true)
    (h7 : u.pz = List.replicate (14 - 14 * (i % 2)) false)
    (h8 : u.qb = List.replicate (14 - 14 * (i % 2)) true)
    (h9 : u.qz = List.replicate (14 * (i % 2)) false) (h10 : u.jb = []) (h11 : u.jz = [])
    (h12 : u.jc = []) (h13 : u.sc = w) (h14 : u.ia = [])
    (h15 : u.t31 = List.replicate 13 true) (h16 : u.t120 = List.replicate 120 true) :
    u = iSt C o0 i w := by
  cases u; simp_all [iSt]

/-- **The last step.** -/
theorem run_lastP (R : RL) (hR : R.Ok) (C o0 : List Bool) :
    run (lastP R) (iSt C o0 15 []).enc = { iSt C (o0 ++ lastW R C) 15 [] with tt := [] }.enc := by
  simp only [lastP, run_seq]
  rw [em_proP R hR 15 le_rfl _ (pq_enc _ 15 (iSt_ok C o0 15 []))]
  encs
  rw [run_copy]
  encs
  rw [treeS_eq R 15]
  rw [run_treeP (SY R 15) (sEd R) (nsEd R) 0 0 (C.drop (15 * tblW)) 20 le_rfl (FS 15) ?hQ
    (fun ℓ h1 h2 => em_sEd R hR 15 le_rfl (fun s hs => hs) ℓ h1 (by omega))
    (fun ℓ _ _ => em_emitU _ _) _ _ (em_emitU _ (rs R.out)) 0 _ ?hQs (by unfold SV.enc; rfl) (by unfold SV.enc; rfl)
    (by unfold SV.enc; rfl) (by unfold SV.enc; rfl) (by unfold SV.enc; rfl) (by unfold SV.enc; rfl)
    ?hc (by encs; rfl) (by encs; rfl)
    (by encs; simp [iSt])]
  case hQ =>
    intro s t u ht ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      rw [Function.update_of_ne (TW_ne ht (by decide) (by decide))] <;> assumption
  case hQs => exact (pq_enc _ 15 (iSt_ok C o0 15 [])).1
  case hc => intro j _; exact SV.enc_tc _ j
  simp only [run_clear]
  encs
  congr 1
  simp [iSt, lastW, List.append_assoc]

/-- **The law of the compiler** (pure semantics): from `C` on tape `0`, `compW R C` on tape `0`,
every other tape blank. -/
theorem run_bpCompP (R : RL) (hR : R.Ok) (C : List Bool) :
    run (bpCompP R) (inp C) = inp (compW R C) := by
  rw [bpCompP]
  repeat rw [run_seq]
  rw [inp_eq, em_gProP R (fun _ => True) (fun _ _ _ => trivial) _ trivial]
  encs
  simp only [run_copy, run_clear, run_snocN]
  encs
  rw [run_steps' R hR C (gProW R) _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)]
  rw [run_lastP R hR]
  encs
  rw [inp_eq]
  congr 1


/-! ### Coin-freeness and well-formedness -/

/-- The tapes of an emitter. -/
def E3 (t : Fin 64) : Prop := t = tO ∨ t = tA ∨ t = tB

/-- A well-behaved emitter: no coin, well formed, writes only the output and the scratch. -/
def GoodE (p : Prog 64) : Prop := p.CoinFree ∧ p.WF ∧ WritesIn E3 p

theorem goodE_seq {p q : Prog 64} (hp : GoodE p) (hq : GoodE q) : GoodE (p ⨾ q) :=
  ⟨hp.1.seq' hq.1, ⟨hp.2.1, hq.2.1⟩, hp.2.2.seq hq.2.2⟩

theorem goodE_emitU (j : ℕ) : GoodE (emitU tO 512 j) :=
  ⟨coinFree_emitU _ _ _, wf_emitU _ _ _, writesIn_emitU (Or.inl rfl) _ _⟩

theorem goodE_dynE (a : ℕ) (xs : List (Fin 64)) (b : ℕ) : GoodE (dynE tO tA tB a xs b) :=
  ⟨coinFree_dynE _ _ _ _ _ _, wf_dynE (by decide) (by decide) _ _ _,
    writesIn_dynE (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) _ _ _⟩

theorem goodE_ifBit {i : Fin 64} {p q : Prog 64} (hp : GoodE p) (hq : GoodE q) :
    GoodE (ifBit i p q) := ⟨hp.1.ifBit' hq.1, ⟨hp.2.1, hq.2.1⟩, hp.2.2.ifBit hq.2.2⟩

theorem goodE_ifBlank {i : Fin 64} {p q : Prog 64} (hp : GoodE p) (hq : GoodE q) :
    GoodE (ifBlank i p q) := ⟨hp.1.ifBlank' hq.1, ⟨hp.2.1, hq.2.1⟩, hp.2.2.ifBlank hq.2.2⟩

theorem goodE_nodeP (sE nsE : ℕ → Prog 64) (Y : SLay) (ℓ : ℕ) {loE hiE dE : Prog 64}
    (hs : GoodE (sE ℓ)) (hns : GoodE (nsE ℓ)) (hlo : GoodE loE) (hhi : GoodE hiE)
    (hd : GoodE dE) : GoodE (nodeP sE nsE Y ℓ loE hiE dE) :=
  goodE_seq (goodE_emitU _) <| goodE_seq hs <| goodE_seq hhi <| goodE_seq (goodE_emitU _) <|
    goodE_seq hns <| goodE_seq hlo <| goodE_seq hd <| goodE_seq (goodE_emitU _) (goodE_emitU _)

/-- A well-behaved piece of the tree code of `m + 2` levels. -/
def GoodT (m : ℕ) (p : Prog 64) : Prop := p.CoinFree ∧ p.WF ∧ WritesIn (TW m) p

theorem GoodE.toT {p : Prog 64} (h : GoodE p) (m : ℕ) : GoodT m p :=
  ⟨h.1, h.2.1, h.2.2.mono fun t ht => by
    rcases ht with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))⟩

theorem goodT_seq {m : ℕ} {p q : Prog 64} (hp : GoodT m p) (hq : GoodT m q) : GoodT m (p ⨾ q) :=
  ⟨hp.1.seq' hq.1, ⟨hp.2.1, hq.2.1⟩, hp.2.2.seq hq.2.2⟩

theorem goodT_prim {m : ℕ} (q : Prim 64) (h : ∀ i ∈ q.writes, TW m i) : GoodT m (prim q) :=
  ⟨rfl, trivial, WritesIn.prim q h⟩

theorem goodT_readL (m : ℕ) {b : Fin 64} (hb : TW m b) : GoodT m (readL b) :=
  goodT_seq ⟨coinFree_dropT _ _ _, wf_dropT (by decide), writesIn_dropT (TW_TT m)
      (Or.inr (Or.inr (Or.inl rfl)))⟩ <|
    goodT_seq (goodT_prim _ (by simp [Prim.writes, TW_TT m, hb]))
      ⟨coinFree_dropT _ _ _, wf_dropT (by decide), writesIn_dropT (TW_TT m)
        (Or.inr (Or.inr (Or.inl rfl)))⟩

/-- **The tree code** is coin-free, well formed, and writes only its tapes. -/
theorem goodT_treeP (sE nsE : ℕ → Prog 64) (Y : SLay) (hs : ∀ ℓ, GoodE (sE ℓ))
    (hns : ∀ ℓ, GoodE (nsE ℓ)) : ∀ m, m ≤ 20 → ∀ dE, GoodE dE → GoodT m (treeP sE nsE Y m dE)
  | 0, _, dE, hd => by
    refine goodT_seq (goodT_readL 0 (TW_b0 0)) <| goodT_seq (goodT_readL 0 (TW_b1 0)) <|
      goodT_seq (goodT_readL 0 (TW_b2 0)) <| goodT_seq (goodT_readL 0 (TW_b3 0)) <|
      goodT_seq ((goodE_nodeP sE nsE Y 2 (hs 2) (hns 2) ?_ ?_ hd).toT 0) <|
      goodT_seq (goodT_prim _ (by simp [Prim.writes, TW_b0])) <|
      goodT_seq (goodT_prim _ (by simp [Prim.writes, TW_b1])) <|
      goodT_seq (goodT_prim _ (by simp [Prim.writes, TW_b2])) (goodT_prim _ (by simp [Prim.writes, TW_b3]))
    all_goals exact goodE_ifBit (goodE_ifBit (goodE_emitU _) (hns 1)) (goodE_ifBit (hs 1) (goodE_emitU _))
  | m + 1, hm, dE, hd => by
    have hc : TW (m + 1) (tc m) := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨m, by omega, rfl⟩)))))))
    have ih := goodT_treeP sE nsE Y hs hns m (by omega) _
      (goodE_ifBlank (i := tc m) (goodE_emitU (Y.hi (m + 2))) (goodE_emitU (Y.lo (m + 2))))
    refine goodT_seq (goodT_prim _ (by simp [Prim.writes, hc])) <|
      goodT_seq ⟨coinFree_snocN _ _ _, wf_snocN _ _ _, writesIn_snocN hc _ _⟩ <|
      goodT_seq ⟨ih.1.loop', ⟨ih.2.1, ih.2.2 (tc m) (not_TW_tc (by omega))⟩,
        WritesIn.loop hc (ih.2.2.mono fun t ht => TW_mono (by omega) ht)⟩
        ((goodE_nodeP sE nsE Y (m + 3) (hs _) (hns _) (goodE_emitU _) (goodE_emitU _) hd).toT _)

/-- Coin-free, well formed, writing only the tapes of `S`. -/
def GoodS (S : Fin 64 → Prop) (p : Prog 64) : Prop := p.CoinFree ∧ p.WF ∧ WritesIn S p

theorem GoodS.seq {S : Fin 64 → Prop} {p q : Prog 64} (hp : GoodS S p) (hq : GoodS S q) :
    GoodS S (p ⨾ q) := ⟨hp.1.seq' hq.1, ⟨hp.2.1, hq.2.1⟩, hp.2.2.seq hq.2.2⟩

theorem GoodS.mono {S S' : Fin 64 → Prop} {p : Prog 64} (hp : GoodS S p) (h : ∀ t, S t → S' t) :
    GoodS S' p := ⟨hp.1, hp.2.1, hp.2.2.mono h⟩

theorem GoodS.prim {S : Fin 64 → Prop} (q : Prim 64) (h : ∀ i ∈ q.writes, S i) : GoodS S (prim q) :=
  ⟨rfl, trivial, WritesIn.prim q h⟩

theorem GoodS.loop {S : Fin 64 → Prop} {c : Fin 64} {p : Prog 64} (hp : GoodS S p) (hc : ¬ S c)
    (S' : Fin 64 → Prop) (hS : ∀ t, S t → S' t) (hc' : S' c) : GoodS S' (loop c p) :=
  ⟨hp.1.loop', ⟨hp.2.1, hp.2.2 c hc⟩, WritesIn.loop hc' (hp.2.2.mono hS)⟩

theorem goodS_snocN {S : Fin 64 → Prop} {o : Fin 64} (ho : S o) (b : Bool) (n : ℕ) :
    GoodS S (snocN o b n) := ⟨coinFree_snocN _ _ _, wf_snocN _ _ _, writesIn_snocN ho _ _⟩

theorem goodS_tlN {S : Fin 64 → Prop} {o : Fin 64} (ho : S o) (n : ℕ) :
    GoodS S (tlN o n) := ⟨coinFree_tlN _ _, wf_tlN _ _, writesIn_tlN ho _⟩

theorem goodE_insL : ∀ (l : List (Prog 64)), (∀ p ∈ l, GoodE p) → GoodE (insL l)
  | [], _ => ⟨rfl, trivial, WritesIn.prim _ (by simp [Prim.writes, E3])⟩
  | p :: l, h => goodE_seq (h p (by simp)) (goodE_insL l fun q hq => h q (by simp [hq]))

theorem goodE_insP {d a b : Prog 64} (hd : GoodE d) (ha : GoodE a) (hb : GoodE b) :
    GoodE (insP d a b) := goodE_seq hd (goodE_seq ha hb)

theorem goodE_proP (R : RL) : GoodE (proP R) := by
  refine goodE_insL _ fun p hp => ?_
  simp only [List.mem_append, List.mem_map] at hp
  rcases hp with ⟨m, -, rfl⟩ | ⟨j, -, rfl⟩
  · exact goodE_insP (goodE_emitU _) (goodE_dynE _ _ _) (goodE_dynE _ _ _)
  · exact goodE_insP (goodE_emitU _) (goodE_dynE _ _ _) (goodE_dynE _ _ _)

theorem goodE_gProP (R : RL) : GoodE (gProP R) := by
  refine goodE_insL _ fun p hp => ?_
  simp only [List.mem_cons, List.mem_map] at hp
  rcases hp with rfl | ⟨j, -, rfl⟩ <;>
    exact goodE_insP (goodE_emitU _) (goodE_emitU _) (goodE_emitU _)

theorem goodE_sEd (R : RL) (ℓ : ℕ) : GoodE (sEd R ℓ) := by
  unfold sEd; split_ifs <;> exact goodE_dynE _ _ _

theorem goodT_treeS (R : RL) {dE : Prog 64} (hd : GoodE dE) : GoodT 20 (treeS R dE) :=
  goodT_treeP _ _ _ (goodE_sEd R) (fun _ => goodE_emitU _) 20 le_rfl dE hd

/-- The tapes of the steps: all but the step counter. -/
abbrev SS (t : Fin 64) : Prop := t ≠ tSC

theorem TW38_SS {t : Fin 64} (h : TW 20 t) : SS t ∧ t ≠ tJC := by
  have := TW_val h
  exact ⟨fun e => by subst e; simp at this, fun e => by subst e; simp at this⟩

theorem goodS_stepP (R : RL) : GoodS SS (stepP R) := by
  have hT := goodT_treeS R (goodE_dynE (rs R.z0) [tQB, tJB, tJZ, tQZ] (512 - rs R.z0 - 27))
  have hJ : GoodS (fun t => SS t ∧ t ≠ tJC) (jBody R) :=
    (GoodS.prim _ (by simp +decide)).seq <|
      (GoodS.mono hT fun t ht => TW38_SS ht).seq <|
      (GoodS.prim _ (by simp +decide)).seq <| (GoodS.prim _ (by simp +decide)).seq
        ⟨coinFree_dropT _ _ _, wf_dropT (by decide), writesIn_dropT (by decide) (by decide)⟩
  have hP := (goodE_proP R)
  refine (GoodS.mono ⟨hP.1, hP.2.1, hP.2.2⟩ fun t ht => by
    rcases ht with h | h | h <;> subst h <;> decide).seq ?_
  refine (GoodS.prim _ (by simp +decide)).seq <|
    (GoodS.prim _ (by simp +decide)).seq <|
    (goodS_snocN (by decide) _ _).seq <| (GoodS.prim _ (by simp +decide)).seq <|
    (goodS_snocN (by decide) _ _).seq <|
    (hJ.loop (by simp) SS (fun t ht => ht.1) (by decide)).seq <|
    (GoodS.prim _ (by simp +decide)).seq <|
    (GoodS.prim _ (by simp +decide)).seq <|
    (GoodS.prim _ (by simp +decide)).seq <|
    (GoodS.prim _ (by simp +decide)).seq <|
    (goodS_tlN (by decide) _).seq <| (GoodS.prim _ (by simp +decide)).seq <|
    GoodS.seq ⟨coinFree_dropT _ _ _, wf_dropT (by decide), writesIn_dropT (by decide) (by decide)⟩ ?_
  unfold swapP
  repeat (first | exact GoodS.prim _ (by simp +decide) |
    refine (GoodS.prim _ (by simp +decide)).seq ?_)

/-- **The compiler is coin-free and well formed.** -/
theorem good_bpCompP (R : RL) : (bpCompP R).CoinFree ∧ (bpCompP R).WF := by
  have hT := goodT_treeS R (goodE_emitU (rs R.out))
  have hP := goodE_proP R
  have hL : GoodS (fun _ => True) (lastP R) :=
    (GoodS.mono ⟨hP.1, hP.2.1, hP.2.2⟩ fun _ _ => trivial).seq <|
      (GoodS.prim _ (by simp)).seq <| (GoodS.mono hT fun _ _ => trivial).seq (GoodS.prim _ (by simp))
  have hG := goodE_gProP R
  have h : GoodS (fun _ => True) (bpCompP R) := by
    refine (GoodS.mono ⟨hG.1, hG.2.1, hG.2.2⟩ fun _ _ => trivial).seq ?_
    refine (GoodS.prim _ (by simp)).seq <| (GoodS.prim _ (by simp)).seq <|
      (GoodS.prim _ (by simp)).seq <| (goodS_snocN trivial _ _).seq <|
      (GoodS.prim _ (by simp)).seq <| (goodS_snocN trivial _ _).seq <|
      (GoodS.prim _ (by simp)).seq <| (goodS_snocN trivial _ _).seq <|
      (GoodS.prim _ (by simp)).seq <| (goodS_snocN trivial _ _).seq <|
      (GoodS.prim _ (by simp)).seq <| (goodS_snocN trivial _ _).seq <|
      (GoodS.prim _ (by simp)).seq <|
      (goodS_snocN trivial _ _).seq <|
      ((goodS_stepP R).loop (by simp [SS]) _ (fun _ _ => trivial) trivial).seq <| hL.seq ?_
    repeat (first | exact GoodS.prim _ (by simp) | refine (GoodS.prim _ (by simp)).seq ?_)
  exact ⟨h.1, h.2.1⟩

/-- **The compiler's law**: the point mass at `compW R C`. -/
theorem law_bpCompP (R : RL) (hR : R.Ok) (C : List Bool) :
    (bpCompP R).law (inp C) = PMF.pure (inp (compW R C)) := by
  rw [law_eq_run_of_coinFree _ (good_bpCompP R).1, run_bpCompP R hR C]

/-! ### The words of the circuit: `rpW` of `MuxTree.tree` is `treeW` -/

theorem unary_eq_blk (j : ℕ) : RP.unary 512 j = blk j := rfl

theorem rpW_single (ins : Instr (Fin 128) 93) :
    RP.rpW 512 [ins] = insW (RP.regSlot 128 ins.dst) (Src.slot ins.a) (Src.slot ins.b) := by
  simp [RP.rpW, insW, unary_eq_blk]

theorem slot_reg (r : Fin 93) : Src.slot (Src.reg (ι := Fin 128) r) = RP.regSlot 128 r := rfl

/-- **A mux tree as words.** -/
theorem rpW_tree (L : MuxTree.Layout (Fin 128) 93) (Y : SLay) (leaf : ℕ → Bool)
    (hs : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 22 → Src.slot (L.s ℓ) = Y.s ℓ)
    (hns : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 22 → Src.slot (L.ns ℓ) = Y.ns ℓ)
    (hz : RP.regSlot 128 L.zero = Y.zero) (h1 : RP.regSlot 128 L.x1 = Y.x1)
    (h2 : RP.regSlot 128 L.x2 = Y.x2) (hlo : ∀ ℓ, RP.regSlot 128 (L.lo ℓ) = Y.lo ℓ)
    (hhi : ∀ ℓ, RP.regSlot 128 (L.hi ℓ) = Y.hi ℓ) :
    ∀ m, m ≤ 20 → ∀ base dst,
      RP.rpW 512 (MuxTree.tree L leaf m base dst) = treeW Y leaf m base (RP.regSlot 128 dst) := by
  have hsrc : ∀ base, Src.slot (MuxTree.src1 L leaf base) = src1W Y leaf base := by
    intro base
    simp only [MuxTree.src1, src1W]
    split_ifs
    · rfl
    · exact hns 1 le_rfl (by omega)
    · exact hs 1 le_rfl (by omega)
    · exact hz
  have hnode : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 22 → ∀ (a b : Src (Fin 128) 93) (d : Fin 93),
      RP.rpW 512 (MuxTree.node L ℓ a b d) =
        nodeW Y ℓ (Src.slot a) (Src.slot b) (RP.regSlot 128 d) := by
    intro ℓ hl1 hl2 a b d
    simp only [MuxTree.node, RP.rpW_cons, RP.rpW_nil, nodeW, insW, unary_eq_blk, List.append_nil,
      List.append_assoc]
    rw [h1, hs ℓ hl1 hl2, h2, hns ℓ hl1 hl2]
    have e1 : Src.slot (Src.reg (ι := Fin 128) L.x1) = Y.x1 := h1
    have e2 : Src.slot (Src.reg (ι := Fin 128) L.x2) = Y.x2 := h2
    rw [e1, e2]
  intro m
  induction m with
  | zero =>
    intro _ base dst
    rw [MuxTree.tree, treeW, hnode 2 (by omega) (by omega), hsrc, hsrc]
  | succ m ih =>
    intro hm base dst
    rw [MuxTree.tree, treeW, RP.rpW_append, RP.rpW_append, ih (by omega), ih (by omega),
      hnode (m + 3) (by omega) (by omega), slot_reg, slot_reg, hlo, hhi]

/-- `treeW` reads its leaves only in its range. -/
theorem treeW_congr (Y : SLay) {leaf leaf' : ℕ → Bool} :
    ∀ m base d, (∀ u < 2 ^ (m + 2), leaf (base + u) = leaf' (base + u)) →
      treeW Y leaf m base d = treeW Y leaf' m base d
  | 0, base, d, h => by
    have h0 := h 0 (by norm_num); have h1 := h 1 (by norm_num)
    have h2 := h 2 (by norm_num); have h3 := h 3 (by norm_num)
    simp only [Nat.add_zero] at h0
    simp only [treeW, src1W, h0, h1, h2, show base + 2 + 1 = base + 3 by omega, h3]
  | m + 1, base, d, h => by
    have hp : 2 ^ (m + 1 + 2) = 2 ^ (m + 2) + 2 ^ (m + 2) := by rw [pow_succ]; omega
    simp only [treeW]
    rw [treeW_congr Y m base (Y.lo (m + 2)) (leaf' := leaf') (fun u hu => h u (by omega)),
      treeW_congr Y m (base + 2 ^ (m + 2)) (Y.hi (m + 2)) (leaf' := leaf') (fun u hu => by
        have := h (2 ^ (m + 2) + u) (by omega); rwa [← Nat.add_assoc] at this)]

theorem hd_drop : ∀ (l : List Bool) (k : ℕ), hd (l.drop k) = l.getD k false
  | [], k => by simp [hd]
  | a :: l, 0 => rfl
  | a :: l, k + 1 => by simp [hd_drop l k]

/-! ### The layout of `bpRP` -/

/-- The register layout of `BPCircuit`. -/
def Rbp : RL where
  zero := 0
  x1 := 91
  x2 := 92
  out := 1
  z0 := 1
  nz := 29
  na := 43
  lo ℓ := 51 + (ℓ - 2) % 20
  hi ℓ := 71 + (ℓ - 2) % 20

theorem Rbp_ok : Rbp.Ok := ⟨by decide⟩

theorem rpW_map (f : ℕ → Instr (Fin 128) 93) :
    ∀ l : List ℕ, RP.rpW 512 (l.map f) = l.flatMap fun j => RP.rpW 512 [f j]
  | [] => rfl
  | j :: l => by
    rw [List.map_cons, List.flatMap_cons, ← rpW_map f l]
    simp [RP.rpW]

theorem rpW_initRP : RP.rpW 512 initRP = gProW Rbp := by
  rw [initRP, RP.rpW_cons, rpW_map, gProW]
  simp only [unary_eq_blk, rpW_single]
  refine congrArg (insW (rs Rbp.zero) 0 0 ++ ·) (List.flatMap_congr fun j hj => ?_)
  have := List.mem_range.mp hj
  exact congrArg (fun x => insW x 0 0) (by simp only [rZ, RP.regSlot, zS, rs, Rbp]; omega)

theorem rpW_negs (i : ℕ) (hi : i ≤ 15) : RP.rpW 512 (negs i) = proW Rbp i := by
  rw [negs, RP.rpW_append, rpW_map, rpW_map, proW]
  refine congrArg₂ (· ++ ·) (List.flatMap_congr fun m hm => ?_) (List.flatMap_congr fun j hj => ?_)
  · have := List.mem_range.mp hm
    rw [rpW_single]
    have e1 : RP.regSlot 128 (rNA m) = rs (Rbp.na + m) := by
      simp only [rNA, RP.regSlot, rs, Rbp]; omega
    have e2 : Src.slot (inX i m) = 1 + 8 * i + m := by
      simp only [inX, inIdx, Src.slot]; omega
    rw [e1, e2]
  · have := List.mem_range.mp hj
    rw [rpW_single]
    have e1 : RP.regSlot 128 (rNZ j) = rs (Rbp.nz + j) := by
      simp only [rNZ, RP.regSlot, rs, Rbp]; omega
    have e2 : Src.slot (Src.reg (ι := Fin 128) (rZ i j)) = zS Rbp (i % 2) j := by
      simp only [rZ, Src.slot, zS, rs, Rbp]; omega
    rw [e1, e2]

/-- The slots of the trees of step `i`. -/
theorem rpW_tree_lay (i : ℕ) (hi : i ≤ 15) (leaf : ℕ → Bool) (dst : Fin 93) :
    RP.rpW 512 (MuxTree.tree (lay i) leaf 20 0 dst) = treeW (SY Rbp i) leaf 20 0 (RP.regSlot 128 dst) :=
  rpW_tree (lay i) (SY Rbp i) leaf
    (fun ℓ h1 h2 => by
      simp only [lay, SY, selS]
      split_ifs <;> simp only [inX, inIdx, rZ, Src.slot, zS, rs, Rbp] <;> omega)
    (fun ℓ h1 h2 => by
      simp only [lay, SY, nselS]
      split_ifs <;> simp only [rNA, rNZ, Src.slot, rs, Rbp] <;> omega)
    rfl rfl rfl (fun ℓ => rfl) (fun ℓ => rfl) 20 le_rfl 0 dst

theorem leafStep_tablesOf (C : List Bool) {i j u : ℕ} (hi : i < 15) (hj : j < 14) (hu : u < 2 ^ 22) :
    leafStep (tablesOf C) i j u = lfT (13 - j) 14 (C.drop (i * tblW)) u := by
  simp only [leafStep, tblLeaf, hu, hi, ↓reduceDIte, tablesOf, readNum, MuxTree.testBit_idx,
    decide_eq_true hj, Bool.true_and, lfT, List.drop_drop, hd_drop]
  congr 1
  simp only [entryIdx, tblW]
  omega

theorem leafOut_tablesOf (C : List Bool) {u : ℕ} (hu : u < 2 ^ 22) :
    leafOut (tablesOf C) u = lfT 0 1 (C.drop (15 * tblW)) u := by
  simp only [leafOut, tblLeaf, hu, ↓reduceDIte, tablesOf, lfT, List.drop_drop, hd_drop]
  congr 1
  simp only [outOff, tblW]
  omega

theorem rpW_flatMap (f : ℕ → RP (Fin 128) 93) :
    ∀ l : List ℕ, RP.rpW 512 (l.flatMap f) = l.flatMap fun j => RP.rpW 512 (f j)
  | [] => rfl
  | j :: l => by rw [List.flatMap_cons, List.flatMap_cons, RP.rpW_append, rpW_flatMap f l]

theorem rpW_treesRP (C : List Bool) (i : ℕ) (hi : i < 15) :
    RP.rpW 512 (treesRP (tablesOf C) i 14) = treesW Rbp i (C.drop (i * tblW)) 14 := by
  rw [treesRP, treesW, rpW_flatMap]
  refine List.flatMap_congr fun j hj => ?_
  have hj := List.mem_range.mp hj
  rw [rpW_tree_lay i (by omega)]
  have e : RP.regSlot 128 (rZ (i + 1) j) = zS Rbp ((i + 1) % 2) j := by
    simp only [rZ, RP.regSlot, zS, rs, Rbp]; omega
  rw [e]
  exact treeW_congr _ 20 0 _ fun u hu => by
    rw [Nat.zero_add]; exact leafStep_tablesOf C hi hj (by simpa using hu)

theorem rpW_stepsRP (C : List Bool) : ∀ n, n ≤ 15 →
    RP.rpW 512 (stepsRP (tablesOf C) n) = (List.range n).flatMap (stepW Rbp C)
  | 0, _ => rfl
  | n + 1, hn => by
    rw [stepsRP, RP.rpW_append, rpW_stepsRP C n (by omega), List.range_succ, List.flatMap_append,
      List.flatMap_singleton, stepRP, RP.rpW_append, rpW_negs n (by omega),
      rpW_treesRP C n (by omega)]
    rfl

theorem rpW_lastRP (C : List Bool) : RP.rpW 512 (lastRP (tablesOf C)) = lastW Rbp C := by
  rw [lastRP, RP.rpW_append, rpW_negs 15 le_rfl, rpW_tree_lay 15 le_rfl, lastW,
    show RP.regSlot 128 rOUT = rs Rbp.out from rfl]
  refine congrArg (proW Rbp 15 ++ ·) (treeW_congr _ 20 0 _ fun u hu => ?_)
  exact (by
    rw [Nat.zero_add]; exact leafOut_tablesOf C (by simpa using hu))

/-- **The word of the circuit of a predicate word is the compiler's word.** -/
theorem rpW_bpRP (C : List Bool) : RP.rpW 512 (bpRP (tablesOf C)) = compW Rbp C := by
  rw [bpRP, RP.rpW_append, RP.rpW_append, rpW_initRP, rpW_stepsRP C 15 le_rfl, rpW_lastRP]
  rfl

/-! ### The compiler of `KeyGen` and `Dec` -/

/-- **The compiler** of the predicate circuit, at the register layout of `BPCircuit`. -/
def bpCompC : Prog 64 := bpCompP Rbp

/-- **The law of the compiler**: from a predicate word `C` on tape `0` (any length), the instruction
stream `rpW 512 (bpRP (tablesOf C))` of its circuit on tape `0`, every other tape blank. -/
theorem law_bpCompC (C : List Bool) :
    bpCompC.law (inp C) = PMF.pure (inp (RP.rpW 512 (bpRP (tablesOf C)))) := by
  rw [bpCompC, law_bpCompP Rbp Rbp_ok C, rpW_bpRP]

theorem coinFree_bpCompC : bpCompC.CoinFree := (good_bpCompP Rbp).1

theorem wf_bpCompC : bpCompC.WF := (good_bpCompP Rbp).2

end AdvancedEncryption.DualUse.BpComp
