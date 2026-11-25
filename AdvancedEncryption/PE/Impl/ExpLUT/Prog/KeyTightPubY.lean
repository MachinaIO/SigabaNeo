import PE.Impl.ExpLUT.Prog.KeyTightCorr

/-!
# KeyGen: RedKeyT's tight back-end kernels at the cap `2^121` (port)

A mechanical port of the `Dc`-level parts of `RedKeyTPub`, `RedKeyTDig`, `RedKeyTUc` (the
standard envelope), `RedKeyTTail` (assembly), `RedKeyTNum`, `RedKeyTCand` (coins) and
`RedKeyTMain` from the cap `Mx = 2^150` to `My = 2^121` (every tape of the real KeyGen fits:
F3's prepared envelope is `2^120`, and the packed output `14 ++ 19` is `≤ 2^121`). Every name
carries the suffix `Y`; the time bounds are re-targeted to the smaller cap (public rows
`< 2^372`, digits `< 2^373`, candidate `< 2^339`, acceptance `< 2^335`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 1000
set_option maxRecDepth 100000

namespace AdvancedEncryption.ExpLUT.Prog.KeyTightY

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Prog.KeyTime
open AdvancedEncryption.ExpLUT.Prog.RedKeyT
open AdvancedEncryption.ExpLUT.Params
open SigabaNeo.Tape.XProg
open AdvancedEncryption.RingBTVW.Prog (bCoins tCoin)

/-- The tape cap of the real KeyGen attempt. -/
abbrev My : ℕ := 2 ^ 121

noncomputable def posTY : ℕ :=
  bhT Dc My (2 ^ 66) 0 + ((2 * My + 5) + appendAFTime My Dc.N Dc.K)

theorem prefixT_leY (n : ℕ) (hn : n ≤ 2 ^ 120) : prefixTime My n ≤ 2 ^ 249 := by
  unfold prefixTime moveAllowance
  calc _ ≤ (32 * 2 ^ 120 + 6) * (2 * 2 ^ 121 + 5) + (2 * 2 ^ 121 + 3) * (20 + 10 * 2 ^ 121) := by
        gcongr
    _ ≤ 2 ^ 249 := by norm_num

theorem gatherT_leY (n : ℕ) (hn : n ≤ 2 ^ 66) :
    gatherTime My (2 ^ 24) (2 ^ 16) (2 ^ 66) n ≤ 2 ^ 314 := by
  unfold gatherTime gatherStepTime fetchTime moveAllowance appendAllowance
  calc _ ≤ 2 * (2 * 2 ^ 121 + 5) + 2 ^ 66 * ((32 * (2 ^ 66 * (2 ^ 24 * 2 ^ 16)) + 6) *
        (2 * 2 ^ 121 + 5) + 2 * ((2 * 2 ^ 121 + 3) * (20 + 10 * 2 ^ 121)) +
        (4 * 2 ^ 121 + 6) * (2 * 2 ^ 121 + 5)) := by gcongr
    _ ≤ 2 ^ 314 := by norm_num

theorem autGT_leY (n k : ℕ) (hn : n ≤ 2 ^ 66) (hk : k ≤ 2 ^ 25) :
    autGT My (2 ^ 24) (2 ^ 16) n k ≤ 2 ^ 312 := by
  unfold autGT autQT autBT mvT appendAllowance operationBound
  calc _ ≤ (32 * 2 ^ 66 + 32 * 2 ^ 25 + 10) * (2 * 2 ^ 121 + 5) + (2 ^ 66 * (2 * 2 ^ 121 +
        ((2 * 2 ^ 121 + 5) + (2 * 2 ^ 121 + 3) * (20 + 10 * (2 ^ 24 * 2 ^ 16)) +
          1000 * (2 ^ 121 + 1) * (2 ^ 24 + 1) ^ 2 * (2 ^ 16 + 1) ^ 2 * (2 ^ 25 + 1) +
          (4 * 2 ^ 121 + 6) * (2 * 2 ^ 121 + 5)) + 4) + 2) := by gcongr
    _ ≤ 2 ^ 312 := by norm_num

theorem bhT_leY (i : ℕ) : bhT Dc My (2 ^ 66) i ≤ 2 ^ 315 := by
  have hb := bh_bounds_Dc i
  have h1 := prefixT_leY _ hb.1
  have h2 := gatherT_leY _ hb.2.1
  have h3 := autGT_leY _ _ hb.2.1 hb.2.2.1
  unfold bhT
  rw [rkN, rkK]
  calc _ ≤ 2 ^ 249 + (2 ^ 314 + 2 ^ 312) := Nat.add_le_add h1 (Nat.add_le_add h2 h3)
    _ ≤ 2 ^ 315 := by norm_num

theorem appendAFTime_leY : appendAFTime My Dc.N Dc.K ≤ 2 ^ 249 := by
  rw [rkN, rkK]
  unfold appendAFTime prefixTime moveAllowance appendAllowance
  norm_num

theorem rktPositiveCoeffCY (i : Fin (setting Dc).E.W) (b : Fin 64 → ℕ)
    (h : RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K b)) (hb : b rB1 = 1)
    (hz : b rZ ≤ Dc.N * Dc.K) (hx : b rZ ≤ b rQx) (hy : Dc.N * Dc.K ≤ b rQy) :
    Cert (MVM.compile (positiveCoeffC Dc i)) (layout My Dc.N Dc.K b)
      (layout My Dc.N Dc.K (positiveResult Dc My i b)) (2 ^ 316) := by
  classical
  let c := bhResult Dc My i.val b
  let d := Function.update c 0 (b 8)
  have bounds := bh_bounds_Dc i.val
  have hc := bhResult_inputs Dc My i.val b h (bounds.1.trans (by norm_num))
    (bounds.2.1.trans (by norm_num)) (bounds.2.2.1.trans (by norm_num))
    (bounds.2.2.2.trans (by norm_num))
  have hd := hc.update_layout 0 _ (by simpa using h.top (tR 8))
  have hs : d 4 + (2 * Dc.K) * (Dc.N * Dc.K) ≤ My := by
    have he : d 4 = 2 * ((bhIndices Dc).length * (Dc.N * Dc.K)) := by
      simpa only [d, Function.update_of_ne (by decide : (4 : Fin 64) ≠ 0)] using
        bhResult_length Dc My i.val b
    rw [he, rkNK, rkK]
    calc _ ≤ 2 * (2 ^ 66 * 2 ^ 40) + (2 * 2 ^ 16) * 2 ^ 40 := by gcongr; exact bounds.2.1
      _ ≤ My := by norm_num
  have p0 := (rktMpkBHC Dc My (2 ^ 66) i.val b h hb hz hx hy publicSizeInputs_Dc.source
    (by rw [rkNK]; norm_num) (bounds.2.1.trans (by norm_num))
    (bounds.2.2.1.trans (by norm_num)) (bounds.2.2.2.trans (by norm_num))).mono le_rfl le_rfl
      (bhT_leY i.val)
  have p1 := layout_copy_update My Dc.N Dc.K c hc.top 0 8
  have h8 : c 8 = b 8 := bhResult_other Dc My i.val b 8 (by decide)
  rw [h8] at p1
  have hbit : d rB1 = 1 := by
    simp only [d, Function.update_of_ne (by decide : rB1 ≠ 0)]
    exact (bhResult_other Dc My i.val b rB1 (by decide)).trans hb
  have p2 := (compile_appendAFC My Dc.N Dc.K (decide (i = (setting Dc).row0)) d hd hbit hs).mono
    le_rfl le_rfl appendAFTime_leY
  exact (p0.seq (p1.seq p2)).mono le_rfl le_rfl (by norm_num)

/-! ### One row -/

/-- The row scratch widened to the cap. -/
def PubCapsXY (b : Fin 64 → ℕ) : Prop := ∀ r ∈ publicScratch, b r = My

theorem pubRecoverXY (b c : Fin 64 → ℕ) (hc : PubCapsXY b)
    (ht : ∀ r, c r ≤ My) (hf : ∀ r, r ∉ publicScratch → c r = b r) : c ≤ b := by
  intro r
  by_cases hr : r ∈ publicScratch
  · rw [hc r hr]; exact ht r
  · exact (hf r hr).le

theorem positiveResult_sizeXY :
    2 * ((bhIndices Dc).length * (Dc.N * Dc.K)) + (2 * Dc.K) * (Dc.N * Dc.K) ≤ My :=
  positiveResult_size_Dc.trans (by norm_num)

theorem rktPositivePublicY (i : Fin (setting Dc).E.W) (b : Fin 64 → ℕ)
    (h : RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K b))
    (hc : PubCapsXY b) (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K) :
    Cert (MVM.compile (positiveCoeffC Dc i)) (layout My Dc.N Dc.K b)
      (layout My Dc.N Dc.K b) (2 ^ 316) := by
  have hx : b rZ ≤ b rQx := by rw [hc rQx (by decide)]; exact hz.trans (h.ring)
  have hy : Dc.N * Dc.K ≤ b rQy := by rw [hc rQy (by decide)]; exact h.ring
  have hs := bh_bounds_Dc i.val
  have hi := positiveResult_inputs Dc My i b h (hs.1.trans (by norm_num))
    (hs.2.1.trans (by norm_num)) (hs.2.2.1.trans (by norm_num)) positiveResult_sizeXY
  apply (rktPositiveCoeffCY i b h hb hz hx hy).mono le_rfl _ le_rfl
  apply layout_mono
  apply pubRecoverXY b _ hc (fun r ↦ by simpa using hi.top (tR r))
  intro r hr
  apply positiveResult_other
  intro hm; apply hr
  simp only [publicScratch, List.mem_cons] at hm ⊢
  tauto

theorem negT_leY : ringOneTime My Dc.N Dc.K + negativeCoeffTime My Dc.N Dc.K
    (Enum.list (α := Jh Dc)).length ≤ 2 ^ 348 := by
  have hh : (Enum.list (α := Jh Dc)).length = 44 := by
    rw [(public_input_lengths Dc).2.2.2.2]; norm_num [Dc, Params.bc]
  rw [hh, rkN, rkK]
  norm_num [ringOneTime, negativeCoeffTime, powersTime, powersBodyTime, repeatAppendTime,
    appendAllowance, operationBound]

theorem rktNegativePublicY (b : Fin 64 → ℕ)
    (h : RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K b))
    (hc : PubCapsXY b) (hb : b rB1 = 1) :
    Cert (MVM.compile (negativeReadyC Dc.N Dc.K (Enum.list (α := Jh Dc)).length))
      (layout My Dc.N Dc.K b) (layout My Dc.N Dc.K b) (2 ^ 348) := by
  have hh : (Enum.list (α := Jh Dc)).length = 44 := by
    rw [(public_input_lengths Dc).2.2.2.2]; norm_num [Dc, Params.bc]
  have h1 : 44 ≤ My := by norm_num
  have h2 : Dc.K * (Dc.N * Dc.K) + Dc.K * (Dc.N * Dc.K) ≤ My := by rw [rkNK, rkK]; norm_num
  have h3 : 44 * (Dc.K * (Dc.N * Dc.K) + Dc.K * (Dc.N * Dc.K)) ≤ My := by
    rw [rkNK, rkK]; norm_num
  rw [← hh] at h1 h3
  have hi := negativeReadyResult_inputs My Dc.N Dc.K _ b h h1 h2 h3
  apply (compile_negativeReadyC My Dc.N Dc.K _ b h hb (by rw [rkNK]; norm_num) h1 h2 h3).mono
    le_rfl _ negT_leY
  apply layout_mono
  apply pubRecoverXY b _ hc (fun r ↦ by simpa using hi.top (tR r))
  intro r hr
  apply negativeReadyResult_other <;> intro he <;> subst r <;> exact hr (by decide)

theorem gT_leY (n : ℕ) (hn : n ≤ 2 ^ 66) : gatherTime My Dc.N Dc.K (2 ^ 66) n ≤ 2 ^ 314 := by
  rw [rkN, rkK]
  unfold gatherTime gatherStepTime fetchTime moveAllowance appendAllowance
  calc _ ≤ 2 * (2 * 2 ^ 121 + 5) + 2 ^ 66 * ((32 * (2 ^ 66 * (2 ^ 24 * 2 ^ 16)) + 6) *
        (2 * 2 ^ 121 + 5) + 2 * ((2 * 2 ^ 121 + 3) * (20 + 10 * 2 ^ 121)) +
        (4 * 2 ^ 121 + 6) * (2 * 2 ^ 121 + 5)) := by gcongr
    _ ≤ 2 ^ 314 := by norm_num

theorem rktGatherPublicY (js : List ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K b))
    (hc : PubCapsXY b) (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K)
    (hj : ∀ j ∈ js, j ≤ 2 ^ 66) (hl : js.length ≤ 2 ^ 66) :
    Cert (MVM.compile (gatherC Dc.N Dc.K js)) (layout My Dc.N Dc.K b)
      (layout My Dc.N Dc.K b) (2 ^ 314) := by
  have hs : js.length * (Dc.N * Dc.K) ≤ My :=
    (Nat.mul_le_mul_right _ hl).trans (by rw [rkNK]; norm_num)
  have hp := compile_gatherC My Dc.N Dc.K (2 ^ 66) js b h hb hz
    (by rw [rkNK]; norm_num) hj hs
  have hi := (gatherBase_inputs My Dc.N Dc.K b h).update_layout 4 _ hs
  have hout : Function.update (gatherBase My b) 4 (js.length * (Dc.N * Dc.K)) ≤ b := by
    apply pubRecoverXY b _ hc (fun r ↦ by simpa using hi.top (tR r))
    intro r hr
    have hne (s : Fin 64) (hs : s ∈ publicScratch) : r ≠ s := fun he ↦ hr (he.symm ▸ hs)
    simp [gatherBase, Function.update_of_ne (hne 1 (by decide)),
      Function.update_of_ne (hne 2 (by decide)), Function.update_of_ne (hne 3 (by decide)),
      Function.update_of_ne (hne 4 (by decide))]
  exact hp.mono le_rfl (layout_mono _ _ _ hout) (gT_leY _ hl)

theorem rktSelGatherPublicY {α β : Type} [Enum α] [Enum β] [DecidableEq α]
    (f : β → α) (ha : (Enum.list (α := α)).length ≤ 2 ^ 66)
    (hβ : (Enum.list (α := β)).length ≤ 2 ^ 66) (b : Fin 64 → ℕ)
    (h : RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K b))
    (hc : PubCapsXY b) (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K) :
    Cert (MVM.compile (gatherC Dc.N Dc.K (Enum.list.map (Enum.index ∘ f))))
      (layout My Dc.N Dc.K b) (layout My Dc.N Dc.K b) (2 ^ 314) := by
  apply rktGatherPublicY _ b h hc hb hz
  · intro j hj
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hj
    exact (Enum.index_lt (f x)).le.trans ha
  · simpa only [List.length_map] using hβ

theorem rktPublicGathersY (i : Fin (setting Dc).E.W) (b : Fin 64 → ℕ)
    (h : RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K b))
    (hc : PubCapsXY b) (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K) :
    Cert (MVM.compile (positiveGatherC Dc i)) (layout My Dc.N Dc.K b)
      (layout My Dc.N Dc.K b) (2 ^ 314) ∧
    Cert (MVM.compile (negativeGatherC Dc i)) (layout My Dc.N Dc.K b)
      (layout My Dc.N Dc.K b) (2 ^ 314) := by
  let : DecidableEq (PIdx (Wb Dc) (Jh Dc) (setting Dc).τ (setting Dc).E.W) := Classical.decEq _
  exact ⟨rktSelGatherPublicY (positiveSelection Dc i) publicSizeInputs_Dc.candidate
    publicSizeInputs_Dc.positive b h hc hb hz,
    rktSelGatherPublicY (negativeSelection Dc i) publicSizeInputs_Dc.candidate
      publicSizeInputs_Dc.negative b h hc hb hz⟩

theorem sdT_leY : sdT My Dc.N Dc.K (2 ^ 66) ≤ 2 ^ 319 := by
  rw [rkN, rkK]
  norm_num [sdT, ipT, ipBT, mvT, operationBound]

theorem natT_leY (n : ℕ) (hn : n ≤ 2 ^ 66) : (32 * n + 4) * (2 * My + 5) ≤ 2 ^ 194 :=
  calc _ ≤ (32 * 2 ^ 66 + 4) * (2 * 2 ^ 121 + 5) := by gcongr
    _ ≤ 2 ^ 194 := by norm_num

/-- **One public row** (tight). -/
theorem rktPublicRowCY (i : Fin (setting Dc).E.W) (b : Fin 64 → ℕ)
    (h : RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K b))
    (hc : PubCapsXY b) (hb : b rB1 = 1) (hz : b rZ = Dc.N * Dc.K) :
    Cert (MVM.compile (publicRowC Dc i)) (layout My Dc.N Dc.K b)
      (layout My Dc.N Dc.K (Function.update b rIa (Dc.N * Dc.K))) (2 ^ 349) := by
  have cp (d s : Fin 64) (hd : d ∈ publicScratch) :
      Cert (MVM.compile (.cp d s)) (layout My Dc.N Dc.K b) (layout My Dc.N Dc.K b) (2 * My + 5) := by
    apply layout_copy _ _ _ b h.top
    rw [hc d hd]
    simpa using h.top (tR s)
  have p := rktPositivePublicY i b h hc hb hz.le
  have n := rktNegativePublicY b h hc hb
  obtain ⟨gp, gn⟩ := rktPublicGathersY i b h hc hb hz.le
  -- the counters, kept at `2^66`
  have hP := publicSizeInputs_Dc.positive
  have hN := publicSizeInputs_Dc.negative
  let b1 := Function.update b rQc (2 ^ 66)
  let b2 := Function.update b1 12 (2 ^ 66)
  have h1 : RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K b1) := h.update_layout _ _ (by norm_num)
  have h2 : RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K b2) := h1.update_layout _ _ (by norm_num)
  have nc := (layout_nat_update My Dc.N Dc.K b h rQc rB1 (by decide) _ hb
    (hP.trans (by norm_num))).mono le_rfl
      (layout_mono _ _ _ (show Function.update b rQc _ ≤ b1 from fun r => by
        by_cases hr : r = rQc
        · subst hr; simp only [b1, Function.update_self]; exact hP
        · simp [b1, Function.update_of_ne hr])) (natT_leY _ hP)
  have nn := (layout_nat_update My Dc.N Dc.K b1 h1 12 rB1 (by decide) _ (by simpa [b1] using hb)
    (hN.trans (by norm_num))).mono le_rfl
      (layout_mono _ _ _ (show Function.update b1 12 _ ≤ b2 from fun r => by
        by_cases hr : r = 12
        · subst hr; simp only [b2, Function.update_self]; exact hN
        · simp [b2, Function.update_of_ne hr])) (natT_leY _ hN)
  have k2 (r : Fin 64) (h1 : r ≠ rQc) (h2 : r ≠ 12) : b2 r = b r := by
    simp only [b2, b1, Function.update_of_ne h1, Function.update_of_ne h2]
  have qa : QueueArithmeticCaps Dc.N Dc.K b2 :=
    ⟨by rw [k2 _ (by decide) (by decide), hc rQx (by decide)]; exact h.ring,
      by rw [k2 _ (by decide) (by decide), hc rQy (by decide)]; exact h.ring,
      by rw [k2 _ (by decide) (by decide), hc rIa (by decide)]; exact h.ring,
      by rw [k2 _ (by decide) (by decide), k2 _ (by decide) (by decide), hc rQx (by decide), hz]
         exact h.ring,
      by rw [k2 _ (by decide) (by decide), k2 _ (by decide) (by decide), hc rQy (by decide), hz]
         exact h.ring⟩
  have sd := (rktSignedDotC My Dc.N Dc.K (2 ^ 66) b2 h2 qa
    (by rw [k2 _ (by decide) (by decide)]; exact hz) (by simp [b2, b1])
    (by rw [k2 _ (by decide) (by decide), hc 13 (by decide)]; exact h.ring)
    (by rw [k2 _ (by decide) (by decide), k2 _ (by decide) (by decide), hc 10 (by decide),
      hc rQa (by decide)])
    (by rw [k2 _ (by decide) (by decide), k2 _ (by decide) (by decide), hc 11 (by decide),
      hc rQb (by decide)])
    (by simp [b2, b1])).mono le_rfl (layout_mono _ _ _
      (show Function.update b2 rIa (Dc.N * Dc.K) ≤ Function.update b rIa (Dc.N * Dc.K) from fun r => by
      by_cases ha : r = rIa
      · subst ha; simp
      · rw [Function.update_of_ne ha, Function.update_of_ne ha]
        by_cases hr : r = rQc
        · subst hr
          rw [show b2 rQc = 2 ^ 66 by simp [b2, b1], hc rQc (by decide)]; norm_num
        by_cases hr' : r = 12
        · subst hr'
          rw [show b2 12 = 2 ^ 66 by simp [b2], hc 12 (by decide)]; norm_num
        exact (k2 r hr hr').le)) sdT_leY
  have all := (cp 0 14 (by decide)).seq
    ((p.seq (cp rQa 4 (by decide))).seq
    ((n.seq (cp 10 4 (by decide))).seq
    ((cp 0 9 (by decide)).seq
    ((gp.seq (cp rQb 4 (by decide))).seq
    ((gn.seq (cp 11 4 (by decide))).seq ((nc.seq nn).seq sd))))))
  simpa only [publicRowC, saveQueueC, rowCountsC, MVM.compile] using
    all.mono le_rfl le_rfl (show _ ≤ 2 ^ 349 by norm_num)


def pubStepTY : ℕ := 2 ^ 349 + appendAllowance My

theorem rktPublicStepY (q : Fin (setting Dc).E.W) (b : Fin 64 → ℕ)
    (h : RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ = Dc.N * Dc.K) (hw : PubCapsXY b)
    (hs : b 15 + Dc.N * Dc.K ≤ My) :
    Cert (MVM.compile (.seq (publicRowC Dc q) (.app 15 rIa)))
      (layout My Dc.N Dc.K b)
      (layout My Dc.N Dc.K (Function.update b 15 (b 15 + Dc.N * Dc.K))) pubStepTY := by
  let c := Function.update b rIa (Dc.N * Dc.K)
  have hi := h.update_layout rIa (Dc.N * Dc.K) h.ring
  have ho : c 15 = b 15 := by simp [c]
  have ha : c rIa = Dc.N * Dc.K := by simp [c]
  have p0 := rktPublicRowCY q b h hw hb hz
  have p1 := layout_append_uniform My Dc.N Dc.K c hi.top 15 rIa
    (by rw [ho, ha]; exact hs)
  have hl : c ≤ b := cap_update_le b rIa _ (by rw [hw rIa (by decide)]; exact h.ring)
  apply (p0.seq p1).mono le_rfl _ le_rfl
  apply layout_mono
  intro r
  by_cases hr : r = 15
  · subst r; simp only [Function.update_self, ho, ha]; exact le_rfl
  · simp only [Function.update_of_ne hr]; exact hl r

theorem rktPublicRowsAppendCY (qs : List (Fin (setting Dc).E.W)) (b : Fin 64 → ℕ)
    (h : RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ = Dc.N * Dc.K) (hw : PubCapsXY b)
    (hs : b 15 + qs.length * (Dc.N * Dc.K) ≤ My) :
    Cert (MVM.compile (publicRowsAppendC Dc qs)) (layout My Dc.N Dc.K b)
      (layout My Dc.N Dc.K (Function.update b 15 (b 15 + qs.length * (Dc.N * Dc.K))))
      (qs.length * pubStepTY + (2 * My + 5)) := by
  induction qs generalizing b with
  | nil =>
    simpa [publicRowsAppendC] using (compile_nop (layout My Dc.N Dc.K b)
      My h.top).mono le_rfl le_rfl (show 2 * (My + 1) + 3 ≤ 2 * My + 5 by omega)
  | cons q qs ih =>
    have hs0 : b 15 + Dc.N * Dc.K ≤ My := by
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hs; omega
    have p0 := rktPublicStepY q b h hb hz hw hs0
    let c := Function.update b 15 (b 15 + Dc.N * Dc.K)
    have hc := h.update_layout 15 _ hs0
    have p1 := ih c hc (by simpa [c] using hb) (by simpa [c] using hz)
      (by intro r hr
          have hn : r ≠ 15 := by intro he; subst r; norm_num [publicScratch] at hr
          simpa [c, Function.update_of_ne hn] using hw r hr)
      (by simp only [c, Function.update_self, List.length_cons, Nat.add_mul, Nat.one_mul] at *
          omega)
    have he : Function.update c 15 (c 15 + qs.length * (Dc.N * Dc.K)) =
        Function.update b 15 (b 15 + (q :: qs).length * (Dc.N * Dc.K)) := by
      simp only [c, Function.update_self, cap_reset, List.length_cons, Nat.add_mul, Nat.one_mul]
      congr 1; omega
    rw [he] at p1
    exact (p0.seq p1).seq_assoc.mono le_rfl le_rfl
      (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega)

/-- The output envelope of the public rows. -/
noncomputable def pubRowsXY (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (publicBase My b) 15 ((Enum.list (α := Fin (setting Dc).E.W)).length *
    (Dc.N * Dc.K))

theorem pubRowsLenY : (Enum.list (α := Fin (setting Dc).E.W)).length = 2 ^ 22 := by
  rw [len_fin, rkW]

/-- **The `2^22` public rows** (tight). -/
theorem rktPublicRowsCY (b : Fin 64 → ℕ)
    (h : RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ = Dc.N * Dc.K) :
    Cert (MVM.compile (publicRowsC Dc)) (layout My Dc.N Dc.K b)
      (layout My Dc.N Dc.K (pubRowsXY b)) (2 ^ 372) := by
  let qs := (Enum.list (α := Fin (setting Dc).E.W))
  have hs : qs.length * (Dc.N * Dc.K) ≤ My := by
    rw [pubRowsLenY, rkNK]; norm_num
  let c := publicBase My b
  have hc := publicBase_inputs My Dc.N Dc.K b h
  have p0 := layout_clear_update My Dc.N Dc.K c hc.top 15
  have p1 := rktPublicRowsAppendCY qs (Function.update c 15 0)
    (hc.update_layout 15 0 (by omega))
    (by simpa [c, publicBase, publicScratch] using hb)
    (by simpa [c, publicBase, publicScratch] using hz)
    (by intro r hr
        have hn : r ≠ 15 := by intro he; subst r; norm_num [publicScratch] at hr
        simp [Function.update_of_ne hn, c, publicBase, hr])
    (by simpa using hs)
  simp only [Function.update_self, zero_add, cap_reset] at p1
  have ht : (2 * My + 5) + (qs.length * pubStepTY + (2 * My + 5)) ≤ 2 ^ 372 := by
    rw [pubRowsLenY]; norm_num [pubStepTY, appendAllowance]
  exact (p0.seq p1).mono (layout_mono _ _ _ (le_publicBase _ _ _ b h)) le_rfl ht

/-! ### The digits tail (F3's generic certificate at `2^150`) -/

theorem decRowsT_varY (N K W : ℕ) (hN : N ≤ 2 ^ 24) (hK : K ≤ 2 ^ 16) (hW : W ≤ 2 ^ 22) :
    decomposeRowsTime My N K K W ≤ 2 ^ 370 := by
  calc _ ≤ decomposeRowsTime My (2 ^ 24) (2 ^ 16) (2 ^ 16) (2 ^ 22) := by
        unfold decomposeRowsTime decomposeRowTime digitQueueTime digitQueueBodyTime operationBound
        gcongr
    _ ≤ 2 ^ 370 := by
        unfold decomposeRowsTime decomposeRowTime digitQueueTime digitQueueBodyTime moveAllowance
          appendAllowance operationBound
        norm_num

theorem targetT_genY (o t : ℕ) (ho : o ≤ 2 ^ 120) (ht : t ≤ 2 ^ 62) :
    ((32 * o + 6) * (2 * My + 5) + 2 * moveAllowance My) + (2 * My + 5) +
      (32 * t + 4) * (2 * My + 5) + appendAllowance My ≤ 2 ^ 249 := by
  unfold moveAllowance appendAllowance
  calc _ ≤ ((32 * 2 ^ 120 + 6) * (2 * 2 ^ 121 + 5) + 2 * ((2 * 2 ^ 121 + 3) * (20 + 10 * 2 ^ 121))) +
        (2 * 2 ^ 121 + 5) + (32 * 2 ^ 62 + 4) * (2 * 2 ^ 121 + 5) +
        (4 * 2 ^ 121 + 6) * (2 * 2 ^ 121 + 5) := by gcongr
    _ ≤ 2 ^ 249 := by norm_num

theorem digitsTailT_genY (D : Dims) (hw : (setting D).E.W ≤ 2 ^ 22) (hk : D.K ≤ 2 ^ 16)
    (hn : D.N ≤ 2 ^ 24) (ho : mpkDOffset D ≤ 2 ^ 120) (hs : targetTailLength D ≤ 2 ^ 62) :
    digitsTailTime D My ≤ 2 ^ 371 := by
  have ht : targetTime D My ≤ 2 ^ 249 := targetT_genY _ _ ho hs
  have hd : decomposeRowsTime My D.N D.K D.K (setting D).E.W ≤ 2 ^ 370 :=
    decRowsT_varY _ _ _ hn hk hw
  unfold digitsTailTime
  calc _ ≤ 2 ^ 249 + ((2 * My + 5) + ((32 * 2 ^ 22 + 4) * (2 * My + 5) +
        ((32 * 2 ^ 16 + 4) * (2 * My + 5) + 2 ^ 370))) := by gcongr
    _ ≤ 2 ^ 371 := by norm_num

theorem digitsTailT_leY : digitsTailTime Dc My ≤ 2 ^ 371 := by
  have ho : mpkDOffset Dc ≤ 2 ^ 120 :=
    (Nat.sub_le (codecSize (mpkEnc Dc)) _).trans keyCodec_bounds_Dc.1
  have hs : targetTailLength Dc ≤ 2 ^ 62 := by
    unfold targetTailLength; rw [rkW, rkNK]
    calc _ ≤ 2 ^ 22 * 2 ^ 40 := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ ≤ 2 ^ 62 := by norm_num
  exact digitsTailT_genY Dc rkW.le rkK.le rkN.le ho hs

/-- **`keyDigitsC`** at the cap `2^150`. -/
theorem rktKeyDigitsCY (b : Fin 64 → ℕ)
    (h : RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ = Dc.N * Dc.K) :
    Cert (MVM.compile (keyDigitsC Dc)) (layout My Dc.N Dc.K b)
      (layout My Dc.N Dc.K (digitsTailResult Dc My (pubRowsXY b))) (2 ^ 373) := by
  have hp := rktPublicRowsCY b h hb hz
  have hpi : RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K (pubRowsXY b)) := by
    apply (publicBase_inputs _ _ _ b h).update_layout
    rw [pubRowsLenY, rkNK]; norm_num
  have ho : mpkDOffset Dc ≤ My :=
    ((Nat.sub_le (codecSize (mpkEnc Dc)) _).trans keyCodec_bounds_Dc.1).trans (by norm_num)
  have pt := (compile_digitsTailC Dc My (pubRowsXY b) hpi
    (by change b rB1 = 1; exact hb) (by change b rZ ≤ Dc.N * Dc.K; exact hz.le) ho
    (by unfold targetTailLength; rw [rkW, rkNK]; norm_num)
    (by rw [rkW]; norm_num) (by rw [rkNK, rkK]; norm_num)
    (by rw [rkW, rkNK, rkK]; norm_num)).mono le_rfl le_rfl digitsTailT_leY
  exact (hp.seq pt).mono le_rfl le_rfl (by norm_num)


/-! ### The standard envelope of the back end -/

/-- All registers at the cap `My`, except the templates `rB1`, `rZ`, the public key `14`, the
digits `17`, the corrected short part `18` and the key `19`. -/
def stdXY (v14 v17 v18 v19 : ℕ) (r : Fin 64) : ℕ :=
  if r = rB1 then 1 else if r = rZ then Dc.N * Dc.K else if r = 14 then v14 else
    if r = 17 then v17 else if r = 18 then v18 else if r = 19 then v19 else My

section
variable (v14 v17 v18 v19 : ℕ)
theorem stdX_rB1Y : stdXY v14 v17 v18 v19 rB1 = 1 := by simp [stdXY]
theorem stdX_rZY : stdXY v14 v17 v18 v19 rZ = Dc.N * Dc.K := by simp [stdXY]
theorem stdX_14Y : stdXY v14 v17 v18 v19 14 = v14 := by simp [stdXY]
theorem stdX_17Y : stdXY v14 v17 v18 v19 17 = v17 := by simp [stdXY]
theorem stdX_18Y : stdXY v14 v17 v18 v19 18 = v18 := by simp [stdXY]
theorem stdX_19Y : stdXY v14 v17 v18 v19 19 = v19 := by simp [stdXY]
theorem stdX_otherY (r : Fin 64) (h1 : r ≠ rB1) (h2 : r ≠ rZ) (h3 : r ≠ 14) (h5 : r ≠ 17)
    (h6 : r ≠ 18) (h4 : r ≠ 19) : stdXY v14 v17 v18 v19 r = My := by
  simp [stdXY, h1, h2, h3, h4, h5, h6]
end

theorem stdX_inputsY (v14 v17 v18 v19 : ℕ) (h14 : v14 ≤ My) (h17 : v17 ≤ My) (h18 : v18 ≤ My)
    (h19 : v19 ≤ My) : RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K (stdXY v14 v17 v18 v19)) := by
  have hNK : Dc.N * Dc.K ≤ My := by rw [rkNK]; norm_num
  apply layout_inputs
  · intro r; unfold stdXY; split_ifs
    · norm_num
    · exact hNK
    · exact h14
    · exact h17
    · exact h18
    · exact h19
    · exact le_rfl
  · exact hNK
  · rw [rkN]; norm_num
  · rw [rkK]; norm_num

theorem le_stdXY (v14 v17 v18 v19 : ℕ) (c : Fin 64 → ℕ) (hc : ∀ r, c r ≤ My) (h1 : c rB1 ≤ 1)
    (hz : c rZ ≤ Dc.N * Dc.K) (h14 : c 14 ≤ v14) (h17 : c 17 ≤ v17) (h18 : c 18 ≤ v18)
    (h19 : c 19 ≤ v19) : c ≤ stdXY v14 v17 v18 v19 := by
  intro r
  unfold stdXY
  split_ifs with a1 a2 a3 a5 a6 a4
  · subst a1; exact h1
  · subst a2; exact hz
  · subst a3; exact h14
  · subst a5; exact h17
  · subst a6; exact h18
  · subst a4; exact h19
  · exact hc r


def asmXY (NK L : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (gatherBase My (Function.update b 0 (b 18 + b 17)))
    4 (L * NK)) 19 (L * NK)

/-- The assembly words, generic in the dimensions and the index list. -/
theorem rktAssembleWordsY (N K : ℕ) (js : List ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs My N K (layout My N K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ N * K) (hs : b 18 + b 17 ≤ My)
    (hj : ∀ j ∈ js, j ≤ 2 ^ 66) (hl : js.length ≤ 2 ^ 66) (hNK : N * K = 2 ^ 40)
    (hg : gatherTime My N K (2 ^ 66) js.length ≤ 2 ^ 314) :
    Cert (MVM.compile (.seq (.cp 0 18) (.seq (.app 0 17)
      (saveQueueC (gatherC N K js) 19)))) (layout My N K b)
      (layout My N K (asmXY (N * K) js.length b)) (2 ^ 315) := by
  let c := Function.update b 0 (b 18)
  have hc := h.update_layout 0 (b 18) (by simpa using h.top (tR 18))
  have p0 := layout_copy_update My N K b h.top 0 18
  have p1 := layout_append_uniform My N K c hc.top 0 17 (by simpa [c] using hs)
  have he : Function.update c 0 (c 0 + c 17) = Function.update b 0 (b 18 + b 17) := by simp [c]
  rw [he] at p1
  have ha : RingInputs My N K (layout My N K (Function.update b 0 (b 18 + b 17))) :=
    h.update_layout 0 _ hs
  have hlen : js.length * (N * K) ≤ My :=
    (Nat.mul_le_mul_right _ hl).trans (by rw [hNK]; norm_num)
  have p2 := compile_gatherC My N K (2 ^ 66) js _ ha (by simpa using hb) (by simpa using hz)
    (by rw [hNK]; norm_num) hj hlen
  have hgi := (gatherBase_inputs _ _ _ _ ha).update_layout 4 _ hlen
  have p3 := layout_copy_update My N K _ hgi.top 19 4
  simp only [Function.update_self] at p3
  have all := p0.seq (p1.seq ((p2.mono le_rfl le_rfl hg).seq p3))
  have hnum : 2 * My + 5 + (appendAllowance My + (2 ^ 314 + (2 * My + 5))) ≤ (2 : ℕ) ^ 315 := by
    norm_num [appendAllowance]
  exact all.mono le_rfl le_rfl hnum

theorem rktAssembleCY (b : Fin 64 → ℕ) (h : RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K) (hs : b 18 + b 17 ≤ My) :
    Cert (MVM.compile (assembleC Dc)) (layout My Dc.N Dc.K b)
      (layout My Dc.N Dc.K (asmXY (Dc.N * Dc.K) (assemblyIndices Dc).length b)) (2 ^ 315) := by
  rw [assembleC_eq]
  exact rktAssembleWordsY Dc.N Dc.K (assemblyIndices Dc) b h hb hz hs assemblyIndices_bounds.1
    assemblyIndices_bounds.2 rkNK (gT_leY _ assemblyIndices_bounds.2)


theorem decQT_varY (N K Q : ℕ) (hN : N ≤ 2 ^ 24) (hK : K ≤ 2 ^ 16) (hQ : Q ≤ 2 ^ 66) :
    decQT My N K N Q ≤ 2 ^ 338 := by
  calc _ ≤ decQT My (2 ^ 24) (2 ^ 16) (2 ^ 24) (2 ^ 66) := by
        unfold decQT decQBT RedKeyT.decT operationBound
        gcongr
    _ ≤ 2 ^ 338 := by
        unfold decQT decQBT RedKeyT.decT decodeBodyTime moveAllowance appendAllowance operationBound
        norm_num

theorem candT_varY (N K tw Q : ℕ) (htw : tw ≤ 32 * 2 ^ 120 + 1)
    (hQ : decQT My N K N Q ≤ 2 ^ 338) :
    (5 + tw) * (2 * My + 5) + (decQT My N K N Q + (2 * My + 5)) ≤ 2 ^ 339 := by
  calc _ ≤ (5 + (32 * 2 ^ 120 + 1)) * (2 * My + 5) + (2 ^ 338 + (2 * My + 5)) := by gcongr
    _ ≤ 2 ^ 339 := by norm_num

theorem candT_genY (D : Dims) (B : ℕ)
    (hw : ((candidateInitOps D B).map (fun op ↦ op.2.weightBound)).sum ≤ 2 ^ 120)
    (hN : D.N ≤ 2 ^ 24) (hK : D.K ≤ 2 ^ 16) (hQ : nPI D ≤ 2 ^ 66) : candT D B My ≤ 2 ^ 339 := by
  have htw := (templateTimeWeight_le (candidateInitOps D B)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 32 hw) 1)
  exact candT_varY D.N D.K _ _ htw (decQT_varY D.N D.K (nPI D) hN hK hQ)

theorem candT_leY : candT Dc Params.Bk My ≤ 2 ^ 339 :=
  candT_genY Dc Params.Bk candidateInitWeight_Dc rkN.le rkK.le correction_counts_Dc.2.2

theorem boxFT_varY (N K R L : ℕ) (hN : N ≤ 2 ^ 24) (hK : K ≤ 2 ^ 16) (hR : R ≤ 2 ^ 16)
    (hL : L ≤ 2 ^ 66) : boxFT My N K K R L ≤ 2 ^ 334 := by
  calc _ ≤ boxFT My (2 ^ 24) (2 ^ 16) (2 ^ 16) (2 ^ 16) (2 ^ 66) := by
        unfold boxFT boxBT tstT tstLT tstBT mvT operationBound
        gcongr
    _ ≤ 2 ^ 334 := by
        unfold boxFT boxBT tstT tstLT tstBT mvT operationBound
        norm_num

theorem acceptInitT_varY (N K B P : ℕ) (hN : N ≤ 2 ^ 24) (hK : K ≤ 2 ^ 16) (hB : B ≤ 2 ^ 16)
    (hKB : K - B ≤ 2 ^ 16) (hP : P ≤ 2 ^ 66) :
    (10 * K + 32 * N + 14) * (2 * My + 5) + repeatAppendTime My N + ((32 * B + 4) * (2 * My + 5) +
      ((32 * (K - B) + 4) * (2 * My + 5) + ((2 * My + 5) + (32 * P + 4) * (2 * My + 5)))) ≤
      2 ^ 270 := by
  calc _ ≤ (10 * 2 ^ 16 + 32 * 2 ^ 24 + 14) * (2 * My + 5) + repeatAppendTime My (2 ^ 24) +
        ((32 * 2 ^ 16 + 4) * (2 * My + 5) + ((32 * 2 ^ 16 + 4) * (2 * My + 5) +
          ((2 * My + 5) + (32 * 2 ^ 66 + 4) * (2 * My + 5)))) := by
        unfold repeatAppendTime
        gcongr
    _ ≤ 2 ^ 270 := by
        unfold repeatAppendTime appendAllowance
        norm_num

theorem accT_genY (D : Dims) (B : ℕ) (hN : D.N ≤ 2 ^ 24) (hK : D.K ≤ 2 ^ 16) (hB : B ≤ 2 ^ 16)
    (hP : (Enum.list (α := PIdxD D)).length ≤ 2 ^ 66) (hk : codecSize (keyEnc D) ≤ 2 ^ 120) :
    accT D My B (2 ^ 66) ≤ 2 ^ 335 := by
  have hKB : D.K - B ≤ 2 ^ 16 := (Nat.sub_le _ _).trans hK
  have h1 := acceptInitT_varY D.N D.K B (Enum.list (α := PIdxD D)).length hN hK hB hKB hP
  have h2 := boxFT_varY D.N D.K (D.K - B) (2 ^ 66) hN hK hKB le_rfl
  have h3 : max (2 * (My + 1) + 3) ((32 * codecSize (keyEnc D) + 4) * (2 * My + 5)) ≤ 2 ^ 248 := by
    apply max_le (by norm_num)
    exact le_trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.mul_le_mul_left 32 hk) 4))
      (by norm_num)
  have hnum : (2 : ℕ) ^ 270 + (2 ^ 334 + (2 ^ 248 + 1)) ≤ 2 ^ 335 := by norm_num
  exact le_trans (Nat.add_le_add h1 (Nat.add_le_add h2 (Nat.add_le_add_right h3 1))) hnum

theorem accT_leY : accT Dc My Params.Bk (2 ^ 66) ≤ 2 ^ 335 :=
  accT_genY Dc Params.Bk rkN.le rkK.le (by rw [← rkK]; exact Params.Bk_lt_Kc.le)
    correction_counts_Dc.2.2 keyCodec_bounds_Dc.2.2


set_option exponentiation.threshold 1000 in
theorem rktCoinTimeY (n : ℕ) (hn : n ≤ 2 ^ 106) :
    (2 * (2 ^ 121 + 1) + 3) + (bCoins n).T 0 (2 ^ 121) ≤ 2 ^ 236 := by
  change (2 * (2 ^ 121 + 1) + 3) + XProg.countT n 1 0 tCoin 0 (2 ^ 121) ≤ _
  unfold XProg.countT tCoin
  calc
    _ ≤ (2 * (2 ^ 121 + 1) + 3) +
        ((2 * 2 ^ 106 + 1) * (4 * (0 + 2 ^ 121) + 12) +
          (2 * (0 + 2 ^ 121) + 3) +
          (2 ^ 106 * (2 * (0 + 2 ^ 106 * 1 + (2 ^ 121 + 2 ^ 106 * 0)) + 3 +
            (6 * (0 + 2 ^ 106 * 1 + (2 ^ 121 + 2 ^ 106 * 0)) + 16) + 1) + 2) +
          (2 * (0 + 2 ^ 106 * 1 + (2 ^ 121 + 2 ^ 106 * 0)) + 3)) := by gcongr
    _ ≤ 2 ^ 236 := by norm_num


theorem le_MxY {n k : ℕ} (h : n ≤ 2 ^ k) (hk : k ≤ 121) : n ≤ My :=
  h.trans (Nat.pow_le_pow_right (by norm_num) hk)

theorem nPIq_genY (Q x : ℕ) (hQ : Q ≤ 2 ^ 66) (hx : x = 2 ^ 40) : Q * x ≤ My := by
  subst hx; calc Q * 2 ^ 40 ≤ 2 ^ 66 * 2 ^ 40 := Nat.mul_le_mul_right _ hQ
    _ ≤ My := by norm_num

theorem nPIqY : nPI Dc * (Dc.N * Dc.K) ≤ My := nPIq_genY _ _ correction_counts_Dc.2.2 rkNK

theorem asmX_keepY (NK L : ℕ) (b : Fin 64 → ℕ) :
    asmXY NK L b rB1 = b rB1 ∧ asmXY NK L b rZ = b rZ ∧ asmXY NK L b 14 = b 14 ∧
    asmXY NK L b 19 = L * NK := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [asmXY, gatherBase, Function.update_apply]


end AdvancedEncryption.ExpLUT.Prog.KeyTightY
