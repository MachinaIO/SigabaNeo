import PE.Impl.ExpLUT.Prog.RedKeyTMv
/-!
# Module 9: the public rows of `keyDigitsC` at the tape cap `2^150` (tight)

F3's `KeyTimePublicKernels` at the cap `Mx = 2^150`, with the queue automorphisms
(`rktGatherAutC`) and the signed inner products (`rktSignedDotC`) charged tightly, and the row
counters `rQc`, `12` kept at `2^66` (F3 widens them to the cap). The scratch of a row is widened
to the cap (`PubCapsX`).

* `rktPublicRowC`: one row, `layout b → layout (update b rIa (N K))`, `≤ 2^407` steps;
* **`rktPublicRowsC`**: all `2^22` rows, `15 := 2^22 · N K`, `≤ 2^430` steps.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 1000
set_option maxRecDepth 100000

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyT

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Prog.KeyTime

/-- The tape cap of the back end. -/
abbrev Mx : ℕ := 2 ^ 150

theorem rkN : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
theorem rkK : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
theorem rkW : (setting Dc).E.W = 2 ^ 22 := by change 2 ^ Dc.b = _; norm_num [Dc, Params.bc]
theorem rkNK : Dc.N * Dc.K = 2 ^ 40 := by rw [rkN, rkK]; norm_num

/-! ### `mpkBHC` and the positive coefficients (tight automorphisms) -/

noncomputable def bhT (D : Dims) (M I i : ℕ) : ℕ :=
  prefixTime M (bhPrefixLength D) +
    (gatherTime M D.N D.K I (bhIndices D).length + autGT M D.N D.K (bhIndices D).length
      (rowExponent D i))

theorem rktMpkBHC (D : Dims) (M I i : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b)) (hb : b rB1 = 1)
    (hz : b rZ ≤ D.N * D.K) (hx : b rZ ≤ b rQx) (hy : D.N * D.K ≤ b rQy)
    (hsrc : (Enum.list (α := BHSource D)).length ≤ I)
    (hi : I * (D.N * D.K) ≤ M) (hn : (bhIndices D).length ≤ M)
    (hk : rowExponent D i ≤ M) (hs : 2 * ((bhIndices D).length * (D.N * D.K)) ≤ M) :
    Cert (MVM.compile (mpkBHC D i)) (layout M D.N D.K b)
      (layout M D.N D.K (bhResult D M i b)) (bhT D M I i) := by
  have hpref : bhPrefixLength D ≤ M := (Nat.mul_le_mul_right (D.N * D.K) hsrc).trans hi
  let c := prefixResult (bhPrefixLength D) b
  have hc := prefixResult_inputs M D.N D.K _ b h hpref
  have p0 := compile_prefixC M D.N D.K _ b h hb hpref
  have p1 := rktGatherAutC M D.N D.K I (rowExponent D i) (bhIndices D) c hc
    (by simpa [c, prefixResult] using hb) (by simpa [c, prefixResult] using hz)
    (by simpa [c, prefixResult] using hx) (by simpa [c, prefixResult] using hy)
    hi (bhIndices_bound D I hsrc) hn hk hs
  exact p0.seq p1

noncomputable def posT : ℕ :=
  bhT Dc Mx (2 ^ 66) 0 + ((2 * Mx + 5) + appendAFTime Mx Dc.N Dc.K)

theorem prefixT_le (n : ℕ) (hn : n ≤ 2 ^ 120) : prefixTime Mx n ≤ 2 ^ 306 := by
  unfold prefixTime moveAllowance
  calc _ ≤ (32 * 2 ^ 120 + 6) * (2 * 2 ^ 150 + 5) + (2 * 2 ^ 150 + 3) * (20 + 10 * 2 ^ 150) := by
        gcongr
    _ ≤ 2 ^ 306 := by norm_num

theorem gatherT_le (n : ℕ) (hn : n ≤ 2 ^ 66) :
    gatherTime Mx (2 ^ 24) (2 ^ 16) (2 ^ 66) n ≤ 2 ^ 372 := by
  unfold gatherTime gatherStepTime fetchTime moveAllowance appendAllowance
  calc _ ≤ 2 * (2 * 2 ^ 150 + 5) + 2 ^ 66 * ((32 * (2 ^ 66 * (2 ^ 24 * 2 ^ 16)) + 6) *
        (2 * 2 ^ 150 + 5) + 2 * ((2 * 2 ^ 150 + 3) * (20 + 10 * 2 ^ 150)) +
        (4 * 2 ^ 150 + 6) * (2 * 2 ^ 150 + 5)) := by gcongr
    _ ≤ 2 ^ 372 := by norm_num

theorem autGT_le (n k : ℕ) (hn : n ≤ 2 ^ 66) (hk : k ≤ 2 ^ 25) :
    autGT Mx (2 ^ 24) (2 ^ 16) n k ≤ 2 ^ 371 := by
  unfold autGT autQT autBT mvT appendAllowance operationBound
  calc _ ≤ (32 * 2 ^ 66 + 32 * 2 ^ 25 + 10) * (2 * 2 ^ 150 + 5) + (2 ^ 66 * (2 * 2 ^ 150 +
        ((2 * 2 ^ 150 + 5) + (2 * 2 ^ 150 + 3) * (20 + 10 * (2 ^ 24 * 2 ^ 16)) +
          1000 * (2 ^ 150 + 1) * (2 ^ 24 + 1) ^ 2 * (2 ^ 16 + 1) ^ 2 * (2 ^ 25 + 1) +
          (4 * 2 ^ 150 + 6) * (2 * 2 ^ 150 + 5)) + 4) + 2) := by gcongr
    _ ≤ 2 ^ 371 := by norm_num

theorem bhT_le (i : ℕ) : bhT Dc Mx (2 ^ 66) i ≤ 2 ^ 373 := by
  have hb := bh_bounds_Dc i
  have h1 := prefixT_le _ hb.1
  have h2 := gatherT_le _ hb.2.1
  have h3 := autGT_le _ _ hb.2.1 hb.2.2.1
  unfold bhT
  rw [rkN, rkK]
  calc _ ≤ 2 ^ 306 + (2 ^ 372 + 2 ^ 371) := Nat.add_le_add h1 (Nat.add_le_add h2 h3)
    _ ≤ 2 ^ 373 := by norm_num

theorem appendAFTime_le : appendAFTime Mx Dc.N Dc.K ≤ 2 ^ 306 := by
  rw [rkN, rkK]
  unfold appendAFTime prefixTime moveAllowance appendAllowance
  norm_num

theorem rktPositiveCoeffC (i : Fin (setting Dc).E.W) (b : Fin 64 → ℕ)
    (h : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b)) (hb : b rB1 = 1)
    (hz : b rZ ≤ Dc.N * Dc.K) (hx : b rZ ≤ b rQx) (hy : Dc.N * Dc.K ≤ b rQy) :
    Cert (MVM.compile (positiveCoeffC Dc i)) (layout Mx Dc.N Dc.K b)
      (layout Mx Dc.N Dc.K (positiveResult Dc Mx i b)) (2 ^ 374) := by
  classical
  let c := bhResult Dc Mx i.val b
  let d := Function.update c 0 (b 8)
  have bounds := bh_bounds_Dc i.val
  have hc := bhResult_inputs Dc Mx i.val b h (bounds.1.trans (by norm_num))
    (bounds.2.1.trans (by norm_num)) (bounds.2.2.1.trans (by norm_num))
    (bounds.2.2.2.trans (by norm_num))
  have hd := hc.update_layout 0 _ (by simpa using h.top (tR 8))
  have hs : d 4 + (2 * Dc.K) * (Dc.N * Dc.K) ≤ Mx := by
    have he : d 4 = 2 * ((bhIndices Dc).length * (Dc.N * Dc.K)) := by
      simpa only [d, Function.update_of_ne (by decide : (4 : Fin 64) ≠ 0)] using
        bhResult_length Dc Mx i.val b
    rw [he, rkNK, rkK]
    calc _ ≤ 2 * (2 ^ 66 * 2 ^ 40) + (2 * 2 ^ 16) * 2 ^ 40 := by gcongr; exact bounds.2.1
      _ ≤ Mx := by norm_num
  have p0 := (rktMpkBHC Dc Mx (2 ^ 66) i.val b h hb hz hx hy publicSizeInputs_Dc.source
    (by rw [rkNK]; norm_num) (bounds.2.1.trans (by norm_num))
    (bounds.2.2.1.trans (by norm_num)) (bounds.2.2.2.trans (by norm_num))).mono le_rfl le_rfl
      (bhT_le i.val)
  have p1 := layout_copy_update Mx Dc.N Dc.K c hc.top 0 8
  have h8 : c 8 = b 8 := bhResult_other Dc Mx i.val b 8 (by decide)
  rw [h8] at p1
  have hbit : d rB1 = 1 := by
    simp only [d, Function.update_of_ne (by decide : rB1 ≠ 0)]
    exact (bhResult_other Dc Mx i.val b rB1 (by decide)).trans hb
  have p2 := (compile_appendAFC Mx Dc.N Dc.K (decide (i = (setting Dc).row0)) d hd hbit hs).mono
    le_rfl le_rfl appendAFTime_le
  exact (p0.seq (p1.seq p2)).mono le_rfl le_rfl (by norm_num)

/-! ### One row -/

/-- The row scratch widened to the cap. -/
def PubCapsX (b : Fin 64 → ℕ) : Prop := ∀ r ∈ publicScratch, b r = Mx

theorem pubRecoverX (b c : Fin 64 → ℕ) (hc : PubCapsX b)
    (ht : ∀ r, c r ≤ Mx) (hf : ∀ r, r ∉ publicScratch → c r = b r) : c ≤ b := by
  intro r
  by_cases hr : r ∈ publicScratch
  · rw [hc r hr]; exact ht r
  · exact (hf r hr).le

theorem positiveResult_sizeX :
    2 * ((bhIndices Dc).length * (Dc.N * Dc.K)) + (2 * Dc.K) * (Dc.N * Dc.K) ≤ Mx :=
  positiveResult_size_Dc.trans (by norm_num)

theorem rktPositivePublic (i : Fin (setting Dc).E.W) (b : Fin 64 → ℕ)
    (h : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b))
    (hc : PubCapsX b) (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K) :
    Cert (MVM.compile (positiveCoeffC Dc i)) (layout Mx Dc.N Dc.K b)
      (layout Mx Dc.N Dc.K b) (2 ^ 374) := by
  have hx : b rZ ≤ b rQx := by rw [hc rQx (by decide)]; exact hz.trans (h.ring)
  have hy : Dc.N * Dc.K ≤ b rQy := by rw [hc rQy (by decide)]; exact h.ring
  have hs := bh_bounds_Dc i.val
  have hi := positiveResult_inputs Dc Mx i b h (hs.1.trans (by norm_num))
    (hs.2.1.trans (by norm_num)) (hs.2.2.1.trans (by norm_num)) positiveResult_sizeX
  apply (rktPositiveCoeffC i b h hb hz hx hy).mono le_rfl _ le_rfl
  apply layout_mono
  apply pubRecoverX b _ hc (fun r ↦ by simpa using hi.top (tR r))
  intro r hr
  apply positiveResult_other
  intro hm; apply hr
  simp only [publicScratch, List.mem_cons] at hm ⊢
  tauto

theorem negT_le : ringOneTime Mx Dc.N Dc.K + negativeCoeffTime Mx Dc.N Dc.K
    (Enum.list (α := Jh Dc)).length ≤ 2 ^ 407 := by
  have hh : (Enum.list (α := Jh Dc)).length = 44 := by
    rw [(public_input_lengths Dc).2.2.2.2]; norm_num [Dc, Params.bc]
  rw [hh, rkN, rkK]
  norm_num [ringOneTime, negativeCoeffTime, powersTime, powersBodyTime, repeatAppendTime,
    appendAllowance, operationBound]

theorem rktNegativePublic (b : Fin 64 → ℕ)
    (h : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b))
    (hc : PubCapsX b) (hb : b rB1 = 1) :
    Cert (MVM.compile (negativeReadyC Dc.N Dc.K (Enum.list (α := Jh Dc)).length))
      (layout Mx Dc.N Dc.K b) (layout Mx Dc.N Dc.K b) (2 ^ 407) := by
  have hh : (Enum.list (α := Jh Dc)).length = 44 := by
    rw [(public_input_lengths Dc).2.2.2.2]; norm_num [Dc, Params.bc]
  have h1 : 44 ≤ Mx := by norm_num
  have h2 : Dc.K * (Dc.N * Dc.K) + Dc.K * (Dc.N * Dc.K) ≤ Mx := by rw [rkNK, rkK]; norm_num
  have h3 : 44 * (Dc.K * (Dc.N * Dc.K) + Dc.K * (Dc.N * Dc.K)) ≤ Mx := by
    rw [rkNK, rkK]; norm_num
  rw [← hh] at h1 h3
  have hi := negativeReadyResult_inputs Mx Dc.N Dc.K _ b h h1 h2 h3
  apply (compile_negativeReadyC Mx Dc.N Dc.K _ b h hb (by rw [rkNK]; norm_num) h1 h2 h3).mono
    le_rfl _ negT_le
  apply layout_mono
  apply pubRecoverX b _ hc (fun r ↦ by simpa using hi.top (tR r))
  intro r hr
  apply negativeReadyResult_other <;> intro he <;> subst r <;> exact hr (by decide)

theorem gT_le (n : ℕ) (hn : n ≤ 2 ^ 66) : gatherTime Mx Dc.N Dc.K (2 ^ 66) n ≤ 2 ^ 372 := by
  rw [rkN, rkK]
  unfold gatherTime gatherStepTime fetchTime moveAllowance appendAllowance
  calc _ ≤ 2 * (2 * 2 ^ 150 + 5) + 2 ^ 66 * ((32 * (2 ^ 66 * (2 ^ 24 * 2 ^ 16)) + 6) *
        (2 * 2 ^ 150 + 5) + 2 * ((2 * 2 ^ 150 + 3) * (20 + 10 * 2 ^ 150)) +
        (4 * 2 ^ 150 + 6) * (2 * 2 ^ 150 + 5)) := by gcongr
    _ ≤ 2 ^ 372 := by norm_num

theorem rktGatherPublic (js : List ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b))
    (hc : PubCapsX b) (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K)
    (hj : ∀ j ∈ js, j ≤ 2 ^ 66) (hl : js.length ≤ 2 ^ 66) :
    Cert (MVM.compile (gatherC Dc.N Dc.K js)) (layout Mx Dc.N Dc.K b)
      (layout Mx Dc.N Dc.K b) (2 ^ 372) := by
  have hs : js.length * (Dc.N * Dc.K) ≤ Mx :=
    (Nat.mul_le_mul_right _ hl).trans (by rw [rkNK]; norm_num)
  have hp := compile_gatherC Mx Dc.N Dc.K (2 ^ 66) js b h hb hz
    (by rw [rkNK]; norm_num) hj hs
  have hi := (gatherBase_inputs Mx Dc.N Dc.K b h).update_layout 4 _ hs
  have hout : Function.update (gatherBase Mx b) 4 (js.length * (Dc.N * Dc.K)) ≤ b := by
    apply pubRecoverX b _ hc (fun r ↦ by simpa using hi.top (tR r))
    intro r hr
    have hne (s : Fin 64) (hs : s ∈ publicScratch) : r ≠ s := fun he ↦ hr (he.symm ▸ hs)
    simp [gatherBase, Function.update_of_ne (hne 1 (by decide)),
      Function.update_of_ne (hne 2 (by decide)), Function.update_of_ne (hne 3 (by decide)),
      Function.update_of_ne (hne 4 (by decide))]
  exact hp.mono le_rfl (layout_mono _ _ _ hout) (gT_le _ hl)

theorem rktSelGatherPublic {α β : Type} [Enum α] [Enum β] [DecidableEq α]
    (f : β → α) (ha : (Enum.list (α := α)).length ≤ 2 ^ 66)
    (hβ : (Enum.list (α := β)).length ≤ 2 ^ 66) (b : Fin 64 → ℕ)
    (h : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b))
    (hc : PubCapsX b) (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K) :
    Cert (MVM.compile (gatherC Dc.N Dc.K (Enum.list.map (Enum.index ∘ f))))
      (layout Mx Dc.N Dc.K b) (layout Mx Dc.N Dc.K b) (2 ^ 372) := by
  apply rktGatherPublic _ b h hc hb hz
  · intro j hj
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hj
    exact (Enum.index_lt (f x)).le.trans ha
  · simpa only [List.length_map] using hβ

theorem rktPublicGathers (i : Fin (setting Dc).E.W) (b : Fin 64 → ℕ)
    (h : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b))
    (hc : PubCapsX b) (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K) :
    Cert (MVM.compile (positiveGatherC Dc i)) (layout Mx Dc.N Dc.K b)
      (layout Mx Dc.N Dc.K b) (2 ^ 372) ∧
    Cert (MVM.compile (negativeGatherC Dc i)) (layout Mx Dc.N Dc.K b)
      (layout Mx Dc.N Dc.K b) (2 ^ 372) := by
  let : DecidableEq (PIdx (Wb Dc) (Jh Dc) (setting Dc).τ (setting Dc).E.W) := Classical.decEq _
  exact ⟨rktSelGatherPublic (positiveSelection Dc i) publicSizeInputs_Dc.candidate
    publicSizeInputs_Dc.positive b h hc hb hz,
    rktSelGatherPublic (negativeSelection Dc i) publicSizeInputs_Dc.candidate
      publicSizeInputs_Dc.negative b h hc hb hz⟩

theorem sdT_le : sdT Mx Dc.N Dc.K (2 ^ 66) ≤ 2 ^ 350 := by
  rw [rkN, rkK]
  norm_num [sdT, ipT, ipBT, mvT, operationBound]

theorem natT_le (n : ℕ) (hn : n ≤ 2 ^ 66) : (32 * n + 4) * (2 * Mx + 5) ≤ 2 ^ 225 :=
  calc _ ≤ (32 * 2 ^ 66 + 4) * (2 * 2 ^ 150 + 5) := by gcongr
    _ ≤ 2 ^ 225 := by norm_num

/-- **One public row** (tight). -/
theorem rktPublicRowC (i : Fin (setting Dc).E.W) (b : Fin 64 → ℕ)
    (h : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b))
    (hc : PubCapsX b) (hb : b rB1 = 1) (hz : b rZ = Dc.N * Dc.K) :
    Cert (MVM.compile (publicRowC Dc i)) (layout Mx Dc.N Dc.K b)
      (layout Mx Dc.N Dc.K (Function.update b rIa (Dc.N * Dc.K))) (2 ^ 409) := by
  have cp (d s : Fin 64) (hd : d ∈ publicScratch) :
      Cert (MVM.compile (.cp d s)) (layout Mx Dc.N Dc.K b) (layout Mx Dc.N Dc.K b) (2 * Mx + 5) := by
    apply layout_copy _ _ _ b h.top
    rw [hc d hd]
    simpa using h.top (tR s)
  have p := rktPositivePublic i b h hc hb hz.le
  have n := rktNegativePublic b h hc hb
  obtain ⟨gp, gn⟩ := rktPublicGathers i b h hc hb hz.le
  -- the counters, kept at `2^66`
  have hP := publicSizeInputs_Dc.positive
  have hN := publicSizeInputs_Dc.negative
  let b1 := Function.update b rQc (2 ^ 66)
  let b2 := Function.update b1 12 (2 ^ 66)
  have h1 : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b1) := h.update_layout _ _ (by norm_num)
  have h2 : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b2) := h1.update_layout _ _ (by norm_num)
  have nc := (layout_nat_update Mx Dc.N Dc.K b h rQc rB1 (by decide) _ hb
    (hP.trans (by norm_num))).mono le_rfl
      (layout_mono _ _ _ (show Function.update b rQc _ ≤ b1 from fun r => by
        by_cases hr : r = rQc
        · subst hr; simp only [b1, Function.update_self]; exact hP
        · simp [b1, Function.update_of_ne hr])) (natT_le _ hP)
  have nn := (layout_nat_update Mx Dc.N Dc.K b1 h1 12 rB1 (by decide) _ (by simpa [b1] using hb)
    (hN.trans (by norm_num))).mono le_rfl
      (layout_mono _ _ _ (show Function.update b1 12 _ ≤ b2 from fun r => by
        by_cases hr : r = 12
        · subst hr; simp only [b2, Function.update_self]; exact hN
        · simp [b2, Function.update_of_ne hr])) (natT_le _ hN)
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
  have sd := (rktSignedDotC Mx Dc.N Dc.K (2 ^ 66) b2 h2 qa
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
        exact (k2 r hr hr').le)) sdT_le
  have all := (cp 0 14 (by decide)).seq
    ((p.seq (cp rQa 4 (by decide))).seq
    ((n.seq (cp 10 4 (by decide))).seq
    ((cp 0 9 (by decide)).seq
    ((gp.seq (cp rQb 4 (by decide))).seq
    ((gn.seq (cp 11 4 (by decide))).seq ((nc.seq nn).seq sd))))))
  simpa only [publicRowC, saveQueueC, rowCountsC, MVM.compile] using
    all.mono le_rfl le_rfl (show _ ≤ 2 ^ 409 by norm_num)

end AdvancedEncryption.ExpLUT.Prog.RedKeyT
