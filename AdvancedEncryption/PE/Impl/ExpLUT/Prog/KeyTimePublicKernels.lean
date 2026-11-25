import PE.Impl.ExpLUT.Prog.KeyTimeBH

/-! Common length envelopes for composing the actual public-row generators. -/
set_option exponentiation.threshold 1000
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib

def publicScratch : List (Fin 64) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, rQa, rQb, rQc, rQk, rIa, rQx, rQy]

def PublicCaps (b : Fin 64 → ℕ) : Prop := ∀ r ∈ publicScratch, b r = 2 ^ 120

theorem public_recover (b c : Fin 64 → ℕ) (hc : PublicCaps b)
    (ht : ∀ r, c r ≤ 2 ^ 120) (hf : ∀ r, r ∉ publicScratch → c r = b r) : c ≤ b := by
  intro r
  by_cases hr : r ∈ publicScratch
  · rw [hc r hr]; exact ht r
  · exact (hf r hr).le

theorem positiveResult_size_Dc :
    2 * ((bhIndices Dc).length * (Dc.N * Dc.K)) + (2 * Dc.K) * (Dc.N * Dc.K) ≤ 2 ^ 120 := by
  have hl := (bh_bounds_Dc 0).2.1
  calc
    _ ≤ 2 * (2 ^ 66 * (Dc.N * Dc.K)) + (2 * Dc.K) * (Dc.N * Dc.K) := by gcongr
    _ ≤ 2 ^ 120 := by norm_num [Dc, Dims.N, Params.en, Params.Kc]

theorem compile_positiveCoeffC_public (i : Fin (setting Dc).E.W) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hc : PublicCaps b) (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K) :
    Cert (MVM.compile (positiveCoeffC Dc i)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K b) (2 ^ 416) := by
  have hx : b rZ ≤ b rQx := by rw [hc rQx (by decide)]; exact hz.trans h.ring
  have hy : Dc.N * Dc.K ≤ b rQy := by rw [hc rQy (by decide)]; exact h.ring
  have hs := bh_bounds_Dc i.val
  have hi := positiveResult_inputs Dc (2 ^ 120) i b h hs.1
    (hs.2.1.trans (by norm_num)) (hs.2.2.1.trans (by norm_num)) positiveResult_size_Dc
  apply (compile_positiveCoeffC_Dc i b h hb hz hx hy).mono le_rfl _ le_rfl
  apply layout_mono
  apply public_recover b _ hc (fun r ↦ by simpa using hi.top (tR r))
  intro r hr
  apply positiveResult_other
  intro hm; apply hr
  simp only [publicScratch, List.mem_cons] at hm ⊢
  tauto

theorem compile_negativeReadyC_public (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hc : PublicCaps b) (hb : b rB1 = 1) :
    Cert (MVM.compile (negativeReadyC Dc.N Dc.K (Enum.list (α := Jh Dc)).length))
      (layout (2 ^ 120) Dc.N Dc.K b) (layout (2 ^ 120) Dc.N Dc.K b) (2 ^ 365) := by
  have hh : (Enum.list (α := Jh Dc)).length = 44 := by
    rw [(public_input_lengths Dc).2.2.2.2]; norm_num [Dc, Params.bc]
  have hi := negativeReadyResult_inputs (2 ^ 120) Dc.N Dc.K (Enum.list (α := Jh Dc)).length b h
    (by rw [hh]; norm_num)
    (by norm_num [Dc, Dims.N, Params.en, Params.Kc])
    (by rw [hh]; norm_num [Dc, Dims.N, Params.en, Params.Kc])
  apply (compile_negativeReadyC_Dc b h hb).mono le_rfl _ le_rfl
  apply layout_mono
  apply public_recover b _ hc (fun r ↦ by simpa using hi.top (tR r))
  intro r hr
  apply negativeReadyResult_other <;> intro he <;> subst r <;> exact hr (by decide)

theorem compile_gatherC_public (js : List ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hc : PublicCaps b) (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K)
    (hj : ∀ j ∈ js, j ≤ 2 ^ 66) (hl : js.length ≤ 2 ^ 66) :
    Cert (MVM.compile (gatherC Dc.N Dc.K js)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K b) (2 ^ 316) := by
  have hn : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
  have hk : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
  have hs : js.length * (Dc.N * Dc.K) ≤ 2 ^ 120 :=
    (Nat.mul_le_mul_right _ hl).trans (by rw [hn, hk]; norm_num)
  have hp := compile_gatherC (2 ^ 120) Dc.N Dc.K (2 ^ 66) js b h hb hz
    (by rw [hn, hk]; norm_num) hj hs
  have hi := (gatherBase_inputs (2 ^ 120) Dc.N Dc.K b h).update_layout 4 _ hs
  have hout : Function.update (gatherBase (2 ^ 120) b) 4 (js.length * (Dc.N * Dc.K)) ≤ b := by
    apply public_recover b _ hc (fun r ↦ by simpa using hi.top (tR r))
    intro r hr
    have hne (s : Fin 64) (hs : s ∈ publicScratch) : r ≠ s := fun he ↦ hr (he.symm ▸ hs)
    simp [gatherBase, Function.update_of_ne (hne 1 (by decide)),
      Function.update_of_ne (hne 2 (by decide)), Function.update_of_ne (hne 3 (by decide)),
      Function.update_of_ne (hne 4 (by decide))]
  have ht : gatherTime (2 ^ 120) Dc.N Dc.K (2 ^ 66) js.length ≤ 2 ^ 316 := by
    rw [hn, hk]
    have hh : gatherTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 66) (2 ^ 66) ≤ 2 ^ 316 := by
      have := gatherTime_concrete; omega
    apply le_trans _ hh
    unfold gatherTime; gcongr
  exact hp.mono le_rfl (layout_mono _ _ _ hout) ht

theorem compile_selectedGather_public {α β : Type} [Enum α] [Enum β] [DecidableEq α]
    (f : β → α) (ha : (Enum.list (α := α)).length ≤ 2 ^ 66)
    (hβ : (Enum.list (α := β)).length ≤ 2 ^ 66) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hc : PublicCaps b) (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K) :
    Cert (MVM.compile (gatherC Dc.N Dc.K (Enum.list.map (Enum.index ∘ f))))
      (layout (2 ^ 120) Dc.N Dc.K b) (layout (2 ^ 120) Dc.N Dc.K b) (2 ^ 316) := by
  apply compile_gatherC_public _ b h hc hb hz
  · intro j hj
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hj
    exact (Enum.index_lt (f x)).le.trans ha
  · simpa only [List.length_map] using hβ

theorem compile_publicGather (i : Fin (setting Dc).E.W) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hc : PublicCaps b) (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K) :
    Cert (MVM.compile (positiveGatherC Dc i)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K b) (2 ^ 316) ∧
    Cert (MVM.compile (negativeGatherC Dc i)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K b) (2 ^ 316) := by
  let : DecidableEq (PIdx (Wb Dc) (Jh Dc) (setting Dc).τ (setting Dc).E.W) := Classical.decEq _
  exact ⟨compile_selectedGather_public (positiveSelection Dc i) publicSizeInputs_Dc.candidate
    publicSizeInputs_Dc.positive b h hc hb hz,
    compile_selectedGather_public (negativeSelection Dc i) publicSizeInputs_Dc.candidate
      publicSizeInputs_Dc.negative b h hc hb hz⟩

theorem compile_publicCopy (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hc : PublicCaps b) (d s : Fin 64) (hd : d ∈ publicScratch) :
    Cert (MVM.compile (.cp d s)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K b) (2 * 2 ^ 120 + 5) := by
  apply layout_copy _ _ _ b h.top
  rw [hc d hd]
  simpa using h.top (tR s)

set_option exponentiation.threshold 1000 in
theorem compile_publicNat (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hc : PublicCaps b) (hb : b rB1 = 1) (r : Fin 64)
    (hr : r ∈ publicScratch) (hne : r ≠ rB1) (n : ℕ) (hn : n ≤ 2 ^ 66) :
    Cert (MVM.compile (natC r rB1 n)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K b) (2 ^ 200) := by
  have hm : n ≤ 2 ^ 120 := hn.trans (by norm_num)
  apply (layout_nat_update _ _ _ b h r rB1 hne n hb hm).mono le_rfl
    (layout_mono _ _ _ (cap_update_le b r n (by rw [hc r hr]; exact hm)))
  calc
    _ ≤ (32 * 2 ^ 66 + 4) * (2 * 2 ^ 120 + 5) := by gcongr
    _ ≤ 2 ^ 200 := by norm_num

set_option exponentiation.threshold 1000 in
theorem compile_publicRowC (i : Fin (setting Dc).E.W) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hc : PublicCaps b) (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K) :
    Cert (MVM.compile (publicRowC Dc i)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (Function.update b rIa (Dc.N * Dc.K)))
      (2 ^ 472) := by
  have cp := compile_publicCopy b h hc
  have p := compile_positiveCoeffC_public i b h hc hb hz
  have n := compile_negativeReadyC_public b h hc hb
  obtain ⟨gp, gn⟩ := compile_publicGather i b h hc hb hz
  have nc := compile_publicNat b h hc hb rQc (by decide) (by decide) _
    publicSizeInputs_Dc.positive
  have nn := compile_publicNat b h hc hb 12 (by decide) (by decide) _
    publicSizeInputs_Dc.negative
  have cap (r : Fin 64) (hr : r ∈ publicScratch) : Dc.N * Dc.K ≤ b r := by
    rw [hc r hr]; exact h.ring
  have zcap (r : Fin 64) (hr : r ∈ publicScratch) : b rZ ≤ b r := hz.trans (cap r hr)
  have qa : QueueArithmeticCaps Dc.N Dc.K b :=
    ⟨cap _ (by decide), cap _ (by decide), cap _ (by decide),
      zcap _ (by decide), zcap _ (by decide)⟩
  have eqcap (r s : Fin 64) (hr : r ∈ publicScratch) (hs : s ∈ publicScratch) :
      b r ≤ b s := by rw [hc r hr, hc s hs]
  have sd := compile_signedDotC (2 ^ 120) Dc.N Dc.K (2 ^ 120) b h qa
    (by rw [hc rQc (by decide)]) (zcap _ (by decide))
    (eqcap _ _ (by decide) (by decide)) (eqcap _ _ (by decide) (by decide))
    (eqcap _ _ (by decide) (by decide)) (eqcap _ _ (by decide) (by decide))
  have ht : signedProductTime (2 ^ 120) Dc.N Dc.K (2 ^ 120) ≤ 2 ^ 468 := by
    have hn : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
    have hk : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
    rw [hn, hk]; exact signedProductTime_concrete
  have sd' := sd.mono le_rfl le_rfl ht
  have all := (cp 0 14 (by decide)).seq
    ((p.seq (cp rQa 4 (by decide))).seq
    ((n.seq (cp 10 4 (by decide))).seq
    ((cp 0 9 (by decide)).seq
    ((gp.seq (cp rQb 4 (by decide))).seq
    ((gn.seq (cp 11 4 (by decide))).seq ((nc.seq nn).seq sd'))))))
  simpa only [publicRowC, saveQueueC, rowCountsC, MVM.compile] using
    all.mono le_rfl le_rfl (show _ ≤ 2 ^ 472 by norm_num)


def publicBase (M : ℕ) (b : Fin 64 → ℕ) (r : Fin 64) : ℕ :=
  if r ∈ publicScratch then M else b r

theorem publicBase_inputs (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) :
    RingInputs M N K (layout M N K (publicBase M b)) := by
  apply layout_inputs
  · intro r; unfold publicBase; split_ifs
    · exact le_rfl
    · simpa using h.top (tR r)
  · exact h.ring
  · exact h.dimension
  · exact h.width

theorem le_publicBase (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) : b ≤ publicBase M b := by
  intro r; unfold publicBase; split_ifs
  · simpa using h.top (tR r)
  · exact le_rfl

def publicStepTime := 2 ^ 472 + appendAllowance (2 ^ 120)

theorem compile_publicStep (q : Fin (setting Dc).E.W) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K) (hw : PublicCaps b)
    (hs : b 15 + Dc.N * Dc.K ≤ 2 ^ 120) :
    Cert (MVM.compile (.seq (publicRowC Dc q) (.app 15 rIa)))
      (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (Function.update b 15 (b 15 + Dc.N * Dc.K)))
      publicStepTime := by
  let c := Function.update b rIa (Dc.N * Dc.K)
  have hi := h.update_layout rIa (Dc.N * Dc.K) h.ring
  have ho : c 15 = b 15 := by simp [c]
  have ha : c rIa = Dc.N * Dc.K := by simp [c]
  have p0 := compile_publicRowC q b h hw hb hz
  have p1 := layout_append_uniform (2 ^ 120) Dc.N Dc.K c hi.top 15 rIa
    (by rw [ho, ha]; exact hs)
  have hl : c ≤ b := cap_update_le b rIa _ (by rw [hw rIa (by decide)]; exact h.ring)
  apply (p0.seq p1).mono le_rfl _ le_rfl
  apply layout_mono
  intro r
  by_cases hr : r = 15
  · subst r; simp only [Function.update_self, ho, ha]; exact le_rfl
  · simp only [Function.update_of_ne hr]; exact hl r

theorem compile_publicRowsAppendC (qs : List (Fin (setting Dc).E.W)) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K)
    (hw : ∀ r ∈ publicScratch, b r = 2 ^ 120)
    (hs : b 15 + qs.length * (Dc.N * Dc.K) ≤ 2 ^ 120) :
    Cert (MVM.compile (publicRowsAppendC Dc qs)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K
        (Function.update b 15 (b 15 + qs.length * (Dc.N * Dc.K))))
      (qs.length * publicStepTime + (2 * 2 ^ 120 + 5)) := by
  induction qs generalizing b with
  | nil =>
    simpa [publicRowsAppendC] using (compile_nop (layout (2 ^ 120) Dc.N Dc.K b)
      (2 ^ 120) h.top).mono le_rfl le_rfl (show 2 * (2 ^ 120 + 1) + 3 ≤ 2 * 2 ^ 120 + 5 by omega)
  | cons q qs ih =>
    have hs0 : b 15 + Dc.N * Dc.K ≤ 2 ^ 120 := by
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hs; omega
    have p0 := compile_publicStep q b h hb hz hw hs0
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

/-- Initial clear and the entire enumeration of public-map rows. -/
theorem compile_publicClear (qs : List (Fin (setting Dc).E.W)) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K)
    (hs : qs.length * (Dc.N * Dc.K) ≤ 2 ^ 120) :
    Cert (MVM.compile (.seq (.clr 15) (publicRowsAppendC Dc qs))) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (Function.update (publicBase (2 ^ 120) b) 15
        (qs.length * (Dc.N * Dc.K))))
      ((2 * 2 ^ 120 + 5) + (qs.length * publicStepTime + (2 * 2 ^ 120 + 5))) := by
  let c := publicBase (2 ^ 120) b
  have hc := publicBase_inputs (2 ^ 120) Dc.N Dc.K b h
  have p0 := layout_clear_update (2 ^ 120) Dc.N Dc.K c hc.top 15
  have p1 := compile_publicRowsAppendC qs (Function.update c 15 0)
    (hc.update_layout 15 0 (by omega))
    (by simpa [c, publicBase, publicScratch] using hb)
    (by simpa [c, publicBase, publicScratch] using hz)
    (by intro r hr
        have hn : r ≠ 15 := by intro he; subst r; norm_num [publicScratch] at hr
        simp [Function.update_of_ne hn, c, publicBase, hr])
    (by simpa using hs)
  simp only [Function.update_self, zero_add, cap_reset] at p1
  exact (p0.seq p1).mono (layout_mono _ _ _ (le_publicBase _ _ _ b h)) le_rfl le_rfl

theorem compile_publicRowsC_Dc (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K) :
    Cert (MVM.compile (publicRowsC Dc)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (Function.update (publicBase (2 ^ 120) b) 15
        ((Enum.list (α := Fin (setting Dc).E.W)).length * (Dc.N * Dc.K)))) (2 ^ 496) := by
  have hl : (Enum.list (α := Fin (setting Dc).E.W)).length = 2 ^ 22 := by
    rw [len_fin]
    change 2 ^ Dc.b = 2 ^ 22
    norm_num [Dc, Params.bc]
  have hn : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
  have hk : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
  have hs : (Enum.list (α := Fin (setting Dc).E.W)).length * (Dc.N * Dc.K) ≤ 2 ^ 120 := by
    rw [hl, hn, hk]; norm_num
  have ht : (2 * 2 ^ 120 + 5) +
      ((Enum.list (α := Fin (setting Dc).E.W)).length * publicStepTime +
        (2 * 2 ^ 120 + 5)) ≤ 2 ^ 496 := by
    rw [hl]; norm_num [publicStepTime, appendAllowance]
  exact (compile_publicClear Enum.list b h hb hz hs).mono le_rfl le_rfl ht

noncomputable def publicRowsResult (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (publicBase (2 ^ 120) b) 15
    ((Enum.list (α := Fin (setting Dc).E.W)).length * (Dc.N * Dc.K))

theorem publicRowsResult_inputs (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b)) :
    RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K (publicRowsResult b)) := by
  apply (publicBase_inputs _ _ _ b h).update_layout
  rw [len_fin]
  change 2 ^ Dc.b * (Dc.N * Dc.K) ≤ 2 ^ 120
  norm_num [Dc, Params.bc, Dims.N, Params.en, Params.Kc]

noncomputable def keyDigitsResult (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  digitsTailResult Dc (2 ^ 120) (publicRowsResult b)

/-- Complete actual public-map evaluation and gadget decomposition. -/
theorem compile_keyDigitsC_Dc (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K) :
    Cert (MVM.compile (keyDigitsC Dc)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (keyDigitsResult b)) (2 ^ 497) := by
  have hp := compile_keyDigitsC_of_publicRows _ (publicRowsResult b) (2 ^ 496)
    (compile_publicRowsC_Dc b h hb hz) (publicRowsResult_inputs b h)
    (by change b rB1 = 1; exact hb)
    (by change b rZ ≤ Dc.N * Dc.K; exact hz)
  exact hp.mono le_rfl le_rfl (by norm_num)

theorem keyDigitsResult_inputs (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b)) :
    RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K (keyDigitsResult b)) := by
  have hn : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
  have hk : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
  have hw : (setting Dc).E.W = 2 ^ 22 := by change 2 ^ Dc.b = _; norm_num [Dc, Params.bc]
  apply digitsTailResult_inputs Dc (2 ^ 120) _ (publicRowsResult_inputs b h)
  · exact (Nat.sub_le (codecSize (mpkEnc Dc)) _).trans keyCodec_bounds_Dc.1
  · unfold targetTailLength; rw [hw, hn, hk]; norm_num
  · rw [hw]; norm_num
  · rw [hw, hn, hk]; norm_num

theorem keyDigitsResult_fields (b : Fin 64 → ℕ) :
    keyDigitsResult b rDq = (setting Dc).E.W * (Dc.K * (Dc.N * Dc.K)) ∧
    keyDigitsResult b rB1 = b rB1 ∧ keyDigitsResult b rZ = b rZ ∧
    keyDigitsResult b rQx = 2 ^ 120 ∧ keyDigitsResult b rQy = 2 ^ 120 ∧
    keyDigitsResult b 9 = b 9 ∧ keyDigitsResult b 16 = b 16 := by
  exact digitsTailResult_fields Dc (2 ^ 120) (publicRowsResult b)

end AdvancedEncryption.ExpLUT.Prog.KeyTime
