import PE.Impl.ExpLUT.Prog.KeyTimeTarget
/-! Composition of target generation, real counters and the complete gadget decomposition. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

def decompositionScratch : List (Fin 64) := [rQx, rIa, rTd, rY, rCK, rU, rZq]

def decompositionBase (M : ℕ) (b : Fin 64 → ℕ) (r : Fin 64) :=
  if r ∈ decompositionScratch then M else b r

theorem decompositionBase_inputs (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) :
    RingInputs M N K (layout M N K (decompositionBase M b)) := by
  apply layout_inputs
  · intro r; unfold decompositionBase; split_ifs
    · exact le_rfl
    · simpa using h.top (tR r)
  · exact h.ring
  · exact h.dimension
  · exact h.width

theorem le_decompositionBase (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) : b ≤ decompositionBase M b := by
  intro r; unfold decompositionBase; split_ifs
  · simpa using h.top (tR r)
  · exact le_rfl

noncomputable def digitsTailC (D : Dims) : Code :=
  .seq (targetC D) (.seq (.cp rQb 15)
    (.seq (natC rQc rB1 (setting D).E.W) (.seq (natC rQk rB1 D.K) decRowsC)))

noncomputable def digitsReady (D : Dims) (M : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update
    (Function.update (decompositionBase M (targetResult D b)) rQb (b 15))
    rQc (setting D).E.W) rQk D.K

noncomputable def digitsTailResult (D : Dims) (M : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (digitsReady D M b) rDq ((setting D).E.W * (D.K * (D.N * D.K)))

noncomputable def digitsTailTime (D : Dims) (M : ℕ) :=
  targetTime D M + ((2 * M + 5) + ((32 * (setting D).E.W + 4) * (2 * M + 5) +
    ((32 * D.K + 4) * (2 * M + 5) + decomposeRowsTime M D.N D.K D.K (setting D).E.W)))

theorem compile_digitsTailC (D : Dims) (M : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ D.N * D.K) (ho : mpkDOffset D ≤ M)
    (hs : D.N * D.K + targetTailLength D ≤ M)
    (hw : (setting D).E.W ≤ M) (hk : D.K * (D.N * D.K) ≤ M)
    (hq : (setting D).E.W * (D.K * (D.N * D.K)) ≤ M) :
    Cert (MVM.compile (digitsTailC D)) (layout M D.N D.K b)
      (layout M D.N D.K (digitsTailResult D M b)) (digitsTailTime D M) := by
  let c := decompositionBase M (targetResult D b)
  let d := Function.update c rQb (b 15)
  let e := Function.update d rQc (setting D).E.W
  let f := digitsReady D M b
  have ht := targetResult_inputs D M b h ho hs
  have hc := decompositionBase_inputs M D.N D.K (targetResult D b) ht
  have hd := hc.update_layout rQb _ (by simpa using h.top (tR 15))
  have he := hd.update_layout rQc _ hw
  have hf := he.update_layout rQk _ h.width
  have p0 := (compile_targetC D M b h hb hz ho hs).mono le_rfl
    (layout_mono _ _ _ (le_decompositionBase M D.N D.K (targetResult D b) ht)) le_rfl
  have p1 := layout_copy_update M D.N D.K c hc.top rQb 15
  have p2 := layout_nat_update M D.N D.K d hd rQc rB1 (by decide) (setting D).E.W
    (by simpa [d, c, decompositionBase, decompositionScratch, targetResult, targetHeadResult] using hb) hw
  have p3 := layout_nat_update M D.N D.K e he rQk rB1 (by decide) D.K
    (by simpa [e, d, c, decompositionBase, decompositionScratch, targetResult, targetHeadResult] using hb) h.width
  have p4 := compile_decRowsC M D.N D.K D.K (setting D).E.W f hf
    (by simpa [f, digitsReady, decompositionBase, decompositionScratch, targetResult, targetHeadResult] using hb)
    (by simpa [f, digitsReady, decompositionBase, decompositionScratch, targetResult, targetHeadResult] using hz.trans h.ring)
    (by simpa [f, digitsReady, decompositionBase, decompositionScratch, targetResult, targetHeadResult] using hz.trans h.ring)
    (by simpa [f, digitsReady, decompositionBase, decompositionScratch] using h.ring)
    (by simpa [f, digitsReady, decompositionBase, decompositionScratch] using h.ring)
    (by simp [f, digitsReady])
    (by simpa [f, digitsReady, decompositionBase, decompositionScratch] using h.width)
    (by simpa [f, digitsReady, decompositionBase, decompositionScratch] using h.width)
    (by simpa [f, digitsReady, decompositionBase, decompositionScratch] using hk)
    (by simp [f, digitsReady]) hq
  have hc15 : c 15 = b 15 := by
    simp [c, decompositionBase, decompositionScratch, targetResult, targetHeadResult]
  rw [hc15] at p1
  exact p0.seq (p1.seq (p2.seq (p3.seq p4)))

set_option exponentiation.threshold 1000 in
theorem digitsTailTime_bound (D : Dims) (ht : targetTime D (2 ^ 120) ≤ 2 ^ 251)
    (hd : decomposeRowsTime (2 ^ 120) D.N D.K D.K (setting D).E.W ≤ 2 ^ 386)
    (hw : (setting D).E.W ≤ 2 ^ 22) (hk : D.K ≤ 2 ^ 16) :
    digitsTailTime D (2 ^ 120) ≤ 2 ^ 388 := by
  unfold digitsTailTime
  calc
    _ ≤ 2 ^ 251 + ((2 * 2 ^ 120 + 5) + ((32 * 2 ^ 22 + 4) * (2 * 2 ^ 120 + 5) +
        ((32 * 2 ^ 16 + 4) * (2 * 2 ^ 120 + 5) + 2 ^ 386))) := by gcongr
    _ ≤ 2 ^ 388 := by norm_num

set_option exponentiation.threshold 1000 in
theorem digitsTailTime_Dc : digitsTailTime Dc (2 ^ 120) ≤ 2 ^ 388 := by
  have hn : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
  have hk : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
  have hw : (setting Dc).E.W = 2 ^ 22 := by change 2 ^ Dc.b = _; norm_num [Dc, Params.bc]
  have ho : mpkDOffset Dc ≤ 2 ^ 120 :=
    (Nat.sub_le (codecSize (mpkEnc Dc)) _).trans keyCodec_bounds_Dc.1
  have ht := targetTime_bound Dc ho (by
    unfold targetTailLength; rw [hw, hn, hk]; norm_num)
  have hd : decomposeRowsTime (2 ^ 120) Dc.N Dc.K Dc.K (setting Dc).E.W ≤ 2 ^ 386 := by
    rw [hw, hn, hk]; exact decomposeRowsTime_concrete
  exact digitsTailTime_bound Dc ht hd hw.le hk.le

theorem compile_digitsTailC_Dc (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K) :
    Cert (MVM.compile (digitsTailC Dc)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (digitsTailResult Dc (2 ^ 120) b)) (2 ^ 388) := by
  have hn : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
  have hk : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
  have hw : (setting Dc).E.W = 2 ^ 22 := by change 2 ^ Dc.b = _; norm_num [Dc, Params.bc]
  have ho : mpkDOffset Dc ≤ 2 ^ 120 :=
    (Nat.sub_le (codecSize (mpkEnc Dc)) _).trans keyCodec_bounds_Dc.1
  exact (compile_digitsTailC Dc (2 ^ 120) b h hb hz ho
    (by unfold targetTailLength; rw [hw, hn, hk]; norm_num)
    (by rw [hw]; norm_num) (by rw [hn, hk]; norm_num) (by rw [hw, hn, hk]; norm_num)).mono
      le_rfl le_rfl digitsTailTime_Dc

theorem digitsTailResult_inputs (D : Dims) (M : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b)) (ho : mpkDOffset D ≤ M)
    (hs : D.N * D.K + targetTailLength D ≤ M)
    (hw : (setting D).E.W ≤ M) (hq : (setting D).E.W * (D.K * (D.N * D.K)) ≤ M) :
    RingInputs M D.N D.K (layout M D.N D.K (digitsTailResult D M b)) :=
  ((((decompositionBase_inputs M D.N D.K (targetResult D b)
    (targetResult_inputs D M b h ho hs)).update_layout rQb _
      (by simpa using h.top (tR 15))).update_layout rQc _ hw).update_layout rQk _ h.width).update_layout rDq _ hq

theorem digitsTailResult_fields (D : Dims) (M : ℕ) (b : Fin 64 → ℕ) :
    digitsTailResult D M b rDq = (setting D).E.W * (D.K * (D.N * D.K)) ∧
    digitsTailResult D M b rB1 = b rB1 ∧ digitsTailResult D M b rZ = b rZ ∧
    digitsTailResult D M b rQx = M ∧ digitsTailResult D M b rQy = b rQy ∧
    digitsTailResult D M b 9 = b 9 ∧ digitsTailResult D M b 16 = b 16 := by
  simp [digitsTailResult, digitsReady, decompositionBase, decompositionScratch,
    targetResult, targetHeadResult]

/-- The remaining public-row certificate composes with the entire verified tail. -/
theorem compile_keyDigitsC_of_publicRows (a : Fin 105 → ℕ) (b : Fin 64 → ℕ) (T : ℕ)
    (hp : Cert (MVM.compile (publicRowsC Dc)) a (layout (2 ^ 120) Dc.N Dc.K b) T)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K) :
    Cert (MVM.compile (keyDigitsC Dc)) a
      (layout (2 ^ 120) Dc.N Dc.K (digitsTailResult Dc (2 ^ 120) b)) (T + 2 ^ 388) :=
  hp.seq (compile_digitsTailC_Dc b h hb hz)

end AdvancedEncryption.ExpLUT.Prog.KeyTime
