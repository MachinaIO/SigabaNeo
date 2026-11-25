import PE.Impl.ExpLUT.Prog.KeyTimeDecompose

/-! Runtime of the actual public-key target-vector loader and zero tail. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

noncomputable def targetHeadResult (D : Dims) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (Function.update b 0 (b 14)) 2 (mpkDOffset D)) 3 (D.N * D.K)

noncomputable def targetHeadTime (D : Dims) (M : ℕ) :=
  (32 * mpkDOffset D + 6) * (2 * M + 5) + 2 * moveAllowance M

theorem targetHeadResult_inputs (D : Dims) (M : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b)) (ho : mpkDOffset D ≤ M) :
    RingInputs M D.N D.K (layout M D.N D.K (targetHeadResult D b)) :=
  ((h.update_layout 0 _ (by simpa using h.top (tR 14))).update_layout 2 _ ho).update_layout 3 _ h.ring

theorem compile_targetHeadC (D : Dims) (M : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ D.N * D.K) (ho : mpkDOffset D ≤ M) :
    Cert (MVM.compile (targetHeadC D)) (layout M D.N D.K b)
      (layout M D.N D.K (targetHeadResult D b)) (targetHeadTime D M) := by
  let c := Function.update b 0 (b 14)
  let d := Function.update c 2 (mpkDOffset D)
  let e := targetHeadResult D b
  have hc := h.update_layout 0 _ (by simpa using h.top (tR 14))
  have hd := hc.update_layout 2 _ ho
  have he := targetHeadResult_inputs D M b h ho
  have p0 := layout_copy_update M D.N D.K b h.top 0 14
  have p1 := layout_nat_update M D.N D.K c hc 2 rB1 (by decide) _
    (by simpa [c] using hb) ho
  have p2 := layout_drop M D.N D.K d hd 0 2 (by decide)
  have p3 := layout_copy_cap M D.N D.K d hd.top 3 rZ (D.N * D.K)
    (by simpa [d, c] using hz)
  have p4 := layout_moveR M D.N D.K e he 3 0 (by decide)
  rw [targetHeadC]
  exact (p0.seq (p1.seq (p2.seq (p3.seq p4)))).mono le_rfl le_rfl
    (by unfold targetHeadTime; ring_nf; omega)

noncomputable def targetTailLength (D : Dims) := ((setting D).E.W - 1) * (D.N * D.K)

noncomputable def targetResult (D : Dims) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (targetHeadResult D b) 2 (targetTailLength D))
    rQa (D.N * D.K + targetTailLength D)

noncomputable def targetTime (D : Dims) (M : ℕ) :=
  targetHeadTime D M + (2 * M + 5) +
    (32 * targetTailLength D + 4) * (2 * M + 5) + appendAllowance M

theorem compile_targetC (D : Dims) (M : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ D.N * D.K) (ho : mpkDOffset D ≤ M)
    (hs : D.N * D.K + targetTailLength D ≤ M) :
    Cert (MVM.compile (targetC D)) (layout M D.N D.K b)
      (layout M D.N D.K (targetResult D b)) (targetTime D M) := by
  let c := targetHeadResult D b
  let d := Function.update c rQa (D.N * D.K)
  let e := Function.update d 2 (targetTailLength D)
  have hc := targetHeadResult_inputs D M b h ho
  have hd := hc.update_layout rQa _ h.ring
  have he := hd.update_layout 2 _ (by omega : targetTailLength D ≤ M)
  have p0 := compile_targetHeadC D M b h hb hz ho
  have p1 := layout_copy_update M D.N D.K c hc.top rQa 3
  have p2 := layout_nat_update M D.N D.K d hd 2 rB1 (by decide) (targetTailLength D)
    (by simpa [d, c, targetHeadResult] using hb) (by omega)
  have p3 := layout_append_uniform M D.N D.K e he.top rQa 2
    (by simpa [e, d] using hs)
  have out : Function.update e rQa (e rQa + e 2) = targetResult D b := by
    funext r
    by_cases h0 : r = rQa <;> by_cases h1 : r = 2 <;>
      simp_all [e, d, c, targetResult]
  rw [out] at p3
  rw [targetC]
  exact (p0.seq (p1.seq (p2.seq p3))).mono le_rfl le_rfl (by unfold targetTime; omega)

theorem targetResult_length (D : Dims) (b : Fin 64 → ℕ) :
    targetResult D b rQa = (setting D).E.W * (D.N * D.K) := by
  have hw := (setting D).E.W_pos
  simp only [targetResult, Function.update_self, targetTailLength]
  have he : (setting D).E.W = 1 + ((setting D).E.W - 1) := by omega
  conv_rhs => rw [he]
  ring

theorem targetResult_inputs (D : Dims) (M : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b)) (ho : mpkDOffset D ≤ M)
    (hs : D.N * D.K + targetTailLength D ≤ M) :
    RingInputs M D.N D.K (layout M D.N D.K (targetResult D b)) :=
  ((targetHeadResult_inputs D M b h ho).update_layout 2 _ (by omega)).update_layout rQa _ hs

theorem targetResult_other (D : Dims) (b : Fin 64 → ℕ) (r : Fin 64)
    (h0 : r ≠ 0) (h2 : r ≠ 2) (h3 : r ≠ 3) (ha : r ≠ rQa) :
    targetResult D b r = b r := by
  simp [targetResult, targetHeadResult, Function.update_of_ne h0,
    Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne ha]

set_option exponentiation.threshold 1000 in
theorem targetTime_bound (D : Dims) (ho : mpkDOffset D ≤ 2 ^ 120)
    (hs : targetTailLength D ≤ 2 ^ 120) : targetTime D (2 ^ 120) ≤ 2 ^ 251 := by
  unfold targetTime targetHeadTime
  calc
    _ ≤ ((32 * 2 ^ 120 + 6) * (2 * 2 ^ 120 + 5) + 2 * moveAllowance (2 ^ 120)) +
        (2 * 2 ^ 120 + 5) + (32 * 2 ^ 120 + 4) * (2 * 2 ^ 120 + 5) +
        appendAllowance (2 ^ 120) := by gcongr
    _ ≤ 2 ^ 251 := by norm_num [moveAllowance, appendAllowance]

theorem compile_targetC_Dc (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K) :
    Cert (MVM.compile (targetC Dc)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (targetResult Dc b)) (2 ^ 251) := by
  have ho : mpkDOffset Dc ≤ 2 ^ 120 :=
    (Nat.sub_le (codecSize (mpkEnc Dc)) _).trans keyCodec_bounds_Dc.1
  have hs : Dc.N * Dc.K + targetTailLength Dc ≤ 2 ^ 120 := by
    have hw : (setting Dc).E.W = 2 ^ 22 := by
      change 2 ^ Dc.b = 2 ^ 22
      norm_num [Dc, Params.bc]
    unfold targetTailLength
    rw [hw]
    norm_num [Dc, Dims.N, Params.en, Params.Kc]
  exact (compile_targetC Dc (2 ^ 120) b h hb hz ho hs).mono le_rfl le_rfl
    (targetTime_bound Dc ho (by omega))

end AdvancedEncryption.ExpLUT.Prog.KeyTime
