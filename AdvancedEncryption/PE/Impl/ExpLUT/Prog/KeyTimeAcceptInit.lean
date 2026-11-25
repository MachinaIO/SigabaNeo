import PE.Impl.ExpLUT.Prog.KeyTimeRadius
/-! Full radius, counter and queue initialization before the family acceptance test. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib

noncomputable def acceptInitResult (D : Dims) (B : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (Function.update (Function.update (radiusResult D.N D.K b)
    rTBk B) rTKB (D.K - B)) rQa (b 18)) rQc (Enum.list (α := PIdxD D)).length

noncomputable def acceptInitTime (D : Dims) (M B : ℕ) :=
  radiusTime M D.N D.K + ((32 * B + 4) * (2 * M + 5) +
    ((32 * (D.K - B) + 4) * (2 * M + 5) +
      ((2 * M + 5) + (32 * (Enum.list (α := PIdxD D)).length + 4) * (2 * M + 5))))

theorem compile_acceptInitC (D : Dims) (M B r : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b)) (hb : b rB1 = 1)
    (hm : 1 ≤ M) (hB : B ≤ D.K) (hc : (Enum.list (α := PIdxD D)).length ≤ M) :
    Cert (MVM.compile (acceptInitC D B r)) (layout M D.N D.K b)
      (layout M D.N D.K (acceptInitResult D B b)) (acceptInitTime D M B) := by
  let c := radiusResult D.N D.K b
  let d := Function.update c rTBk B
  let e := Function.update d rTKB (D.K - B)
  let f := Function.update e rQa (b 18)
  have hi := radiusResult_inputs M D.N D.K b h hm
  have hd := hi.update_layout rTBk B (hB.trans h.width)
  have he := hd.update_layout rTKB (D.K - B) ((Nat.sub_le _ _).trans h.width)
  have hf := he.update_layout rQa (b 18) (by simpa using h.top (tR 18))
  have p0 := compile_radiusC M D.N D.K r b h hb hm
  have p1 := layout_nat_update M D.N D.K c hi rTBk rB1 (by decide) B
    (by simpa [c, radiusResult] using hb) (hB.trans h.width)
  have p2 := layout_nat_update M D.N D.K d hd rTKB rB1 (by decide) (D.K - B)
    (by simpa [d, c, radiusResult] using hb) ((Nat.sub_le _ _).trans h.width)
  have p3 := layout_copy_update M D.N D.K e he.top rQa 18
  have h18 : e 18 = b 18 := by simp [e, d, c, radiusResult]
  rw [h18] at p3
  have p4 := layout_nat_update M D.N D.K f hf rQc rB1 (by decide) _
    (by simpa [f, e, d, c, radiusResult] using hb) hc
  exact p0.seq (p1.seq (p2.seq (p3.seq p4)))

theorem acceptInitResult_inputs (D : Dims) (M B : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b)) (hm : 1 ≤ M)
    (hB : B ≤ D.K) (hc : (Enum.list (α := PIdxD D)).length ≤ M) :
    RingInputs M D.N D.K (layout M D.N D.K (acceptInitResult D B b)) :=
  ((((radiusResult_inputs M D.N D.K b h hm).update_layout rTBk B (hB.trans h.width)).update_layout
    rTKB (D.K - B) ((Nat.sub_le _ _).trans h.width)).update_layout rQa (b 18)
      (by simpa using h.top (tR 18))).update_layout rQc _ hc

theorem acceptInitResult_fields (D : Dims) (B : ℕ) (b : Fin 64 → ℕ) :
    acceptInitResult D B b rRR = D.N * D.K ∧
    acceptInitResult D B b rTBk = B ∧ acceptInitResult D B b rTKB = D.K - B ∧
    acceptInitResult D B b rQa = b 18 ∧
    acceptInitResult D B b rQc = (Enum.list (α := PIdxD D)).length ∧
    acceptInitResult D B b rB1 = b rB1 ∧ acceptInitResult D B b rZ = b rZ ∧
    acceptInitResult D B b 19 = b 19 := by
  simp [acceptInitResult, radiusResult]

set_option exponentiation.threshold 1000 in
theorem acceptInitTime_bound (D : Dims) (B : ℕ)
    (hr : radiusTime (2 ^ 120) D.N D.K ≤ 2 ^ 270) (hB : B ≤ 2 ^ 16)
    (hk : D.K ≤ 2 ^ 16) (hc : (Enum.list (α := PIdxD D)).length ≤ 2 ^ 66) :
    acceptInitTime D (2 ^ 120) B ≤ 2 ^ 272 := by
  have hsub : D.K - B ≤ 2 ^ 16 := (Nat.sub_le _ _).trans hk
  unfold acceptInitTime
  calc
    _ ≤ 2 ^ 270 + ((32 * 2 ^ 16 + 4) * (2 * 2 ^ 120 + 5) +
        ((32 * 2 ^ 16 + 4) * (2 * 2 ^ 120 + 5) +
          ((2 * 2 ^ 120 + 5) + (32 * 2 ^ 66 + 4) * (2 * 2 ^ 120 + 5)))) := by gcongr
    _ ≤ 2 ^ 272 := by norm_num

theorem compile_acceptInitC_Dc (B r : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hB : B ≤ Dc.K) :
    Cert (MVM.compile (acceptInitC Dc B r)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (acceptInitResult Dc B b)) (2 ^ 272) := by
  have hn : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
  have hk : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
  have hc := correction_counts_Dc.2.2
  have hr : radiusTime (2 ^ 120) Dc.N Dc.K ≤ 2 ^ 270 := by
    rw [hn, hk]; exact radiusTime_concrete
  exact (compile_acceptInitC Dc (2 ^ 120) B r b h hb (by norm_num) hB
    (hc.trans (by norm_num))).mono le_rfl le_rfl
      (acceptInitTime_bound Dc B hr (hB.trans hk.le) hk.le hc)

end AdvancedEncryption.ExpLUT.Prog.KeyTime
