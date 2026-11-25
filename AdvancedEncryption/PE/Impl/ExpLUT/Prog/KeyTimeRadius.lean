import PE.Impl.ExpLUT.Prog.KeyTimeAssembly
/-! Literal radius generation on the actual acceptance initialization path. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encM length_encM)

theorem layout_emitBitsC (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (r : Fin 64) (h5 : r ≠ 5) (hb : r ≠ rB1)
    (bs : List Bool) (ht : b 5 = 1) (hf : b rB1 = 1) (hs : b r + bs.length ≤ M) :
    Cert (MVM.compile (emitBitsC r bs)) (layout M N K b)
      (layout M N K (Function.update b r (b r + bs.length)))
      ((10 * bs.length + 1) * (2 * M + 5)) := by
  have hp := compile_emitBitsC r h5 hb bs M (layout M N K b) h.top
    (by simpa using ht) (by simpa using hf) (by simpa using hs)
  simp only [layout_register] at hp
  apply hp.mono le_rfl _ le_rfl
  apply le_layout M N K _ _ (natResult_top _ _ _ _ h.top hs)
  · rw [natResult_low _ _ _ _ 35 (by decide)]; exact h.templateK
  · rw [natResult_low _ _ _ _ 36 (by decide)]; exact h.templateN
  · rw [natResult_low _ _ _ _ 37 (by decide)]; exact h.zeros.le
  · rw [natResult_low _ _ _ _ 38 (by decide)]; exact h.ones
  · intro q; simp [natResult_register, Function.update_apply]

def radiusResult (N K : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update b
    5 1) 6 1) 7 K) 2 N) rRR (N * K)

def radiusTime (M N K : ℕ) :=
  (10 * K + 32 * N + 14) * (2 * M + 5) + repeatAppendTime M N

theorem compile_radiusC (M N K r : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1) (hm : 1 ≤ M) :
    Cert (MVM.compile (radiusC N K r)) (layout M N K b)
      (layout M N K (radiusResult N K b)) (radiusTime M N K) := by
  let c := Function.update b 7 0
  let d := Function.update (Function.update c 5 1) 6 1
  let e := Function.update d rRR 0
  let f := Function.update e rRR K
  let g := Function.update f 7 K
  let j := Function.update g rRR 0
  let k := Function.update j 2 N
  have hc := h.update_layout 7 0 (Nat.zero_le _)
  have hd := (hc.update_layout 5 1 hm).update_layout 6 1 hm
  have he := hd.update_layout rRR 0 (Nat.zero_le _)
  have hf := he.update_layout rRR K h.width
  have hg := hf.update_layout 7 K h.width
  have hj := hg.update_layout rRR 0 (Nat.zero_le _)
  have hk := hj.update_layout 2 N h.dimension
  have p0 := layout_clear_update M N K b h.top 7
  have p1 := layout_bitsC M N K c 5 6 7 (by decide) (by decide) (by decide) hc hm
  have p2 := layout_clear_update M N K d hd.top rRR
  have p3 := layout_emitBitsC M N K e he rRR (by decide) (by decide)
    (encM K (r : ZMod (2 ^ K - 1))) (by simp [e, d])
    (by simpa [e, d, c] using hb) (by simpa [e, length_encM] using h.width)
  simp only [e, Function.update_self, zero_add, length_encM] at p3
  have p4 := layout_copy_update M N K f hf.top 7 rRR
  simp only [f, Function.update_self] at p4
  have p5 := layout_clear_update M N K g hg.top rRR
  have p6 := layout_nat_update M N K j hj 2 rB1 (by decide) N
    (by simpa [j, g, f, e, d, c] using hb) h.dimension
  have p7 := compile_repAppC M N K N k 2 rRR 7 (by decide) (by decide) hk
    (by simp [k]) (by simpa [k, j, g] using h.ring)
  have hout : Function.update k rRR (k rRR + N * k 7) = radiusResult N K b := by
    funext q
    simp only [k, j, g, f, e, d, c, radiusResult, Function.update_apply]
    split_ifs <;> simp_all
  rw [hout] at p7
  rw [radiusC]
  exact (p0.seq (p1.seq (p2.seq (p3.seq (p4.seq (p5.seq (p6.seq p7))))))).mono
    le_rfl le_rfl (by unfold radiusTime; ring_nf; omega)

theorem radiusResult_inputs (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hm : 1 ≤ M) :
    RingInputs M N K (layout M N K (radiusResult N K b)) :=
  ((((h.update_layout 5 1 hm).update_layout 6 1 hm).update_layout 7 K h.width).update_layout
    2 N h.dimension).update_layout rRR (N * K) h.ring

theorem radiusResult_fields (N K : ℕ) (b : Fin 64 → ℕ) :
    radiusResult N K b rRR = N * K ∧ radiusResult N K b rB1 = b rB1 ∧
    radiusResult N K b rZ = b rZ ∧ radiusResult N K b 18 = b 18 ∧
    radiusResult N K b 19 = b 19 := by simp [radiusResult]

set_option exponentiation.threshold 1000 in
theorem radiusTime_concrete : radiusTime (2 ^ 120) (2 ^ 24) (2 ^ 16) ≤ 2 ^ 270 := by
  norm_num [radiusTime, repeatAppendTime, appendAllowance]

theorem compile_radiusC_Dc (r : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) :
    Cert (MVM.compile (radiusC Dc.N Dc.K r)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (radiusResult Dc.N Dc.K b)) (2 ^ 270) := by
  apply (compile_radiusC _ _ _ r b h hb (by norm_num)).mono le_rfl le_rfl
  have hn : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
  have hk : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
  rw [hn, hk]; exact radiusTime_concrete

end AdvancedEncryption.ExpLUT.Prog.KeyTime
