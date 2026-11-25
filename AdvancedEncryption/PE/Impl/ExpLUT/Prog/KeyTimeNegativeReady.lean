import PE.Impl.ExpLUT.Prog.KeyTimePowers

/-! Actual ring-one initialization and the complete negative-coefficient generator. -/
set_option exponentiation.threshold 1000

namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib

theorem layout_bitsC (M N K : ℕ) (b : Fin 64 → ℕ) (t f z : Fin 64)
    (htf : t ≠ f) (htz : t ≠ z) (hfz : f ≠ z)
    (h : RingInputs M N K (layout M N K b)) (hm : 1 ≤ M) :
    Cert (MVM.compile (bitsC t f z)) (layout M N K b)
      (layout M N K (Function.update (Function.update b t 1) f 1)) (4 * (2 * M + 5)) := by
  simpa only [bitsResult, ← layout_update] using
    compile_bitsC t f z htf htz hfz M hm (layout M N K b) h.top

def ringOneResult (N K : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (Function.update b 5 0) 6 (N * K)) 7 (N * K)

def ringOneTime (M N K : ℕ) :=
  (32 * (N * K - 1) + 10) * (2 * M + 5) + appendAllowance M

theorem compile_ringOneC (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1) (hn : 0 < N * K) :
    Cert (MVM.compile (ringOneC N K)) (layout M N K b)
      (layout M N K (ringOneResult N K b)) (ringOneTime M N K) := by
  let c := Function.update b 5 0
  let d := Function.update (Function.update c 6 1) 7 1
  let e := Function.update d 7 (N * K - 1)
  let f := Function.update e 6 (N * K)
  have hm : 1 ≤ M := by have := h.ring; omega
  have heq : 1 + (N * K - 1) = N * K := by omega
  have hc := h.update_layout 5 0 (by omega)
  have hd := (hc.update_layout 6 1 hm).update_layout 7 1 hm
  have he := hd.update_layout 7 _ ((Nat.sub_le (N * K) 1).trans h.ring)
  have hf := he.update_layout 6 _ h.ring
  have p0 := layout_clear_update M N K b h.top 5
  have p1 := layout_bitsC M N K c 6 7 5 (by decide) (by decide) (by decide) hc hm
  have p2 := layout_nat_update M N K d hd 7 rB1 (by decide) (N * K - 1)
    (by simpa [d, c] using hb) ((Nat.sub_le (N * K) 1).trans h.ring)
  have p3 := layout_append_uniform M N K e he.top 6 7
    (by simpa [e, d, heq] using h.ring)
  have p4 := layout_copy_update M N K f hf.top 7 6
  have h3 : Function.update e 6 (e 6 + e 7) = f := by simp [f, e, d, heq]
  have h4 : Function.update f 7 (f 6) = ringOneResult N K b := by
    funext r
    by_cases h5 : r = 5 <;> by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
      simp_all [f, e, d, c, ringOneResult]
  rw [h3] at p3
  rw [h4] at p4
  rw [ringOneC]
  exact (p0.seq (p1.seq (p2.seq (p3.seq p4)))).mono le_rfl le_rfl
    (by unfold ringOneTime; ring_nf; omega)

theorem ringOneResult_inputs (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) :
    RingInputs M N K (layout M N K (ringOneResult N K b)) :=
  ((h.update_layout 5 0 (Nat.zero_le _)).update_layout 6 _ h.ring).update_layout 7 _ h.ring

def negativeReadyResult (N K H : ℕ) (b : Fin 64 → ℕ) :=
  negativeCoeffResult N K H (ringOneResult N K b)

theorem compile_negativeReadyC (M N K H : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1) (hn : 0 < N * K)
    (hh : H ≤ M) (hr : K * (N * K) + K * (N * K) ≤ M)
    (hs : H * (K * (N * K) + K * (N * K)) ≤ M) :
    Cert (MVM.compile (negativeReadyC N K H)) (layout M N K b)
      (layout M N K (negativeReadyResult N K H b))
      (ringOneTime M N K + negativeCoeffTime M N K H) :=
  (compile_ringOneC M N K b h hb hn).seq
    (compile_negativeCoeffC M N K H (ringOneResult N K b) (ringOneResult_inputs M N K b h)
      (by simpa [ringOneResult] using hb) (by simp [ringOneResult]) hh hr hs)

set_option exponentiation.threshold 1000 in
theorem ringOneTime_concrete : ringOneTime (2 ^ 120) (2 ^ 24) (2 ^ 16) ≤ 2 ^ 246 := by
  norm_num [ringOneTime, appendAllowance]

theorem compile_negativeReadyC_concrete (H : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hb : b rB1 = 1) (hh : H ≤ 2 ^ 6) :
    Cert (MVM.compile (negativeReadyC (2 ^ 24) (2 ^ 16) H))
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) (negativeReadyResult (2 ^ 24) (2 ^ 16) H b))
      (2 ^ 365) := by
  have p0 := (compile_ringOneC (2 ^ 120) (2 ^ 24) (2 ^ 16) b h hb (by norm_num)).mono
    le_rfl le_rfl ringOneTime_concrete
  have p1 := compile_negativeCoeffC_concrete H (ringOneResult (2 ^ 24) (2 ^ 16) b)
    (ringOneResult_inputs _ _ _ b h) (by simpa [ringOneResult] using hb)
    (by simp [ringOneResult]) hh
  exact (p0.seq p1).mono le_rfl le_rfl (by norm_num)

theorem negativeReadyResult_inputs (M N K H : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hh : H ≤ M)
    (hr : K * (N * K) + K * (N * K) ≤ M)
    (hs : H * (K * (N * K) + K * (N * K)) ≤ M) :
    RingInputs M N K (layout M N K (negativeReadyResult N K H b)) :=
  negativeCoeffResult_inputs M N K H (ringOneResult N K b)
    (ringOneResult_inputs M N K b h) hh hr hs

theorem negativeReadyResult_other (N K H : ℕ) (b : Fin 64 → ℕ) (r : Fin 64)
    (h2 : r ≠ 2) (h4 : r ≠ 4) (h5 : r ≠ 5) (h6 : r ≠ 6) (h7 : r ≠ 7) :
    negativeReadyResult N K H b r = b r := by
  simp [negativeReadyResult, negativeCoeffResult, ringOneResult,
    Function.update_of_ne h2, Function.update_of_ne h4, Function.update_of_ne h5,
    Function.update_of_ne h6, Function.update_of_ne h7]

theorem compile_negativeReadyC_Dc (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) :
    Cert (MVM.compile (negativeReadyC Dc.N Dc.K (Enum.list (α := Jh Dc)).length))
      (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K
        (negativeReadyResult Dc.N Dc.K (Enum.list (α := Jh Dc)).length b)) (2 ^ 365) := by
  have hh : (Enum.list (α := Jh Dc)).length ≤ 2 ^ 6 := by
    rw [(public_input_lengths Dc).2.2.2.2]
    norm_num [Dc, Params.bc]
  have hn : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
  have hk : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
  rw [hn, hk] at h ⊢
  exact compile_negativeReadyC_concrete _ b h hb hh

end AdvancedEncryption.ExpLUT.Prog.KeyTime
