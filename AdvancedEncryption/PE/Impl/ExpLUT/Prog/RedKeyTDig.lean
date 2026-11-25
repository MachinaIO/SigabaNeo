import PE.Impl.ExpLUT.Prog.RedKeyTPub

/-!
# Module 9: `keyDigitsC` at the tape cap `2^150`

The `2^22` public rows (`rktPublicRowsC`, F3's `compile_publicClear` with the tight row) and F3's
generic digits tail (`compile_digitsTailC` at `M = 2^150`).

* **`rktKeyDigitsC`**: `layout b → layout (digitsTailResult Dc Mx (pubRowsX b))`, `≤ 2^430` steps.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 1000
set_option maxRecDepth 100000

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyT

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Prog.KeyTime

def pubStepT : ℕ := 2 ^ 409 + appendAllowance Mx

theorem rktPublicStep (q : Fin (setting Dc).E.W) (b : Fin 64 → ℕ)
    (h : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ = Dc.N * Dc.K) (hw : PubCapsX b)
    (hs : b 15 + Dc.N * Dc.K ≤ Mx) :
    Cert (MVM.compile (.seq (publicRowC Dc q) (.app 15 rIa)))
      (layout Mx Dc.N Dc.K b)
      (layout Mx Dc.N Dc.K (Function.update b 15 (b 15 + Dc.N * Dc.K))) pubStepT := by
  let c := Function.update b rIa (Dc.N * Dc.K)
  have hi := h.update_layout rIa (Dc.N * Dc.K) h.ring
  have ho : c 15 = b 15 := by simp [c]
  have ha : c rIa = Dc.N * Dc.K := by simp [c]
  have p0 := rktPublicRowC q b h hw hb hz
  have p1 := layout_append_uniform Mx Dc.N Dc.K c hi.top 15 rIa
    (by rw [ho, ha]; exact hs)
  have hl : c ≤ b := cap_update_le b rIa _ (by rw [hw rIa (by decide)]; exact h.ring)
  apply (p0.seq p1).mono le_rfl _ le_rfl
  apply layout_mono
  intro r
  by_cases hr : r = 15
  · subst r; simp only [Function.update_self, ho, ha]; exact le_rfl
  · simp only [Function.update_of_ne hr]; exact hl r

theorem rktPublicRowsAppendC (qs : List (Fin (setting Dc).E.W)) (b : Fin 64 → ℕ)
    (h : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ = Dc.N * Dc.K) (hw : PubCapsX b)
    (hs : b 15 + qs.length * (Dc.N * Dc.K) ≤ Mx) :
    Cert (MVM.compile (publicRowsAppendC Dc qs)) (layout Mx Dc.N Dc.K b)
      (layout Mx Dc.N Dc.K (Function.update b 15 (b 15 + qs.length * (Dc.N * Dc.K))))
      (qs.length * pubStepT + (2 * Mx + 5)) := by
  induction qs generalizing b with
  | nil =>
    simpa [publicRowsAppendC] using (compile_nop (layout Mx Dc.N Dc.K b)
      Mx h.top).mono le_rfl le_rfl (show 2 * (Mx + 1) + 3 ≤ 2 * Mx + 5 by omega)
  | cons q qs ih =>
    have hs0 : b 15 + Dc.N * Dc.K ≤ Mx := by
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hs; omega
    have p0 := rktPublicStep q b h hb hz hw hs0
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
noncomputable def pubRowsX (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (publicBase Mx b) 15 ((Enum.list (α := Fin (setting Dc).E.W)).length *
    (Dc.N * Dc.K))

theorem pubRowsLen : (Enum.list (α := Fin (setting Dc).E.W)).length = 2 ^ 22 := by
  rw [len_fin, rkW]

/-- **The `2^22` public rows** (tight). -/
theorem rktPublicRowsC (b : Fin 64 → ℕ)
    (h : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ = Dc.N * Dc.K) :
    Cert (MVM.compile (publicRowsC Dc)) (layout Mx Dc.N Dc.K b)
      (layout Mx Dc.N Dc.K (pubRowsX b)) (2 ^ 432) := by
  let qs := (Enum.list (α := Fin (setting Dc).E.W))
  have hs : qs.length * (Dc.N * Dc.K) ≤ Mx := by
    rw [pubRowsLen, rkNK]; norm_num
  let c := publicBase Mx b
  have hc := publicBase_inputs Mx Dc.N Dc.K b h
  have p0 := layout_clear_update Mx Dc.N Dc.K c hc.top 15
  have p1 := rktPublicRowsAppendC qs (Function.update c 15 0)
    (hc.update_layout 15 0 (by omega))
    (by simpa [c, publicBase, publicScratch] using hb)
    (by simpa [c, publicBase, publicScratch] using hz)
    (by intro r hr
        have hn : r ≠ 15 := by intro he; subst r; norm_num [publicScratch] at hr
        simp [Function.update_of_ne hn, c, publicBase, hr])
    (by simpa using hs)
  simp only [Function.update_self, zero_add, cap_reset] at p1
  have ht : (2 * Mx + 5) + (qs.length * pubStepT + (2 * Mx + 5)) ≤ 2 ^ 432 := by
    rw [pubRowsLen]; norm_num [pubStepT, appendAllowance]
  exact (p0.seq p1).mono (layout_mono _ _ _ (le_publicBase _ _ _ b h)) le_rfl ht

/-! ### The digits tail (F3's generic certificate at `2^150`) -/

theorem decRowsT_var (N K W : ℕ) (hN : N ≤ 2 ^ 24) (hK : K ≤ 2 ^ 16) (hW : W ≤ 2 ^ 22) :
    decomposeRowsTime Mx N K K W ≤ 2 ^ 429 := by
  calc _ ≤ decomposeRowsTime Mx (2 ^ 24) (2 ^ 16) (2 ^ 16) (2 ^ 22) := by
        unfold decomposeRowsTime decomposeRowTime digitQueueTime digitQueueBodyTime operationBound
        gcongr
    _ ≤ 2 ^ 429 := by
        unfold decomposeRowsTime decomposeRowTime digitQueueTime digitQueueBodyTime moveAllowance
          appendAllowance operationBound
        norm_num

theorem targetT_gen (o t : ℕ) (ho : o ≤ 2 ^ 120) (ht : t ≤ 2 ^ 62) :
    ((32 * o + 6) * (2 * Mx + 5) + 2 * moveAllowance Mx) + (2 * Mx + 5) +
      (32 * t + 4) * (2 * Mx + 5) + appendAllowance Mx ≤ 2 ^ 306 := by
  unfold moveAllowance appendAllowance
  calc _ ≤ ((32 * 2 ^ 120 + 6) * (2 * 2 ^ 150 + 5) + 2 * ((2 * 2 ^ 150 + 3) * (20 + 10 * 2 ^ 150))) +
        (2 * 2 ^ 150 + 5) + (32 * 2 ^ 62 + 4) * (2 * 2 ^ 150 + 5) +
        (4 * 2 ^ 150 + 6) * (2 * 2 ^ 150 + 5) := by gcongr
    _ ≤ 2 ^ 306 := by norm_num

theorem digitsTailT_gen (D : Dims) (hw : (setting D).E.W ≤ 2 ^ 22) (hk : D.K ≤ 2 ^ 16)
    (hn : D.N ≤ 2 ^ 24) (ho : mpkDOffset D ≤ 2 ^ 120) (hs : targetTailLength D ≤ 2 ^ 62) :
    digitsTailTime D Mx ≤ 2 ^ 430 := by
  have ht : targetTime D Mx ≤ 2 ^ 306 := targetT_gen _ _ ho hs
  have hd : decomposeRowsTime Mx D.N D.K D.K (setting D).E.W ≤ 2 ^ 429 :=
    decRowsT_var _ _ _ hn hk hw
  unfold digitsTailTime
  calc _ ≤ 2 ^ 306 + ((2 * Mx + 5) + ((32 * 2 ^ 22 + 4) * (2 * Mx + 5) +
        ((32 * 2 ^ 16 + 4) * (2 * Mx + 5) + 2 ^ 429))) := by gcongr
    _ ≤ 2 ^ 430 := by norm_num

theorem digitsTailT_le : digitsTailTime Dc Mx ≤ 2 ^ 430 := by
  have ho : mpkDOffset Dc ≤ 2 ^ 120 :=
    (Nat.sub_le (codecSize (mpkEnc Dc)) _).trans keyCodec_bounds_Dc.1
  have hs : targetTailLength Dc ≤ 2 ^ 62 := by
    unfold targetTailLength; rw [rkW, rkNK]
    calc _ ≤ 2 ^ 22 * 2 ^ 40 := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ ≤ 2 ^ 62 := by norm_num
  exact digitsTailT_gen Dc rkW.le rkK.le rkN.le ho hs

/-- **`keyDigitsC`** at the cap `2^150`. -/
theorem rktKeyDigitsC (b : Fin 64 → ℕ)
    (h : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ = Dc.N * Dc.K) :
    Cert (MVM.compile (keyDigitsC Dc)) (layout Mx Dc.N Dc.K b)
      (layout Mx Dc.N Dc.K (digitsTailResult Dc Mx (pubRowsX b))) (2 ^ 433) := by
  have hp := rktPublicRowsC b h hb hz
  have hpi : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K (pubRowsX b)) := by
    apply (publicBase_inputs _ _ _ b h).update_layout
    rw [pubRowsLen, rkNK]; norm_num
  have ho : mpkDOffset Dc ≤ Mx :=
    ((Nat.sub_le (codecSize (mpkEnc Dc)) _).trans keyCodec_bounds_Dc.1).trans (by norm_num)
  have pt := (compile_digitsTailC Dc Mx (pubRowsX b) hpi
    (by change b rB1 = 1; exact hb) (by change b rZ ≤ Dc.N * Dc.K; exact hz.le) ho
    (by unfold targetTailLength; rw [rkW, rkNK]; norm_num)
    (by rw [rkW]; norm_num) (by rw [rkNK, rkK]; norm_num)
    (by rw [rkW, rkNK, rkK]; norm_num)).mono le_rfl le_rfl digitsTailT_le
  exact (hp.seq pt).mono le_rfl le_rfl (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.RedKeyT
