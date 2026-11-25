import PE.Impl.ExpLUT.Prog.RedKeyTUc
import PE.Impl.ExpLUT.Prog.RedKeyTDig
/-!
# Module 9: the `u` routine at `Dc` (cap `2^150`)

**`rktUC`**: `uC Dc` maps the standard envelope `stdX v14 v19` into itself in `≤ 2^432` steps.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 1000
set_option maxRecDepth 100000

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyT

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Prog.KeyTime

theorem uRowT_le : uRowT Mx (2 ^ 24) (2 ^ 16) (2 ^ 25) ≤ 2 ^ 409 := by
  unfold uRowT recomposeTime recomposeBodyTime autQueueTime autQueueBodyTime innerProductTime
    innerProductBodyTime evalInstructionTime moveAllowance appendAllowance operationBound
  norm_num

theorem uRowsT_le : 2 ^ 22 * uRowT Mx Dc.N Dc.K (2 * Dc.N) + (2 * Mx + 5) ≤ 2 ^ 432 := by
  rw [rkN, rkK]
  have := uRowT_le
  calc _ ≤ 2 ^ 22 * 2 ^ 409 + (2 * 2 ^ 150 + 5) := by
        gcongr; exact le_of_eq_of_le (by norm_num) this
    _ ≤ 2 ^ 432 := by norm_num

theorem uFrontT_le : ringOneTime Mx Dc.N Dc.K + ((2 * Mx + 5) + (prefixTime Mx (bhPrefixLength Dc) +
    (gatherTime Mx Dc.N Dc.K (2 ^ 66) (2 ^ 16) + (2 * Mx + 5)))) ≤ 2 ^ 380 := by
  have hp := prefixT_le _ (bh_bounds_Dc 0).1
  have hg := gatherT_le (2 ^ 16) (by norm_num)
  rw [rkN, rkK] at *
  have hr : ringOneTime Mx (2 ^ 24) (2 ^ 16) ≤ 2 ^ 306 := by
    unfold ringOneTime appendAllowance; norm_num
  calc _ ≤ 2 ^ 306 + ((2 * Mx + 5) + (2 ^ 306 + (2 ^ 372 + (2 * Mx + 5)))) := by gcongr
    _ ≤ 2 ^ 380 := by norm_num

/-- **The `u` routine** at `Dc`. -/
theorem rktUC (v14 v17 v18 v19 : ℕ) (h14 : v14 ≤ Mx) (h17 : v17 ≤ Mx) (h18 : v18 ≤ Mx)
    (h19 : v19 ≤ Mx) :
    Cert (MVM.compile (uC Dc)) (layout Mx Dc.N Dc.K (stdX v14 v17 v18 v19))
      (layout Mx Dc.N Dc.K (stdX v14 v17 v18 v19)) (2 ^ 434) := by
  have hNK : Dc.N * Dc.K ≤ Mx := by rw [rkNK]; norm_num
  let b0 := stdX v14 v17 v18 v19
  have h0 := stdX_inputs v14 v17 v18 v19 h14 h17 h18 h19
  have hb0 : b0 rB1 = 1 := stdX_rB1 _ _ _ _
  -- ring one
  have p1 := compile_ringOneC Mx Dc.N Dc.K b0 h0 hb0 (by rw [rkNK]; norm_num)
  let b1 := ringOneResult Dc.N Dc.K b0
  have h1 : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b1) := ringOneResult_inputs _ _ _ b0 h0
  -- bRowC
  have p2 := layout_copy Mx Dc.N Dc.K b1 h1.top 0 14 (by simp [b1, ringOneResult, b0, stdX]; exact h14)
  have hpre : bhPrefixLength Dc ≤ Mx := (bh_bounds_Dc 0).1.trans (by norm_num)
  have p3 := compile_prefixC Mx Dc.N Dc.K _ b1 h1 (by simp [b1, ringOneResult, b0, stdX]) hpre
  let b2 := prefixResult (bhPrefixLength Dc) b1
  have h2 : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b2) := prefixResult_inputs _ _ _ _ b1 h1 hpre
  have hidx : ∀ j ∈ bRowIdx Dc, j ≤ 2 ^ 66 := by
    intro j hj
    simp only [bRowIdx, List.mem_map, List.mem_ofFn] at hj
    obtain ⟨x, _, rfl⟩ := hj
    exact (Enum.index_lt x).le.trans publicSizeInputs_Dc.source
  have hlen : (bRowIdx Dc).length = 2 ^ 16 := by
    rw [bRowIdx, List.length_map, List.length_ofFn, rkK]
  have p4 := compile_gatherC Mx Dc.N Dc.K (2 ^ 66) (bRowIdx Dc) b2 h2
    (by simp [b2, prefixResult, b1, ringOneResult, b0, stdX])
    (by simp [b2, prefixResult, b1, ringOneResult, b0, stdX])
    (by rw [rkNK]; norm_num) hidx (by rw [hlen, rkNK]; norm_num)
  rw [hlen] at p4
  let b3 := Function.update (gatherBase Mx b2) 4 (2 ^ 16 * (Dc.N * Dc.K))
  have h3 : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b3) :=
    (gatherBase_inputs _ _ _ b2 h2).update_layout _ _ (by rw [rkNK]; norm_num)
  have p5 := layout_copy_update Mx Dc.N Dc.K b3 h3.top rUb 4
  let b4 := Function.update b3 rUb (2 ^ 16 * (Dc.N * Dc.K))
  have e5 : Function.update b3 rUb (b3 4) = b4 := by simp [b4, b3]
  rw [e5] at p5
  have h4 : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b4) :=
    h3.update_layout _ _ (by rw [rkNK]; norm_num)
  -- the row queues
  have p6 := layout_copy Mx Dc.N Dc.K b4 h4.top rUz 17
    (by simp [b4, b3, gatherBase, b2, prefixResult, b1, ringOneResult, b0, stdX]; exact h17)
  have p7 := layout_clear_update Mx Dc.N Dc.K b4 h4.top rUp
  let b5 := Function.update b4 rUp 0
  have h5 : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b5) := h4.update_layout _ _ (by omega)
  have p8 := layout_clear_update Mx Dc.N Dc.K b5 h5.top rUg
  let b6 := Function.update b5 rUg 0
  have h6 : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b6) := h5.update_layout _ _ (by omega)
  have hrows : (List.ofFn fun i : Fin (setting Dc).E.W => i.val).length = 2 ^ 22 := by
    rw [List.length_ofFn, rkW]
  have p9 := rktURowsC Mx Dc.N Dc.K (2 * Dc.N) (rowExponent Dc)
    (List.ofFn fun i : Fin (setting Dc).E.W => i.val) b6 h6
    (by simp [b6, b5, b4, b3, gatherBase, b2, prefixResult, b1, ringOneResult, b0, stdX])
    (by simp [b6, b5, b4, b3, gatherBase, b2, prefixResult, b1, ringOneResult, b0, stdX])
    (by intro r hr
        simp only [uScr, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [b6, b5, b4, b3, gatherBase, b2, prefixResult, b1, ringOneResult, b0, stdX])
    (fun i _ => (rowExponent_lt Dc i).le) (by rw [rkN]; norm_num) (by rw [rkK]; norm_num)
    (by simp only [b6, b5, b4, Function.update_apply]; simp; rw [rkNK, rkK]; norm_num)
    (by rw [hrows]; simp [b6, b5]; rw [rkNK]; norm_num)
    (by rw [hrows]; simp [b6, b5]; rw [rkNK]; norm_num)
  rw [hrows] at p9
  let b7 := Function.update (Function.update b6 rUg (b6 rUg + 2 ^ 22 * (Dc.N * Dc.K))) rUp
    (b6 rUp + 2 ^ 22 * (Dc.N * Dc.K))
  have hW : 2 ^ 22 * (Dc.N * Dc.K) ≤ Mx := by rw [rkNK]; norm_num
  have h7 : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b7) :=
    (h6.update_layout _ _ (by simp [b6]; exact hW)).update_layout _ _ (by simp [b6, b5]; exact hW)
  have p10 := layout_copy Mx Dc.N Dc.K b7 h7.top rQa rUp
    (by simp [b7, b6, b5, b4, b3, gatherBase, b2, prefixResult, b1, ringOneResult, b0, stdX]
        exact hW)
  have p11 := layout_copy Mx Dc.N Dc.K b7 h7.top rQb rUg
    (by simp [b7, b6, b5, b4, b3, gatherBase, b2, prefixResult, b1, ringOneResult, b0, stdX]
        exact hW)
  have hWM : (setting Dc).E.W ≤ Mx := by rw [rkW]; norm_num
  have hKM : Dc.K ≤ Mx := by rw [rkK]; norm_num
  have p12 := layout_nat_update Mx Dc.N Dc.K b7 h7 rQc rB1 (by decide) _
    (by simp [b7, b6, b5, b4, b3, gatherBase, b2, prefixResult, b1, ringOneResult, b0, stdX]) hWM
  let b8 := Function.update b7 rQc (setting Dc).E.W
  have h8 : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b8) := h7.update_layout _ _ hWM
  have p13 := layout_nat_update Mx Dc.N Dc.K b8 h8 rQk rB1 (by decide) _
    (by simp [b8, b7, b6, b5, b4, b3, gatherBase, b2, prefixResult, b1, ringOneResult, b0, stdX])
    hKM
  let b9 := Function.update b8 rQk Dc.K
  have h9 : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b9) := h8.update_layout _ _ hKM
  have k9 (r : Fin 64) (hr : r ∉ [0, 1, 2, 3, 4, 5, 6, 7, rUb, rUp, rUg, rQc, rQk]) :
      b9 r = stdX v14 v17 v18 v19 r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [b9, b8, b7, b6, b5, b4, b3, gatherBase, b2, prefixResult, b1, ringOneResult, b0, hr]
  have hsx (r : Fin 64) (hr : r ∉ [0, 1, 2, 3, 4, 5, 6, 7, rUb, rUp, rUg, rQc, rQk])
      (h1 : r ≠ rB1) (h2 : r ≠ rZ) (h3 : r ≠ 14) (h5 : r ≠ 17) (h6 : r ≠ 18) (h4 : r ≠ 19) :
      b9 r = Mx := by
    rw [k9 r hr, stdX_other _ _ _ _ r h1 h2 h3 h5 h6 h4]
  have p14 := compile_decRowsC Mx Dc.N Dc.K Dc.K (setting Dc).E.W b9 h9
    (by rw [k9 _ (by decide), stdX_rB1])
    (by rw [k9 rZ (by decide), k9 rQx (by decide), stdX_rZ,
      stdX_other _ _ _ _ rQx (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hNK)
    (by rw [k9 rZ (by decide), k9 rIa (by decide), stdX_rZ,
      stdX_other _ _ _ _ rIa (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hNK)
    (by rw [hsx rTd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hNK)
    (by rw [hsx rY (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hNK)
    (by simp [b9])
    (by rw [hsx rCK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp only [b9, Function.update_self]; exact hKM)
    (by rw [hsx rU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hKM)
    (by rw [hsx rZq (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), rkNK, rkK]
        norm_num)
    (by simp [b9, b8])
    (by rw [rkW, rkNK, rkK]; norm_num)
  let b10 := Function.update b9 rDq ((setting Dc).E.W * (Dc.K * (Dc.N * Dc.K)))
  have h10 : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b10) :=
    h9.update_layout _ _ (by rw [rkW, rkNK, rkK]; norm_num)
  have p15 := layout_copy Mx Dc.N Dc.K b10 h10.top rVu rDq
    (by have := top_of_inputs h10 rDq
        rw [show b10 rVu = b9 rVu by simp [b10], hsx rVu (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)]
        exact this)
  have hout : b10 ≤ stdX v14 v17 v18 v19 := by
    apply le_stdX _ _ _ _ _ (top_of_inputs h10)
    · simp only [b10, Function.update_of_ne (by decide : rB1 ≠ rDq)]
      rw [k9 _ (by decide), stdX_rB1]
    · simp only [b10, Function.update_of_ne (by decide : rZ ≠ rDq)]
      rw [k9 _ (by decide), stdX_rZ]
    · simp only [b10, Function.update_of_ne (by decide : (14 : Fin 64) ≠ rDq)]
      rw [k9 _ (by decide), stdX_14]
    · simp only [b10, Function.update_of_ne (by decide : (17 : Fin 64) ≠ rDq)]
      rw [k9 _ (by decide), stdX_17]
    · simp only [b10, Function.update_of_ne (by decide : (18 : Fin 64) ≠ rDq)]
      rw [k9 _ (by decide), stdX_18]
    · simp only [b10, Function.update_of_ne (by decide : (19 : Fin 64) ≠ rDq)]
      rw [k9 _ (by decide), stdX_19]
  have hT1 := uFrontT_le
  have hT2 := uRowsT_le
  have hT3 : decomposeRowsTime Mx Dc.N Dc.K Dc.K (setting Dc).E.W ≤ 2 ^ 429 :=
    decRowsT_var _ _ _ rkN.le rkK.le rkW.le
  have hn1 : (32 * (setting Dc).E.W + 4) * (2 * Mx + 5) ≤ 2 ^ 200 := by rw [rkW]; norm_num
  have hn2 : (32 * Dc.K + 4) * (2 * Mx + 5) ≤ 2 ^ 200 := by rw [rkK]; norm_num
  have front := p2.seq (p3.seq (p4.seq p5))
  have rest := p6.seq (p7.seq (p8.seq (p9.seq (p10.seq (p11.seq (p12.seq (p13.seq
    (p14.seq p15))))))))
  have all := p1.seq (front.seq rest)
  rw [uC, bRowC, saveQueueC]
  refine all.mono le_rfl (layout_mono _ _ _ hout) ?_
  have hr : (2 * Mx + 5) + ((2 * Mx + 5) + ((2 * Mx + 5) +
      ((2 ^ 22 * uRowT Mx Dc.N Dc.K (2 * Dc.N) + (2 * Mx + 5)) + ((2 * Mx + 5) + ((2 * Mx + 5) +
      ((32 * (setting Dc).E.W + 4) * (2 * Mx + 5) + ((32 * Dc.K + 4) * (2 * Mx + 5) +
      (decomposeRowsTime Mx Dc.N Dc.K Dc.K (setting Dc).E.W + (2 * Mx + 5))))))))) ≤
      (2 * Mx + 5) + ((2 * Mx + 5) + ((2 * Mx + 5) + (2 ^ 432 + ((2 * Mx + 5) + ((2 * Mx + 5) +
      (2 ^ 200 + (2 ^ 200 + (2 ^ 429 + (2 * Mx + 5))))))))) := by
    gcongr
  have hnum : 2 ^ 380 + ((2 * Mx + 5) + ((2 * Mx + 5) + ((2 * Mx + 5) + (2 ^ 432 + ((2 * Mx + 5) +
      ((2 * Mx + 5) + (2 ^ 200 + (2 ^ 200 + (2 ^ 429 + (2 * Mx + 5)))))))))) ≤ (2 : ℕ) ^ 434 := by
    norm_num
  rw [← Nat.add_assoc]
  exact le_trans (Nat.add_le_add hT1 hr) hnum

end AdvancedEncryption.ExpLUT.Prog.RedKeyT
