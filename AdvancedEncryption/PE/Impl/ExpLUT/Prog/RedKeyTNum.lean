import PE.Impl.ExpLUT.Prog.RedKeyTUD
/-!
# Module 9: numeric bounds of the back-end phases at the cap `2^150`

All bounds are first proved for variables (so that no tactic sees the concrete `Dc` terms) and
then instantiated.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 1000
set_option maxRecDepth 100000

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyT

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Prog.KeyTime

theorem decQT_var (N K Q : ℕ) (hN : N ≤ 2 ^ 24) (hK : K ≤ 2 ^ 16) (hQ : Q ≤ 2 ^ 66) :
    decQT Mx N K N Q ≤ 2 ^ 396 := by
  calc _ ≤ decQT Mx (2 ^ 24) (2 ^ 16) (2 ^ 24) (2 ^ 66) := by
        unfold decQT decQBT decT operationBound
        gcongr
    _ ≤ 2 ^ 396 := by
        unfold decQT decQBT decT decodeBodyTime moveAllowance appendAllowance operationBound
        norm_num

theorem candT_var (N K tw Q : ℕ) (htw : tw ≤ 32 * 2 ^ 120 + 1)
    (hQ : decQT Mx N K N Q ≤ 2 ^ 396) :
    (5 + tw) * (2 * Mx + 5) + (decQT Mx N K N Q + (2 * Mx + 5)) ≤ 2 ^ 397 := by
  calc _ ≤ (5 + (32 * 2 ^ 120 + 1)) * (2 * Mx + 5) + (2 ^ 396 + (2 * Mx + 5)) := by gcongr
    _ ≤ 2 ^ 397 := by norm_num

theorem candT_gen (D : Dims) (B : ℕ)
    (hw : ((candidateInitOps D B).map (fun op ↦ op.2.weightBound)).sum ≤ 2 ^ 120)
    (hN : D.N ≤ 2 ^ 24) (hK : D.K ≤ 2 ^ 16) (hQ : nPI D ≤ 2 ^ 66) : candT D B Mx ≤ 2 ^ 397 := by
  have htw := (templateTimeWeight_le (candidateInitOps D B)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 32 hw) 1)
  exact candT_var D.N D.K _ _ htw (decQT_var D.N D.K (nPI D) hN hK hQ)

theorem candT_le : candT Dc Params.Bk Mx ≤ 2 ^ 397 :=
  candT_gen Dc Params.Bk candidateInitWeight_Dc rkN.le rkK.le correction_counts_Dc.2.2

theorem mvSubT_var (N K R L : ℕ) (hN : N ≤ 2 ^ 24) (hK : K ≤ 2 ^ 16) (hR : R ≤ 2 ^ 66)
    (hL : L ≤ 2 ^ 66) : mvSubT Mx N K R L ≤ 2 ^ 416 := by
  calc _ ≤ mvSubT Mx (2 ^ 24) (2 ^ 16) (2 ^ 66) (2 ^ 66) := by
        unfold mvSubT mvRowT ipT ipBT mvT operationBound
        gcongr
    _ ≤ 2 ^ 416 := by
        unfold mvSubT mvRowT ipT ipBT mvT operationBound
        norm_num

theorem boxFT_var (N K R L : ℕ) (hN : N ≤ 2 ^ 24) (hK : K ≤ 2 ^ 16) (hR : R ≤ 2 ^ 16)
    (hL : L ≤ 2 ^ 66) : boxFT Mx N K K R L ≤ 2 ^ 370 := by
  calc _ ≤ boxFT Mx (2 ^ 24) (2 ^ 16) (2 ^ 16) (2 ^ 16) (2 ^ 66) := by
        unfold boxFT boxBT tstT tstLT tstBT mvT operationBound
        gcongr
    _ ≤ 2 ^ 370 := by
        unfold boxFT boxBT tstT tstLT tstBT mvT operationBound
        norm_num

theorem acceptInitT_var (N K B P : ℕ) (hN : N ≤ 2 ^ 24) (hK : K ≤ 2 ^ 16) (hB : B ≤ 2 ^ 16)
    (hKB : K - B ≤ 2 ^ 16) (hP : P ≤ 2 ^ 66) :
    (10 * K + 32 * N + 14) * (2 * Mx + 5) + repeatAppendTime Mx N + ((32 * B + 4) * (2 * Mx + 5) +
      ((32 * (K - B) + 4) * (2 * Mx + 5) + ((2 * Mx + 5) + (32 * P + 4) * (2 * Mx + 5)))) ≤
      2 ^ 330 := by
  calc _ ≤ (10 * 2 ^ 16 + 32 * 2 ^ 24 + 14) * (2 * Mx + 5) + repeatAppendTime Mx (2 ^ 24) +
        ((32 * 2 ^ 16 + 4) * (2 * Mx + 5) + ((32 * 2 ^ 16 + 4) * (2 * Mx + 5) +
          ((2 * Mx + 5) + (32 * 2 ^ 66 + 4) * (2 * Mx + 5)))) := by
        unfold repeatAppendTime
        gcongr
    _ ≤ 2 ^ 330 := by
        unfold repeatAppendTime appendAllowance
        norm_num

theorem accT_gen (D : Dims) (B : ℕ) (hN : D.N ≤ 2 ^ 24) (hK : D.K ≤ 2 ^ 16) (hB : B ≤ 2 ^ 16)
    (hP : (Enum.list (α := PIdxD D)).length ≤ 2 ^ 66) (hk : codecSize (keyEnc D) ≤ 2 ^ 120) :
    accT D Mx B (2 ^ 66) ≤ 2 ^ 371 := by
  have hKB : D.K - B ≤ 2 ^ 16 := (Nat.sub_le _ _).trans hK
  have h1 := acceptInitT_var D.N D.K B (Enum.list (α := PIdxD D)).length hN hK hB hKB hP
  have h2 := boxFT_var D.N D.K (D.K - B) (2 ^ 66) hN hK hKB le_rfl
  have h3 : max (2 * (Mx + 1) + 3) ((32 * codecSize (keyEnc D) + 4) * (2 * Mx + 5)) ≤ 2 ^ 280 := by
    apply max_le (by norm_num)
    exact le_trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.mul_le_mul_left 32 hk) 4))
      (by norm_num)
  have hnum : (2 : ℕ) ^ 330 + (2 ^ 370 + (2 ^ 280 + 1)) ≤ 2 ^ 371 := by norm_num
  exact le_trans (Nat.add_le_add h1 (Nat.add_le_add h2 (Nat.add_le_add_right h3 1))) hnum

theorem accT_le : accT Dc Mx Params.Bk (2 ^ 66) ≤ 2 ^ 371 :=
  accT_gen Dc Params.Bk rkN.le rkK.le (by rw [← rkK]; exact Params.Bk_lt_Kc.le)
    correction_counts_Dc.2.2 keyCodec_bounds_Dc.2.2

end AdvancedEncryption.ExpLUT.Prog.RedKeyT
