import PE.Impl.ExpLUT.Prog.RedKeyC3MT
import PE.Impl.ExpLUT.Prog.RedKeyC4
import PE.Impl.ExpLUT.Prog.RedKeyTInv
import PE.Impl.ExpLUT.Prog.RedChalDc
/-!
# Cost certificate of `mid`, phase M3 (part 3): the mirrors describe the codes

**`m3_er_const : AD.Er m3Const (pkConstC Dc)`**, **`m3_er_cf : AD.Er m3Cf (pkCfC Dc)`**, the
three template blocks of `pktC Dc` (`m3_er_sw`, `m3_er_pb`, `m3_er_lp`). Every leaf bound is
proved over the symbolic sizes (`Dc.N = 2^24`, `Dc.K = 2^16`, `Dc.b = 22`,
`Dc.mb = 3 · 2^40 + 408`, the field offsets by the word lengths) — no code is unfolded by the
kernel.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 2000

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyC3M

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open AdvancedEncryption.ExpLUT.Prog AdvancedEncryption.ExpLUT.Prog.RedKeyC4
open AdvancedEncryption.ExpLUT.Prog.RedKeyMid AdvancedEncryption.ExpLUT.Prog.RedKeyPkt

/-! ### The sizes at `Dc` -/

theorem m3_K : Dc.K = 2 ^ 16 := RedChal.Dc_K
theorem m3_N : Dc.N = 2 ^ 24 := rfl
theorem m3_b : Dc.b = 22 := rfl
theorem m3_mb : Dc.mb = m3Mb := c4_mb

theorem m3_gD : gD Dc = 9 := by
  show Lattices.gGen Dc.N (2 ^ Dc.b) = 9
  rw [m3_N, m3_b]; rfl

theorem m3_encRM_le (a : Cslib.Negacyclic (ZMod (2 ^ Dc.K - 1)) Dc.N) :
    (Lattices.Algo.encRM Dc.N Dc.K a).length ≤ 2 ^ 40 := by
  rw [Lattices.Algo.length_encRM, m3_N, m3_K]; norm_num

theorem m3_w8 : w8.len = 16 := by decide

theorem m3_nSl : nSl Dc = m3NSl := by
  rw [nSl, length_seRestL, m3_mb, m3_b, m3_K]; rfl

theorem m3_offH : pbOffHv Dc ≤ 2 ^ 98 ∧ pbOffav Dc ≤ 2 ^ 98 ∧ pbOffA0v Dc ≤ 2 ^ 98 ∧
    pbOffAinv Dc ≤ 2 ^ 98 ∧ pbOffAav Dc ≤ 2 ^ 98 := by
  have h := publicFieldLengths_sum Dc
  have hc := c4_codec
  simp only [publicFieldLengths, List.sum_cons, List.sum_nil] at h
  simp only [pbOffAav, pbOffAinv, pbOffA0v, pbOffav, pbOffHv]
  omega

theorem m3_ct : (ctEnc Dc).len ≤ 2 ^ 110 := RedChal.tmBase_Dc_le 166

theorem m3_offh : pbOffhv Dc ≤ 2 ^ 110 ∧ pbOffcbv Dc ≤ 2 ^ 110 := by
  have h := m3_ct
  have e : pbOffcbv Dc ≤ (ctEnc Dc).len := by
    simp only [pbOffcbv, pbOffhv, ctEnc, FixedEnc.len, FixedEnc.prod, FixedEnc.comap, codecSize]
    omega
  have e2 : pbOffhv Dc ≤ pbOffcbv Dc := by simp only [pbOffcbv]; omega
  omega

theorem m3_offzr : pbOffzr Dc ≤ 2 ^ 99 := by
  have h := RedKeyT.rawEnc_len_Dc_T
  have e : pbOffzr Dc ≤ (rawEnc Dc).len := by
    simp only [pbOffzr, rawEnc, FixedEnc.len, FixedEnc.prod, FixedEnc.comap, codecSize]
    omega
  omega

theorem m3_nZ : pkNZ Dc = 2 ^ 21 ∧ pkNR0 Dc = 2 ^ 17 ∧ pkNRin Dc = 2 ^ 55 ∧ ptND Dc = 2 ^ 34 := by
  simp only [pkNZ, pkNR0, pkNRin, ptND, Pos, Dig, Col, Enum.length_prod, len_fin, m3_w8]
  rw [show (setting Dc).τ = Dc.K from rfl, m3_K]
  norm_num

/-! ### The descriptions -/

theorem m3_er_const : AD.Er m3Const (pkConstC Dc) := by
  unfold m3Const pkConstC
  refine .s (.a (.c _)) (.s (.a (.c _)) (twL_er _ _ ?_))
  simp only [pkConstOps, m3ConstL, List.forall₂_cons, List.Forall₂.nil, TemplateWord.value,
    List.length_replicate, m3_encRM_le, m3_gD, and_true, true_and, le_refl]
  simp only [m3_K, m3_N, m3_b]
  norm_num

theorem m3_er_cf : AD.Er m3Cf (pkCfC Dc) := by
  unfold m3Cf pkCfC
  refine .a (.s (.c _) (.s (.nat _ _ _ _ ?_) (.s (.c _) (.s (.c _) (.s (.c _) (.s (.nat _ _ _ _ ?_)
    (.s (.c _) (.s (.c _) (.s (.nat _ _ _ _ ?_) (.c _))))))))))
  · norm_num [cpLen, tlK, predLen]
  · rw [m3_nSl]
  · rw [m3_mb]

theorem m3_er_sw : AD.Er (twL m3SwL) (templateOpsC (pkSwOps Dc)) := by
  refine twL_er _ _ ?_
  simp only [pkSwOps, m3SwL, List.forall₂_cons, List.Forall₂.nil, TemplateWord.value,
    List.length_replicate, List.length_cons, List.length_nil, m3_K, m3_N, and_true, true_and,
    le_refl]
  norm_num

theorem m3_er_pb : AD.Er (twL m3PbL) (templateOpsC (pkPbOps Dc)) := by
  refine twL_er _ _ ?_
  obtain ⟨h1, h2, h3, h4, h5⟩ := m3_offH
  obtain ⟨h6, h7⟩ := m3_offh
  simp only [pkPbOps, m3PbL, List.forall₂_cons, List.Forall₂.nil, TemplateWord.value,
    List.length_replicate, m3_gD, m3_K, m3_N, m3_b, and_true, true_and, le_refl, h1, h2, h3, h4,
    h5, h6, h7]
  norm_num

theorem m3_er_lp : AD.Er (twL m3LpL) (templateOpsC (pkLpOps Dc)) := by
  refine twL_er _ _ ?_
  obtain ⟨h1, h2, h3, h4⟩ := m3_nZ
  simp only [pkLpOps, m3LpL, List.forall₂_cons, List.Forall₂.nil, TemplateWord.value,
    List.length_replicate, List.length_cons, List.length_nil, m3_K, m3_N, m3_b, m3_mb, h1, h2, h3,
    h4, m3_offzr, and_true, true_and, le_refl]
  norm_num

end AdvancedEncryption.ExpLUT.Prog.RedKeyC3M
