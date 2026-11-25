import PE.Impl.ExpLUT.Prog.RedKeyC3Fin
import PE.Impl.ExpLUT.Prog.RedDecode

/-!
# The weight of the M3 code `pkOf RedKeyPkt.pkt` (`≤ 2^160`, hypothesis `hw3` of `c3_spec`)

`pkOf pkt = pkConstC Dc ; pkCfC Dc ; pktC Dc`. The fixed (literal-free) phases are counted by
`decide`; every template list by F3's `weight_templateOpsC` (linear `natC` weights), with the
template lengths (codec sizes, `Enum` lengths) bounded at `Dc` by `omega` after rewriting the
dimensions to **numerals** (`cw_K`, `cw_N`, `cw_b`) and generalizing `Dc.mb ≤ 2^42`,
`rows ≤ 2^51`, `gD ≤ 2^30`. (Rewriting with `2 ^ k`-forms, or `norm_num` on the resulting goals,
makes the kernel recurse too deeply.)

* **`cw_pkOf : codeWeight (pkOf RedKeyPkt.pkt) ≤ 2 ^ 160`** (in fact `≤ 2^124`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 2000
set_option maxRecDepth 100000

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyC

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM
open AdvancedEncryption.ExpLUT.Prog.RedKeyPkt AdvancedEncryption.ExpLUT.Prog.RedKeyMid
open AdvancedEncryption.ExpLUT.Params AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open SigabaNeo.Lattices.Algo

/-! ### The dimensions at `Dc`, as numerals -/

theorem cw_gD : gD Dc ≤ 1073741824 := by norm_num [Dc, Kc, gD, gGen]
theorem cw_K : Dc.K = 65536 := by show Kc = _; rw [Kc_def]; rfl
theorem cw_N : Dc.N = 16777216 := rfl
theorem cw_b : Dc.b = 22 := rfl
theorem cw_mb : Dc.mb ≤ 4398046511104 := by show mbar ≤ _; rw [mbar_def, Kc_def]; norm_num [en]
theorem cw_rows : (circParamsD Dc).rows ≤ 2251799813685248 := rowsD_Dc_le.trans (by norm_num)
theorem cw_w8 : w8.len = 16 := rfl

/-! ### `Enum` lengths -/

theorem cw_lenNZ (n : ℕ) : (Enum.list (α := Pos × Col n)).length = 16 * (2 * n) := by
  rw [Enum.length_prod, Enum.length_prod, len_fin, len_fin, len_fin, cw_w8]

theorem cw_lenR0 (n : ℕ) : (Enum.list (α := Col n)).length = 2 * n := by
  rw [Enum.length_prod, len_fin, len_fin]

theorem cw_lenRin (n : ℕ) :
    (Enum.list (α := Pos × AdvancedEncryption.ExpLUT.Dig n × Col n)).length =
      16 * ((2 * (2 * n * n)) * (2 * n)) := by
  simp only [Enum.length_prod, len_fin, cw_w8]

theorem cw_lenD (n : ℕ) : (Enum.list (α := DigI n)).length = 2 * (2 * n) * n := by
  simp only [Enum.length_prod, len_fin]; ring

theorem cw_NZ : pkNZ Dc = 16 * (2 * 65536) := by rw [← cw_K]; exact cw_lenNZ _
theorem cw_NR0 : pkNR0 Dc = 2 * 65536 := by rw [← cw_K]; exact cw_lenR0 _
theorem cw_NRin : pkNRin Dc = 16 * ((2 * (2 * 65536 * 65536)) * (2 * 65536)) := by
  rw [← cw_K]; exact cw_lenRin _
theorem cw_ND : ptND Dc = 2 * (2 * 65536) * 65536 := by rw [← cw_K]; exact cw_lenD _

/-! ### The template lists -/

/-- The weights of `pkConstOps`, listed (a separate step: unfolding the list and summing it in
one `simp` call makes the kernel recurse too deeply). -/
theorem cw_constMap (D : Dims) : (pkConstOps D).map (fun op ↦ op.2.weightBound) =
    [3 * gD D + 1, 3 * 1 + 1, 3 * D.b + 1, 3 * ((32 * D.K ^ 3 + 12 * D.K) * (D.N * D.K)) + 1,
     3 * D.K + 1, 3 * (D.K - 1) + 1, 3 * (D.N * D.K) + 1, 3 * (2 * D.K) + 1,
     3 * (D.K * (D.N * D.K)) + 1, 3 * (2 * D.K * (D.N * D.K)) + 1,
     3 * (2 * (2 * D.K) * (D.N * D.K)) + 1, D.N * D.K + 2, D.N * D.K + 2, 3 * (4 * D.K) + 1,
     3 * 2 ^ D.b + 1, 3 * tlK + 1, D.N * D.K + 2, 3 * 14 + 1] := by
  simp only [pkConstOps, List.map_cons, List.map_nil, TemplateWord.weightBound, length_encRM]

theorem cw_constOps : ((pkConstOps Dc).map (fun op ↦ op.2.weightBound)).sum ≤ 2 ^ 120 := by
  rw [cw_constMap Dc]
  have hg := cw_gD
  simp only [List.sum_cons, List.sum_nil, cw_K, cw_N, cw_b, tlK]
  generalize gD Dc = g at hg
  omega

/-- The weights of `pkSwOps`, listed. -/
theorem cw_swMap (D : Dims) : (pkSwOps D).map (fun op ↦ op.2.weightBound) =
    [3 * 8 + 1, 3 * 2 ^ 14 + 1, 3 * (2 * D.N) + 1, 0 + 1 + 2, 3 * (D.N * D.K - 1) + 1, 3 * 14 + 1,
     3 * tlK + 1, 0 + 1 + 2, 3 * 16 + 1] := by
  simp only [pkSwOps, List.map_cons, List.map_nil, TemplateWord.weightBound, List.length_cons,
    List.length_nil]

theorem cw_swOps : ((pkSwOps Dc).map (fun op ↦ op.2.weightBound)).sum ≤ 2 ^ 120 := by
  rw [cw_swMap Dc]
  simp only [List.sum_cons, List.sum_nil, cw_K, cw_N, tlK]
  omega

theorem cw_pbOps : ((pkPbOps Dc).map (fun op ↦ op.2.weightBound)).sum ≤ 2 ^ 120 := by
  simp only [pkPbOps, pbOffHv, pbOffav, pbOffA0v, pbOffAinv, pbOffAav, pbOffhv, pbOffcbv,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, TemplateWord.weightBound, codecSize,
    Wb, Jh, Pos, len_sum, Enum.length_prod, len_fin]
  have hmb := cw_mb
  have hg := cw_gD
  simp only [cw_K, cw_N, cw_b, cw_w8]
  generalize Dc.mb = m at hmb
  generalize gD Dc = g at hg
  omega

theorem cw_lpOps : ((pkLpOps Dc).map (fun op ↦ op.2.weightBound)).sum ≤ 2 ^ 120 := by
  simp only [pkLpOps, pbOffzr, cw_NZ, cw_NR0, cw_NRin, cw_ND, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, TemplateWord.weightBound]
  simp only [codecSize, Wb, Jh, Pos, Col, AdvancedEncryption.ExpLUT.Dig, len_sum,
    Enum.length_prod, len_fin, List.length_cons, List.length_nil]
  have hmb := cw_mb
  have hr := cw_rows
  simp only [cw_K, cw_N, cw_b, cw_w8]
  generalize Dc.mb = m at hmb
  generalize (circParamsD Dc).rows = r at hr
  omega

/-! ### The three parts -/

theorem cw_pkMoveC : codeWeight pkMoveC ≤ 1000 := by decide +kernel
theorem cw_pkWalkC : codeWeight pkWalkC ≤ 1000 := by decide +kernel
theorem cw_pbPubC : codeWeight pbPubC ≤ 1000 := by decide +kernel
theorem cw_pkFinC : codeWeight pkFinC ≤ 1000 := by decide +kernel
theorem cw_bitsC : codeWeight (bitsC 5 rB1 6) ≤ 1000 := by decide +kernel

theorem cw_fixedPk : codeWeight pkMoveC + codeWeight pkWalkC + codeWeight pbPubC +
    codeWeight pkFinC + codeWeight (bitsC 5 rB1 6) ≤ 5000 := by
  have := cw_pkMoveC; have := cw_pkWalkC; have := cw_pbPubC; have := cw_pkFinC; have := cw_bitsC
  omega

theorem cw_pkConstC : codeWeight (pkConstC Dc) ≤ 2 ^ 121 := by
  have h1 := weight_templateOpsC (pkConstOps Dc)
  have h2 := cw_constOps
  have h3 := cw_fixedPk
  rw [show pkConstC Dc = .seq (.clr 6) (.seq (bitsC 5 rB1 6) (templateOpsC (pkConstOps Dc)))
    from rfl, cs_cw_seq, cs_cw_seq, show codeWeight (.clr 6) = 1 from rfl]
  omega

theorem cw_nSl : nSl Dc ≤ 4398046511104 + 22 * (2 * (2 * 65536)) := by
  rw [nSl, length_seRestL, cw_b, cw_K]
  exact Nat.add_le_add_right cw_mb _

theorem cw_pkCfC : codeWeight (pkCfC Dc) ≤ 2 ^ 121 := by
  have h1 := weight_natC 29 rB1 (cpLen - predLen)
  have h2 := weight_natC seLoopC rB1 (nSl Dc)
  have h3 := weight_natC 29 rB1 Dc.mb
  have h4 : cpLen - predLen ≤ 16 * 58720256 := by
    simp only [cpLen, tlK]; omega
  have h5 := cw_nSl
  have h6 := cw_mb
  simp only [pkCfC, codeWeight] at h1 h2 h3 ⊢
  omega

theorem cw_pktC : codeWeight (pktC Dc) ≤ 2 ^ 123 := by
  have h1 := weight_templateOpsC (pkSwOps Dc)
  have h2 := weight_templateOpsC (pkPbOps Dc)
  have h3 := weight_templateOpsC (pkLpOps Dc)
  have h4 := cw_swOps
  have h5 := cw_pbOps
  have h6 := cw_lpOps
  have h7 := cw_fixedPk
  simp only [pktC, codeWeight] at h1 h2 h3 ⊢
  omega

/-- **Hypothesis `hw3` of `c3_spec`.** -/
theorem cw_pkOf : codeWeight (pkOf RedKeyPkt.pkt) ≤ 2 ^ 160 := by
  have h1 := cw_pkConstC
  have h2 := cw_pkCfC
  have h3 := cw_pktC
  rw [show pkOf RedKeyPkt.pkt = .seq (pkConstC Dc) (.seq (pkCfC Dc) (pktC Dc)) from rfl,
    cs_cw_seq, cs_cw_seq]
  omega

end AdvancedEncryption.ExpLUT.Prog.RedKeyC
