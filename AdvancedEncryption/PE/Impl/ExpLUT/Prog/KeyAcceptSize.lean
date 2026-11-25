import PE.Impl.ExpLUT.Prog.KeyGatherSize
/-! Syntax-size bounds for the actual radius initializer and acceptance branch. -/
namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib

theorem weight_radiusC (N K r : ℕ) :
    codeWeight (radiusC N K r) ≤ K + 3 * N + 12 := by
  have he := weight_emitBitsC rRR (encM K (r : ZMod (2 ^ K - 1)))
  have hn := weight_natC 2 rB1 N
  simp only [length_encM] at he
  simp only [radiusC, bitsC, repAppC, codeWeight, he]
  omega

theorem weight_acceptInitC (D : Dims) (B r : ℕ) :
    codeWeight (acceptInitC D B r) ≤ D.K + 3 * D.N + 3 * B + 3 * (D.K - B) +
      3 * (Enum.list (α := PIdxD D)).length + 16 := by
  have hr := weight_radiusC D.N D.K r
  have hB := weight_natC rTBk rB1 B
  have hK := weight_natC rTKB rB1 (D.K - B)
  have hP := weight_natC rQc rB1 (Enum.list (α := PIdxD D)).length
  simp only [acceptInitC, codeWeight]
  omega

theorem weight_boxFamilyC : codeWeight boxFamilyC ≤ 100 := by decide +kernel

theorem weight_acceptC (D : Dims) (B r : ℕ) :
    codeWeight (acceptC D B r) ≤ D.K + 3 * D.N + 3 * B + 3 * (D.K - B) +
      3 * (Enum.list (α := PIdxD D)).length + 3 * codecSize (keyEnc D) + 119 := by
  have hi := weight_acceptInitC D B r
  have hz := weight_natC 19 rB1 (codecSize (keyEnc D))
  have hb := weight_boxFamilyC
  simp only [acceptC, codeWeight]
  omega

/-- Uniform state bound after replacing only the explicit dimension/count parameters. -/
theorem size_acceptC_of_bounds (D : Dims) (B r M : ℕ)
    (hK : D.K ≤ M) (hN : D.N ≤ M) (hB : B ≤ M)
    (hP : (Enum.list (α := PIdxD D)).length ≤ M) (hkey : codecSize (keyEnc D) ≤ M) :
    (compile (acceptC D B r)).size ≤ 100000 * (16 * M + 119) := by
  apply (size_compile_weight _).trans
  apply Nat.mul_le_mul_left
  have h := weight_acceptC D B r
  have hsub : D.K - B ≤ M := (Nat.sub_le _ _).trans hK
  omega

theorem keyCodecSize_eq (D : Dims) : codecSize (keyEnc D) =
    (Enum.list (α := KColt D)).length * (D.N * D.K) := rfl

open Params

/-- The scalar rejection bound includes the entire canonical zero-key output. -/
theorem accept_counts_Dc :
    (Enum.list (α := PIdxD Dc)).length ≤ 2 ^ 106 ∧
    codecSize (keyEnc Dc) ≤ 2 ^ 106 := by
  rw [keyCodecSize_eq]
  have hk := assembly_lengths_Dc.1
  have hn : Dc.N * Dc.K ≤ 2 ^ 40 := by norm_num [Dc, Kc]
  constructor
  · simp only [PIdxD, PIdx, Col, Wb, Jh, len_sum, Enum.length_prod, len_fin]
    norm_num [Dc, Kc, mbar]
  · exact (Nat.mul_le_mul hk hn).trans (by norm_num)

theorem size_acceptC_Dc : (compile (acceptC Dc Bk rSmall)).size ≤ 2 ^ 128 := by
  have hk : Dc.K ≤ 2 ^ 106 := by norm_num [Dc, Kc]
  have hn : Dc.N ≤ 2 ^ 106 := by norm_num [Dc]
  have hb : Bk ≤ 2 ^ 106 := by rw [Bk_def]; norm_num
  exact (size_acceptC_of_bounds Dc Bk rSmall (2 ^ 106) hk hn hb
    accept_counts_Dc.1 accept_counts_Dc.2).trans (by norm_num)

end AdvancedEncryption.ExpLUT.Prog
