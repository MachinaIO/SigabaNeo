import PE.Impl.DualUse.Prog.EncCostT
import PE.Impl.DualUse.Prog.CostConf

/-!
# The clock of `Enc` at `confP`, with the per-tape bound of the core

`time_encMP_confT : (encMP hkp confP chiSamplerP).time ≤ 2 ^ 416` (against `2 ^ 8000` from the
uniform bound of the core, `time_encMP_conf`).

The input has at most `41 · 2^170` bits (`nInE_leT`, about `2^175.3`); the parser adds its chunks
(`ub_encParsePT`, at most `21 · 2^170` bits, almost all the `B_j`) and the samplers at most
`21 · 2^170` bits (`encSN_confT`, almost all the flooding errors `e_j`), so every tape at the entry
of the core is at most `G ≤ 83 · 2^170` (about `2^176.4`; the longest is about `2^174.3`). The core
takes at most `(2 G + 3) · W` steps with `W = pEval ρ wE ≤ 7 · 2^235` sweeps (`pEval_wE_conf`;
exactly `≈ 6.875 · 2^235`), dominated by `44 N² K² k J` (`N = 2^34`, `K = 2^25`, `k = 2^25 + 1`,
`J = 40 k² N ≈ 2^89.3` encodings): the BGG+ encodings, `J` rows of `2k` schoolbook ring products
each. So the core costs about `2^415.2` steps; the parser, the samplers, the templates and the
output frame are below `2^381`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg SigabaNeo.Tape.Sym
  AdvancedEncryption.DualUse.Params
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

/-! ### Sizes at `confP` -/

theorem pEval_head (G : ℕ) (r : List ℕ) : pEval (G :: r) wE = pEval (0 :: r) wE := by
  simp only [wE, pEval, mEval, List.headD, List.tail, pow_zero]

theorem wE_num : pEval [0, 2 ^ 34, 2 ^ 25, 2 ^ 25 + 1, 2 ^ 61,
    1 + (2 * (2 ^ 25 + 1) + 2 * (2 ^ 25 + 1)), 10 * (2 * (2 * (2 ^ 25 + 1) * ((2 ^ 25 + 1) * 2 ^ 34))),
    10, 2 ^ 25 + 1 - 2 ^ 25, 2 ^ 34 * 2 ^ 25 - 2 ^ 25] wE ≤ 7 * 2 ^ 235 := by decide +kernel

/-! ### The clock -/

/-- `encSTL` with the counts as variables. -/
def encSTLv (N K D C R E ba bs fa fs a s w Eχ wB EB wF EF M : ℕ) : ℕ :=
  let S1 := M + N * K * 1 + N * K * 0
  let S2 := S1 + D * N * a + D * N * s
  let S3 := S2 + N * a + N * s
  let S4 := S3 + C * N * a + C * N * s
  let S5 := S4 + C * N * a + C * N * s
  let S6 := S5 + R * ba + R * bs
  linC (N * K) M + (linX a s w Eχ (D * N) S1 + (linX a s w Eχ N S2 + (linX a s w Eχ (C * N) S3 +
    (linX a s w Eχ (C * N) S4 + (linX ba bs wB EB R S5 +
    (linX fa fs wF EF E S6 + linX a s w Eχ N (S6 + E * fa + E * fs)))))))

theorem encSTL_eqv {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)
    {a s w Eχ wB EB wF EF M D C R E : ℕ}
    (hd : (Enum.list (α := Fin c.d)).length = D)
    (hc : (Enum.list (α := RingBTVW.Col k)).length = C) (hR : nR hk c = R)
    (hE : nE (N := N) hk = E) :
    encSTL hk c a s w Eχ wB EB wF EF M = encSTLv N K D C R E (bEntB N K).a (bEntB N K).s
      (bEntF K c.w).a (bEntF K c.w).s a s w Eχ wB EB wF EF M := by
  unfold encSTL encSTLv
  rw [hd, hc, hR, hE]

/-- The bound after the parser at `confP` (from `41 · 2^170`). -/
def PE0 : ℕ := parseEGv (1 * (2 ^ 61 * (2 ^ 34 * 2 ^ 25)))
  (1 * ((1 + (2 * (2 ^ 25 + 1) + 2 * (2 ^ 25 + 1))) * (2 ^ 34 * 2 ^ 25)))
  (10 * (2 * (2 * (2 ^ 25 + 1) * ((2 ^ 25 + 1) * 2 ^ 34))) * (1 * (2 * (2 ^ 25 + 1) * (2 ^ 34 * 2 ^ 25))))
  (2 ^ 34 * 2 ^ 25) (41 * 2 ^ 170)

/-- The time of the parser at `confP`. -/
def TE0 : ℕ := parseETv (2 * 515 + 1) (1 * (2 ^ 61 * (2 ^ 34 * 2 ^ 25)))
  (1 * ((1 + (2 * (2 ^ 25 + 1) + 2 * (2 ^ 25 + 1))) * (2 ^ 34 * 2 ^ 25)))
  (10 * (2 * (2 * (2 ^ 25 + 1) * ((2 ^ 25 + 1) * 2 ^ 34))) * (1 * (2 * (2 ^ 25 + 1) * (2 ^ 34 * 2 ^ 25))))
  (2 ^ 34 * 2 ^ 25) (41 * 2 ^ 170)

theorem PE0_le : 41 * 2 ^ 170 ≤ PE0 ∧ PE0 ≤ 62 * 2 ^ 170 := by
  unfold PE0 parseEGv; norm_num

set_option exponentiation.threshold 500 in
theorem TE0_le : TE0 ≤ 2 ^ 380 := by
  unfold TE0 parseETv ufCTT dropCT forT loopT ufTb
  norm_num

end AdvancedEncryption.DualUse.Prog
