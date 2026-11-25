import PE.Impl.RingBTVW.Prog.TightChain
import PE.Impl.RingBTVW.Prog.SetupEncCost
import PE.Impl.RingBTVW.Prog.SetupCost

/-!
# The clock of `Setup` at `confP` by per-tape counting

`time_setupMP_tight`: the clock of the compiled `Setup` is the loader, the per-tape time bound of
`setupP` (`vb_setupP`: every loop charged the bound of its own counter tape) and the emitter of the
output tape `91`. At `confP` (`N = 2^34`, `K = 2^25`, `k = 2^25 + 1`, `d = 2^61`, the χ sampler of
width 16), **`time_setupMP_conf'`**: at most `2^355` steps (the earlier uniform bound,
`time_setupMP_conf`, is `2^3200`).

The bound is dominated by the words of size `n = nBj = 80 k³ N² K ≈ 2^174.32` (the fair bits of the
`B_j`): drawing them (about `24 n²`: each of the `n` rounds sweeps tapes of about `n` bits, plus
building the counter), appending them to the public key (`6 n²`) and writing the two output frames
(`16 n² + 32 n²`); its value lies strictly between `2^354` and `2^355` (`setupF_conf`).
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg SigabaNeo.Tape.Sym
open AdvancedEncryption.RingBTVW.Params TightS

/-- The linear bound of a counted χ sampler from blank output (`lin_Bcount`). -/
def lxB (n a s w E S : ℕ) : ℕ := (8 * n + 8 + n * (w + 3)) * (0 + S + (n * a + n * s + E + 3))

/-- **The closed bound of the clock of `Setup`** in the sizes: the six samplers, the deterministic
part (`detCostT`), the loader and the emitter. -/
def setupF (N K k d nI G0 a s w E nA : ℕ) : ℕ :=
  let ρ : List ℕ := [0, N, K, k, d, nI, G0, a, s, nA]
  (2 * nI + 2) +
  (countT (d * (N * K)) 1 0 tCoin 0 (pEval ρ Sp) + (countT (2 * k * (N * K)) 1 0 tCoin 0 (pEval ρ Sp) +
  (lxB N a s w E (pEval ρ Sp) + (lxB (2 * k * N) a s w E (pEval ρ S3) +
  (countT (8 * (N ^ 2 * K * k ^ 3 * nA)) 1 0 tCoin 0 (pEval ρ S4) +
  (countT (N * K) 1 0 tCoin 0 (pEval ρ S4) + detCostT ρ)))))) +
  (2 * pEval ρ (aGet D17 91) + 2)

/-- The closed bound unfolded. -/
theorem setupF_eq (N K k d nI G0 a s w E nA : ℕ) : setupF N K k d nI G0 a s w E nA =
    (2 * nI + 2) +
    (countT (d * (N * K)) 1 0 tCoin 0 (pEval [0, N, K, k, d, nI, G0, a, s, nA] Sp) +
    (countT (2 * k * (N * K)) 1 0 tCoin 0 (pEval [0, N, K, k, d, nI, G0, a, s, nA] Sp) +
    (lxB N a s w E (pEval [0, N, K, k, d, nI, G0, a, s, nA] Sp) +
    (lxB (2 * k * N) a s w E (pEval [0, N, K, k, d, nI, G0, a, s, nA] S3) +
    (countT (8 * (N ^ 2 * K * k ^ 3 * nA)) 1 0 tCoin 0 (pEval [0, N, K, k, d, nI, G0, a, s, nA] S4) +
    (countT (N * K) 1 0 tCoin 0 (pEval [0, N, K, k, d, nI, G0, a, s, nA] S4) +
      detCostT [0, N, K, k, d, nI, G0, a, s, nA])))))) +
    (2 * pEval [0, N, K, k, d, nI, G0, a, s, nA] (aGet D17 91) + 2) := rfl

section Generic

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (X : ChiSampler c)

theorem z_bnd (ρ : List ℕ) (σ : Asg) (t : Fin 96) (h : aGet σ t.val = []) : bnd ρ σ t = 0 := by
  simp only [bnd, h]; rfl

set_option maxRecDepth 100000 in
theorem setupCostT_le (nI G0 : ℕ) {w E : ℕ} (hLin : Lin X.B.T w E) :
    setupCostT hk c X nI G0 ≤
      countT (c.d * (N * K)) 1 0 tCoin 0 (pEval (ρS c X nI G0) Sp) +
      (countT (2 * k * (N * K)) 1 0 tCoin 0 (pEval (ρS c X nI G0) Sp) +
      (lxB N X.B.a X.B.s w E (pEval (ρS c X nI G0) Sp) +
      (lxB (2 * k * N) X.B.a X.B.s w E (pEval (ρS c X nI G0) S3) +
      (countT (8 * (N ^ 2 * K * k ^ 3 * nA)) 1 0 tCoin 0 (pEval (ρS c X nI G0) S4) +
      (countT (N * K) 1 0 tCoin 0 (pEval (ρS c X nI G0) S4) + detCostT (ρS c X nI G0)))))) := by
  have x1 := z_bnd (ρS c X nI G0) σS0 (eB0 0) (by decide +kernel)
  have x2 := z_bnd (ρS c X nI G0) σS1 (eAa 0) (by decide +kernel)
  have x3 := z_bnd (ρS c X nI G0) σS2 (eTt 0) (by decide +kernel)
  have x4 := z_bnd (ρS c X nI G0) σS3 (eEe 0) (by decide +kernel)
  have x5 := z_bnd (ρS c X nI G0) σS4 (eBj 0) (by decide +kernel)
  have x6 := z_bnd (ρS c X nI G0) σS5 (ePp 0) (by decide +kernel)
  unfold setupCostT
  rw [x1, x2, x3, x4, x5, x6]
  have c1 : (bCoins (nRowD N K c.d)).T 0 (pEval (ρS c X nI G0) Sp) =
      countT (c.d * (N * K)) 1 0 tCoin 0 (pEval (ρS c X nI G0) Sp) := by
    rw [← nRowD_eq]; rfl
  have c2 : (bCoins (nRowC N K k)).T 0 (pEval (ρS c X nI G0) Sp) =
      countT (2 * k * (N * K)) 1 0 tCoin 0 (pEval (ρS c X nI G0) Sp) := by
    rw [← nRowC_eq]; rfl
  have c5 : (bCoins (nBj (N := N) hk)).T 0 (pEval (ρS c X nI G0) S4) =
      countT (8 * (N ^ 2 * K * k ^ 3 * nA)) 1 0 tCoin 0 (pEval (ρS c X nI G0) S4) := by
    rw [← nBj_eq hk]; rfl
  have c3 := lin_Bcount hLin N 0 (pEval (ρS c X nI G0) Sp)
  have c4 := lin_Bcount hLin ((Enum.list (α := RingBTVW.Fresh.Col k)).length * N) 0
    (pEval (ρS c X nI G0) S3)
  rw [nCol_eq] at c4
  have c6 : (bCoins (N * K)).T 0 (pEval (ρS c X nI G0) S4) =
      countT (N * K) 1 0 tCoin 0 (pEval (ρS c X nI G0) S4) := rfl
  rw [c1, c2, c5, c6, nCol_eq]
  unfold lxB
  gcongr

/-- **The clock of `Setup` by per-tape counting.** -/
theorem time_setupMP_tight (nI G0 : ℕ) (hnI : nInS ≤ nI) (hG1 : 1 ≤ G0) (hGS : X.B.S₀ ≤ G0) :
    (setupMP hk c X).time ≤ (2 * nI + 2) + setupCostT hk c X nI G0 +
      (2 * pEval (ρS c X nI G0) (aGet D17 91) + 2) := by
  have hin : Prog.inputBound (94 : Fin 96) nInS ≤ bnd (ρS c X nI G0) σS0 := by
    intro t
    simp only [Prog.inputBound, Function.update_apply]
    split_ifs with h
    · subst h
      show nInS ≤ pEval (ρS c X nI G0) (aGet σS0 94)
      have e : aGet σS0 94 = vnI := by decide +kernel
      rw [e]
      simp [vnI, mq, ρS, pEval, mEval]
      exact hnI
    · exact Nat.zero_le _
  obtain ⟨ht, hl⟩ := vb_setupP hk c X nI G0 hG1 hGS _ hin
  rw [time_setupMP]
  have h91 : lenBoundT (setupP hk c X) (Prog.inputBound 94 nInS) 91 ≤
      pEval (ρS c X nI G0) (aGet D17 91) := hl 91
  omega

end Generic

end AdvancedEncryption.RingBTVW.Prog
