import PE.Impl.ExpLUT.Prog.SetupTime
import PE.Impl.ExpLUT.Prog.Samplers

/-!
# The cost of `Setup` at the concrete dimensions

For any dimensions with `N = 2^24`, `K = 2^16`, `b = 22`, `m̄ = 3 · 2^40 + 408` (those of package
P, `Dc`) and the binary sampler of `T` (`binSampler`):

* **`time_setupMP_conf`**: the clock of `setupMP` is at most `2^242` (the closed form
  `setupTF` with the scratch bound `S = 2^97` and the top `M = 2^98`, evaluated by
  `decide +kernel` on numerals; dominated by `Ā T`: `22 N² K² · m̄ K` sweeps of `2 M + 3` steps);
* **`descLen_setupMP_conf`**: the description length is at most `2^249`.

The counts of the fields are first put in closed form (`nB2_eq` …), so no enumeration of a large
index type is ever evaluated.
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg SigabaNeo.Tape.Sym
open AdvancedEncryption.DualUse.Prog

theorem len_sum (α β : Type) [Enum α] [Enum β] :
    (Enum.list (α := α ⊕ β)).length = (Enum.list (α := α)).length + (Enum.list (α := β)).length := by
  show ((Enum.list (α := α)).map Sum.inl ++ (Enum.list (α := β)).map Sum.inr).length = _
  simp

theorem len_col (K : ℕ) : (Enum.list (α := Col K)).length = 2 * K := by
  rw [Enum.length_prod, len_fin, len_fin]

theorem len_dig (K : ℕ) : (Enum.list (α := Dig K)).length = 2 * (2 * K * K) := by
  rw [Enum.length_prod, Enum.length_prod, len_fin, len_col, len_fin]

theorem nB2_eq (D : Dims) : nB2 D = D.mb + D.K := by rw [nB2, len_sum, len_fin, len_fin]
theorem nH_eq (D : Dims) : nH D = D.b * 2 * (2 * (2 * D.K)) := by
  simp only [nH, Enum.length_prod, len_fin]
theorem nA_eq (D : Dims) : nA D = 16 * (2 * D.K) := by rw [nA, len_fin, len_col]; rfl
theorem nA0_eq (D : Dims) : nA0 D = 2 * (2 * D.K) := by rw [nA0, len_fin, len_col]
theorem nAin_eq (D : Dims) : nAin D = 16 * (2 * (2 * D.K * D.K) * (2 * (2 * D.K))) := by
  rw [nAin, len_fin, len_dig, len_fin, len_col]; rfl
theorem nAaut_eq (D : Dims) : nAaut D = D.b * (2 * (2 * D.K * D.K) * (2 * (2 * D.K))) := by
  rw [nAaut, len_fin, len_dig, len_fin, len_col]

/-- The time of the samplers in closed form. -/
def smpTn (N K b mb : ℕ) (B : Bnd) (S : ℕ) : ℕ :=
  let sT := S + K + mb * K * B.s
  ucT N K mb S + ((B.count (mb * K)).T 0 (S + K) +
  (ucT N K (mb + K) sT + (ucT N K (b * 2 * (2 * (2 * K))) (sT + K) +
  (ucT N K (16 * (2 * K)) (sT + K + K) + (ucT N K (2 * (2 * K)) (sT + K + K + K) +
  (ucT N K (16 * (2 * (2 * K * K) * (2 * (2 * K)))) (sT + K + K + K + K) +
  (ucT N K (b * (2 * (2 * K * K) * (2 * (2 * K)))) (sT + K + K + K + K + K) +
  ucT N K 2 (sT + K + K + K + K + K + K))))))))

/-- The templates in closed form. -/
def tmplTn (N K mb M : ℕ) : ℕ :=
  (2 * K + 1) * (4 * M + 12) + ((2 * N + 1) * (4 * M + 12) +
  ((2 * (N * K) + 1) * (4 * M + 12) + ((2 * 1 + 1) * (4 * M + 12) +
  ((2 * mb + 1) * (4 * M + 12) + ((2 * K + 1) * (4 * M + 12) +
  ((2 * (K * (N * K)) + 1) * (4 * M + 12) + ((2 * (K - 1) + 1) * (4 * M + 12) +
  ((2 * (N * K - 1) + 1) * (4 * M + 12) + (2 * (M + 1) + 3)))))))))

/-- The gadget columns in closed form. -/
def detTn (N K mb M : ℕ) : ℕ :=
  (2 * (M + 1) + 3) + ((2 * M + 3) * pEval (Prog.SpecT.vars M N K 1 mb K 0) wMatM +
    (2 * M + 3) * pEval (Prog.SpecT.vars M N K 0 0 0 0) wGr)

/-- **The clock of `Setup` in closed form.** -/
def setupTFn (N K b mb : ℕ) (B : Bnd) (nI S M : ℕ) : ℕ :=
  (2 * nI + 2) + (smpTn N K b mb B S + (tmplTn N K mb M + (detTn N K mb M + outT M))) +
    (2 * (39 * M + 2) + 2)

theorem setupTF_eq (D : Dims) (B : Bnd) (nI S M : ℕ) :
    setupTF D B nI S M = setupTFn D.N D.K D.b D.mb B nI S M := by
  simp only [setupTF, setupTFn, smpT, smpTn, tmplT, tmplTn, detT, detTn, sT, nB2_eq, nH_eq, nA_eq,
    nA0_eq, nAin_eq, nAaut_eq]

/-- The length of the parameters' word. -/
theorem nInS_le : nInS ≤ 2 ^ 11 := by decide +kernel

/-! ### The size of the binary sampler -/

theorem size_coinAp02 : (coinAp (0 : Fin 7) 2).size ≤ 1000 := by decide +kernel
theorem size_forZero : (forN (4 : Fin 7) 3 (bitAp 0 false)).size ≤ 1000 := by decide +kernel

theorem size_entB_le {N K m : ℕ} (h : N * K - 1 < 2 ^ m) : (entB N K).size ≤ 195 * m + 2072 := by
  have h1 := size_natP_le (3 : Fin 7) 4 (N * K - 1) m h
  have h2 := size_coinAp02
  have h3 := size_forZero
  have e : (prog (.prim (.clear (3 : Fin 7)))).size = 36 := rfl
  simp only [entB, zerosF, withCount, XProg.size_seq] at *
  omega

/-! ### The concrete dimensions -/

set_option maxRecDepth 100000 in
/-- The closed form at the concrete dimensions (`decide +kernel` on numerals). -/
theorem setupTFn_conf : setupTFn (2 ^ 24) (2 ^ 16) 22 (3 * 2 ^ 40 + 408)
    (bEntB (2 ^ 24) (2 ^ 16)) (2 ^ 11) (2 ^ 97) (2 ^ 98) ≤ 2 ^ 242 := by
  decide +kernel


section Conc

variable (D : Dims) (he : D.e = 24) (hK : D.K = 2 ^ 16) (hb : D.b = 22)
  (hmb : D.mb = 3 * 2 ^ 40 + 408)
include he hK hb hmb

theorem setupBounds_conf : SetupBounds D (binSampler D).B (2 ^ 11) (2 ^ 97) (2 ^ 98) := by
  have eB : (binSampler D).B = bEntB D.N D.K := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [nB2_eq, nH_eq, nA_eq, nA0_eq, nAin_eq, nAaut_eq, Dims.N, he, hK, hb, hmb]
    decide +kernel
  · rw [eB]; simp only [Dims.N, he, hK]; decide +kernel
  · rw [eB]; simp only [Dims.N, he, hK]; decide +kernel
  · rw [eB]; simp only [sT, Dims.N, he, hK, hmb]; decide +kernel
  · decide +kernel
  · simp only [Dims.N, he, hK]; decide +kernel
  · simp only [Dims.N, he, hK, hmb]; decide +kernel

/-- **The clock of `Setup` at the concrete dimensions**: at most `2^242` steps. -/
theorem time_setupMP_conf : (setupMP (binSampler D)).time ≤ 2 ^ 242 := by
  have h := time_setupMP_le (binSampler D) (setupBounds_conf D he hK hb hmb) nInS_le
  have eB : (binSampler D).B = bEntB D.N D.K := rfl
  rw [setupTF_eq, eB] at h
  simp only [Dims.N, he, hK, hb, hmb] at h
  exact h.trans setupTFn_conf

/-- **The description length of `Setup` at the concrete dimensions**: at most `2^249` bits. -/
theorem descLen_setupMP_conf : (setupMP (binSampler D)).descLen ≤ 2 ^ 249 := by
  have hm : SetupCounts D 97 := by
    unfold SetupCounts
    simp only [nB2_eq, nH_eq, nA_eq, nA0_eq, nAin_eq, nAaut_eq, Dims.N, he, hK, hb, hmb]
    decide +kernel
  have hs : (binSampler D).P.size ≤ 195 * 40 + 2072 := by
    refine size_entB_le ?_
    simp only [Dims.N, he, hK]
    decide +kernel
  refine (descLen_setupMP_le (binSampler D) hm).trans ?_
  calc 6 * ((binSampler D).P.size + 34 * (195 * 97 + 36) + 2000004) * 3 ^ 128 *
        (4 + 4 * 128 + ((binSampler D).P.size + 34 * (195 * 97 + 36) + 2000004))
      ≤ 6 * (195 * 40 + 2072 + 34 * (195 * 97 + 36) + 2000004) * 3 ^ 128 *
        (4 + 4 * 128 + (195 * 40 + 2072 + 34 * (195 * 97 + 36) + 2000004)) := by gcongr
    _ ≤ 2 ^ 249 := by decide +kernel

end Conc

end AdvancedEncryption.ExpLUT.Prog
