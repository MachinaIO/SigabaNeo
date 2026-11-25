import PE.Impl.RingBTVW.Prog.CompLib
import PE.Impl.RingBTVW.Prog.SetupEncCost
import PE.Impl.RingBTVW.Prog.SetupCostP
import PE.Impl.RingBTVW.Prog.EncCostP

/-!
# The clocks of `Setup` and `Enc` at `confP`

`time_setupMP_conf`, `time_encMP_conf`: closed bounds of the clocks of the compiled `Setup` and
`Enc` with the sampler `chiSamplerP`, from the uniform bounds `ub_setupP`, `ub_encP`; the
primitive programs are bounded by `tbC · (L + 1) ^ tbD` (constants by the kernel).
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.RingBTVW.Params
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

/-! ### The primitive programs -/

theorem tb_le' {k : ℕ} {p : Prog k} (h : p.NoGrow) {C D : ℕ} (hC : Prog.tbC p ≤ C)
    (hD : Prog.tbD p ≤ D) (L : ℕ) : Prog.timeBound p L ≤ C * (L + 1) ^ D :=
  (Prog.timeBound_le p h L).trans (Nat.mul_le_mul hC (Nat.pow_le_pow_right (by omega) hD))

theorem tbs_splitP : Prog.tbD Prog.splitP ≤ 8 ∧ Prog.tbC Prog.splitP ≤ 2 ^ 20 := by decide +kernel
theorem tbs_joinP : Prog.tbD Prog.joinP ≤ 8 ∧ Prog.tbC Prog.joinP ≤ 2 ^ 20 := by decide +kernel
theorem tbs_subRWP : Prog.tbD Prog.subRWP ≤ 8 ∧ Prog.tbC Prog.subRWP ≤ 2 ^ 20 := by decide +kernel
theorem tbs_addRWP : Prog.tbD Prog.addRWP ≤ 8 ∧ Prog.tbC Prog.addRWP ≤ 2 ^ 20 := by decide +kernel
theorem tbs_gadP : Prog.tbD Prog.gadP ≤ 8 ∧ Prog.tbC Prog.gadP ≤ 2 ^ 20 := by decide +kernel
theorem tbs_matMulP : Prog.tbD Prog.matMulP ≤ 16 ∧ Prog.tbC Prog.matMulP ≤ 2 ^ 30 := by
  decide +kernel
theorem tbs_encCoreP : Prog.tbD encCoreP ≤ 32 ∧ Prog.tbC encCoreP ≤ 2 ^ 40 := by decide +kernel

theorem tb_splitP (L : ℕ) : Prog.timeBound Prog.splitP L ≤ 2 ^ 20 * (L + 1) ^ 8 :=
  tb_le' Prog.noGrow_splitP tbs_splitP.2 tbs_splitP.1 L
theorem tb_joinP (L : ℕ) : Prog.timeBound Prog.joinP L ≤ 2 ^ 20 * (L + 1) ^ 8 :=
  tb_le' Prog.noGrow_joinP tbs_joinP.2 tbs_joinP.1 L
theorem tb_subRWP (L : ℕ) : Prog.timeBound Prog.subRWP L ≤ 2 ^ 20 * (L + 1) ^ 8 :=
  tb_le' Prog.noGrow_subRWP tbs_subRWP.2 tbs_subRWP.1 L
theorem tb_addRWP (L : ℕ) : Prog.timeBound Prog.addRWP L ≤ 2 ^ 20 * (L + 1) ^ 8 :=
  tb_le' Prog.noGrow_addRWP tbs_addRWP.2 tbs_addRWP.1 L
theorem tb_gadP (L : ℕ) : Prog.timeBound Prog.gadP L ≤ 2 ^ 20 * (L + 1) ^ 8 :=
  tb_le' Prog.noGrow_gadP tbs_gadP.2 tbs_gadP.1 L
theorem tb_matMulP (L : ℕ) : Prog.timeBound Prog.matMulP L ≤ 2 ^ 30 * (L + 1) ^ 16 :=
  tb_le' Prog.noGrow_matMulP tbs_matMulP.2 tbs_matMulP.1 L
theorem tb_encCoreP (L : ℕ) : Prog.timeBound encCoreP L ≤ 2 ^ 40 * (L + 1) ^ 32 :=
  tb_le' noGrow_encCoreP tbs_encCoreP.2 tbs_encCoreP.1 L

/-! ### `Setup` -/

/-- A closed form above `timeC0`. -/
def timeC0L (oB oS d N K M : ℕ) : ℕ :=
  (2 * oB + 1) * (4 * M + 12) + (2 * (d * (N * K)) + 1) * (4 * M + 12) +
    (2 * oS + 1) * (4 * M + 12) + (2 * (N * K) + 1) * (4 * M + 12) +
    (2 * (d * (N * K)) + 1) * (4 * M + 12) + (2 * K + 1) * (4 * M + 12) +
    (2 * N + 1) * (4 * M + 12) + (2 * 1 + 1) * (4 * M + 12) + (2 * 1 + 1) * (4 * M + 12) +
    (2 * d + 1) * (4 * M + 12) + (2 * (1 * d * (N * K)) + 1) * (4 * M + 12) +
    (2 * (1 * d * N) + 1) * (4 * M + 12) +
    2 ^ 20 * (M + 1) ^ 8 + 2 ^ 20 * (M + 1) ^ 8 + 2 ^ 30 * (M + 1) ^ 16 +
    2 ^ 20 * (M + 1) ^ 8 + (2 * (M + 1) + 3) +
    (c0Tapes.length * (2 * (M + 1 + 1) + 3) + (2 * (M + 1 + 1) + 3))

theorem timeC0_le (oB oS d N K M : ℕ) : timeC0 oB oS d N K M ≤ timeC0L oB oS d N K M := by
  unfold timeC0 timeC0L
  have := tb_splitP M; have := tb_matMulP M; have := tb_addRWP M
  omega

/-- A closed form above `timeB1`. -/
def timeB1L (N K k M : ℕ) : ℕ :=
  (2 * K + 1) * (4 * M + 12) + (2 * N + 1) * (4 * M + 12) + (2 * (N * K) + 1) * (4 * M + 12) +
    (2 * k + 1) * (4 * M + 12) + (2 * rowL N K k + 1) * (4 * M + 12) +
    (2 * rowL N K k + 1) * (4 * M + 12) + (2 * (1 * (2 * k) * N) + 1) * (4 * M + 12) +
    (2 * (N * K + rowL N K k + rowL N K k) + 1) * (4 * M + 12) +
    2 ^ 20 * (M + 1) ^ 8 + 2 ^ 20 * (M + 1) ^ 8 + 2 ^ 20 * (M + 1) ^ 8 +
    (2 * (N * K - 1) + 1) * (4 * M + 12) + (2 * (M + 1) + 3) +
    2 ^ 20 * (M + 1 + 1) ^ 8 +
    (b1Tapes.length * (2 * (M + 1 + 1) + 3) + (2 * (M + 1 + 1) + 3))

theorem timeB1_le (N K k M : ℕ) : timeB1 N K k M ≤ timeB1L N K k M := by
  unfold timeB1 timeB1L
  have := tb_splitP M; have := tb_gadP M; have := tb_subRWP M; have := tb_joinP (M + 1)
  omega

/-- `detT` with the closed forms of `timeC0`, `timeB1`. -/
def detTL (N K k M : ℕ) : ℕ :=
  let A1 := apGS M
  let A2 := apGS A1
  let C1 := A2 + 1
  let A3 := apGS C1
  let B1 := A3 + 1
  let A4 := apGS B1
  let A5 := apGS A4
  let A6 := apGS A5
  let F1 := apGS A6
  let A7 := apGS F1
  let A8 := apGS A7
  (2 * (M + 1) + 3) + (((2 * (M + 1) + 3) + appT M) + (((2 * (A1 + 1) + 3) + appT A1) +
    (timeC0L 0 (2 * k * (N * K)) (2 * k) N K A2 + ((2 * (C1 + 1) + 3) + ((2 * (C1 + 1) + 3) +
    (((2 * (C1 + 1) + 3) + appT C1) + (timeB1L N K k A3 + ((2 * (B1 + 1) + 3) + ((2 * (B1 + 1) + 3) +
    (((2 * (B1 + 1) + 3) + appT B1) + (((2 * (A4 + 1) + 3) + appT A4) +
    (((2 * (A5 + 1) + 3) + appT A5) + (appT A6 + (((2 * (F1 + 1) + 3) + appT F1) +
    (((2 * (A7 + 1) + 3) + appT A7) + appT A8)))))))))))))))

theorem detT_le (N K k M : ℕ) : detT N K k M ≤ detTL N K k M := by
  unfold detT detTL
  have h1 := timeC0_le 0 (2 * k * (N * K)) (2 * k) N K (apGS (apGS M))
  have h2 := timeB1_le N K k (apGS (apGS (apGS M) + 1))
  dsimp only
  omega

/-- The linear forms of the coins' clock. -/
abbrev linC (n x : ℕ) : ℕ := (8 * n + 8 + n * (6 + 3)) * (x + x + (n * 1 + n * 0 + 3 + 3))

/-- The linear forms of a counted sampler's clock. -/
abbrev linX (a s w E n x : ℕ) : ℕ :=
  (8 * n + 8 + n * (w + 3)) * (x + x + (n * a + n * s + E + 3))

/-- `setupST` with the linear bounds of the samplers. -/
def setupSTL {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (a s w E M : ℕ) : ℕ :=
  let M1 := M + nRowD N K c.d * 1 + nRowD N K c.d * 0
  let M2 := M1 + nRowC N K k * 1 + nRowC N K k * 0
  let M3 := M2 + N * a + N * s
  let M4 := M3 + (Enum.list (α := RingBTVW.Fresh.Col k)).length * N * a +
    (Enum.list (α := RingBTVW.Fresh.Col k)).length * N * s
  let M5 := M4 + nBj (N := N) hk * 1 + nBj (N := N) hk * 0
  linC (nRowD N K c.d) M + (linC (nRowC N K k) M1 + (linX a s w E N M2 +
    (linX a s w E ((Enum.list (α := RingBTVW.Fresh.Col k)).length * N) M3 +
    (linC (nBj (N := N) hk) M4 + linC (N * K) M5))))

theorem setupST_le {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) {Bχ : Bnd} {w E : ℕ}
    (hB : Lin Bχ.T w E) (M : ℕ) : setupST hk c Bχ M ≤ setupSTL hk c Bχ.a Bχ.s w E M := by
  unfold setupST setupSTL
  exact Nat.add_le_add (lin_bCoins _ _ _) (Nat.add_le_add (lin_bCoins _ _ _)
    (Nat.add_le_add (lin_Bcount hB _ _ _) (Nat.add_le_add (lin_Bcount hB _ _ _)
      (Nat.add_le_add (lin_bCoins _ _ _) (lin_bCoins _ _ _)))))

theorem chiB : chiSamplerP.B = bChi := rfl

end AdvancedEncryption.RingBTVW.Prog

namespace AdvancedEncryption.RingBTVW.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.RingBTVW.Params

theorem detTL_mono (N K k : ℕ) {M M' : ℕ} (h : M ≤ M') : detTL N K k M ≤ detTL N K k M' := by
  simp only [detTL, timeC0L, timeB1L, appT, forT, loopT, stepT, apGS]
  gcongr

theorem detG_le (M : ℕ) : detG M ≤ 2 ^ 30 * (M + 1) := by
  simp only [detG, apGS]; omega

/-! ### `Enc` -/

/-- `encST` with linear bounds of the samplers (`a, s`: the shape of the χ sampler). -/
def encSTL {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (a s w E wB EB wF EF M : ℕ) : ℕ :=
  let S1 := M + N * K * 1 + N * K * 0
  let S2 := S1 + (Enum.list (α := Fin c.d)).length * N * a + (Enum.list (α := Fin c.d)).length * N * s
  let S3 := S2 + N * a + N * s
  let S4 := S3 + (Enum.list (α := RingBTVW.Fresh.Col k)).length * N * a +
    (Enum.list (α := RingBTVW.Fresh.Col k)).length * N * s
  let S5 := S4 + (Enum.list (α := RingBTVW.Fresh.Col k)).length * N * a +
    (Enum.list (α := RingBTVW.Fresh.Col k)).length * N * s
  let S6 := S5 + nR hk c * (bEntB N K).a + nR hk c * (bEntB N K).s
  let S7 := S6 + nE (N := N) hk * (bEntF K c.w).a + nE (N := N) hk * (bEntF K c.w).s
  linC (N * K) M + (linX a s w E ((Enum.list (α := Fin c.d)).length * N) S1 +
    (linX a s w E N S2 + (linX a s w E ((Enum.list (α := RingBTVW.Fresh.Col k)).length * N) S3 +
    (linX a s w E ((Enum.list (α := RingBTVW.Fresh.Col k)).length * N) S4 +
    (linX (bEntB N K).a (bEntB N K).s wB EB (nR hk c) S5 +
    (linX (bEntF K c.w).a (bEntF K c.w).s wF EF (nE (N := N) hk) S6 + linX a s w E N S7))))))

theorem encST_le {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) {Bχ : Bnd} {w E wB EB wF EF : ℕ}
    (hB : Lin Bχ.T w E) (hEB : Lin (bEntB N K).T wB EB) (hEF : Lin (bEntF K c.w).T wF EF) (M : ℕ) :
    encST hk c Bχ M ≤ encSTL hk c Bχ.a Bχ.s w E wB EB wF EF M := by
  unfold encST encSTL
  exact Nat.add_le_add (lin_bCoins _ _ _) (Nat.add_le_add (lin_Bcount hB _ _ _)
    (Nat.add_le_add (lin_Bcount hB _ _ _) (Nat.add_le_add (lin_Bcount hB _ _ _)
      (Nat.add_le_add (lin_Bcount hB _ _ _) (Nat.add_le_add (lin_Bcount hEB _ _ _)
        (Nat.add_le_add (lin_Bcount hEF _ _ _) (lin_Bcount hB _ _ _)))))))

/-- `encS` with the shape of the χ sampler as numbers. -/
def encSN {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (a s M : ℕ) : ℕ :=
  let S1 := M + N * K * 1 + N * K * 0
  let S2 := S1 + (Enum.list (α := Fin c.d)).length * N * a + (Enum.list (α := Fin c.d)).length * N * s
  let S3 := S2 + N * a + N * s
  let S4 := S3 + (Enum.list (α := RingBTVW.Fresh.Col k)).length * N * a +
    (Enum.list (α := RingBTVW.Fresh.Col k)).length * N * s
  let S5 := S4 + (Enum.list (α := RingBTVW.Fresh.Col k)).length * N * a +
    (Enum.list (α := RingBTVW.Fresh.Col k)).length * N * s
  let S6 := S5 + nR hk c * (bEntB N K).a + nR hk c * (bEntB N K).s
  let S7 := S6 + nE (N := N) hk * (bEntF K c.w).a + nE (N := N) hk * (bEntF K c.w).s
  S7 + N * a + N * s

theorem encS_eq {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (Bχ : Bnd) (M : ℕ) :
    encS hk c Bχ M = encSN hk c Bχ.a Bχ.s M := rfl

theorem natLT_le : ∀ (l : List (Fin 124 × ℕ)) (M X : ℕ), (∀ p ∈ l, p.2 ≤ X) →
    natLT l M ≤ l.length * ((2 * X + 1) * (4 * M + 12)) + (2 * (M + 1) + 3)
  | [], M, X, _ => by simp [natLT]
  | p :: l, M, X, h => by
    have h1 : (2 * p.2 + 1) * (4 * M + 12) ≤ (2 * X + 1) * (4 * M + 12) :=
      Nat.mul_le_mul_right _ (by have := h p (by simp); omega)
    have h2 := natLT_le l M X (fun q hq => h q (by simp [hq]))
    simp only [natLT, List.length_cons]
    nlinarith

theorem lin_bEntB (N K : ℕ) : Lin (bEntB N K).T (6 + (8 * (N * K - 1) + 8 + (N * K - 1) * (2 + 3)))
    (3 + ((N * K - 1) * 1 + (N * K - 1) * 0 + 3 + 3) + 1 + 0) :=
  lin_Bseq lin_bCoin (lin_bZeros _)

theorem lin_bEntF (K w : ℕ) : Lin (bEntF K w).T ((8 * min w K + 8 + min w K * (6 + 3)) +
    (8 * (K - w) + 8 + (K - w) * (2 + 3)))
    ((min w K * 1 + min w K * 0 + 3 + 3) + ((K - w) * 1 + (K - w) * 0 + 3 + 3) + min w K * 1 +
      min w K * 0) :=
  lin_Bseq (lin_bCoins _) (lin_bZeros _)

theorem bEntB_as (N K : ℕ) : (bEntB N K).a = 1 + (N * K - 1) * 1 ∧
    (bEntB N K).s = 0 + (N * K - 1) * 0 := ⟨rfl, rfl⟩
theorem bEntF_as (K w : ℕ) : (bEntF K w).a = min w K * 1 + (K - w) * 1 ∧
    (bEntF K w).s = min w K * 0 + (K - w) * 0 := ⟨rfl, rfl⟩
theorem linX_le {a s w E n x A W E' C X : ℕ} (ha : a ≤ A) (hs : s ≤ A) (hw : w ≤ W) (hE : E ≤ E')
    (hn : n ≤ C) (hx : x ≤ X) : linX a s w E n x ≤ linX A A W E' C X := by
  unfold linX; gcongr

theorem linC_le {n x A W E' C X : ℕ} (hn : n ≤ C) (hx : x ≤ X) (h1 : 1 ≤ A) (h6 : 6 ≤ W)
    (h3 : 3 ≤ E') : linC n x ≤ linX A A W E' C X := by
  unfold linC linX
  have : n * 0 ≤ C * A := by simp
  gcongr

section EncGen

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The counts of `Enc`'s samplers are below `C`, their shapes below `A`. -/
structure EncCounts (a s C A : ℕ) : Prop where
  nk : N * K ≤ C
  nd : (Enum.list (α := Fin c.d)).length * N ≤ C
  n : N ≤ C
  ncol : (Enum.list (α := RingBTVW.Fresh.Col k)).length * N ≤ C
  nr : nR hk c ≤ C
  ne : nE (N := N) hk ≤ C
  a : a ≤ A
  s : s ≤ A
  one : 1 ≤ A
  ba : (bEntB N K).a ≤ A
  bs : (bEntB N K).s ≤ A
  fa : (bEntF K c.w).a ≤ A
  fs : (bEntF K c.w).s ≤ A

theorem encSN_le {a s C A : ℕ} (h : EncCounts hk c a s C A) (M : ℕ) :
    encSN hk c a s M ≤ M + 20 * (C * A) := by
  have m := fun {x y : ℕ} (hx : x ≤ C) (hy : y ≤ A) => Nat.mul_le_mul hx hy
  have := m h.nk h.one; have := m h.nk (Nat.zero_le A)
  have := m h.nd h.a; have := m h.nd h.s; have := m h.n h.a; have := m h.n h.s
  have := m h.ncol h.a; have := m h.ncol h.s; have := m h.nr h.ba; have := m h.nr h.bs
  have := m h.ne h.fa; have := m h.ne h.fs
  dsimp only [encSN]
  omega

theorem encSTL_le {a s w E wB EB wF EF C A W E' : ℕ} (h : EncCounts hk c a s C A)
    (hw : w ≤ W) (hwB : wB ≤ W) (hwF : wF ≤ W) (h6 : 6 ≤ W) (hE : E ≤ E') (hEB : EB ≤ E')
    (hEF : EF ≤ E') (h3 : 3 ≤ E') (M : ℕ) :
    encSTL hk c a s w E wB EB wF EF M ≤ 8 * linX A A W E' C (M + 20 * (C * A)) := by
  have m := fun {x y : ℕ} (hx : x ≤ C) (hy : y ≤ A) => Nat.mul_le_mul hx hy
  have := m h.nk h.one; have := m h.nk (Nat.zero_le A)
  have := m h.nd h.a; have := m h.nd h.s; have := m h.n h.a; have := m h.n h.s
  have := m h.ncol h.a; have := m h.ncol h.s; have := m h.nr h.ba; have := m h.nr h.bs
  have := m h.ne h.fa; have := m h.ne h.fs
  dsimp only [encSTL]
  have e := fun {x : ℕ} (hx : x ≤ M + 20 * (C * A)) => hx
  refine le_trans (Nat.add_le_add (linC_le h.nk (e (by omega)) h.one h6 h3)
    (Nat.add_le_add (linX_le h.a h.s hw hE h.nd (e (by omega)))
    (Nat.add_le_add (linX_le h.a h.s hw hE h.n (e (by omega)))
    (Nat.add_le_add (linX_le h.a h.s hw hE h.ncol (e (by omega)))
    (Nat.add_le_add (linX_le h.a h.s hw hE h.ncol (e (by omega)))
    (Nat.add_le_add (linX_le h.ba h.bs hwB hEB h.nr (e (by omega)))
    (Nat.add_le_add (linX_le h.fa h.fs hwF hEF h.ne (e (by omega)))
      (linX_le h.a h.s hw hE h.n (e (by omega)))))))))) (le_of_eq (by ring))

end EncGen

theorem ufCT_le (n M : ℕ) : ufCT n M ≤ (2 * n + 1) * (4 * M + 12) + 100 * (M + 1) ^ 2 := by
  unfold ufCT forT loopT
  nlinarith

theorem dropCT_le (n M : ℕ) : dropCT n M ≤ (2 * n + 1) * (4 * M + 12) + 100 * (M + 1) ^ 2 := by
  unfold dropCT forT loopT
  nlinarith

theorem appT_le (M : ℕ) : appT M ≤ 200 * (M + 1) ^ 2 := by
  unfold appT forT loopT stepT
  nlinarith

theorem parseEG_eq (M : ℕ) : parseEG M = 64 * M := by
  simp only [parseEG]; ring

section EncGen2

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

theorem parseET_le (C M : ℕ) (h0 : 2 * RingBTVW.pw.length + 1 ≤ C)
    (h1 : (Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K)) ≤ C)
    (h2 : (Enum.list (α := Fin 1)).length * ((Enum.list (α := TrapCol k)).length * (N * K)) ≤ C)
    (h3 : (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).length *
      ((Enum.list (α := Fin 1)).length * ((Enum.list (α := RingBTVW.Fresh.Col k)).length * (N * K))) ≤ C)
    (h4 : N * K ≤ C) (h5 : nA ≤ C) :
    parseET hk c M ≤ 7 * ((2 * C + 1) * (4 * (64 * M) + 12) + 100 * (64 * M + 1) ^ 2) +
      2 * (2 * (64 * M + 1) + 3) := by
  have b := fun (n P : ℕ) (hn : n ≤ C) (hP : P ≤ 64 * M) =>
    (ufCT_le n P).trans (Nat.add_le_add (Nat.mul_le_mul (show 2 * n + 1 ≤ 2 * C + 1 by omega)
      (show 4 * P + 12 ≤ 4 * (64 * M) + 12 by omega))
      (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left (show P + 1 ≤ 64 * M + 1 by omega) 2)))
  have d := (dropCT_le (2 * RingBTVW.pw.length + 1) M).trans (Nat.add_le_add
    (Nat.mul_le_mul (show 2 * (2 * RingBTVW.pw.length + 1) + 1 ≤ 2 * C + 1 by omega)
      (show 4 * M + 12 ≤ 4 * (64 * M) + 12 by omega))
    (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left (show M + 1 ≤ 64 * M + 1 by omega) 2)))
  dsimp only [parseET]
  have := b _ (M + M * 0) h1 (by omega)
  have := b _ (M + M * 0 + (M + M * 0) * 1) h2 (by omega)
  have := b _ (M + M * 0 + (M + M * 0) * 1 + (M + M * 0 + (M + M * 0) * 1) * 1) h3 (by omega)
  have := b _ (M + M * 0 + (M + M * 0) * 1 + (M + M * 0 + (M + M * 0) * 1) * 1 +
    (M + M * 0 + (M + M * 0) * 1 + (M + M * 0 + (M + M * 0) * 1) * 1) * 1) h4 (by omega)
  have := b nA (M + M * 0 + (M + M * 0) * 1 + (M + M * 0 + (M + M * 0) * 1) * 1 +
    (M + M * 0 + (M + M * 0) * 1 + (M + M * 0 + (M + M * 0) * 1) * 1) * 1 +
    (M + M * 0 + (M + M * 0) * 1 + (M + M * 0 + (M + M * 0) * 1) * 1 +
    (M + M * 0 + (M + M * 0) * 1 + (M + M * 0 + (M + M * 0) * 1) * 1) * 1) * 1) h5 (by omega)
  have := b 1 (M + M * 0 + (M + M * 0) * 1 + (M + M * 0 + (M + M * 0) * 1) * 1 +
    (M + M * 0 + (M + M * 0) * 1 + (M + M * 0 + (M + M * 0) * 1) * 1) * 1 +
    (M + M * 0 + (M + M * 0) * 1 + (M + M * 0 + (M + M * 0) * 1) * 1 +
    (M + M * 0 + (M + M * 0) * 1 + (M + M * 0 + (M + M * 0) * 1) * 1) * 1) * 1 +
    (M + M * 0 + (M + M * 0) * 1 + (M + M * 0 + (M + M * 0) * 1) * 1 +
    (M + M * 0 + (M + M * 0) * 1 + (M + M * 0 + (M + M * 0) * 1) * 1) * 1 +
    (M + M * 0 + (M + M * 0) * 1 + (M + M * 0 + (M + M * 0) * 1) * 1 +
    (M + M * 0 + (M + M * 0) * 1 + (M + M * 0 + (M + M * 0) * 1) * 1) * 1) * 1) * 1) (by omega)
    (by omega)
  omega

end EncGen2

end AdvancedEncryption.RingBTVW.Prog
