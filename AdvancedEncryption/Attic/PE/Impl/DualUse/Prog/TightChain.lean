import PE.Impl.DualUse.Prog.TightSetup
import PE.Impl.DualUse.Prog.CompCost

/-!
# The per-tape bounds of `Setup`, step by step

Symbolic stores over the variables `ρ = [0, N, K, k, d, n_in, G₀, a_χ, s_χ, n_A]` (`n_in` the input
length, `G₀` a bound of the thresholds of the χ sampler, `a_χ`, `s_χ` its shape, `n_A` the number of
attribute bits): the six framed
samplers (`σS1 … σS6`), then the seventeen steps of `setupDet` (`D1 … D17`). Every side condition is
a closed check (`chk_*`, `decide +kernel`).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg SigabaNeo.Tape.Sym

namespace TightS

/-- The monomial `c · N^a K^b k^c d^e n^f G₀^g a_χ^h s_χ^i n_A^j`. -/
def mq (c : ℕ) (e : List ℕ) : Poly := [(0 :: e, c)]

def pN : Poly := mq 1 [1]
def pK : Poly := mq 1 [0, 1]
def pk : Poly := mq 1 [0, 0, 1]
def pNK : Poly := mq 1 [1, 1]
def pdNK : Poly := mq 1 [1, 1, 0, 1]
def p2kNK : Poly := mq 2 [1, 1, 1]
def p2kN : Poly := mq 2 [1, 0, 1]
def pNXa : Poly := mq 1 [1, 0, 0, 0, 0, 0, 1]
def p2kNXa : Poly := mq 2 [1, 0, 1, 0, 0, 0, 1]
def pNXs : Poly := mq 1 [1, 0, 0, 0, 0, 0, 0, 1]
def p2kNXs : Poly := mq 2 [1, 0, 1, 0, 0, 0, 0, 1]
def pBj : Poly := mq 8 [2, 1, 3, 0, 0, 0, 0, 0, 1]
def vnI : Poly := mq 1 [0, 0, 0, 0, 1]
def vG0 : Poly := mq 1 [0, 0, 0, 0, 0, 1]

/-- The scratch bound of the samplers: `G₀` and every count. -/
def Sp : Poly := pAdd (pAdd (pAdd (pAdd (pAdd (pAdd vG0 pdNK) p2kNK) pN) p2kN) pBj) pNK
def S3 : Poly := pAdd Sp pNXs
def S4 : Poly := pAdd S3 p2kNXs

/-- A sampler appending `x` to tape `o`, its scratch at `S`. -/
def smpA (σ : Asg) (o : ℕ) (x S : Poly) : Asg :=
  aSet (aSet (aSet (aSet (aSet (aSet (aSet σ o x) 93 S) 2 S) 3 S) 4 S) 5 S) 6 S

def σS0 : Asg := aSet (List.replicate 96 []) 94 vnI
def σS1 : Asg := smpA σS0 82 pdNK Sp
def σS2 : Asg := smpA σS1 83 p2kNK Sp
def σS3 : Asg := smpA σS2 84 pNXa S3
def σS4 : Asg := smpA σS3 85 p2kNXa S4
def σS5 : Asg := smpA σS4 86 pBj S4
def σS6 : Asg := aSet (smpA σS5 87 pNK S4) 4 pNK

/-- The side conditions of a sampler. -/
def smpChk (e : Fin 7 ↪ Fin 96) (σ σ' : Asg) (Sp pa ps : Poly) : Bool :=
  ((List.finRange 7).all fun j => j == 0 ||
      (pLe (aGet σ (e j).val) Sp && pLe (pAdd Sp ps) (aGet σ' (e j).val))) &&
    pLe (pAdd (aGet σ (e 0).val) pa) (aGet σ' (e 0).val) && aLe σ σ'

def smpChk4 (e : Fin 7 ↪ Fin 96) (σ σ' : Asg) (Sp pa ps p4 : Poly) : Bool :=
  ((List.finRange 7).all fun j => j == 0 ||
      (pLe (aGet σ (e j).val) Sp && (j == 4 || pLe (pAdd Sp ps) (aGet σ' (e j).val)))) &&
    pLe (pAdd (aGet σ (e 0).val) pa) (aGet σ' (e 0).val) && pLe p4 (aGet σ' (e 4).val) &&
    (List.finRange 96).all (fun t => t == e 4 || pLe (aGet σ t.val) (aGet σ' t.val))

set_option maxRecDepth 100000 in
theorem chk_smp : smpChk eB0 σS0 σS1 Sp pdNK [] = true ∧ smpChk eAa σS1 σS2 Sp p2kNK [] = true ∧
    smpChk eTt σS2 σS3 Sp pNXa pNXs = true ∧ smpChk eEe σS3 σS4 S3 p2kNXa p2kNXs = true ∧
    smpChk eBj σS4 σS5 S4 pBj [] = true ∧ smpChk4 ePp σS5 σS6 S4 pNK [] pNK = true := by
  decide +kernel

/-! ### The deterministic part -/

/-- The coefficient of a monomial. -/
def coeffOf (m : Mono) (p : Poly) : ℕ := ((p.find? fun t => mBeq t.1 m).map Prod.snd).getD 0

/-- The coefficientwise maximum. -/
def pMax (p q : Poly) : Poly :=
  q.foldl (fun acc t => if t.2 ≤ coeffOf t.1 acc then acc else addTerm (t.1, t.2 - coeffOf t.1 acc) acc) p

/-- A bound of every tape. -/
def aMax (σ : Asg) : Poly := σ.foldl pMax []

/-- The bound of an append of tape `s` to tape `0`. -/
def appM (σ : Asg) (s : ℕ) : Poly := pMax (aMax σ) (pAdd (aGet σ 0) (aGet σ s))

/-- The bound of a framed append of tape `0` to tape `91`. -/
def frM (σ : Asg) : Poly := pMax (aMax σ) (pAdd (aGet σ 91) (pAdd (pMul (pC 2) (aGet σ 0)) (pC 1)))

/-- The checks of an append, a framed append, a copy. -/
def appChk (σ : Asg) (s : ℕ) : Bool := allLe σ (appM σ s) 96 && pLe (pAdd (aGet σ 0) (aGet σ s)) (appM σ s)
def frChk (σ : Asg) : Bool :=
  allLe σ (frM σ) 96 && pLe (pAdd (aGet σ 91) (pAdd (pMul (pC 2) (aGet σ 0)) (pC 1))) (frM σ)

/-- The variable `i` (`N`, `K`, `k` are `1`, `2`, `3`). -/
def vq (i : ℕ) : Poly := [(List.replicate i 0 ++ [1], 1)]

/-- The variables of `c0P` at the store `σ`: the bulk `Gp`, `N`, `K`, `k`, tapes `0` and `4`. -/
def θC0 (Gp : Poly) (σ : Asg) : List Poly := [[], Gp, vq 1, vq 2, vq 3, aGet σ 0, aGet σ 4]
def θB1 (Gp : Poly) (σ : Asg) : List Poly := [[], Gp, vq 1, vq 2, vq 3, aGet σ 0, aGet σ 4, aGet σ 9]

/-- The check of a framed block with a summary (`fcall`), without the program. -/
def fcallChk {m : ℕ} (e : Fin m ↪ Fin 96) (τ τ' : Asg) (c : Poly) (θ : List Poly) (σ claim : Asg)
    (cc : Poly) : Bool :=
  ((List.finRange m).all fun j => pLe (aGet σ (e j).val) (pSubst θ (aGet τ j.val))) &&
    aLe ((setMany e (τ'.map (pSubst θ)) σ (List.finRange m)).take claim.length) claim &&
    pLe (pSubst θ c) cc

/-- The cost of the templates of `c0P` as a polynomial in its variables. -/
def natC0P : Poly :=
  pMul [([], 16), ([0, 0, 1, 1, 1], 20), ([0, 0, 1, 1], 2), ([0, 0, 0, 1], 2), ([0, 0, 1], 2),
    ([0, 0, 0, 0, 1], 4), ([0, 0, 1, 0, 1], 4)] (pAdd (pMul (pC 4) TightP.Tb) (pC 12))
def cC0P : Poly := pAdd natC0P TightC0.cRest

/-- The cost of the templates of `b1P` as a polynomial in its variables. -/
def natB1P : Poly :=
  pAdd (pMul [([], 9), ([0, 0, 0, 1], 2), ([0, 0, 1], 2), ([0, 0, 1, 1], 6), ([0, 0, 0, 0, 1], 2),
    ([0, 0, 1, 1, 1], 16), ([0, 0, 1, 0, 1], 4)] (pAdd (pMul (pC 4) TightB1.Tb1) (pC 12)))
    (pAdd (pMul (pC 2) TightB1.Tb1) (pC 5))
def cB1P : Poly := pAdd natB1P (pAdd TightB1.cRest1 TightB1.cRest2)

def D1 : Asg := aSet σS6 0 (aGet σS6 83)
def D2 : Asg := appA D1 84
def D3 : Asg := appA D2 85
def G4 : Poly := S4
def D4 : Asg := setMany e82 (TightC0.claim.map (pSubst (θC0 G4 D3))) D3 (List.finRange 82)
def D5 : Asg := aSet D4 92 (aGet D4 0)
def D6 : Asg := aSet D5 0 (aGet D5 83)
def D7 : Asg := appA D6 92
def G8 : Poly := pSubst (θC0 G4 D3) TightP.Tb
def D8 : Asg := setMany e82 (TightB1.claim.map (pSubst (θB1 G8 D7))) D7 (List.finRange 82)
def D9 : Asg := aSet D8 92 (aGet D8 0)
def D10 : Asg := aSet D9 0 (aGet D9 82)
def D11 : Asg := appA D10 92
def D12 : Asg := appA D11 86
def D13 : Asg := appA D12 87
def D14 : Asg := frA D13
def D15 : Asg := appA D14 85
def D16 : Asg := appA D15 84
def D17 : Asg := frA D16

set_option maxRecDepth 100000 in
theorem chk_copy : allLe σS6 (aMax σS6) 96 = true ∧ allLe D4 (aMax D4) 96 = true ∧
    allLe D5 (aMax D5) 96 = true ∧ allLe D8 (aMax D8) 96 = true ∧ allLe D9 (aMax D9) 96 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chk_app : appChk D1 84 = true ∧ appChk D2 85 = true ∧ appChk D6 92 = true ∧
    appChk D10 92 = true ∧ appChk D11 86 = true ∧ appChk D12 87 = true ∧ appChk D14 85 = true ∧
    appChk D15 84 = true ∧ frChk D13 = true ∧ frChk D16 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chk_c0 : fcallChk e82 TightC0.σ0 TightC0.claim cC0P (θC0 G4 D3) D3 D4
    (pSubst (θC0 G4 D3) cC0P) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chk_b1 : fcallChk e82 TightB1.σ0 TightB1.claim cB1P (θB1 G8 D7) D7 D8
    (pSubst (θB1 G8 D7) cB1P) = true := by
  decide +kernel

theorem D_length : D4.length = 96 ∧ D8.length = 96 := by decide +kernel

/-! ### Summaries of the framed blocks -/

theorem pEval_vq (ρ : List ℕ) (i : ℕ) : pEval ρ (vq i) = ρ.getD i 0 := by
  induction i generalizing ρ with
  | zero => cases ρ <;> simp [vq, pEval, mEval]
  | succ i ih =>
    cases ρ with
    | nil =>
      have := ih []
      simp only [vq, pEval, mEval, List.replicate_succ, List.cons_append] at this ⊢
      simpa using this
    | cons a ρ =>
      have := ih ρ
      simp only [vq, pEval, mEval, List.replicate_succ, List.cons_append] at this ⊢
      simpa using this

/-- The variables `1`, `2`, `3` are `N`, `K`, `k`. -/
def HN (N K k : ℕ) (ρ : List ℕ) : Prop := ρ.getD 1 0 = N ∧ ρ.getD 2 0 = K ∧ ρ.getD 3 0 = k

theorem natC0_le (N K k T : ℕ) :
    natC0 N K k T ≤ (16 + 20 * (k * (N * K)) + 2 * (N * K) + 2 * K + 2 * N + 4 * k + 4 * (k * N)) *
      (4 * T + 12) := by
  have e : natC0 N K k T = (16 + 16 * (k * (N * K)) + 2 * (N * K) + 2 * K + 2 * N + 4 * k +
      4 * (k * N)) * (4 * T + 12) := by unfold natC0; ring
  rw [e]
  exact Nat.mul_le_mul_right _ (by omega)

theorem hS_c0 {N K k : ℕ} (Gp : Poly) (σ : Asg) : ∀ ρ, HN N K k ρ →
    XSoundAt (c0P 0 (2 * k * (N * K)) (2 * k) N K) TightC0.σ0 TightC0.claim cC0P
      ((θC0 Gp σ).map (pEval ρ)) := by
  intro ρ hH ℓ hℓ
  obtain ⟨h1, h2, h3⟩ := hH
  have e : (θC0 Gp σ).map (pEval ρ) =
      TightP.ρv (pEval ρ Gp) N K k (pEval ρ (aGet σ 0)) (pEval ρ (aGet σ 4)) := by
    simp only [θC0, TightP.ρv, List.map_cons, List.map_nil, pEval_vq, h1, h2, h3, pEval_nil]
  rw [e] at hℓ ⊢
  obtain ⟨ht, hl⟩ := vb_c0P (pEval ρ Gp) N K k _ _ ℓ hℓ
  refine ⟨hl, ht.trans ?_⟩
  simp only [cC0P, pEval_pAdd]
  refine Nat.add_le_add_right ((natC0_le _ _ _ _).trans (le_of_eq ?_)) _
  simp only [natC0P, pEval_pMul, pEval_pAdd, pEval_pC, TightP.pEval_Tb]
  simp [pEval, mEval, TightP.ρv]
  ring

theorem natB1_le (N K k T : ℕ) :
    natB1 N K k T ≤ (9 + 2 * K + 2 * N + 6 * (N * K) + 2 * k + 16 * (k * (N * K)) + 4 * (k * N)) *
      (4 * T + 12) + (2 * T + 5) := by
  have e : natB1 N K k T = (9 + 2 * K + 2 * N + 6 * (N * K) + 2 * k + 16 * (k * (N * K)) +
      4 * (k * N)) * (4 * T + 12) + (2 * T + 5) := by unfold natB1; ring
  omega

theorem hS_b1 {N K k : ℕ} (Gp : Poly) (σ : Asg) : ∀ ρ, HN N K k ρ →
    XSoundAt (b1P N K k) TightB1.σ0 TightB1.claim cB1P ((θB1 Gp σ).map (pEval ρ)) := by
  intro ρ hH ℓ hℓ
  obtain ⟨h1, h2, h3⟩ := hH
  have e : (θB1 Gp σ).map (pEval ρ) = TightB1.ρ1 (pEval ρ Gp) N K k (pEval ρ (aGet σ 0))
      (pEval ρ (aGet σ 4)) (pEval ρ (aGet σ 9)) := by
    simp only [θB1, TightB1.ρ1, List.map_cons, List.map_nil, pEval_vq, h1, h2, h3, pEval_nil]
  rw [e] at hℓ ⊢
  obtain ⟨ht, hl⟩ := vb_b1P (pEval ρ Gp) N K k _ _ _ ℓ hℓ
  refine ⟨hl, ht.trans ?_⟩
  simp only [cB1P, pEval_pAdd]
  refine Nat.add_le_add_right ((natB1_le _ _ _ _).trans (le_of_eq ?_)) _
  simp only [natB1P, pEval_pMul, pEval_pAdd, pEval_pC, TightB1.pEval_Tb1]
  simp [pEval, mEval, TightB1.ρ1]
  ring

theorem xcheck_fcall {H : List ℕ → Prop} {m : ℕ} (e : Fin m ↪ Fin 96) (p : XProg m) (τ τ' : Asg)
    (c : Poly) (θ : List Poly) (hS : ∀ ρ, H ρ → XSoundAt p τ τ' c (θ.map (pEval ρ)))
    (σ claim : Asg) (cc : Poly) (h : fcallChk e τ τ' c θ σ claim cc = true) :
    xcheck 8 (XAst.fcall (H := H) e p τ τ' c θ hS) σ claim cc = true := by
  unfold fcallChk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [xcheck, XAst.xabs, h1, if_true, h2, h3, Bool.and_self]

/-! ### The chain -/

section Chain

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (X : ChiSampler c)

/-- The variables at a configuration. -/
def ρS (nI G0 : ℕ) : List ℕ := [0, N, K, k, c.d, nI, G0, X.B.a, X.B.s, nA]

theorem hN_ρS (nI G0 : ℕ) : HN N K k (ρS c X nI G0) := ⟨rfl, rfl, rfl⟩

theorem pEval_Sp (nI G0 : ℕ) : pEval (ρS c X nI G0) Sp =
    G0 + c.d * (N * K) + 2 * k * (N * K) + N + 2 * k * N + 8 * (N ^ 2 * K * k ^ 3 * nA) + N * K := by
  simp [Sp, ρS, pN, pNK, pdNK, p2kNK, p2kN, pBj, vG0, mq, pEval, mEval]; try ring

theorem pEval_S3 (nI G0 : ℕ) : pEval (ρS c X nI G0) S3 =
    pEval (ρS c X nI G0) Sp + N * X.B.s := by
  simp [S3, ρS, pNXs, mq, pEval, mEval]; try ring

theorem pEval_S4 (nI G0 : ℕ) : pEval (ρS c X nI G0) S4 =
    pEval (ρS c X nI G0) Sp + N * X.B.s + 2 * k * N * X.B.s := by
  simp [S4, S3, ρS, pNXs, p2kNXs, mq, pEval, mEval]; try ring

theorem nRowD_eq : nRowD N K c.d = c.d * (N * K) := by simp [nRowD, len_fin]
theorem nRowC_eq : nRowC N K k = 2 * k * (N * K) := by simp [nRowC, len_fin, len_col]
theorem nBj_eq : nBj (N := N) hk = 8 * (N ^ 2 * K * k ^ 3 * nA) := by
  have hA : (Enum.list (α := (Sdw (N := N) hk).Attr)).length = nA := len_Attr hk
  simp only [nBj, nRowC, Enum.length_prod, len_fin, len_col, hA, len_Index]; ring
theorem nCol_eq : (Enum.list (α := RingBTVW.Col k)).length * N = 2 * k * N := by rw [len_col]

/-- The cost of the deterministic part of `Setup` (`ρ` the variables). -/
def detCostT (ρ : List ℕ) : ℕ :=
  2 * (pEval ρ (aMax σS6) + 1) + 3 +
  (2 * pEval ρ (appM D1 84) + 3 + appT' (pEval ρ (appM D1 84)) (bnd ρ D1 (84 : Fin 96)) +
  (2 * pEval ρ (appM D2 85) + 3 + appT' (pEval ρ (appM D2 85)) (bnd ρ D2 (85 : Fin 96)) +
  (pEval ρ (pSubst (θC0 G4 D3) cC0P) +
  (2 * (pEval ρ (aMax D4) + 1) + 3 +
  (2 * (pEval ρ (aMax D5) + 1) + 3 +
  (2 * pEval ρ (appM D6 92) + 3 + appT' (pEval ρ (appM D6 92)) (bnd ρ D6 (92 : Fin 96)) +
  (pEval ρ (pSubst (θB1 G8 D7) cB1P) +
  (2 * (pEval ρ (aMax D8) + 1) + 3 +
  (2 * (pEval ρ (aMax D9) + 1) + 3 +
  (2 * pEval ρ (appM D10 92) + 3 + appT' (pEval ρ (appM D10 92)) (bnd ρ D10 (92 : Fin 96)) +
  (2 * pEval ρ (appM D11 86) + 3 + appT' (pEval ρ (appM D11 86)) (bnd ρ D11 (86 : Fin 96)) +
  (2 * pEval ρ (appM D12 87) + 3 + appT' (pEval ρ (appM D12 87)) (bnd ρ D12 (87 : Fin 96)) +
  (frT' (pEval ρ (frM D13)) (bnd ρ D13 (0 : Fin 96)) +
  (2 * pEval ρ (appM D14 85) + 3 + appT' (pEval ρ (appM D14 85)) (bnd ρ D14 (85 : Fin 96)) +
  (2 * pEval ρ (appM D15 84) + 3 + appT' (pEval ρ (appM D15 84)) (bnd ρ D15 (84 : Fin 96)) +
  frT' (pEval ρ (frM D16)) (bnd ρ D16 (0 : Fin 96)))))))))))))))))

/-- The cost of `Setup`'s program. -/
def setupCostT (nI G0 : ℕ) : ℕ :=
  (bCoins (nRowD N K c.d)).T (bnd (ρS c X nI G0) σS0 (eB0 0)) (pEval (ρS c X nI G0) Sp) +
  ((bCoins (nRowC N K k)).T (bnd (ρS c X nI G0) σS1 (eAa 0)) (pEval (ρS c X nI G0) Sp) +
  ((X.B.count N).T (bnd (ρS c X nI G0) σS2 (eTt 0)) (pEval (ρS c X nI G0) Sp) +
  ((X.B.count ((Enum.list (α := RingBTVW.Col k)).length * N)).T (bnd (ρS c X nI G0) σS3 (eEe 0))
    (pEval (ρS c X nI G0) S3) +
  ((bCoins (nBj (N := N) hk)).T (bnd (ρS c X nI G0) σS4 (eBj 0)) (pEval (ρS c X nI G0) S4) +
  ((bCoins (N * K)).T (bnd (ρS c X nI G0) σS5 (ePp 0)) (pEval (ρS c X nI G0) S4) +
  detCostT (ρS c X nI G0))))))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **The per-tape bounds of `setupP`.** -/
theorem vb_setupP (nI G0 : ℕ) (hG1 : 1 ≤ G0) (hGS : X.B.S₀ ≤ G0) :
    VB (setupP hk c X) (bnd (ρS c X nI G0) σS0) (setupCostT hk c X nI G0)
      (bnd (ρS c X nI G0) D17) := by
  set ρ := ρS c X nI G0 with hρ
  have eSp := pEval_Sp c X nI G0
  have eS3 := pEval_S3 c X nI G0
  have eS4 := pEval_S4 c X nI G0
  rw [← hρ] at eSp eS3 eS4
  have hH : HN N K k ρ := hN_ρS c X nI G0
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := chk_smp
  have z : ∀ σ : Asg, ∀ o : ℕ, aGet σ o = [] → pEval ρ (aGet σ o) = 0 := fun σ o h => by
    rw [h]; rfl
  have eA : ∀ x : ℕ, x * 1 = x := fun x => Nat.mul_one x
  -- the samplers
  have s1 := vb_smpS eB0 (atbb_coinsF (nRowD N K c.d)) ρ σS0 σS1 Sp pdNK [] k1
    (by show max 1 _ ≤ _; rw [eSp, nRowD_eq]; omega)
    (by show _ * 1 ≤ _; rw [nRowD_eq]; simp [hρ, ρS, pdNK, mq, pEval, mEval]; ring_nf; omega)
    (by show _ * 0 ≤ _; simp)
  have s2 := vb_smpS eAa (atbb_coinsF (nRowC N K k)) ρ σS1 σS2 Sp p2kNK [] k2
    (by show max 1 _ ≤ _; rw [eSp, nRowC_eq]; omega)
    (by show _ * 1 ≤ _; rw [nRowC_eq]; simp [hρ, ρS, p2kNK, mq, pEval, mEval]; ring_nf; omega)
    (by show _ * 0 ≤ _; simp)
  have s3 := vb_smpS eTt (atbb_repF X.atb X.pres6 N) ρ σS2 σS3 Sp pNXa pNXs k3
    (by show max X.B.S₀ N ≤ _; rw [eSp]; omega)
    (by show N * X.B.a ≤ _; simp [hρ, ρS, pNXa, mq, pEval, mEval])
    (by show N * X.B.s ≤ _; simp [hρ, ρS, pNXs, mq, pEval, mEval])
  have s4 := vb_smpS eEe (atbb_repF X.atb X.pres6 ((Enum.list (α := RingBTVW.Col k)).length * N)) ρ σS3 σS4 S3 p2kNXa p2kNXs k4
    (by show max X.B.S₀ _ ≤ _; rw [eS3, eSp, nCol_eq]; omega)
    (by show _ * X.B.a ≤ _; rw [nCol_eq]; simp [hρ, ρS, p2kNXa, mq, pEval, mEval]; ring_nf; omega)
    (by show _ * X.B.s ≤ _; rw [nCol_eq]; simp [hρ, ρS, p2kNXs, mq, pEval, mEval]; ring_nf; omega)
  have s5 := vb_smpS eBj (atbb_coinsF (nBj (N := N) hk)) ρ σS4 σS5 S4 pBj [] k5
    (by show max 1 _ ≤ _; rw [eS4, eSp, nBj_eq hk]; omega)
    (by show _ * 1 ≤ _; rw [nBj_eq hk]; simp [hρ, ρS, pBj, mq, pEval, mEval]; ring_nf; omega)
    (by show _ * 0 ≤ _; simp)
  have s6 := vb_smpS4 ePp (N * K) ρ σS5 σS6 S4 pNK [] pNK k6
    (by show max 1 _ ≤ _; rw [eS4, eSp]; omega)
    (by show _ * 1 ≤ _; simp [hρ, ρS, pNK, mq, pEval, mEval])
    (by show _ * 0 ≤ _; simp)
    (by simp [hρ, ρS, pNK, mq, pEval, mEval])
  -- the deterministic part
  obtain ⟨q1, q4, q5, q8, q9⟩ := chk_copy
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, f1, f2⟩ := chk_app
  simp only [appChk, frChk, Bool.and_eq_true] at a1 a2 a3 a4 a5 a6 a7 a8 f1 f2
  have d1 := vb_copyS 0 83 ρ σS6 (aMax σS6) q1
  have d2 := vb_appCS 84 ρ D1 (appM D1 84) a1.1 a1.2
  have d3 := vb_appCS 85 ρ D2 (appM D2 85) a2.1 a2.2
  have d4 := vb_xcheck (XAst.fcall (H := HN N K k) e82 (c0P 0 (2 * k * (N * K)) (2 * k) N K)
    TightC0.σ0 TightC0.claim cC0P (θC0 G4 D3) (hS_c0 G4 D3))
    (xcheck_fcall _ _ _ _ _ _ _ _ _ _ chk_c0) D_length.1 ρ hH
  have d5 := vb_copyS 92 0 ρ D4 (aMax D4) q4
  have d6 := vb_copyS 0 83 ρ D5 (aMax D5) q5
  have d7 := vb_appCS 92 ρ D6 (appM D6 92) a3.1 a3.2
  have d8 := vb_xcheck (XAst.fcall (H := HN N K k) e82 (b1P N K k)
    TightB1.σ0 TightB1.claim cB1P (θB1 G8 D7) (hS_b1 G8 D7))
    (xcheck_fcall _ _ _ _ _ _ _ _ _ _ chk_b1) D_length.2 ρ hH
  have d9 := vb_copyS 92 0 ρ D8 (aMax D8) q8
  have d10 := vb_copyS 0 82 ρ D9 (aMax D9) q9
  have d11 := vb_appCS 92 ρ D10 (appM D10 92) a4.1 a4.2
  have d12 := vb_appCS 86 ρ D11 (appM D11 86) a5.1 a5.2
  have d13 := vb_appCS 87 ρ D12 (appM D12 87) a6.1 a6.2
  have d14 := vb_frS ρ D13 (frM D13) f1.1 f1.2
  have d15 := vb_appCS 85 ρ D14 (appM D14 85) a7.1 a7.2
  have d16 := vb_appCS 84 ρ D15 (appM D15 84) a8.1 a8.2
  have d17 := vb_frS ρ D16 (frM D16) f2.1 f2.2
  have h := s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (d1.seq (d2.seq (d3.seq (d4.seq
    (d5.seq (d6.seq (d7.seq (d8.seq (d9.seq (d10.seq (d11.seq (d12.seq (d13.seq (d14.seq
    (d15.seq (d16.seq d17)))))))))))))))))))))
  exact h

end Chain

end TightS

end AdvancedEncryption.DualUse.Prog
