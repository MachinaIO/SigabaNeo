import PE.Impl.ExpLUT.Prog.Words
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMMat

/-!
# KeyGen (package F3): the VM routines are the operations of §4

The `KeyGen` machine is written as code of the Mersenne VM (`SigabaNeo.Tape.MVM`, registers of
canonical ring words, compiled to a framed tape program with exact semantics `MVM.law_compile`).
This file identifies the VM routines with the operations of the scheme at the dimensions `D`:

* the word of a `2 × 2K` matrix is the queue of its entries (`matE_enc`);
* `mulPKC` computes `mulPK` (`mulPK_eq_mulPKm`);
* `ginvMulC` computes `B · G⁻¹(C)` (`mul_ginv_eq`);
* `autMatC` computes `σ_k` entrywise (`autMat_eq`), and `σ_g` iterated `2^t` times is
  `σ_{g^{2^t}}` (`aut_iterate`).
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.MVM Matrix Cslib

variable (D : Dims)

/-- **The word of a matrix is the queue of its entries.** -/
theorem matE_enc (A : Matrix (Fin 2) (Col D.K) (Rg D)) :
    (matE D (Fin 2) (Col D.K)).enc A = encL D.N D.K (matL (fun a c => A a c)) := by
  show ((Enum.list (α := Fin 2)).map A).flatMap
    (fun r => ((Enum.list (α := Col D.K)).map r).flatMap (encRM D.N D.K)) = _
  simp only [matL, encL, List.flatMap_map, List.flatMap_assoc]
  rfl

/-- The family of digit matrices as a queue. -/
theorem digE_enc (Ad : Dig D.K → Matrix (Fin 2) (Col D.K) (Rg D)) :
    (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K))).enc Ad =
      encL D.N D.K (adL (fun d a c => Ad d a c)) := by
  have e : (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K))).enc Ad =
      (Enum.list (α := Dig D.K)).flatMap (fun d => (matE D (Fin 2) (Col D.K)).enc (Ad d)) := by
    simp only [FixedEnc.«fun», FixedEnc.encList, List.flatMap_map]
  rw [e]
  simp only [matE_enc, adL, encL, List.flatMap_assoc]

theorem ginv_apply (A : Matrix (Fin 2) (Col (setting D).τ) (Rg D)) (c col : Col (setting D).τ) :
    (setting D).ginv A c col = binaryDigit (A c.1 col) c.2 := by
  simp [Setting.ginv, gswGadget, gadgetOf, setting, canonSetting, binaryDigits]
  rfl

/-- **`mulPK` with binary digits** is the function computed by `mulPKC`. -/
theorem mulPK_eq_mulPKm (A : Matrix (Fin 2) (Col (setting D).τ) (Rg D))
    (Ad : Dig (setting D).τ → Matrix (Fin 2) (Col (setting D).τ) (Rg D)) :
    mulPK (setting D) A Ad = Matrix.of (mulPKm (K := D.K) (fun a c => A a c) (fun d a c => Ad d a c)) := by
  refine Matrix.ext fun a j => ?_
  show _ = mulPKm (K := D.K) (fun a c => A a c) (fun d a c => Ad d a c) a j
  simp only [mulPK, mulPKm, Matrix.of_apply, Matrix.mul_apply, ginv_apply]
  rfl

/-- **`B · G⁻¹(C)`** is the function computed by `ginvMulC`. -/
theorem mul_ginv_eq (B C : Matrix (Fin 2) (Col (setting D).τ) (Rg D)) :
    B * (setting D).ginv C = Matrix.of (ginvMulm (K := D.K) (fun a c => B a c) (fun a c => C a c)) := by
  refine Matrix.ext fun a col => ?_
  show _ = ginvMulm (K := D.K) (fun a c => B a c) (fun a c => C a c) a col
  simp only [Matrix.mul_apply, ginv_apply, ginvMulm, digRow]
  refine Finset.sum_congr rfl fun c _ => ?_
  rcases c with ⟨r, i⟩
  fin_cases r <;> simp

/-- **`σ_k` entrywise** (odd `k`) is `aut N k`. -/
theorem autMat_eq {k : ℕ} (hk : Odd k) (A : Matrix (Fin 2) (Col (setting D).τ) (Rg D)) :
    autMat (setting D) k A = Matrix.of fun a c => aut D.N k (A a c) := by
  refine Matrix.ext fun a c => ?_
  simp only [autMat, Matrix.map_apply, Matrix.of_apply]
  exact autσ_of_odd hk _

/-- `σ_g` iterated `m` times is `σ_{g^m}` (odd `g`). -/
theorem aut_iterate {g : ℕ} (hg : Odd g) (m : ℕ) (a : Rg D) :
    (aut D.N g)^[m] a = aut D.N (g ^ m) a := by
  induction m with
  | zero => simp [aut_one]
  | succ m ih => rw [Function.iterate_succ_apply', ih, aut_aut hg, pow_succ, mul_comm]

/-- **`EvalPK` of `Aut_k`** (odd `k`) is the function computed by `autPKC`. -/
theorem autPK_eq {k : ℕ} (hk : Odd k) (Hk A : Matrix (Fin 2) (Col (setting D).τ) (Rg D))
    (Aaut : Dig (setting D).τ → Matrix (Fin 2) (Col (setting D).τ) (Rg D)) :
    autPK (setting D) k Hk Aaut A = Matrix.of (ginvMulm (K := D.K) (fun a c => Hk a c)
      (mulPKm (K := D.K) (fun a c => aut D.N k (A a c)) (fun d a c => Aaut d a c))) := by
  rw [autPK, autMid, mul_ginv_eq, mulPK_eq_mulPKm, autMat_eq D hk]
  rfl

/-! ### The rounds as chains over the bits of the index -/

section Chain

variable {α : Type*}

/-- Apply `f s` for each set bit `s < t` of `j`, in increasing order of `s`. -/
def bitChain (f : ℕ → α → α) : ℕ → ℕ → α → α
  | 0, _, a => a
  | t + 1, j, a => if j.testBit t then f t (bitChain f t j a) else bitChain f t j a

theorem bitChain_congr (f : ℕ → α → α) : ∀ (t : ℕ) {j j' : ℕ},
    (∀ s < t, j.testBit s = j'.testBit s) → ∀ a, bitChain f t j a = bitChain f t j' a
  | 0, _, _, _, _ => rfl
  | t + 1, j, j', h, a => by
    simp only [bitChain, h t (by omega), bitChain_congr f t (fun s hs => h s (by omega)) a]

theorem testBit_sub_two_pow {j t s : ℕ} (h1 : 2 ^ t ≤ j) (h2 : j < 2 ^ (t + 1)) (hs : s < t) :
    (j - 2 ^ t).testBit s = j.testBit s := by
  have e : j - 2 ^ t = j % 2 ^ t := by
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by rw [pow_succ] at h2; omega)]
  rw [e, Nat.testBit_mod_two_pow]; simp [hs]

theorem testBit_top {j t : ℕ} (h2 : j < 2 ^ (t + 1)) : j.testBit t = decide (2 ^ t ≤ j) := by
  by_cases h : 2 ^ t ≤ j
  · rw [decide_eq_true h]
    have : j / 2 ^ t = 1 := by
      rw [pow_succ] at h2
      exact le_antisymm (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by positivity)).mpr
        (by omega))) ((Nat.le_div_iff_mul_le (by positivity)).mpr (by omega))
    rw [Nat.testBit_eq_decide_div_mod_eq, this]; rfl
  · rw [decide_eq_false h]
    exact Nat.testBit_eq_false_of_lt (by omega)

end Chain

variable {R : Type*} [CommRing R] {S : Setting R}

/-! ### The table coefficients as powers -/

theorem X_pow_two_n_sub (E : ExpRing R) {u : ℕ} (hu : u ≤ 2 * E.n) :
    E.X ^ (2 * E.n - u) = (E.X ^ (2 * E.n - 1)) ^ u := by
  rcases Nat.eq_zero_or_pos u with rfl | hu0
  · simp [E.X_pow_two_n]
  · rw [← pow_mul]
    have hn := E.n_pos
    have e : (2 * E.n - 1) * u = (2 * E.n - u) + 2 * E.n * (u - 1) := by
      have : (2 * E.n - 1) * u + u = 2 * E.n * u := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
      have h2 : 2 * E.n * u = 2 * E.n * (u - 1) + 2 * E.n := by
        rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hu0]
      omega
    rw [e, pow_add, pow_mul, E.X_pow_two_n, one_pow, mul_one]

/-- **A table coefficient is a power sum**: `W⁻¹ Σ_{u<W} c_u σ_k(X^{2n−1})^u`. -/
theorem lutCoef_pow (E : ExpRing R) (c : ℕ → R) (k : ℕ) :
    E.lutCoef c k = E.Winv * ∑ u ∈ Finset.range E.W, c u * (E.σ k (E.X ^ (2 * E.n - 1))) ^ u := by
  rw [ExpRing.lutCoef, ExpRing.lutCoefOf]
  congr 1
  refine Finset.sum_congr rfl fun u hu => ?_
  have hW := E.W_lt
  rw [X_pow_two_n_sub E (by have := Finset.mem_range.mp hu; omega), map_pow]

/-- **The rounds are chains**: `A_j` after `t` rounds applies `Aut_{g_s}` for the set bits `s` of
`j`, in increasing order (`j < 2^t`). -/
theorem roundsPK_eq_bitChain (P : AutPub S) (A : Matrix (Fin 2) (Col S.τ) R) :
    ∀ (t j : ℕ), j < 2 ^ t → roundsPK P A t j =
      bitChain (fun s M => autPK S (S.kf s) (P.Hf s) (P.Aaut s) M) t j A
  | 0, j, _ => rfl
  | t + 1, j, hj => by
    simp only [roundsPK, bitChain, testBit_top hj]
    by_cases h : j < 2 ^ t
    · rw [if_pos h, decide_eq_false (by omega), roundsPK_eq_bitChain P A t j h]
      rfl
    · rw [if_neg h, decide_eq_true (by omega), if_pos rfl,
        roundsPK_eq_bitChain P A t (j - 2 ^ t) (by rw [pow_succ] at hj; omega)]
      congr 1
      exact bitChain_congr _ t (fun s hs => testBit_sub_two_pow (by omega) hj hs) A

end AdvancedEncryption.ExpLUT.Prog
