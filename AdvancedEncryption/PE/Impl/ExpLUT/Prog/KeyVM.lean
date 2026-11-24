import PE.Impl.ExpLUT.Prog.Words
import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.VMMat

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

end AdvancedEncryption.ExpLUT.Prog
