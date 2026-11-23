import PE.Impl.ExpLUT.Scheme

/-!
# Correctness of the scheme, exactly (§5.2)

* `evalOK_encrypt`: a ciphertext of `Enc` gives exact ciphertext data for Lemma 9, with the
  errors `encErrs` of its coins (flooding errors for `c₀`, `C^in_t` and the digit encodings, base
  errors for the helpers).
* **Linearity in the secret** (eq. (4), `decRow_sub_decConst`): with `s̄_H = (σ_i(s̄))_{i ∈ H}`,
  `y_F − κ_F = s̄_H M_F − F(x) (0, s̄ G⁽¹⁾ + G⁽²⁾) + e_F`, with the error row `e_F` (`decErr`):
  `σ_i(e_b)`, `σ_i(e_k)` and the error of `c_F` (`evalErr`).
* **Theorem 1, exactly** (`decryptRaw_encrypt`): for `F(x) = 0` and a valid key,
  `μ' = ⌊q/2⌉ m + e_m − e_F k_Fᵀ`.

The norm-level bound is `PE.Impl.ExpLUT.CorrectBound`.
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix

variable {R : Type*} [CommRing R] {S : Setting R} {Wb J Pos : Type*} [Fintype Wb] [Fintype J]
  [DecidableEq J]

/-- The errors of the ciphertext data of `Enc`. -/
def encErrs (M : HelperMap S J) (r : EncCoins S Wb J Pos) : EvalErrs S Pos :=
  { e0 := r.e0
    fin := r.ein
    ein := r.edin
    aut := ⟨finExt fun t => r.eh (M.fwd t), finExt fun t => r.eh (M.inv t), finExt r.eaut⟩ }

theorem finExt_of_lt {α : Type*} [Zero α] (f : Fin S.b → α) {t : ℕ} (ht : t < S.b) :
    finExt f t = f ⟨t, ht⟩ := by
  simp [finExt, ht]

omit [Fintype Wb] [Fintype J] [DecidableEq J] in
/-- **The ciphertext data of `Enc` are exact** for Lemma 9 (for a program of width `w`). -/
theorem evalOK_encrypt (M : HelperMap S J) {w : ℕ} (half : R) (mpk : MPK S Wb J Pos) (x : Pos → ℕ)
    (m : R) (r : EncCoins S Wb J Pos) (F : BP Pos) (hw : F.w = w) :
    EvalOK F (evalPub M mpk) (evalData M mpk (encrypt M w half mpk x m r)) r.s x (encErrs M r) where
  c0 := rfl
  Cin t := by
    subst hw
    unfold IsGC
    funext j
    simp only [evalData, encrypt, cinMat, cinBots, encErrs, Pi.add_apply, vecMul_G_apply]
    obtain ⟨a, i⟩ := j
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    fin_cases a <;> simp [sec, Matrix.smul_vecMul, vecMul_G_apply] <;> ring
  cin t d := rfl
  aut t ht := by
    refine ⟨?_, ?_, fun d => ?_⟩
    · simp only [evalPub, evalData, encErrs, finExt_of_lt _ ht, encrypt, helpers, M.je_fwd]
      rfl
    · simp only [evalPub, evalData, encErrs, finExt_of_lt _ ht, encrypt, helpers, M.je_inv]
      rfl
    · simp only [evalPub, evalData, encErrs, finExt_of_lt _ ht, encrypt]
      rfl

/-- `s̄_H = (σ_i(s̄))_{i ∈ H}`. -/
def sH (S : Setting R) (sb : R) : Fin S.E.W → R := fun i => S.E.σ (S.idx i) sb

/-- The row `(0, s̄ G⁽¹⁾ + G⁽²⁾)`: `s G` on the last `2τ` columns. -/
def lastPay (S : Setting R) (sb : R) : KCol Wb J S.τ S.E.W → R
  | .inr (.inr c) => (sec sb ᵥ* S.G) c
  | _ => 0

/-- The error row `e_F` of eq. (4): `σ_i(e_b)`, `σ_i(e_k)`, and the error of `c_F`. -/
def decErr (M : HelperMap S J) (w : ℕ) (half : R) (mpk : MPK S Wb J Pos) (F : BP Pos)
    (x : Pos → ℕ) (m : R) (r : EncCoins S Wb J Pos) : KCol Wb J S.τ S.E.W → R
  | .inl (i, c) => S.E.σ (S.idx i) (r.eb c)
  | .inr (.inl (i, k, c)) => S.E.σ (S.idx i) (r.eh k c)
  | .inr (.inr c) =>
    evalErr F (evalPub M mpk) (evalData M mpk (encrypt M w half mpk x m r)) x (encErrs M r) c

theorem sH_row0 (sb : R) : sH S sb S.row0 = sb := S.idx_zero sb

/-- **Linearity in the secret** (eq. (4)): `y_F − κ_F = s̄_H M_F − F(x) (0, s G) + e_F`. -/
theorem decRow_sub_decConst (h8 : Lemma8 S) (M : HelperMap S J) {w : ℕ} (half : R)
    (mpk : MPK S Wb J Pos) (F : BP Pos) (hF : F.WF S.E.W) (hw : F.w = w) (x : Pos → ℕ)
    (hx : ∀ t, x t < F.nsym) (m : R) (r : EncCoins S Wb J Pos) :
    decRow M mpk F (encrypt M w half mpk x m r) - decConst M mpk F =
      sH S r.s ᵥ* keyMat M mpk F - (F.eval x : R) • lastPay S r.s + decErr M w half mpk F x m r := by
  funext c
  rcases c with ⟨i, c⟩ | ⟨i, k, c⟩ | c
  · simp only [decRow, decConst, keyMat, decErr, lastPay, encrypt, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, mul_zero, sub_zero]
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.sum_univ_two, sec, sH]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, map_add,
      map_mul]
    ring
  · have hmul : S.E.σ (S.idx i) (S.E.σ (S.idx (M.je k)) r.s) = sH S r.s (M.mulRow i k) := by
      simp only [sH, HelperMap.mulRow, S.idx_add]
    simp only [decRow, decConst, keyMat, decErr, lastPay, encrypt, helpers, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_zero, sub_zero, vecMul_G_apply]
    have hv : ∀ j : Fin S.E.W, sH S r.s j * ((if j = i then S.E.σ (S.idx i) (mpk.H k 0 c) else 0) -
        if j = M.mulRow i k then S.G 0 c else 0) =
        (if j = i then sH S r.s j * S.E.σ (S.idx i) (mpk.H k 0 c) else 0) -
          if j = M.mulRow i k then sH S r.s j * S.G 0 c else 0 := by
      intro j; split_ifs <;> ring
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, hv, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← hmul]
    simp only [Fin.sum_univ_two, sec, map_add, map_sub, map_mul, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, sH]
    obtain ⟨a, c'⟩ := c
    fin_cases a <;> simp [G_apply, S.σ_g] <;> ring
  · have he : evalCiphertext M mpk F (encrypt M w half mpk x m r) =
        sec r.s ᵥ* keyPK M mpk F - ((F.eval x : R) • sec r.s) ᵥ* S.G +
          evalErr F (evalPub M mpk) (evalData M mpk (encrypt M w half mpk x m r)) x (encErrs M r) :=
      encodes_eval h8 F hF (evalPub M mpk) (evalData M mpk (encrypt M w half mpk x m r)) hx
        (evalOK_encrypt M half mpk x m r F hw)
    simp only [decRow, decConst, keyMat, decErr, lastPay, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, he, Matrix.smul_vecMul]
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.sum_univ_two]
    rw [sH_row0]
    simp only [sec, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
    ring

/-- **Theorem 1, exactly**: for `F(x) = 0` and a valid key, `μ' = ⌊q/2⌉ m + e_m − e_F k_Fᵀ`. -/
theorem decryptRaw_encrypt (h8 : Lemma8 S) (M : HelperMap S J) {w : ℕ} (half : R)
    (mpk : MPK S Wb J Pos) (F : BP Pos) (hF : F.WF S.E.W) (hw : F.w = w) (x : Pos → ℕ)
    (hx : ∀ t, x t < F.nsym) (hFx : F.eval x = 0) (m : R) (r : EncCoins S Wb J Pos)
    (k : KCol Wb J S.τ S.E.W → R) (hk : ValidKey M mpk F k) :
    decryptRaw M mpk F k (encrypt M w half mpk x m r) =
      half * m + r.em - decErr M w half mpk F x m r ⬝ᵥ k := by
  unfold decryptRaw
  rw [decRow_sub_decConst h8 M half mpk F hF hw x hx m r, hFx, Nat.cast_zero, zero_smul, sub_zero,
    add_dotProduct, ← Matrix.dotProduct_mulVec, hk]
  have ht : sH S r.s ⬝ᵥ keyTarget mpk = r.s * mpk.d 0 := by
    simp only [dotProduct, keyTarget, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, sH_row0]
  rw [ht]
  simp only [encrypt, dotProduct, Fin.sum_univ_two, sec, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_mul]
  ring

end AdvancedEncryption.ExpLUT
