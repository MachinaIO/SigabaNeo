import PE.Impl.ExpLUT.Scheme

/-!
# The decryption algorithm in the order of the machine (ring level)

The machine of `Dec` (package F4) computes `decryptRaw` by loops whose shape differs from the
definitions of `PE.Impl.ExpLUT.{Ops, LUT, Eval, Scheme}`. Here the reshaped forms, all exact
identities over an abstract `Setting`:

* **One kernel, the digit dot product.** `(v G⁻¹(M))_col = Σ_{c} v_c · d(M_{c.1, col}, c.2)`
  (`vecMul_ginv_apply`): only the column `col` of `M` is read. `Mul`, `SMul` and `Aut` are sums of
  such products (`mulCT_eq`, `mulPK_eq`, `autPK_row`, `smulPK_row`, `autCT_eq`).
* **Rounds along the bits** (`rounds_eq_bitRounds`): after `t` rounds, the pair (public matrix,
  encoding) of index `j < 2^t` is obtained from the input by applying `Aut_{g_s}` for the set bits
  `s < t` of `j`, in increasing order (`bitRounds`). So `LUT` is one loop over `j < W` whose body
  recomputes the pair of `j` (`lutPK_eq`, `lutCT_eq`).
* **Automorphisms along the bits** (`σ_idx_eq_bitAut`): `σ_{g^j} = σ_{g_{s_m}} ∘ ⋯ ∘ σ_{g_{s_1}}`
  for the set bits `s_1 < ⋯ < s_m` of `j < W`, and `σ_{g^{i+1}} = σ_g ∘ σ_{g^i}` (`σ_idx_succ`).
* **The decryption sum** (`decryptRaw_eq`): `μ' = c_m − d₂ − (Σ_{i<W} Σ_c σ_{g^i}(xB_c) k_{i,c} +
  Σ_{i<W} Σ_{k,c} σ_{g^i}(xH_{k,c}) k_{i,k,c} + Σ_c (c_F − A_F⁽²⁾)_c k_c)` with `xB = b − B⁽²⁾`
  and `xH_{k,c} = h_{k,c} − H_{k,1,c} + G_{1,c}` (the automorphisms fix `G`).
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix

variable {R : Type*} [CommRing R] {S : Setting R}

/-! ### The digit dot product -/

/-- **`(v G⁻¹(M))_col = Σ_c v_c d(M_{c.1, col}, c.2)`.** -/
theorem vecMul_ginv_apply (v : Col S.τ → R) (M : Matrix (Fin 2) (Col S.τ) R) (col : Col S.τ) :
    (v ᵥ* S.ginv M) col = ∑ c : Col S.τ, v c * S.D.d (M c.1 col) c.2 := by
  simp only [Matrix.vecMul, dotProduct, ginv_apply]

/-- `Mul` on encodings as digit dot products. -/
theorem mulCT_eq (A C : Matrix (Fin 2) (Col S.τ) R) (cd : Dig S.τ → Col S.τ → R)
    (c : Col S.τ → R) (j : Col S.τ) :
    mulCT S A C cd c j = ∑ ri : Col S.τ, (cd (ri.1, j, ri.2) ᵥ* S.ginv A) ri +
      (c ᵥ* S.ginv C) j := by
  rw [mulCT, Finset.sum_add_distrib, vecMul_ginv_apply]
  congr 1
  refine Finset.sum_congr rfl fun ri _ => ?_
  rw [digits, mul_comm]

/-- `Mul` on public matrices as digit dot products. -/
theorem mulPK_eq (A : Matrix (Fin 2) (Col S.τ) R) (Ad : Dig S.τ → Matrix (Fin 2) (Col S.τ) R)
    (a : Fin 2) (j : Col S.τ) :
    mulPK S A Ad a j = ∑ ri : Col S.τ, (Ad (ri.1, j, ri.2) a ᵥ* S.ginv A) ri := by
  simp only [mulPK, Matrix.of_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct]

/-- A row of a product with `G⁻¹`. -/
theorem mul_ginv_row (H M : Matrix (Fin 2) (Col S.τ) R) (a : Fin 2) :
    (H * S.ginv M) a = H a ᵥ* S.ginv M := by
  funext col
  simp only [Matrix.mul_apply, Matrix.vecMul, dotProduct]

theorem autPK_row (k : ℕ) (Hk : Matrix (Fin 2) (Col S.τ) R)
    (Aaut : Dig S.τ → Matrix (Fin 2) (Col S.τ) R) (A : Matrix (Fin 2) (Col S.τ) R) (a : Fin 2) :
    autPK S k Hk Aaut A a = Hk a ᵥ* S.ginv (autMid S k Aaut A) :=
  mul_ginv_row _ _ a

theorem smulPK_row (α : R) (A : Matrix (Fin 2) (Col S.τ) R) (a : Fin 2) :
    smulPK S α A a = A a ᵥ* S.ginv (α • S.G) :=
  mul_ginv_row _ _ a

/-! ### Rounds along the bits -/

/-- One round on a pair (public matrix, encoding): `Aut_{g_t}`. -/
def autStep (P : AutPub S) (h : AutData S) (t : ℕ)
    (x : Matrix (Fin 2) (Col S.τ) R × (Col S.τ → R)) : Matrix (Fin 2) (Col S.τ) R × (Col S.τ → R) :=
  (autPK S (S.kf t) (P.Hf t) (P.Aaut t) x.1,
    autCT S (S.kf t) (P.Hi t) (P.Aaut t) x.1 (h.hf t) (h.hi t) (h.caut t) x.2)

/-- **The pair of index `j` after `t` rounds**: `Aut_{g_s}` for the set bits `s < t` of `j`, in
increasing order. -/
def bitRounds (P : AutPub S) (h : AutData S) (x : Matrix (Fin 2) (Col S.τ) R × (Col S.τ → R))
    (j : ℕ) : ℕ → Matrix (Fin 2) (Col S.τ) R × (Col S.τ → R)
  | 0 => x
  | t + 1 => if j.testBit t then autStep P h t (bitRounds P h x j t) else bitRounds P h x j t

theorem bitRounds_congr (P : AutPub S) (h : AutData S) (x : Matrix (Fin 2) (Col S.τ) R × (Col S.τ → R))
    {j j' : ℕ} : ∀ t, (∀ s < t, j.testBit s = j'.testBit s) →
      bitRounds P h x j t = bitRounds P h x j' t
  | 0, _ => rfl
  | t + 1, hb => by
    simp only [bitRounds, hb t (Nat.lt_succ_self t),
      bitRounds_congr P h x t fun s hs => hb s (by omega)]

theorem testBit_sub_two_pow {j t s : ℕ} (hj : 2 ^ t ≤ j) (hs : s < t) :
    (j - 2 ^ t).testBit s = j.testBit s := by
  have e : j = 2 ^ t + (j - 2 ^ t) := by omega
  conv_rhs => rw [e]
  rw [Nat.testBit_two_pow_add_gt hs]

/-- **The rounds along the bits.** -/
theorem rounds_eq_bitRounds (P : AutPub S) (A : Matrix (Fin 2) (Col S.τ) R) (h : AutData S)
    (c : Col S.τ → R) : ∀ t, ∀ j < 2 ^ t,
      (roundsPK P A t j, roundsCT P A h c t j) = bitRounds P h (A, c) j t
  | 0, j, _ => rfl
  | t + 1, j, hj => by
    simp only [roundsPK, roundsCT, bitRounds]
    by_cases hjt : j < 2 ^ t
    · rw [if_pos hjt, if_pos hjt, rounds_eq_bitRounds P A h c t j hjt,
        Nat.testBit_lt_two_pow hjt, if_neg (by simp)]
    · rw [if_neg hjt, if_neg hjt]
      have hj' : j - 2 ^ t < 2 ^ t := by rw [pow_succ] at hj; omega
      have hb : j.testBit t = true := by
        have e : j = 2 ^ t + (j - 2 ^ t) := by omega
        rw [e, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hj']
        rfl
      rw [if_pos hb, ← bitRounds_congr P h (A, c) t fun s hs => testBit_sub_two_pow (by omega) hs,
        ← rounds_eq_bitRounds P A h c t (j - 2 ^ t) hj']
      rfl

theorem fst_autStep (P : AutPub S) (h h' : AutData S) (t : ℕ)
    (x x' : Matrix (Fin 2) (Col S.τ) R × (Col S.τ → R)) (hx : x.1 = x'.1) :
    (autStep P h t x).1 = (autStep P h' t x').1 := by
  simp only [autStep, hx]

/-- The public matrix of `bitRounds` depends neither on the helpers nor on the encoding. -/
theorem fst_bitRounds (P : AutPub S) (h h' : AutData S)
    (x x' : Matrix (Fin 2) (Col S.τ) R × (Col S.τ → R)) (hx : x.1 = x'.1) (j : ℕ) :
    ∀ t, (bitRounds P h x j t).1 = (bitRounds P h' x' j t).1
  | 0 => hx
  | t + 1 => by
    simp only [bitRounds]
    split_ifs
    · exact fst_autStep P h h' t _ _ (fst_bitRounds P h h' x x' hx j t)
    · exact fst_bitRounds P h h' x x' hx j t

/-- **`LUT` on public matrices, one loop over `j`.** -/
theorem lutPK_eq (P : AutPub S) (coef : ℕ → R) (A : Matrix (Fin 2) (Col S.τ) R) (h : AutData S)
    (c : Col S.τ → R) :
    lutPK P coef A = ∑ j ∈ Finset.range S.E.W, smulPK S (coef j) (bitRounds P h (A, c) j S.b).1 := by
  unfold lutPK
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < 2 ^ S.b := by rw [← S.W_eq]; exact Finset.mem_range.mp hj
  rw [← rounds_eq_bitRounds P A h c S.b j hj']

/-- **`LUT` on encodings, one loop over `j`.** -/
theorem lutCT_eq (P : AutPub S) (coef : ℕ → R) (A : Matrix (Fin 2) (Col S.τ) R) (h : AutData S)
    (c : Col S.τ → R) :
    lutCT P coef A h c = ∑ j ∈ Finset.range S.E.W, smulCT S (coef j) (bitRounds P h (A, c) j S.b).2 := by
  unfold lutCT
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < 2 ^ S.b := by rw [← S.W_eq]; exact Finset.mem_range.mp hj
  rw [← rounds_eq_bitRounds P A h c S.b j hj']

/-- `Aut_k` on encodings as digit dot products. -/
theorem autCT_eq (k : ℕ) (Hk' : Matrix (Fin 2) (Col S.τ) R)
    (Aaut : Dig S.τ → Matrix (Fin 2) (Col S.τ) R) (A : Matrix (Fin 2) (Col S.τ) R)
    (hk hk' : Col S.τ → R) (cd : Dig S.τ → Col S.τ → R) (c : Col S.τ → R) (j : Col S.τ) :
    autCT S k Hk' Aaut A hk hk' cd c j = (hk ᵥ* S.ginv (autMid S k Aaut A)) j +
      (∑ ri : Col S.τ, (cd (ri.1, j, ri.2) ᵥ* S.ginv (autMat S k A)) ri +
        (autRow S k c ᵥ* S.ginv (gcAut S k Hk' hk')) j) := by
  rw [autCT, Pi.add_apply, mulCT_eq]

/-! ### Automorphisms along the bits -/

/-- `σ_{g^j}` along the set bits `s < t` of `j`: `σ_{g_s}` in increasing order of `s`. -/
def bitAut (S : Setting R) (j : ℕ) (a : R) : ℕ → R
  | 0 => a
  | t + 1 => if j.testBit t then S.E.σ (S.kf t) (bitAut S j a t) else bitAut S j a t

theorem bitAut_congr (a : R) {j j' : ℕ} : ∀ t, (∀ s < t, j.testBit s = j'.testBit s) →
    bitAut S j a t = bitAut S j' a t
  | 0, _ => rfl
  | t + 1, hb => by
    simp only [bitAut, hb t (Nat.lt_succ_self t), bitAut_congr a t fun s hs => hb s (by omega)]

/-- **`σ_{g^j}` along the bits.** -/
theorem σ_idx_eq_bitAut (a : R) : ∀ t ≤ S.b, ∀ j < 2 ^ t, S.E.σ (S.idx j) a = bitAut S j a t
  | 0, _, j, hj => by
    have : j = 0 := by omega
    subst this; simp [bitAut, S.idx_zero]
  | t + 1, ht, j, hj => by
    simp only [bitAut]
    have hW : 2 ^ (t + 1) ≤ S.E.W := by rw [S.W_eq]; exact Nat.pow_le_pow_right (by norm_num) ht
    by_cases hjt : j < 2 ^ t
    · rw [Nat.testBit_lt_two_pow hjt]
      exact σ_idx_eq_bitAut a t (by omega) j hjt
    · have hj' : j - 2 ^ t < 2 ^ t := by rw [pow_succ] at hj; omega
      have hb : j.testBit t = true := by
        have e : j = 2 ^ t + (j - 2 ^ t) := by omega
        rw [e, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hj']
        rfl
      rw [if_pos hb, ← bitAut_congr a t fun s hs => testBit_sub_two_pow (by omega) hs,
        ← σ_idx_eq_bitAut a t (by omega) (j - 2 ^ t) hj', S.idx_add,
        show 2 ^ t + (j - 2 ^ t) = j by omega, Nat.mod_eq_of_lt (by omega)]

/-- `σ_{g^{i+1}} = σ_g ∘ σ_{g^i}` inside `H`. -/
theorem σ_idx_succ (a : R) {i : ℕ} (hi : i + 1 < S.E.W) :
    S.E.σ (S.idx (i + 1)) a = S.E.σ (S.idx 1) (S.E.σ (S.idx i) a) := by
  rw [S.idx_add, show 1 + i = i + 1 by omega, Nat.mod_eq_of_lt hi]

/-! ### The decryption sum -/

theorem σ_G (k : ℕ) (a : Fin 2) (c : Col S.τ) : S.E.σ k (S.G a c) = S.G a c := by
  rw [G_apply]
  split_ifs
  · exact S.σ_g k _
  · exact map_zero _

variable {Wb J Pos : Type*} [Fintype Wb] [Fintype J]

/-- **`μ'` as the sums of the machine.** -/
theorem decryptRaw_eq (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos)
    (k : KCol Wb J S.τ S.E.W → R) (ct : Ciphertext S Wb J Pos) :
    decryptRaw M mpk F k ct = ct.cm - mpk.d 1 -
      ((∑ i : Fin S.E.W, ∑ c : BCol Wb S.τ,
          S.E.σ (S.idx i) (ct.b c - mpk.B 1 c) * k (.inl (i, c))) +
        ((∑ i : Fin S.E.W, ∑ kc : J × Col S.τ,
          S.E.σ (S.idx i) (ct.h kc.1 kc.2 - mpk.H kc.1 1 kc.2 + S.G 1 kc.2) *
            k (.inr (.inl (i, kc.1, kc.2)))) +
        ∑ c : Col S.τ, (evalCiphertext M mpk F ct c - keyPK M mpk F 1 c) * k (.inr (.inr c)))) := by
  unfold decryptRaw
  congr 1
  simp only [dotProduct]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => ?_
    simp only [Pi.sub_apply, decRow, decConst, map_sub]
  · congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun kc _ => ?_
    simp only [Pi.sub_apply, decRow, decConst, map_add, map_sub, σ_G]
    ring

end AdvancedEncryption.ExpLUT
