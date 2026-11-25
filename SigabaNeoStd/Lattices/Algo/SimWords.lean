import SigabaNeoStd.Lattices.Algo.SLPWords
import SigabaNeoStd.Lattices.Homomorphic.SLPSim
import SigabaNeoStd.Lattices.Homomorphic.SLPCircuit

/-!
# Simulated public keys on words

The simulation of `KeyGen*` (BTVW17 §4.2) runs a program jointly on (public key `A`, short
matrix `W`, value `x`) with the step `simStep`:
`(G − A_a G⁻¹(A_b), −(W_a G⁻¹(A_b) + x_a W_b), 1 − x_a x_b)`. Here on words, for any gadget with
columns `Col k` given on words (`GadgetW`: the word of `G` and `G⁻¹` as a word function):

* `simStepW`, `slpSimW`: the joint run on words (`slpSimW_enc`);
* the binary top-row gadget (`topGadgetW`, rows `Fin 1`) and the binary Ring-GSW gadget
  (`gswGadgetW`, rows `Fin 2`: `gswGadW`, `ginvGswW`);
* `evalSim_circuit`: the simulation along the tree `p.circuit w` (`evalSim`) is the run `slpSim`
  on the program, so it is computed gate by gate;
* `keySumMW`: `∑_b W_b · G̲⁻¹(V_b)` for matrices of `m` rows (`keySumMW_enc`);
* `bitsW`: the `0/1` ring words of the bits of a Ring-GSW ciphertext word (`bitsW_enc`).
-/

namespace SigabaNeo.Lattices.Algo

open SigabaNeo.Encode Cslib Matrix

variable {N K k : ℕ}

/-! ### Matrices with the gadget columns -/

/-- The word of a matrix `Fin m × Col k`. -/
def colsW (N K k m : ℕ) (M : Matrix (Fin m) (Fin 2 × Fin k) (Rq N K)) : List Bool :=
  matW N K m (2 * k) (M.submatrix id (colE k))

theorem rowW_eq_colsW (B : Matrix (Fin 1) (Fin 2 × Fin k) (Rq N K)) :
    rowW N K k B = colsW N K k 1 B := rfl

theorem colsW_mul_sq {m : ℕ} (A : Matrix (Fin m) (Fin 2 × Fin k) (Rq N K))
    (M : Matrix (Fin 2 × Fin k) (Fin 2 × Fin k) (Rq N K)) :
    matMulW N K m (2 * k) (2 * k) (colsW N K k m A) (sqW N K k M) = colsW N K k m (A * M) := by
  rw [colsW, sqW, matMulW_enc, submatrix_mul_equiv, colsW]

theorem matW_zero (m n : ℕ) : matW N K m n 0 = zeroW (m * n * (N * K)) := by
  rw [← concatN_zeroW]
  symm
  apply concatN_eq_matW
  intro p _
  exact (enc_zeroR N K).symm

/-- Entrywise product with a ring element. -/
def smulMatW (N K L : ℕ) (x y : List Bool) : List Bool :=
  concatN L fun p => mulRW N K x (rget N K p y)

theorem smulMatW_enc {m n : ℕ} (r : Rq N K) (M : Matrix (Fin m) (Fin n) (Rq N K)) :
    smulMatW N K (m * n) ((ringEnc N K).enc r) (matW N K m n M) = matW N K m n (r • M) :=
  concatN_eq_matW _ fun p hp => by rw [rget_matW M hp, mulRW_enc]; rfl

/-- Entrywise negation: `0 − y`. -/
def negMatW (N K L : ℕ) (y : List Bool) : List Bool := matSubW N K L (zeroW (L * (N * K))) y

theorem negMatW_enc {m n : ℕ} (M : Matrix (Fin m) (Fin n) (Rq N K)) :
    negMatW N K (m * n) (matW N K m n M) = matW N K m n (-M) := by
  rw [negMatW, ← matW_zero, matSubW_enc, zero_sub]

/-- The word of the ring element `1`. -/
def oneW (N K : ℕ) : List Bool := constW N K (bitW K true)

theorem enc_bitR (b : Bool) :
    (ringEnc N K).enc (if b then (1 : Rq N K) else 0) = constW N K (bitW K b) := by
  rw [← enc_bit, ← enc_algebraMap]
  cases b <;> simp

theorem enc_one : (ringEnc N K).enc (1 : Rq N K) = oneW N K := by
  have h := enc_bitR (N := N) (K := K) true
  simp only [ite_true] at h
  rw [h, oneW]

/-! ### Gadgets on words -/

/-- A gadget with columns `Col k` on rows `Fin r`, given on words. -/
structure GadgetW (N K k r : ℕ) (Γ : GadgetMatrix (Rq N K) (Fin r) (Fin 2 × Fin k)) where
  /-- The word of `G`. -/
  gad : List Bool
  /-- `G⁻¹` on words. -/
  ginv : List Bool → List Bool
  gad_eq : gad = colsW N K k r Γ.G
  ginv_eq : ∀ A, ginv (colsW N K k r A) = sqW N K k (Γ.ginv A)

/-- The joint step of the simulation on words, for a short matrix of `d` rows. -/
def simStepW (N K k r d : ℕ) (gad : List Bool) (ginv : List Bool → List Bool)
    (u v : List Bool × List Bool × List Bool) : List Bool × List Bool × List Bool :=
  (matSubW N K (r * (2 * k)) gad (matMulW N K r (2 * k) (2 * k) u.1 (ginv v.1)),
    negMatW N K (d * (2 * k)) (matAddW N K (d * (2 * k))
      (matMulW N K d (2 * k) (2 * k) u.2.1 (ginv v.1)) (smulMatW N K (d * (2 * k)) u.2.2 v.2.1)),
    subRW N K (oneW N K) (mulRW N K u.2.2 v.2.2))

/-- The words of a state of the simulation. -/
def simWords (N K k r d : ℕ)
    (u : Matrix (Fin r) (Fin 2 × Fin k) (Rq N K) × Matrix (Fin d) (Fin 2 × Fin k) (Rq N K) × Rq N K) :
    List Bool × List Bool × List Bool :=
  (colsW N K k r u.1, colsW N K k d u.2.1, (ringEnc N K).enc u.2.2)

theorem simStepW_enc {r d : ℕ} {Γ : GadgetMatrix (Rq N K) (Fin r) (Fin 2 × Fin k)}
    (gw : GadgetW N K k r Γ) (u v) :
    simWords N K k r d (simStep Γ u v) =
      simStepW N K k r d gw.gad gw.ginv (simWords N K k r d u) (simWords N K k r d v) := by
  obtain ⟨A, W, x⟩ := u
  obtain ⟨B, V, y⟩ := v
  simp only [simWords, simStepW, simStep, gw.ginv_eq, gw.gad_eq, colsW_mul_sq]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [colsW]; rw [matSubW_enc]; rfl
  · simp only [colsW]
    rw [smulMatW_enc, matAddW_enc, negMatW_enc]; rfl
  · simp only; rw [mulRW_enc, ← enc_one, subRW_enc]

/-- **The simulation on words**: the run of a program on (public key, short matrix, value) words. -/
def slpSimRunW {ι : Type*} (N K k r d : ℕ) (gad : List Bool) (ginv : List Bool → List Bool)
    (aW wW xW : ι → List Bool) (p : SLP ι) (w : Wire ι) : List Bool × List Bool × List Bool :=
  SLP.valueOf (fun i => (aW i, wW i, xW i)) (gad, zeroW (d * (2 * k) * (N * K)), oneW N K)
    (simStepW N K k r d gad ginv) p w

theorem slpSimRunW_enc {ι : Type*} {r d : ℕ} {Γ : GadgetMatrix (Rq N K) (Fin r) (Fin 2 × Fin k)}
    (gw : GadgetW N K k r Γ) (A : ι → Matrix (Fin r) (Fin 2 × Fin k) (Rq N K))
    (Wm : ι → Matrix (Fin d) (Fin 2 × Fin k) (Rq N K)) (x : ι → Rq N K) (p : SLP ι) (w : Wire ι) :
    slpSimRunW N K k r d gw.gad gw.ginv (fun i => colsW N K k r (A i)) (fun i => colsW N K k d (Wm i))
      (fun i => (ringEnc N K).enc (x i)) p w = simWords N K k r d (simRun Γ A Wm x p w) := by
  unfold slpSimRunW simRun
  refine (SLP.valueOf_map (fun i => (A i, Wm i, x i)) (Γ.G, 0, 1) (simStep Γ) _ _ _
    (simWords N K k r d) (fun _ => rfl) ?_ (fun u v => simStepW_enc gw u v) p w).symm
  simp only [simWords, gw.gad_eq, enc_one]
  have hz : colsW N K k d (0 : Matrix (Fin d) (Fin 2 × Fin k) (Rq N K)) =
      zeroW (d * (2 * k) * (N * K)) := by
    rw [colsW, ← matW_zero]; rfl
  rw [hz]

/-- **The short matrix `W_w` of a wire, on words** (`slpSim`). -/
theorem slpSim_words {ι : Type*} {r d : ℕ} {Γ : GadgetMatrix (Rq N K) (Fin r) (Fin 2 × Fin k)}
    (gw : GadgetW N K k r Γ) (A : ι → Matrix (Fin r) (Fin 2 × Fin k) (Rq N K))
    (Wm : ι → Matrix (Fin d) (Fin 2 × Fin k) (Rq N K)) (x : ι → Rq N K) (p : SLP ι) (w : Wire ι) :
    (slpSimRunW N K k r d gw.gad gw.ginv (fun i => colsW N K k r (A i))
      (fun i => colsW N K k d (Wm i)) (fun i => (ringEnc N K).enc (x i)) p w).2.1 =
      colsW N K k d (slpSim Γ A Wm x p w) := by
  rw [slpSimRunW_enc gw]; rfl

/-! ### The two binary gadgets -/

variable (hk : 2 ^ K ≤ 2 ^ k)

/-- The binary top-row gadget on words. -/
noncomputable def topGadgetW : GadgetW N K k 1 (topBin N K k hk) where
  gad := gadW N K k
  ginv := ginvW N K k
  gad_eq := gadW_enc hk
  ginv_eq := ginvW_enc hk

/-- The binary Ring-GSW gadget `G ∈ R_q^{2 × Col k}`. -/
noncomputable abbrev gswB (N K k : ℕ) (hk : 2 ^ K ≤ 2 ^ k) :
    GadgetMatrix (Rq N K) (Fin 2) (Fin 2 × Fin k) :=
  gswGadget (binaryDigits N (2 ^ K) k hk)

theorem gswB_ginv_apply (A : Matrix (Fin 2) (Fin 2 × Fin k) (Rq N K)) (c col : Fin 2 × Fin k) :
    (gswB N K k hk).ginv A c col = binaryDigit (A c.1 col) c.2 := by
  simp only [gswB, gswGadget, gadgetOf, Matrix.of_apply, id]
  rw [Finset.sum_eq_single c.1]
  · simp [binaryDigits]
  · intro b _ hb; simp [hb]
  · simp

theorem gswB_G_apply (a : Fin 2) (col : Fin 2 × Fin k) :
    (gswB N K k hk).G a col =
      if a = col.1 then algebraMap (ZMod (2 ^ K)) (Rq N K) (2 ^ (col.2 : ℕ)) else 0 := by
  simp only [gswB, gswGadget, gadgetOf, Matrix.of_apply, id, binaryDigits]

/-- `G⁻¹` of the Ring-GSW gadget on words: the entry `(c, col)` is the binary digit `c.2` of the
entry `(c.1, col)`. -/
def ginvGswW (N K k : ℕ) (a : List Bool) : List Bool :=
  concatN (2 * k * (2 * k)) fun p =>
    digitRW N K (p / (2 * k) % k) (rget N K (p / (2 * k) / k * (2 * k) + p % (2 * k)) a)

theorem ginvGswW_enc (A : Matrix (Fin 2) (Fin 2 × Fin k) (Rq N K)) :
    ginvGswW N K k (colsW N K k 2 A) = sqW N K k ((gswB N K k hk).ginv A) := by
  apply concatN_eq_matW
  intro p hp
  rw [submatrix_apply, gswB_ginv_apply, colE_apply, colE_apply]
  dsimp only
  have hc := div_lt_of_lt_mul' hp
  have h1 : p / (2 * k) / k < 2 := div_lt_of_lt_mul' hc
  have h := rget_matW' (A.submatrix id (colE k)) ⟨p / (2 * k) / k, h1⟩
    ⟨p % (2 * k), mod_lt_of_lt_mul' hp⟩
  simp only at h
  rw [colsW, h, digitRW_enc, submatrix_apply, id, colE_apply]

/-- The word of the Ring-GSW gadget: `2^i` at `(a, (a, i))`. -/
def gswGadW (N K k : ℕ) : List Bool :=
  concatN (2 * (2 * k)) fun p =>
    if p / (2 * k) = p % (2 * k) / k then constW N K (powW K (p % (2 * k) % k))
    else zeroW (N * K)

theorem gswGadW_enc : gswGadW N K k = colsW N K k 2 (gswB N K k hk).G := by
  apply concatN_eq_matW
  intro p hp
  rw [submatrix_apply, id, gswB_G_apply, colE_apply]
  dsimp only
  split_ifs with h1 h2 h2
  · rw [enc_algebraMap, enc_pow]
  · exact absurd (Fin.ext h1) h2
  · exact absurd (congrArg Fin.val h2) h1
  · exact (enc_zeroR N K).symm

/-- The binary Ring-GSW gadget on words. -/
noncomputable def gswGadgetW : GadgetW N K k 2 (gswB N K k hk) where
  gad := gswGadW N K k
  ginv := ginvGswW N K k
  gad_eq := gswGadW_enc hk
  ginv_eq := ginvGswW_enc hk

/-! ### The simulation along a circuit -/

/-- **`evalSim` along the circuit of a wire is the run of the program.** -/
theorem evalSim_circuit {R : Type*} [CommRing R] {r W m : Type*} [Fintype r] [Fintype W]
    [Fintype m] (Γ : GadgetMatrix R r W) {ι : Type*} (A : ι → Matrix r W R) (x : ι → R)
    (Wm : ι → Matrix m W R) (p : SLP ι) (w : Wire ι) :
    evalSim Γ A x Wm (p.circuit w) = slpSim Γ A Wm x p w := by
  have h := SLP.valueOf_map (Circuit.input) Circuit.one Circuit.nand (fun i => (A i, Wm i, x i))
    (Γ.G, 0, 1) (simStep Γ)
    (fun c => (evalMat Γ A c, evalSim Γ A x Wm c, c.eval x)) (fun _ => rfl) rfl
    (fun _ _ => rfl) p w
  exact congrArg (fun u => u.2.1) h

/-! ### Sums over the bits of a row, with `m` rows -/

/-- The accumulation loop on words of `m × Col k` matrices. -/
def mSum (N K k m : ℕ) (f : ℕ → List Bool) : ℕ → List Bool
  | 0 => zeroW (m * (2 * k) * (N * K))
  | t + 1 => matAddW N K (m * (2 * k)) (mSum N K k m f t) (f t)

theorem mSum_enc {m n : ℕ} {f : ℕ → List Bool} (g : ℕ → Matrix (Fin m) (Fin 2 × Fin k) (Rq N K))
    (hf : ∀ t < n, f t = colsW N K k m (g t)) :
    ∀ t ≤ n, mSum N K k m f t = colsW N K k m (∑ t' ∈ Finset.range t, g t')
  | 0, _ => by simp [mSum, colsW, matW_zero]
  | t + 1, ht => by
    rw [mSum, mSum_enc g hf t (by omega), hf t (by omega), colsW, colsW, matAddW_enc,
      Finset.sum_range_succ, colsW]
    rfl

theorem mSum_fin {m n : ℕ} {f : ℕ → List Bool} (g : Fin n → Matrix (Fin m) (Fin 2 × Fin k) (Rq N K))
    (hf : ∀ t (ht : t < n), f t = colsW N K k m (g ⟨t, ht⟩)) :
    mSum N K k m f n = colsW N K k m (∑ t, g t) := by
  rw [mSum_enc (fun t => if h : t < n then g ⟨t, h⟩ else 0)
    (fun t ht => by rw [dite_eq_left_of_eq_true (eq_true ht)]; exact hf t ht) n le_rfl, ← Fin.sum_univ_eq_sum_range]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [dite_eq_left_of_eq_true (eq_true t.isLt)]

/-- **`∑_b W_b · G̲⁻¹(V_b)` on words**, for `m`-row matrices `W_b`. -/
def keySumMW (N K k m : ℕ) (wW : ℕ → ℕ → ℕ → List Bool) : List Bool :=
  mSum N K k m (fun c => mSum N K k m (fun i => mSum N K k m (fun j =>
    matMulW N K m (2 * k) (2 * k) (wW c i j) (ginvW N K k (vW N K k c i j))) N) k) (2 * k)

theorem keySumMW_enc {m : ℕ} (Wb : Fin 1 × (Fin 2 × Fin k) × Fin k × Fin N →
      Matrix (Fin m) (Fin 2 × Fin k) (Rq N K))
    (wW : ℕ → ℕ → ℕ → List Bool)
    (hw : ∀ (c : Fin (2 * k)) (i : Fin k) (j : Fin N),
      wW c i j = colsW N K k m (Wb (0, colE k c, i, j))) :
    keySumMW N K k m wW = colsW N K k m (∑ b, Wb b *
      (topBin N K k hk).ginv ((coeffBits N (2 ^ K) k hk (Fin 1) (Fin 2 × Fin k)).V b)) := by
  have hsum : (∑ b, Wb b *
      (topBin N K k hk).ginv ((coeffBits N (2 ^ K) k hk (Fin 1) (Fin 2 × Fin k)).V b)) =
      ∑ c : Fin (2 * k), ∑ i : Fin k, ∑ j : Fin N, Wb (0, colE k c, i, j) *
        (topBin N K k hk).ginv ((coeffBits N (2 ^ K) k hk (Fin 1) (Fin 2 × Fin k)).V
          (0, colE k c, i, j)) := by
    rw [Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero,
      Fintype.sum_prod_type, ← (colE k).sum_comp]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Fintype.sum_prod_type]
  rw [hsum, keySumMW]
  apply mSum_fin
  intro c hc
  apply mSum_fin
  intro i hi
  apply mSum_fin
  intro j hj
  rw [hw ⟨c, hc⟩ ⟨i, hi⟩ ⟨j, hj⟩, vW_enc hk ⟨c, hc⟩ ⟨i, hi⟩ ⟨j, hj⟩, ginvW_enc hk,
    colsW_mul_sq]

/-! ### The bits of a Ring-GSW ciphertext -/

/-- The `0/1` ring word of the bit `(a, c, i, t)` of a `2 × Col k` matrix word: bit `i` of the
coefficient `t` of the entry `(a, c)`, `c` at the position `c₁ k + c₂`. -/
def bitsW (N K k : ℕ) (ψ : List Bool) (a c₁ c₂ i t : ℕ) : List Bool :=
  constW N K (bitW K ((block K t (rget N K (a * (2 * k) + (c₁ * k + c₂)) ψ)).getD i false))

theorem bitsW_enc (Ψ : Matrix (Fin 2) (Fin 2 × Fin k) (Rq N K)) (a : Fin 2) (c : Fin 2 × Fin k)
    (i : Fin k) (t : Fin N) :
    bitsW N K k (colsW N K k 2 Ψ) a c.1 c.2 i t =
      (ringEnc N K).enc ((coeffBits N (2 ^ K) k hk (Fin 2) (Fin 2 × Fin k)).bits Ψ (a, c, i, t)) := by
  have hc : c.1.val * k + c.2.val < 2 * k := index_lt c.1 c.2
  have h := rget_matW' (Ψ.submatrix id (colE k)) a ⟨c.1.val * k + c.2.val, hc⟩
  simp only at h
  have hk0 : 0 < k := by have := c.2.isLt; omega
  have hce : colE k ⟨c.1.val * k + c.2.val, hc⟩ = c := by
    rw [colE_apply]
    ext
    · simp only; rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk0, Nat.div_eq_of_lt c.2.isLt,
        zero_add]
    · simp only; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt c.2.isLt]
  rw [bitsW, colsW, h, submatrix_apply, id, hce, block_ringEnc _ t.isLt, getD_enc]
  show _ = (ringEnc N K).enc (algebraMap (ZMod (2 ^ K)) (Rq N K)
    (if ((Ψ a c).coeffs t).val.testBit i then 1 else 0))
  rw [enc_algebraMap, enc_bit]

end SigabaNeo.Lattices.Algo
