import PE.Impl.RingBTVW.Algo.KeyWords
import PE.Impl.RingBTVW.Algo.KeyCoins
import PE.Impl.RingBTVW.Params.Conf

/-!
# One try of key generation on words

One try of box rejection of `KeyGen` (`RingBTVW.keyTry`), as explicit loops on words, generic in the
sizes `(N, K, k, d, B)` and the radius `S` (given by its word `sW`):

1. `p = emb(coins)`: `embW` writes the `n = (d + 1 + 4k) N` centered coefficients of the big-box
   element (`embW_eq`, with the explicit layout `keyEmbE`);
2. `u = p_pub − B₀ p₀ − B₁ p₁` (`shortMapW_eq`);
3. `z = G̲⁻¹(u)`, the binary decomposition (`decW_vec`);
4. the real trapdoor shift `T z = (0, [e; t I; I] · G̲⁻¹(B_f̂ − G̲) · z)` (`trapShiftW_eq`), with
   `B_f̂` given by its word (computed by `keyMatrixW`, `keyMatrixW_eq`);
5. `x = p − T z` (`subShiftW_eq`) and the ball test `x ∈ keyBall S` (`ballW_shortW`);
6. the output: the public key, then `(x, z)` if the predicate is in the class and `x` passes the
   test, the zero key otherwise.

`keyTryMskW` reads the public key and the trapdoor `(e, t)` from the word of the master secret key.
**`keyTryMskW_eq`**: it is the word (`skEnc`) of `keyTry msk C (keyEmbE … (bitsOf m l))`.

For `confP` (`keyM_words`): the law of the words of the keys of `KeyGen` is the image of `mBp` fair
coins under `keyTryMskW` with the radius word `toBits Kp Sp` (the big boxes of `keyEmb` and of the
explicit layout `keyEmbE` are equal, `univ_map_keyEmbE_eq`). (`B_f̂` is given by its word.)

Step count: `keyTrySteps` (sum of the steps of the parts).
-/

namespace AdvancedEncryption.RingBTVW.Algo

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo Matrix Cslib
  Cslib.Probability AdvancedEncryption.RingBTVW.Fresh AdvancedEncryption.PE
  AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord

variable {N K k : ℕ}

/-- The number of ring entries of `k₁` (the columns `TrapCol k` of `B₁`). -/
abbrev nT (k : ℕ) : ℕ := 1 + (2 * k + 2 * k)

/-! ### The binary decomposition -/

/-- The binary decomposition of `confP`, for any sizes: the column `(0, 0)` of `G̲⁻¹`. -/
noncomputable def decG (hk : 2 ^ K < 2 ^ k) (h0 : 0 < k) (u : RingBTVW.Rg N K) :
    Col k → RingBTVW.Rg N K :=
  fun c => (RingBTVW.Sdw (N := N) hk).Γ₁.ginv (Matrix.of fun _ _ => u) c (0, ⟨0, h0⟩)

theorem decp_eq : Params.decp = decG Params.hkp (Nat.succ_pos _) := rfl

/-- **The binary decomposition on words.** -/
theorem decW_vec (hk : 2 ^ K < 2 ^ k) (h0 : 0 < k) (u : RingBTVW.Rg N K) :
    decW N K k ((ringEnc N K).enc u) = vecW N K (decG hk h0 u) := by
  rw [decW_enc hk.le u (0, ⟨0, h0⟩), vecW_col]
  rfl

/-! ### The public map -/

/-- **`B₀ p₀ + B₁ p₁`** on words: two dot products (`d` and `L` entries) and a sum. -/
def shortMapW (N K d L : ℕ) (b0W b1W pW : List Bool) : List Bool :=
  addRW N K (dotW N K d b0W (pW.take (d * (N * K)))) (dotW N K L b1W (pW.drop (d * (N * K))))

theorem take_shortW {d : ℕ} {Wt : Type} [Enum Wt] (x : RingBTVW.KeyShort (Fin d) Wt (Rq N K)) :
    (shortW N K x).take (d * (N * K)) = vecW N K x.1 :=
  List.take_left' (by rw [length_vecW, len_fin])

theorem drop_shortW {d : ℕ} {Wt : Type} [Enum Wt] (x : RingBTVW.KeyShort (Fin d) Wt (Rq N K)) :
    (shortW N K x).drop (d * (N * K)) = vecW N K x.2 :=
  List.drop_left' (by rw [length_vecW, len_fin])

theorem shortMapW_eq (hk : 2 ^ K < 2 ^ k) {d : ℕ}
    (mpk : RingBTVW.MPK (RingBTVW.Sdw (N := N) hk) (Fin d) (RingBTVW.TrapCol k))
    (x : RingBTVW.KeyShort (Fin d) (RingBTVW.TrapCol k) (RingBTVW.Rg N K)) :
    shortMapW N K d (nT k) (vecW N K (mpk.B₀ 0)) (vecW N K (mpk.B₁ 0))
        (shortW N K x) = (ringEnc N K).enc (RingBTVW.shortMap mpk x) := by
  have h0 := dotW_vecW (N := N) (K := K) (mpk.B₀ 0) x.1
  have h1 := dotW_vecW (N := N) (K := K) (mpk.B₁ 0) x.2
  rw [len_fin] at h0
  rw [len_trapCol] at h1
  rw [shortMapW, take_shortW, drop_shortW, h0, h1, addRW_enc]
  rfl

/-! ### The real trapdoor shift -/

/-- **The shift `[e; t I; I] · G̲⁻¹(B_f̂ − G̲) · z`** on words: `y = G̲⁻¹(B_f̂ − G̲) z`, then
`(e · y, t y, y)`. -/
def trapShiftW (N K k : ℕ) (eW tW bfW zW : List Bool) : List Bool :=
  let yW := matMulW N K (2 * k) (2 * k) 1 (ginvW N K k (matSubW N K (1 * (2 * k)) bfW (gadW N K k))) zW
  dotW N K (2 * k) eW yW ++ (smulVW N K (2 * k) tW yW ++ yW)

/-- The matrix-vector product on the gadget columns. -/
theorem matMulW_vec (M : Matrix (Col k) (Col k) (Rq N K)) (z : Col k → Rq N K) :
    matMulW N K (2 * k) (2 * k) 1 (sqW N K k M) (vecW N K z) = vecW N K (M *ᵥ z) := by
  rw [vecW_colW z, sqW, matMulW_enc, vecW_colW]
  congr 1
  refine Matrix.ext fun p j => ?_
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.of_apply, Matrix.mulVec,
    dotProduct]
  exact (colE k).sum_comp (fun c => M (colE k p) c * z c)

theorem trapMat_mulVec (e : Matrix (Fin 1) (Col k) (Rq N K)) (t : Rq N K) (y : Col k → Rq N K) :
    (RingBTVW.trapMat e t *ᵥ y) =
      Sum.elim (fun _ => ∑ c, e 0 c * y c) (Sum.elim (fun c => t * y c) y) := by
  funext i
  rcases i with i | i | i
  · rw [Fin.fin_one_eq_zero i]
    simp [RingBTVW.trapMat, Matrix.mulVec, dotProduct]
  · simp [RingBTVW.trapMat, Matrix.mulVec, dotProduct, ite_mul]
  · simp [RingBTVW.trapMat, Matrix.mulVec, dotProduct, ite_mul]

theorem rowW_eq_vecW (e : Matrix (Fin 1) (Col k) (Rq N K)) : rowW N K k e = vecW N K (e 0) := by
  rw [vecW_col]
  congr 1
  ext i c
  rw [Fin.fin_one_eq_zero i]
  rfl

/-- **The trapdoor shift on words.** -/
theorem trapShiftW_eq (hk : 2 ^ K < 2 ^ k) (e Bf : Matrix (Fin 1) (Col k) (RingBTVW.Rg N K))
    (t : RingBTVW.Rg N K) (z : Col k → RingBTVW.Rg N K) :
    trapShiftW N K k (rowW N K k e) ((ringEnc N K).enc t) (rowW N K k Bf) (vecW N K z) =
      vecW N K ((RingBTVW.trapMat e t *
        (RingBTVW.Sdw (N := N) hk).Γ₁.ginv (Bf - (RingBTVW.Sdw (N := N) hk).Γ₁.G)) *ᵥ z) := by
  have hD : matSubW N K (1 * (2 * k)) (rowW N K k Bf) (gadW N K k) =
      rowW N K k (Bf - (topBin N K k hk.le).G) := by
    rw [gadW_enc hk.le]
    simp only [rowW]
    rw [matSubW_enc]
    rfl
  have hY : matMulW N K (2 * k) (2 * k) 1
      (ginvW N K k (matSubW N K (1 * (2 * k)) (rowW N K k Bf) (gadW N K k))) (vecW N K z) =
      vecW N K ((RingBTVW.Sdw (N := N) hk).Γ₁.ginv (Bf - (RingBTVW.Sdw (N := N) hk).Γ₁.G) *ᵥ z) := by
    rw [hD, ginvW_enc hk.le, matMulW_vec]
    rfl
  rw [trapShiftW, hY, ← Matrix.mulVec_mulVec, trapMat_mulVec, vecW_sum, vecW_sum, vecW_fin1,
    rowW_eq_vecW]
  set y := (RingBTVW.Sdw (N := N) hk).Γ₁.ginv (Bf - (RingBTVW.Sdw (N := N) hk).Γ₁.G) *ᵥ z
  have h1 := dotW_vecW (N := N) (K := K) (e 0) y
  have h2 := smulVW_vecW (N := N) (K := K) t y
  rw [len_col] at h1 h2
  rw [h1, h2]
  rfl

/-! ### The shifted key -/

/-- **`x = p − (0, T)`** on words: copy `p₀`, subtract on `p₁`. -/
def subShiftW (N K d L : ℕ) (pW TW : List Bool) : List Bool :=
  pW.take (d * (N * K)) ++ matSubW N K L (pW.drop (d * (N * K))) TW

theorem subShiftW_eq {d : ℕ} (p : RingBTVW.KeyShort (Fin d) (RingBTVW.TrapCol k) (Rq N K))
    (T : RingBTVW.TrapCol k → Rq N K) :
    subShiftW N K d (nT k) (shortW N K p) (vecW N K T) =
      shortW N K (p - ((0 : Fin d → Rq N K), T)) := by
  have h := matSubW_vecW (N := N) (K := K) p.2 T
  rw [len_trapCol] at h
  rw [subShiftW, take_shortW, drop_shortW, h, shortW]
  simp

/-! ### Reading the words of the keys -/


theorem nCoef_trap (d : ℕ) : nCoef d (RingBTVW.TrapCol k) N = (d + nT k) * N := by
  show ((Enum.list (α := Fin d ⊕ RingBTVW.TrapCol k)).product (Enum.list (α := Fin N))).length = _
  rw [length_product', len_fin]
  show ((Enum.list (α := Fin d)).map Sum.inl ++
    (Enum.list (α := RingBTVW.TrapCol k)).map Sum.inr).length * N = _
  rw [List.length_append, List.length_map, List.length_map, len_fin, len_trapCol]

/-- A word made of three parts, read back from the lengths of the last two. -/
theorem split3 (a b c : List Bool) {β γ : ℕ} (hb : b.length = β) (hc : c.length = γ) :
    (a ++ (b ++ c)).take ((a ++ (b ++ c)).length - (β + γ)) = a ∧
      ((a ++ (b ++ c)).drop ((a ++ (b ++ c)).length - (β + γ))).take β = b ∧
      (a ++ (b ++ c)).drop ((a ++ (b ++ c)).length - γ) = c := by
  have hl : (a ++ (b ++ c)).length - (β + γ) = a.length := by
    simp only [List.length_append, hb, hc]; omega
  refine ⟨by rw [hl]; exact List.take_left' rfl, by rw [hl, List.drop_left' rfl]; exact List.take_left' hb,
    ?_⟩
  rw [← List.append_assoc]
  exact List.drop_left' (by simp only [List.length_append, hb, hc]; omega)

/-- **The word of a master secret key**: the public key, `e`, `t`. -/
theorem mskEnc_eq (hk : 2 ^ K < 2 ^ k) (c : RingBTVW.Conf N K k) (msk : RingBTVW.SKey hk c) :
    (RingBTVW.mskEnc hk c).enc msk =
      (RingBTVW.pkEnc hk c).enc msk.1 ++ (rowW N K k msk.2.1 ++ (ringEnc N K).enc msk.2.2) := by
  show (RingBTVW.pkEnc hk c).enc msk.1 ++ ((RingBTVW.matEnc (N := N) (K := K) (Fin 1) (Col k)).enc
    msk.2.1 ++ (ringEnc N K).enc msk.2.2) = _
  rw [matEnc_row]

theorem length_rowW (B : Matrix (Fin 1) (Col k) (Rq N K)) : (rowW N K k B).length = 2 * k * (N * K) := by
  rw [rowW, length_matW, Nat.one_mul]

/-- **The blocks of a public key**: `B₀`, `B₁`, and `p` at the end. -/
theorem pkEnc_blocks (hk : 2 ^ K < 2 ^ k) (c : RingBTVW.Conf N K k) (m : RingBTVW.PK hk c) :
    ((RingBTVW.pkEnc hk c).enc m).take (c.d * (N * K)) = vecW N K (m.B₀ 0) ∧
      (((RingBTVW.pkEnc hk c).enc m).drop (c.d * (N * K))).take (nT k * (N * K)) =
        vecW N K (m.B₁ 0) ∧
      ((RingBTVW.pkEnc hk c).enc m).drop (((RingBTVW.pkEnc hk c).enc m).length - N * K) =
        (ringEnc N K).enc m.p := by
  have he : (RingBTVW.pkEnc hk c).enc m = vecW N K (m.B₀ 0) ++ (vecW N K (m.B₁ 0) ++
      ((FixedEnc.fun (α := (RingBTVW.Sdw (N := N) hk).Attr × (RingBTVW.Sdw (N := N) hk).ctBits.Index)
        (RingBTVW.matEnc (N := N) (K := K) (Fin 1) (Col k))).enc m.Bj ++ (ringEnc N K).enc m.p)) := by
    show (RingBTVW.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc m.B₀ ++
      ((RingBTVW.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.TrapCol k)).enc m.B₁ ++
      ((FixedEnc.fun (α := (RingBTVW.Sdw (N := N) hk).Attr × (RingBTVW.Sdw (N := N) hk).ctBits.Index)
        (RingBTVW.matEnc (N := N) (K := K) (Fin 1) (Col k))).enc m.Bj ++ (ringEnc N K).enc m.p)) = _
    rw [matEnc_row1, matEnc_row1]
  have l0 : (vecW N K (m.B₀ 0)).length = c.d * (N * K) := by rw [length_vecW, len_fin]
  have l1 : (vecW N K (m.B₁ 0)).length = nT k * (N * K) := by rw [length_vecW, len_trapCol]
  rw [he]
  refine ⟨List.take_left' l0, by rw [List.drop_left' l0]; exact List.take_left' l1, ?_⟩
  simp only [← List.append_assoc]
  exact List.drop_left' (by simp only [List.length_append, (ringEnc N K).length]; omega)

/-- **The zero key.** -/
theorem keyEnc_zero (c : RingBTVW.Conf N K k) :
    (RingBTVW.keyEnc (N := N) (K := K) c).enc ⟨0, 0, 0⟩ =
      zeroW (c.d * (N * K)) ++ (zeroW (nT k * (N * K)) ++ zeroW (2 * k * (N * K))) := by
  rw [keyEnc_eq]
  erw [vecW_zero, vecW_zero, vecW_zero]
  rw [len_fin, len_trapCol, len_col]

/-! ### One try -/

/-- **One try of key generation on words**, from the words of the public key, of `e` and `t`, of
the key row `B_f̂`, and the coins `l`; `inC` says whether the predicate is in the class. -/
def keyTryCoreW (N K k d B : ℕ) (sW : List Bool) (inC : Bool) (pkW eW tW bfW l : List Bool) :
    List Bool :=
  -- the big-box element `p`
  let pW := embW ((d + nT k) * N) B K l
  -- `z = G̲⁻¹(p_pub − B₀ p₀ − B₁ p₁)`
  let zW := decW N K k (subRW N K (pkW.drop (pkW.length - N * K))
    (shortMapW N K d (nT k) (pkW.take (d * (N * K)))
      ((pkW.drop (d * (N * K))).take (nT k * (N * K))) pW))
  -- `x = p − T z`
  let xW := subShiftW N K d (nT k) pW (trapShiftW N K k eW tW bfW zW)
  pkW ++ if (inC && ballW ((d + nT k) * N) K sW xW) = true then xW ++ zW
    else zeroW (d * (N * K)) ++ (zeroW (nT k * (N * K)) ++ zeroW (2 * k * (N * K)))

/-- **One try of key generation on words**, from the word of the master secret key. -/
def keyTryMskW (N K k d B : ℕ) (sW : List Bool) (inC : Bool) (mskW bfW l : List Bool) :
    List Bool :=
  keyTryCoreW N K k d B sW inC (mskW.take (mskW.length - (2 * k * (N * K) + N * K)))
    ((mskW.drop (mskW.length - (2 * k * (N * K) + N * K))).take (2 * k * (N * K)))
    (mskW.drop (mskW.length - N * K)) bfW l

/-- **`keyTryMskW` computes one try of `KeyGen`**, for a configuration whose small box is the ball
of radius `S`, whose decomposition is binary and whose big box is read with `keyEmbE`. -/
theorem keyTryMskW_eq (hk : 2 ^ K < 2 ^ k) (h0 : 0 < k) (c : RingBTVW.Conf N K k) (B : ℕ)
    (hB : 2 ^ B ≤ 2 ^ K) (m : ℕ) (hm : nCoef c.d (RingBTVW.TrapCol k) N * B = m) {S : ℕ}
    {sW : List Bool} (hs : sW.length = K) (hS : val sW = S)
    (hSmall : c.Small = RingBTVW.keyBall (2 ^ K) c.d (RingBTVW.TrapCol k) N S)
    (hdec : c.dec = decG hk h0) (msk : RingBTVW.SKey hk c) (C : List Bool) (inC : Bool)
    (hC : inC = true ↔ ValidC C) (bfW : List Bool)
    (hbf : bfW = rowW N K k (RingBTVW.keyMatrix msk.1 (RingBTVW.predC C))) (l : List Bool) :
    keyTryMskW N K k c.d B sW inC ((RingBTVW.mskEnc hk c).enc msk) bfW l =
      (RingBTVW.skEnc hk c).enc (RingBTVW.keyTry hk c msk C
        (keyEmbE (d := c.d) (Wt := RingBTVW.TrapCol k) (N := N) B hB m hm
          (SigabaNeo.Lattices.Algo.bitsOf m l))) := by
  set p := keyEmbE (d := c.d) (Wt := RingBTVW.TrapCol k) (N := N) B hB m hm
    (SigabaNeo.Lattices.Algo.bitsOf m l) with hp
  have hpW : embW ((c.d + nT k) * N) B K l = shortW N K p := by
    rw [← nCoef_trap]; exact embW_eq B hB m hm l
  obtain ⟨h1, h2, h3⟩ := split3 ((RingBTVW.pkEnc hk c).enc msk.1) (rowW N K k msk.2.1)
    ((ringEnc N K).enc msk.2.2) (length_rowW _) ((ringEnc N K).length _)
  obtain ⟨g1, g2, g3⟩ := pkEnc_blocks hk c msk.1
  unfold keyTryMskW keyTryCoreW
  dsimp only
  rw [mskEnc_eq, h1, h2, h3, g1, g2, g3, hpW, shortMapW_eq hk msk.1 p, subRW_enc,
    decW_vec hk h0, ← hdec, hbf, trapShiftW_eq hk, subShiftW_eq, ← nCoef_trap,
    ballW_shortW hs hS, ← hSmall]
  set z := c.dec (msk.1.p - RingBTVW.shortMap msk.1 p)
  have hx : p - ((0 : Fin c.d → RingBTVW.Rg N K), (RingBTVW.trapMat msk.2.1 msk.2.2 *
      (RingBTVW.Sdw (N := N) hk).Γ₁.ginv (RingBTVW.keyMatrix msk.1 (RingBTVW.predC C) -
        (RingBTVW.Sdw (N := N) hk).Γ₁.G)) *ᵥ z) =
      p - RingBTVW.realTrap (S := RingBTVW.Sdw (N := N) hk) (Wd := Fin c.d)
        (RingBTVW.trapMat msk.2.1 msk.2.2) (RingBTVW.keyMatrix msk.1 (RingBTVW.predC C)) z := rfl
  rw [hx]
  set x := p - RingBTVW.realTrap (S := RingBTVW.Sdw (N := N) hk) (Wd := Fin c.d)
    (RingBTVW.trapMat msk.2.1 msk.2.2) (RingBTVW.keyMatrix msk.1 (RingBTVW.predC C)) z
  show _ = (RingBTVW.pkEnc hk c).enc (RingBTVW.keyTry hk c msk C p).1 ++
    (RingBTVW.keyEnc (N := N) (K := K) c).enc (RingBTVW.keyTry hk c msk C p).2
  by_cases hcl : ValidC C
  · have hinC : inC = true := hC.mpr hcl
    have hT : RingBTVW.keyTry hk c msk C p = RingBTVW.keyTryW hk c msk C p := by
      simp [RingBTVW.keyTry, hcl]
    rw [hT, hinC, Bool.true_and]
    by_cases hxs : x ∈ c.Small
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (decide_eq_true hxs))]
      show _ = _ ++ (RingBTVW.keyEnc (N := N) (K := K) c).enc
        (RingBTVW.keyOfOutput (if x ∈ c.Small then some (x, z) else none))
      rw [ite_eq_left_of_eq_true _ _ (eq_true hxs), keyEnc_eq, shortW, List.append_assoc]
      rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by simpa using hxs))]
      show _ = _ ++ (RingBTVW.keyEnc (N := N) (K := K) c).enc
        (RingBTVW.keyOfOutput (if x ∈ c.Small then some (x, z) else none))
      rw [ite_eq_right_of_eq_false _ _ (eq_false hxs)]
      exact congrArg _ (keyEnc_zero c).symm
  · have hinC : inC = false := by
      cases inC
      · rfl
      · exact absurd (hC.mp rfl) hcl
    have hT : RingBTVW.keyTry hk c msk C p = (msk.1, RingBTVW.dummyKey c) := by
      simp [RingBTVW.keyTry, hcl]
    rw [hT, hinC, Bool.false_and, ite_eq_right_of_eq_false _ _ (eq_false Bool.false_ne_true)]
    exact congrArg _ (keyEnc_zero c).symm

/-! ### `KeyGen` for `confP` -/

/-- **`KeyGen` from fair coins, with the explicit layout of the big box.** -/
theorem keyM_coinsE (hk : 2 ^ K < 2 ^ k) (c : RingBTVW.Conf N K k) (B : ℕ) (hB : 2 ^ B ≤ 2 ^ K)
    (m : ℕ) (hm : nCoef c.d (RingBTVW.TrapCol k) N * B = m)
    (hBig : c.Big = Finset.univ.map (keyEmbE (d := c.d) (Wt := RingBTVW.TrapCol k) (N := N) B hB m hm))
    (msk : RingBTVW.SKey hk c) (C : List Bool) :
    RingBTVW.keyM hk c msk C = (BitString.uniformList m).map (fun l => RingBTVW.keyTry hk c msk C
      (keyEmbE (d := c.d) (Wt := RingBTVW.TrapCol k) (N := N) B hB m hm
        (SigabaNeo.Lattices.Algo.bitsOf m l))) := by
  have key : ∀ (s t : Finset (RingBTVW.KeyShort (Fin c.d) (RingBTVW.TrapCol k) (RingBTVW.Rg N K)))
      (h1 : s.Nonempty) (h2 : t.Nonempty), s = t →
      PMF.uniformOfFinset s h1 = PMF.uniformOfFinset t h2 := by
    rintro s _ h1 h2 rfl; rfl
  unfold RingBTVW.keyM
  rw [key _ _ c.hBig Finset.univ_nonempty.map hBig, uniformOfFinset_map_eq, PMF.map_comp,
    Function.comp_def]

namespace Params

set_option maxRecDepth 100000

open AdvancedEncryption.RingBTVW.Params

theorem hmE : nCoef dp (RingBTVW.TrapCol kp) Np * Bp = mBp := by
  rw [nCoef_eq_card]; exact hmBp

/-- The big box of `confP` with the explicit layout. -/
theorem big_eqE : confP.Big =
    Finset.univ.map (keyEmbE (d := dp) (Wt := RingBTVW.TrapCol kp) (N := Np) Bp hBp mBp hmE) := by
  rw [univ_map_keyEmbE_eq Bp hBp mBp hmE hmBp]
  rfl

/-- The word of the radius `Sp`. -/
noncomputable def SpW : List Bool := toBits Kp Sp

theorem length_SpW : SpW.length = Kp := length_toBits _ _

theorem val_SpW : val SpW = Sp := by
  rw [SpW, val_toBits, Nat.mod_eq_of_lt]
  have h1 : 2 ^ (Bp - 1) < 2 ^ Bp :=
    Nat.pow_lt_pow_right (by norm_num) (by have := one_le_Bp; omega)
  exact lt_of_le_of_lt Sp_le (lt_of_lt_of_le h1 hBp)

/-- **The words of the keys of `KeyGen` for `confP`**: the image of `mBp` fair coins under one try
on words, for the key row `B_f̂` given by its word. -/
theorem keyM_words (msk : RingBTVW.SKey hkp confP) (C : List Bool) (inC : Bool)
    (hC : inC = true ↔ ValidC C) (bfW : List Bool)
    (hbf : bfW = rowW Np Kp kp (RingBTVW.keyMatrix msk.1 (RingBTVW.predC C))) :
    (RingBTVW.keyM hkp confP msk C).map (RingBTVW.skEnc hkp confP).enc =
      (BitString.uniformList mBp).map
        (keyTryMskW Np Kp kp dp Bp SpW inC ((RingBTVW.mskEnc hkp confP).enc msk) bfW) := by
  rw [keyM_coinsE hkp confP Bp hBp mBp hmE big_eqE, PMF.map_comp]
  congr 1
  funext l
  exact (keyTryMskW_eq hkp (Nat.succ_pos _) confP Bp hBp mBp hmE length_SpW val_SpW rfl decp_eq
    msk C inC hC bfW hbf l).symm

end Params

/-! ### Step counts -/

/-- Steps of `dotW` on `n` entries: per entry two block copies and a product, then the sum. -/
def dotSteps (N K n : ℕ) : ℕ := n * (2 * (N * K) + mulRSteps N K) + sumSteps N K n

/-- Steps of `shortMapW`: splitting `p`, the two dot products, the sum. -/
def shortMapSteps (N K d L : ℕ) : ℕ :=
  (d + L) * (N * K) + dotSteps N K d + dotSteps N K L + addRSteps N K

/-- Steps of `trapShiftW`: `B_f̂ − G̲`, `G̲⁻¹`, `y = G̲⁻¹(B_f̂ − G̲) z`, then `e · y`, `t y`, `y`. -/
def trapShiftSteps (N K k : ℕ) : ℕ :=
  gadSteps N K k + 2 * k * (2 * (N * K) + addRSteps N K) + ginvSteps N K k +
    matMulSteps N K (2 * k) (2 * k) 1 + dotSteps N K (2 * k) +
    2 * k * (N * K + mulRSteps N K) + 2 * k * (N * K)

/-- Steps of `subShiftW`: copy `p₀`, subtract on `p₁`. -/
def subShiftSteps (N K d L : ℕ) : ℕ := d * (N * K) + L * (2 * (N * K) + addRSteps N K)

/-- **Steps of one try** (`keyTryMskW`), for a public key of `P` bits: reading `(pk, e, t)` and the
blocks `B₀`, `B₁`, `p_pub` of `pk`, the coins (`embSteps`), `u`, `z`, the shift, `x`, the ball
test, and writing the output (the public key and a key). -/
def keyTrySteps (N K k d B P : ℕ) : ℕ :=
  (P + 2 * k * (N * K) + N * K) + ((d + nT k) * (N * K) + N * K) +
    embSteps ((d + nT k) * N) B K + shortMapSteps N K d (nT k) + addRSteps N K +
    decSteps N K k + trapShiftSteps N K k + subShiftSteps N K d (nT k) +
    ballSteps ((d + nT k) * N) K + 1 +
    (P + (d + nT k) * (N * K) + 2 * k * (N * K))

end AdvancedEncryption.RingBTVW.Algo
