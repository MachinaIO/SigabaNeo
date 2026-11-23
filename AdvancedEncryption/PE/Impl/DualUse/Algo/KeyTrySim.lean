import PE.Impl.DualUse.Algo.KeyTry
import PE.Impl.DualUse.Algo.SimKey
import PE.Impl.DualUse.SimKeyGame

/-!
# One try of key generation with the simulated trapdoor, on words

The reductions answer a key query `C` (a window predicate of at most `c.L` bits) with one try of
box rejection with the simulated trapdoor `simTrap W_f`, `W_f = simW d C` (`KGsim`). On words
(`keyTrySimW`), from the word of the public key, the word of `W_f` (`colsW`, as computed by
`simKeyW`) and the coins `l`:

1. `p = emb(coins)` (`embW`);
2. `z = G̲⁻¹(p_pub − B₀ p₀ − B₁ p₁)` (`shortMapW`, `decW`);
3. the simulated shift `W_f z` (`simShiftW`, a matrix-vector product, `simShiftW_eq`);
4. `x = p − (W_f z, 0)` (`simSubW`, `simSubW_eq`) and the ball test;
5. the output: the public key, then `(x, z)` if `x` passes the test, the zero key otherwise.

The key matrix `B_f̂` is not read: the simulated trapdoor does not depend on it.

* `keyTrySimW_eq`: `keyTrySimW` is the word (`skEnc`) of `(mpk, keyOfOutput (boxTry … (simTrap W) …))`;
* `KGsim_words`: on program words of at most `c.L` bits, `KGsim d C` is the image of `m` fair
  coins under `keyTrySimW` with `W_f = simW d C`.
-/

namespace AdvancedEncryption.DualUse.Algo

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo Matrix Cslib
  Cslib.Probability AdvancedEncryption.RingBTVW AdvancedEncryption.PE
  AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord

variable {N K k : ℕ}

/-! ### Vectors on `Fin d` are columns -/

theorem vecW_fin {d : ℕ} (v : Fin d → Rq N K) :
    vecW N K v = matW N K d 1 (Matrix.of fun i _ => v i) := by
  rw [vecW, fun_enc_concatN]
  have hl : (Enum.list (α := Fin d)).length = d * 1 := by rw [len_fin, Nat.mul_one]
  conv_lhs => arg 1; rw [hl]
  apply concatN_eq_matW
  intro p hp
  have hp' : p < (Enum.list (α := Fin d)).length := hl ▸ hp
  rw [dite_eq_left_of_eq_true (eq_true hp')]
  congr 2
  show (List.finRange d)[p] = _
  ext
  simp

/-! ### The simulated shift -/

/-- **The simulated shift `W_f z`** on words: the product of the `d × 2k` matrix `W_f` and the
column `z`. -/
def simShiftW (N K k d : ℕ) (wfW zW : List Bool) : List Bool := matMulW N K d (2 * k) 1 wfW zW

theorem simShiftW_eq {d : ℕ} (W : Matrix (Fin d) (Col k) (Rq N K)) (z : Col k → Rq N K) :
    simShiftW N K k d (colsW N K k d W) (vecW N K z) = vecW N K (W *ᵥ z) := by
  rw [simShiftW, vecW_colW z, colsW, matMulW_enc, vecW_fin]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.of_apply, Matrix.mulVec,
    dotProduct, id]
  exact (colE k).sum_comp (fun c => W i c * z c)

/-- **`x = p − (T, 0)`** on words: subtract on `p₀`, copy `p₁`. -/
def simSubW (N K d : ℕ) (pW TW : List Bool) : List Bool :=
  matSubW N K d (pW.take (d * (N * K))) TW ++ pW.drop (d * (N * K))

theorem simSubW_eq {d : ℕ} {Wt : Type} [Enum Wt] (p : DualUse.KeyShort (Fin d) Wt (Rq N K))
    (T : Fin d → Rq N K) :
    simSubW N K d (shortW N K p) (vecW N K T) = shortW N K (p - (T, (0 : Wt → Rq N K))) := by
  have h := matSubW_vecW (N := N) (K := K) p.1 T
  rw [len_fin] at h
  rw [simSubW, take_shortW, drop_shortW, h, shortW]
  simp

/-! ### One try -/

/-- **One try of key generation with the simulated trapdoor, on words**, from the word of the
public key, the word of `W_f` and the coins `l`. -/
def keyTrySimW (N K k d B : ℕ) (sW pkW wfW l : List Bool) : List Bool :=
  -- the big-box element `p`
  let pW := embW ((d + nT k) * N) B K l
  -- `z = G̲⁻¹(p_pub − B₀ p₀ − B₁ p₁)`
  let zW := decW N K k (subRW N K (pkW.drop (pkW.length - N * K))
    (shortMapW N K d (nT k) (pkW.take (d * (N * K)))
      ((pkW.drop (d * (N * K))).take (nT k * (N * K))) pW))
  -- `x = p − (W_f z, 0)`
  let xW := simSubW N K d pW (simShiftW N K k d wfW zW)
  pkW ++ if ballW ((d + nT k) * N) K sW xW = true then xW ++ zW
    else zeroW (d * (N * K)) ++ (zeroW (nT k * (N * K)) ++ zeroW (2 * k * (N * K)))

/-- **`keyTrySimW` computes one try with the simulated trapdoor**, for a configuration whose small
box is the ball of radius `S`, whose decomposition is binary and whose big box is read with
`keyEmbE`. -/
theorem keyTrySimW_eq (hk : 2 ^ K < 2 ^ k) (h0 : 0 < k) (c : DualUse.Conf N K k) (B : ℕ)
    (hB : 2 ^ B ≤ 2 ^ K) (m : ℕ) (hm : nCoef c.d (DualUse.TrapCol k) N * B = m) {S : ℕ}
    {sW : List Bool} (hs : sW.length = K) (hS : val sW = S)
    (hSmall : c.Small = DualUse.keyBall (2 ^ K) c.d (DualUse.TrapCol k) N S)
    (hdec : c.dec = decG hk h0) (mpk : DualUse.PK hk c)
    (W : Matrix (Fin c.d) (Col k) (DualUse.Rg N K)) (l : List Bool) :
    keyTrySimW N K k c.d B sW ((DualUse.pkEnc hk c).enc mpk) (colsW N K k c.d W) l =
      (DualUse.skEnc hk c).enc (mpk, DualUse.keyOfOutput
        (boxTry c.Small (DualUse.shortMap mpk) c.dec (DualUse.simTrap (Wt := DualUse.TrapCol k) W)
          mpk.p (keyEmbE (d := c.d) (Wt := DualUse.TrapCol k) (N := N) B hB m hm
            (SigabaNeo.Lattices.Algo.bitsOf m l)))) := by
  set p := keyEmbE (d := c.d) (Wt := DualUse.TrapCol k) (N := N) B hB m hm
    (SigabaNeo.Lattices.Algo.bitsOf m l) with hp
  have hpW : embW ((c.d + nT k) * N) B K l = shortW N K p := by
    rw [← nCoef_trap]; exact embW_eq B hB m hm l
  obtain ⟨g1, g2, g3⟩ := pkEnc_blocks hk c mpk
  unfold keyTrySimW
  dsimp only
  rw [g1, g2, g3, hpW, shortMapW_eq hk mpk p, subRW_enc, decW_vec hk h0, ← hdec, simShiftW_eq,
    simSubW_eq, ← nCoef_trap, ballW_shortW hs hS, ← hSmall]
  set z := c.dec (mpk.p - DualUse.shortMap mpk p)
  have hx : p - (W *ᵥ z, (0 : DualUse.TrapCol k → DualUse.Rg N K)) =
      p - DualUse.simTrap (Wt := DualUse.TrapCol k) W z := rfl
  rw [hx]
  set x := p - DualUse.simTrap (Wt := DualUse.TrapCol k) W z
  show _ = (DualUse.pkEnc hk c).enc mpk ++ (DualUse.keyEnc (N := N) (K := K) c).enc
    (DualUse.keyOfOutput (if x ∈ c.Small then some (x, z) else none))
  by_cases hxs : x ∈ c.Small
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (decide_eq_true hxs)),
      ite_eq_left_of_eq_true _ _ (eq_true hxs), keyEnc_eq, shortW, List.append_assoc]
    rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by simpa using hxs)),
      ite_eq_right_of_eq_false _ _ (eq_false hxs)]
    exact congrArg _ (keyEnc_zero c).symm

/-! ### The law of the simulated key oracle -/

theorem keyLaw_big_congr {R : Type*} [CommRing R] [DecidableEq R] {k' : ℕ} {S : Setting R k'}
    {Wd Wt : Type*} [Fintype Wd] [Fintype Wt] (s t : Finset (DualUse.KeyShort Wd Wt R))
    (Small : Finset (DualUse.KeyShort Wd Wt R)) (h1 : s.Nonempty) (h2 : t.Nonempty)
    (dec : R → (Col k' → R)) (mpk : DualUse.MPK S Wd Wt)
    (T : (Col k' → R) → DualUse.KeyShort Wd Wt R) (h : s = t) :
    DualUse.keyLaw s Small h1 dec mpk T = DualUse.keyLaw t Small h2 dec mpk T := by
  subst h; rfl

/-- **The simulated key oracle on words**: on a window predicate of at most `c.L` bits, `KGsim`
is the image of `m` fair coins under `keyTrySimW` with the word of `W_f = simW d C`. -/
theorem KGsim_words (hk : 2 ^ K < 2 ^ k) (h0 : 0 < k) {c : DualUse.Conf N K k} (B : ℕ)
    (hB : 2 ^ B ≤ 2 ^ K) (m : ℕ) (hm : nCoef c.d (DualUse.TrapCol k) N * B = m)
    (hBig : c.Big =
      Finset.univ.map (keyEmbE (d := c.d) (Wt := DualUse.TrapCol k) (N := N) B hB m hm))
    {S : ℕ} {sW : List Bool} (hs : sW.length = K) (hS : val sW = S)
    (hSmall : c.Small = DualUse.keyBall (2 ^ K) c.d (DualUse.TrapCol k) N S)
    (hdec : c.dec = decG hk h0) (sd : DualUse.SimData hk c) (C : List Bool) (hL : C.length ≤ c.L)
    (hC : ValidC C) :
    DualUse.KGsim sd C = (BitString.uniformList m).map
      (keyTrySimW N K k c.d B sW ((DualUse.pkEnc hk c).enc sd.mpk)
        (colsW N K k c.d (DualUse.simW sd C))) := by
  unfold DualUse.KGsim
  rw [if_pos hL, if_pos hC,
    keyLaw_big_congr _ _ _ c.hBig Finset.univ_nonempty.map _ _ _ hBig, keyLaw_coins,
    PMF.map_comp]
  congr 1
  funext l
  exact (keyTrySimW_eq hk h0 c B hB m hm hs hS hSmall hdec sd.mpk _ l).symm

/-! ### For `confP` -/

namespace Params

set_option maxRecDepth 100000

open AdvancedEncryption.DualUse.Params

end Params

end AdvancedEncryption.DualUse.Algo
