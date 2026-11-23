import PE.Impl.DualUse.ImplCorrect
import PE.Impl.DualUse.ParamSupport
import PE.Impl.DualUse.KeyBoxes
import PE.Impl.DualUse.Params.Sizes

/-!
# A configuration covering real and simulated keys

The configuration `confP` over `R = ℤ_{2^K}[X]/(X^N + 1)` with the sizes of `Params/Sizes.lean`
(`K = 2^27`, `N = 2^36`, `|Wd| = 2^65`): errors from the centered binomial law of width `16`,
flooding below `2^768`, big box of `B = 51056224` bits per coefficient, small box of radius
`S = 2^{B−1} − 1 − τ` and inner box of radius `2^{B−1} − 1 − 2τ`, with `τ = 2^{51055984}`; the
predicates are the words of `bpLen` bits (`confP.L = bpLen`).

* **Both trapdoors are covered**: the real trapdoor of every key of `Setup`
  (`goodTrap_real`) and the simulated trapdoor `W_f` of the reductions, for binary `Rᵢ`, `W_j`
  and every program predicate (`goodTrap_sim`, `goodTrap_sim_of`). So keys with `W_f` have
  exactly the law of real keys (`keyLaw_real_eq_sim_conf`), the ideal key law
  (`keyLaw_sim_eq_ideal`).
* **Correctness** (`correct_conf`): with the larger key box `S` entering the noise, every
  predicate of depth at most `Dmax = 1054` (`depth_predC`, from `depth_bpPred`) stays below `q/4`
  (`Params.noise_ok`); the abort probability is at most `2^{-128}`.
* **Expressiveness** (`expressive_conf`).
-/

namespace AdvancedEncryption.DualUse.Params

set_option maxRecDepth 100000

open SigabaNeo SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord
open AdvancedEncryption.DualUse.Concrete (pow_mul_le' pow_le_pow')
open scoped ENNReal

/-- The error law: centered binomial of width `16`. -/
noncomputable def χp : PMF (ZMod (2 ^ Kp)) :=
  SigabaNeo.Lattices.ModuleLWE.coeffLaw (2 ^ Kp) (SigabaNeo.Lattices.SecretDist.cbd 16)

theorem χp_short : ∀ e ∈ χp.support, zabs e ≤ 16 := by
  intro e he
  simp only [χp, ModuleLWE.coeffLaw, PMF.mem_support_map_iff] at he
  obtain ⟨ab, -, rfl⟩ := he
  rw [← Int.cast_sub]
  refine (zabs_intCast_le (q := 2 ^ Kp) _).trans ?_
  have h1 := Finset.card_le_univ (Finset.univ.filter fun i => ab.1 i)
  have h2 := Finset.card_le_univ (Finset.univ.filter fun i => ab.2 i)
  simp only [Fintype.card_fin] at h1 h2
  omega

/-- The radius of the small box. -/
noncomputable def Sp : ℕ := 2 ^ (Bp - 1) - 1 - τp

theorem hBp : 2 ^ Bp ≤ 2 ^ Kp := pow_le_pow' (by rw [Bp_def, Kp_def]; norm_num)

theorem one_le_Bp : 1 ≤ Bp := by rw [Bp_def]; norm_num

/-- `2 τ + 2 ≤ 2^{B−1}`. -/
theorem hτM : 2 * τp + 2 ≤ 2 ^ (Bp - 1) := by
  have h1 : 2 * τp + 2 ≤ 2 ^ (Eτ + 2) := by
    unfold τp
    rw [pow_add]
    have : 1 ≤ 2 ^ Eτ := Nat.one_le_two_pow
    omega
  exact h1.trans (pow_le_pow' (by rw [Eτ_def, Bp_def]; norm_num))

/-- The box arithmetic, with the large numbers as variables. -/
theorem box_arith (M τ : ℕ) (h : 2 * τ + 2 ≤ M) :
    M - 1 - 2 * τ ≤ M - 1 ∧ M - 1 - τ + τ ≤ M - 1 ∧ M - 1 - 2 * τ + τ ≤ M - 1 - τ ∧
      1 ≤ M - 1 - τ ∧ M - 1 - τ ≤ M := by
  omega

theorem Sp_le : Sp ≤ 2 ^ (Bp - 1) := (box_arith _ _ hτM).2.2.2.2

/-- A column of the gadget. -/
def c₀p : Col kp := (0, ⟨0, Nat.succ_pos _⟩)

/-- The binary decomposition of a ring element. -/
noncomputable def decp (u : Rg Np Kp) : Col kp → Rg Np Kp := fun c =>
  (Sdw (N := Np) hkp).Γ₁.ginv (Matrix.of fun _ _ => u) c c₀p

theorem hdecp (u : Rg Np Kp) : gadgetMap (S := Sdw (N := Np) hkp) (decp u) = u := by
  have h := congrFun (congrFun ((Sdw (N := Np) hkp).Γ₁.mul_ginv (Matrix.of fun _ _ => u)) 0) c₀p
  simp only [Matrix.mul_apply, Matrix.of_apply] at h
  exact h

theorem cnorm_decp (u : Rg Np Kp) (c : Col kp) : cnorm (decp u c) ≤ 1 :=
  cnorm_gadgetOf_binary_ginv_le hkp.le (fun _ : Fin 1 => (0 : Fin 2)) _ _ c c₀p

/-- The number of coins of the big box. -/
noncomputable def mBp : ℕ := (dp + (1 + (2 * kp + 2 * kp))) * Np * Bp

theorem card_coefP :
    Fintype.card (Coef dp (TrapCol kp) Np) = (dp + (1 + (2 * kp + 2 * kp))) * Np := by
  rw [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Fintype.card_sum,
    Fintype.card_sum, Fintype.card_fin, card_colP]

theorem hmBp : Fintype.card (Coef dp (TrapCol kp) Np) * Bp = mBp := by rw [card_coefP]; rfl

/-- **The parameters.** -/
noncomputable def confP : Conf Np Kp kp where
  hN := Np_pos
  d := dp
  χc := χp
  mχ := 16 + 16
  hχ := BitLaw.cbd 16
  w := wP
  mB := mBp
  emb := keyEmb Bp hBp mBp hmBp
  Small := keyBall (2 ^ Kp) dp (TrapCol kp) Np Sp
  dec := decp
  L := bpLen

/-- The inner box. -/
noncomputable def innerP : Finset (KeyShort (Fin dp) (TrapCol kp) (Rg Np Kp)) :=
  keyBall (2 ^ Kp) dp (TrapCol kp) Np (2 ^ (Bp - 1) - 1 - 2 * τp)

theorem big_eqP :
    confP.Big = Finset.univ.map (keyEmb (d := dp) (Wt := TrapCol kp) (N := Np) Bp hBp mBp hmBp) :=
  rfl

theorem ball_sub_bigP : keyBall (2 ^ Kp) dp (TrapCol kp) Np (2 ^ (Bp - 1) - 1) ⊆ confP.Big := by
  rw [big_eqP]; exact keyBall_subset_big Bp hBp one_le_Bp mBp hmBp

/-- A shift by at most `τ` maps the small box into the big box. -/
theorem add_mem_bigP {y T : KeyShort (Fin dp) (TrapCol kp) (Rg Np Kp)} (hy : y ∈ confP.Small)
    (hT : ∀ i, zabs (keyEquiv T i) ≤ τp) : y + T ∈ confP.Big :=
  ball_sub_bigP (keyBall_mono (box_arith _ _ hτM).2.1 (add_mem_keyBall hy hT))

/-- The shift of the real trapdoor for a key of `Setup`. -/
theorem shift_shortP (v : PK hkp confP × SKey hkp confP) (hv : v ∈ (setupM hkp confP).support)
    (Bf : Matrix (Fin 1) (Col kp) (Rg Np Kp)) (u : Rg Np Kp) :
    ∀ i, zabs (keyEquiv (realTrap (Wd := Fin dp) (S := Sdw (N := Np) hkp)
      (trapMat v.2.2.1 v.2.2.2) Bf (decp u)) i) ≤ τp := by
  obtain ⟨he, ht⟩ := setup_trapdoor_short hkp confP χp_short v hv
  obtain ⟨-, h2⟩ := cnorm_realTrap_le hkp confP (by norm_num) v.2.2.1 v.2.2.2 he ht Bf (decp u)
    (cnorm_decp u)
  refine zabs_keyEquiv_le (fun i => ?_) (fun i => (h2 i).trans realShift_le)
  show cnorm ((0 : Fin dp → Rg Np Kp) i) ≤ τp
  simp [cnorm_zero]

/-- `|Coef| ≤ 2^eCoef`. -/
def eCoef : ℕ := 102

theorem kp4_le : 1 + 4 * kp ≤ 2 ^ ad := by
  have h1 := kp_le
  have h2 : (4 : ℕ) * 2 ^ ak + 1 ≤ 2 ^ ad := by norm_num [ak, ad]
  omega

theorem card_coef_leP : Fintype.card (Coef dp (TrapCol kp) Np) ≤ 2 ^ eCoef :=
  Gen.card_coef_le dp_le kp4_le Np_le (by norm_num [ad, an, eCoef])

theorem four_τ_le : 4 * τp + 1 ≤ 2 ^ (Eτ + 3) := Gen.four_τ_le Eτ

/-- **The abort probability** is at most `2^{-128}`. -/
theorem abortP : (((confP.Big.card - innerP.card : ℕ) : ℝ≥0∞) / confP.Big.card) ≤
    ((2 : ℝ≥0∞) ^ params.corrBits)⁻¹ := by
  have hprod : Fintype.card (Coef dp (TrapCol kp) Np) * (4 * τp + 1) * 2 ^ 128 ≤ 2 ^ Bp :=
    Gen.abort_prod card_coef_leP (by rw [Eτ_def, Bp_def]; norm_num [eCoef])
  have h4 : 4 * τp + 1 ≤ 2 ^ Bp :=
    four_τ_le.trans (pow_le_pow' (by rw [Eτ_def, Bp_def]; norm_num))
  exact abort_le (d := dp) (Wt := TrapCol kp) (N := Np) Bp τp 128 hBp one_le_Bp mBp hmBp h4 hprod

/-- The predicates have depth at most `Dmax`. -/
theorem depth_predC (C : List Bool) : SLP.depth (predC C).1 (predC C).2 ≤ Dmax :=
  depth_bpPred _

variable {ms : Machines hkp confP}

theorem confP_L : confP.L = bpLen := rfl

/-- **The implementation is correct.** -/
theorem correct_conf : Correct PUniv params (impl hkp confP ms) := by
  have hb := box_arith _ _ hτM
  refine DualUse.correct hkp confP confP_L.ge (by show 0 < dp; rw [dp_def]; positivity) hdecp
    (2 ^ wP) Sp innerP ?_ ?_ ?_ abortP ?_ ?_ ?_ ?_
  · -- the inner box lies in the big box
    exact (keyBall_mono hb.1).trans ball_sub_bigP
  · -- coverage
    intro v hv C _ y hy u
    exact add_mem_bigP hy (shift_shortP v hv _ u)
  · -- the inner box shifted stays in the small box
    intro v hv C _ p hp u
    exact keyBall_mono hb.2.2.1 (sub_mem_keyBall hp (shift_shortP v hv _ u))
  · -- the small box is short
    intro v hv
    exact cnorm_of_mem_keyBall hv
  · -- the decomposition is short
    intro u i
    exact (cnorm_decp u i).trans hb.2.2.2.1
  · -- the coins are short
    refine coins_short hkp confP χp_short ?_
    have h : (16 : ℕ) ≤ 2 ^ wP :=
      (show (16 : ℕ) = 2 ^ 4 from rfl).le.trans (pow_le_pow' (by norm_num [wP]))
    exact h
  · -- the noise
    intro C _
    exact noise_ok _ (depth_predC C) Sp Sp_le

/-- **The implementation is expressive.** -/
theorem expressive_conf : Expressive PUniv params (impl hkp confP ms) :=
  DualUse.expressive hkp confP

/-! ### Both trapdoors are covered -/

/-- **The real trapdoor is covered** for every key of `Setup` and every program predicate. -/
theorem goodTrap_real (v : PK hkp confP × SKey hkp confP) (hv : v ∈ (setupM hkp confP).support)
    (C : List Bool) :
    GoodTrap confP.Big confP.Small confP.dec v.1 (keyMatrix v.1 (predC C))
      (realTrap (S := Sdw (N := Np) hkp) (trapMat v.2.2.1 v.2.2.2)
        (keyMatrix v.1 (predC C))) := by
  obtain ⟨hT, -⟩ := msk_trapdoor _ v hv
  exact ⟨realTrap_spec hkp confP v.1 _ hT _,
    fun y hy u => add_mem_bigP hy (shift_shortP v hv _ u)⟩

/-- **The simulated trapdoor is covered**: for binary `Rᵢ` and `W_j` (as drawn by the
reductions), any `Ψ`, and a program predicate `f` whose key row is `B₀ W_f + G̲`, the trapdoor
`W_f = simKeyMat …` is a covered trapdoor of the key row. -/
theorem goodTrap_sim (mpk : PK hkp confP) (Rm : Fin nA → Matrix (Fin confP.d) (Col kp) (Rg Np Kp))
    (x : Fin nA → Bool)
    (W : Fin nA × (Sdw (N := Np) hkp).ctBits.Index → Matrix (Fin confP.d) (Col kp) (Rg Np Kp))
    (Ψ : Fin nA → Matrix (Fin 2) (Col kp) (Rg Np Kp))
    (hR : ∀ i a c, cnorm (Rm i a c) ≤ 1) (hW : ∀ j a c, cnorm (W j a c) ≤ 1) (C : List Bool)
    (hBf : keyMatrix mpk (predC C) =
      mpk.B₀ * simKeyMat (S := Sdw (N := Np) hkp) Rm x W Ψ mpk.Bj (predC C) +
        (Sdw (N := Np) hkp).Γ₁.G) :
    GoodTrap confP.Big confP.Small confP.dec mpk (keyMatrix mpk (predC C))
      (simTrap (Wt := TrapCol kp)
        (simKeyMat (S := Sdw (N := Np) hkp) Rm x W Ψ mpk.Bj (predC C))) := by
  refine ⟨simTrap_public mpk _ _ hBf, fun y hy u => add_mem_bigP hy ?_⟩
  obtain ⟨h1, h2⟩ := cnorm_simTrap_le_depth (Wt := TrapCol kp) hkp Rm x W Ψ mpk.Bj
    (predC C) hR hW (decp u) (cnorm_decp u) (depth_predC C)
  have hb := simTrapBound_le (le_refl Dmax)
  exact zabs_keyEquiv_le (fun i => (h1 i).trans hb) (fun i => (h2 i).trans hb)

/-- `B_f̂ = B₀ W_f + G̲` when `f(x) = 1`. -/
theorem keyMatrix_eq_sim_one {R : Type*} [CommRing R] {k : ℕ} {S : Setting R k} {Wd Wt : Type*}
    [Fintype Wd] (hfhat : S.FhatCorrect) (mpk : MPK S Wd Wt) (c₀ : Matrix (Fin 1) Wd R)
    (Rm : S.Attr → Matrix Wd (Col k) R) (x : S.Attr → Bool)
    (W : S.Attr × S.ctBits.Index → Matrix Wd (Col k) R) (Ψ : S.Attr → Matrix (Fin 2) (Col k) R)
    (hΨ : ∀ i, Ψ i = gswPK mpk.B₀ c₀ * Rm i + bitR (R := R) (x i) • S.Γ.G)
    (hB : ∀ j, mpk.Bj j = mpk.B₀ * W j + bitsOf S Ψ j • S.Γ₁.G) (f : S.Pred)
    (h1 : (S.circ f).eval (fun i => bitR (R := R) (x i)) = 1) :
    keyMatrix mpk f = mpk.B₀ * simKeyMat Rm x W Ψ mpk.Bj f + S.Γ₁.G := by
  rw [keyMatrix_eq_sim hfhat mpk c₀ Rm x W Ψ hΨ hB f, h1, one_smul]

/-- A predicate true on `x` evaluates to `1` on the bits of `x`. -/
theorem circ_eval_one (x : Fin nA → Bool) (f : SLP (Fin nA) × Wire (Fin nA))
    (hfx : SLP.evalBool x f.1 f.2 = true) :
    ((Sdw (N := Np) hkp).circ f).eval (fun i => bitR (R := Rg Np Kp) (x i)) = 1 := by
  have := Circuit.eval_bits (R := Rg Np Kp) x (f.1.circuit f.2)
  rw [SLP.evalBool_circuit, hfx] at this
  simp only [bitR]
  exact this.trans (by simp)

/-- **The simulated trapdoor is covered**, from the relations of the reductions
(`Ψᵢ = A Rᵢ + xᵢ G`, `B_j = B₀ W_j + ψ_j G̲`) and `f(x) = 1`. -/
theorem goodTrap_sim_of (mpk : PK hkp confP) (c₀ : Matrix (Fin 1) (Fin confP.d) (Rg Np Kp))
    (Rm : Fin nA → Matrix (Fin confP.d) (Col kp) (Rg Np Kp)) (x : Fin nA → Bool)
    (W : Fin nA × (Sdw (N := Np) hkp).ctBits.Index → Matrix (Fin confP.d) (Col kp) (Rg Np Kp))
    (Ψ : Fin nA → Matrix (Fin 2) (Col kp) (Rg Np Kp))
    (hΨ : ∀ i, Ψ i = gswPK mpk.B₀ c₀ * Rm i + bitR (R := Rg Np Kp) (x i) • (Sdw (N := Np) hkp).Γ.G)
    (hB : ∀ j, mpk.Bj j = mpk.B₀ * W j + bitsOf (Sdw (N := Np) hkp) Ψ j • (Sdw (N := Np) hkp).Γ₁.G)
    (hR : ∀ i a c, cnorm (Rm i a c) ≤ 1) (hW : ∀ j a c, cnorm (W j a c) ≤ 1) (C : List Bool)
    (hfx : SLP.evalBool x (predC C).1 (predC C).2 = true) :
    GoodTrap confP.Big confP.Small confP.dec mpk (keyMatrix mpk (predC C))
      (simTrap (Wt := TrapCol kp)
        (simKeyMat (S := Sdw (N := Np) hkp) Rm x W Ψ mpk.Bj (predC C))) := by
  exact goodTrap_sim mpk Rm x W Ψ hR hW C (keyMatrix_eq_sim_one
    (ringSetting_fhatCorrect hkp (Fin nA)) mpk c₀ Rm x W Ψ hΨ hB _ (circ_eval_one x _ hfx))

/-- **Keys with the simulated trapdoor have the ideal key law.** -/
theorem keyLaw_sim_eq_ideal (mpk : PK hkp confP) (Rm : Fin nA → Matrix (Fin confP.d) (Col kp) (Rg Np Kp))
    (x : Fin nA → Bool)
    (W : Fin nA × (Sdw (N := Np) hkp).ctBits.Index → Matrix (Fin confP.d) (Col kp) (Rg Np Kp))
    (Ψ : Fin nA → Matrix (Fin 2) (Col kp) (Rg Np Kp))
    (hR : ∀ i a c, cnorm (Rm i a c) ≤ 1) (hW : ∀ j a c, cnorm (W j a c) ≤ 1) (C : List Bool)
    (hBf : keyMatrix mpk (predC C) =
      mpk.B₀ * simKeyMat (S := Sdw (N := Np) hkp) Rm x W Ψ mpk.Bj (predC C) +
        (Sdw (N := Np) hkp).Γ₁.G) :
    keyLaw confP.Big confP.Small confP.hBig confP.dec mpk
        (simTrap (simKeyMat (S := Sdw (N := Np) hkp) Rm x W Ψ mpk.Bj (predC C))) =
      idealKeyLaw confP.Big confP.Small confP.hBig confP.dec mpk
        (keyMatrix mpk (predC C)) :=
  keyLaw_eq_ideal (dec := confP.dec) _ _ _ hdecp mpk _ _ (goodTrap_sim mpk Rm x W Ψ hR hW C hBf)

/-- **Real and simulated keys have the same law** for the keys of `Setup`. -/
theorem keyLaw_real_eq_sim_conf (v : PK hkp confP × SKey hkp confP)
    (hv : v ∈ (setupM hkp confP).support) (Rm : Fin nA → Matrix (Fin confP.d) (Col kp) (Rg Np Kp))
    (x : Fin nA → Bool)
    (W : Fin nA × (Sdw (N := Np) hkp).ctBits.Index → Matrix (Fin confP.d) (Col kp) (Rg Np Kp))
    (Ψ : Fin nA → Matrix (Fin 2) (Col kp) (Rg Np Kp))
    (hR : ∀ i a c, cnorm (Rm i a c) ≤ 1) (hW : ∀ j a c, cnorm (W j a c) ≤ 1) (C : List Bool)
    (hBf : keyMatrix v.1 (predC C) =
      v.1.B₀ * simKeyMat (S := Sdw (N := Np) hkp) Rm x W Ψ v.1.Bj (predC C) +
        (Sdw (N := Np) hkp).Γ₁.G) :
    keyLaw confP.Big confP.Small confP.hBig confP.dec v.1
        (realTrap (S := Sdw (N := Np) hkp) (trapMat v.2.2.1 v.2.2.2)
          (keyMatrix v.1 (predC C))) =
      keyLaw confP.Big confP.Small confP.hBig confP.dec v.1
        (simTrap (simKeyMat (S := Sdw (N := Np) hkp) Rm x W Ψ v.1.Bj (predC C))) := by
  exact (keyLaw_eq_ideal (dec := confP.dec) _ _ _ hdecp v.1 _ _ (goodTrap_real v hv C)).trans
    (keyLaw_sim_eq_ideal v.1 Rm x W Ψ hR hW C hBf).symm

end AdvancedEncryption.DualUse.Params
