import PE.Impl.ExpLUT.Prog.Words
import PE.Impl.ExpLUT.Hybrid6
import SigabaNeo.Lib.Lattices.Stat

/-!
# The near-uniform law of the machines (package G, statistical step)

`ℤ_{2^K − 1}` has an odd number of elements, so the machines draw the "uniform" public matrices
from `unifW D`: `N K` fair bits read by `decRM` (package F). Every ring element has probability at
least `2^{−NK}` under `unifW` (its canonical word), so `unifW` is within
`ε_U = N · 2^{−K}` of the uniform law (`closeTo_unif_unifW`, Bernoulli's inequality
`(2^K)^N ≤ (2^K − 1)^N + N (2^K)^{N−1}`). Families of independent draws add up
(`closeTo_iid_unif`, `closeTo_iidFam_unif`), so:

* `closeTo_setupCoins`: the coins of `Setup` (`setupCoinsLaw`, uniform public matrices) are within
  `nPub D · ε_U` of the machines' coins (`setupCoinsLawW D (unifW D)`), `nPub D` the number of public
  ring elements; `closeTo_setupLaw`: the same for the laws of `Setup`;
* `ctUW`: the simulator's ciphertext law (independent `unifW` entries, in the order of `ctEnc`);
  `closeTo_ctU_ctUW`: within `nCT D · ε_U` of the uniform ciphertext `ctU`;
* `mem_support_setupLawW`: on the support of the machines' `Setup`, `msk = (mpk, T)` with
  `B⁽¹⁾ = [Ā | g − Ā T]` and `T` from `χT`.
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Lattices.Algo Matrix Cslib Cslib.Probability
open scoped ENNReal

variable (D : Dims)

/-- `ε_U = N · 2^{−K}`: the distance of `unifW` to the uniform law. -/
noncomputable def epsU : ℝ≥0∞ := (D.N : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ D.K)⁻¹

theorem card_Rg : Fintype.card (Rg D) = D.q ^ D.N := by
  rw [Fintype.card_congr (Negacyclic.coeffsEquiv (R := ZMod D.q) (n := D.N)), Fintype.card_fun,
    ZMod.card, Fintype.card_fin]

/-- A word of length `n` has probability `2^{−n}`. -/
theorem uniformList_apply_of_length {n : ℕ} {w : List Bool} (hw : w.length = n) :
    BitString.uniformList n w = ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  have h := BitString.uniformList_map_apply id n w
  rw [PMF.map_id] at h
  rw [h, Finset.card_eq_one.mpr ⟨fun i : Fin n => w.get (i.cast hw.symm), ?_⟩]
  · simp [div_eq_mul_inv]
  · ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, id]
    constructor
    · rintro rfl
      funext i
      simp
    · rintro rfl
      subst hw
      exact List.ofFn_get w

/-- **Every ring element has probability at least `2^{−NK}` under `unifW`**: its canonical word. -/
theorem unifW_ge (y : Rg D) : ((2 : ℝ≥0∞) ^ (D.N * D.K))⁻¹ ≤ unifW D y := by
  rw [unifW, PMF.map_apply]
  rw [← uniformList_apply_of_length (length_encRM D.N D.K y)]
  refine le_trans ?_ (le_tsum _ (encRM D.N D.K y))
  simp [decRM_encRM D.K_pos]

/-- Bernoulli's inequality in the form used: `(b + 1)^N ≤ b^N + N (b + 1)^{N−1}`. -/
theorem pow_succ_le_bernoulli (b : ℕ) : ∀ N : ℕ, (b + 1) ^ (N + 1) ≤ b ^ (N + 1) + (N + 1) * (b + 1) ^ N
  | 0 => by simp
  | N + 1 => by
    have ih := pow_succ_le_bernoulli b N
    have h1 : b ^ (N + 1) ≤ (b + 1) ^ (N + 1) := Nat.pow_le_pow_left (Nat.le_succ b) _
    calc (b + 1) ^ (N + 1 + 1) = (b + 1) * (b + 1) ^ (N + 1) := by ring
      _ ≤ (b + 1) * (b ^ (N + 1) + (N + 1) * (b + 1) ^ N) := Nat.mul_le_mul_left _ ih
      _ = b ^ (N + 1 + 1) + b ^ (N + 1) + (N + 1) * (b + 1) ^ (N + 1) := by ring
      _ ≤ b ^ (N + 1 + 1) + (b + 1) ^ (N + 1) + (N + 1) * (b + 1) ^ (N + 1) := by omega
      _ = b ^ (N + 1 + 1) + (N + 1 + 1) * (b + 1) ^ (N + 1) := by ring

/-- The arithmetic of `closeTo_unif_unifW`: `c (c⁻¹ − A⁻¹) ≤ N a⁻¹` for `c = (a − 1)^N`, `A = a^N`. -/
theorem unif_arith (a N : ℕ) (ha : 2 ≤ a) (hN : 1 ≤ N) :
    (((a - 1) ^ N : ℕ) : ℝ≥0∞) * ((((a - 1) ^ N : ℕ) : ℝ≥0∞)⁻¹ - ((a ^ N : ℕ) : ℝ≥0∞)⁻¹) ≤
      (N : ℝ≥0∞) * (a : ℝ≥0∞)⁻¹ := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hb : 0 < b := by omega
  have hc0 : ((b ^ (M + 1) : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (pow_pos hb _).ne'
  have hcT : ((b ^ (M + 1) : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hA0 : (((b + 1) ^ (M + 1) : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (pow_pos (by omega) _).ne'
  have hAT : (((b + 1) ^ (M + 1) : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.mul_sub (fun _ _ => hcT), ENNReal.mul_inv_cancel hc0 hcT, tsub_le_iff_right]
  -- `1 ≤ c/A + N/a`, from `A ≤ c + N a^M`
  have hB := pow_succ_le_bernoulli b M
  have key : (((b + 1) ^ (M + 1) : ℕ) : ℝ≥0∞) ≤
      ((b ^ (M + 1) : ℕ) : ℝ≥0∞) + ((M + 1 : ℕ) : ℝ≥0∞) * (((b + 1) ^ M : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hB
  have e1 : ((M + 1 : ℕ) : ℝ≥0∞) * ((b + 1 : ℕ) : ℝ≥0∞)⁻¹ =
      ((M + 1 : ℕ) : ℝ≥0∞) * (((b + 1) ^ M : ℕ) : ℝ≥0∞) * (((b + 1) ^ (M + 1) : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [show (((b + 1) ^ (M + 1) : ℕ) : ℝ≥0∞) = (((b + 1) ^ M : ℕ) : ℝ≥0∞) * ((b + 1 : ℕ) : ℝ≥0∞) by
      push_cast; ring]
    have h0 : (((b + 1) ^ M : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (pow_pos (by omega) _).ne'
    have hT : (((b + 1) ^ M : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [ENNReal.mul_inv (Or.inl h0) (Or.inl hT)]
    rw [show ((M + 1 : ℕ) : ℝ≥0∞) * (((b + 1) ^ M : ℕ) : ℝ≥0∞) *
        ((((b + 1) ^ M : ℕ) : ℝ≥0∞)⁻¹ * ((b + 1 : ℕ) : ℝ≥0∞)⁻¹) =
        ((M + 1 : ℕ) : ℝ≥0∞) * ((((b + 1) ^ M : ℕ) : ℝ≥0∞) * (((b + 1) ^ M : ℕ) : ℝ≥0∞)⁻¹) *
          ((b + 1 : ℕ) : ℝ≥0∞)⁻¹ by ring, ENNReal.mul_inv_cancel h0 hT, mul_one]
  have e2 : (1 : ℝ≥0∞) = (((b + 1) ^ (M + 1) : ℕ) : ℝ≥0∞) * (((b + 1) ^ (M + 1) : ℕ) : ℝ≥0∞)⁻¹ :=
    (ENNReal.mul_inv_cancel hA0 hAT).symm
  rw [e2, e1]
  calc _ ≤ (((b ^ (M + 1) : ℕ) : ℝ≥0∞) + ((M + 1 : ℕ) : ℝ≥0∞) * (((b + 1) ^ M : ℕ) : ℝ≥0∞)) *
        (((b + 1) ^ (M + 1) : ℕ) : ℝ≥0∞)⁻¹ := by gcongr
    _ = _ := by ring

/-- **`unifW` is within `ε_U = N · 2^{−K}` of the uniform law.** -/
theorem closeTo_unif_unifW : CloseTo (PMF.uniformOfFintype (Rg D)) (unifW D) (epsU D) := by
  rw [closeTo_iff_tsum_tsub_le, tsum_fintype]
  have hq : D.q = 2 ^ D.K - 1 := rfl
  calc ∑ y : Rg D, (PMF.uniformOfFintype (Rg D) y - unifW D y)
      ≤ ∑ _y : Rg D, (((Fintype.card (Rg D) : ℕ) : ℝ≥0∞)⁻¹ - ((2 : ℝ≥0∞) ^ (D.N * D.K))⁻¹) :=
        Finset.sum_le_sum fun y _ => by
          rw [PMF.uniformOfFintype_apply]; exact tsub_le_tsub_left (unifW_ge D y) _
    _ = ((Fintype.card (Rg D) : ℕ) : ℝ≥0∞) *
          (((Fintype.card (Rg D) : ℕ) : ℝ≥0∞)⁻¹ - ((2 : ℝ≥0∞) ^ (D.N * D.K))⁻¹) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ epsU D := by
        have h := unif_arith (2 ^ D.K) D.N
          (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) D.hK)) D.N_pos
        rw [card_Rg, hq]
        rw [show ((2 : ℝ≥0∞) ^ (D.N * D.K)) = (((2 ^ D.K) ^ D.N : ℕ) : ℝ≥0∞) by
          push_cast; rw [← pow_mul, mul_comm]]
        refine h.trans (le_of_eq ?_)
        unfold epsU
        push_cast
        rfl

/-! ### Families -/

/-- Independent coordinates, each `ε`-close: `|ι| ε`-close. -/
theorem closeTo_pi_const {ι α : Type} [Fintype ι] [DecidableEq ι] [Finite α] {p p' : PMF α}
    {ε : ℝ≥0∞} (h : CloseTo p p' ε) :
    CloseTo (PMF.pi fun _ : ι => p) (PMF.pi fun _ : ι => p') (Fintype.card ι * ε) := by
  have := closeTo_pi (fun _ : ι => p) (fun _ : ι => p') (fun _ => ε) fun _ => h
  rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this

/-- Uniform functions vs independent `unifW` entries. -/
theorem closeTo_iid_unif (ι : Type) [Fintype ι] [DecidableEq ι] :
    CloseTo (PMF.uniformOfFintype (ι → Rg D)) (iidLaw (unifW D) ι) (Fintype.card ι * epsU D) := by
  rw [← Cslib.Probability.PMF.pi_uniformOfFintype]
  exact closeTo_pi_const (closeTo_unif_unifW D)

/-- Uniform families of rows vs independent `unifW` entries. -/
theorem closeTo_iidFam_unif (κ ι : Type) [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] :
    CloseTo (PMF.uniformOfFintype (κ → ι → Rg D)) (iidFam (unifW D) κ ι)
      (Fintype.card κ * (Fintype.card ι * epsU D)) := by
  rw [← Cslib.Probability.PMF.pi_uniformOfFintype]
  exact closeTo_pi_const (closeTo_iid_unif D ι)

/-- Three levels. -/
theorem closeTo_iidFam3_unif (l' κ ι : Type) [Fintype l'] [DecidableEq l'] [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] :
    CloseTo (PMF.uniformOfFintype (l' → κ → ι → Rg D))
      (Cslib.Probability.PMF.pi fun _ : l' => iidFam (unifW D) κ ι)
      (Fintype.card l' * (Fintype.card κ * (Fintype.card ι * epsU D))) := by
  rw [← Cslib.Probability.PMF.pi_uniformOfFintype]
  exact closeTo_pi_const (closeTo_iidFam_unif D κ ι)

/-- Four levels. -/
theorem closeTo_iidFam4_unif (μ' l' κ ι : Type) [Fintype μ'] [DecidableEq μ'] [Fintype l']
    [DecidableEq l'] [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] :
    CloseTo (PMF.uniformOfFintype (μ' → l' → κ → ι → Rg D))
      (Cslib.Probability.PMF.pi fun _ : μ' => Cslib.Probability.PMF.pi fun _ : l' =>
        iidFam (unifW D) κ ι)
      (Fintype.card μ' * (Fintype.card l' * (Fintype.card κ * (Fintype.card ι * epsU D)))) := by
  rw [← Cslib.Probability.PMF.pi_uniformOfFintype]
  exact closeTo_pi_const (closeTo_iidFam3_unif D l' κ ι)

/-! ### `Setup` -/

/-- The distance between the coins of `Setup` and the machines' coins: `ε_U` per public ring
element. -/
noncomputable def epsSetup : ℝ≥0∞ :=
  Fintype.card (Wb D) * epsU D + (Fintype.card (BCol (Wb D) D.K) * epsU D +
  (Fintype.card (Jh D) * (Fintype.card (Fin 2) * (Fintype.card (Col D.K) * epsU D)) +
  (Fintype.card Pos * (Fintype.card (Col D.K) * epsU D) +
  (Fintype.card (Fin 2) * (Fintype.card (Col D.K) * epsU D) +
  (Fintype.card Pos * (Fintype.card (Dig D.K) * (Fintype.card (Fin 2) * (Fintype.card (Col D.K) *
    epsU D))) +
  (Fintype.card (Fin D.b) * (Fintype.card (Dig D.K) * (Fintype.card (Fin 2) *
    (Fintype.card (Col D.K) * epsU D))) +
  Fintype.card (Fin 2) * epsU D))))))

/-- **The coins of `Setup` are close to the machines' coins.** -/
theorem closeTo_setupCoins (χT : PMF (Rg D)) :
    CloseTo (setupCoinsLaw (setting D) (Wb D) (Jh D) Pos χT) (setupCoinsLawW D (unifW D) χT)
      (epsSetup D) := by
  unfold setupCoinsLaw setupCoinsLawW epsSetup
  refine (closeTo_iid_unif D (Wb D)).bind fun Abar _ => ?_
  refine CloseTo.bind_right _ fun T _ => ?_
  refine (closeTo_iid_unif D (BCol (Wb D) D.K)).bind fun B2 _ => ?_
  refine (closeTo_iidFam3_unif D (Jh D) (Fin 2) (Col D.K)).bind fun H _ => ?_
  refine (closeTo_iidFam_unif D Pos (Col D.K)).bind fun a _ => ?_
  refine (closeTo_iidFam_unif D (Fin 2) (Col D.K)).bind fun A0 _ => ?_
  refine (closeTo_iidFam4_unif D Pos (Dig D.K) (Fin 2) (Col D.K)).bind fun Ain _ => ?_
  refine (closeTo_iidFam4_unif D (Fin D.b) (Dig D.K) (Fin 2) (Col D.K)).bind fun Aaut _ => ?_
  exact (closeTo_iid_unif D (Fin 2)).map _

/-- **The law of `Setup` is close to the machines'.** -/
theorem closeTo_setupLaw (χT : PMF (Rg D)) :
    CloseTo (setupLaw (setting D) (Wb D) (Jh D) Pos χT) (setupLawW D χT) (epsSetup D) :=
  (closeTo_setupCoins D χT).map _

variable {D} in
/-- On the support of the machines' `Setup`, `msk = (mpk, T)` with `B⁽¹⁾ = [Ā | g − Ā T]` and `T`
from `χT`. -/
theorem mem_support_setupLawW {χT : PMF (Rg D)} {v : MPKt D × MSKt D}
    (hv : v ∈ (setupLawW D χT).support) :
    v.2.mpk = v.1 ∧ TrapOK v.1 v.2.T ∧ ∀ w c, v.2.T w c ∈ χT.support := by
  simp only [setupLawW, setupCoinsLawW, PMF.support_map, PMF.support_bind, Set.mem_image,
    Set.mem_iUnion] at hv
  obtain ⟨r, ⟨Abar, -, T, hT, B2, -, H, -, a, -, A0, -, Ain, -, Aaut, -, d, -, rfl⟩, rfl⟩ := hv
  exact ⟨rfl, fun c => rfl, fun w c => mem_support_iidFam hT w c⟩

/-! ### The simulator's ciphertext -/

/-- The uniform ciphertext, drawn in the order of the encoding `ctEnc`. -/
noncomputable def ctUe : PMF (CTt D) :=
  (PMF.uniformOfFintype (BCol (Wb D) D.K → Rg D)).bind fun b =>
  (PMF.uniformOfFintype (Jh D → Col D.K → Rg D)).bind fun h =>
  (PMF.uniformOfFintype (Fin D.b → Dig D.K → Col D.K → Rg D)).bind fun caut =>
  (PMF.uniformOfFintype (Pos → Col D.K → Rg D)).bind fun cb =>
  (PMF.uniformOfFintype (Pos → Dig D.K → Col D.K → Rg D)).bind fun cin =>
  (PMF.uniformOfFintype (Col D.K → Rg D)).bind fun c0 =>
  (PMF.uniformOfFintype (Rg D)).map fun cm => ⟨b, h, caut, cb, cin, c0, cm⟩

/-- **The simulator's ciphertext law**: independent `unifW` entries, in the order of `ctEnc`. -/
noncomputable def ctUW : PMF (CTt D) :=
  (iidLaw (unifW D) (BCol (Wb D) D.K)).bind fun b =>
  (iidFam (unifW D) (Jh D) (Col D.K)).bind fun h =>
  (Cslib.Probability.PMF.pi fun _ : Fin D.b => iidFam (unifW D) (Dig D.K) (Col D.K)).bind fun caut =>
  (iidFam (unifW D) Pos (Col D.K)).bind fun cb =>
  (Cslib.Probability.PMF.pi fun _ : Pos => iidFam (unifW D) (Dig D.K) (Col D.K)).bind fun cin =>
  (iidLaw (unifW D) (Col D.K)).bind fun c0 =>
  (unifW D).map fun cm => ⟨b, h, caut, cb, cin, c0, cm⟩

/-- The uniform ciphertext of package D in the order of the encoding. -/
theorem ctU_eq_ctUe : ctU (setting D) (Wb D) (Jh D) Pos = ctUe D := by
  unfold ctU ctUe
  refine congrArg (PMF.bind _) (funext fun b => congrArg (PMF.bind _) (funext fun h => ?_))
  -- move `c_m` to the end
  simp only [PMF.map]
  rw [PMF.bind_comm (PMF.uniformOfFintype (Rg D))]
  conv_lhs => enter [2, cb]; rw [PMF.bind_comm]
  conv_lhs => enter [2, cb, 2, c0]; rw [PMF.bind_comm]
  conv_lhs => enter [2, cb, 2, c0, 2, cin]; rw [PMF.bind_comm]
  conv_lhs => enter [2, cb, 2, c0]; rw [PMF.bind_comm]
  conv_lhs => enter [2, cb]; rw [PMF.bind_comm]
  conv_lhs => rw [PMF.bind_comm]
  conv_lhs => enter [2, caut, 2, cb]; rw [PMF.bind_comm]
  rfl

/-- The distance of the simulator's ciphertext to the uniform one. -/
noncomputable def epsCT : ℝ≥0∞ :=
  Fintype.card (BCol (Wb D) D.K) * epsU D +
  (Fintype.card (Jh D) * (Fintype.card (Col D.K) * epsU D) +
  (Fintype.card (Fin D.b) * (Fintype.card (Dig D.K) * (Fintype.card (Col D.K) * epsU D)) +
  (Fintype.card Pos * (Fintype.card (Col D.K) * epsU D) +
  (Fintype.card Pos * (Fintype.card (Dig D.K) * (Fintype.card (Col D.K) * epsU D)) +
  (Fintype.card (Col D.K) * epsU D + epsU D)))))

/-- **The simulator's ciphertext is close to the uniform one.** -/
theorem closeTo_ctU_ctUW : CloseTo (ctU (setting D) (Wb D) (Jh D) Pos) (ctUW D) (epsCT D) := by
  rw [ctU_eq_ctUe]
  unfold ctUe ctUW epsCT
  refine (closeTo_iid_unif D _).bind fun b _ => ?_
  refine (closeTo_iidFam_unif D (Jh D) (Col D.K)).bind fun h _ => ?_
  refine (closeTo_iidFam3_unif D (Fin D.b) (Dig D.K) (Col D.K)).bind fun caut _ => ?_
  refine (closeTo_iidFam_unif D Pos (Col D.K)).bind fun cb _ => ?_
  refine (closeTo_iidFam3_unif D Pos (Dig D.K) (Col D.K)).bind fun cin _ => ?_
  refine (closeTo_iid_unif D (Col D.K)).bind fun c0 _ => ?_
  exact (closeTo_unif_unifW D).map _

end AdvancedEncryption.ExpLUT.Prog
