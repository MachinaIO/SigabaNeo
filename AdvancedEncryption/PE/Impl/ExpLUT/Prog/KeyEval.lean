import PE.Impl.ExpLUT.Prog.KeyLut

/-!
# KeyGen (package F3): the VM's `EvalPK` is `keyPK`

At the dimensions `D` with `W = 2^22` (`D.b = 22`), the public matrix computed by `evalC`
(`evalVM` with the coefficient routines of the predicate word) is the scheme's
`A_F = keyPK mpk (bpOf (progOf C))` (**`keyPK_eq_evalVM`**):

* `X^{2N−1} = X⁻¹` (`monoX_pow_two_n_sub_one`), so `μ_j = σ_g^{j}(X⁻¹) = σ_{g^j}(X^{2N−1})`;
* the entry `L(u)` of a transition table and the complement `c_u` of its `14` bits add up to
  `2^{14} − 1` (`val_take_add_cmpl`), so `X^{L(u)} = X^{−c_u} X^{2^{14}−1}`;
* `α G` is `gM α`, `A G⁻¹(α G)` is `ginvMulm A (gM α)`, the rounds are the chains (`chainM`).
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.MVM
  Matrix Cslib AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open SigabaNeo.Lattices.Algo (encRM decRM val)

/-! ### Monomials -/

section Mono

variable {R : Type} [CommRing R] {n : ℕ}

theorem xInvG_mul_monoX (hn : 0 < n) : xInvG R n * monoX n = 1 := by
  rw [← rhoG_eq_mul]
  apply ext_coefG
  intro i hi
  rw [coefG_rhoG _ hi]
  have hX : ∀ t, t < n → coefG (monoX n : Negacyclic R n) t =
      (if 1 % (2 * n) = t then 1 else 0) - (if 1 % (2 * n) = t + n then 1 else 0) := by
    intro t ht; simp [coefG, ht, monoX, mono, monoCoeffs]
  have h1 : coefG (1 : Negacyclic R n) i = if i = 0 then 1 else 0 := by
    simp [coefG, hi, Negacyclic.coeffs_one]
  rw [h1]
  rcases Nat.lt_or_ge 1 n with h | h
  · have hm : 1 % (2 * n) = 1 := Nat.mod_eq_of_lt (by omega)
    by_cases hi1 : i + 1 < n
    · rw [if_pos hi1, hX _ hi1, hm]
      split_ifs <;> first | omega | simp
    · rw [if_neg hi1, hX 0 (by omega), hm]
      have hi0 : i ≠ 0 := by omega
      simp only [hi0, ↓reduceIte, if_neg (show (1 : ℕ) ≠ 0 + n by omega),
        if_neg (show (1 : ℕ) ≠ 0 by omega), sub_zero, neg_zero]
  · have hn1 : n = 1 := by omega
    subst hn1
    have hi0 : i = 0 := by omega
    subst hi0
    simp [hX]

theorem monoX_pow_two_n_sub_one (hn : 0 < n) : (monoX n : Negacyclic R n) ^ (2 * n - 1) = xInvG R n := by
  have h := xInvG_mul_monoX (R := R) hn
  calc (monoX n : Negacyclic R n) ^ (2 * n - 1)
      = (monoX n) ^ (2 * n - 1) * (xInvG R n * monoX n) := by rw [h, mul_one]
    _ = xInvG R n * (monoX n) ^ (2 * n - 1 + 1) := by ring
    _ = xInvG R n := by rw [Nat.sub_add_cancel (by omega), monoX_pow_two_n, mul_one]

theorem monoX_pow_eq_xInvG_pow (hn : 0 < n) {L c m : ℕ} (h : L + c = m) :
    (monoX n : Negacyclic R n) ^ L = xInvG R n ^ c * (monoX n) ^ m := by
  rw [← h, pow_add]
  have h1 := xInvG_mul_monoX (R := R) hn
  calc (monoX n : Negacyclic R n) ^ L = monoX n ^ L * (xInvG R n * monoX n) ^ c := by
        rw [h1, one_pow, mul_one]
    _ = _ := by ring

end Mono

/-! ### Table entries -/

theorem val_take_add_cmpl : ∀ (l : List Bool) (m : ℕ), val (l.take m) + cmpl l m = 2 ^ m - 1
  | _, 0 => by simp [cmpl]
  | [], m + 1 => by
    simp only [List.take_nil, Algo.val_nil, zero_add, cmpl, List.getD_nil]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have := Nat.geomSum_eq (m := 2) (by norm_num) (m + 1)
    omega
  | x :: l, m + 1 => by
    have ih := val_take_add_cmpl l m
    have hc : cmpl (x :: l) (m + 1) = (if x then 0 else 1) + 2 * cmpl l m := by
      unfold cmpl
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> ring
    rw [List.take_succ_cons, Algo.val_cons, hc]
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    cases x <;> simp <;> rw [pow_succ] <;> omega

/-! ### `α G` -/

variable (D : Dims)

theorem smul_G_eq_gM (α : Rg D) :
    (fun (a : Fin 2) (c : Fin 2 × Fin D.K) => (α • (setting D).G) a c) = gM (N := D.N) (K := D.K) α := by
  funext a c
  have h := G_apply (S := setting D) a c
  change α * (setting D).G a c = gM α a c
  rw [h]
  simp only [gM]
  split_ifs
  · show α * algebraMap (ZMod D.q) (Rg D) (2 ^ (c.2 : ℕ)) = _
    rw [map_pow, map_ofNat, mul_comm]
  · simp

end AdvancedEncryption.ExpLUT.Prog

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.MVM
  Matrix Cslib AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open SigabaNeo.Lattices.Algo (encRM decRM val)

variable (D : Dims)

/-! ### The data of `EvalPK` as VM families -/

/-- `g = 1 + 2N/W`. -/
abbrev gD : ℕ := gGen D.N (2 ^ D.b)

theorem odd_gD : Odd (gD D) := odd_gGen D.W_dvd

/-- `H_{g_t}` (zero for `t ≥ b`). -/
noncomputable def HfK (mpk : MPKt D) (t : ℕ) : Fin 2 → Fin 2 × Fin D.K → Rq D.N D.K :=
  fun a c => (evalPub (helperMap D) mpk).aut.Hf t a c

/-- `H_{g_t⁻¹}` (zero for `t ≥ b`). -/
noncomputable def HiK (mpk : MPKt D) (t : ℕ) : Fin 2 → Fin 2 × Fin D.K → Rq D.N D.K :=
  fun a c => (evalPub (helperMap D) mpk).aut.Hi t a c

/-- `A^aut_t` (zero for `t ≥ b`). -/
noncomputable def AaK (mpk : MPKt D) (t : ℕ) : DigI D.K → Fin 2 → Fin 2 × Fin D.K → Rq D.N D.K :=
  fun d a c => (evalPub (helperMap D) mpk).aut.Aaut t d a c

/-- `A^in_{i mod 16}`. -/
def AinK (mpk : MPKt D) (i : ℕ) : DigI D.K → Fin 2 → Fin 2 × Fin D.K → Rq D.N D.K :=
  fun d a c => mpk.Ain ⟨i % 16, Nat.mod_lt _ (by decide)⟩ d a c

/-- `X_c = X^{2^{14} − 1}`. -/
noncomputable def xcK : Rq D.N D.K := monoX D.N ^ (2 ^ 14 - 1)

/-- The bits of a transition table: `14 · 2^{22}`. -/
abbrev tlK : ℕ := 14 * 2 ^ 22

/-- The coefficient functions of the steps of the predicate word `C`. -/
noncomputable def cvsK (C : List Bool) (i : ℕ) : Rq D.N D.K → Rq D.N D.K :=
  if i < 15 then cvA 14 (2 ^ D.b) D.b (xcK D) (C.drop (tlK * i))
  else cvV (2 ^ D.b) D.b (C.drop (tlK * 15))

/-! ### The rounds are the chains -/

theorem kf_setting (t : ℕ) : (setting D).kf t = gD D ^ (2 ^ t) := rfl

theorem bitChain_autPK (mpk : MPKt D) (B : Matrix (Fin 2) (Col (setting D).τ) (Rg D)) :
    ∀ t j : ℕ, (fun (a : Fin 2) (c : Fin 2 × Fin D.K) => bitChain (fun s M => autPK (setting D) ((setting D).kf s)
      ((evalPub (helperMap D) mpk).aut.Hf s) ((evalPub (helperMap D) mpk).aut.Aaut s) M) t j B a c) =
      chainM (N := D.N) (K := D.K) (gD D) (HfK D mpk) (AaK D mpk) t j (fun a c => B a c)
  | 0, j => rfl
  | t + 1, j => by
    rw [chainM_succ, ← bitChain_autPK mpk B t j]
    by_cases h : j.testBit t
    · simp only [bitChain, h, ↓reduceIte]
      rw [autPK_eq D (by rw [kf_setting]; exact (odd_gD D).pow)]
      show ginvMulm _ (mulPKm (fun a c => aut D.N _ _) _) = ginvMulm _ (mulPKm _ _)
      congr 2
      funext a' c'
      rw [aut_iterate D (odd_gD D), kf_setting]
    · simp only [bitChain, h, Bool.false_eq_true, ↓reduceIte]

theorem roundsPK_eq_chainM (mpk : MPKt D) (B : Matrix (Fin 2) (Col (setting D).τ) (Rg D)) (j : ℕ)
    (hj : j < 2 ^ D.b) :
    (fun (a : Fin 2) (c : Fin 2 × Fin D.K) =>
      roundsPK (evalPub (helperMap D) mpk).aut B (setting D).b j a c) =
      chainM (N := D.N) (K := D.K) (gD D) (HfK D mpk) (AaK D mpk) D.b j (fun a c => B a c) := by
  have h := roundsPK_eq_bitChain (S := setting D) (evalPub (helperMap D) mpk).aut B (setting D).b j hj
  exact (congrArg (fun M : Matrix (Fin 2) (Col (setting D).τ) (Rg D) =>
    fun (a : Fin 2) (c : Fin 2 × Fin D.K) => M a c) h).trans
    (bitChain_autPK D mpk B D.b j)

/-! ### The coefficients -/

theorem aut_xInvG (j : ℕ) :
    (aut D.N (gD D))^[j] (xInvG (ZMod (2 ^ D.K - 1)) D.N) =
      (setting D).E.σ ((setting D).idx j) ((setting D).E.X ^ (2 * (setting D).E.n - 1)) := by
  rw [aut_iterate D (odd_gD D)]
  show _ = autσ D.N (gD D ^ j) (monoX D.N ^ (2 * D.N - 1))
  rw [autσ_of_odd ((odd_gD D).pow), monoX_pow_two_n_sub_one D.N_pos]

theorem winv_mul (x : Rg D) :
    (setting D).E.Winv * x = (2 : ZMod (2 ^ D.K - 1)) ^ (D.K - D.b) • x := by
  show algebraMap (ZMod D.q) (Rg D) ((2 : ZMod D.q) ^ (D.K - D.b)) * x = _
  rw [← Algebra.smul_def]

theorem uOf_toSt_toSym {u : ℕ} (hu : u < 2 ^ 22) :
    (uOf (toSt (u % wSt)) (toSym (u / wSt))).val = u := by
  show (u % 2 ^ 14) % 2 ^ 14 + 2 ^ 14 * ((u / 2 ^ 14) % 2 ^ 8) = u
  omega

theorem table_bpOf (C : List Bool) {i u : ℕ} (hi : i < 15) (hu : u < 2 ^ 22) :
    (bpOf (progOf C)).table i u = val ((C.drop (14 * (2 ^ 22 * i + u))).take 14) := by
  have hv := Algo.val_lt ((C.drop (14 * (2 ^ 22 * i + u))).take 14)
  have hl : ((C.drop (14 * (2 ^ 22 * i + u))).take 14).length ≤ 14 := by simp
  have h14 : 2 ^ ((C.drop (14 * (2 ^ 22 * i + u))).take 14).length ≤ 2 ^ 14 :=
    Nat.pow_le_pow_right (by norm_num) hl
  simp only [BP.table, bpOf, bpStep, dif_pos hi, progOf, readSt]
  rw [uOf_toSt_toSym hu]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le hv h14)

theorem table15_bpOf (C : List Bool) {u : ℕ} (hu : u < 2 ^ 22) :
    (bpOf (progOf C)).table 15 u = if C.getD (210 * 2 ^ 22 + u) false then 1 else 0 := by
  simp only [BP.table, bpOf, bpStep, lt_irrefl, dite_false, progOf, uOf_toSt_toSym hu]

theorem getD_drop' (C : List Bool) (n u : ℕ) : (C.drop n).getD u false = C.getD (n + u) false := by
  simp [List.getD_eq_getElem?_getD]

theorem coefs_lt (hb : D.b = 22) (C : List Bool) {i : ℕ} (hi : i < 15) (j : ℕ) :
    (bpOf (progOf C)).coefs (setting D) i j =
      cvsK D C i ((aut D.N (gD D))^[j] (xInvG (ZMod (2 ^ D.K - 1)) D.N)) := by
  rw [BP.coefs, if_pos (show i + 1 < (bpOf (progOf C)).T by show i + 1 < 16; omega), cvsK,
    if_pos hi, cvA, alphaCoef, ExpRing.alpha, lutCoef_pow, winv_mul, aut_xInvG]
  congr 1
  simp only [sumA, Finset.sum_mul]
  have hW : (setting D).E.W = 2 ^ D.b := rfl
  rw [hW]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu' : u < 2 ^ 22 := by rw [← hb]; exact Finset.mem_range.mp hu
  rw [table_bpOf C hi hu', List.drop_drop]
  have e : 14 * (2 ^ 22 * i + u) = tlK * i + 14 * u := by simp only [tlK]; ring
  rw [e]
  have h := val_take_add_cmpl (C.drop (tlK * i + 14 * u)) 14
  show monoX D.N ^ _ * _ = _
  rw [monoX_pow_eq_xInvG_pow D.N_pos h, xcK]
  ring

theorem coefs_15 (hb : D.b = 22) (C : List Bool) (j : ℕ) :
    (bpOf (progOf C)).coefs (setting D) 15 j =
      cvsK D C 15 ((aut D.N (gD D))^[j] (xInvG (ZMod (2 ^ D.K - 1)) D.N)) := by
  rw [BP.coefs, if_neg (show ¬ (15 + 1 < (bpOf (progOf C)).T) by show ¬ (15 + 1 < 16); omega),
    cvsK, if_neg (by omega), cvV, vCoef, ExpRing.vcoef, lutCoef_pow, winv_mul, aut_xInvG]
  congr 1
  simp only [sumV]
  have hW : (setting D).E.W = 2 ^ D.b := rfl
  rw [hW]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu' : u < 2 ^ 22 := by rw [← hb]; exact Finset.mem_range.mp hu
  rw [table15_bpOf C hu', getD_drop']
  have e : tlK * 15 = 210 * 2 ^ 22 := by simp only [tlK]; ring
  rw [e]
  split_ifs <;> simp

/-! ### `EvalPK` -/

theorem coefs_eq (hb : D.b = 22) (C : List Bool) {i : ℕ} (hi : i < 16) (j : ℕ) :
    (bpOf (progOf C)).coefs (setting D) i j =
      cvsK D C i ((aut D.N (gD D))^[j] (xInvG (ZMod (2 ^ D.K - 1)) D.N)) := by
  rcases Nat.lt_or_ge i 15 with h | h
  · exact coefs_lt D hb C h j
  · obtain rfl : i = 15 := by omega
    exact coefs_15 D hb C j

/-- One table: the VM's sum is `lutPK`. -/
theorem lutPK_eq (hb : D.b = 22) (mpk : MPKt D) (C : List Bool) {i : ℕ} (hi : i < 16)
    (B : Matrix (Fin 2) (Col (setting D).τ) (Rg D)) :
    lutPK (evalPub (helperMap D) mpk).aut ((bpOf (progOf C)).coefs (setting D) i) B =
      Matrix.of (accM (N := D.N) (K := D.K) (cvsK D C i) (gD D) (HfK D mpk) (AaK D mpk) D.b
        (fun a c => B a c) (xInvG (ZMod (2 ^ D.K - 1)) D.N) (2 ^ D.b)) := by
  have hW : (setting D).E.W = 2 ^ D.b := rfl
  have h1 : lutPK (evalPub (helperMap D) mpk).aut ((bpOf (progOf C)).coefs (setting D) i) B =
      ∑ j ∈ Finset.range (2 ^ D.b), Matrix.of (ginvMulm (N := D.N) (K := D.K)
        (chainM (gD D) (HfK D mpk) (AaK D mpk) D.b j (fun a c => B a c))
        (gM (cvsK D C i ((aut D.N (gD D))^[j] (xInvG (ZMod (2 ^ D.K - 1)) D.N))))) := by
    unfold lutPK
    rw [hW]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < 2 ^ D.b := Finset.mem_range.mp hj
    rw [smulPK, mul_ginv_eq D, smul_G_eq_gM D, roundsPK_eq_chainM D mpk B j hj',
      coefs_eq D hb C hi j]
  rw [h1, accM]
  ext a c
  simp [Matrix.sum_apply, Finset.sum_apply]

/-- **The VM's `EvalPK` is `keyPK`**, step by step. -/
theorem evalPKAt_eq (hb : D.b = 22) (mpk : MPKt D) (C : List Bool) : ∀ i ≤ 16,
    (fun a c => evalPKAt (bpOf (progOf C)) (evalPub (helperMap D) mpk) i a c) =
      evalVM (N := D.N) (K := D.K) (cvsK D C) (gD D) (HfK D mpk) (AaK D mpk) D.b
        (xInvG (ZMod (2 ^ D.K - 1)) D.N) (2 ^ D.b) (AinK D mpk) (fun a c => mpk.A0 a c) i
  | 0, _ => rfl
  | i + 1, hi => by
    have ih := evalPKAt_eq hb mpk C i (by omega)
    simp only [evalPKAt]
    rw [lutPK_eq D hb mpk C (by omega), evalVM, ← ih, mulPK_eq_mulPKm]
    rfl

/-- **The VM's `EvalPK` is `A_F = keyPK mpk (bpOf (progOf C))`.** -/
theorem keyPK_eq_evalVM (hb : D.b = 22) (mpk : MPKt D) (C : List Bool) :
    (fun a c => keyPK (helperMap D) mpk (bpOf (progOf C)) a c) =
      evalVM (N := D.N) (K := D.K) (cvsK D C) (gD D) (HfK D mpk) (AaK D mpk) D.b
        (xInvG (ZMod (2 ^ D.K - 1)) D.N) (2 ^ D.b) (AinK D mpk) (fun a c => mpk.A0 a c) 16 :=
  evalPKAt_eq D hb mpk C 16 le_rfl

end AdvancedEncryption.ExpLUT.Prog
