import PE.Impl.ExpLUT.Params.Conf

/-!
# The noise certificate of ExpLUT at the concrete parameters

**Generic exponent chain** (any `Setting`, bounds as powers of `2`, no power with a large exponent
is ever evaluated):

* `gammaB_le_pow`: `γ = W D^{b+2} ≤ 2^{bw + ed(b+2)}` for `W ≤ 2^bw`, `D ≤ 2^ed`;
* `deltaB_le_pow`: `Δ ≤ 2^{bw + ed(b+1) + (x + et + ed + 3)}` for `τ ≤ 2^et` and `β, B_χ, B_C ≤ 2^x`;
* `stepBound_iterate_le_pow`: Lemma 9, `step^[T] B₀ ≤ 2^{Tm(bw + ed(b+2)) + (bw + ed(b+1) + (x + et + ed + 3) + 1)}`
  for every `T ≤ Tm` (the iterate is monotone in `T`, `stepBound_iterate_mono`).

**At `confS`** (`W = 2^22`, `b = 22`, `τ = K ≤ 2^16`, `n = 2^24`, `D = 2τn ≤ 2^41`, `T ≤ 16`):

* `γ ≤ 2^1006`, Lemma 9 for the encryption errors (`B₀ = β = B_C = B_fl = 2^eFl`, `B_χ = 16`):
  **`B_F ≤ 2^{17122 + eFl} = 2^17522`** (`evalBound_le`);
* the simulation matrices of Corollary 1 (`R* = Z* = 1`, helpers `1`): **`B_R̂ ≤ 2^17122`**
  (`rhatBound_le`; it bounds the closed form `γ^T (1 + Δ_sim)` of `stepBound_iterate_le` too),
  below `2^eRhat = 2^17400`;
* **Lemma 11's trapdoor is covered** (`simShift_le`): its shift is at most
  `simShift B_R̂ = W τ n D^b (B_R̂ + 2)` (`‖X‖∞ ≤ D^b (B_R̂ + 2)`, then `T_sim z = X_P · gadDec(·)` sums
  `Wτ` binary-digit products), which is at most `2^{965 + eRhat} ≤ coverBound = 2^eSh` for every
  `B_R̂ ≤ 2^eRhat`;
* **the correctness condition** (`corrBound_le`, `four_corrBound_lt`): for keys within
  `2^{Bk−1}` (the small box and the binary decompositions),
  `corrBound ≤ 16 + 2^{36361}` and `4 · corrBound + 2 < q = 2^{2^16} − 1`; hence decoding is exact
  (`decode_ok`);
* **the flooding budget** (`flood_budget`): at most `2^81` flooded coefficients, shifts at most
  `m_B n B_χ ≤ 2^70`, so `Σ|δ| / 2^eFl ≤ 2^{−249}`.
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices

variable {R : Type*} [CommRing R] (S : Setting R)

/-- `γ ≤ 2^{bw + ed(b+2)}`. -/
theorem gammaB_le_pow {bw ed : ℕ} (hW : S.E.W ≤ 2 ^ bw) (hD : S.gfac ≤ 2 ^ ed) :
    gammaB S ≤ 2 ^ (bw + ed * (S.b + 2)) := by
  unfold gammaB
  rw [pow_add 2 bw, pow_mul 2 ed]
  exact Nat.mul_le_mul hW (Nat.pow_le_pow_left hD _)

/-- The inner factor of `Δ`, with the bounds as variables. -/
theorem deltaInner_le {τ g β Bχ BC c d a : ℕ} (hτ : τ ≤ c) (hg : g ≤ d) (hβ : β ≤ a) (hχ : Bχ ≤ a)
    (hC : BC ≤ a) (hc : 1 ≤ c) (hd : 2 ≤ d) :
    2 * τ * g * β + BC + 2 * (2 * τ * β + 2 * Bχ) ≤ 8 * c * d * a := by
  have h1 : τ * g * β ≤ c * d * a := Nat.mul_le_mul (Nat.mul_le_mul hτ hg) hβ
  have h2 : τ * β ≤ c * a := Nat.mul_le_mul hτ hβ
  have hca : a ≤ c * a := Nat.le_mul_of_pos_left a hc
  have hcda : 2 * (c * a) ≤ c * d * a := by
    calc 2 * (c * a) = c * 2 * a := by ring
      _ ≤ c * d * a := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hd)
  calc 2 * τ * g * β + BC + 2 * (2 * τ * β + 2 * Bχ)
      = 2 * (τ * g * β) + BC + 4 * (τ * β) + 4 * Bχ := by ring
    _ ≤ 2 * (c * d * a) + a + 4 * (c * a) + 4 * a := by omega
    _ ≤ 8 * c * d * a := by
      have e : 8 * c * d * a = 8 * (c * d * a) := by ring
      rw [e]; omega

/-- `Δ ≤ 2^{bw + ed(b+1) + (x + et + ed + 3)}`. -/
theorem deltaB_le_pow {bw ed et x β Bχ BC : ℕ} (hW : S.E.W ≤ 2 ^ bw) (hD : S.gfac ≤ 2 ^ ed)
    (hed : 1 ≤ ed) (hτ : S.τ ≤ 2 ^ et) (hβ : β ≤ 2 ^ x) (hχ : Bχ ≤ 2 ^ x) (hC : BC ≤ 2 ^ x) :
    deltaB S β Bχ BC ≤ 2 ^ (bw + ed * (S.b + 1) + (x + et + ed + 3)) := by
  unfold deltaB
  have hd : 2 ≤ 2 ^ ed :=
    (show 2 = 2 ^ 1 from rfl).le.trans (Nat.pow_le_pow_right (n := 2) (by norm_num) hed)
  have hin := deltaInner_le hτ hD hβ hχ hC Nat.one_le_two_pow hd
  have e : 2 ^ (x + et + ed + 3) = 8 * 2 ^ et * 2 ^ ed * 2 ^ x := by
    rw [pow_add 2 (x + et + ed) 3, pow_add 2 (x + et) ed, pow_add 2 x et]; ring
  rw [← e] at hin
  rw [pow_add 2 (bw + ed * (S.b + 1)), pow_add 2 bw, pow_mul 2 ed]
  exact Nat.mul_le_mul (Nat.mul_le_mul hW (Nat.pow_le_pow_left hD _)) hin

theorem le_stepBound (hD : 1 ≤ S.gfac) (hW : 1 ≤ S.E.W) (β Bχ BC E : ℕ) :
    E ≤ stepBound S β Bχ BC E := by
  unfold stepBound
  have h1 : S.gfac * E + 2 * S.τ * S.gfac * β + BC ≤
      (autBound S β Bχ)^[S.b] (S.gfac * E + 2 * S.τ * S.gfac * β + BC) :=
    le_autBound_iterate hD β Bχ _ 0 S.b (Nat.zero_le _)
  have h2 : E ≤ S.gfac * E := Nat.le_mul_of_pos_left E hD
  calc E ≤ (autBound S β Bχ)^[S.b] (S.gfac * E + 2 * S.τ * S.gfac * β + BC) := by omega
    _ ≤ S.gfac * (autBound S β Bχ)^[S.b] (S.gfac * E + 2 * S.τ * S.gfac * β + BC) :=
        Nat.le_mul_of_pos_left _ hD
    _ ≤ S.E.W * (S.gfac * (autBound S β Bχ)^[S.b] (S.gfac * E + 2 * S.τ * S.gfac * β + BC)) :=
        Nat.le_mul_of_pos_left _ hW

/-- The iterate of Lemma 9 is monotone in the length. -/
theorem stepBound_iterate_mono (hD : 1 ≤ S.gfac) (hW : 1 ≤ S.E.W) (β Bχ BC B0 : ℕ) {T T' : ℕ}
    (h : T ≤ T') : (stepBound S β Bχ BC)^[T] B0 ≤ (stepBound S β Bχ BC)^[T'] B0 := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (le_stepBound S hD hW _ _ _ _)

/-- **Lemma 9 in exponents**: for every `T ≤ Tm`, `step^[T] B₀ ≤ 2^{Tm g + (δ + 1)}` with
`g = bw + ed(b+2)` and `δ = bw + ed(b+1) + (x + et + ed + 3)`. -/
theorem stepBound_iterate_le_pow {bw ed et x β Bχ BC B0 T Tm : ℕ} (hD2 : 2 ≤ S.gfac)
    (hW1 : 1 ≤ S.E.W) (hW : S.E.W ≤ 2 ^ bw) (hD : S.gfac ≤ 2 ^ ed) (hed : 1 ≤ ed)
    (hτ : S.τ ≤ 2 ^ et) (hβ : β ≤ 2 ^ x) (hχ : Bχ ≤ 2 ^ x) (hC : BC ≤ 2 ^ x) (hB0 : B0 ≤ 2 ^ x)
    (hT : T ≤ Tm) :
    (stepBound S β Bχ BC)^[T] B0 ≤
      2 ^ (Tm * (bw + ed * (S.b + 2)) + (bw + ed * (S.b + 1) + (x + et + ed + 3) + 1)) := by
  refine (stepBound_iterate_mono S (by omega) hW1 β Bχ BC B0 hT).trans ?_
  refine (stepBound_iterate_le hD2 hW1 β Bχ BC B0 Tm).trans ?_
  have hγ : gammaB S ^ Tm ≤ 2 ^ (Tm * (bw + ed * (S.b + 2))) := by
    rw [Nat.mul_comm Tm, pow_mul 2 _ Tm]
    exact Nat.pow_le_pow_left (gammaB_le_pow S hW hD) _
  have hΔ := deltaB_le_pow S hW hD hed hτ hβ hχ hC
  have hx : B0 ≤ 2 ^ (bw + ed * (S.b + 1) + (x + et + ed + 3)) :=
    hB0.trans (Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega))
  have hs : B0 + deltaB S β Bχ BC ≤ 2 ^ (bw + ed * (S.b + 1) + (x + et + ed + 3) + 1) := by
    rw [pow_succ]; omega
  rw [pow_add 2 (Tm * (bw + ed * (S.b + 2)))]
  exact Nat.mul_le_mul hγ hs

end AdvancedEncryption.ExpLUT

namespace AdvancedEncryption.ExpLUT.Params

open SigabaNeo.Lattices Cslib

theorem confS_b' : confS.b = 22 := rfl

/-- `1 + d ≤ 2^{e+1}` for `d ≤ 2^e` (generic). -/
theorem one_add_le_pow {d e : ℕ} (h : d ≤ 2 ^ e) : 1 + d ≤ 2 ^ (e + 1) := by
  have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  rw [pow_succ]; omega

theorem W_le : confS.E.W ≤ 2 ^ 22 := le_of_eq rfl
theorem one_le_W : 1 ≤ confS.E.W := Nat.one_le_two_pow
theorem τ_le : confS.τ ≤ 2 ^ 16 := Kc_le

theorem four_le_eFl : 4 ≤ eFl := by rw [eFl_def]; norm_num

theorem Bχ_le : Bχ ≤ 2 ^ eFl := (show Bχ = 2 ^ 4 from rfl).le.trans (pow_le_pow' four_le_eFl)

/-! ### Lemma 9 at the concrete parameters -/

/-- **The error of `c_F`** (Lemma 9, encryption errors): `B_F ≤ 2^{17122 + eFl}` for `T ≤ 16`. -/
theorem evalBound_le {T : ℕ} (hT : T ≤ 16) : evalBound confS T Bχ Bfl ≤ 2 ^ (17122 + eFl) := by
  have h := stepBound_iterate_le_pow confS (bw := 22) (ed := 41) (et := 16) (x := eFl) (β := Bfl)
    (Bχ := Bχ) (BC := Bfl) (B0 := Bfl) (T := T) (Tm := 16) two_le_gfac one_le_W W_le gfac_le
    (by norm_num) τ_le le_rfl Bχ_le le_rfl le_rfl hT
  rw [confS_b'] at h
  refine h.trans (pow_le_pow' (le_of_eq ?_))
  omega

/-- The bound `B_R̂` of the simulation matrices for `R* = Z* = 1` (Corollary 1): Lemma 9's
recurrence with all initial witnesses, digit witnesses and helpers within `1`. -/
theorem rhatBound_le {T : ℕ} (hT : T ≤ 16) : (stepBound confS 1 1 1)^[T] 1 ≤ 2 ^ 17122 := by
  have h := stepBound_iterate_le_pow confS (bw := 22) (ed := 41) (et := 16) (x := 0) (β := 1)
    (Bχ := 1) (BC := 1) (B0 := 1) (T := T) (Tm := 16) two_le_gfac one_le_W W_le gfac_le
    (by norm_num) τ_le le_rfl le_rfl le_rfl le_rfl hT
  rw [confS_b'] at h
  refine h.trans (pow_le_pow' ?_)
  norm_num

theorem eRhat_ge : 17122 ≤ eRhat := by rw [eRhat_def]; norm_num

theorem rhatBound_le_eRhat {T : ℕ} (hT : T ≤ 16) : (stepBound confS 1 1 1)^[T] 1 ≤ 2 ^ eRhat :=
  (rhatBound_le hT).trans (pow_le_pow' eRhat_ge)

/-! ### Lemma 11: the simulated trapdoor is covered -/

/-- **The shift of Lemma 11's simulated trapdoor** for simulation matrices `R̂_F` with
coefficients within `B`: `‖X‖∞ ≤ D^b (B + 2)` (one gadget move per element of the binary basis,
`V_{j·a} = V_j G̃⁻¹(σ_j(H_a⁽¹⁾)) − J̃_{η_{j,a}}` multiplies by at most `D = 2τn` and adds `1`), and
`T_sim z = X_P · gadDec(M_F(0, z) − (I_W ⊗ g) z)` sums `W τ` products with binary digits:
`‖T_sim z‖∞ ≤ W τ n ‖X‖∞`. -/
noncomputable def simShift (B : ℕ) : ℕ := confS.E.W * confS.τ * confS.E.n * (confS.gfac ^ confS.b * (B + 2))

/-- The shift bound in exponents (generic). -/
theorem simShift_gen {W τ n g b B eW eτ en eg eB : ℕ} (hW : W ≤ 2 ^ eW) (hτ : τ ≤ 2 ^ eτ)
    (hn : n ≤ 2 ^ en) (hg : g ≤ 2 ^ eg) (hB : B + 2 ≤ 2 ^ eB) :
    W * τ * n * (g ^ b * (B + 2)) ≤ 2 ^ (eW + eτ + en + (eg * b + eB)) := by
  have hgb : g ^ b ≤ 2 ^ (eg * b) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hg b
  exact pow_mul_le' (pow_mul_le' (pow_mul_le' hW hτ rfl) hn rfl) (pow_mul_le' hgb hB rfl) rfl

/-- `B + 2 ≤ 2^{e+1}` for `B ≤ 2^e`, `e ≥ 1` (generic). -/
theorem add_two_le_pow {B e : ℕ} (hB : B ≤ 2 ^ e) (he : 1 ≤ e) : B + 2 ≤ 2 ^ (e + 1) := by
  have : 2 ≤ 2 ^ e := (show 2 = 2 ^ 1 from rfl).le.trans (pow_le_pow' he)
  rw [pow_succ]; omega

/-- **Lemma 11's trapdoor is covered by the key boxes** whenever `B_R̂ ≤ 2^eRhat`. -/
theorem simShift_le {B : ℕ} (hB : B ≤ 2 ^ eRhat) : simShift B ≤ coverBound := by
  have h := simShift_gen (b := confS.b) W_le τ_le (le_of_eq rfl : confS.E.n ≤ 2 ^ 24) gfac_le
    (add_two_le_pow hB (by rw [eRhat_def]; norm_num))
  refine h.trans (pow_le_pow' ?_)
  rw [confS_b', eSh_def, eRhat_def]; norm_num

/-- Lemma 11's trapdoor with `R̂_F` from Corollary 1 (`R* = Z* = 1`, `T ≤ 16`) is covered. -/
theorem simShift_rhat_le {T : ℕ} (hT : T ≤ 16) :
    simShift ((stepBound confS 1 1 1)^[T] 1) ≤ coverBound :=
  simShift_le (rhatBound_le_eRhat hT)

/-! ### The correctness condition -/

/-- The bound on the coefficients of keys: the small box and the binary decompositions. -/
abbrev Kkey : ℕ := 2 ^ (Bk - 1)

/-- `|KCol| = W(m̄ + τ) + W|J|2τ + 2τ` (generic, with the instance of `corrBound`). -/
theorem card_KCol_gen {τ W : ℕ} (Wb J : Type*) [Fintype Wb] [Fintype J] :
    Fintype.card (KCol Wb J τ W) =
      W * (Fintype.card Wb + τ) + (W * (Fintype.card J * (2 * τ)) + 2 * τ) := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]

theorem card_KCol_conf : Fintype.card (KCol Wbc Jc confS.τ confS.E.W) ≤ 2 ^ 65 := by
  rw [card_KCol_gen, Fintype.card_fin, card_Jc, confS_W, confS_τ]
  exact card_gen_le mbar_le Kc_le

/-- The exponent of the noise bound. -/
def eNoise : ℕ := 65 + 24 + (17122 + eFl) + (Bk - 1)

/-- **The noise bound**: `corrBound ≤ 16 + 2^eNoise` (`eNoise = 36360`) for `T ≤ 16` and keys
within `2^{Bk−1}`. -/
theorem corrBound_le {T : ℕ} (hT : T ≤ 16) :
    corrBound confS Wbc Jc T Bχ Bfl Kkey ≤ 16 + 2 ^ eNoise := by
  unfold corrBound
  have hmax : max Bχ (evalBound confS T Bχ Bfl) ≤ 2 ^ (17122 + eFl) :=
    max_le (Bχ_le.trans (pow_le_pow' (by omega))) (evalBound_le hT)
  have hn : confS.E.n ≤ 2 ^ 24 := le_of_eq rfl
  have h := pow_mul_le' card_KCol_conf (pow_mul_le' (pow_mul_le' hn hmax rfl) (le_refl Kkey) rfl)
    (show 65 + (24 + (17122 + eFl) + (Bk - 1)) = eNoise by unfold eNoise; omega)
  exact Nat.add_le_add_left h 16

theorem eNoise_lt : eNoise + 3 < Kc := by
  unfold eNoise; rw [eFl_def, Bk_def, Kc_def]; norm_num

theorem five_le_eNoise : 5 ≤ eNoise := by unfold eNoise; omega

/-- The final arithmetic, with the large numbers as variables. -/
theorem four_lt_gen {c p Q : ℕ} (hc : c ≤ 16 + p) (hp : 32 ≤ p) (hQ : 8 * p ≤ Q) :
    4 * c + 2 < Q - 1 := by
  omega

/-- **The correctness condition**: `4 · corrBound + 2 < q`. -/
theorem four_corrBound_lt {T : ℕ} (hT : T ≤ 16) :
    4 * corrBound confS Wbc Jc T Bχ Bfl Kkey + 2 < qc := by
  have hp : 32 ≤ 2 ^ eNoise :=
    (show 32 = 2 ^ 5 from rfl).le.trans (pow_le_pow' five_le_eNoise)
  have hQ : 8 * 2 ^ eNoise ≤ 2 ^ Kc := by
    have : 8 * 2 ^ eNoise = 2 ^ (eNoise + 3) := by rw [pow_add]; ring
    rw [this]; exact pow_le_pow' eNoise_lt.le
  exact four_lt_gen (corrBound_le hT) hp hQ

/-! ### Messages and decoding -/

/-- `⌊q/2⌋` in the ring (the constant). -/
noncomputable def half : Rc := algebraMap (ZMod qc) Rc ((qc / 2 : ℕ) : ZMod qc)

/-- A bit as a ring element: `1` or `0`. -/
def msgR (M : Bool) : Rc := if M then 1 else 0

theorem half_mul_msgR (M : Bool) : half * msgR M = algebraMap (ZMod qc) Rc (encodeBit qc M) := by
  cases M
  · simp [msgR, encodeBit]
  · simp [msgR, encodeBit, half]

/-- Decoding is exact for errors within `C` when `4C + 2 < q` (generic). -/
theorem decodeBit_ok {q N : ℕ} [NeZero q] (hN : 0 < N) (M : Bool) (e : Negacyclic (ZMod q) N)
    (C : ℕ) (he : cnorm e ≤ C) (hC : 4 * C + 2 < q) :
    decodeBit hN (algebraMap (ZMod q) _ (encodeBit q M) + e) = M := by
  apply decodeBit_encodeBit_add
  have h0 : zabs (e.coeffs ⟨0, hN⟩) ≤ C := (zabs_coeffs_le_cnorm _ _).trans he
  have h1 : |(e.coeffs ⟨0, hN⟩).valMinAbs| = ((zabs (e.coeffs ⟨0, hN⟩) : ℕ) : ℤ) := by
    simp only [zabs, Int.natCast_natAbs]
  rw [h1]
  have : 4 * zabs (e.coeffs ⟨0, hN⟩) + 2 < q := by omega
  exact_mod_cast this

/-- **Decoding at the concrete parameters**: every error within `corrBound` is removed. -/
theorem decode_ok {T : ℕ} (hT : T ≤ 16) (M : Bool) (e : Rc)
    (he : cnorm e ≤ corrBound confS Wbc Jc T Bχ Bfl Kkey) :
    decodeBit hnc (half * msgR M + e) = M := by
  rw [half_mul_msgR]
  exact decodeBit_ok hnc M e _ he (four_corrBound_lt hT)

/-! ### The flooding budget (for hybrid H2) -/

/-- The flooded ring elements: `e₀` (`2τ`), the `e_t` (`16 · 2τ`), the errors of the digit
encodings of `C^in_t` and `C_{g_t}` (`(16 + 22) · 4τ² · 2τ`); `lhlCols` counts one more. Their
coefficients number at most `2^81`. -/
theorem floodCoefs_le : lhlCols * 2 ^ en ≤ 2 ^ 81 :=
  pow_mul_le' lhlCols_le (le_refl _) rfl

/-- The shift that flooding must hide, per coefficient: a product of a base error row (`m_B = m̄ + τ`
entries within `B_χ`) with a binary programming column, `m_B · n · B_χ ≤ 2^70` (the factor `n`
covers products of ring elements). -/
theorem floodShift_le : (mbar + Kc) * 2 ^ en * Bχ ≤ 2 ^ 70 :=
  pow_mul_le' (pow_mul_le' mbar_le (le_refl _) rfl) (le_of_eq rfl : Bχ ≤ 2 ^ 4) rfl

/-- **The flooding budget**: `#coefficients · shift / 2^eFl ≤ 2^{−249}` (`closeTo_floodLaw_add`
bounds the statistical distance of flooding by `Σ |δ| / W`). -/
theorem flood_budget : lhlCols * 2 ^ en * ((mbar + Kc) * 2 ^ en * Bχ) * 2 ^ 249 ≤ 2 ^ eFl := by
  refine (Nat.mul_le_mul_right _ (pow_mul_le' floodCoefs_le floodShift_le rfl)).trans ?_
  rw [← pow_add]
  exact pow_le_pow' (by rw [eFl_def])

end AdvancedEncryption.ExpLUT.Params
