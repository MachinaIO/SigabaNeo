import PE.Impl.ExpLUT.Ops
import Mathlib.Algebra.Module.BigOperators
import SigabaNeoStd.Lattices.Automorphism.LUT

/-!
# Lookup tables over encodings (Lemma 8)

From an encoding `c : ⟦X^u s⟧^A_s`, the rounds of §4.3 apply `Aut_{g_t}` along the binary basis
`g_t = g^{2^t}` (`t < b`): in round `t`, `c_{j + 2^t} := Aut_{g_t}(c_j)` for `j < 2^t`, so that after
`b` rounds `c_j : ⟦σ_{g^j}(X^u) s⟧_s` for every `j < W = 2^b` (`roundsPK`, `roundsCT`,
`roundsErr`, `encodes_rounds`). The table is then `LUT(c) := Σ_{j<W} SMul_{α_j}(c_j)` (`lutPK`,
`lutCT`, `lutErr`, `encodes_lut`): it encodes `Σ_j α_j σ_{g^j}(X^u)`, which is `X^{L(u)}` for the
coefficients `α_{k,L}` and `L(u)` for `v_{k,L}` (`encodes_lut_of_spec`).

* The helper data of round `t` (`AutPub`, `AutData`): `H_{g_t}`, `H_{g_t^{-1}}`, the digit matrices
  `A^aut_{t,·}` (public), the helpers `h_{g_t}`, `h_{g_t^{-1}}` and the digit encodings of `C_{g_t}`
  under `s_{g_t}` (ciphertext), indexed by `t : ℕ` (only `t < b` is used). Their exact form
  (`HelperOK`): `h_k = s H_k − s_k G + e_k` and `c_{t,d} = s_k(A^aut_{t,d} − d_d(C_k) G) + e_{t,d}`.
* The coefficients are those of Lemma 8 (`ExpRing.alpha`, `ExpRing.vcoef` of
  `SigabaNeoStd.Lattices.Automorphism.LUT`), `α_{k,L} = W⁻¹ Σ_{j<W} X^{L(j)} σ_k(X^{2n−j})` and
  `v_{k,L} = W⁻¹ Σ_{j<W} L(j) σ_k(X^{2n−j})`, at `k = g^j` (`alphaCoef`, `vCoef`). The identities of
  Lemma 8 over the exponents of the setting (`Lemma8`) are a hypothesis here; for the canonical
  setting `idx j = g^j` they are `ExpRing.lut_alpha_pow`, `ExpRing.lut_vcoef_pow`
  (`PE.Impl.ExpLUT.Canonical`).
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix

variable {R : Type*} [CommRing R] (S : Setting R)

/-- The index of the basis automorphism `g_t = g^{2^t}`. -/
abbrev Setting.kf (t : ℕ) : ℕ := S.idx (2 ^ t)

/-- The index of its inverse `g^{W − 2^t}`. -/
abbrev Setting.ki (t : ℕ) : ℕ := S.idx (S.E.W - 2 ^ t)

/-- The public helper data of the rounds: `H_{g_t}`, `H_{g_t^{-1}}` and `A^aut_{t,·}`. -/
structure AutPub where
  /-- `H_{g_t}`. -/
  Hf : ℕ → Matrix (Fin 2) (Col S.τ) R
  /-- `H_{g_t^{-1}}`. -/
  Hi : ℕ → Matrix (Fin 2) (Col S.τ) R
  /-- `A^aut_{t, (r, j, i)}`. -/
  Aaut : ℕ → Dig S.τ → Matrix (Fin 2) (Col S.τ) R

/-- The helper data of a ciphertext (or their errors): `h_{g_t}`, `h_{g_t^{-1}}` and the digit
encodings of `C_{g_t}`. -/
structure AutData where
  /-- `h_{g_t}`. -/
  hf : ℕ → Col S.τ → R
  /-- `h_{g_t^{-1}}`. -/
  hi : ℕ → Col S.τ → R
  /-- `c^aut_{t, (r, j, i)}`. -/
  caut : ℕ → Dig S.τ → Col S.τ → R

variable {S}

/-- The helper data of round `t` are exact: the helpers encode `s_{g_t}` and `s_{g_t^{-1}}` under
`s`, and the digit encodings encode the digits of `C_{g_t}` under `s_{g_t}`, with the errors `er`. -/
def HelperOK (P : AutPub S) (h er : AutData S) (sb : R) (t : ℕ) : Prop :=
  Encodes S (sec sb) (P.Hf t) (sec (S.E.σ (S.kf t) sb)) (er.hf t) (h.hf t) ∧
    Encodes S (sec sb) (P.Hi t) (sec (S.E.σ (S.ki t) sb)) (er.hi t) (h.hi t) ∧
    ∀ d, Encodes S (sec (S.E.σ (S.kf t) sb)) (P.Aaut t d)
      (digits S (gcAut S (S.kf t) (P.Hi t) (h.hi t)) d • sec (S.E.σ (S.kf t) sb)) (er.caut t d)
      (h.caut t d)

/-! ### Rounds -/

/-- The public matrices after `t` rounds: `A_j` for `j < 2^t`. -/
def roundsPK (P : AutPub S) (A : Matrix (Fin 2) (Col S.τ) R) : ℕ → ℕ → Matrix (Fin 2) (Col S.τ) R
  | 0, _ => A
  | t + 1, j =>
    if j < 2 ^ t then roundsPK P A t j else autPK S (S.kf t) (P.Hf t) (P.Aaut t) (roundsPK P A t (j - 2 ^ t))

/-- The encodings after `t` rounds: `c_j` for `j < 2^t`. -/
def roundsCT (P : AutPub S) (A : Matrix (Fin 2) (Col S.τ) R) (h : AutData S) (c : Col S.τ → R) :
    ℕ → ℕ → Col S.τ → R
  | 0, _ => c
  | t + 1, j =>
    if j < 2 ^ t then roundsCT P A h c t j
    else autCT S (S.kf t) (P.Hi t) (P.Aaut t) (roundsPK P A t (j - 2 ^ t)) (h.hf t) (h.hi t)
      (h.caut t) (roundsCT P A h c t (j - 2 ^ t))

/-- The errors after `t` rounds, for the payload `μ` of the input. -/
def roundsErr (P : AutPub S) (A : Matrix (Fin 2) (Col S.τ) R) (h : AutData S) (μ : R)
    (er : AutData S) (e : Col S.τ → R) : ℕ → ℕ → Col S.τ → R
  | 0, _ => e
  | t + 1, j =>
    if j < 2 ^ t then roundsErr P A h μ er e t j
    else autErr S (S.kf t) (P.Hi t) (P.Aaut t) (roundsPK P A t (j - 2 ^ t)) (h.hi t)
      (S.E.σ (S.idx (j - 2 ^ t)) μ) (er.hf t) (er.hi t) (er.caut t) (roundsErr P A h μ er e t (j - 2 ^ t))

/-- **The rounds** (Lemma 8, "Rounds"): after `t ≤ b` rounds, `c_j : ⟦σ_{g^j}(μ) s⟧^{A_j}_s` for
every `j < 2^t`, exactly. -/
theorem encodes_rounds (P : AutPub S) {A : Matrix (Fin 2) (Col S.τ) R} (h er : AutData S) {sb μ : R}
    {e c : Col S.τ → R} (hc : Encodes S (sec sb) A (μ • sec sb) e c)
    (hH : ∀ t < S.b, HelperOK P h er sb t) :
    ∀ t ≤ S.b, ∀ j < 2 ^ t, Encodes S (sec sb) (roundsPK P A t j) (S.E.σ (S.idx j) μ • sec sb)
      (roundsErr P A h μ er e t j) (roundsCT P A h c t j) := by
  intro t
  induction t with
  | zero =>
    intro _ j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simpa [roundsPK, roundsCT, roundsErr, S.idx_zero] using hc
  | succ t ih =>
    intro ht j hj
    simp only [roundsPK, roundsCT, roundsErr]
    split_ifs with hjt
    · exact ih (by omega) j hjt
    · have hW : 2 ^ (t + 1) ≤ S.E.W := by
        rw [S.W_eq]; exact Nat.pow_le_pow_right (by norm_num) ht
      have hj' : j - 2 ^ t < 2 ^ t := by rw [pow_succ] at hj; omega
      obtain ⟨h1, h2, h3⟩ := hH t (by omega)
      have hkk : ∀ a, S.E.σ (S.kf t) (S.E.σ (S.ki t) a) = a :=
        σ_idx_inv t (le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ t)) hW)
      have := encodes_aut (S.kf t) (S.ki t) hkk sb (ih (by omega) (j - 2 ^ t) hj') h1 h2 h3
      have hμ : S.E.σ (S.kf t) (S.E.σ (S.idx (j - 2 ^ t)) μ) = S.E.σ (S.idx j) μ := by
        rw [S.idx_add, show 2 ^ t + (j - 2 ^ t) = j by omega, Nat.mod_eq_of_lt (by omega)]
      rwa [hμ] at this

/-! ### The table -/

/-- `EvalPK` of `LUT`: `Σ_{j<W} A_j G⁻¹(α_j G)`. -/
def lutPK (P : AutPub S) (coef : ℕ → R) (A : Matrix (Fin 2) (Col S.τ) R) : Matrix (Fin 2) (Col S.τ) R :=
  ∑ j ∈ Finset.range S.E.W, smulPK S (coef j) (roundsPK P A S.b j)

/-- `EvalCT` of `LUT`: `Σ_{j<W} c_j G⁻¹(α_j G)`. -/
def lutCT (P : AutPub S) (coef : ℕ → R) (A : Matrix (Fin 2) (Col S.τ) R) (h : AutData S)
    (c : Col S.τ → R) : Col S.τ → R :=
  ∑ j ∈ Finset.range S.E.W, smulCT S (coef j) (roundsCT P A h c S.b j)

/-- The error of `LUT`. -/
def lutErr (P : AutPub S) (coef : ℕ → R) (A : Matrix (Fin 2) (Col S.τ) R) (h : AutData S) (μ : R)
    (er : AutData S) (e : Col S.τ → R) : Col S.τ → R :=
  ∑ j ∈ Finset.range S.E.W, smulCT S (coef j) (roundsErr P A h μ er e S.b j)

/-- **The table**: `LUT(c) : ⟦(Σ_j α_j σ_{g^j}(μ)) s⟧^{A_L}_s`, exactly. -/
theorem encodes_lut (P : AutPub S) (coef : ℕ → R) {A : Matrix (Fin 2) (Col S.τ) R} (h er : AutData S)
    {sb μ : R} {e c : Col S.τ → R} (hc : Encodes S (sec sb) A (μ • sec sb) e c)
    (hH : ∀ t < S.b, HelperOK P h er sb t) :
    Encodes S (sec sb) (lutPK P coef A)
      ((∑ j ∈ Finset.range S.E.W, coef j * S.E.σ (S.idx j) μ) • sec sb)
      (lutErr P coef A h μ er e) (lutCT P coef A h c) := by
  have hr := encodes_rounds P h er hc hH S.b le_rfl
  rw [Finset.sum_smul]
  refine encodes_sum _ fun j hj => ?_
  rw [mul_smul]
  exact encodes_smul _ (hr j (by rw [← S.W_eq]; exact Finset.mem_range.mp hj))

/-! ### Coefficients (Lemma 8) -/

/-- The coefficients `α_{g^j, L}` of the table `L`, indexed by the exponent `j`
(`ExpRing.alpha`: `α_{k,L} = W⁻¹ Σ_{i<W} X^{L(i)} σ_k(X^{2n−i})`). -/
def alphaCoef (L : ℕ → ℕ) (j : ℕ) : R := S.E.alpha L (S.idx j)

/-- The coefficients `v_{g^j, L}` (`ExpRing.vcoef`: `v_{k,L} = W⁻¹ Σ_{i<W} L(i) σ_k(X^{2n−i})`). -/
def vCoef (L : ℕ → ℕ) (j : ℕ) : R := S.E.vcoef L (S.idx j)

variable (S) in
/-- A table specification: on every `X^u` with `u < W`, the coefficients `coef` give `out u`. -/
def LUTSpec (coef : ℕ → R) (out : ℕ → R) : Prop :=
  ∀ u < S.E.W, ∑ j ∈ Finset.range S.E.W, coef j * S.E.σ (S.idx j) (S.E.X ^ u) = out u

variable (S) in
/-- **Lemma 8 over the binary basis** (`lemma8_canon` for the canonical setting): for
every table `L`, `Σ_{j<W} α_{g^j,L} σ_{g^j}(X^u) = X^{L(u)}` and `Σ_{j<W} v_{g^j,L} σ_{g^j}(X^u) = L(u)`
for every `u < W`. -/
def Lemma8 : Prop :=
  ∀ L : ℕ → ℕ, LUTSpec S (alphaCoef (S := S) L) (fun u => S.E.X ^ L u) ∧
    LUTSpec S (vCoef (S := S) L) (fun u => (L u : R))

/-- **Lemma 8 over encodings**: for coefficients with the specification `out`,
`LUT(c) : ⟦out(u) s⟧^{A_L}_s` from `c : ⟦X^u s⟧^A_s`, exactly. -/
theorem encodes_lut_of_spec (P : AutPub S) {coef : ℕ → R} {out : ℕ → R} (hspec : LUTSpec S coef out)
    {A : Matrix (Fin 2) (Col S.τ) R} (h er : AutData S) {sb : R} {u : ℕ} (hu : u < S.E.W)
    {e c : Col S.τ → R} (hc : Encodes S (sec sb) A (S.E.X ^ u • sec sb) e c)
    (hH : ∀ t < S.b, HelperOK P h er sb t) :
    Encodes S (sec sb) (lutPK P coef A) (out u • sec sb) (lutErr P coef A h (S.E.X ^ u) er e)
      (lutCT P coef A h c) := by
  have := encodes_lut P coef h er hc hH
  rwa [hspec u hu] at this

end AdvancedEncryption.ExpLUT
