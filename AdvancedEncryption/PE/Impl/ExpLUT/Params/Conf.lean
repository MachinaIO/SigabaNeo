import PE.Impl.ExpLUT.Laws
import PE.Impl.ExpLUT.NegacyclicNorm
import SigabaNeoStd.Lattices.RingBoxes
import SigabaNeoStd.Lattices.ModuleLWE
import SigabaNeoStd.Lattices.Decode

/-!
# The concrete configuration of ExpLUT

The parameters of the scheme of ePrint 2026/2539 §5 for the 128-bit BP universe with symbols of
`8` bits (`PE.BranchingProgram.w8`: `16` symbols, `14`-bit states, so `W = 2^14 · 2^8 = 2^22`,
`b = 22`, `T = 16`), at the ring of the certified strength (`Params/Strength.lean`:
`1155 ≤ CircularRingLWE.H` at `N = 2^24`, `q = 2^(2^16) − 1`, CBD(16)).

* **Ring.** `Rc = ℤ_q[X]/(X^n + 1)` with `n = 2^24`, `q = 2^K − 1`, `K = 2^16` (`Kc`, opaque:
  no power `2^K` is ever evaluated). `2W = 2^23 ∣ n`.
* **Setting** (`confS`): `expRingOf` with `W⁻¹ = 2^(K − 22)` (the instance `expRingMersenne`), the
  canonical `H` (`idx j = g^j`, `canonSetting`), binary gadget digits with `τ = K` (`q ≤ 2^K`);
  its norm is `cnorm` (`confN = cnormSpec …`); `D = 2τn = 2^41`.
* **Helpers** (`helperJ`): `J = K ∪ K⁻¹` as `Fin 22 ⊕ Fin 21` (`g_t` for `t < 22` and `g_t^{-1}`
  for `t < 21`; `g_{21} = g^{W/2}` is its own inverse), `|J| = 43`.
* **`m̄ = 3nK + 408`** columns of `Ā` (`mbar`), see `mbar_lhl` for the reasoning.
* **Laws**: `χT` binary (`0/1` constants, the TrapGen trapdoor), `χs = χ` = CBD(16) coefficients
  (`B_χ = 16`), `χfl` coefficients uniform below `2^eFl`, `eFl = 400` (flooding).
* **Key boxes**: short parts `Pc = PIdx …` of `|Pc| n ≤ 2^89` coefficients; the big box of
  `Bk = 18750` bits per coefficient (`Big`), the small ball of radius `2^{Bk−1} − 1 − 2^eSh`
  (`Small`), the inner ball of radius `2^{Bk−1} − 1 − 2·2^eSh` (`Inner`), the binary
  decomposition `dec = gadDec`. **Every trapdoor whose shift is within `coverBound = 2^eSh`,
  `eSh = 18500`, is covered** (`covered_of_shift`), and the abort probability is then at most
  `2^{−130}` (`abort_le_of_shift`). The real trapdoor shifts by at most `τ n = 2^40`
  (`realShift_le`), the simulated trapdoor of Lemma 11 by at most `W τ n D^b (B_R̂ + 2)`
  (`simShift`), which is within `coverBound` for every `B_R̂ ≤ 2^eRhat`, `eRhat = 17400`
  (`simShift_le`); Lemma 9's bound with `R* = Z* = 1` gives `B_R̂ ≤ 2^17122`
  (`rhatBound_le`, `rhatClosed_le`).
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices
open scoped ENNReal

/-- **The abort probability of `keyLaw`** (generic): at most `1 − |Inner| / |Big|` for an inner box
whose shifts by the trapdoor stay in the small box. (Stated generically, so that the instances of
`keyLaw` are never re-synthesized at concrete types.) -/
theorem keyLaw_none_le {R : Type*} [CommRing R] [DecidableEq R] {S : Setting R} {Wb J Pos : Type*}
    [Fintype Wb] [Fintype J] (Big Small : Finset (PIdx Wb J S.τ S.E.W → R)) (hBig : Big.Nonempty)
    (dec : (Fin S.E.W → R) → ZIdx S.τ S.E.W → R) (M : HelperMap S J) (mpk : MPK S Wb J Pos)
    (F : BP Pos) (T : (ZIdx S.τ S.E.W → R) → PIdx Wb J S.τ S.E.W → R)
    (Inner : Finset (PIdx Wb J S.τ S.E.W → R)) (hIn : Inner ⊆ Big)
    (hInner : ∀ p ∈ Inner, ∀ y, p - T (dec y) ∈ Small) :
    keyLaw Big Small hBig dec M mpk F T none ≤ ((Big.card - Inner.card : ℕ) : ℝ≥0∞) / Big.card :=
  boxSample_none_le Big hBig Small _ dec T _ Inner hIn hInner

end AdvancedEncryption.ExpLUT

namespace AdvancedEncryption.ExpLUT.Params

open SigabaNeo.Lattices Cslib
open scoped ENNReal

/-! ### Exponents and sizes -/

/-- `K`, with `q = 2^K − 1` (opaque, so that `2^K` is never evaluated). -/
irreducible_def Kc : ℕ := 2 ^ 16
/-- `log₂ n`. -/
abbrev en : ℕ := 24
/-- `b = log₂ W`. -/
abbrev bc : ℕ := 22
/-- The modulus `q = 2^K − 1`. -/
abbrev qc : ℕ := 2 ^ Kc - 1
/-- The number of columns of `Ā`: `m̄ = 3nK + 2·(140 + 64)` (`mbar_lhl`). -/
irreducible_def mbar : ℕ := 3 * (2 ^ en * Kc) + 2 * (140 + 64)
/-- `log₂` of the flooding width. -/
irreducible_def eFl : ℕ := 400
/-- `log₂` of the bound on the shifts of the trapdoors covered by the key boxes. -/
irreducible_def eSh : ℕ := 18500
/-- `log₂` of the bound on the coefficients of `R̂_F` for which Lemma 11's trapdoor is covered. -/
irreducible_def eRhat : ℕ := 17400
/-- The bits of a coefficient of the big box. -/
irreducible_def Bk : ℕ := 18750

/-- `2^α ≤ 2^β` (the base is fixed, so that elaboration never unifies two powers). -/
theorem pow_le_pow' {α β : ℕ} (h : α ≤ β) : 2 ^ α ≤ 2 ^ β := Nat.pow_le_pow_right (by norm_num) h

theorem pow_mul_le' {a b α β γ : ℕ} (ha : a ≤ 2 ^ α) (hb : b ≤ 2 ^ β) (h : α + β = γ) :
    a * b ≤ 2 ^ γ := by
  rw [← h, pow_add]; exact Nat.mul_le_mul ha hb

theorem Kc_le : Kc ≤ 2 ^ 16 := by rw [Kc_def]
theorem one_le_Kc : 1 ≤ Kc := by rw [Kc_def]; norm_num
theorem bc_le_Kc : bc ≤ Kc := by rw [Kc_def]; norm_num

theorem two_le_two_pow_Kc : 2 ≤ 2 ^ Kc :=
  (show 2 = 2 ^ 1 from rfl).le.trans (pow_le_pow' one_le_Kc)

instance : NeZero qc := ⟨by show 2 ^ Kc - 1 ≠ 0; have := two_le_two_pow_Kc; omega⟩

/-- The ring `ℤ_q[X]/(X^n + 1)`. -/
abbrev Rc : Type := Negacyclic (ZMod qc) (2 ^ en)

theorem hwc : (2 : ZMod qc) ^ bc * 2 ^ (Kc - bc) = 1 := two_pow_mul_two_pow_sub_mersenne bc_le_Kc
theorem hnc : 0 < 2 ^ en := by positivity
theorem hWc : 2 ^ bc ∣ 2 ^ en := pow_dvd_pow 2 (by norm_num)
theorem hltc : 2 ^ bc < 2 ^ en := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
theorem h2c : 2 * 2 ^ bc ∣ 2 ^ en := by
  rw [← pow_succ']; exact pow_dvd_pow 2 (by norm_num)
theorem hτc : qc ≤ 2 ^ Kc := Nat.sub_le _ _

/-! ### The setting -/

/-- The ring with automorphisms: `expRingMersenne Kc (2^24) 22`, i.e. `W = 2^22`, `W⁻¹ = 2^(K−22)`. -/
noncomputable abbrev confE : ExpRing Rc := expRingOf (2 ^ en) bc ((2 : ZMod qc) ^ (Kc - bc)) hwc hnc hWc hltc

theorem confE_eq_mersenne : confE = expRingMersenne Kc (2 ^ en) bc bc_le_Kc hnc hWc hltc := rfl

/-- **The setting**: canonical `H`, binary digits, `τ = K`. -/
noncomputable def confS : Setting Rc :=
  canonSetting confE rfl h2c (binaryDigits (2 ^ en) qc Kc hτc) (binaryDigits_g hτc)

/-- **Its norm**: the centered coefficient norm. -/
noncomputable def confN : NormSpec confS := cnormSpec en bc _ hwc hnc hWc hltc h2c hτc

@[simp] theorem confS_τ : confS.τ = Kc := rfl
@[simp] theorem confS_b : confS.b = bc := rfl
@[simp] theorem confS_W : confS.E.W = 2 ^ bc := rfl
@[simp] theorem confS_n : confS.E.n = 2 ^ en := rfl

/-- The norm of `cnormSpec` is `cnorm` (generic: no enumeration of `Fin (2^e)` is possible). -/
theorem cnormSpec_nrm {q : ℕ} [NeZero q] (e b : ℕ) (w : ZMod q) (hw : (2 : ZMod q) ^ b * w = 1)
    (hn : 0 < 2 ^ e) (hW : 2 ^ b ∣ 2 ^ e) (hlt : 2 ^ b < 2 ^ e) (h2 : 2 * 2 ^ b ∣ 2 ^ e) {τ : ℕ}
    (hτ : q ≤ 2 ^ τ) (a : Negacyclic (ZMod q) (2 ^ e)) :
    (cnormSpec e b w hw hn hW hlt h2 hτ).nrm a = cnorm a := rfl

theorem confN_nrm (a : Rc) : confN.nrm a = cnorm a := cnormSpec_nrm _ _ _ _ _ _ _ _ _ a

theorem confS_gfac : confS.gfac = 2 * Kc * 2 ^ en := rfl

theorem gfac_le : confS.gfac ≤ 2 ^ 41 := by
  rw [confS_gfac, Kc_def]; norm_num

theorem two_le_gfac : 2 ≤ confS.gfac := by
  rw [confS_gfac]
  have := one_le_Kc
  have h : 1 ≤ 2 ^ en := Nat.one_le_two_pow
  calc 2 = 2 * 1 * 1 := by norm_num
    _ ≤ 2 * Kc * 2 ^ en := Nat.mul_le_mul (Nat.mul_le_mul_left _ this) h

/-! ### The helpers `J = K ∪ K⁻¹` -/

/-- The helper indices: `g_t` (`t < 22`) and `g_t^{-1}` (`t < 21`). -/
abbrev Jc : Type := Fin bc ⊕ Fin (bc - 1)

/-- **The helpers** `K ∪ K⁻¹`: `je (inl t) = 2^t`, `je (inr t) = W − 2^t`; the inverse of
`g_{21} = g^{W/2}` is itself. -/
def helperJ : HelperMap confS Jc where
  je := Sum.elim (fun t => 2 ^ (t : ℕ)) (fun t => 2 ^ bc - 2 ^ (t : ℕ))
  fwd t := .inl t
  inv t := if h : (t : ℕ) < bc - 1 then .inr ⟨t, h⟩ else .inl t
  je_fwd _ := rfl
  je_inv t := by
    by_cases h : (t : ℕ) < bc - 1
    · simp only [h, dite_true, Sum.elim_inr]; rfl
    · simp only [h, dite_false]
      have ht : (t : ℕ) = 21 := by
        have : (t : ℕ) < 22 := t.isLt
        have hb : bc = 22 := rfl
        omega
      show 2 ^ (t : ℕ) = 2 ^ bc - 2 ^ (t : ℕ)
      rw [ht]; norm_num

theorem card_Jc : Fintype.card Jc = 43 := by simp

/-! ### `m̄` and the leftover hash lemma -/

/-- The columns of `Ā`. -/
abbrev Wbc : Type := Fin mbar

/-- `|ℤ_q[X]/(X^n + 1)| ≤ 2^{Kn}` for `q ≤ 2^K` (generic). -/
theorem card_negacyclic_le {q : ℕ} [NeZero q] (n K : ℕ) (hq : q ≤ 2 ^ K) :
    Fintype.card (Negacyclic (ZMod q) n) ≤ 2 ^ (K * n) := by
  rw [Fintype.card_congr (Negacyclic.coeffsEquiv (R := ZMod q) (n := n)), Fintype.card_fun,
    ZMod.card, Fintype.card_fin, pow_mul]
  exact Nat.pow_le_pow_left hq _

/-- `|R| ≤ 2^{Kn}`. -/
theorem card_Rc_le : Fintype.card Rc ≤ 2 ^ (Kc * 2 ^ en) := card_negacyclic_le _ _ hτc

/-- `c ≤ 2^{Kn}` gives `c³ ≤ 2^{3nK}` (generic in `c`, so that no cardinality is unfolded). -/
theorem cube_le {c K n : ℕ} (h : c ≤ 2 ^ (K * n)) : c ^ 3 ≤ 2 ^ (3 * (n * K)) :=
  calc c ^ 3 ≤ (2 ^ (K * n)) ^ 3 := Nat.pow_le_pow_left h 3
    _ = 2 ^ (3 * (n * K)) := by rw [← pow_mul, Nat.mul_comm (K * n) 3, Nat.mul_comm K]

/-- **Why `m̄ = 3nK + 408`.** In hybrid H5 the programmed columns `B⁽¹⁾ r` (`r` binary on the `Ā`
columns, `2^{m̄}` values) are hashed by the 3-row seed `(B; b)` into `R³`, of size at most
`2^{3nK}` (`card_Rc_le`). The leftover hash lemma (`isTwoUniversal_binaryHash`) gives a distance of
at most `½ √(|R|³ / 2^{m̄}) ≤ 2^{−205}` per column; there are fewer than `2^{57}` programmed
columns (`2τ` of `R₀`, `16 · 2τ` of the `a_t`, `16 · 8τ³` of `A^in`, `22 · 8τ³` of `A^aut`,
one of `d`), so the total is below `2^{−148}`. (H3′, with the seed `Ā` alone, needs only
`m̄ ≥ nK + …`.) Exactly: `m̄ = 3 · (nK) + 2 · (140 + 64)`, with `|R³| ≤ 2^{3nK}`. -/
theorem mbar_lhl :
    mbar = 3 * (2 ^ en * Kc) + 2 * (140 + 64) ∧ Fintype.card Rc ^ 3 ≤ 2 ^ (3 * (2 ^ en * Kc)) := by
  exact ⟨mbar_def, cube_le card_Rc_le⟩

/-- The number of programmed columns (H1/H5): `2τ` (`R₀`), `16 · 2τ` (`a_t`), `(16 + 22) · 8τ³`
(`A^in`, `A^aut`) and `1` (`d`), for `16` attribute positions. -/
def lhlCols : ℕ := 2 * Kc + 16 * (2 * Kc) + (16 + bc) * (8 * Kc ^ 3) + 1

theorem lhlCols_le : lhlCols ≤ 2 ^ 57 := by
  have hK := Kc_le
  have h3 : Kc ^ 3 ≤ (2 ^ 16) ^ 3 := Nat.pow_le_pow_left hK 3
  unfold lhlCols
  have : (16 + bc) * (8 * Kc ^ 3) ≤ 38 * (8 * (2 ^ 16) ^ 3) := by
    simp only [bc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
  norm_num at this ⊢
  omega

theorem mbar_le_gen {k : ℕ} (hk : k ≤ 2 ^ 16) : 3 * (2 ^ en * k) + 2 * (140 + 64) + k ≤ 2 ^ 42 := by
  have h := Nat.mul_le_mul_left (2 ^ en) hk
  norm_num at h ⊢
  omega

theorem mbar_le : mbar + Kc ≤ 2 ^ 42 := by
  rw [mbar_def]; exact mbar_le_gen Kc_le

/-! ### The coin laws -/

/-- **The trapdoor law** `χT`: the constants `0` and `1`, uniform. -/
noncomputable def χT : PMF Rc := (Cslib.Probability.PMF.uniformOfFintype Bool).map fun b => if b then 1 else 0

/-- The CBD(16) law of a coefficient. -/
noncomputable def cbdCoef : PMF (ZMod qc) := ModuleLWE.coeffLaw qc (SecretDist.cbd 16)

/-- A ring element with independent coefficients from `c`. -/
noncomputable def ringLaw (c : PMF (ZMod qc)) : PMF Rc :=
  (Cslib.Probability.PMF.pi fun _ : Fin (2 ^ en) => c).map Negacyclic.ofCoeffs

/-- **The secret and error law** `χs = χ`: CBD(16) coefficients (as the strength certificate). -/
noncomputable def χc : PMF Rc := ringLaw cbdCoef

instance : NeZero (2 ^ eFl) := ⟨pow_ne_zero _ two_ne_zero⟩

/-- **The flooding law** `χfl`: coefficients uniform in `{0, …, 2^eFl − 1}` (`floodLaw` entrywise). -/
noncomputable def χfl : PMF Rc :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin (2 ^ en) → Fin (2 ^ eFl))).map fun T =>
    Negacyclic.ofCoeffs fun j => ((T j : ℕ) : ZMod qc)

/-- The bound `B_χ = 16`. -/
abbrev Bχ : ℕ := 16
/-- The bound `B_fl = 2^eFl`. -/
abbrev Bfl : ℕ := 2 ^ eFl

theorem χT_short : ∀ a ∈ χT.support, cnorm a ≤ 1 := by
  intro a ha
  simp only [χT, PMF.mem_support_map_iff] at ha
  obtain ⟨b, -, rfl⟩ := ha
  cases b
  · simp [cnorm_zero]
  · rw [cnorm_le_iff]; intro j
    show zabs ((1 : Rc).coeffs j) ≤ 1
    change zabs (if (j : ℕ) = 0 then (1 : ZMod qc) else 0) ≤ 1
    split_ifs
    · exact zabs_one_le
    · simp [zabs_zero]

theorem cbdCoef_short : ∀ e ∈ cbdCoef.support, zabs e ≤ 16 := by
  intro e he
  simp only [cbdCoef, ModuleLWE.coeffLaw, PMF.mem_support_map_iff] at he
  obtain ⟨ab, -, rfl⟩ := he
  rw [← Int.cast_sub]
  refine (zabs_intCast_le (q := qc) _).trans ?_
  have h1 := Finset.card_le_univ (Finset.univ.filter fun i => ab.1 i)
  have h2 := Finset.card_le_univ (Finset.univ.filter fun i => ab.2 i)
  simp only [Fintype.card_fin] at h1 h2
  omega

theorem ringLaw_short {c : PMF (ZMod qc)} {B : ℕ} (hc : ∀ e ∈ c.support, zabs e ≤ B) :
    ∀ a ∈ (ringLaw c).support, cnorm a ≤ B := by
  intro a ha
  simp only [ringLaw, PMF.mem_support_map_iff] at ha
  obtain ⟨v, hv, rfl⟩ := ha
  rw [cnorm_le_iff]; intro j
  exact hc _ ((Cslib.Probability.PMF.mem_support_pi_iff _ v).mp hv j)

theorem χc_short : ∀ a ∈ χc.support, cnorm a ≤ Bχ := ringLaw_short cbdCoef_short

theorem χfl_short : ∀ a ∈ χfl.support, cnorm a ≤ Bfl := by
  intro a ha
  simp only [χfl, PMF.mem_support_map_iff] at ha
  obtain ⟨T, -, rfl⟩ := ha
  rw [cnorm_le_iff]; intro j
  rw [Negacyclic.coeffs_ofCoeffs, ← Int.cast_natCast]
  refine (zabs_intCast_le (q := qc) ((T j : ℕ) : ℤ)).trans ?_
  rw [Int.natAbs_natCast]
  exact (T j).isLt.le

/-! ### Sizes of keys -/

/-- The short coordinates of a key. -/
abbrev Pc : Type := PIdx Wbc Jc confS.τ confS.E.W

/-- The gadget coordinates of a key. -/
abbrev Zc : Type := ZIdx confS.τ confS.E.W

/-- The coordinates of a key. -/
abbrev KColc : Type := KCol Wbc Jc confS.τ confS.E.W

theorem card_Pc : Fintype.card Pc = 2 ^ bc * mbar + (2 ^ bc * (43 * (2 * Kc)) + 2 * Kc) := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  rw [confS_W, confS_τ, show bc + (bc - 1) = 43 from rfl]

theorem card_KColc :
    Fintype.card KColc = 2 ^ bc * (mbar + Kc) + (2 ^ bc * (43 * (2 * Kc)) + 2 * Kc) := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  rw [confS_W, confS_τ, show bc + (bc - 1) = 43 from rfl]

theorem card_gen_le {m k : ℕ} (hm : m + k ≤ 2 ^ 42) (hk : k ≤ 2 ^ 16) :
    2 ^ bc * (m + k) + (2 ^ bc * (43 * (2 * k)) + 2 * k) ≤ 2 ^ 65 := by
  have h1 := Nat.mul_le_mul_left (2 ^ bc) hm
  have h2 := Nat.mul_le_mul_left (2 ^ bc) (Nat.mul_le_mul_left 86 hk)
  have e : 43 * (2 * k) = 86 * k := by ring
  rw [e]
  norm_num at h1 h2 ⊢
  omega

/-- `|KCol| ≤ 2^65` ring elements in a key. -/
theorem card_KColc_le : Fintype.card KColc ≤ 2 ^ 65 := by
  rw [card_KColc]; exact card_gen_le mbar_le Kc_le

/-- `|Pc| n ≤ 2^89` coefficients in the short part of a key. -/
theorem card_Pc_le : Fintype.card Pc * 2 ^ en ≤ 2 ^ 89 := by
  have h : Fintype.card Pc ≤ 2 ^ 65 := by
    rw [card_Pc]
    refine le_trans ?_ (card_gen_le mbar_le Kc_le)
    have := Nat.mul_le_mul_left (2 ^ bc) (Nat.le_add_right mbar Kc)
    omega
  calc Fintype.card Pc * 2 ^ en ≤ 2 ^ 65 * 2 ^ 24 := Nat.mul_le_mul_right _ h
    _ = 2 ^ 89 := by norm_num

/-! ### Key boxes -/

theorem Bk_lt_Kc : Bk < Kc := by rw [Bk_def, Kc_def]; norm_num

theorem hBk : 2 ^ Bk ≤ qc := by
  have := Nat.pow_lt_pow_right (a := 2) (by norm_num) Bk_lt_Kc
  show 2 ^ Bk ≤ 2 ^ Kc - 1
  omega

theorem one_le_Bk : 1 ≤ Bk := by rw [Bk_def]; norm_num

/-- **The cover bound**: every trapdoor whose shifts have coefficients within `2^eSh` is covered by
the boxes, with abort probability at most `2^{−130}`. -/
abbrev coverBound : ℕ := 2 ^ eSh

/-- **The big box**: `Bk` fair bits per coefficient of the short part (opaque: membership in it is
never unfolded by the elaborator). -/
noncomputable irreducible_def Big : Finset (Pc → Rc) := famBig qc (2 ^ en) Pc Bk hBk

/-- **The small box**: coefficients within `2^{Bk−1} − 1 − 2^eSh`. -/
noncomputable irreducible_def Small : Finset (Pc → Rc) := famBall qc (2 ^ en) Pc (2 ^ (Bk - 1) - 1 - coverBound)

/-- The inner box (for the abort probability): coefficients within `2^{Bk−1} − 1 − 2 · 2^eSh`. -/
noncomputable irreducible_def Inner : Finset (Pc → Rc) :=
  famBall qc (2 ^ en) Pc (2 ^ (Bk - 1) - 1 - 2 * coverBound)

theorem hBig : Big.Nonempty := nonempty_of_eq_famBig Big_def

/-- **The decomposition** of key generation: `dec = (I_W ⊗ g)⁻¹`, binary digits. -/
noncomputable def decc : (Fin confS.E.W → Rc) → Zc → Rc := gadDec (S := confS)

theorem hdecc (y : Fin confS.E.W → Rc) : gadZ (decc y) = y := gadZ_gadDec y

theorem decc_short (y : Fin confS.E.W → Rc) (ic : Zc) : cnorm (decc y ic) ≤ 1 := by
  rw [← confN_nrm]; exact confN.nrm_digit _ _

theorem eSh_lt_Bk : eSh + 3 ≤ Bk - 1 := by rw [eSh_def, Bk_def]; norm_num

/-- `2τ + 2 ≤ 2^{Bk−1}` for `τ = 2^eSh`. -/
theorem two_cover_le : 2 * coverBound + 2 ≤ 2 ^ (Bk - 1) := by
  have h : 2 ^ (eSh + 3) ≤ 2 ^ (Bk - 1) := pow_le_pow' eSh_lt_Bk
  have e : 2 ^ (eSh + 3) = 8 * 2 ^ eSh := by rw [pow_add]; ring
  have : 1 ≤ 2 ^ eSh := Nat.one_le_two_pow
  show 2 * 2 ^ eSh + 2 ≤ 2 ^ (Bk - 1)
  omega

/-- The box arithmetic, with the large numbers as variables. -/
theorem box_arith (M τ : ℕ) (h : 2 * τ + 2 ≤ M) :
    M - 1 - 2 * τ ≤ M - 1 ∧ M - 1 - τ + τ ≤ M - 1 ∧ M - 1 - 2 * τ + τ ≤ M - 1 - τ ∧
      M - 1 - τ ≤ M := by
  omega

/-- The box arithmetic at `M = 2^{Bk−1}`, `τ = coverBound`. -/
theorem boxFacts :
    2 ^ (Bk - 1) - 1 - 2 * coverBound ≤ 2 ^ (Bk - 1) - 1 ∧
      2 ^ (Bk - 1) - 1 - coverBound + coverBound ≤ 2 ^ (Bk - 1) - 1 ∧
      2 ^ (Bk - 1) - 1 - 2 * coverBound + coverBound ≤ 2 ^ (Bk - 1) - 1 - coverBound ∧
      2 ^ (Bk - 1) - 1 - coverBound ≤ 2 ^ (Bk - 1) :=
  box_arith (2 ^ (Bk - 1)) coverBound two_cover_le

theorem mem_Small (v : Pc → Rc) :
    v ∈ Small ↔ ∀ p, cnorm (v p) ≤ 2 ^ (Bk - 1) - 1 - coverBound :=
  mem_of_eq_famBall Small_def v

theorem Small_short (v : Pc → Rc) (hv : v ∈ Small) (p : Pc) : cnorm (v p) ≤ 2 ^ (Bk - 1) :=
  le_trans ((mem_Small v).mp hv p) boxFacts.2.2.2

/-- **Coverage**: a trapdoor shifting by at most `coverBound` maps the small box into the big box. -/
theorem covered_of_shift (T : (Zc → Rc) → Pc → Rc) (hT : ∀ y p, cnorm (T (decc y) p) ≤ coverBound) :
    ∀ x ∈ Small, ∀ y, x + T (decc y) ∈ Big := fun x hx y =>
  add_mem_of_eq Small_def Big_def one_le_Bk boxFacts.2.1 (hT y) x hx

theorem inner_sub_big : Inner ⊆ Big :=
  @subset_of_eq qc (2 ^ en) _ Pc _ _ Inner Big (2 ^ (Bk - 1) - 1 - 2 * coverBound) Bk hBk Inner_def
    Big_def one_le_Bk boxFacts.1

theorem inner_of_shift (T : (Zc → Rc) → Pc → Rc) (hT : ∀ y p, cnorm (T (decc y) p) ≤ coverBound) :
    ∀ p ∈ Inner, ∀ y, p - T (decc y) ∈ Small := fun p hp y =>
  sub_mem_of_eq Inner_def Small_def boxFacts.2.2.1 (hT y) p hp

theorem four_cover_le : 4 * coverBound + 1 ≤ 2 ^ (eSh + 3) := by
  have e : 2 ^ (eSh + 3) = 8 * 2 ^ eSh := by rw [pow_add]; ring
  have : 1 ≤ 2 ^ eSh := Nat.one_le_two_pow
  show 4 * 2 ^ eSh + 1 ≤ 2 ^ (eSh + 3)
  omega

theorem abort_prod : Fintype.card Pc * 2 ^ en * (4 * coverBound + 1) * 2 ^ 130 ≤ 2 ^ Bk := by
  calc Fintype.card Pc * 2 ^ en * (4 * coverBound + 1) * 2 ^ 130
      ≤ 2 ^ 89 * 2 ^ (eSh + 3) * 2 ^ 130 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul card_Pc_le four_cover_le)
    _ = 2 ^ (89 + (eSh + 3) + 130) := by rw [pow_add 2 (89 + (eSh + 3)) 130, pow_add 2 89 (eSh + 3)]
    _ ≤ 2 ^ Bk := pow_le_pow' (by rw [eSh_def, Bk_def]; norm_num)

/-- **The abort probability** of one try of key generation, for every trapdoor shifting by at most
`coverBound`: at most `2^{−130}`. -/
theorem abort_le_of_shift (M : HelperMap confS Jc) {Pos : Type} (mpk : MPK confS Wbc Jc Pos)
    (F : BP Pos) (T : (Zc → Rc) → Pc → Rc) (hT : ∀ y p, cnorm (T (decc y) p) ≤ coverBound) :
    keyLaw Big Small hBig decc M mpk F T none ≤ ((2 : ℝ≥0∞) ^ 130)⁻¹ := by
  refine le_trans (keyLaw_none_le Big Small hBig decc M mpk F T Inner inner_sub_big
    (inner_of_shift T hT)) ?_
  have h4 : 4 * coverBound + 1 ≤ 2 ^ Bk :=
    four_cover_le.trans (pow_le_pow' (by rw [eSh_def, Bk_def]; norm_num))
  exact @abort_of_eq qc (2 ^ en) _ Pc _ _ Inner Big Bk coverBound 130 hBk Inner_def Big_def
    one_le_Bk h4 abort_prod

/-- **The real trapdoor shifts by at most `τ n = 2^40`** for a binary `T` (`χT`). -/
theorem realShift_le (T : Matrix Wbc (Fin confS.τ) Rc) (hT : ∀ w c, cnorm (T w c) ≤ 1)
    (y : Fin confS.E.W → Rc) (p : Pc) : cnorm (realTrap (J := Jc) T (decc y) p) ≤ coverBound := by
  have h := rowBnd_realTrap (J := Jc) confN T 1 (fun w c => by rw [confN_nrm]; exact hT w c)
    (decc y) (fun ic => by rw [confN_nrm]; exact decc_short y ic) p
  rw [confN_nrm, confS_τ, confS_n] at h
  refine h.trans ?_
  calc Kc * (2 ^ en * 1) ≤ 2 ^ 16 * 2 ^ 24 := by rw [mul_one]; exact Nat.mul_le_mul_right _ Kc_le
    _ = 2 ^ 40 := by norm_num
    _ ≤ 2 ^ eSh := pow_le_pow' (by rw [eSh_def]; norm_num)

/-- The real trapdoor is covered. -/
theorem realTrap_covered (T : Matrix Wbc (Fin confS.τ) Rc) (hT : ∀ w c, cnorm (T w c) ≤ 1) :
    ∀ x ∈ Small, ∀ y, x + realTrap (J := Jc) T (decc y) ∈ Big :=
  covered_of_shift _ fun y p => realShift_le T hT y p

end AdvancedEncryption.ExpLUT.Params
