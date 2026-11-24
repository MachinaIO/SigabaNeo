import PE.Impl.ExpLUT.Prog.Samplers
import PE.Impl.DualUse.Prog.Chi
import PE.Impl.DualUse.Prog.SetupLaws

/-!
# The samplers of `Enc`: centered binomial and flooding ring elements

Ring elements with independent coefficients (`ringLawD D c`), written as their canonical words
(`rEnc`, `N` blocks of `K` bits): the word is the concatenation of the canonical `K`-bit words of
the coefficients (`rEnc_ofCoeffs`), so `n` independent elements are `n N` independent coefficient
words (`ringLawD_enc`). The samplers are coefficient samplers repeated `N` times (`repF`, counter
tapes `5`, `6`; scratch `2 … 6` blank before and after: `P5`).

* **Flooding** `floodR D e` (coefficients uniform below `2^e`, `e < K`; package P's `χfl` at
  `Dc` with `e = eFl`): `floodP D e = repF N (entF K e)` (`e` fair bits, then `K − e` zeros;
  DualUse's `entF`), **`law_floodP`**.
* **Centered binomial** `cbdR D η` (package P's `χc` at `Dc`, `η = 16`): the coefficient sampler
  `cbdPM η L K` is DualUse's `cbdP` (coins, unary value, a chain of tests) whose leaves append the
  *one's-complement* word: for `v < 0` the canonical word of `v` modulo `2^K − 1` is the two's
  complement word of `v − 1` (`encM_eq_zmodEnc`), so the leaf of `v` is DualUse's leaf of
  `mv v = v − [v < 0]`. **`law_cbdPM`**, `cbdP D η L = repF N (cbdPM η L K)`, **`law_cbdRP`**.
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.XProg Cslib Cslib.Probability
open AdvancedEncryption.DualUse.Prog

/-! ### Words of coefficients -/

theorem toBits_eq_map : ∀ (K n : ℕ), toBits K n = (List.finRange K).map fun i => n.testBit i.val
  | 0, _ => rfl
  | K + 1, n => by
    rw [toBits, toBits_eq_map K (n / 2), List.finRange_succ, List.map_cons, List.map_map]
    congr 1
    · simp [Nat.testBit_zero]
    · refine List.map_congr_left fun i _ => ?_
      simp [Function.comp, Nat.testBit_succ]

theorem concatN_finRange : ∀ (n : ℕ) (g : ℕ → List Bool),
    concatN n g = (List.finRange n).flatMap fun i => g i.val
  | 0, _ => rfl
  | n + 1, g => by
    rw [concatN, concatN_finRange n g, List.finRange_succ_last, List.flatMap_append,
      List.flatMap_map]
    simp

variable (D : Dims)

/-- **The canonical word of a ring element with coefficients `c`** is the concatenation of the
canonical words of the coefficients. -/
theorem rEnc_ofCoeffs (c : Fin D.N → ZMod D.q) :
    (rEnc D).enc (Negacyclic.ofCoeffs c) = ((Enum.list (α := Fin D.N)).map c).flatMap (encM D.K) := by
  rw [rEnc_enc, encRM, concatN_finRange, List.flatMap_map]
  show _ = (List.finRange D.N).flatMap _
  refine List.flatMap_congr fun i _ => ?_
  rw [NegaG.coefG_of_lt _ i.isLt]

/-- A ring element with independent coefficients from `c`. -/
noncomputable def ringLawD (c : PMF (ZMod D.q)) : PMF (Rg D) :=
  (Cslib.Probability.PMF.pi fun _ : Fin D.N => c).map Negacyclic.ofCoeffs

/-- **Independent coefficients**: `N` independent coefficient words. -/
theorem ringLawD_enc (c : PMF (ZMod D.q)) :
    (ringLawD D c).map (rEnc D).enc = catPow (c.map (encM D.K)) D.N := by
  rw [ringLawD, PMF.map_comp]
  have h := pi_map_flatMap (α := Fin D.N) c (encM D.K)
  rw [len_fin] at h
  rw [← h]
  congr 1
  funext T
  exact rEnc_ofCoeffs D T

/-! ### Flooding -/

/-- **The flooding law**: coefficients uniform below `2^e`. -/
noncomputable def floodR (e : ℕ) : PMF (Rg D) :=
  (PMF.uniformOfFintype (Fin D.N → Fin (2 ^ e))).map fun T =>
    Negacyclic.ofCoeffs fun j => ((T j : ℕ) : ZMod D.q)

theorem pow_lt_q {e : ℕ} (he : e < D.K) : 2 ^ e < D.q := by
  have hK := D.hK
  have h1 : 2 ^ e ≤ 2 ^ (D.K - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ D.K = 2 * 2 ^ (D.K - 1) := by rw [← pow_succ']; congr 1; omega
  have h3 : 2 ≤ 2 ^ (D.K - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (D.K - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [Dims.q]; omega

/-- The coefficient of a flooding sample. -/
def flC (e : ℕ) (t : Fin (2 ^ e)) : ZMod D.q := ((t.val : ℕ) : ZMod D.q)

/-- The canonical word of a flooding coefficient is its word modulo `2^K`. -/
theorem encM_flood {e : ℕ} (he : e < D.K) (t : Fin (2 ^ e)) :
    encM D.K (flC D e t) = gF D.K e t := by
  have hq := pow_lt_q D he
  have hK : 2 ^ e ≤ 2 ^ D.K := Nat.pow_le_pow_right (by norm_num) he.le
  have : NeZero (2 ^ D.K) := ⟨by positivity⟩
  rw [flC, encM, gF, ZMod.val_natCast, Nat.mod_eq_of_lt (t.isLt.trans hq), toBits_eq_map]
  show _ = (List.finRange D.K).map fun i => (((t : ℕ) : ZMod (2 ^ D.K)).val).testBit i.val
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_of_lt_of_le t.isLt hK)]

theorem floodR_eq (e : ℕ) :
    floodR D e = ringLawD D ((PMF.uniformOfFintype (Fin (2 ^ e))).map (flC D e)) := by
  rw [floodR, ringLawD, ← Cslib.Probability.PMF.pi_uniformOfFintype,
    show (Cslib.Probability.PMF.pi fun _ : Fin D.N =>
      (PMF.uniformOfFintype (Fin (2 ^ e))).map (flC D e)) =
      (Cslib.Probability.PMF.pi fun _ : Fin D.N => PMF.uniformOfFintype (Fin (2 ^ e))).map
        (fun T i => flC D e (T i)) from (Cslib.Probability.PMF.pi_map
          (fun _ : Fin D.N => PMF.uniformOfFintype (Fin (2 ^ e))) (fun _ : Fin D.N => flC D e)),
    PMF.map_comp]
  rfl

/-- The flooding sampler: `N` coefficients of `e` fair bits and `K − e` zeros. -/
def floodP (e : ℕ) : XProg 7 := repF D.N (entF D.K e)

/-- **The law of the flooding sampler.** -/
theorem law_floodP {e : ℕ} (he : e < D.K) :
    AppendLaw (floodP D e) 0 P5 ((floodR D e).map (rEnc D).enc) := by
  rw [floodR_eq, ringLawD_enc, PMF.map_comp]
  have h : (encM D.K ∘ flC D e) = gF D.K e := funext (encM_flood D he)
  rw [h, coefF_eq]
  exact law_repF (law_entF e) D.N

/-! ### Centered binomial -/

/-- The value of the leaf of `v`: `v − 1` for `v < 0`, so DualUse's two's-complement leaf writes
the canonical word modulo `2^K − 1`. -/
def mv (v : ℤ) : ℤ := if v < 0 then v - 1 else v

/-- The chain of tests with one's-complement leaves. -/
def chainPM (K L η : ℕ) : ℕ → ℕ → XProg 7
  | 0, j => leafP K L (mv ((j : ℤ) - η))
  | f + 1, j => ifBlank 3 (leafP K L (mv ((j : ℤ) - η)))
      (seq (prog (.prim (.tail 3))) (chainPM K L η f (j + 1)))

theorem law_chainPM (K L η : ℕ) : ∀ (f j m : ℕ) (s : Store 7), m ≤ f →
    s 3 = List.replicate m true → s 4 = [] → (chainPM K L η f j).law s =
      PMF.pure (Function.update (Function.update s 3 []) 0
        (s 0 ++ leafW K L (mv ((j + m : ℕ) - η))))
  | 0, j, m, s, hm, h3, h4 => by
    obtain rfl : m = 0 := by omega
    rw [chainPM, law_leafP K L _ s h4]; simp
  | f + 1, j, m, s, hm, h3, h4 => by
    rw [chainPM, XProg.law_ifBlank]
    rcases m with _ | m
    · rw [if_pos (by simp [h3]), law_leafP K L _ s h4]; simp
    · rw [if_neg (by simp [h3]), law_seq, law_prim, PMF.pure_bind,
        law_chainPM K L η f (j + 1) m _ (by omega) (by simp [Prim.apply, h3])
          (by simp [Prim.apply, h4])]
      congr 1
      funext t
      by_cases t0 : t = 0
      · subst t0; simp [Prim.apply, Nat.add_right_comm j 1 m, Nat.add_assoc]
      · by_cases t3 : t = 3
        · subst t3; simp [Prim.apply]
        · simp [Prim.apply, t0, t3]

/-- **The centered binomial coefficient sampler** modulo `2^K − 1` (canonical words). -/
def cbdPM (η L K : ℕ) : XProg 7 :=
  seq (repX (coinAp 2 4) (η + η)) (seq (repX (bitAp 3 true) η) (seq (repX upStep η)
    (seq (repX downStep η) (chainPM K L η (η + η) 0))))

/-- The centered binomial value of the coins `l`. -/
def cbdV (η : ℕ) (l : List Bool) : ℤ :=
  ((η + (l.take η).count true - (l.drop η).count true : ℕ) : ℤ) - η

theorem law_cbdPM_det (η L K : ℕ) (s : Store 7) (l : List Bool) (hl : l.length = η + η)
    (h2 : s 2 = l) (h3 : s 3 = []) (h4 : s 4 = []) :
    (seq (repX (bitAp 3 true) η) (seq (repX upStep η)
      (seq (repX downStep η) (chainPM K L η (η + η) 0)))).law s =
      PMF.pure (Function.update (Function.update s 2 []) 0 (s 0 ++ leafW K L (mv (cbdV η l)))) := by
  have hb := AppendLaw.repX (appendLaw_bitAp (k := 7) 3 true (fun _ => True)) (fun _ _ _ => trivial) η
  have hcat : catPow (PMF.pure [true]) η = PMF.pure (List.replicate η true) := by
    clear hb hl; induction η with
    | zero => rfl
    | succ m ih => rw [catPow_succ, ih, PMF.pure_bind, PMF.pure_map, List.replicate_succ']
  rw [law_seq, hb s trivial, hcat, PMF.pure_map, PMF.pure_bind, law_seq,
    law_upSteps η l η _ (by simp [h2]) (by simp [h3]), PMF.pure_bind, law_seq,
    law_downSteps η (l.drop η) (η + (l.take η).count true) _ (by simp) (by simp), PMF.pure_bind]
  have hb2 : (l.drop η).take η = l.drop η := List.take_of_length_le (by simp [hl])
  have hdd : (l.drop η).drop η = [] := List.drop_eq_nil_of_le (by simp [hl])
  have hc : ((l.drop η).count true) ≤ η := by
    have := List.count_le_length (a := true) (l := l.drop η); simp [hl] at this; omega
  have ha : ((l.take η).count true) ≤ η := by
    have := List.count_le_length (a := true) (l := l.take η); simp [hl] at this; omega
  rw [law_chainPM K L η (η + η) 0 (η + (l.take η).count true - (l.drop η).count true) _
    (by omega) (by simp [hb2]) (by simp [h4])]
  congr 1
  funext t
  by_cases t0 : t = 0
  · subst t0; simp [cbdV, hb2]
  · by_cases t2 : t = 2
    · subst t2; simp [hdd]
    · by_cases t3 : t = 3
      · subst t3; simp [h3]
      · simp [t0, t2, t3]

/-- The coins of the sampler give the centered binomial residue, for any modulus. -/
theorem uniformList_cbdM (η q : ℕ) [NeZero q] :
    (BitString.uniformList (η + η)).map (fun l => ((cbdV η l : ℤ) : ZMod q)) =
      ModuleLWE.coeffLaw q (.cbd η) := by
  let e : (Fin (η + η) → Bool) ≃ (Fin η → Bool) × (Fin η → Bool) :=
    (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
      (Equiv.sumArrowEquivProdArrow _ _ _)
  rw [ModuleLWE.coeffLaw, ← Cslib.Probability.PMF.uniformOfFintype_map_equiv e, PMF.map_comp,
    BitString.uniformList, PMF.map_comp]
  congr 1
  funext f
  have hcount : ∀ {n : ℕ} (g : Fin n → Bool),
      (List.ofFn g).count true = (Finset.univ.filter fun i => g i = true).card := by
    intro n g
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.ofFn_succ, List.count_cons, ih, Finset.card_filter, Finset.card_filter,
        Fin.sum_univ_succ]
      cases g 0 <;> simp [Nat.add_comm]
  have hsplit := List.ofFn_add (f := f)
  have hlen1 : (List.ofFn fun i : Fin η => f (Fin.castAdd η i)).length = η := List.length_ofFn
  have htake : (List.ofFn f).take η = List.ofFn fun i : Fin η => f (Fin.castAdd η i) := by
    rw [hsplit]; exact List.take_left' hlen1
  have hdrop : (List.ofFn f).drop η = List.ofFn fun i : Fin η => f (Fin.natAdd η i) := by
    rw [hsplit]; exact List.drop_left' hlen1
  have hc2 : ((List.ofFn f).drop η).count true ≤ η := by
    have := List.count_le_length (a := true) (l := (List.ofFn f).drop η); simpa using this
  simp only [Function.comp_apply, cbdV]
  rw [Nat.cast_sub (by omega), Nat.cast_add, htake, hdrop, hcount, hcount]
  simp only [e, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.sumArrowEquivProdArrow_apply_fst,
    Equiv.sumArrowEquivProdArrow_apply_snd, Function.comp_apply, Equiv.refl_apply,
    Equiv.symm_symm, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  push_cast
  ring

theorem cbdV_bounds (η : ℕ) (l : List Bool) (hl : l.length = η + η) :
    -(η : ℤ) ≤ cbdV η l ∧ cbdV η l ≤ η := by
  have ha : (l.take η).count true ≤ η :=
    (List.count_le_length (a := true) (l := l.take η)).trans (by simp)
  have hc : (l.drop η).count true ≤ η :=
    (List.count_le_length (a := true) (l := l.drop η)).trans (by simp [hl])
  unfold cbdV
  constructor <;> push_cast [Nat.cast_sub (show (l.drop η).count true ≤
    η + (l.take η).count true by omega)] <;> omega

/-- **One's complement from two's complement**: for small `v`, the canonical word of `v` modulo
`2^K − 1` is the word of `mv v` modulo `2^K`. -/
theorem encM_eq_zmodEnc {K : ℕ} (hK : 2 ≤ K) (v : ℤ) (h1 : -(2 : ℤ) ^ (K - 1) ≤ v)
    (h2 : v < 2 ^ (K - 1)) :
    encM K ((v : ℤ) : ZMod (2 ^ K - 1)) = (zmodEnc K).enc ((mv v : ℤ) : ZMod (2 ^ K)) := by
  have hpos : (2 : ℤ) ^ K = 2 * 2 ^ (K - 1) := by rw [← pow_succ']; congr 1; omega
  have hq : (1 : ℤ) < 2 ^ K - 1 := by
    have : (2 : ℤ) ≤ 2 ^ (K - 1) := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (K - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    omega
  have : NeZero (2 ^ K - 1) := ⟨by have : 2 ≤ 2 ^ K := Nat.le_self_pow (by omega) 2; omega⟩
  have : NeZero (2 ^ K) := ⟨by positivity⟩
  rw [encM, toBits_eq_map]
  show _ = (List.finRange K).map fun i => (((mv v : ℤ) : ZMod (2 ^ K)).val).testBit i.val
  congr 2
  funext i
  congr 1
  have e1 := ZMod.val_intCast (n := 2 ^ K - 1) v
  have e2 := ZMod.val_intCast (n := 2 ^ K) (mv v)
  have hq' : ((2 ^ K - 1 : ℕ) : ℤ) = 2 ^ K - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
  rw [hq'] at e1
  push_cast at e2
  apply Nat.cast_injective (R := ℤ)
  rw [e1, e2]
  unfold mv
  split_ifs with hv
  · rw [show v % (2 ^ K - 1) = v + (2 ^ K - 1) by
      rw [← Int.add_emod_right]; exact Int.emod_eq_of_lt (by omega) (by omega),
      show (v - 1) % 2 ^ K = v - 1 + 2 ^ K by
      rw [← Int.add_emod_right]; exact Int.emod_eq_of_lt (by omega) (by omega)]
    ring
  · rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)]

/-- **The law of the centered binomial coefficient sampler.** -/
theorem law_cbdPM (η L K : ℕ) [NeZero (2 ^ K - 1)] (hK : 2 ≤ K) (hL : 1 ≤ L) (hLK : L ≤ K)
    (hη : η + 1 ≤ 2 ^ (L - 1)) :
    AppendLaw (cbdPM η L K) 0 P3
      ((ModuleLWE.coeffLaw (2 ^ K - 1) (.cbd η)).map (encM K)) := by
  rintro s ⟨h2, h3, h4⟩
  have hc := AppendLaw.repX (appendLaw_coinAp (k := 7) (r := 2) (b := 4) (by decide))
    (fun s w hs => by rwa [Function.update_of_ne (by decide)]) (η + η)
  rw [catPow_uniformList, Nat.mul_one] at hc
  rw [cbdPM, law_seq, hc s h4, PMF.bind_map]
  have hdet : ∀ u ∈ (BitString.uniformList (η + η)).support,
      ((seq (repX (bitAp 3 true) η) (seq (repX upStep η)
        (seq (repX downStep η) (chainPM K L η (η + η) 0)))).law ∘
        fun u => Function.update s 2 (s 2 ++ u)) u =
      PMF.pure (Function.update s 0 (s 0 ++ leafW K L (mv (cbdV η u)))) := by
    intro u hu
    simp only [Function.comp_apply]
    rw [law_cbdPM_det η L K _ u (BitString.length_of_mem_support_uniformList hu) (by simp [h2])
      (by simp [h3]) (by simp [h4])]
    congr 1
    funext t
    by_cases t0 : t = 0
    · subst t0; simp
    · by_cases t2 : t = 2
      · subst t2; simp [h2]
      · simp [t0, t2]
  rw [PMF.bind_congr_on_support _ _ _ hdet,
    show ((BitString.uniformList (η + η)).bind fun a =>
        PMF.pure (Function.update s 0 (s 0 ++ leafW K L (mv (cbdV η a))))) =
      (BitString.uniformList (η + η)).map
        (fun a => Function.update s 0 (s 0 ++ leafW K L (mv (cbdV η a))))
      from PMF.bind_pure_comp _ _, ← uniformList_cbdM η (2 ^ K - 1), PMF.map_comp, PMF.map_comp]
  refine PMF.map_congr_on_support _ _ _ fun u hu => ?_
  simp only [Function.comp_apply]
  obtain ⟨b1, b2⟩ := cbdV_bounds η u (BitString.length_of_mem_support_uniformList hu)
  have hη' : (η : ℤ) + 1 ≤ 2 ^ (L - 1) := by exact_mod_cast hη
  have hLK' : (2 : ℤ) ^ (L - 1) ≤ 2 ^ (K - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [encM_eq_zmodEnc hK _ (by omega) (by omega), leafW, ← zmodEnc_small hL hLK]
  · unfold mv; split_ifs <;> omega
  · unfold mv; split_ifs <;> omega

/-- **The centered binomial law** of a ring element. -/
noncomputable def cbdR (η : ℕ) : PMF (Rg D) := ringLawD D (ModuleLWE.coeffLaw D.q (.cbd η))

/-- The centered binomial ring sampler (`L` low bits per leaf). -/
def cbdRP (η L : ℕ) : XProg 7 := repF D.N (cbdPM η L D.K)

/-- **The law of the centered binomial ring sampler.** -/
theorem law_cbdRP {η L : ℕ} (hL : 1 ≤ L) (hLK : L ≤ D.K) (hη : η + 1 ≤ 2 ^ (L - 1)) :
    AppendLaw (cbdRP D η L) 0 P5 ((cbdR D η).map (rEnc D).enc) := by
  rw [cbdR, ringLawD_enc]
  exact law_repF (law_cbdPM η L D.K D.hK hL hLK hη) D.N

end AdvancedEncryption.ExpLUT.Prog
