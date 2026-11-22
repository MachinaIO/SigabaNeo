module

public import SigabaNeo.Lib.Lattices.Research.Wall1.MultiBlockVerify
import Mathlib.Data.ZMod.ValMinAbs
import all SigabaNeo.Lib.Lattices.Planted.Probability

/-! # End-to-end multi-block sample-deletion attack (PROOF_GAP Wall 1, Parts 39/131/132)

Plain LWE with `m` rows: iid CBD(η) secret `s` and errors `e`, uniform `A`, all independent;
the attacker sees `(A, y)` with `y = A s + e (mod q)`. The rows are split into `k`
predetermined blocks `b i : Fin (r i) → Fin m` and `v` reserved rows `c : Fin v → Fin m`,
pairwise disjoint and without repetition.

The attack (`attack`) is a function of the public data `(A, y)` only:
* for each block `i`, it calls an exact SVP oracle `O` (any function returning a shortest
  nonzero vector of the given embedding lattice, `IsSVPOracle`) on the block's Part 39 lattice;
* from the output `z` it forms the candidate `h · z_secret`, where `h = ±1` is the height (other
  heights give no candidate), decoded coordinatewise to the residue representative in `[−η, η]`
  (`decode`; no candidate if a residue has no such representative);
* it accepts a candidate iff it passes the residual test on all `v` reserved rows (`passes`) and
  outputs the first accepted candidate.

`attack_success`: for every exact SVP oracle, `q > 6` prime and `η ≤ 3`,
`Pr[attack outputs s] ≥ 1 − E_s[∏ᵢ condFailure (r i) s] − k · (7/q)^v`.

The independence of a block's candidate from the reserved rows is derived from the construction
(`candidate_congr`: the candidate only reads the block's rows), not assumed. -/

public section
namespace SigabaNeo.Wall1.MultiBlock.Attack
open SigabaNeo.Planted SigabaNeo.SampleDeletion SigabaNeo.Wall1.MultiBlock

variable {n q : ℕ}

/-! ## Oracle -/

/-- The embedding lattice of public block data `(B, t)`: `z_err + B z_sec ≡ z_height · t`. -/
@[expose] def pubMember {r : ℕ} (B : Matrix (Fin r) (Fin n) (ZMod q)) (t : Fin r → ZMod q)
    (z : Coord r n → ℤ) : Prop :=
  ∀ i, (z (.inl i) : ZMod q) + B i ⬝ᵥ (fun j ↦ (z (.inr (.inl j)) : ZMod q)) =
    (z (.inr (.inr ())) : ZMod q) * t i

/-- An oracle maps the public data of an `r`-row block to an integer vector. -/
abbrev Oracle (n q : ℕ) :=
  ∀ r : ℕ, Matrix (Fin r) (Fin n) (ZMod q) → (Fin r → ZMod q) → Coord r n → ℤ

/-- Exact SVP: the output is a nonzero lattice vector of minimal squared norm. -/
@[expose] def IsSVPOracle (O : Oracle n q) : Prop :=
  ∀ r B t, pubMember B t (O r B t) ∧ O r B t ≠ 0 ∧
    ∀ w, pubMember B t w → w ≠ 0 → normSq (O r B t) ≤ normSq w

/-- Exact SVP oracles exist (so the hypothesis of `attack_success` is not vacuous). -/
theorem exists_svpOracle [NeZero q] : ∃ O : Oracle n q, IsSVPOracle O := by
  classical
  have key : ∀ (r : ℕ) (B : Matrix (Fin r) (Fin n) (ZMod q)) (t : Fin r → ZMod q),
      ∃ z, pubMember B t z ∧ z ≠ 0 ∧ ∀ w, pubMember B t w → w ≠ 0 → normSq z ≤ normSq w := by
    intro r B t
    have hex : ∃ N, ∃ w, pubMember B t w ∧ w ≠ 0 ∧ normSq w = N := by
      refine ⟨_, Pi.single (.inr (.inr ())) (q : ℤ), ?_, ?_, rfl⟩
      · intro i
        simp
      · intro h
        have := congrFun h (.inr (.inr ()))
        simp only [Pi.single_eq_same, Pi.zero_apply, Nat.cast_eq_zero] at this
        exact NeZero.ne q this
    obtain ⟨z, hz, hne, hN⟩ := Nat.find_spec hex
    exact ⟨z, hz, hne, fun w hw hw0 ↦ hN ▸ Nat.find_min' hex ⟨w, hw, hw0, rfl⟩⟩
  choose O hO using key
  exact ⟨O, hO⟩

/-! ## The attack -/

/-- Decode each coordinate to its residue representative in `[−η, η]`, if all exist. -/
@[expose] def decode (η q : ℕ) (u : Fin n → ℤ) : Option (Fin n → ℤ) :=
  if ∀ j, ((u j : ZMod q).valMinAbs).natAbs ≤ η then
    some fun j ↦ (u j : ZMod q).valMinAbs
  else none

/-- The candidate from one block: call the oracle on the block's public data, normalize the
height to one (rejecting heights other than `±1`), and decode. -/
@[expose] def candidate (η : ℕ) (O : Oracle n q) {m r : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod q))
    (y : Fin m → ZMod q) (b : Fin r → Fin m) : Option (Fin n → ℤ) :=
  let z := O r (fun a ↦ A (b a)) (fun a ↦ y (b a))
  if z (.inr (.inr ())) = 1 ∨ z (.inr (.inr ())) = -1 then
    decode η q (fun j ↦ z (.inr (.inr ())) * z (.inr (.inl j)))
  else none

/-- The residual test on all reserved rows `c`. -/
@[expose] def passes {m v : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod q)) (y : Fin m → ZMod q)
    (c : Fin v → Fin m) (d : Fin n → ℤ) : Prop :=
  ∀ j, accept (y (c j) - A (c j) ⬝ᵥ fun l ↦ (d l : ZMod q))

open Classical in
/-- The attack: the first block candidate (in block order) passing all reserved rows. -/
@[expose] noncomputable def attack (η : ℕ) (O : Oracle n q) {m k v : ℕ} (r : Fin k → ℕ)
    (b : ∀ i, Fin (r i) → Fin m) (c : Fin v → Fin m) (A : Matrix (Fin m) (Fin n) (ZMod q))
    (y : Fin m → ZMod q) : Option (Fin n → ℤ) :=
  (List.finRange k).findSome? fun i ↦
    (candidate η O A y (b i)).filter fun d ↦ decide (passes A y c d)

/-- The public LWE vector `y = A s + e (mod q)`. -/
@[expose] def lweSample {m η : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod q)) (s : Fin n → Digit η)
    (e : Fin m → Digit η) : Fin m → ZMod q :=
  fun i ↦ A i ⬝ᵥ (fun j ↦ ((centered (s j) : ℤ) : ZMod q)) + ((centered (e i) : ℤ) : ZMod q)

/-! ## The probability space -/

open Classical in
/-- Probability of an event under plain LWE: iid CBD(η) `s ∈ Digit^n`, `e ∈ Digit^m`, uniform
`A`. The same normalization as the left side of `multiblock_exact`. -/
@[expose] noncomputable def lweProb (m n q η : ℕ) [Fact q.Prime]
    (P : (Fin n → Digit η) → (Fin m → Digit η) → Matrix (Fin m) (Fin n) (ZMod q) → Prop) : ℚ :=
  (∑ s : Fin n → Digit η, ∑ e : Fin m → Digit η, ∑ A : Matrix (Fin m) (Fin n) (ZMod q),
      if P s e A then ((∏ j, (mass (s j) : ℚ)) * ∏ j, (mass (e j) : ℚ)) else 0) /
    (((4^η : ℕ) : ℚ)^(m+n) * (q : ℚ)^(n*m))

private theorem mass_prod_sum (η d : ℕ) :
    ∑ x : Fin d → Digit η, ∏ j, (mass (x j) : ℚ) = ((4^η : ℕ) : ℚ)^d := by
  have h1 : ∑ a : Digit η, (mass a : ℚ) = ((4^η : ℕ) : ℚ) := by
    have h := cbdWeight_sum η
    simp only [cbdWeight, ← Finset.sum_div] at h
    rwa [div_eq_one_iff_eq (by positivity)] at h
  rw [← Fintype.prod_sum (fun (_ : Fin d) (a : Digit η) ↦ (mass a : ℚ)), h1]
  simp

private theorem card_matrix (m n q : ℕ) [Fact q.Prime] :
    (Fintype.card (Matrix (Fin m) (Fin n) (ZMod q)) : ℚ) = (q : ℚ)^(n*m) := by
  change ((Fintype.card (Fin m → Fin n → ZMod q) : ℕ) : ℚ) = _
  simp [← pow_mul, mul_comm]

private theorem denom_pos (m n q η : ℕ) [Fact q.Prime] :
    0 < ((4^η : ℕ) : ℚ)^(m+n) * (q : ℚ)^(n*m) := by
  have : (0 : ℚ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  positivity

private theorem weight_total (m n q η : ℕ) [Fact q.Prime] :
    (∑ s : Fin n → Digit η, ∑ e : Fin m → Digit η, ∑ _A : Matrix (Fin m) (Fin n) (ZMod q),
      ((∏ j, (mass (s j) : ℚ)) * ∏ j, (mass (e j) : ℚ))) =
      ((4^η : ℕ) : ℚ)^(m+n) * (q : ℚ)^(n*m) := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_matrix, ← Finset.mul_sum,
    ← Finset.sum_mul, mass_prod_sum]
  ring

theorem lweProb_not (m n q η : ℕ) [Fact q.Prime]
    (P : (Fin n → Digit η) → (Fin m → Digit η) → Matrix (Fin m) (Fin n) (ZMod q) → Prop) :
    lweProb m n q η (fun s e A ↦ ¬ P s e A) = 1 - lweProb m n q η P := by
  classical
  unfold lweProb
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq (denom_pos m n q η).ne',
    ← weight_total m n q η]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun e _ ↦
    Finset.sum_congr rfl fun A _ ↦ ?_
  split_ifs <;> simp_all

private theorem sum_comm4 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] {k : ℕ}
    (f : Fin k → α → β → γ → ℚ) :
    ∑ i, ∑ a, ∑ b, ∑ c, f i a b c = ∑ a, ∑ b, ∑ c, ∑ i, f i a b c := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.sum_comm]

theorem lweProb_union (m n q η : ℕ) [Fact q.Prime] {k : ℕ}
    (P Q : (Fin n → Digit η) → (Fin m → Digit η) → Matrix (Fin m) (Fin n) (ZMod q) → Prop)
    (R : Fin k → (Fin n → Digit η) → (Fin m → Digit η) → Matrix (Fin m) (Fin n) (ZMod q) → Prop)
    (h : ∀ s e A, P s e A → Q s e A ∨ ∃ i, R i s e A) :
    lweProb m n q η P ≤ lweProb m n q η Q + ∑ i, lweProb m n q η (R i) := by
  classical
  unfold lweProb
  rw [← Finset.sum_div, ← add_div, sum_comm4]
  refine div_le_div_of_nonneg_right ?_ (denom_pos m n q η).le
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ ↦ Finset.sum_le_sum fun e _ ↦ Finset.sum_le_sum fun A _ ↦ ?_
  have hw : 0 ≤ (∏ j, (mass (s j) : ℚ)) * ∏ j, (mass (e j) : ℚ) := by positivity
  have hR : ∀ i, 0 ≤ if R i s e A then ((∏ j, (mass (s j) : ℚ)) * ∏ j, (mass (e j) : ℚ))
      else 0 := fun i ↦ by split_ifs <;> simp [hw]
  have hQ0 : 0 ≤ if Q s e A then ((∏ j, (mass (s j) : ℚ)) * ∏ j, (mass (e j) : ℚ))
      else 0 := by split_ifs <;> simp [hw]
  by_cases hP : P s e A
  · rcases h s e A hP with hQ | ⟨i, hi⟩
    · simp only [hP, hQ, ↓reduceIte]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ hR i)
    · simp only [hP, ↓reduceIte]
      refine le_add_of_nonneg_of_le hQ0 ?_
      refine le_trans ?_ (Finset.single_le_sum (fun i _ ↦ hR i) (Finset.mem_univ i))
      simp [hi]
  · simp only [hP, ↓reduceIte]
    exact add_nonneg hQ0 (Finset.sum_nonneg fun i _ ↦ hR i)

open Classical in
/-- A count bound for every fixed `(s, e)` gives the probability bound. -/
theorem lweProb_le_of_count (m n q η : ℕ) [Fact q.Prime]
    (R : (Fin n → Digit η) → (Fin m → Digit η) → Matrix (Fin m) (Fin n) (ZMod q) → Prop)
    (ρ : ℚ) (h : ∀ s e, ((Finset.univ.filter (R s e)).card : ℚ) ≤ ρ * (q : ℚ)^(n*m)) :
    lweProb m n q η R ≤ ρ := by
  unfold lweProb
  rw [div_le_iff₀ (denom_pos m n q η)]
  have key : ∀ s e, (∑ A : Matrix (Fin m) (Fin n) (ZMod q),
      if R s e A then ((∏ j, (mass (s j) : ℚ)) * ∏ j, (mass (e j) : ℚ)) else 0) ≤
      ρ * (q : ℚ)^(n*m) * ((∏ j, (mass (s j) : ℚ)) * ∏ j, (mass (e j) : ℚ)) := by
    intro s e
    have hw : 0 ≤ (∏ j, (mass (s j) : ℚ)) * ∏ j, (mass (e j) : ℚ) := by positivity
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (h s e) hw
  refine (Finset.sum_le_sum fun s _ ↦ Finset.sum_le_sum fun e _ ↦ key s e).trans (le_of_eq ?_)
  simp only [← Finset.mul_sum, ← Finset.sum_mul, mass_prod_sum]
  ring

/-! ## Reserved rows are independent of the block candidates -/

/-- A candidate `G A` that does not read the reserved rows `c` of `A` has a wrong residue passing
all reserved rows for at most a `(7/q)^v` fraction of designs `A`, for every reserved error. -/
theorem reserved_count [Fact q.Prime] (hq : 6 < q) {m v : ℕ} (c : Fin v → Fin m)
    (hc : Function.Injective c) (σ : Fin n → ZMod q) (e : Fin v → ZMod q)
    (G : Matrix (Fin m) (Fin n) (ZMod q) → Option (Fin n → ZMod q))
    (hG : ∀ A A' : Matrix (Fin m) (Fin n) (ZMod q),
      (∀ i, i ∉ Set.range c → A i = A' i) → G A = G A') :
    ((Finset.univ.filter fun A : Matrix (Fin m) (Fin n) (ZMod q) ↦
      ∃ d, G A = some d ∧ d ≠ σ ∧ ∀ j, accept (A (c j) ⬝ᵥ σ + e j - A (c j) ⬝ᵥ d)).card : ℚ) ≤
      (7/q)^v * (q : ℚ)^(n*m) := by
  classical
  let R := {i : Fin m // i ∉ Set.range c}
  let E : Fin v ⊕ R ≃ Fin m :=
    (Equiv.sumCongr (Equiv.ofInjective c hc) (Equiv.refl R)).trans
      (Equiv.sumCompl (· ∈ Set.range c))
  have hE (j : Fin v) : E.symm (c j) = .inl j := by
    apply E.injective
    simp only [Equiv.apply_symm_apply]
    rfl
  have hE' (i : R) : E.symm i.1 = .inr i := by
    apply E.injective
    simp only [Equiv.apply_symm_apply]
    rfl
  let Φ : (Fin v → Fin n → ZMod q) × (R → Fin n → ZMod q) ≃ Matrix (Fin m) (Fin n) (ZMod q) :=
    (Equiv.sumArrowEquivProdArrow _ _ _).symm.trans (E.arrowCongr (Equiv.refl _))
  have hΦc (p : (Fin v → Fin n → ZMod q) × (R → Fin n → ZMod q)) (j : Fin v) :
      Φ p (c j) = p.1 j := by
    obtain ⟨X, Y⟩ := p
    change (Equiv.sumArrowEquivProdArrow _ _ _).symm (X, Y) (E.symm (c j)) = X j
    rw [hE, Equiv.sumArrowEquivProdArrow_symm_apply_inl]
  have hΦr (p : (Fin v → Fin n → ZMod q) × (R → Fin n → ZMod q)) (i : R) :
      Φ p i.1 = p.2 i := by
    obtain ⟨X, Y⟩ := p
    change (Equiv.sumArrowEquivProdArrow _ _ _).symm (X, Y) (E.symm i.1) = Y i
    rw [hE', Equiv.sumArrowEquivProdArrow_symm_apply_inr]
  have hGΦ (X : Fin v → Fin n → ZMod q) (Y : R → Fin n → ZMod q) :
      G (Φ (X, Y)) = G (Φ (0, Y)) :=
    hG _ _ fun i hi ↦ by rw [hΦr (X, Y) ⟨i, hi⟩, hΦr (0, Y) ⟨i, hi⟩]
  let P : Matrix (Fin m) (Fin n) (ZMod q) → Prop := fun A ↦
    ∃ d, G A = some d ∧ d ≠ σ ∧ ∀ j, accept (A (c j) ⬝ᵥ σ + e j - A (c j) ⬝ᵥ d)
  let Q : (R → Fin n → ZMod q) → (Fin v → Fin n → ZMod q) → Prop := fun Y X ↦
    ∃ d, G (Φ (0, Y)) = some d ∧ d ≠ σ ∧ ∀ j, accept (X j ⬝ᵥ σ + e j - X j ⬝ᵥ d)
  have hPQ (X Y) : P (Φ (X, Y)) ↔ Q Y X := by
    simp only [P, Q, hGΦ, hΦc]
  have hcard : ((Finset.univ.filter P).card : ℚ) =
      ∑ Y, ((Finset.univ.filter (Q Y)).card : ℚ) := by
    simp only [Finset.card_filter]
    push_cast
    rw [← Φ.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun Y _ ↦ Finset.sum_congr rfl fun X _ ↦ ?_
    simp only [hPQ]
  have hq0 : (0 : ℚ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have inner (Y : R → Fin n → ZMod q) :
      ((Finset.univ.filter (Q Y)).card : ℚ) ≤ (7/q)^v * (q : ℚ)^(n*v) := by
    obtain hY | ⟨d, hY⟩ := Option.eq_none_or_eq_some (G (Φ (0, Y)))
    · have : Finset.univ.filter (Q Y) = ∅ := by
        ext X; simp [Q, hY]
      rw [this]; simp; positivity
    · by_cases hd : d = σ
      · have : Finset.univ.filter (Q Y) = ∅ := by
          ext X; simp [Q, hY, hd]
        rw [this]; simp; positivity
      · have hv := verify_exact (v := v) hq σ d hd e
        rw [div_eq_iff (by positivity)] at hv
        refine le_of_eq (Eq.trans ?_ hv)
        congr 2
        ext X
        constructor
        · intro h
          obtain ⟨d', hd', -, h⟩ := (Finset.mem_filter.mp h).2
          rw [hY] at hd'
          cases hd'
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
        · intro h
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, d, hY, hd, (Finset.mem_filter.mp h).2⟩
  rw [hcard]
  refine (Finset.sum_le_sum fun Y _ ↦ inner Y).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc' := congrArg (fun x : ℕ ↦ (x : ℚ)) (Fintype.card_congr Φ)
  simp only [Fintype.card_prod] at hc'
  rw [← card_matrix m n q, ← hc']
  have : ((Fintype.card (Fin v → Fin n → ZMod q) : ℕ) : ℚ) = (q : ℚ)^(n*v) := by
    simp [← pow_mul]
  push_cast
  rw [this]
  ring

/-! ## A good block yields the secret -/

private theorem support_bound {η : ℕ} (a : Digit η) : (centered a).natAbs ≤ η := by
  have := a.isLt
  unfold centered
  omega

theorem valMinAbs_small (hq : 2*η < q) (x : ℤ) (hx : x.natAbs ≤ η) :
    ((x : ZMod q)).valMinAbs = x := by
  have : NeZero q := ⟨by omega⟩
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_, ?_⟩ <;> omega

theorem decode_support {η : ℕ} {u d : Fin n → ℤ} (h : decode η q u = some d) (j : Fin n) :
    (d j).natAbs ≤ η := by
  unfold decode at h
  split_ifs at h with hh
  cases h
  exact hh j

theorem candidate_support {η : ℕ} {O : Oracle n q} {m r : ℕ} {A : Matrix (Fin m) (Fin n) (ZMod q)}
    {y : Fin m → ZMod q} {b : Fin r → Fin m} {d : Fin n → ℤ}
    (h : candidate η O A y b = some d) (j : Fin n) : (d j).natAbs ≤ η := by
  simp only [candidate] at h
  split_ifs at h
  exact decode_support h j

/-- If block `b` does not fail (the projected plant is the unique shortest pair), the candidate
of an exact SVP oracle is the secret. -/
theorem candidate_good {η : ℕ} [Fact q.Prime] (hq : 2*η < q) {O : Oracle n q} (hO : IsSVPOracle O)
    {m r : ℕ} (b : Fin r → Fin m) (s : Fin n → Digit η) (e : Fin m → Digit η)
    (A : Matrix (Fin m) (Fin n) (ZMod q)) (hgood : ¬ sampleBlockBad (q := q) b s e A) :
    candidate η O A (lweSample A s e) b = some (fun j ↦ centered (s j)) := by
  obtain ⟨hz, hne, hmin⟩ := hO r (fun a ↦ A (b a)) (fun a ↦ lweSample A s e (b a))
  set z := O r (fun a ↦ A (b a)) (fun a ↦ lweSample A s e (b a)) with hzdef
  have hrec := exact_svp_recovery (q := q) (fun a ↦ centered (e (b a))) (fun j ↦ centered (s j))
    (fun a ↦ A (b a)) hgood z hz hne (fun w hw hw0 ↦ hmin w hw hw0)
  obtain ⟨h1, h2⟩ := hrec
  have hh : z (.inr (.inr ())) = 1 ∨ z (.inr (.inr ())) = -1 := by
    rcases h1 with h | h <;> rw [h] <;> simp [plantedPoint]
  unfold candidate
  simp only [← hzdef]
  simp only [hh, ↓reduceIte]
  have h2' : (fun j ↦ z (.inr (.inr ())) * z (.inr (.inl j))) = fun j ↦ centered (s j) := h2
  rw [h2']
  unfold decode
  have hv (j : Fin n) : (((centered (s j) : ℤ) : ZMod q)).valMinAbs = centered (s j) :=
    valMinAbs_small hq _ (support_bound _)
  simp only [hv]
  simp only [support_bound, implies_true, ↓reduceIte]

/-- The secret passes the reserved rows when `η ≤ 3`. -/
theorem passes_secret {η : ℕ} (hη : η ≤ 3) {m v : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod q))
    (s : Fin n → Digit η) (e : Fin m → Digit η) (c : Fin v → Fin m) :
    passes A (lweSample A s e) c (fun j ↦ centered (s j)) := by
  intro j
  refine ⟨centered (e (c j)), ?_, ?_, ?_⟩
  · have := support_bound (e (c j)); omega
  · have := support_bound (e (c j)); omega
  · simp [lweSample]

/-- A block candidate does not depend on rows of `A` outside the block. -/
theorem candidate_congr {η : ℕ} (O : Oracle n q) {m r : ℕ} (b : Fin r → Fin m)
    (s : Fin n → Digit η) (e : Fin m → Digit η) (A A' : Matrix (Fin m) (Fin n) (ZMod q))
    (h : ∀ a, A (b a) = A' (b a)) :
    candidate η O A (lweSample A s e) b = candidate η O A' (lweSample A' s e) b := by
  have hB : (fun a ↦ A (b a)) = fun a ↦ A' (b a) := funext h
  have ht : (fun a ↦ lweSample A s e (b a)) = fun a ↦ lweSample A' s e (b a) :=
    funext fun a ↦ by simp only [lweSample, h a]
  unfold candidate
  rw [hB, ht]

/-! ## The end-to-end bound -/

/-- Block `i`'s candidate is a wrong integer vector that passes all reserved rows. -/
@[expose] def falseAccept (η : ℕ) (O : Oracle n q) {m r v : ℕ} (b : Fin r → Fin m)
    (c : Fin v → Fin m) (s : Fin n → Digit η) (e : Fin m → Digit η)
    (A : Matrix (Fin m) (Fin n) (ZMod q)) : Prop :=
  ∃ d, candidate η O A (lweSample A s e) b = some d ∧ d ≠ (fun j ↦ centered (s j)) ∧
    passes A (lweSample A s e) c d

/-- Failure of the attack implies that every block fails or some block's candidate is a false
acceptance. -/
theorem attack_fail_imp {η : ℕ} [Fact q.Prime] (hq : 6 < q) (hη : η ≤ 3) {O : Oracle n q}
    (hO : IsSVPOracle O) {m k v : ℕ} (r : Fin k → ℕ) (b : ∀ i, Fin (r i) → Fin m)
    (c : Fin v → Fin m) (s : Fin n → Digit η) (e : Fin m → Digit η)
    (A : Matrix (Fin m) (Fin n) (ZMod q))
    (hfail : attack η O r b c A (lweSample A s e) ≠ some (fun j ↦ centered (s j))) :
    (∀ i, sampleBlockBad (q := q) (b i) s e A) ∨ ∃ i, falseAccept η O (b i) c s e A := by
  classical
  by_cases hall : ∀ i, sampleBlockBad (q := q) (b i) s e A
  · exact .inl hall
  right
  push Not at hall
  obtain ⟨i, hi⟩ := hall
  have hc := candidate_good (by omega) hO (b i) s e A hi
  have hp := passes_secret hη A s e c
  have hsome : attack η O r b c A (lweSample A s e) ≠ none := by
    unfold attack
    rw [Ne, List.findSome?_eq_none_iff]
    intro hn
    have := hn i (List.mem_finRange i)
    rw [hc] at this
    simp [hp] at this
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hsome
  have hd' := hd
  unfold attack at hd'
  obtain ⟨i', -, hi'⟩ := List.exists_of_findSome?_eq_some hd'
  rw [Option.filter_eq_some_iff] at hi'
  refine ⟨i', d, hi'.1, ?_, of_decide_eq_true hi'.2⟩
  rintro rfl
  exact hfail hd

/-- Block `i` produces a false acceptance with probability at most `(7/q)^v`. -/
theorem falseAccept_le {η : ℕ} [Fact q.Prime] (hq : 6 < q) (hη : η ≤ 3) (O : Oracle n q)
    {m r v : ℕ} (b : Fin r → Fin m) (c : Fin v → Fin m)
    (hbc : ∀ a j, b a ≠ c j) (hc : Function.Injective c) :
    lweProb m n q η (falseAccept η O b c) ≤ (7/q)^v := by
  classical
  apply lweProb_le_of_count
  intro s e
  let σ : Fin n → ZMod q := fun j ↦ ((centered (s j) : ℤ) : ZMod q)
  let e' : Fin v → ZMod q := fun j ↦ ((centered (e (c j)) : ℤ) : ZMod q)
  let G : Matrix (Fin m) (Fin n) (ZMod q) → Option (Fin n → ZMod q) := fun A ↦
    (candidate η O A (lweSample A s e) b).map fun d l ↦ ((d l : ℤ) : ZMod q)
  have hG (A A' : Matrix (Fin m) (Fin n) (ZMod q))
      (hA : ∀ i, i ∉ Set.range c → A i = A' i) : G A = G A' := by
    simp only [G]
    rw [candidate_congr O b s e A A' fun a ↦ hA _ fun ⟨j, hj⟩ ↦ hbc a j hj.symm]
  refine le_trans (Nat.cast_le.mpr (Finset.card_le_card fun A hA ↦ ?_))
    (reserved_count hq c hc σ e' G hG)
  obtain ⟨d, hd, hne, hp⟩ := (Finset.mem_filter.mp hA).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun l ↦ ((d l : ℤ) : ZMod q), by simp [G, hd],
    ?_, fun j ↦ hp j⟩
  intro heq
  apply hne
  funext l
  have h1 := valMinAbs_small (q := q) (η := η) (by omega) _ (candidate_support hd l)
  have h2 := valMinAbs_small (q := q) (η := η) (by omega) _ (support_bound (s l))
  have h3 := congrFun heq l
  simp only [σ] at h3
  rw [← h1, ← h2, h3]

/-- **End-to-end failure bound.** For plain LWE with `m` rows split into predetermined disjoint
blocks `b i` (sizes `r i`) and `v` reserved rows `c`, any exact SVP oracle, `q > 6` prime and
CBD(η) with `η ≤ 3`: the attack fails to output the secret with probability at most
`E_s[∏ᵢ condFailure (r i) s] + k · (7/q)^v`. -/
theorem attack_failure_le {η : ℕ} [Fact q.Prime] (hq : 6 < q) (hη : η ≤ 3) {m k v : ℕ}
    (r : Fin k → ℕ) (b : ∀ i, Fin (r i) → Fin m) (c : Fin v → Fin m)
    (hb : Function.Injective (Sum.elim (fun p : (Σ i, Fin (r i)) ↦ b p.1 p.2) c))
    (O : Oracle n q) (hO : IsSVPOracle O) :
    lweProb m n q η (fun s e A ↦
        attack η O r b c A (lweSample A s e) ≠ some (fun j ↦ centered (s j))) ≤
      expect (cbdWeight η) (fun s ↦ ∏ i, condFailure (r i) n q η s) + k * (7/q)^v := by
  have hblocks : Function.Injective (fun p : (Σ i, Fin (r i)) ↦ b p.1 p.2) :=
    hb.comp Sum.inl_injective
  have hc : Function.Injective c := hb.comp Sum.inr_injective
  have hbc (i : Fin k) (a : Fin (r i)) (j : Fin v) : b i a ≠ c j := fun h ↦
    Sum.inl_ne_inr (hb (a₁ := .inl ⟨i, a⟩) (a₂ := .inr j) h)
  refine (lweProb_union m n q η _ (fun s e A ↦ ∀ i, sampleBlockBad (q := q) (b i) s e A)
    (fun i ↦ falseAccept η O (b i) c) fun s e A h ↦ attack_fail_imp hq hη hO r b c s e A h).trans
    (add_le_add (le_of_eq ?_) ?_)
  · rw [← multiblock_exact m n q η r b hblocks]
    unfold lweProb
    congr 1
    refine Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun e _ ↦
      Finset.sum_congr rfl fun A _ ↦ ?_
    by_cases h : ∀ i, sampleBlockBad (q := q) (b i) s e A <;> simp only [h, ↓reduceIte]
  · refine (Finset.sum_le_sum fun i _ ↦ falseAccept_le hq hη O (b i) c (hbc i) hc).trans
      (le_of_eq ?_)
    simp

/-- **End-to-end success bound** (PROOF_GAP Parts 131/132). Same hypotheses: the attack outputs
the true secret with probability at least `1 − E_s[∏ᵢ condFailure (r i) s] − k · (7/q)^v`. -/
theorem attack_success {η : ℕ} [Fact q.Prime] (hq : 6 < q) (hη : η ≤ 3) {m k v : ℕ}
    (r : Fin k → ℕ) (b : ∀ i, Fin (r i) → Fin m) (c : Fin v → Fin m)
    (hb : Function.Injective (Sum.elim (fun p : (Σ i, Fin (r i)) ↦ b p.1 p.2) c))
    (O : Oracle n q) (hO : IsSVPOracle O) :
    1 - expect (cbdWeight η) (fun s ↦ ∏ i, condFailure (r i) n q η s) - k * (7/q)^v ≤
      lweProb m n q η (fun s e A ↦
        attack η O r b c A (lweSample A s e) = some (fun j ↦ centered (s j))) := by
  have h := attack_failure_le hq hη r b c hb O hO
  rw [lweProb_not] at h
  linarith

/-- The success bound in terms of the norm-only conditional bound `condBound` (for the numeric
check), with the secret average reduced to a finite sum over `‖s‖²` by `expect_energy`. -/
theorem attack_success_condBound {η : ℕ} [Fact q.Prime] (hq : 6 < q) (hη : η ≤ 3) (J : ℕ)
    (hJ : J*(1+η^2) < q^2) {m k v : ℕ}
    (r : Fin k → ℕ) (b : ∀ i, Fin (r i) → Fin m) (c : Fin v → Fin m)
    (hb : Function.Injective (Sum.elim (fun p : (Σ i, Fin (r i)) ↦ b p.1 p.2) c))
    (O : Oracle n q) (hO : IsSVPOracle O) :
    1 - (∑ E ∈ Finset.range (n*η^2+1), (shell η n E : ℚ) * ∏ i, condBound (r i) n q η J E) /
        ((4^η : ℕ) : ℚ)^n - k * (7/q)^v ≤
      lweProb m n q η (fun s e A ↦
        attack η O r b c A (lweSample A s e) = some (fun j ↦ centered (s j))) := by
  refine le_trans ?_ (attack_success hq hη r b c hb O hO)
  rw [← expect_energy n η (fun E ↦ ∏ i, condBound (r i) n q η J E)]
  have hle : expect (cbdWeight η) (fun s ↦ ∏ i, condFailure (r i) n q η s) ≤
      expect (cbdWeight η) (fun s : Fin n → Digit η ↦
        ∏ i, condBound (r i) n q η J (normSq (fun j ↦ centered (s j)))) := by
    unfold expect
    refine Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left ?_
      (Finset.prod_nonneg fun j _ ↦ cbdWeight_nonneg _ _)
    exact Finset.prod_le_prod₀ (fun i _ ↦ condFailure_nonneg _ _ _ _ _)
      (fun i _ ↦ condFailure_le _ _ _ _ _ hJ s)
  linarith

end SigabaNeo.Wall1.MultiBlock.Attack

#print axioms SigabaNeo.Wall1.MultiBlock.Attack.exists_svpOracle
#print axioms SigabaNeo.Wall1.MultiBlock.Attack.reserved_count
#print axioms SigabaNeo.Wall1.MultiBlock.Attack.candidate_good
#print axioms SigabaNeo.Wall1.MultiBlock.Attack.candidate_congr
#print axioms SigabaNeo.Wall1.MultiBlock.Attack.attack_fail_imp
#print axioms SigabaNeo.Wall1.MultiBlock.Attack.falseAccept_le
#print axioms SigabaNeo.Wall1.MultiBlock.Attack.attack_failure_le
#print axioms SigabaNeo.Wall1.MultiBlock.Attack.attack_success
#print axioms SigabaNeo.Wall1.MultiBlock.Attack.attack_success_condBound
