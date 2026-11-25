import SigabaNeoStd.Lattices.Estimator.Bound.Primal

/-!
# A lower bound on one primal candidate
-/

namespace SigabaNeo.Lattices.Estimator

open Fx NumPrimal PrimalHybrid Reduction

theorem Reduction.matzovBits_nonneg {b d : ℕ} (hb : 20 ≤ b) (hd : 1 ≤ d) : 0 ≤ matzovBits b d := by
  unfold matzovBits
  have h20 : ¬ b < 20 := by omega
  simp only [h20, ↓reduceIte]
  refine le_trans ?_ (le_log2Add_left _ _)
  unfold lllBits
  have := log2_ofInt_nonneg (x := (d : ℤ)) (by exact_mod_cast hd)
  linarith

/-- A candidate of the primal attacks costs at least `K`: by its reduction cost, by its guessing
cost and miss probability (`Mz` bits), or by Babai's failure on its profile. -/
theorem PrimalHybrid.evalAt_ge {K : Fx} {p : LWEParams} {mitm : Bool} {m : Option ℕ}
    {q xi s : Fx} {z : ℕ} {ws : Array (Fx × Fx)} {b d : ℕ} {Mz : ℤ}
    (hMz : -1 ≤ Mz) (hws : ∀ e ∈ ws, 0 ≤ e.1 ∧ Mz * ONE ≤ e.1 - e.2)
    (hcase : (20 ≤ b ∧ K ≤ redLB b) ∨ K + 20 * ONE ≤ Mz * ONE ∨
      ∀ eta, eta ≤ d → (d > 4096 → eta ≤ maxBeta + 1) →
        profile (d - eta) (q - ((p.n - z : ℕ) * (q - xi)) / (d : ℤ) - s + ((d : ℤ) - 1) * log2Delta b)
          (2 * log2Delta b) false ≤ -(K + 21 * ONE)) :
    CostGe K (evalAt p mitm m q xi s z ws b d) := by
  unfold evalAt
  simp only []
  have heta4 : d > 4096 → (if mitm = true then 0 else etaFor (q - ((p.n - z : ℕ) * (q - xi)) / (d : ℤ) - s)
      (log2Delta b) d) ≤ maxBeta + 1 := by
    intro hd; split
    · omega
    · have := etaFor_le (q - ((p.n - z : ℕ) * (q - xi)) / (d : ℤ) - s) (log2Delta b) d
      simp only [hd, ↓reduceIte] at this; have := min_le_right d maxBeta; omega
  generalize (if mitm = true then 0 else etaFor (q - ((p.n - z : ℕ) * (q - xi)) / (d : ℤ) - s)
      (log2Delta b) d) = eta at heta4 ⊢
  split
  · simp
  rename_i hdb
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hdb
  split
  · simp
  rename_i heta
  simp only [Id.run_pure]
  apply NumPrimal.minimize_ge
  intro i
  apply CostGe.bind
  intro e he
  obtain ⟨a, t⟩ := e
  have hmem : (a, t) ∈ ws := Array.mem_of_getElem? he
  obtain ⟨ha, hat⟩ := hws _ hmem
  simp only at ha hat
  intro x hx
  simp only [Option.pure_def, Option.some.injEq] at hx
  subst hx
  have heta' : eta ≤ d := by simpa using heta
  set svp := if mitm = true then 2 * log2Nat d else
    log2Add (matzovBits (eta + 1) (eta + 1)) (2 * log2Nat (max (d - eta) 1))
  have hsvp : 0 ≤ svp := by
    simp only [svp]; split
    · have := log2Nat_nonneg d; linarith
    · have := le_log2Add_right (matzovBits (eta + 1) (eta + 1)) (2 * log2Nat (max (d - eta) 1))
      have := log2Nat_nonneg (max (d - eta) 1); linarith
  set first := q - ((p.n - z : ℕ) * (q - xi)) / (d : ℤ) - s + ((d : ℤ) - 1) * log2Delta b
  set lp := profile (d - eta) first (2 * log2Delta b) false +
    (if (mitm && decide (z > 0)) = true then profile d first (2 * log2Delta b) true else 0)
  have hlp1 : lp ≤ profile (d - eta) first (2 * log2Delta b) false := by
    simp only [lp]; split
    · have := profile_nonpos d first (2 * log2Delta b) true; linarith
    · linarith
  have hlp : lp ≤ 0 := hlp1.trans (profile_nonpos _ _ _ _)
  have hrep := repetitions_ge (lp + t)
  have hrep0 := repetitions_nonneg (lp + t)
  have hO := ONE_pos
  rcases hcase with ⟨hb20, h⟩ | h | h
  · exact h.trans ((redLB_le hb20 d).trans (by
      have := le_log2Add_left (matzovBits b d) (svp + a); linarith))
  · have := le_log2Add_right (matzovBits b d) (svp + a)
    linarith
  · have := le_log2Add_right (matzovBits b d) (svp + a)
    have hpro := h eta heta' heta4
    have : (-1 : ℤ) * ONE ≤ Mz * ONE := Int.mul_le_mul_of_nonneg_right hMz (le_of_lt hO)
    linarith

/-- AM–GM in integers: `⌊A/d⌋ + dδ ≥ T − 1` when `T² ≤ 4Aδ`. -/
theorem amgm_floor {A δ T : ℤ} {d : ℕ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hd : 1 ≤ d) (hT : 0 ≤ T)
    (h : T * T ≤ 4 * A * δ) : T - 1 ≤ A / (d : ℤ) + d * δ := by
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have hf := Int.lt_ediv_add_one_mul_self A hd'
  have hf0 : 0 ≤ A / (d : ℤ) := Int.ediv_nonneg hA (le_of_lt hd')
  by_contra hc
  push Not at hc
  set f := A / (d : ℤ)
  have hx : 0 ≤ f + 1 + d * δ := by positivity
  have h1 : (f + 1 + d * δ) * (f + 1 + d * δ) < T * T := by nlinarith
  have h2 : 4 * A * δ ≤ 4 * ((f + 1) * d) * δ := by nlinarith
  nlinarith [sq_nonneg (f + 1 - d * δ)]

/-- **Babai fails at small block sizes.** If `T² ≤ 4 u (q − ξ) δ` with `T` above `log₂ q` by the
margin below, the GSA profile of every dimension `d ≥ maxBeta + 1 + W` drops by more than 55 bits
at least `W` coordinates before the last `maxBeta + 1`, so the success probability is at most
`2^{c0 W}`. -/
theorem PrimalHybrid.profile_fail {K q xi s T : Fx} {u d b W : ℕ}
    (hδ : 0 < log2Delta b) (hq : 0 ≤ q - xi) (hT0 : 0 ≤ T)
    (hT : T * T ≤ 4 * ((u : ℤ) * (q - xi)) * log2Delta b)
    (hmargin : q - s + 1 + 55 * ONE +
      2 * log2Delta b * ((maxBeta + 1 + W + NumPrimal.strideOf (2 * log2Delta b) : ℕ) : ℤ) ≤ T)
    (hW : c0 * W ≤ -(K + 21 * ONE)) (hd : maxBeta + 1 + W ≤ d) :
    ∀ eta, eta ≤ d → (d > 4096 → eta ≤ maxBeta + 1) →
      profile (d - eta) (q - ((u : ℤ) * (q - xi)) / (d : ℤ) - s + ((d : ℤ) - 1) * log2Delta b)
        (2 * log2Delta b) false ≤ -(K + 21 * ONE) := by
  intro eta _ heta
  have hd4 : d > 4096 := by have : (4096 : ℕ) < maxBeta := by decide
                            omega
  have hE := heta hd4
  set δ := log2Delta b
  set st := NumPrimal.strideOf (2 * δ)
  have hst := NumPrimal.strideOf_pos (2 * δ)
  set jstar := (d - (maxBeta + 1) - W) / st
  have hj1 : jstar * st ≤ d - (maxBeta + 1) - W := Nat.div_mul_le_self _ _
  have hj2 : d - (maxBeta + 1) - W < jstar * st + st := by
    exact Nat.lt_div_mul_add (a := d - (maxBeta + 1) - W) (b := st) (by omega)
  have hgm := amgm_floor (A := (u : ℤ) * (q - xi)) (δ := δ) (T := T) (d := d)
    (mul_nonneg (by positivity) hq) (le_of_lt hδ) (by omega) hT0 hT
  have htail := profile_tail (d - eta) (q - ((u : ℤ) * (q - xi)) / (d : ℤ) - s + ((d : ℤ) - 1) * δ)
    (2 * δ) (by linarith) jstar (by
      have h1 : ((d - (maxBeta + 1) - W : ℕ) : ℤ) < ((jstar * st : ℕ) : ℤ) + st := by exact_mod_cast hj2
      have h2 : ((d - (maxBeta + 1) - W : ℕ) : ℤ) = d - (maxBeta + 1 : ℕ) - W := by
        push_cast; omega
      have h3 : ((maxBeta + 1 + W + st : ℕ) : ℤ) = (maxBeta + 1 : ℕ) + W + st := by push_cast; ring
      rw [h3] at hmargin
      push_cast at h1 h2 hmargin ⊢
      nlinarith)
  have hk : (W : ℤ) ≤ max 0 (((d - eta : ℕ) : ℤ) - ((jstar * st : ℕ) : ℤ)) := by
    refine le_trans ?_ (le_max_right _ _)
    have : jstar * st + W ≤ d - eta := by omega
    have := (Nat.cast_le (α := ℤ)).mpr this
    push_cast at this ⊢; linarith
  have hc0 := c0_neg
  calc profile (d - eta) _ (2 * δ) false ≤ c0 * max 0 (((d - eta : ℕ) : ℤ) - ((jstar * st : ℕ) : ℤ)) := htail
    _ ≤ c0 * W := Int.mul_le_mul_of_nonpos_left (le_of_lt hc0) hk
    _ ≤ -(K + 21 * ONE) := hW

end SigabaNeo.Lattices.Estimator

namespace SigabaNeo.Lattices.Estimator

open Fx NumPrimal PrimalHybrid Reduction

/-- The three ways a block size `b` is expensive, for `z` guessed coordinates. -/
def PrimalHybrid.Expensive (K : Fx) (p : LWEParams) (m : Option ℕ) (q xi s : Fx) (z : ℕ) (Mz : ℤ)
    (Dmin b : ℕ) : Prop :=
  (20 ≤ b ∧ K ≤ redLB b) ∨ K + 20 * ONE ≤ Mz * ONE ∨
    (Dmin ≤ rankOf (p.n - z) q xi m z b ∧ Dmin ≤ p.n - z ∧
      ∀ d, Dmin ≤ d → ∀ eta, eta ≤ d → (d > 4096 → eta ≤ maxBeta + 1) →
        profile (d - eta) (q - ((p.n - z : ℕ) * (q - xi)) / (d : ℤ) - s + ((d : ℤ) - 1) * log2Delta b)
          (2 * log2Delta b) false ≤ -(K + 21 * ONE))

theorem PrimalHybrid.zcost_ge {K : Fx} {p : LWEParams} {mitm plain : Bool} {m : Option ℕ}
    {top : ℕ} {q xi s : Fx} {z : ℕ} {Mz : ℤ} {Dmin : ℕ} (htop : top ≤ maxBeta) (hMz : -1 ≤ Mz)
    (hws : ∀ e ∈ weights p z mitm, 0 ≤ e.1 ∧ Mz * ONE ≤ e.1 - e.2)
    (hb : ∀ b < maxBeta + 2, Expensive K p m q xi s z Mz Dmin b) :
    CostGe K (zcost p mitm plain m top q xi s z) := by
  have hev : ∀ b < maxBeta + 2, ∀ d, (Dmin ≤ d ∨ d = rankOf (p.n - z) q xi m z b) →
      CostGe K (evalAt p mitm m q xi s z (weights p z mitm) b d) := by
    intro b hb' d hd
    apply evalAt_ge hMz hws
    rcases hb b hb' with h | h | ⟨h1, -, h3⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr (h3 d ?_))
      rcases hd with hd | hd
      · exact hd
      · rw [hd]; exact h1
  unfold zcost
  simp only []
  split
  · simp
  have hlm := NumPrimal.localMinimum_ge (k := K) 40 (top + 2) 2
    (fun b => evalAt p mitm m q xi s z (weights p z mitm) b (rankOf (p.n - z) q xi m z b))
    (fun b _ hb2 => hev b (by omega) _ (Or.inr rfl)) (by omega)
  split
  · simp only [Id.run_pure]
    set b := (localMinimum 40 (top + 2) 2 fun b =>
      evalAt p mitm m q xi s z (weights p z mitm) b (rankOf (p.n - z) q xi m z b)).1
    have hbt : b < maxBeta + 2 := by have := hlm.2; omega
    apply (NumPrimal.localMinimum_ge _ _ _ _ _ (by omega)).1
    intro d hd _
    apply evalAt_ge hMz hws
    rcases hb b hbt with h | h | ⟨-, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (h3 d (le_trans h2 hd)))
  · exact hlm.1

end SigabaNeo.Lattices.Estimator

namespace SigabaNeo.Lattices.Estimator

open Fx NumPrimal PrimalHybrid Reduction

/-- The GSA-optimal dimension of `rankOf`, before the caps. -/
def PrimalHybrid.d0 (u : ℕ) (q xi : Fx) (b : ℕ) : ℕ :=
  (ceil (sqrt (div ((u : ℤ) * (q - xi)) (log2Delta b)))).toNat

theorem PrimalHybrid.d0_mono {u u' : ℕ} {q xi : Fx} {b : ℕ} (hu : u ≤ u') (hq : 0 ≤ q - xi)
    (hδ : 0 < log2Delta b) : d0 u q xi b ≤ d0 u' q xi b := by
  unfold d0
  apply Int.toNat_le_toNat
  unfold ceil
  have hO := ONE_pos
  have h1 : div ((u : ℤ) * (q - xi)) (log2Delta b) ≤ div ((u' : ℤ) * (q - xi)) (log2Delta b) := by
    unfold div
    rw [Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt hδ), Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt hδ)]
    apply Int.ediv_le_ediv hδ
    have : (u : ℤ) * (q - xi) ≤ u' * (q - xi) :=
      Int.mul_le_mul_of_nonneg_right (by exact_mod_cast hu) hq
    nlinarith
  have h2 : sqrt (div ((u : ℤ) * (q - xi)) (log2Delta b)) ≤ sqrt (div ((u' : ℤ) * (q - xi)) (log2Delta b)) := by
    unfold sqrt
    exact_mod_cast Nat.sqrt_le_sqrt (Int.toNat_le_toNat (Int.mul_le_mul_of_nonneg_right
      (max_le_max le_rfl h1) (le_of_lt hO)))
  rw [Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt hO), Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt hO)]
  have := Int.ediv_le_ediv hO (neg_le_neg h2)
  linarith

/-- The per-block-size check of the primal attacks: the reduction bound, or Babai's failure with
an AM–GM margin uniform in the dimension, at `uMin` lattice coordinates. -/
def PrimalHybrid.check (K : Fx) (uMin : ℕ) (q xi s : Fx) (W b : ℕ) : Bool :=
  (decide (20 ≤ b) && decide (K ≤ redLB b)) ||
    (decide (0 < log2Delta b) &&
      decide (q - s + 1 + 55 * ONE + 2 * log2Delta b *
        ((maxBeta + 1 + W + strideOf (2 * log2Delta b) : ℕ) : ℤ) ≤
        (Nat.sqrt (4 * ((uMin : ℤ) * (q - xi)) * log2Delta b).toNat : ℤ)) &&
      decide (maxBeta + 1 + W ≤ d0 uMin q xi b))

theorem PrimalHybrid.check_spec {K : Fx} {p : LWEParams} {m : Option ℕ} {q xi s : Fx} {z uMin W : ℕ}
    {Mz : ℤ} {b : ℕ} (hq : 0 ≤ q - xi) (hu : uMin ≤ p.n - z) (hDu : maxBeta + 1 + W ≤ uMin)
    (hm : ∀ M, m = some M → maxBeta + 1 + W + z ≤ M) (hW : c0 * W ≤ -(K + 21 * ONE))
    (h : check K uMin q xi s W b = true) :
    Expensive K p m q xi s z Mz (maxBeta + 1 + W) b := by
  unfold check at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
    exact Or.inl ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩
  obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h12
  have hδ := of_decide_eq_true h1
  have hmargin := of_decide_eq_true h2
  have hd0 := of_decide_eq_true h3
  right; right
  refine ⟨?_, le_trans hDu hu, ?_⟩
  · unfold rankOf
    refine le_trans ?_ (le_max_right _ _)
    have h0 := le_trans hd0 (d0_mono hu hq hδ)
    unfold d0 at h0
    apply le_min h0
    cases hmm : m with
    | none => simpa using h0
    | some M => have := hm M hmm; simp; omega
  · intro d hd eta heta heta4
    have hA : 0 ≤ 4 * ((uMin : ℤ) * (q - xi)) * log2Delta b := by
      have : (0 : ℤ) ≤ uMin * (q - xi) := mul_nonneg (by positivity) hq
      nlinarith
    apply profile_fail (u := p.n - z) (T := (Nat.sqrt (4 * ((uMin : ℤ) * (q - xi)) * log2Delta b).toNat : ℤ))
      hδ hq (by positivity) ?_ hmargin hW hd eta heta heta4
    have hsq := Nat.sqrt_le' (4 * ((uMin : ℤ) * (q - xi)) * log2Delta b).toNat
    have hsq' : (Nat.sqrt (4 * ((uMin : ℤ) * (q - xi)) * log2Delta b).toNat : ℤ) *
        (Nat.sqrt (4 * ((uMin : ℤ) * (q - xi)) * log2Delta b).toNat : ℤ) ≤
        4 * ((uMin : ℤ) * (q - xi)) * log2Delta b := by
      have := (Nat.cast_le (α := ℤ)).mpr hsq
      push_cast at this; rw [Int.toNat_of_nonneg hA] at this; linarith
    refine hsq'.trans ?_
    have : (uMin : ℤ) * (q - xi) ≤ ((p.n - z : ℕ) : ℤ) * (q - xi) :=
      Int.mul_le_mul_of_nonneg_right (by exact_mod_cast hu) hq
    nlinarith

end SigabaNeo.Lattices.Estimator

namespace SigabaNeo.Lattices.Estimator

open Fx NumPrimal PrimalHybrid Reduction

/-- **The primal attacks** (`bdd`, `bdd_hybrid`, `bdd_mitm_hybrid`) cost at least `K`, for a dense
bounded secret, when every block size passes `check` (at `uMin = n − Z₁` lattice coordinates), when
guessing `Z₁` coordinates already costs `K`, and when `W` Babai failures cost `K`. -/
theorem PrimalHybrid.estimate_ge {params : LWEParams} {mitm plain : Bool} {K : Fx} {Z₁ W : ℕ}
    {a b : ℤ} (hk : ∀ s, params.normalize.Xs.kind ≠ .gauss s)
    (hab : params.normalize.Xs.bounds.getD (0, 0) = (a, b)) (hB : 16 ≤ (b - a).toNat)
    (hhn : params.normalize.Xs.hammingWeight.toNat ≤ params.normalize.n)
    (h4 : 4 * (params.normalize.n - params.normalize.Xs.hammingWeight.toNat) ≤ params.normalize.n)
    (hq : 0 ≤ log2Nat params.normalize.q - Usvp.log2Xi params.normalize)
    (hK1 : K + 20 * ONE ≤ ((Z₁ : ℤ) - 1) * ONE)
    (hK2 : K + 20 * ONE ≤ (2 * params.normalize.Xs.hammingWeight.toNat : ℤ) * ONE)
    (hW : c0 * W ≤ -(K + 21 * ONE)) (hDu : maxBeta + 1 + W ≤ params.normalize.n - Z₁)
    (hm : ∀ M, (if params.normalize.Xs.stddev ≤ params.normalize.Xe.stddev then
      params.normalize.m.map (· + params.normalize.n) else params.normalize.m) = some M →
        maxBeta + 1 + W + Z₁ ≤ M)
    (hb : ∀ b < maxBeta + 2, check K (params.normalize.n - Z₁) (log2Nat params.normalize.q)
      (Usvp.log2Xi params.normalize) (log2 params.normalize.Xe.stddev) W b = true) :
    CostGe K (PrimalHybrid.estimate params mitm plain) := by
  set P := params.normalize
  set h := P.Xs.hammingWeight.toNat
  have hz : ∀ (top : ℕ), top ≤ maxBeta → ∀ z,
      CostGe K (zcost P mitm plain (if P.Xs.stddev ≤ P.Xe.stddev then P.m.map (· + P.n) else P.m)
        top (log2Nat P.q) (Usvp.log2Xi P) (log2 P.Xe.stddev) z) := by
    intro top htop z
    have hO := ONE_pos
    apply zcost_ge (Mz := min ((z : ℤ) - 1) (2 * h)) htop
      (le_min (by omega) (by omega)) (weights_bound P z mitm a b hab hk hB hhn h4)
    intro b' hb'
    by_cases hzZ : Z₁ ≤ z
    · right; left
      have : ((Z₁ : ℤ) - 1) * ONE ≤ ((z : ℤ) - 1) * ONE :=
        Int.mul_le_mul_of_nonneg_right (by omega) (le_of_lt hO)
      rw [min_def]; split <;> linarith
    · exact check_spec hq (by omega) hDu (fun M hM => by have := hm M hM; omega) hW (hb b' hb')
  unfold estimate
  simp only []
  split
  · simp
  simp only [Id.run_pure]
  have htop : ∀ mm : Option ℕ, (if (localMinimum 40 (max 45 (min maxBeta (mm.getD maxBeta))) 5
      fun b => Usvp.costGsa b P mm).2.isSome = true then
      (localMinimum 40 (max 45 (min maxBeta (mm.getD maxBeta))) 5 fun b => Usvp.costGsa b P mm).1
      else min maxBeta (mm.getD maxBeta)) ≤ maxBeta := by
    intro mm
    split
    · have := (NumPrimal.localMinimum_inv (fun _ => True) trivial 40
        (max 45 (min maxBeta (mm.getD maxBeta))) 5 (fun b => Usvp.costGsa b P mm)
        (fun _ _ _ => trivial) (lt_of_lt_of_le (by decide) (le_max_left 45 _))).2
      have h45 : (45 : ℕ) ≤ maxBeta := by decide
      have := max_le h45 (min_le_left maxBeta (mm.getD maxBeta))
      omega
    · exact min_le_left _ _
  split
  · exact hz _ (htop _) 0
  · exact NumPrimal.minimize_ge _ _ _ (hz _ (htop _))

end SigabaNeo.Lattices.Estimator
