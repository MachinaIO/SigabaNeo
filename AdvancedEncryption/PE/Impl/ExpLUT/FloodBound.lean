import PE.Impl.ExpLUT.Hybrid12
import PE.Impl.ExpLUT.Noise
import SigabaNeo.Lib.Lattices.FloodRing

/-!
# The flooding hypothesis of hybrid H2 over `ℤ_Q[X]/(X^n + 1)`

For the flooding law `floodRing n Q W` (coefficients uniform below `W`, P's `χfl`) and an error law
`χ` whose samples have norm at most `B_χ`:

* `closeTo_iidFam_floodRing_add`: an independent family shifted entrywise by elements of norm at
  most `B` moves by at most `#entries · n B / W` (`closeTo_pi_floodRing_add_le` twice);
* `closeTo_floodLaw_add_le`: D's `floodLaw S Pos χfl` (four independent families) shifted by any
  `fl : FloodV S Pos` with entries of norm at most `B` moves by at most `floodCount S Pos · n B / W`;
* `cnorm_floodShift_le`: the entries of `floodShift ē_b zr` are sums of at most `m̄` entries of
  `ē_b` (possibly negated and under `σ_{g_t}`, a signed permutation of the coefficients), so their
  norm is at most `m̄ B_χ` when the entries of `ē_b` are within `B_χ`;
* **`hflood_floodRing`**: the hypothesis `hflood` of `hybrid2_close` at
  `ε = floodCount S Pos · n (m̄ B_χ) / W`.
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Cslib Cslib.Probability Matrix
open scoped ENNReal

variable {Q n : ℕ} [NeZero Q]

/-- **Flooding of an independent family of rows.** -/
theorem closeTo_iidFam_floodRing_add {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι]
    [DecidableEq ι] (W : ℕ) [NeZero W] (δ : κ → ι → Negacyclic (ZMod Q) n) {B : ℕ}
    (hδ : ∀ k i, cnorm (δ k i) ≤ B) :
    CloseTo ((iidFam (floodRing n Q W) κ ι).map (· + δ)) (iidFam (floodRing n Q W) κ ι)
      (Fintype.card κ * (Fintype.card ι * (((n * B : ℕ) : ℝ≥0∞) / W))) := by
  have e : (iidFam (floodRing n Q W) κ ι).map (· + δ) =
      PMF.pi fun k => (iidLaw (floodRing n Q W) ι).map (· + δ k) := by
    unfold iidFam; rw [PMF.pi_map]; rfl
  rw [e]
  have h := closeTo_pi (fun k => (iidLaw (floodRing n Q W) ι).map (· + δ k))
    (fun _ => iidLaw (floodRing n Q W) ι) (fun _ => Fintype.card ι * (((n * B : ℕ) : ℝ≥0∞) / W))
    fun k => closeTo_pi_floodRing_add_le W (δ k) (hδ k)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  exact h

variable {S : Setting (Negacyclic (ZMod Q) n)} {Pos : Type} [Fintype Pos] [DecidableEq Pos]

variable (S Pos) in
/-- The number of flooded ring elements: the digit encodings of the `C_{g_t}`, the `C^in_t`, their
digit encodings, `c₀`. -/
def floodCount : ℕ :=
  Fintype.card (Fin S.b × Dig S.τ) * Fintype.card (Col S.τ) +
    Fintype.card Pos * Fintype.card (Col S.τ) +
    Fintype.card (Pos × Dig S.τ) * Fintype.card (Col S.τ) + Fintype.card (Col S.τ)

omit [DecidableEq Pos] in
theorem floodCount_eq : floodCount S Pos =
    S.b * (2 * (2 * S.τ) * S.τ) * (2 * S.τ) + Fintype.card Pos * (2 * S.τ) +
      Fintype.card Pos * (2 * (2 * S.τ) * S.τ) * (2 * S.τ) + 2 * S.τ := by
  simp only [floodCount, Fintype.card_prod, Fintype.card_fin]
  ring

omit [DecidableEq Pos] in
/-- The flooding law moved by a shift, factor by factor. -/
theorem floodLaw_map_add (χfl : PMF (Negacyclic (ZMod Q) n)) (fl : FloodV S Pos) :
    (floodLaw S Pos χfl).map (· + fl) =
      ((iidFam χfl (Fin S.b × Dig S.τ) (Col S.τ)).map (· + fun td => fl.1 td.1 td.2)).bind
        fun eaut => ((iidFam χfl Pos (Col S.τ)).map (· + fl.2.1)).bind fun ein =>
        ((iidFam χfl (Pos × Dig S.τ) (Col S.τ)).map (· + fun td => fl.2.2.1 td.1 td.2)).bind
          fun edin => ((iidLaw χfl (Col S.τ)).map (· + fl.2.2.2)).map fun e0 =>
            ((fun t d => eaut (t, d)), ein, (fun t d => edin (t, d)), e0) := by
  unfold floodLaw
  simp only [PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
  rfl

/-- **Flooding of D's flooding errors**: shifted by any `fl` with entries of norm at most `B`, within
`floodCount S Pos · n B / W`. -/
theorem closeTo_floodLaw_add_le (W : ℕ) [NeZero W] (fl : FloodV S Pos) {B : ℕ}
    (h1 : ∀ t d c, cnorm (fl.1 t d c) ≤ B) (h2 : ∀ t c, cnorm (fl.2.1 t c) ≤ B)
    (h3 : ∀ t d c, cnorm (fl.2.2.1 t d c) ≤ B) (h4 : ∀ c, cnorm (fl.2.2.2 c) ≤ B) :
    CloseTo ((floodLaw S Pos (floodRing n Q W)).map (· + fl)) (floodLaw S Pos (floodRing n Q W))
      (floodCount S Pos * (((n * B : ℕ) : ℝ≥0∞) / W)) := by
  rw [floodLaw_map_add]
  have ha := closeTo_iidFam_floodRing_add (κ := Fin S.b × Dig S.τ) (ι := Col S.τ) W
    (fun td => fl.1 td.1 td.2) fun td c => h1 td.1 td.2 c
  have hb := closeTo_iidFam_floodRing_add (κ := Pos) (ι := Col S.τ) W fl.2.1 h2
  have hc := closeTo_iidFam_floodRing_add (κ := Pos × Dig S.τ) (ι := Col S.τ) W
    (fun td => fl.2.2.1 td.1 td.2) fun td c => h3 td.1 td.2 c
  have hd := closeTo_pi_floodRing_add_le (ι := Col S.τ) W fl.2.2.2 h4
  have h := ha.bind fun eaut _ => hb.bind fun ein _ => hc.bind fun edin _ =>
    hd.map fun e0 => (((fun t d => eaut (t, d)), ein, (fun t d => edin (t, d)), e0) : FloodV S Pos)
  unfold floodLaw
  refine h.mono (le_of_eq ?_)
  unfold floodCount
  push_cast
  ring

/-! ### The shifts of hybrid H2 -/

omit [NeZero Q] in
/-- `cnorm (v · bv z) ≤ |Wb| B` for entries of `v` within `B`. -/
theorem cnorm_dot_bv_le {Wb : Type} [Fintype Wb] (v : Wb → Negacyclic (ZMod Q) n) (z : Wb → Bool)
    {B : ℕ} (hv : ∀ w, cnorm (v w) ≤ B) : cnorm (v ⬝ᵥ bv z) ≤ Fintype.card Wb * B := by
  unfold dotProduct
  refine (cnorm_sum_le _ _).trans ?_
  calc ∑ w, cnorm (v w * bv z w) ≤ ∑ _w : Wb, B := Finset.sum_le_sum fun w _ => by
        unfold bv bitVal
        cases z w
        · simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, cnorm_zero]; exact Nat.zero_le _
        · simp only [↓reduceIte, mul_one]; exact hv w
    _ = Fintype.card Wb * B := by simp

omit [NeZero Q] [Fintype Pos] [DecidableEq Pos] in
/-- **The entries of `floodShift ē_b zr`** have norm at most `|Wb| B_χ` when the entries of `ē_b`
on the `Ā` columns have norm at most `B_χ`. -/
theorem cnorm_floodShift_le (NS : NormSpec S) (hN : ∀ a, NS.nrm a = cnorm a) {Wb : Type}
    [Fintype Wb] (eb : BCol Wb S.τ → Negacyclic (ZMod Q) n) (zr : PrI S Pos → Wb → Bool) {B : ℕ}
    (heb : ∀ w, cnorm (eb (.inl w)) ≤ B) :
    (∀ t d c, cnorm ((floodShift eb zr).1 t d c) ≤ Fintype.card Wb * B) ∧
      (∀ t c, cnorm ((floodShift eb zr).2.1 t c) ≤ Fintype.card Wb * B) ∧
      (∀ t d c, cnorm ((floodShift eb zr).2.2.1 t d c) ≤ Fintype.card Wb * B) ∧
      (∀ c, cnorm ((floodShift eb zr).2.2.2 c) ≤ Fintype.card Wb * B) := by
  have hd := fun z => cnorm_dot_bv_le (fun w => eb (.inl w)) z heb
  refine ⟨fun t d c => ?_, fun t c => hd _, fun t d c => ?_, fun c => ?_⟩
  · show cnorm (-S.E.σ (S.kf t) _) ≤ _
    rw [cnorm_neg, ← hN]
    exact (NS.nrm_σ _ _ (S.idx_odd _)).trans (by rw [hN]; exact hd _)
  · show cnorm (-_) ≤ _
    rw [cnorm_neg]; exact hd _
  · show cnorm (-_) ≤ _
    rw [cnorm_neg]; exact hd _

/-- **The flooding hypothesis of hybrid H2** for the flooding law `floodRing n Q W` and an error law
with samples of norm at most `B_χ`. -/
theorem hflood_floodRing (NS : NormSpec S) (hN : ∀ a, NS.nrm a = cnorm a) {Wb : Type} [Fintype Wb]
    (W : ℕ) [NeZero W] {χ : PMF (Negacyclic (ZMod Q) n)} {Bχ : ℕ}
    (hχ : ∀ a ∈ χ.support, cnorm a ≤ Bχ) :
    ∀ eb ∈ (iidLaw χ (BCol Wb S.τ)).support, ∀ zr : PrI S Pos → Wb → Bool,
      CloseTo ((floodLaw S Pos (floodRing n Q W)).map (· + floodShift eb zr))
        (floodLaw S Pos (floodRing n Q W))
        (floodCount S Pos * (((n * (Fintype.card Wb * Bχ) : ℕ) : ℝ≥0∞) / W)) := by
  intro eb heb zr
  obtain ⟨h1, h2, h3, h4⟩ := cnorm_floodShift_le NS hN eb zr fun w =>
    hχ _ (mem_support_iidLaw heb (.inl w))
  exact closeTo_floodLaw_add_le W _ h1 h2 h3 h4

end AdvancedEncryption.ExpLUT
