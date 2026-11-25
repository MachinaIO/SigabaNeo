import PE.Impl.RingBTVW.KeyGen
import SigabaNeo.Lib.Lattices.Boxes

/-!
# The boxes of key generation

The short part of a key, `KeyShort (Fin d) Wt R` over `R = ℤ_Q[X]/(X^N + 1)`, is a vector of
`n = (d + |Wt|) N` coefficients (`keyEquiv`). The big box is the image of `n B` fair bits
(`keyEmb`, centered residues), the small box and the inner box are the products of balls of radii
`S` and `S − τ` (`keyBall`). With `S = 2^{B−1} − 1 − τ`, a shift by at most `τ` in every coefficient
maps the small box into the big box and the inner box into the small box (`add_mem_big`,
`sub_mem_small`), and the abort probability is at most `n (4τ + 1) / 2^B` (`abort_le`).
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo.Lattices Matrix Cslib
open scoped ENNReal

variable {N Q : ℕ} [NeZero Q] {d : ℕ} {Wt : Type} [Fintype Wt] [DecidableEq Wt]

/-- The positions of the coefficients of a key. -/
abbrev Coef (d : ℕ) (Wt : Type) (N : ℕ) := (Fin d ⊕ Wt) × Fin N

/-- The coefficients of the short part of a key. -/
def keyEquiv : KeyShort (Fin d) Wt (Negacyclic (ZMod Q) N) ≃ (Coef d Wt N → ZMod Q) :=
  (Equiv.sumArrowEquivProdArrow _ _ _).symm.trans
    ((Equiv.arrowCongr (Equiv.refl _) Negacyclic.coeffsEquiv).trans (Equiv.curry _ _ _).symm)

theorem keyEquiv_inl (v : KeyShort (Fin d) Wt (Negacyclic (ZMod Q) N)) (i : Fin d) (j : Fin N) :
    keyEquiv v (.inl i, j) = (v.1 i).coeffs j := rfl

theorem keyEquiv_inr (v : KeyShort (Fin d) Wt (Negacyclic (ZMod Q) N)) (r : Wt) (j : Fin N) :
    keyEquiv v (.inr r, j) = (v.2 r).coeffs j := rfl

theorem keyEquiv_add (u v : KeyShort (Fin d) Wt (Negacyclic (ZMod Q) N)) :
    keyEquiv (u + v) = keyEquiv u + keyEquiv v := by
  funext ⟨i, j⟩
  rcases i with i | i <;> simp [keyEquiv_inl, keyEquiv_inr, Negacyclic.coeffs_add]

theorem keyEquiv_sub (u v : KeyShort (Fin d) Wt (Negacyclic (ZMod Q) N)) :
    keyEquiv (u - v) = keyEquiv u - keyEquiv v := by
  funext ⟨i, j⟩
  rcases i with i | i <;> simp [keyEquiv_inl, keyEquiv_inr, Negacyclic.coeffs_sub]

/-- The keys within `r` in every coefficient. -/
def keyBall (Q : ℕ) [NeZero Q] (d : ℕ) (Wt : Type) [Fintype Wt] [DecidableEq Wt] (N r : ℕ) :
    Finset (KeyShort (Fin d) Wt (Negacyclic (ZMod Q) N)) :=
  (ball Q r).map keyEquiv.symm.toEmbedding

theorem mem_keyBall {r : ℕ} {v : KeyShort (Fin d) Wt (Negacyclic (ZMod Q) N)} :
    v ∈ keyBall Q d Wt N r ↔ ∀ i, zabs (keyEquiv v i) ≤ r := by
  simp only [keyBall, Finset.mem_map_equiv, Equiv.symm_symm]
  exact mem_ball

theorem cnorm_of_mem_keyBall {r : ℕ} {v : KeyShort (Fin d) Wt (Negacyclic (ZMod Q) N)}
    (hv : v ∈ keyBall Q d Wt N r) : (∀ i, cnorm (v.1 i) ≤ r) ∧ ∀ i, cnorm (v.2 i) ≤ r := by
  rw [mem_keyBall] at hv
  refine ⟨fun i => (cnorm_le_iff _ _).mpr fun j => hv (.inl i, j),
    fun i => (cnorm_le_iff _ _).mpr fun j => hv (.inr i, j)⟩

/-- The bits of the big box. -/
noncomputable def bitsOfKey (d : ℕ) (Wt : Type) [Fintype Wt] (N B m : ℕ)
    (hm : Fintype.card (Coef d Wt N) * B = m) :
    (Fin m → Bool) ≃ (Coef d Wt N → Fin B → Bool) :=
  (Equiv.arrowCongr (Fintype.equivFinOfCardEq (by rw [Fintype.card_prod, Fintype.card_fin, hm])).symm
    (Equiv.refl Bool)).trans
    (Equiv.curry _ _ _)

/-- **The big box** as the image of fair bits. -/
noncomputable def keyEmb (B : ℕ) (hB : 2 ^ B ≤ Q) (m : ℕ) (hm : Fintype.card (Coef d Wt N) * B = m) :
    (Fin m → Bool) ↪ KeyShort (Fin d) Wt (Negacyclic (ZMod Q) N) :=
  (bitsOfKey d Wt N B m hm).toEmbedding.trans
    ((Function.Embedding.piCongrRight fun _ => cenEmb B hB).trans keyEquiv.symm.toEmbedding)

theorem univ_map_keyEmb (B : ℕ) (hB : 2 ^ B ≤ Q) (m : ℕ) (hm : Fintype.card (Coef d Wt N) * B = m) :
    Finset.univ.map (keyEmb (d := d) (Wt := Wt) (N := N) B hB m hm) =
      (bigBox B hB).map keyEquiv.symm.toEmbedding := by
  rw [keyEmb, ← Finset.map_map, ← Finset.map_map, bigBox]
  congr 2
  exact Finset.map_univ_equiv _

theorem keyBall_subset_big (B : ℕ) (hB : 2 ^ B ≤ Q) (hB1 : 1 ≤ B) (m : ℕ)
    (hm : Fintype.card (Coef d Wt N) * B = m) :
    keyBall Q d Wt N (2 ^ (B - 1) - 1) ⊆
      Finset.univ.map (keyEmb (d := d) (Wt := Wt) (N := N) B hB m hm) := by
  rw [univ_map_keyEmb, keyBall]
  exact Finset.map_subset_map.mpr (ball_subset_bigBox B hB hB1)

/-- A shift by at most `τ` keeps a key of `keyBall S` within `S + τ`. -/
theorem add_mem_keyBall {S τ : ℕ} {y T : KeyShort (Fin d) Wt (Negacyclic (ZMod Q) N)}
    (hy : y ∈ keyBall Q d Wt N S) (hT : ∀ i, zabs (keyEquiv T i) ≤ τ) :
    y + T ∈ keyBall Q d Wt N (S + τ) := by
  rw [mem_keyBall] at hy ⊢
  intro i
  rw [keyEquiv_add, Pi.add_apply]
  exact (zabs_add_le _ _).trans (Nat.add_le_add (hy i) (hT i))

theorem sub_mem_keyBall {S τ : ℕ} {y T : KeyShort (Fin d) Wt (Negacyclic (ZMod Q) N)}
    (hy : y ∈ keyBall Q d Wt N S) (hT : ∀ i, zabs (keyEquiv T i) ≤ τ) :
    y - T ∈ keyBall Q d Wt N (S + τ) := by
  rw [mem_keyBall] at hy ⊢
  intro i
  rw [keyEquiv_sub, Pi.sub_apply]
  exact (zabs_sub_le _ _).trans (Nat.add_le_add (hy i) (hT i))

theorem keyBall_mono {r s : ℕ} (h : r ≤ s) : keyBall Q d Wt N r ⊆ keyBall Q d Wt N s := by
  intro v hv
  rw [mem_keyBall] at hv ⊢
  exact fun i => (hv i).trans h

/-- The coefficients of a key whose parts are within `τ`. -/
theorem zabs_keyEquiv_le {τ : ℕ} {T : KeyShort (Fin d) Wt (Negacyclic (ZMod Q) N)}
    (h1 : ∀ i, cnorm (T.1 i) ≤ τ) (h2 : ∀ i, cnorm (T.2 i) ≤ τ) :
    ∀ i, zabs (keyEquiv T i) ≤ τ := by
  rintro ⟨i | i, j⟩
  · exact (zabs_coeffs_le_cnorm _ j).trans (h1 i)
  · exact (zabs_coeffs_le_cnorm _ j).trans (h2 i)

/-- **The abort probability of box rejection** for the big box of `B` bits and the inner ball of
radius `2^{B−1} − 1 − 2τ`: at most `2^{−κ}` when `n (4τ + 1) 2^κ ≤ 2^B`. -/
theorem abort_le (B τ κ : ℕ) (hB : 2 ^ B ≤ Q) (hB1 : 1 ≤ B) (m : ℕ)
    (hm : Fintype.card (Coef d Wt N) * B = m) (hτ : 4 * τ + 1 ≤ 2 ^ B)
    (hκ : Fintype.card (Coef d Wt N) * (4 * τ + 1) * 2 ^ κ ≤ 2 ^ B) :
    (((Finset.univ.map (keyEmb (d := d) (Wt := Wt) (N := N) B hB m hm)).card -
        (keyBall Q d Wt N (2 ^ (B - 1) - 1 - 2 * τ)).card : ℕ) : ℝ≥0∞) /
      (Finset.univ.map (keyEmb (d := d) (Wt := Wt) (N := N) B hB m hm)).card ≤
        ((2 : ℝ≥0∞) ^ κ)⁻¹ := by
  set n := Fintype.card (Coef d Wt N)
  have hpow : 2 ^ B = 2 * 2 ^ (B - 1) := by rw [← pow_succ']; congr 1; omega
  have hcB : (Finset.univ.map (keyEmb (d := d) (Wt := Wt) (N := N) B hB m hm)).card =
      (2 ^ B) ^ n := by
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      ← hm, ← pow_mul, mul_comm]
  have hrad : 2 * (2 ^ (B - 1) - 1 - 2 * τ) + 1 = 2 ^ B - (4 * τ + 1) := by omega
  have hcI : (keyBall Q d Wt N (2 ^ (B - 1) - 1 - 2 * τ)).card = (2 ^ B - (4 * τ + 1)) ^ n := by
    rw [keyBall, Finset.card_map, card_ball _ (by omega), hrad]
  rw [hcB, hcI]
  have hdiff := pow_sub_pow_le (2 ^ B) (4 * τ + 1) hτ n
  have hA : (2 : ℝ≥0∞) ^ κ ≠ 0 := pow_ne_zero _ two_ne_zero
  have hA' : (2 : ℝ≥0∞) ^ κ ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  -- D 2^κ ≤ (2^B)^n
  have hD : ((2 ^ B) ^ n - (2 ^ B - (4 * τ + 1)) ^ n) * 2 ^ κ ≤ (2 ^ B) ^ n := by
    calc ((2 ^ B) ^ n - (2 ^ B - (4 * τ + 1)) ^ n) * 2 ^ κ
        ≤ n * (4 * τ + 1) * (2 ^ B) ^ (n - 1) * 2 ^ κ := Nat.mul_le_mul_right _ hdiff
      _ = n * (4 * τ + 1) * 2 ^ κ * (2 ^ B) ^ (n - 1) := by ring
      _ ≤ 2 ^ B * (2 ^ B) ^ (n - 1) := Nat.mul_le_mul_right _ hκ
      _ = (2 ^ B) ^ n := by rw [← pow_succ']; congr 1; omega
  refine ENNReal.div_le_of_le_mul ?_
  set D := (2 ^ B) ^ n - (2 ^ B - (4 * τ + 1)) ^ n
  calc ((D : ℕ) : ℝ≥0∞) = (D : ℝ≥0∞) * 2 ^ κ * (2 ^ κ)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hA hA', mul_one]
    _ ≤ (((2 ^ B) ^ n : ℕ) : ℝ≥0∞) * (2 ^ κ)⁻¹ := by
        gcongr
        exact_mod_cast hD
    _ = (2 ^ κ)⁻¹ * (((2 ^ B) ^ n : ℕ) : ℝ≥0∞) := mul_comm _ _

end AdvancedEncryption.RingBTVW
