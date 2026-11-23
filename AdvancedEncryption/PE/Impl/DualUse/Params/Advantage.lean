import PE.Impl.DualUse.Params.Stat

/-!
# Attribute hiding for the configuration covering simulated keys

For `confP`, every hypothesis of `DualUse.advantage_le` but the Ring-LWE ones is discharged:
the gadget decomposition (`hdecp`), real keys covered (`realCovered_conf`), flooding within
`2^{-148}` (`flood_conf`), and the statistical terms `δ₁, δ₆ ≤ 2^{-180}` (`delta1_le`,
`delta6_le`). So for every adversary `A` and distinguisher `D`, the real and ideal experiments
differ by at most `δ₃ + δ₅ + δ_I + 2^{-135}`, the three Ring-LWE advantages of the reductions'
experiments plus a negligible term (`advantage_le_conf`).
-/

namespace AdvancedEncryption.DualUse.Params

open SigabaNeo SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow
open scoped ENNReal

theorem two_pow_mul_inv (a b : ℕ) :
    (2 : ℝ≥0∞) ^ a * ((2 : ℝ≥0∞) ^ (a + b))⁻¹ = ((2 : ℝ≥0∞) ^ b)⁻¹ := by
  rw [pow_add, ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero))
    (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)), ← mul_assoc,
    ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
    one_mul]

theorem card_date : ((Fintype.card Date : ℕ) : ℝ≥0∞) = 2 ^ 10 := by
  rw [show Fintype.card Date = 2 ^ 10 by simp [Date, DateWindow.Sym]]; push_cast; norm_num

/-- A term summed over a set of at most `2^a` elements: `|A| · 2^{-(a + t)} ≤ 2^{-t'}` for
`t' ≤ t`. -/
theorem card_mul_le {A : Type*} [Fintype A] {a t t' : ℕ} (hA : (Fintype.card A : ℝ≥0∞) ≤ 2 ^ a)
    (ht : t' ≤ t) {δ : ℝ≥0∞} (h : δ ≤ ((2 : ℝ≥0∞) ^ (a + t))⁻¹) :
    (Fintype.card A : ℝ≥0∞) * δ ≤ ((2 : ℝ≥0∞) ^ t')⁻¹ :=
  calc (Fintype.card A : ℝ≥0∞) * δ ≤ 2 ^ a * ((2 : ℝ≥0∞) ^ (a + t))⁻¹ := by gcongr
    _ = ((2 : ℝ≥0∞) ^ t)⁻¹ := two_pow_mul_inv a t
    _ ≤ ((2 : ℝ≥0∞) ^ t')⁻¹ := ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ (by norm_num) ht)

theorem date_mul_le {δ : ℝ≥0∞} (h : δ ≤ ((2 : ℝ≥0∞) ^ 180)⁻¹) :
    (Fintype.card Date : ℝ≥0∞) * δ ≤ ((2 : ℝ≥0∞) ^ 138)⁻¹ :=
  card_mul_le (a := 10) (t := 170) card_date.le (by norm_num) h

variable {ms : Machines hkp confP}

/-- **Attribute hiding for `confP`**: the advantage of any distinguisher is at most the Ring-LWE
advantages of the three experiments-as-distinguishers plus `2^{-135}`. -/
theorem advantage_le_conf (A : Machine 3) (D : Machine) {δ₃ δ₅ δI : ℝ≥0∞}
    (h₃ : CloseTo ((inst3Real (k := kp) (χR confP)).bind fun ab =>
        (G (hk := hkp) A fun x => F3 hkp confP x ab).bind (Dc D))
      (inst3Unif.bind fun ab => (G (hk := hkp) A fun x => F3 hkp confP x ab).bind (Dc D)) δ₃)
    (h₅ : CloseTo ((nfReal (χR confP)).bind fun i =>
        (G (hk := hkp) A fun x => F5 hkp confP x i).bind (Dc D))
      (nfUnif.bind fun i => (G (hk := hkp) A fun x => F5 hkp confP x i).bind (Dc D)) δ₅)
    (hI : CloseTo ((inst3Real (k := kp) (χR confP)).bind fun ab =>
        (G (hk := hkp) A fun x => FI hkp confP x ab).bind (Dc D))
      (inst3Unif.bind fun ab => (G (hk := hkp) A fun x => FI hkp confP x ab).bind (Dc D)) δI)
    (hfin : δ₃ + δ₅ + δI ≠ ⊤) :
    |D.acceptProb ((PE.real dateUniverse params (impl hkp confP ms) A).map view) -
        D.acceptProb ((PE.ideal dateUniverse params (impl hkp confP ms) (simMachine hkp confP) A).map
          view)| ≤ (δ₃ + δ₅ + δI + ((2 : ℝ≥0∞) ^ 135)⁻¹).toReal := by
  set x : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ 138)⁻¹
  have h1 := date_mul_le delta1_le
  have h6 := date_mul_le delta6_le
  have hε : (Fintype.card Date : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 148)⁻¹ ≤ x := by
    rw [card_date]; exact le_of_eq (two_pow_mul_inv 10 138)
  have hsum : (Fintype.card Date * delta1 (Sdw (N := Np) hkp) (Fin confP.d) +
        Fintype.card Date * ((2 : ℝ≥0∞) ^ 148)⁻¹ + δ₃ + δ₅ +
        Fintype.card Date * delta6 (Sdw (N := Np) hkp) (Fin confP.d)) +
      (Fintype.card Date * delta1 (Sdw (N := Np) hkp) (Fin confP.d) + δI +
        Fintype.card Date * delta1 (Sdw (N := Np) hkp) (Fin confP.d)) ≤
      δ₃ + δ₅ + δI + ((2 : ℝ≥0∞) ^ 135)⁻¹ :=
    calc _ ≤ (x + x + δ₃ + δ₅ + x) + (x + δI + x) :=
          add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h1 hε) le_rfl) le_rfl) h6)
            (add_le_add (add_le_add h1 le_rfl) h1)
      _ = δ₃ + δ₅ + δI + 5 * x := by ring
      _ ≤ δ₃ + δ₅ + δI + 2 ^ 3 * x := by gcongr; norm_num
      _ = δ₃ + δ₅ + δI + ((2 : ℝ≥0∞) ^ 135)⁻¹ := by rw [two_pow_mul_inv 3 135]
  have htop : δ₃ + δ₅ + δI + ((2 : ℝ≥0∞) ^ 135)⁻¹ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hfin, ENNReal.inv_ne_top.mpr (pow_ne_zero _ two_ne_zero)⟩
  exact (advantage_le hdecp realCovered_conf A D flood_conf h₃ h₅ hI
    (ne_top_of_le_ne_top htop hsum)).trans (ENNReal.toReal_mono htop hsum)

end AdvancedEncryption.DualUse.Params
