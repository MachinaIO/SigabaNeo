import PE.Impl.ExpLUT.Prog.KeyTimeMatAddExact
/-! Asymmetric runtime bounds for the actual digit-accumulation kernel. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

def digitBodyTime (M N K : ℕ) : ℕ :=
  (2 * M + 5) + 2 * moveAllowance M + 3 * evalInstructionTime M N K

theorem layout_drop (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (d c : Fin 64) (hd : d ≠ c) :
    Cert (MVM.compile (.drop d c)) (layout M N K b) (layout M N K b) (moveAllowance M) := by
  have ht := compile_drop_scratch d c hd (layout M N K b) M h.top
  exact ht.mono le_rfl le_rfl (by unfold moveAllowance; gcongr; exact h.top (tR c))

theorem compile_digAccBody (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hu : b rTK1 ≤ b rUp)
    (hd : N * K ≤ b rDg) (hp : N * K ≤ b rPr) (ha : N * K ≤ b rDA) :
    Cert (MVM.compile digAccBody) (layout M N K b) (layout M N K b) (digitBodyTime M N K) := by
  have h0 := layout_copy M N K b h.top rUp rTK1 hu
  have h1 := layout_drop M N K b h rUp MVM.rDn (by decide)
  have h2 := layout_moveR M N K b h rEl rDE (by decide)
  have hs : operationBound M N K M ≤ evalInstructionTime M N K := by
    unfold evalInstructionTime; omega
  have h3 := (layout_op M N K b h .dig rDg rDX rUp hd).mono le_rfl le_rfl hs
  have h4 := (layout_op M N K b h .mul rPr rEl rDg hp).mono le_rfl le_rfl hs
  have h5 := (layout_op M N K b h .add rDA rDA rPr ha).mono le_rfl le_rfl hs
  rw [digAccBody]
  exact (h0.seq (h1.seq (h2.seq (h3.seq (h4.seq h5))))).mono le_rfl le_rfl
    (by unfold digitBodyTime; omega)

/-- These three temporary words are cleared after the loop; M also covers iteration zero. -/
def digitWide (M N K : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (Function.update (Function.update b rDA (N * K))
    rUp M) rDg M) rPr M

def digitBase (M N K : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (digitWide M N K b) MVM.rDn (b rTK)) rEl (N * K)

def digitClean (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (Function.update (Function.update b rUp 0) rEl 0) rDg 0) rPr 0

def digitResult (M N K : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ := digitClean (digitBase M N K b)

theorem digitWide_inputs (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) :
    RingInputs M N K (layout M N K (digitWide M N K b)) :=
  (((h.update_layout rDA (N * K) h.ring).update_layout rUp M le_rfl).update_layout rDg M le_rfl).update_layout rPr M le_rfl

theorem digitBase_inputs (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) :
    RingInputs M N K (layout M N K (digitBase M N K b)) :=
  ((digitWide_inputs M N K b h).update_layout MVM.rDn (b rTK)
    (by simpa using h.top (tR rTK))).update_layout rEl (N * K) h.ring

/-- The real two-copy prefix resets the loop counter and initial element word. -/
theorem compile_digAccPre (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (ha : b rDA ≤ N * K) (hz : b rZ ≤ N * K) :
    Cert (MVM.compile (.seq (.cp MVM.rDn rTK) (.cp rEl rZ)))
      (layout M N K b) (layout M N K (digitBase M N K b)) (2 * (2 * M + 5)) := by
  let c := digitWide M N K b
  let c1 := Function.update c MVM.rDn (b rTK)
  have hi := digitWide_inputs M N K b h
  have hi1 : RingInputs M N K (layout M N K c1) := hi.update_layout MVM.rDn (b rTK)
    (by simpa using h.top (tR rTK))
  have h0 : Cert (MVM.compile (.cp MVM.rDn rTK)) (layout M N K c) (layout M N K c1)
      (2 * M + 5) := by simpa [c, c1, digitWide] using layout_copy_update M N K c hi.top MVM.rDn rTK
  have h1 := layout_copy_cap M N K c1 hi1.top rEl rZ (N * K) (by simpa [c1, c, digitWide] using hz)
  apply (h0.seq h1).mono _ le_rfl (by omega)
  apply layout_mono
  have hb : ∀ r, b r ≤ M := fun r ↦ by simpa using h.top (tR r)
  intro r
  by_cases h0 : r = rDA <;> by_cases h1 : r = rUp <;>
    by_cases h2 : r = rDg <;> by_cases h3 : r = rPr <;>
    simp_all [c, digitWide]

/-- Explicit cleanup is reflected in zero final caps, rather than retained loop maxima. -/
theorem compile_digAccClean (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) :
    Cert (MVM.compile (.seq (.clr rUp) (.seq (.clr rEl) (.seq (.clr rDg) (.clr rPr)))))
      (layout M N K b) (layout M N K (digitClean b)) (4 * (2 * M + 5)) := by
  have h0 := layout_clear_update M N K b h.top rUp
  have hi0 := h.update_layout rUp 0 (Nat.zero_le _)
  have h1 := layout_clear_update M N K _ hi0.top rEl
  have hi1 := hi0.update_layout rEl 0 (Nat.zero_le _)
  have h2 := layout_clear_update M N K _ hi1.top rDg
  have hi2 := hi1.update_layout rDg 0 (Nat.zero_le _)
  have h3 := layout_clear_update M N K _ hi2.top rPr
  exact (h0.seq (h1.seq (h2.seq h3))).mono le_rfl le_rfl (by omega)

/-- Actual initialization, K digit rounds, and cleanup, with no old scratch-cap restrictions. -/
theorem compile_digAccC (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (ha : b rDA ≤ N * K) (hz : b rZ ≤ N * K)
    (hk : b rTK ≤ R) :
    Cert (MVM.compile digAccC) (layout M N K b) (layout M N K (digitResult M N K b))
      (6 * (2 * M + 5) + R * (2 * M + digitBodyTime M N K + 4) + 2) := by
  let c := digitWide M N K b
  let c1 := Function.update c MVM.rDn (b rTK)
  let c2 := digitBase M N K b
  have hi := digitWide_inputs M N K b h
  have hi1 : RingInputs M N K (layout M N K c1) := hi.update_layout MVM.rDn (b rTK)
    (by simpa using h.top (tR rTK))
  have hi2 := digitBase_inputs M N K b h
  have h0 : Cert (MVM.compile (.cp MVM.rDn rTK)) (layout M N K c) (layout M N K c1)
      (2 * M + 5) := by simpa [c, c1, digitWide] using layout_copy_update M N K c hi.top MVM.rDn rTK
  have h1 := layout_copy_cap M N K c1 hi1.top rEl rZ (N * K) (by simpa [c1, c, digitWide] using hz)
  have hb := compile_digAccBody M N K c2 hi2
    (by simpa [c2, digitBase, digitWide] using h.top (tR rTK1))
    (by simpa [c2, digitBase, digitWide] using h.ring)
    (by simpa [c2, digitBase, digitWide] using h.ring) (by simp [c2, digitBase, digitWide])
  have hl := rep_fixed MVM.rDn digAccBody (layout M N K c2) M R (digitBodyTime M N K)
    hi2.top (by simpa [c2, digitBase, digitWide] using hk) hb
  have hc := compile_digAccClean M N K c2 hi2
  rw [digAccC]
  apply (h0.seq (h1.seq (hl.seq hc))).mono _ le_rfl (by omega)
  apply layout_mono
  have hb : ∀ r, b r ≤ M := fun r ↦ by simpa using h.top (tR r)
  intro r
  by_cases h0 : r = rDA <;> by_cases h1 : r = rUp <;>
    by_cases h2 : r = rDg <;> by_cases h3 : r = rPr <;>
    simp_all [c, digitWide]

theorem digitResult_inputs (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) :
    RingInputs M N K (layout M N K (digitResult M N K b)) :=
  ((((digitBase_inputs M N K b h).update_layout rUp 0 (Nat.zero_le _)).update_layout
    rEl 0 (Nat.zero_le _)).update_layout rDg 0 (Nat.zero_le _)).update_layout rPr 0 (Nat.zero_le _)

theorem digitResult_fields (M N K : ℕ) (b : Fin 64 → ℕ) :
    digitResult M N K b rDA = N * K ∧ digitResult M N K b MVM.rDn = b rTK ∧
    digitResult M N K b rUp = 0 ∧ digitResult M N K b rEl = 0 ∧
    digitResult M N K b rDg = 0 ∧ digitResult M N K b rPr = 0 := by
  simp [digitResult, digitClean, digitBase, digitWide]

theorem digitResult_other (M N K : ℕ) (b : Fin 64 → ℕ) (r : Fin 64)
    (ha : r ≠ rDA) (hn : r ≠ MVM.rDn) (hu : r ≠ rUp) (he : r ≠ rEl)
    (hd : r ≠ rDg) (hp : r ≠ rPr) : digitResult M N K b r = b r := by
  simp [digitResult, digitClean, digitBase, digitWide, Function.update_of_ne, ha, hn, hu, he, hd, hp]

set_option exponentiation.threshold 1000 in
/-- Concrete digit accumulation has K iterations and restores its temporary words to zero. -/
theorem compile_digAccC_concrete (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (ha : b rDA ≤ 2 ^ 24 * 2 ^ 16) (hz : b rZ ≤ 2 ^ 24 * 2 ^ 16) (hk : b rTK ≤ 2 ^ 16) :
    Cert (MVM.compile digAccC) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) (digitResult (2 ^ 120) (2 ^ 24) (2 ^ 16) b)) (2 ^ 363) := by
  have hf := compile_digAccC (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) b h ha hz hk
  have ht := evalInstructionTime_concrete
  apply hf.mono le_rfl le_rfl
  unfold digitBodyTime
  calc
    _ ≤ 6 * (2 * 2 ^ 120 + 5) + 2 ^ 16 * (2 * 2 ^ 120 +
        ((2 * 2 ^ 120 + 5) + 2 * moveAllowance (2 ^ 120) + 3 * 2 ^ 341) + 4) + 2 := by gcongr
    _ ≤ 2 ^ 363 := by norm_num [moveAllowance]

end AdvancedEncryption.ExpLUT.Prog.KeyTime
