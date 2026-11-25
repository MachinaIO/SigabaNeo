import PE.Impl.ExpLUT.Prog.RedKeyTCand
/-!
# Module 9: the clock of `mvSubC` (`18 := p − X u`, tight)

`|PIdx|` rows (counter `rVn`) of one inner product of length `|ZIdx|` (counter `rQc := rVm`),
each appending one ring word to register `18`. **`rktMvSubC`**: from `layout M N K b` to
`layout M N K (update b 18 (L N K))` with `L ≥ |rVn|`, `R ≥ |rVm|`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyT

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM
open AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Prog.KeyTime

def mvRowT (M N K R : ℕ) : ℕ :=
  3 * (2 * M + 5) + ipT M N K R + ((2 * M + 5) + mvT M N K + operationBound M N K (N * K) +
    (4 * (N * K) + 6) * (2 * M + 5))

/-- One row of `mvSubC`. The envelope has the word registers at `≥ N K` and `rQc ≥ |rVm|`. -/
theorem rktMvRowBody (M N K R : ℕ) (b : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K b))
    (hz : b rZ = N * K) (hx : N * K ≤ b rQx) (hy : N * K ≤ b rQy) (hia : N * K ≤ b rIa)
    (hqb : b rVu ≤ b rQb) (hqc : b rVm ≤ b rQc) (hR : b rVm ≤ R) (hs : b 18 + N * K ≤ M) :
    Cert (MVM.compile mvRowBody) (layout M N K b)
      (layout M N K (Function.update b 18 (b 18 + N * K))) (mvRowT M N K R) := by
  let b1 := Function.update b rIa (N * K)
  let b2 := Function.update b1 rQc (b rVm)
  have h1 : RingInputs M N K (layout M N K b1) := h.update_layout _ _ h.ring
  have h2 : RingInputs M N K (layout M N K b2) :=
    h1.update_layout _ _ (by simpa using h.top (tR rVm))
  have k2 (r : Fin 64) (h1 : r ≠ rQc) (h2 : r ≠ rIa) : b2 r = b r := by
    simp only [b2, b1, Function.update_of_ne h1, Function.update_of_ne h2]
  have k2a : b2 rIa = N * K := by simp [b2, b1]
  have k2c : b2 rQc = b rVm := by simp [b2]
  have p0 := layout_copy_update M N K b h.top rIa rZ
  rw [hz] at p0
  have p1 := layout_copy M N K b1 h1.top rQb rVu (by simpa [b1] using hqb)
  have p2 := layout_copy_update M N K b1 h1.top rQc rVm
  have e2 : b1 rVm = b rVm := by simp [b1]
  rw [e2] at p2
  have hc2 : QueueArithmeticCaps N K b2 :=
    ⟨by rw [k2 _ (by decide) (by decide)]; exact hx, by rw [k2 _ (by decide) (by decide)]; exact hy,
      k2a.ge, by rw [k2 _ (by decide) (by decide), k2 _ (by decide) (by decide), hz]; exact hx,
      by rw [k2 _ (by decide) (by decide), k2 _ (by decide) (by decide), hz]; exact hy⟩
  have pi := rktIpC M N K R b2 h2 hc2 (by rw [k2 _ (by decide) (by decide)]; exact hz.le)
    (by rw [k2c]; exact hR)
  have p3 := layout_copy M N K b2 h2.top rQx rZ
    (by rw [k2 _ (by decide) (by decide), k2 _ (by decide) (by decide), hz]; exact hx)
  have p4 := rktMvR M N K b2 h2 rQx 9 (by decide)
  have p5 := rktOpU M N K (N * K) b2 h2 .sub rQy rQx rIa k2a.le
  let b3 := Function.update b2 rQy (N * K)
  have h3 : RingInputs M N K (layout M N K b3) := h2.update_layout _ _ h.ring
  have p6 := layout_append M N K b3 h3.top 18 rQy
    (by simp only [b3, b2, b1, Function.update_apply]; simpa using hs)
  have e6 : b3 rQy = N * K := by simp [b3]
  have e7 : b3 18 = b 18 := by simp [b3, b2, b1]
  rw [e6, e7] at p6
  rw [mvRowBody, mvPre, mvPost]
  apply ((p0.seq (p1.seq p2)).seq (pi.seq (p3.seq (p4.seq (p5.seq p6))))).mono le_rfl _
    (by unfold mvRowT; omega)
  apply layout_mono
  intro r
  by_cases h18 : r = 18
  · subst r; simp
  by_cases hya : r = rQy
  · subst r; simpa [b3, b2, b1] using hy
  by_cases hca : r = rQc
  · subst r; simpa [b3, b2, b1] using hqc
  by_cases hia' : r = rIa
  · subst r; simpa [b3, b2, b1] using hia
  simp [b3, b2, b1, Function.update_of_ne h18, Function.update_of_ne hya, Function.update_of_ne hca,
    Function.update_of_ne hia']

def mvSubT (M N K R L : ℕ) : ℕ := 2 * (2 * M + 5) + (L * (2 * M + mvRowT M N K R + 4) + 2)

/-- **`mvSubC`** (tight). -/
theorem rktMvSubC (M N K R L : ℕ) (b : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K b))
    (hz : b rZ = N * K) (hx : N * K ≤ b rQx) (hy : N * K ≤ b rQy) (hia : N * K ≤ b rIa)
    (hqb : b rVu ≤ b rQb) (hqc : b rVm ≤ b rQc) (hR : b rVm ≤ R) (hqa : b 16 ≤ b rQa)
    (hL : b rVn ≤ L) (hs : L * (N * K) ≤ M) :
    Cert (MVM.compile mvSubC) (layout M N K b)
      (layout M N K (Function.update b 18 (L * (N * K)))) (mvSubT M N K R L) := by
  let γ := fun j ↦ layout M N K (Function.update b 18 (j * (N * K)))
  have hi (j : ℕ) (hj : j ≤ L) : RingInputs M N K (γ j) :=
    h.update_layout 18 _ ((Nat.mul_le_mul_right (N * K) hj).trans hs)
  have p0 := layout_clear_update M N K b h.top 18
  have h0 : RingInputs M N K (layout M N K (Function.update b 18 0)) := h.update_layout _ _ (by omega)
  have p1 := layout_copy M N K _ h0.top rQa 16 (by simpa using hqa)
  have p2 : Cert (MVM.compile (.rep rVn mvRowBody)) (layout M N K (Function.update b 18 0)) (γ L)
      (L * (2 * M + mvRowT M N K R + 4) + 2) := by
    apply rep_family rVn mvRowBody γ L (mvRowT M N K R) _ (by simp [γ]) (by simpa using hL)
    · intro j hj
      have hsize : (j + 1) * (N * K) ≤ M :=
        (Nat.mul_le_mul_right (N * K) (by omega : j + 1 ≤ L)).trans hs
      have hb := rktMvRowBody M N K R (Function.update b 18 (j * (N * K))) (hi j (by omega))
        (by simpa using hz) (by simpa using hx) (by simpa using hy) (by simpa using hia)
        (by simpa using hqb) (by simpa using hqc) (by simpa using hR)
        (by simpa only [Function.update_self, Nat.add_mul, Nat.one_mul] using hsize)
      simp only [Function.update_self, cap_reset] at hb
      rw [show j * (N * K) + N * K = (j + 1) * (N * K) by ring] at hb
      exact hb.mono (tailB_le (tR rVn) _) le_rfl le_rfl
    · intro j hj; exact SigabaNeo.Tape.Prog.supB_le_of (hi j (by omega)).top
    · intro j hj
      apply layout_mono
      intro r
      by_cases he : r = 18
      · subst r; simp only [Function.update_self]; exact Nat.mul_le_mul_right (N * K) hj
      · simp [Function.update_of_ne he]
  rw [mvSubC]
  exact (p0.seq (p1.seq p2)).mono le_rfl le_rfl (by unfold mvSubT; omega)

end AdvancedEncryption.ExpLUT.Prog.RedKeyT
