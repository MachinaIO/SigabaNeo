import SigabaNeo.Lib.Machines.Prog.Sample
import SigabaNeo.Lib.Machines.Prog.FrameSize

/-!
# The state count of `natP`

`natP t c n` doubles along the bits of `n`: its compiled machine has at most
`(log₂ n + 1) · (|dblP| + |bitAp|) + 36` states (`size_natP_le`).
-/

namespace SigabaNeo.Tape

namespace XProg

variable {k : ℕ}

theorem log2_div_two_succ {n : ℕ} (h : 2 ≤ n) : Nat.log2 (n / 2) + 1 = Nat.log2 n := by
  rw [Nat.log2_def n, if_pos h]

/-- **The state count of `natP`.** -/
theorem size_natP_le (t c : Fin k) : ∀ n : ℕ,
    (natP t c n).size ≤ (Nat.log2 n + 1) * ((dblP t c).size + (bitAp t false).size) + 36
  | 0 => by
    rw [natP]
    show (prog (Prog.prim (Prim.clear t))).size ≤ _
    simp [Prog.size, Prim.pad]
  | n + 1 => by
    rw [natP]
    have ih := size_natP_le t c ((n + 1) / 2)
    split_ifs with h
    · show (natP t c ((n + 1) / 2)).size + (dblP t c).size ≤ _
      have e : Nat.log2 ((n + 1) / 2) + 1 = Nat.log2 (n + 1) := log2_div_two_succ (by omega)
      rw [← e]
      nlinarith
    · show (natP t c ((n + 1) / 2)).size + (dblP t c).size + (bitAp t false).size ≤ _
      by_cases h1 : n = 0
      · subst h1
        simp only [Nat.reduceAdd, Nat.reduceDiv] at ih ⊢
        have : Nat.log2 1 = 0 := by decide
        have h0 : (natP t c 0).size = 36 := by
          rw [natP]; show (prog (Prog.prim (Prim.clear t))).size = 36; simp [Prog.size, Prim.pad]
        rw [this, h0]; omega
      · have e : Nat.log2 ((n + 1) / 2) + 1 = Nat.log2 (n + 1) := log2_div_two_succ (by omega)
        rw [← e]
        nlinarith
  decreasing_by all_goals omega

@[simp] theorem size_bitAp (t : Fin k) (b : Bool) : (bitAp t b).size = 60 := by
  simp [bitAp, Prog.size, Prim.pad]

@[simp] theorem size_dblP (t c : Fin k) : (dblP t c).size = 135 := by
  simp [dblP, forN, bitAp, Prog.size, Prim.pad]

/-- **The state count of `natP`** below a power of two. -/
theorem size_natP_lt (t c : Fin k) {n B : ℕ} (h : n < 2 ^ (B + 1)) :
    (natP t c n).size ≤ (B + 1) * 195 + 36 := by
  have h1 := size_natP_le t c n
  rw [size_dblP, size_bitAp] at h1
  have h2 : Nat.log2 n ≤ B := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Nat.log2_zero]
    · exact Nat.lt_succ_iff.mp ((Nat.log2_lt hn.ne').2 h)
  have : (Nat.log2 n + 1) * 195 ≤ (B + 1) * 195 := Nat.mul_le_mul_right _ (by omega)
  omega

end XProg

end SigabaNeo.Tape
