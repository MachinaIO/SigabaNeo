import PE.Impl.DualUse.Prog.SetupEncDescA

/-!
# Tight description-length arithmetic

`Machine.descLen A = 6 · S · 3^k · 3^ops · entryBits k S ops` with
`entryBits k S 0 = 4 + 4k + Nat.size S`. The earlier bound (`descLen_arithA`) charged
`Nat.size S ≤ S`; here `Nat.size S ≤ m` for `S ≤ B < 2^m`, so the entry width is
`4 + 4k + m` bits.
-/

set_option autoImplicit false

namespace AdvancedEncryption.ExpLUT.Prog.DescTight

open SigabaNeo

/-- **Tight description-length arithmetic**: for `S ≤ B < 2^m`, the entry width is at most
`4 + 4k + m`. -/
theorem descTight_arith {k S B m : ℕ} (h : S ≤ B) (hB : B < 2 ^ m) :
    6 * S * 3 ^ k * 3 ^ 0 * Machine.entryBits k S 0 ≤ 6 * B * 3 ^ k * (4 + 4 * k + m) := by
  have hs : Nat.size S ≤ m := Nat.size_le.mpr (lt_of_le_of_lt h hB)
  unfold Machine.entryBits
  simp only [pow_zero, mul_one, Nat.mul_zero, Nat.add_zero, Nat.size_zero]
  gcongr

end AdvancedEncryption.ExpLUT.Prog.DescTight
