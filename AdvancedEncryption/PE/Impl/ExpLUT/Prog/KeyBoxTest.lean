import PE.Impl.ExpLUT.Prog.KeyTryVM
import PE.Impl.ExpLUT.Prog.KeyBoxW
import SigabaNeoStd.Lattices.BallTest

/-! The VM's accumulated high-digit test is exactly small-box membership. -/
namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)

/-- The high-digit accumulator vanishes exactly inside the centered coefficient ball.
The digit-count bound rules out modular cancellation of nonzero test bits. -/
theorem sum_tstD_eq_zero_iff {N K : ℕ} [NeZero (2 ^ K - 1)] (B r : ℕ)
    (hBK : B ≤ K) (hr : 2 * r < 2 ^ B) (hq : 2 ^ (B + 1) ≤ 2 ^ K - 1)
    (hcount : 2 * (K - B) < 2 ^ K - 1) (x : Rq N K) :
    (∑ m ∈ Finset.range (K - B), tstD x (allC N (r : ZMod (2 ^ K - 1))) (B + m)) = 0 ↔
      cnorm x ≤ r := by
  let R : Rq N K := allC N (r : ZMod (2 ^ K - 1))
  let a : ℕ × Bool → Rq N K := fun t ↦ if t.2 then R - x else x + R
  let i : ℕ × Bool → ℕ := fun t ↦ B + t.1
  let s : Finset (ℕ × Bool) := (Finset.range (K - B)).product Finset.univ
  have hs : s.card < 2 ^ K - 1 := by simpa [s, mul_comm] using hcount
  have he : (∑ t ∈ s, binaryDigit (a t) (i t)) =
      ∑ m ∈ Finset.range (K - B), tstD x R (B + m) := by
    simp [s, Finset.sum_product, a, i, tstD, add_comm]
  have hz := sum_binaryDigit_eq_zero_iff s a i hs
  rw [he] at hz
  constructor
  · intro h
    have ht := hz.mp h
    apply (cnorm_le_iff_digits (Nat.sub_le (2 ^ K) 1) B r hr hq x).mpr
    intro j hj hjK
    have hm : j - B ∈ Finset.range (K - B) := Finset.mem_range.mpr (by omega)
    have hp := ht (j - B, false) (Finset.mem_product.mpr ⟨hm, Finset.mem_univ _⟩)
    have hn := ht (j - B, true) (Finset.mem_product.mpr ⟨hm, Finset.mem_univ _⟩)
    simpa [a, i, R, Nat.add_sub_cancel' hj] using And.intro hp hn
  · intro h
    apply hz.mpr
    rintro ⟨m, b⟩ hm
    have hm' : m < K - B := Finset.mem_range.mp (Finset.mem_product.mp hm).1
    have ht := (cnorm_le_iff_digits (Nat.sub_le (2 ^ K) 1) B r hr hq x).mp h
      (B + m) (by omega) (by omega)
    cases b <;> simp_all [a, i, R]

/-- The actual VM test accepts exactly the radius-`r` coefficient ball. -/
theorem exec_tstC_eq_zero_iff {N K : ℕ} [NeZero (2 ^ K - 1)]
    (hK : 0 < K) (B r : ℕ) (hBK : B ≤ K) (hr : 2 * r < 2 ^ B)
    (hq : 2 ^ (B + 1) ≤ 2 ^ K - 1) (hcount : 2 * (K - B) < 2 ^ K - 1)
    (w : St) (x : Rq N K)
    (hx : w rTx = encRM N K x)
    (hR : w rRR = encRM N K (allC N (r : ZMod (2 ^ K - 1))))
    (hF : w rFa = encRM N K 0)
    (hB : w rTBk = List.replicate B false)
    (hn : w rTKB = List.replicate (K - B) false) (h1 : w rB1 = [false]) :
    exec N K tstC w rFa = encRM N K 0 ↔ cnorm x ≤ r := by
  rw [exec_tstC hK w x (allC N (r : ZMod (2 ^ K - 1))) 0 B (K - B)
    hx hR hF hB hn h1, zero_add]
  have hinj : Function.Injective (encRM N K) := by
    intro a b hab
    have h := congrArg (SigabaNeo.Lattices.Algo.decRM N K) hab
    simpa only [SigabaNeo.Lattices.Algo.decRM_encRM hK] using h
  rw [hinj.eq_iff, sum_tstD_eq_zero_iff B r hBK hr hq hcount]

/-- Applying the test to every short coordinate characterizes the configured small box. -/
theorem small_iff_tstD (D : Dims) (B r : ℕ) (hB : 2 ^ B ≤ D.q)
    (hBK : B ≤ D.K) (hr : 2 * r < 2 ^ B) (hq : 2 ^ (B + 1) ≤ D.q)
    (hcount : 2 * (D.K - B) < D.q) (p : PIdxD D → Rg D) :
    p ∈ (kbOf D B hB r).Small ↔ ∀ t,
      (∑ m ∈ Finset.range (D.K - B),
        tstD (p t) (allC D.N (r : ZMod D.q)) (B + m)) = 0 := by
  rw [kbOf_Small, mem_famBall]
  exact forall_congr' fun t ↦ (sum_tstD_eq_zero_iff B r hBK hr hq hcount (p t)).symm

/-- Test one ring element and place its acceptance bit in `rTx`. -/
def ballTestC : Code := .seq tstC (.eqb rTx rFa rZ)

theorem wf_ballTestC : ballTestC.WFc := by
  simp [ballTestC, tstC, tstBody, Code.WFc, Code.writes]

/-- The executable Boolean branch condition for one coordinate of the short family. -/
theorem exec_ballTestC {N K : ℕ} [NeZero (2 ^ K - 1)]
    (hK : 0 < K) (B r : ℕ) (hBK : B ≤ K) (hr : 2 * r < 2 ^ B)
    (hq : 2 ^ (B + 1) ≤ 2 ^ K - 1) (hcount : 2 * (K - B) < 2 ^ K - 1)
    (w : St) (x : Rq N K)
    (hx : w rTx = encRM N K x)
    (hR : w rRR = encRM N K (allC N (r : ZMod (2 ^ K - 1))))
    (hF : w rFa = encRM N K 0)
    (hB : w rTBk = List.replicate B false)
    (hn : w rTKB = List.replicate (K - B) false) (h1 : w rB1 = [false])
    (hZ : w rZ = encRM N K 0) :
    exec N K ballTestC w rTx = [decide (cnorm x ≤ r)] := by
  have hz : exec N K tstC w rZ = encRM N K 0 := by
    rw [exec_writes _ _ _ (by decide), hZ]
  have htest := exec_tstC_eq_zero_iff hK B r hBK hr hq hcount w x hx hR hF hB hn h1
  rw [ballTestC, exec_seq]
  simp only [exec, rTx, rFa, rZ, Fin.reduceEq, or_self, ↓reduceIte, Function.update_self]
  simp only [hz, htest]

open Params

/-- The concrete parameters satisfy the separation and no-cancellation conditions. -/
theorem small_test_conditions_Dc :
    2 * rSmall < 2 ^ Bk ∧ 2 ^ (Bk + 1) ≤ Dc.q ∧
      2 * (Dc.K - Bk) < Dc.q := by
  have hp : 2 ^ Bk = 2 * 2 ^ (Bk - 1) := by
    rw [← pow_succ']; congr 1; have := one_le_Bk; omega
  have hr := rSmall_add
  have hpos : 0 < 2 ^ (Bk - 1) := by positivity
  refine ⟨by omega, ?_, ?_⟩
  · have he : Bk + 1 < Kc := by rw [Bk_def, Kc_def]; norm_num
    have h := Nat.pow_lt_pow_right (a := 2) (by norm_num) he
    change 2 ^ (Bk + 1) ≤ 2 ^ Kc - 1
    omega
  · have he : 17 < Kc := by rw [Kc_def]; norm_num
    have h := Nat.pow_lt_pow_right (a := 2) (by norm_num) he
    have hb : 2 * (Dc.K - Bk) < 2 ^ 17 := by
      change 2 * (Kc - Bk) < 2 ^ 17
      rw [Kc_def, Bk_def]; norm_num
    change 2 * (Dc.K - Bk) < 2 ^ Kc - 1
    omega

/-- Exact small-box test at the parameters used by the submitted scheme. -/
theorem kbDc_small_iff_tstD (p : PIdxD Dc → Rg Dc) :
    p ∈ kbDc.Small ↔ ∀ t,
      (∑ m ∈ Finset.range (Dc.K - Bk),
        tstD (p t) (allC Dc.N (rSmall : ZMod Dc.q)) (Bk + m)) = 0 := by
  rw [kbDc_def]
  exact small_iff_tstD Dc Bk rSmall hBk_Dc Bk_lt_Kc.le
    small_test_conditions_Dc.1 small_test_conditions_Dc.2.1 small_test_conditions_Dc.2.2 p

end AdvancedEncryption.ExpLUT.Prog
