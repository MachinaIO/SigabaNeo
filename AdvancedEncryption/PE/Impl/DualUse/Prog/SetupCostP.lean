import PE.Impl.DualUse.Prog.SetupEncCost
import PE.Impl.DualUse.Prog.SetupCost
import PE.Impl.DualUse.Prog.UBLoop
import PE.Impl.DualUse.Prog.C0

/-!
# The time of the compiled `Setup`

`ub_setupP`: from tapes below `M` (with `M` above the sampler thresholds), `setupP` takes at most
`setupT M` steps and leaves every tape below `setupG M`: the six framed samplers (their shape bounds,
`ub_of_atb`), then the deterministic part (`ub_c0P`, `ub_b1P`, the appends).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The bound after the samplers of `Setup`. -/
def setupS (Bχ : Bnd) (M : ℕ) : ℕ :=
  let M1 := M + (bCoins (nRowD N K c.d)).a + (bCoins (nRowD N K c.d)).s
  let M2 := M1 + (bCoins (nRowC N K k)).a + (bCoins (nRowC N K k)).s
  let M3 := M2 + (Bχ.count N).a + (Bχ.count N).s
  let M4 := M3 + (Bχ.count ((Enum.list (α := RingBTVW.Col k)).length * N)).a +
    (Bχ.count ((Enum.list (α := RingBTVW.Col k)).length * N)).s
  let M5 := M4 + (bCoins (nBj (N := N) hk)).a + (bCoins (nBj (N := N) hk)).s
  M5 + (bCoins (N * K)).a + (bCoins (N * K)).s

/-- The time of the samplers of `Setup`. -/
def setupST (Bχ : Bnd) (M : ℕ) : ℕ :=
  let M1 := M + (bCoins (nRowD N K c.d)).a + (bCoins (nRowD N K c.d)).s
  let M2 := M1 + (bCoins (nRowC N K k)).a + (bCoins (nRowC N K k)).s
  let M3 := M2 + (Bχ.count N).a + (Bχ.count N).s
  let M4 := M3 + (Bχ.count ((Enum.list (α := RingBTVW.Col k)).length * N)).a +
    (Bχ.count ((Enum.list (α := RingBTVW.Col k)).length * N)).s
  let M5 := M4 + (bCoins (nBj (N := N) hk)).a + (bCoins (nBj (N := N) hk)).s
  (bCoins (nRowD N K c.d)).T M M + ((bCoins (nRowC N K k)).T M1 M1 + ((Bχ.count N).T M2 M2 +
    ((Bχ.count ((Enum.list (α := RingBTVW.Col k)).length * N)).T M3 M3 +
    ((bCoins (nBj (N := N) hk)).T M4 M4 + (bCoins (N * K)).T M5 M5))))

/-- The bound after an append (`appC`) from tapes below `M`. -/
abbrev apGS (M : ℕ) : ℕ := 4 * M + 1

theorem ub_appC (r a : Fin 96) (M : ℕ) : UB (appC r a) M ((2 * (M + 1) + 3) + appT M) (apGS M) :=
  (ub_copyS 88 a M).seq (ub_appendTapeP r 88 89 90 M)

/-- The time of `setupDet` from tapes below `M`. -/
def detT (N K k M : ℕ) : ℕ :=
  let A1 := apGS M
  let A2 := apGS A1
  let C1 := A2 + 1
  let A3 := apGS C1
  let B1 := A3 + 1
  let A4 := apGS B1
  let A5 := apGS A4
  let A6 := apGS A5
  let F1 := apGS A6
  let A7 := apGS F1
  let A8 := apGS A7
  (2 * (M + 1) + 3) + (((2 * (M + 1) + 3) + appT M) + (((2 * (A1 + 1) + 3) + appT A1) +
    (timeC0 0 (2 * k * (N * K)) (2 * k) N K A2 + ((2 * (C1 + 1) + 3) + ((2 * (C1 + 1) + 3) +
    (((2 * (C1 + 1) + 3) + appT C1) + (timeB1 N K k A3 + ((2 * (B1 + 1) + 3) + ((2 * (B1 + 1) + 3) +
    (((2 * (B1 + 1) + 3) + appT B1) + (((2 * (A4 + 1) + 3) + appT A4) +
    (((2 * (A5 + 1) + 3) + appT A5) + (appT A6 + (((2 * (F1 + 1) + 3) + appT F1) +
    (((2 * (A7 + 1) + 3) + appT A7) + appT A8)))))))))))))))

/-- The bound after `setupDet` from tapes below `M`. -/
def detG (M : ℕ) : ℕ :=
  let A2 := apGS (apGS M)
  let A3 := apGS (A2 + 1)
  let A6 := apGS (apGS (apGS (A3 + 1)))
  apGS (apGS (apGS (apGS A6)))

set_option maxHeartbeats 4000000 in
theorem ub_setupDet (M : ℕ) (hC : sizeC0 0 (2 * k * (N * K)) (2 * k) N K ≤ apGS (apGS M))
    (hB : sizeB1 N K k ≤ apGS (apGS (apGS M) + 1)) :
    UB (setupDet (N := N) (K := K) (k := k)) M (detT N K k M) (detG M) := by
  rw [setupDet]
  refine ((ub_copyS 0 83 M).seq <| (ub_appC 0 84 _).seq <| (ub_appC 0 85 _).seq <|
    (ub_frameLe e82 (ub_c0P 0 (2 * k * (N * K)) (2 * k) N K _ hC) (by omega)).seq <|
    (ub_copyS 92 0 _).seq <| (ub_copyS 0 83 _).seq <| (ub_appC 0 92 _).seq <|
    (ub_frameLe e82 (ub_b1P N K k _ hB) (by omega)).seq <|
    (ub_copyS 92 0 _).seq <| (ub_copyS 0 82 _).seq <| (ub_appC 0 92 _).seq <|
    (ub_appC 0 86 _).seq <| (ub_appC 0 87 _).seq <| (ub_frameApP 91 0 89 90 _).seq <|
    (ub_appC 0 85 _).seq <| (ub_appC 0 84 _).seq (ub_frameApP 91 0 89 90 _)).mono
    (le_of_eq rfl) (le_of_eq rfl)

set_option maxHeartbeats 4000000 in
/-- **The uniform bound of `setupP`.** -/
theorem ub_setupP {X : ChiSampler c} (M : ℕ)
    (h1 : (bCoins (nRowD N K c.d)).S₀ ≤ M)
    (h2 : (bCoins (nRowC N K k)).S₀ ≤ M)
    (h3 : (X.B.count N).S₀ ≤ M)
    (h4 : (X.B.count ((Enum.list (α := RingBTVW.Col k)).length * N)).S₀ ≤ M)
    (h5 : (bCoins (nBj (N := N) hk)).S₀ ≤ M) (h6 : (bCoins (N * K)).S₀ ≤ M)
    (hpres : X.P.Preserves 6)
    (hC : sizeC0 0 (2 * k * (N * K)) (2 * k) N K ≤ apGS (apGS (setupS hk c X.B M)))
    (hB : sizeB1 N K k ≤ apGS (apGS (apGS (setupS hk c X.B M)) + 1)) :
    UB (setupP hk c X) M (setupST hk c X.B M + detT N K k (setupS hk c X.B M))
      (detG (setupS hk c X.B M)) := by
  rw [setupP]
  refine ((ub_of_atb eB0 (atbb_coinsF _) h1).seq <|
    (ub_of_atb eAa (atbb_coinsF _) (by omega)).seq <|
    (ub_of_atb eTt (atbb_repF X.atb hpres N) (by omega)).seq <|
    (ub_of_atb eEe (atbb_repF X.atb hpres _) (by omega)).seq <|
    (ub_of_atb eBj (atbb_coinsF _) (by omega)).seq <|
    (ub_of_atb ePp (atbb_coinsF _) (by omega)).seq
    (ub_setupDet _ hC hB)).mono (le_of_eq ?_) (le_of_eq rfl)
  simp only [setupST, setupS, Nat.add_assoc]

end AdvancedEncryption.DualUse.Prog
