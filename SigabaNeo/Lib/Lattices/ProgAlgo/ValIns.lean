import SigabaNeo.Lib.Lattices.ProgAlgo.ValConst

/-!
# The inputs of `f̂` on the word machine

`insC`: from three streams — the rows `B_j` (`A1` bits each), the matrices `W_j` (`Ad` bits each),
both in the order of `Fin 10 × BI N k`, and the words `ψᵢ` (`4 k` ring elements of `N K` bits
each) — the joint words `B_j ++ W_j ++ [b_j] ++ 0^(N K − 1)` of all the inputs `j = (i, a, c, i', t)`
are shifted into `INSW`, where `b_j` is the bit `i'` of the coefficient `t` of the entry `(a, c)` of
`ψᵢ` (`false` for `i' = K`, `k = K + 1`) (`exec_insC`).
-/

namespace SigabaNeo.Tape

namespace ValVM

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP SigabaNeo.Lattices.Algo SigabaNeo.Encode

set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

variable {V : ℕ} {f : List Bool → List Bool → List Bool}

/-! ### Registers -/

abbrev PSt : Fin 120 := 64
abbrev BSt : Fin 120 := 66
abbrev WSt : Fin 120 := 67
abbrev JR : Fin 120 := 68
abbrev INSW : Fin 120 := 116
abbrev TA1 : Fin 120 := 104
abbrev TAd : Fin 120 := 105
abbrev TNK : Fin 120 := 106
abbrev TK1 : Fin 120 := 107
abbrev ZNK1 : Fin 120 := 108
abbrev T10 : Fin 120 := 109
abbrev T4k : Fin 120 := 117

/-! ### One input -/

/-- **One input**: `JR := B ++ W ++ [first bit of rZ] ++ 0^(NK − 1)` (`rZ` advanced by `K` bits),
shifted into `INSW`. -/
def jtBody : Code :=
  ofList [.cp JR 10, .mv JR BSt TA1, .mv JR WSt TAd, .mv JR rZ 29, .drop rZ TK1, .cp rY ZNK1,
    .mv JR rY ZNK1, .mvV INSW JR]

/-- The templates of the inputs. -/
structure ITmpl (V A1 Ad N K : ℕ) (w : St) : Prop where
  h10 : (w 10).length = V
  hV : V = A1 + Ad + N * K
  ta1 : (w TA1).length = A1
  tad : (w TAd).length = Ad
  tk1 : (w TK1).length = K - 1
  znk1 : w ZNK1 = List.replicate (N * K - 1) false
  t29 : (w 29).length = 1
  hNK : 0 < N * K
  hK : 0 < K

theorem exec_mv_gen {d s c : Fin 120} (h : ¬(d = s ∨ d = c ∨ s = c)) (w : St) :
    exec V f (.mv d s c) w = Function.update (Function.update w s ((w s).drop (w c).length)) d
      ((w d ++ takeD (w c).length (w s)).drop (w c).length) := by
  simp only [exec, if_neg h, shiftIn]

theorem exec_jtBody {A1 Ad N K : ℕ} (w : St) (ht : ITmpl V A1 Ad N K w) {b x L0 L1 z : List Bool}
    (hb : b.length = A1) (hx : x.length = Ad) (hB : w BSt = b ++ L0) (hW : w WSt = x ++ L1)
    (hZ : w rZ = z) :
    exec V f jtBody w INSW = (w INSW ++ (b ++ x ++ (takeD 1 z ++ List.replicate (N * K - 1)
        false))).drop V ∧
      exec V f jtBody w BSt = L0 ∧ exec V f jtBody w WSt = L1 ∧
      exec V f jtBody w rZ = (z.drop 1).drop (K - 1) ∧
      ∀ j, j ≠ JR → j ≠ BSt → j ≠ WSt → j ≠ rZ → j ≠ rY → j ≠ INSW → exec V f jtBody w j = w j := by
  obtain ⟨h10, hV, ta1, tad, tk1, znk1, t29, hNK, hK⟩ := ht
  simp only [jtBody, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  rw [exec_mv_shift (d := JR) (s := BSt) (c := TA1) (x := b) (L := L0) (by decide)
    (by simp (config := {decide := true}) [Function.update_apply, hb, ta1])
    (by simp (config := {decide := true}) [Function.update_apply, hB])]
  rw [exec_mv_shift (d := JR) (s := WSt) (c := TAd) (x := x) (L := L1) (by decide)
    (by simp (config := {decide := true}) [Function.update_apply, hx, tad])
    (by simp (config := {decide := true}) [Function.update_apply, hW])]
  rw [exec_mv_gen (d := JR) (s := rZ) (c := 29) (by decide)]
  rw [exec_drop' (by decide)]
  rw [exec_mv_shift (d := JR) (s := rY) (c := ZNK1) (x := List.replicate (N * K - 1) false) (L := [])
    (by decide) (by simp (config := {decide := true}) [Function.update_apply, znk1])
    (by simp (config := {decide := true}) [Function.update_apply, znk1])]
  set J := ((((w 10 ++ b).drop b.length ++ x).drop x.length ++ takeD 1 z).drop 1 ++
    List.replicate (N * K - 1) false).drop (List.replicate (N * K - 1) false).length with hJ
  have hJ' : J = b ++ x ++ (takeD 1 z ++ List.replicate (N * K - 1) false) := by
    have e1 : ((w 10 ++ b).drop b.length ++ x).drop x.length =
        (w 10 ++ b ++ x).drop (b.length + x.length) := by
      rw [drop_append_drop' (by simp)]
    have e2 : ((w 10 ++ b ++ x).drop (b.length + x.length) ++ takeD 1 z).drop 1 =
        (w 10 ++ b ++ x ++ takeD 1 z).drop (b.length + x.length + 1) := by
      rw [drop_append_drop' (by simp)]
    have e3 : ((w 10 ++ b ++ x ++ takeD 1 z).drop (b.length + x.length + 1) ++
        List.replicate (N * K - 1) false).drop (List.replicate (N * K - 1) false).length =
        (w 10 ++ b ++ x ++ takeD 1 z ++ List.replicate (N * K - 1) false).drop
          (b.length + x.length + 1 + (List.replicate (N * K - 1) false).length) := by
      rw [drop_append_drop' (by simp [takeD]; omega)]
    rw [hJ, e1, e2, e3, List.append_assoc, List.append_assoc, List.append_assoc,
      List.drop_left' (by simp [h10, hb, hx, takeD]; omega)]
    simp only [List.append_assoc]
  have hJl : J.length = V := by
    rw [hJ']; simp [hb, hx, takeD]; omega
  rw [exec_mvV_push (d := INSW) (s := JR) (by decide) (by
    simp (config := {decide := true}) only [Function.update_apply, if_true, if_false, t29, hZ]
    rw [← hJ, hJl])]
  refine ⟨?_, ?_, ?_, ?_, fun j a1 a2 a3 a4 a5 a6 => ?_⟩
  · simp (config := {decide := true}) only [Function.update_apply, if_true, if_false, t29, hZ]
    rw [← hJ, hJ']
  · simp (config := {decide := true}) [Function.update_apply]
  · simp (config := {decide := true}) [Function.update_apply]
  · simp (config := {decide := true}) [Function.update_apply, hZ, t29, tk1]
  · simp [Function.update_apply, a1, a2, a3, a4, a5, a6]

end ValVM

end SigabaNeo.Tape
