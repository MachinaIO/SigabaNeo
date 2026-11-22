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

/-- The words of `ITmpl`. -/
def itW : List (Fin 120) := [10, TA1, TAd, TK1, ZNK1, 29]

theorem ITmpl.of_eq {A1 Ad N K : ℕ} {w w' : St} (h : ITmpl V A1 Ad N K w)
    (e : ∀ j ∈ itW, w' j = w j) : ITmpl V A1 Ad N K w' :=
  ⟨by rw [e 10 (by decide)]; exact h.h10, h.hV, by rw [e TA1 (by decide)]; exact h.ta1,
    by rw [e TAd (by decide)]; exact h.tad, by rw [e TK1 (by decide)]; exact h.tk1,
    by rw [e ZNK1 (by decide)]; exact h.znk1, by rw [e 29 (by decide)]; exact h.t29, h.hNK, h.hK⟩

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

/-! ### The coefficients `t` -/

/-- The `N` inputs of `(i, q, i')`: `rZ := ZM`, `N` rounds. -/
def tLoopI : Code := ofList [.cp rZ ZM, .cp CT TN, .rep CT jtBody]

/-- The joint word of an input with the bit `b`. -/
def jw (b x : List Bool) (bit : Bool) (N K : ℕ) : List Bool :=
  b ++ x ++ (bit :: List.replicate (N * K - 1) false)

theorem takeD_one (z : List Bool) : takeD 1 z = [z.getD 0 false] := by
  cases z <;> rfl

theorem exec_tLoopI {A1 Ad N K : ℕ} (w : St) (ht : ITmpl V A1 Ad N K w) (htn : (w TN).length = N)
    (bF wF : ℕ → List Bool) (hb : ∀ t, (bF t).length = A1) (hx : ∀ t, (wF t).length = Ad)
    {RB RW : List Bool} (hB : w BSt = ((List.range N).map bF).flatten ++ RB)
    (hW : w WSt = ((List.range N).map wF).flatten ++ RW) :
    exec V f tLoopI w INSW = (w INSW ++ ((List.range N).map fun t =>
        jw (bF t) (wF t) ((w ZM).getD (t * K) false) N K).flatten).drop (N * V) ∧
      exec V f tLoopI w BSt = RB ∧ exec V f tLoopI w WSt = RW ∧
      ∀ j, j ≠ JR → j ≠ BSt → j ≠ WSt → j ≠ rZ → j ≠ rY → j ≠ INSW → j ≠ CT →
        exec V f tLoopI w j = w j := by
  have hK := ht.hK
  simp only [tLoopI, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  set w1 := Function.update (Function.update w rZ (w ZM)) CT (Function.update w rZ (w ZM) TN)
    with hw1
  have e1 : ∀ j, j ≠ rZ → j ≠ CT → w1 j = w j := fun j h1 h2 => by
    simp [hw1, Function.update_apply, h1, h2]
  have ht1 : ITmpl V A1 Ad N K w1 := ht.of_eq fun j hj =>
    e1 j (by revert j hj; decide) (by revert j hj; decide)
  have I := exec_rep_inv (V := V) (f := f) (c := CT) (B := jtBody)
    (fun r w' => r ≤ N → ITmpl V A1 Ad N K w' ∧
      w' BSt = (((List.range N).map bF).drop r).flatten ++ RB ∧
      w' WSt = (((List.range N).map wF).drop r).flatten ++ RW ∧
      w' rZ = (w ZM).drop (r * K) ∧
      w' INSW = (w1 INSW ++ ((List.range r).map fun t =>
        jw (bF t) (wF t) ((w ZM).getD (t * K) false) N K).flatten).drop (r * V) ∧
      ∀ j, j ≠ JR → j ≠ BSt → j ≠ WSt → j ≠ rZ → j ≠ rY → j ≠ INSW → j ≠ CT → w' j = w1 j)
    (fun r w' ih hr => by
      obtain ⟨t1, hB', hW', hZ', hI', ho⟩ := ih (by omega)
      have hrN : r < ((List.range N).map bF).length := by simp; omega
      have hrW : r < ((List.range N).map wF).length := by simp; omega
      have t2 : ITmpl V A1 Ad N K (Function.update w' CT (w' CT).tail) :=
        t1.of_eq fun j hj => Function.update_of_ne (by revert j hj; decide) _ _
      obtain ⟨R1, R2, R3, R4, R5⟩ := exec_jtBody (V := V) (f := f)
        (Function.update w' CT (w' CT).tail) t2 (b := bF r) (x := wF r)
        (L0 := (((List.range N).map bF).drop (r + 1)).flatten ++ RB)
        (L1 := (((List.range N).map wF).drop (r + 1)).flatten ++ RW) (z := (w ZM).drop (r * K))
        (hb r) (hx r)
        (by rw [Function.update_of_ne (by decide), hB', flatten_drop_cons hrN]; simp)
        (by rw [Function.update_of_ne (by decide), hW', flatten_drop_cons hrW]; simp)
        (by rw [Function.update_of_ne (by decide), hZ'])
      refine ⟨t2.of_eq fun j hj => R5 j (by revert j hj; decide) (by revert j hj; decide)
          (by revert j hj; decide) (by revert j hj; decide) (by revert j hj; decide)
          (by revert j hj; decide), R2, R3, ?_, ?_, fun j a1 a2 a3 a4 a5 a6 a7 => ?_⟩
      · rw [R4, List.drop_drop, List.drop_drop]
        congr 1
        obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
        simp; ring
      · rw [R1, Function.update_of_ne (by decide), hI', takeD_one, List.getD_eq_getElem?_getD,
          List.getElem?_drop, Nat.add_zero, ← List.getD_eq_getElem?_getD]
        have hl : ((List.range r).map fun t =>
            jw (bF t) (wF t) ((w ZM).getD (t * K) false) N K).flatten.length = r * V := by
          rw [length_flatten_of (V := V) (fun y hy => by
            simp only [List.mem_map, List.mem_range] at hy
            obtain ⟨t, -, rfl⟩ := hy
            simp [jw, hb, hx, t1.hV]; have := t1.hNK; omega)]
          simp
        rw [drop_append_drop' (by rw [List.length_append, hl]; omega), List.append_assoc,
          List.range_succ, List.map_append, List.map_singleton, List.flatten_append,
          List.flatten_singleton, Nat.succ_mul]
        rfl
      · rw [R5 j a1 a2 a3 a4 a5 a6, Function.update_of_ne a7]; exact ho j a1 a2 a3 a4 a5 a6 a7) w1
    (fun _ => ⟨ht1, by rw [e1 BSt (by decide) (by decide), hB]; simp,
      by rw [e1 WSt (by decide) (by decide), hW]; simp,
      by simp (config := {decide := true}) [hw1, Function.update_apply], by simp,
      fun _ _ _ _ _ _ _ _ => rfl⟩)
  have hn : (w1 CT).length = N := by simp (config := {decide := true}) [hw1, Function.update_apply, htn]
  rw [hn] at I
  obtain ⟨-, I2, I3, -, I5, I6⟩ := I le_rfl
  refine ⟨?_, by rw [I2, List.drop_eq_nil_of_le (by simp)]; simp,
    by rw [I3, List.drop_eq_nil_of_le (by simp)]; simp, fun j a1 a2 a3 a4 a5 a6 a7 => ?_⟩
  · rw [I5, e1 INSW (by decide) (by decide)]
  · rw [I6 j a1 a2 a3 a4 a5 a6 a7, e1 j a4 a7]

end ValVM

end SigabaNeo.Tape
