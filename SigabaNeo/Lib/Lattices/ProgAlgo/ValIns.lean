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

/-! ### The bits `i'` of an entry -/

/-- One bit index `i'`: its `N` inputs, then the next bit. -/
def ipBody : Code := ofList [tLoopI, .tl ZM]

/-- **One entry** `E` of `ψᵢ` (`N K` bits from `PSt`): the bits `i' < K`, then `i' = K` (all
`false`). -/
def eBody : Code :=
  ofList [.cp rX TNK, .mv rX PSt TNK, .cp ZM rX, .cp CI 20, .rep CI ipBody, .clr ZM, tLoopI]

/-- The bit of the input `(i', t)` of an entry `E`. -/
def bitE (K : ℕ) (E : List Bool) (i' t : ℕ) : Bool := if i' < K then E.getD (t * K + i') false else false

theorem range_map_dite {β : Type*} {n : ℕ} (g : Fin n → β) (d : β) :
    (List.range n).map (fun t => if h : t < n then g ⟨t, h⟩ else d) = (List.finRange n).map g := by
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  congr 1; funext t; simp [t.isLt]

/-- The `N` inputs of `(i, q, i')` with the bits from `z`. -/
def blockI (N K : ℕ) (bF wF : Fin N → List Bool) (bit : ℕ → Bool) : List (List Bool) :=
  (List.finRange N).map fun t => jw (bF t) (wF t) (bit t.val) N K

theorem exec_tLoopI' {A1 Ad N K : ℕ} (w : St) (ht : ITmpl V A1 Ad N K w) (htn : (w TN).length = N)
    (bF wF : Fin N → List Bool) (hb : ∀ t, (bF t).length = A1) (hx : ∀ t, (wF t).length = Ad)
    {RB RW : List Bool} (hB : w BSt = ((List.finRange N).map bF).flatten ++ RB)
    (hW : w WSt = ((List.finRange N).map wF).flatten ++ RW) :
    exec V f tLoopI w INSW = (w INSW ++ (blockI N K bF wF fun t =>
        (w ZM).getD (t * K) false).flatten).drop (N * V) ∧
      exec V f tLoopI w BSt = RB ∧ exec V f tLoopI w WSt = RW ∧
      ∀ j, j ≠ JR → j ≠ BSt → j ≠ WSt → j ≠ rZ → j ≠ rY → j ≠ INSW → j ≠ CT →
        exec V f tLoopI w j = w j := by
  have h := exec_tLoopI (V := V) (f := f) w ht htn
    (fun t => if h : t < N then bF ⟨t, h⟩ else List.replicate A1 false)
    (fun t => if h : t < N then wF ⟨t, h⟩ else List.replicate Ad false)
    (fun t => by split_ifs <;> simp [hb]) (fun t => by split_ifs <;> simp [hx])
    (RB := RB) (RW := RW) (by rw [hB, range_map_dite]) (by rw [hW, range_map_dite])
  refine ⟨?_, h.2.1, h.2.2.1, h.2.2.2⟩
  rw [h.1, blockI]
  congr 3
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  congr 1; funext t; simp [t.isLt]

theorem blockI_shape {A1 Ad N K : ℕ} (hV : V = A1 + Ad + N * K) (hNK : 0 < N * K)
    {bF wF : Fin N → List Bool} (hb : ∀ t, (bF t).length = A1) (hx : ∀ t, (wF t).length = Ad)
    (bit : ℕ → Bool) : UV V (blockI N K bF wF bit) ∧ (blockI N K bF wF bit).length = N := by
  refine ⟨fun y hy => ?_, by simp [blockI]⟩
  simp only [blockI, List.mem_map] at hy
  obtain ⟨t, -, rfl⟩ := hy
  simp [jw, hb, hx, hV]; omega

/-- The inputs of an entry `E`. -/
def entryI (N K : ℕ) (bF wF : Fin (K + 1) → Fin N → List Bool) (E : List Bool) :
    List (List Bool) :=
  (List.finRange (K + 1)).flatMap fun i' => blockI N K (bF i') (wF i') (bitE K E i'.val)

theorem exec_eBody {A1 Ad N K : ℕ} (w : St) (ht : ITmpl V A1 Ad N K w)
    (htn : (w TN).length = N) (h20 : (w 20).length = K) (hnk : (w TNK).length = N * K)
    (bF wF : Fin (K + 1) → Fin N → List Bool) (hb : ∀ i t, (bF i t).length = A1)
    (hx : ∀ i t, (wF i t).length = Ad) {E RB RW RP : List Bool} (hE : E.length = N * K)
    (hB : w BSt = ((List.finRange (K + 1)).flatMap fun i' =>
      (List.finRange N).map (bF i')).flatten ++ RB)
    (hW : w WSt = ((List.finRange (K + 1)).flatMap fun i' =>
      (List.finRange N).map (wF i')).flatten ++ RW)
    (hP : w PSt = E ++ RP) :
    exec V f eBody w INSW = (w INSW ++ (entryI N K bF wF E).flatten).drop
        ((K + 1) * (N * V)) ∧
      exec V f eBody w BSt = RB ∧ exec V f eBody w WSt = RW ∧ exec V f eBody w PSt = RP ∧
      ∀ j ∉ wr eBody, exec V f eBody w j = w j := by
  refine ⟨?_, ?_, ?_, ?_, fun j hj => exec_not_mem _ _ _ hj⟩ <;>
  · rw [show eBody = ofList ([.cp rX TNK, .mv rX PSt TNK, .cp ZM rX, .cp CI 20] ++
      [.rep CI ipBody, .clr ZM, tLoopI]) from rfl, exec_ofList_append]
    have pre : exec V f (ofList [.cp rX TNK, .mv rX PSt TNK, .cp ZM rX, .cp CI 20]) w ZM = E ∧
        exec V f (ofList [.cp rX TNK, .mv rX PSt TNK, .cp ZM rX, .cp CI 20]) w PSt = RP ∧
        (exec V f (ofList [.cp rX TNK, .mv rX PSt TNK, .cp ZM rX, .cp CI 20]) w CI).length = K ∧
        ∀ j, j ≠ rX → j ≠ PSt → j ≠ ZM → j ≠ CI →
          exec V f (ofList [.cp rX TNK, .mv rX PSt TNK, .cp ZM rX, .cp CI 20]) w j = w j := by
      simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
      rw [exec_mv_pop (x := E) (L := RP) (by decide) (by simp [Function.update_apply])
        (by simp (config := {decide := true}) [Function.update_apply, hE, hnk])
        (by simp (config := {decide := true}) [Function.update_apply, hP])]
      refine ⟨by simp (config := {decide := true}) [Function.update_apply],
        by simp (config := {decide := true}) [Function.update_apply],
        by simp (config := {decide := true}) [Function.update_apply, h20],
        fun j a1 a2 a3 a4 => by simp [Function.update_apply, a1, a2, a3, a4]⟩
    obtain ⟨p1, p2, p3, p4⟩ := pre
    generalize exec V f (ofList [.cp rX TNK, .mv rX PSt TNK, .cp ZM rX, .cp CI 20]) w = u at p1 p2 p3 p4
    have ht1 : ITmpl V A1 Ad N K u := ht.of_eq fun j hj => p4 j (by revert j hj; decide)
      (by revert j hj; decide) (by revert j hj; decide) (by revert j hj; decide)
    have I := exec_rep_inv (V := V) (f := f) (c := CI) (B := ipBody)
      (fun r w' => r ≤ K → ITmpl V A1 Ad N K w' ∧ (w' TN).length = N ∧ w' ZM = E.drop r ∧
        w' BSt = (((List.finRange (K + 1)).drop r).flatMap fun i' =>
          (List.finRange N).map (bF i')).flatten ++ RB ∧
        w' WSt = (((List.finRange (K + 1)).drop r).flatMap fun i' =>
          (List.finRange N).map (wF i')).flatten ++ RW ∧
        w' PSt = RP ∧
        w' INSW = (u INSW ++ (((List.finRange (K + 1)).take r).flatMap fun i' =>
          blockI N K (bF i') (wF i') (bitE K E i'.val)).flatten).drop (r * (N * V)))
      (fun r w' ih hr => by
        obtain ⟨t1, tn1, hz, hB', hW', hP', hI'⟩ := ih (by omega)
        have hrl : r < (List.finRange (K + 1)).length := by simp; omega
        set i' := (List.finRange (K + 1))[r] with hi'
        have hi'v : i'.val = r := by simp [hi']
        have t2 := t1.of_eq fun j hj => Function.update_of_ne (show j ≠ CI by revert j hj; decide)
          (w' CI).tail w'
        simp only [ipBody, exec_ofList, List.foldl_cons, List.foldl_nil, exec_tl']
        obtain ⟨T1, T2, T3, T4⟩ := exec_tLoopI' (V := V) (f := f)
          (Function.update w' CI (w' CI).tail) t2 (by rw [Function.update_of_ne (by decide), tn1])
          (bF i') (wF i') (hb i') (hx i')
          (RB := (((List.finRange (K + 1)).drop (r + 1)).flatMap fun i' =>
            (List.finRange N).map (bF i')).flatten ++ RB)
          (RW := (((List.finRange (K + 1)).drop (r + 1)).flatMap fun i' =>
            (List.finRange N).map (wF i')).flatten ++ RW)
          (by rw [Function.update_of_ne (by decide), hB', List.drop_eq_getElem_cons hrl,
            List.flatMap_cons, List.flatten_append, List.append_assoc])
          (by rw [Function.update_of_ne (by decide), hW', List.drop_eq_getElem_cons hrl,
            List.flatMap_cons, List.flatten_append, List.append_assoc])
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · refine (t2.of_eq fun j hj => T4 j (by revert j hj; decide) (by revert j hj; decide)
            (by revert j hj; decide) (by revert j hj; decide) (by revert j hj; decide)
            (by revert j hj; decide) (by revert j hj; decide)).of_eq fun j hj => ?_
          exact Function.update_of_ne (show j ≠ ZM by revert j hj; decide) _ _
        · rw [Function.update_of_ne (by decide), T4 TN (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide), Function.update_of_ne (by decide), tn1]
        · rw [Function.update_self, T4 ZM (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide), Function.update_of_ne (by decide), hz,
            List.tail_drop]
        · rw [Function.update_of_ne (by decide), T2]
        · rw [Function.update_of_ne (by decide), T3]
        · rw [Function.update_of_ne (by decide), T4 PSt (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide), Function.update_of_ne (by decide), hP']
        · rw [Function.update_of_ne (by decide), T1, Function.update_of_ne (by decide), hI']
          have hzm : (Function.update w' CI (w' CI).tail ZM) = E.drop r := by
            rw [Function.update_of_ne (by decide), hz]
          rw [hzm]
          have hbs := blockI_shape (V := V) ht.hV ht.hNK (hb i') (hx i')
            (fun t => (E.drop r).getD (t * K) false)
          have e : blockI N K (bF i') (wF i') (fun t => (E.drop r).getD (t * K) false) =
              blockI N K (bF i') (wF i') (bitE K E i'.val) := by
            congr 1; funext t; rw [bitE, hi'v, if_pos (by omega), List.getD_eq_getElem?_getD,
              List.getElem?_drop, ← List.getD_eq_getElem?_getD, Nat.add_comm]
          have hpl : ((((List.finRange (K + 1)).take r).flatMap fun i' =>
              blockI N K (bF i') (wF i') (bitE K E i'.val)).flatten).length = r * (N * V) := by
            rw [length_flatten_of (V := V) (fun y hy => by
              simp only [List.mem_flatMap] at hy
              obtain ⟨j, -, hy⟩ := hy
              exact (blockI_shape ht.hV ht.hNK (hb j) (hx j) _).1 y hy)]
            simp only [List.length_flatMap]
            rw [List.map_congr_left (fun j _ => (blockI_shape (V := V) ht.hV ht.hNK (hb j) (hx j)
              (bitE K E j.val)).2), List.map_const', List.sum_replicate]
            simp [List.length_take]; rw [min_eq_left (by omega)]; ring
          rw [e, show (r + 1) * (N * V) = r * (N * V) + N * V by ring]
          rw [drop_append_drop' (by simp only [List.length_append, hpl]; omega), List.append_assoc,
            List.take_succ, List.getElem?_eq_getElem hrl, Option.toList_some, List.flatMap_append,
            List.flatMap_singleton, List.flatten_append, ← hi']) u
      (fun _ => ⟨ht1, by rw [p4 TN (by decide) (by decide) (by decide) (by decide), htn],
        by simp [p1], by rw [p4 BSt (by decide) (by decide) (by decide) (by decide), hB]; simp,
        by rw [p4 WSt (by decide) (by decide) (by decide) (by decide), hW]; simp, p2, by simp⟩)
    rw [p3] at I
    obtain ⟨t1, tn1, hz, hB', hW', hP', hI'⟩ := I le_rfl
    simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_clr']
    generalize exec V f (.rep CI ipBody) u = v at t1 tn1 hz hB' hW' hP' hI'
    have hK' : K < (List.finRange (K + 1)).length := by simp
    have hlast : (List.finRange (K + 1)).drop K = [Fin.last K] := by
      rw [List.drop_eq_getElem_cons hK', List.drop_eq_nil_of_le (by simp)]
      congr 1; ext; simp
    have t2 := t1.of_eq (w' := Function.update v ZM []) fun j hj =>
      Function.update_of_ne (show j ≠ ZM by revert j hj; decide) _ _
    obtain ⟨T1, T2, T3, T4⟩ := exec_tLoopI' (V := V) (f := f) (Function.update v ZM []) t2
      (by rw [Function.update_of_ne (by decide), tn1]) (bF (Fin.last K)) (wF (Fin.last K))
      (hb _) (hx _) (RB := RB) (RW := RW)
      (by rw [Function.update_of_ne (by decide), hB', hlast]; simp)
      (by rw [Function.update_of_ne (by decide), hW', hlast]; simp)
    have hINS : exec V f tLoopI (Function.update v ZM []) INSW =
        (w INSW ++ (entryI N K bF wF E).flatten).drop ((K + 1) * (N * V)) := by
       rw [T1, Function.update_of_ne (by decide), hI', p4 INSW (by decide) (by decide) (by decide)
        (by decide)]
       have hpl : ((((List.finRange (K + 1)).take K).flatMap fun i' =>
           blockI N K (bF i') (wF i') (bitE K E i'.val)).flatten).length = K * (N * V) := by
         rw [length_flatten_of (V := V) (fun y hy => by
           simp only [List.mem_flatMap] at hy
           obtain ⟨j, -, hy⟩ := hy
           exact (blockI_shape ht.hV ht.hNK (hb j) (hx j) _).1 y hy)]
         simp only [List.length_flatMap]
         rw [List.map_congr_left (fun j _ => (blockI_shape (V := V) ht.hV ht.hNK (hb j) (hx j)
           (bitE K E j.val)).2), List.map_const', List.sum_replicate]
         simp [List.length_take]; ring
       rw [drop_append_drop' (by simp only [List.length_append, hpl]; omega), List.append_assoc]
       have e : blockI N K (bF (Fin.last K)) (wF (Fin.last K)) (fun t =>
           (Function.update v ZM [] ZM).getD (t * K) false) =
           blockI N K (bF (Fin.last K)) (wF (Fin.last K)) (bitE K E (Fin.last K).val) := by
         congr 1; funext t; simp [bitE]
       have hEI : entryI N K bF wF E = ((List.finRange (K + 1)).take K).flatMap (fun i' =>
           blockI N K (bF i') (wF i') (bitE K E i'.val)) ++
           blockI N K (bF (Fin.last K)) (wF (Fin.last K)) (bitE K E (Fin.last K).val) := by
         unfold entryI
         conv_lhs => rw [← List.take_append_drop K (List.finRange (K + 1)), hlast]
         rw [List.flatMap_append, List.flatMap_singleton]
       rw [e, hEI, List.flatten_append]
       congr 1; ring
    first
    | exact hINS
    | exact T2
    | exact T3
    | (rw [T4 PSt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), Function.update_of_ne (by decide), hP'])

/-! ### The entries and the inputs -/

/-- The `4k` entries of `ψᵢ`. -/
def iBody : Code := ofList [.cp CC2 T4k, .rep CC2 eBody]

/-- **The inputs of `f̂`**: the `10` words `ψᵢ`. -/
def insC : Code := ofList [.cp CA T10, .rep CA iBody]

/-- The entries `(a, c)` of a `2 × 2k` matrix. -/
def qsL (k : ℕ) : List (Fin 2 × (Fin 2 × Fin k)) := List.finRange 2 ×ˢ cols k

theorem length_qsL (k : ℕ) : (qsL k).length = 2 * (2 * k) := by
  simp [qsL, cols, List.length_product]

/-- The words of a stream in the order of the inputs: for each entry `q`, its `k × N` items. -/
def strQ {N K : ℕ} (g : Fin 2 × (Fin 2 × Fin (K + 1)) → Fin (K + 1) → Fin N → List Bool)
    (qs : List (Fin 2 × (Fin 2 × Fin (K + 1)))) : List Bool :=
  (qs.flatMap fun q => (List.finRange (K + 1)).flatMap fun i' => (List.finRange N).map (g q i')).flatten

/-- The inputs of the entries `qs`. -/
def insQ {N K : ℕ} (bF wF : Fin 2 × (Fin 2 × Fin (K + 1)) → Fin (K + 1) → Fin N → List Bool)
    (ent : Fin 2 × (Fin 2 × Fin (K + 1)) → List Bool) (qs : List (Fin 2 × (Fin 2 × Fin (K + 1)))) :
    List (List Bool) :=
  qs.flatMap fun q => entryI N K (bF q) (wF q) (ent q)

theorem entryI_shape {A1 Ad N K : ℕ} (hV : V = A1 + Ad + N * K) (hNK : 0 < N * K)
    {bF wF : Fin (K + 1) → Fin N → List Bool} (hb : ∀ i t, (bF i t).length = A1)
    (hx : ∀ i t, (wF i t).length = Ad) (E : List Bool) :
    UV V (entryI N K bF wF E) ∧ (entryI N K bF wF E).length = (K + 1) * N := by
  refine ⟨fun y hy => ?_, ?_⟩
  · simp only [entryI, List.mem_flatMap] at hy
    obtain ⟨j, -, hy⟩ := hy
    exact (blockI_shape hV hNK (hb j) (hx j) _).1 y hy
  · simp only [entryI, List.length_flatMap]
    rw [List.map_congr_left (fun j _ => (blockI_shape (V := V) hV hNK (hb j) (hx j) _).2),
      List.map_const', List.sum_replicate]; simp

theorem exec_iBody {A1 Ad N K : ℕ} (w : St) (ht : ITmpl V A1 Ad N K w)
    (htn : (w TN).length = N) (h20 : (w 20).length = K) (hnk : (w TNK).length = N * K)
    (h4k : (w T4k).length = 2 * (2 * (K + 1)))
    (bF wF : Fin 2 × (Fin 2 × Fin (K + 1)) → Fin (K + 1) → Fin N → List Bool)
    (hb : ∀ q i t, (bF q i t).length = A1) (hx : ∀ q i t, (wF q i t).length = Ad)
    (ent : Fin 2 × (Fin 2 × Fin (K + 1)) → List Bool) (he : ∀ q, (ent q).length = N * K)
    {RB RW RP : List Bool} (hB : w BSt = strQ bF (qsL (K + 1)) ++ RB)
    (hW : w WSt = strQ wF (qsL (K + 1)) ++ RW)
    (hP : w PSt = ((qsL (K + 1)).map ent).flatten ++ RP) :
    exec V f iBody w INSW = (w INSW ++ (insQ bF wF ent (qsL (K + 1))).flatten).drop
        ((insQ bF wF ent (qsL (K + 1))).flatten.length) ∧
      exec V f iBody w BSt = RB ∧ exec V f iBody w WSt = RW ∧ exec V f iBody w PSt = RP ∧
      ITmpl V A1 Ad N K (exec V f iBody w) ∧ ∀ j ∉ wr iBody, exec V f iBody w j = w j := by
  have hsh : ∀ q, UV V (entryI N K (bF q) (wF q) (ent q)) ∧
      (entryI N K (bF q) (wF q) (ent q)).length = (K + 1) * N :=
    fun q => entryI_shape ht.hV ht.hNK (hb q) (hx q) _
  refine ⟨?_, ?_, ?_, ?_, ht.of_eq fun j hj => exec_not_mem _ _ _ (by revert j hj; decide),
    fun j hj => exec_not_mem _ _ _ hj⟩ <;>
  · simp only [iBody, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
    set w1 := Function.update w CC2 (w T4k) with hw1
    have e1 : ∀ j, j ≠ CC2 → w1 j = w j := fun j h => Function.update_of_ne h _ _
    have I := exec_rep_inv (V := V) (f := f) (c := CC2) (B := eBody)
      (fun r w' => r ≤ (qsL (K + 1)).length → ITmpl V A1 Ad N K w' ∧ (w' TN).length = N ∧
        (w' 20).length = K ∧ (w' TNK).length = N * K ∧
        w' BSt = strQ bF ((qsL (K + 1)).drop r) ++ RB ∧
        w' WSt = strQ wF ((qsL (K + 1)).drop r) ++ RW ∧
        w' PSt = (((qsL (K + 1)).drop r).map ent).flatten ++ RP ∧
        w' INSW = (w1 INSW ++ (insQ bF wF ent ((qsL (K + 1)).take r)).flatten).drop
          ((insQ bF wF ent ((qsL (K + 1)).take r)).flatten.length))
      (fun r w' ih hr => by
        obtain ⟨t1, tn1, t20, tnk, hB', hW', hP', hI'⟩ := ih (by omega)
        have hrl : r < (qsL (K + 1)).length := by omega
        set q := (qsL (K + 1))[r]
        have c0 : ∀ j, j ≠ CC2 → Function.update w' CC2 (w' CC2).tail j = w' j :=
          fun j h => Function.update_of_ne h _ _
        obtain ⟨E1, E2, E3, E4, E5⟩ := exec_eBody (V := V) (f := f)
          (Function.update w' CC2 (w' CC2).tail)
          (t1.of_eq fun j hj => c0 j (by revert j hj; decide))
          (by rw [c0 TN (by decide), tn1]) (by rw [c0 20 (by decide), t20])
          (by rw [c0 TNK (by decide), tnk]) (bF q) (wF q) (hb q) (hx q) (he q)
          (RB := strQ bF ((qsL (K + 1)).drop (r + 1)) ++ RB)
          (RW := strQ wF ((qsL (K + 1)).drop (r + 1)) ++ RW)
          (RP := (((qsL (K + 1)).drop (r + 1)).map ent).flatten ++ RP)
          (by rw [c0 BSt (by decide), hB', strQ, List.drop_eq_getElem_cons hrl, List.flatMap_cons,
            List.flatten_append, List.append_assoc]; rfl)
          (by rw [c0 WSt (by decide), hW', strQ, List.drop_eq_getElem_cons hrl, List.flatMap_cons,
            List.flatten_append, List.append_assoc]; rfl)
          (by rw [c0 PSt (by decide), hP', List.drop_eq_getElem_cons hrl, List.map_cons,
            List.flatten_cons, List.append_assoc])
        refine ⟨t1.of_eq fun j hj => by rw [E5 j (by revert j hj; decide), c0 j (by revert j hj; decide)],
          by rw [E5 TN (by decide), c0 TN (by decide), tn1],
          by rw [E5 20 (by decide), c0 20 (by decide), t20],
          by rw [E5 TNK (by decide), c0 TNK (by decide), tnk], E2, E3, E4, ?_⟩
        rw [E1, c0 INSW (by decide), hI', show (K + 1) * (N * V) =
          (entryI N K (bF q) (wF q) (ent q)).flatten.length by
            rw [length_flatten_of (hsh q).1, (hsh q).2]; ring, shift_acc]
        have e : insQ bF wF ent ((qsL (K + 1)).take (r + 1)) =
            insQ bF wF ent ((qsL (K + 1)).take r) ++ entryI N K (bF q) (wF q) (ent q) := by
          rw [insQ, insQ, List.take_succ, List.getElem?_eq_getElem hrl, Option.toList_some,
            List.flatMap_append, List.flatMap_singleton]
        rw [e, List.flatten_append]) w1
      (fun _ => ⟨ht.of_eq fun j hj => e1 j (by revert j hj; decide),
        by rw [e1 TN (by decide), htn], by rw [e1 20 (by decide), h20],
        by rw [e1 TNK (by decide), hnk], by rw [e1 BSt (by decide), hB]; rfl,
        by rw [e1 WSt (by decide), hW]; rfl, by rw [e1 PSt (by decide), hP]; rfl, by simp [insQ]⟩)
    rw [show (w1 CC2).length = (qsL (K + 1)).length by rw [hw1, Function.update_self, h4k,
      length_qsL]] at I
    obtain ⟨-, -, -, -, I5, I6, I7, I8⟩ := I le_rfl
    first
    | (rw [I8, List.take_of_length_le le_rfl, e1 INSW (by decide)])
    | (rw [I5, List.drop_eq_nil_of_le le_rfl]; rfl)
    | (rw [I6, List.drop_eq_nil_of_le le_rfl]; rfl)
    | (rw [I7, List.drop_eq_nil_of_le le_rfl]; rfl)

end ValVM

end SigabaNeo.Tape
