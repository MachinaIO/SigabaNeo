import SigabaNeo.Lib.Lattices.ProgAlgo.ValGsw

/-!
# The two runs of the word machine

* `fhatC` (the simulation of `f̂`, step `f` on joint words of `V` bits): `zv := f (one, one)`, the
  words `zv^k` and `true^k`, the inputs (`insC`), the constant bundle (`cbC`), the store
  `C^(W − 9) ++ ins`, the gates with the NAND block (`gloopC nandC`): **`exec_fhatC`**, `OUTW` ends
  with the word of the output bundle `fhatV …`;
* `gswC` (the simulation of the predicate): the inputs (`insGC`), the store `one^(W − 9) ++ ins`,
  the gates with the single `gate`: **`exec_gswC`**, `OUTW` ends with the value of the output wire.
-/

namespace SigabaNeo.Tape

namespace ValVM

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP SigabaNeo.Lattices.Algo SigabaNeo.Encode SigabaNeo.Tape.Prog

set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

variable {V : ℕ} {f : List Bool → List Bool → List Bool}

/-! ### Shifting copies of a word -/

/-- One copy of `src` shifted into `dst` (through `sc`, `|cl|` bits). -/
def shiftOne (dst src sc cl : Fin 120) : Code := ofList [.cp sc src, .mv dst sc cl]

theorem exec_shiftRep {dst src sc cl ctr : Fin 120}
    (hd : dst ≠ src ∧ dst ≠ sc ∧ dst ≠ cl ∧ dst ≠ ctr) (hs : src ≠ sc ∧ src ≠ ctr)
    (hc : sc ≠ cl ∧ sc ≠ ctr ∧ cl ≠ ctr) (w : St) (hl : (w src).length = (w cl).length) :
    exec V f (.rep ctr (shiftOne dst src sc cl)) w dst =
        (w dst ++ (List.replicate (w ctr).length (w src)).flatten).drop
          ((w ctr).length * (w cl).length) ∧
      ∀ j, j ≠ dst → j ≠ sc → j ≠ ctr → exec V f (.rep ctr (shiftOne dst src sc cl)) w j = w j := by
  have I := exec_rep_inv (V := V) (f := f) (c := ctr) (B := shiftOne dst src sc cl)
    (fun r w' => w' dst = (w dst ++ (List.replicate r (w src)).flatten).drop (r * (w cl).length) ∧
      ∀ j, j ≠ dst → j ≠ sc → j ≠ ctr → w' j = w j)
    (fun r w' ih => by
      obtain ⟨h1, h2⟩ := ih
      have e : ∀ j, j ≠ dst → j ≠ sc → j ≠ ctr → Function.update w' ctr (w' ctr).tail j = w j :=
        fun j a1 a2 a3 => by rw [Function.update_of_ne a3, h2 j a1 a2 a3]
      simp only [shiftOne, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
      rw [exec_mv_shift (d := dst) (s := sc) (c := cl) (x := w src) (L := []) (by
          simp only [not_or]; exact ⟨hd.2.1, hd.2.2.1, hc.1⟩)
        (by rw [Function.update_of_ne hc.1.symm, e cl (Ne.symm hd.2.2.1) hc.1.symm hc.2.2, hl])
        (by rw [Function.update_self, e src hd.1.symm hs.1 hs.2, List.append_nil])]
      refine ⟨?_, fun j a1 a2 a3 => ?_⟩
      · rw [Function.update_self, Function.update_of_ne hd.2.1, Function.update_of_ne hd.2.2.2, h1,
          hl, drop_append_drop' (by simp; nlinarith [List.length_replicate (n := r) (a := w src)]),
          List.append_assoc, List.replicate_succ', List.flatten_append, List.flatten_singleton,
          Nat.succ_mul]
      · rw [Function.update_of_ne a1, Function.update_of_ne a2, Function.update_of_ne a2,
          e j a1 a2 a3]) w
    ⟨by simp, fun _ _ _ _ => rfl⟩
  exact I

/-! ### The run of `f̂` -/

abbrev CBW : Fin 120 := 115
abbrev TW9 : Fin 120 := 118
abbrev TINS : Fin 120 := 119

/-- `dst := src^|tC|` (`dst` from the template `tD` of `|tC| · |cl|` bits). -/
def fillC (dst src cl tD tC : Fin 120) : Code :=
  ofList [.cp dst tD, .cp CQ tC, .rep CQ (shiftOne dst src rY cl)]

theorem exec_fillC {dst src cl tD tC : Fin 120}
    (hd : dst ≠ src ∧ dst ≠ rY ∧ dst ≠ cl ∧ dst ≠ CQ ∧ dst ≠ tC) (hs : src ≠ rY ∧ src ≠ CQ)
    (hc : rY ≠ cl ∧ cl ≠ CQ) (ht : tC ≠ CQ) (w : St) (hl : (w src).length = (w cl).length)
    (hT : (w tD).length = (w tC).length * (w cl).length) :
    exec V f (fillC dst src cl tD tC) w dst = (List.replicate (w tC).length (w src)).flatten ∧
      ∀ j, j ≠ dst → j ≠ rY → j ≠ CQ → exec V f (fillC dst src cl tD tC) w j = w j := by
  simp only [fillC, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  set w1 := Function.update (Function.update w dst (w tD)) CQ (Function.update w dst (w tD) tC)
    with hw1
  have e1 : ∀ j, j ≠ dst → j ≠ CQ → w1 j = w j := fun j a1 a2 => by
    simp [hw1, Function.update_apply, a1, a2]
  obtain ⟨R1, R2⟩ := exec_shiftRep (V := V) (f := f) (dst := dst) (src := src) (sc := rY) (cl := cl)
    (ctr := CQ) ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1⟩ hs ⟨hc.1, by decide, hc.2⟩ w1
    (by rw [e1 src (Ne.symm hd.1) hs.2, e1 cl (Ne.symm hd.2.2.1) hc.2, hl])
  have hCQ : (w1 CQ).length = (w tC).length := by
    rw [hw1, Function.update_self, Function.update_of_ne (Ne.symm hd.2.2.2.2)]
  rw [hCQ, e1 src (Ne.symm hd.1) hs.2, e1 cl (Ne.symm hd.2.2.1) hc.2] at R1
  refine ⟨?_, fun j a1 a2 a3 => ?_⟩
  · rw [R1, show w1 dst = w tD by simp [hw1, Function.update_apply, hd.2.2.2.1]]
    rw [List.drop_left' (by rw [hT])]
  · rw [R2 j a1 a2 a3, e1 j a1 a3]

/-- `ZKV := zv^k`. -/
def zkvC : Code := fillC ZKV 11 10 14 12
/-- `TTk := true^k`. -/
def ttkC : Code := fillC TTk OB 29 12 12
/-- `TT2 := [true, true]`. -/
def tt2C : Code := fillC TT2 OB 29 27 27
/-- The store `C^(W − 9) ++ ins`. -/
def stC : Code := ofList [.cp GST TST, .cp CQ TW9, .rep CQ (shiftOne GST CBW rX TSl), .mv GST INSW TINS]

/-- **The run of `f̂`.** -/
def fhatC : Code :=
  ofList [.gate 11 10 10, zkvC, ttkC, tt2C, insC, .cp RES TSl, cbC, .cp CBW RES, stC, gloopC nandC]

theorem exec_stC {S W : ℕ} (hW : 10 ≤ W) (w : St) {C : List Bool} (hC : w CBW = C)
    (hCl : C.length = S) (hts : (w TSl).length = S) (htst : (w TST).length = (W + 1) * S)
    (htw9 : (w TW9).length = W - 9) {ins : List (List Bool)} (hins : UV S ins)
    (hinsl : ins.length = 10) (hI : w INSW = ins.flatten) (htins : (w TINS).length = 10 * S) :
    exec V f stC w GST = (List.replicate (W - 10) C ++ (C :: ins)).flatten ∧
      ∀ j, j ≠ GST → j ≠ CQ → j ≠ rX → j ≠ INSW → exec V f stC w j = w j := by
  rw [show stC = ofList ([.cp GST TST, .cp CQ TW9] ++ [.rep CQ (shiftOne GST CBW rX TSl),
    .mv GST INSW TINS]) from rfl, exec_ofList_append]
  simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  set w1 := Function.update (Function.update w GST (w TST)) CQ
    (Function.update w GST (w TST) TW9) with hw1
  have e1 : ∀ j, j ≠ GST → j ≠ CQ → w1 j = w j := fun j a1 a2 => by
    simp [hw1, Function.update_apply, a1, a2]
  obtain ⟨R1, R2⟩ := exec_shiftRep (V := V) (f := f) (dst := GST) (src := CBW) (sc := rX) (cl := TSl)
    (ctr := CQ) (by decide) (by decide) (by decide) w1
    (by rw [e1 CBW (by decide) (by decide), e1 TSl (by decide) (by decide), hC, hCl, hts])
  have hCQ : (w1 CQ).length = W - 9 := by simp (config := {decide := true}) [hw1, Function.update_apply, htw9]
  rw [hCQ, e1 CBW (by decide) (by decide), e1 TSl (by decide) (by decide), hC, hts,
    show w1 GST = w TST by simp (config := {decide := true}) [hw1, Function.update_apply]] at R1
  generalize exec V f (.rep CQ (shiftOne GST CBW rX TSl)) w1 = v at R1 R2
  have hrep : UV S (List.replicate (W - 9) C) := fun x hx => by rw [List.eq_of_mem_replicate hx, hCl]
  rw [exec_mv_shift (d := GST) (s := INSW) (c := TINS) (x := ins.flatten) (L := []) (by decide)
    (by rw [R2 TINS (by decide) (by decide) (by decide), e1 TINS (by decide) (by decide), htins,
      length_flatten_of hins, hinsl]) (by rw [R2 INSW (by decide) (by decide) (by decide),
      e1 INSW (by decide) (by decide), hI, List.append_nil])]
  refine ⟨?_, fun j a1 a2 a3 a4 => ?_⟩
  · have hCf : (List.replicate (W - 9) C).flatten.length = (W - 9) * S := by
      rw [length_flatten_of hrep]; simp
    rw [Function.update_self, R1, drop_append_drop' (by simp only [List.length_append, hCf]; omega),
      List.append_assoc, List.drop_left' (by
        rw [htst, length_flatten_of hins, hinsl, ← Nat.add_mul]; congr 1; omega)]
    rw [← List.flatten_append, show W - 9 = (W - 10) + 1 by omega, List.replicate_succ',
      List.append_assoc, List.singleton_append]
  · rw [Function.update_of_ne a1, Function.update_of_ne a4, R2 j a1 a3 a2, e1 j a1 a2]

/-- The bundle of the input `i` of `f̂`. -/
def inBW {N K : ℕ} (bW wW : Fin 10 × BI N (K + 1) → List Bool)
    (ent : Fin 10 → Fin 2 × (Fin 2 × Fin (K + 1)) → List Bool) (i : Fin 10) (b : BI N (K + 1)) :
    List Bool :=
  jw (bW (i, b)) (wW (i, b)) (bitE K (ent i (b.1, b.2.1)) b.2.2.1.val b.2.2.2.val) N K

theorem insWords_flatten {N K : ℕ} (bW wW : Fin 10 × BI N (K + 1) → List Bool)
    (ent : Fin 10 → Fin 2 × (Fin 2 × Fin (K + 1)) → List Bool) :
    (insWords bW wW ent).flatten = ((List.finRange 10).map fun i => bw (inBW bW wW ent i)).flatten := by
  have h : (Enum.list (α := Fin 10 × BI N (K + 1))) =
      List.finRange 10 ×ˢ (Enum.list (α := BI N (K + 1))) := rfl
  rw [insWords, h, product_def', List.map_flatMap, flatten_flatMap']
  congr 1
  apply List.map_congr_left
  intro i _
  rw [List.map_map, bw]
  rfl

/-- **The initial words of the run of `f̂`.** -/
structure FInit (V K N W A1 Ad : ℕ) (one : List Bool) (gs : GateList)
    (bW wW : Fin 10 × BI N (K + 1) → List Bool)
    (ent : Fin 10 → Fin 2 × (Fin 2 × Fin (K + 1)) → List Bool) (RB RW RP : List Bool) (w : St) :
    Prop where
  tm : Tmpl V K w
  vone : w 10 = one
  ob : w OB = [true]
  zb : w ZB = [false]
  nv : (w TNV).length = N * V
  nkv : (w TNKV).length = N * ((K + 1) * V)
  t2k : (w T2K).length = 2 * (K + 1)
  tlb : (w TLB).length = (2 * (K + 1) * N + 1) * ((K + 1) * V)
  tcnt : (w TCNT).length = 2 * (K + 1) * N + 1
  th : (w TH).length = treeHeight N (K + 1)
  tn : (w TN).length = N
  tn1 : (w TN1).length = N - 1
  tn1v : (w TN1V).length = (N - 1) * V
  tkv : (w TKV).length = K * V
  t2knv : (w T2kNV).length = 2 * (N * ((K + 1) * V))
  t2kknv : (w T2kkNV).length = 2 * (K + 1) * (N * ((K + 1) * V))
  ta1 : (w TA1).length = A1
  tad : (w TAd).length = Ad
  tk1 : (w TK1).length = K - 1
  znk1 : w ZNK1 = List.replicate (N * K - 1) false
  hV : V = A1 + Ad + N * K
  hNK : 0 < N * K
  hK : 0 < K
  tnk : (w TNK).length = N * K
  t4k : (w T4k).length = 2 * (2 * (K + 1))
  t10 : (w T10).length = 10
  bst : w BSt = ((Enum.list (α := Fin 10 × BI N (K + 1))).map bW).flatten ++ RB
  wst : w WSt = ((Enum.list (α := Fin 10 × BI N (K + 1))).map wW).flatten ++ RW
  pst : w PSt = ((List.finRange 10).flatMap fun i => (qsL (K + 1)).map (ent i)).flatten ++ RP
  insw : (w INSW).length = 10 * ((Enum.list (α := BI N (K + 1))).length * V)
  tsl : (w TSl).length = (Enum.list (α := BI N (K + 1))).length * V
  tst : (w TST).length = (W + 1) * ((Enum.list (α := BI N (K + 1))).length * V)
  td2 : (w TD2).length = 2 * ((W + 1) * ((Enum.list (α := BI N (K + 1))).length * V))
  tw : (w TW).length = W
  tpad : (w TPAD).length = (W - 10) * ((Enum.list (α := BI N (K + 1))).length * V)
  tw9 : (w TW9).length = W - 9
  tins : (w TINS).length = 10 * ((Enum.list (α := BI N (K + 1))).length * V)
  gsw : w GS = gsW W gs
  gcnt : (w GCNT).length = gs.length

theorem flatten_replicate_single (n : ℕ) (b : Bool) :
    (List.replicate n [b]).flatten = List.replicate n b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, ih]; rfl

/-- **The run of `f̂` on the machine**: `OUTW` ends with the word of the output bundle of `f̂`
(`fhatV` at the orders `enumT`, `enumO`, the coefficients `gvExp q`, the step `fV V f`), for the
input bundles `inBW` built from the streams. -/
theorem exec_fhatC (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V)
    {N K W A1 Ad : ℕ} (hN : 0 < N) {one : List Bool} {gs : GateList} (hgs : gs.length + 10 ≤ W)
    (hbnd : ∀ g ∈ gs, g.1 ≤ W ∧ g.2 ≤ W) (hne : gs ≠ [])
    {bW wW : Fin 10 × BI N (K + 1) → List Bool} (hb : ∀ j, (bW j).length = A1)
    (hx : ∀ j, (wW j).length = Ad) {ent : Fin 10 → Fin 2 × (Fin 2 × Fin (K + 1)) → List Bool}
    (he : ∀ i q, (ent i q).length = N * K) {RB RW RP : List Bool} (w : St)
    (h : FInit V K N W A1 Ad one gs bW wW ent RB RW RP w) :
    exec V f fhatC w OUTW = bw (fhatV one (fV V f) (inBW bW wW ent) (enumT N (K + 1))
      (enumO N (K + 1)) (gvExp (2 ^ K)) (2 ^ K) (predOf 10 gs).1 (predOf 10 gs).2) := by
  set S := (Enum.list (α := BI N (K + 1))).length * V with hS
  have h1 : one.length = V := by rw [← h.vone]; exact h.tm.h10
  set zv := fV V f one one with hzv
  have hz : zv.length = V := by rw [hzv, fV]; exact hf _ _ (by simp) (by simp)
  have hin : ∀ i b, (inBW bW wW ent i b).length = V := fun i b => by
    simp [inBW, jw, hb, hx, h.hV]; have := h.hNK; omega
  rw [fhatC, show [Code.gate 11 10 10, zkvC, ttkC, tt2C, insC, .cp RES TSl, cbC, .cp CBW RES, stC,
    gloopC nandC] = [Code.gate 11 10 10, zkvC, ttkC, tt2C] ++ ([insC] ++ ([.cp RES TSl, cbC,
    .cp CBW RES] ++ ([stC] ++ [gloopC nandC]))) from rfl, exec_ofList_append, exec_ofList_append,
    exec_ofList_append, exec_ofList_append]
  -- `zv`, `zv^k`, `true^k`, `[true, true]`
  have P1 : NCtx V K N one zv (exec V f (ofList [Code.gate 11 10 10, zkvC, ttkC, tt2C]) w) ∧
      ∀ j, j ≠ 11 → j ≠ ZKV → j ≠ TTk → j ≠ TT2 → j ≠ rY → j ≠ CQ →
        exec V f (ofList [Code.gate 11 10 10, zkvC, ttkC, tt2C]) w j = w j := by
    simp only [exec_ofList, List.foldl_cons, List.foldl_nil, zkvC, ttkC, tt2C]
    have g1 : exec V f (.gate 11 10 10) w = Function.update w 11 zv := by
      simp [exec, fV, hzv, h.vone]
    rw [g1]
    have tm1 : Tmpl V K (Function.update w 11 zv) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp (config := {decide := true}) [Function.update_apply, hz, h.tm.h10, h.tm.h12,
          h.tm.h13, h.tm.h14, h.tm.h15, h.tm.h16, h.tm.h20, h.tm.h27, h.tm.h29]
    obtain ⟨Z1, Z2⟩ := exec_fillC (V := V) (f := f) (dst := ZKV) (src := 11) (cl := 10) (tD := 14)
      (tC := 12) (by decide) (by decide) (by decide) (by decide) (Function.update w 11 zv)
      (by rw [tm1.h11, tm1.h10]) (by rw [tm1.h14, tm1.h12, tm1.h10])
    rw [tm1.h12, show Function.update w 11 zv 11 = zv by simp] at Z1
    generalize exec V f (fillC ZKV 11 10 14 12) (Function.update w 11 zv) = w2 at Z1 Z2
    have tm2 : Tmpl V K w2 := tm1.of_eq fun j hj => Z2 j (by revert j hj; decide)
      (by revert j hj; decide) (by revert j hj; decide)
    have hOB2 : w2 OB = [true] := by
      rw [Z2 OB (by decide) (by decide) (by decide), Function.update_of_ne (by decide), h.ob]
    obtain ⟨T1, T2⟩ := exec_fillC (V := V) (f := f) (dst := TTk) (src := OB) (cl := 29) (tD := 12)
      (tC := 12) (by decide) (by decide) (by decide) (by decide) w2
      (by rw [hOB2, tm2.h29]; rfl) (by rw [tm2.h12, tm2.h29, Nat.mul_one])
    rw [tm2.h12, hOB2, flatten_replicate_single] at T1
    generalize exec V f (fillC TTk OB 29 12 12) w2 = w3 at T1 T2
    have tm3 : Tmpl V K w3 := tm2.of_eq fun j hj => T2 j (by revert j hj; decide)
      (by revert j hj; decide) (by revert j hj; decide)
    have hOB3 : w3 OB = [true] := by rw [T2 OB (by decide) (by decide) (by decide), hOB2]
    obtain ⟨U1, U2⟩ := exec_fillC (V := V) (f := f) (dst := TT2) (src := OB) (cl := 29) (tD := 27)
      (tC := 27) (by decide) (by decide) (by decide) (by decide) w3
      (by rw [hOB3, tm3.h29]; rfl) (by rw [tm3.h27, tm3.h29])
    rw [tm3.h27, hOB3, flatten_replicate_single] at U1
    generalize exec V f (fillC TT2 OB 29 27 27) w3 = w4 at U1 U2
    have e : ∀ j, j ≠ 11 → j ≠ ZKV → j ≠ TTk → j ≠ TT2 → j ≠ rY → j ≠ CQ → w4 j = w j :=
      fun j a1 a2 a3 a4 a5 a6 => by
        rw [U2 j a4 a5 a6, T2 j a3 a5 a6, Z2 j a2 a5 a6, Function.update_of_ne a1]
    refine ⟨⟨tm3.of_eq fun j hj => U2 j (by revert j hj; decide) (by revert j hj; decide)
        (by revert j hj; decide), by rw [e 10 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), h.vone],
      by rw [U2 11 (by decide) (by decide) (by decide), T2 11 (by decide) (by decide) (by decide),
        Z2 11 (by decide) (by decide) (by decide)]; simp,
      by rw [e OB (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.ob],
      by rw [e ZB (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.zb],
      by rw [e TNV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.nv],
      by rw [e TNKV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.nkv],
      by rw [e T2K (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.t2k],
      by rw [e TLB (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.tlb],
      by rw [e TCNT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.tcnt],
      by rw [e TH (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.th],
      U1, by rw [U2 TTk (by decide) (by decide) (by decide), T1],
      by rw [e TN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.tn],
      by rw [e TN1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.tn1],
      by rw [e TN1V (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.tn1v],
      by rw [e TKV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.tkv],
      by rw [e T2kNV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        h.t2knv],
      by rw [e T2kkNV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        h.t2kknv],
      by rw [U2 ZKV (by decide) (by decide) (by decide), T2 ZKV (by decide) (by decide)
        (by decide), Z1]⟩, e⟩
  obtain ⟨c1, e1⟩ := P1
  generalize exec V f (ofList [Code.gate 11 10 10, zkvC, ttkC, tt2C]) w = w1 at c1 e1
  have E1 : ∀ j, j.val ≥ 61 → j ≠ ZKV → j ≠ TTk → j ≠ TT2 → j ≠ rY → j ≠ CQ → w1 j = w j :=
    fun j hj a2 a3 a4 a5 a6 => e1 j (by rintro rfl; simp at hj) a2 a3 a4 a5 a6
  -- the inputs
  have hIT : ITmpl V A1 Ad N K w1 := ⟨c1.tm.h10, h.hV,
    by rw [E1 TA1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.ta1],
    by rw [E1 TAd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.tad],
    by rw [E1 TK1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.tk1],
    by rw [E1 ZNK1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.znk1],
    c1.tm.h29, h.hNK, h.hK⟩
  obtain ⟨I1, -, -, -, -, I6⟩ := exec_insC (V := V) (f := f) w1 hIT c1.tn c1.tm.h20
    (by rw [E1 TNK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.tnk])
    (by rw [E1 T4k (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.t4k])
    (by rw [E1 T10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.t10])
    bW wW hb hx ent he
    (by rw [E1 BSt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.bst])
    (by rw [E1 WSt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.wst])
    (by rw [E1 PSt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.pst])
  have hIW : (insWords bW wW ent).flatten.length = 10 * S := by
    rw [length_flatten_of (V := V) (fun y hy => by
      simp only [insWords, List.mem_map] at hy
      obtain ⟨j, -, rfl⟩ := hy
      simp [jw, hb, hx, h.hV]; have := h.hNK; omega), insWords, List.length_map]
    rw [show (Enum.list (α := Fin 10 × BI N (K + 1))).length =
      10 * (Enum.list (α := BI N (K + 1))).length by
        show (List.finRange 10 ×ˢ Enum.list (α := BI N (K + 1))).length = _
        rw [List.length_product, List.length_finRange], hS]; ring
  rw [E1 INSW (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    List.drop_left' (by rw [h.insw, hIW])] at I1
  have c2 : NCtx V K N one zv (exec V f (ofList [insC]) w1) := by
    simp only [exec_ofList, List.foldl_cons, List.foldl_nil]
    exact c1.exec _ (by decide +kernel)
  have e2 : ∀ j ∉ wr insC, exec V f (ofList [insC]) w1 j = w1 j := fun j hj => by
    simp only [exec_ofList, List.foldl_cons, List.foldl_nil]; exact I6 j hj
  have I1' : exec V f (ofList [insC]) w1 INSW = (insWords bW wW ent).flatten := by
    simp only [exec_ofList, List.foldl_cons, List.foldl_nil]; exact I1
  generalize exec V f (ofList [insC]) w1 = w2 at c2 e2 I1'
  have E2 : ∀ j, j ∉ wr insC → j.val ≥ 61 → j ≠ ZKV → j ≠ TTk → j ≠ TT2 → j ≠ rY → j ≠ CQ →
      w2 j = w j := fun j h0 hj a2 a3 a4 a5 a6 => by rw [e2 j h0, E1 j hj a2 a3 a4 a5 a6]
  -- the constant bundle
  set cst := constRepVV (N := N) (k := K + 1) one zv (gvExp (2 ^ K)) with hcst
  have hcl : (bw cst).length = S := length_bw (constRepVV_len one zv h1 hz _)
  have P3 : exec V f (ofList [.cp RES TSl, cbC, .cp CBW RES]) w2 CBW = bw cst ∧
      NCtx V K N one zv (exec V f (ofList [.cp RES TSl, cbC, .cp CBW RES]) w2) ∧
      ∀ j ∉ wr (ofList [.cp RES TSl, cbC, .cp CBW RES]),
        exec V f (ofList [.cp RES TSl, cbC, .cp CBW RES]) w2 j = w2 j := by
    refine ⟨?_, c2.exec _ (by decide +kernel), fun j hj => exec_not_mem _ _ _ hj⟩
    simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
    obtain ⟨R1, -, -⟩ := exec_cbC (V := V) (f := f) (K := K) hN (Function.update w2 RES (w2 TSl))
      (c2.upd RES (by decide) _)
    rw [Function.update_self, R1, Function.update_self, List.drop_left' (by
      rw [hcl, E2 TSl (by decide +kernel) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), h.tsl])]
  obtain ⟨p31, c3, p33⟩ := P3
  generalize exec V f (ofList [.cp RES TSl, cbC, .cp CBW RES]) w2 = w3 at p31 c3 p33
  have E3 : ∀ j, j ∉ wr (ofList [.cp RES TSl, cbC, .cp CBW RES]) → j ∉ wr insC → j.val ≥ 61 →
      j ≠ ZKV → j ≠ TTk → j ≠ TT2 → j ≠ rY → j ≠ CQ → w3 j = w j :=
    fun j h00 h0 hj a2 a3 a4 a5 a6 => by rw [p33 j h00, E2 j h0 hj a2 a3 a4 a5 a6]
  -- the store
  set ins := (List.finRange 10).map fun i => bw (inBW bW wW ent i) with hins
  have hinsu : UV S ins := fun x hx => by
    simp only [hins, List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact length_bw (hin i)
  have hinsl : ins.length = 10 := by simp [hins]
  obtain ⟨S1, S2⟩ := exec_stC (V := V) (f := f) (S := S) (W := W) (by omega) w3 p31 hcl
    (by rw [E3 TSl (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), h.tsl])
    (by rw [E3 TST (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), h.tst])
    (by rw [E3 TW9 (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), h.tw9]) hinsu hinsl
    (by rw [p33 INSW (by decide +kernel), I1', insWords_flatten])
    (by rw [E3 TINS (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), h.tins])
  simp only [exec_ofList, List.foldl_cons, List.foldl_nil]
  generalize exec V f stC w3 = w4 at S1 S2
  have E4 : ∀ j, j ≠ GST → j ≠ CQ → j ≠ rX → j ≠ INSW →
      j ∉ wr (ofList [.cp RES TSl, cbC, .cp CBW RES]) → j ∉ wr insC → j.val ≥ 61 →
      j ≠ ZKV → j ≠ TTk → j ≠ TT2 → j ≠ rY → w4 j = w j :=
    fun j b1 b2 b3 b4 h00 h0 hj a2 a3 a4 a5 => by
      rw [S2 j b1 b2 b3 b4, E3 j h00 h0 hj a2 a3 a4 a5 b2]
  have c4 : NCtx V K N one zv w4 := c3.of_eq fun j hj => S2 j (by revert j hj; decide)
    (by revert j hj; decide) (by revert j hj; decide) (by revert j hj; decide)
  -- the gates
  have hD : GData S W (bw cst) ins gs w4 := ⟨hcl, hinsu, hinsl, hgs, hbnd,
    by rw [E4 TSl (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (by decide), h.tsl],
    by rw [E4 TST (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (by decide), h.tst],
    by rw [E4 TD2 (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (by decide), h.td2],
    by rw [E4 TW (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (by decide), h.tw]⟩
  obtain ⟨-, G2, -, -⟩ := exec_gloopC (V := V) (f := f) (blockSpec_nandC hf hN one zv h1 hz) w4 hD
    c4 S1
    (by rw [E4 GS (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (by decide), h.gsw])
    (by rw [E4 GCNT (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (by decide), h.gcnt])
    (by rw [E4 TPAD (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (by decide), h.tpad])
  rw [G2 hne, hcst, getLast_gl_nandW one zv (inBW bW wW ent) hf h1 rfl hin gs hne]

/-! ### The run of the predicate -/

/-- **The run of the predicate.** -/
def gswC : Code := ofList [insGC, .cp CBW 10, stC, gloopC (.gate RES IA IB)]

/-- **The initial words of the run of the predicate** (`M = N K`). -/
structure GInit (V W A2 Ad M : ℕ) (one : List Bool) (gs : GateList) (pW rW : Fin 10 → List Bool)
    (xs RB RW : List Bool) (w : St) : Prop where
  it : ITmpl V A2 Ad M 1 w
  vone : w 10 = one
  t10 : (w T10).length = 10
  bst : w BSt = ((List.finRange 10).map pW).flatten ++ RB
  wst : w WSt = ((List.finRange 10).map rW).flatten ++ RW
  zs : w rZ = xs
  insw : (w INSW).length = 10 * V
  tsl : (w TSl).length = V
  tst : (w TST).length = (W + 1) * V
  td2 : (w TD2).length = 2 * ((W + 1) * V)
  tw : (w TW).length = W
  tpad : (w TPAD).length = (W - 10) * V
  tw9 : (w TW9).length = W - 9
  tins : (w TINS).length = 10 * V
  gsw : w GS = gsW W gs
  gcnt : (w GCNT).length = gs.length

/-- **The run of the predicate on the machine**: `OUTW` ends with the value of the predicate's
output wire for the step `fV V f`. -/
theorem exec_gswC (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V)
    {W A2 Ad M : ℕ} {one : List Bool} {gs : GateList} (hgs : gs.length + 10 ≤ W)
    (hbnd : ∀ g ∈ gs, g.1 ≤ W ∧ g.2 ≤ W) (hne : gs ≠ []) {pW rW : Fin 10 → List Bool}
    (hp : ∀ i, (pW i).length = A2) (hr : ∀ i, (rW i).length = Ad) {xs RB RW : List Bool} (w : St)
    (h : GInit V W A2 Ad M one gs pW rW xs RB RW w) :
    exec V f gswC w OUTW = valueOf (fun i : Fin 10 =>
        ((List.finRange 10).map fun i => jw (pW i) (rW i) (xs.getD i.val false) M 1).getD i.val [])
      one (fV V f) (predOf 10 gs).1 (predOf 10 gs).2 := by
  have h1 : one.length = V := by rw [← h.vone]; exact h.it.h10
  set ins := (List.finRange 10).map fun i => jw (pW i) (rW i) (xs.getD i.val false) M 1 with hins
  have hinsu : UV V ins := fun x hx => by
    simp only [hins, List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    simp [jw, hp, hr, h.it.hV]; have := h.it.hNK; omega
  have hinsl : ins.length = 10 := by simp [hins]
  simp only [gswC, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  obtain ⟨I1, I2⟩ := exec_insGC (V := V) (f := f) w h.it h.t10 pW rW hp hr xs h.bst h.wst h.zs
  rw [List.drop_left' (by rw [h.insw])] at I1
  generalize exec V f insGC w = w1 at I1 I2
  have hone1 : w1 10 = one := by rw [I2 10 (by decide), h.vone]
  obtain ⟨S1, S2⟩ := exec_stC (V := V) (f := f) (S := V) (W := W) (by omega)
    (Function.update w1 CBW (w1 10)) (by rw [Function.update_self, hone1]) h1
    (by rw [Function.update_of_ne (by decide), I2 TSl (by decide), h.tsl])
    (by rw [Function.update_of_ne (by decide), I2 TST (by decide), h.tst])
    (by rw [Function.update_of_ne (by decide), I2 TW9 (by decide), h.tw9]) hinsu hinsl
    (by rw [Function.update_of_ne (by decide), I1])
    (by rw [Function.update_of_ne (by decide), I2 TINS (by decide), h.tins])
  generalize exec V f stC (Function.update w1 CBW (w1 10)) = w2 at S1 S2
  have E2 : ∀ j, j ≠ GST → j ≠ CQ → j ≠ rX → j ≠ INSW → j ≠ CBW → j ∉ wr insGC → w2 j = w j :=
    fun j a1 a2 a3 a4 a5 a6 => by rw [S2 j a1 a2 a3 a4, Function.update_of_ne a5, I2 j a6]
  have hD : GData V W one ins gs w2 := ⟨h1, hinsu, hinsl, hgs, hbnd,
    by rw [E2 TSl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.tsl],
    by rw [E2 TST (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.tst],
    by rw [E2 TD2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.td2],
    by rw [E2 TW (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.tw]⟩
  obtain ⟨-, G2, -, -⟩ := exec_gloopC (V := V) (f := f) (blockSpec_gate hf) w2 hD trivial S1
    (by rw [E2 GS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.gsw])
    (by rw [E2 GCNT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.gcnt])
    (by rw [E2 TPAD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.tpad])
  rw [G2 hne, getLast_gl_values (fV V f) one ins hinsl gs hne]

end ValVM

end SigabaNeo.Tape
