import SigabaNeo.Lib.Lattices.ProgAlgo.ValLeaves
import SigabaNeo.Lib.Lattices.Algo.FhatShadow

/-!
# The tree of additions on the word machine

`prC` runs one round of `pairRound`: the numbers (`k V` bits each) of the stream `LS = 35` are
added two by two (`modAddC`) into the buffer `RB = 36`, which starts as a copy of the stream and
shrinks by one number per pair, so that it ends with exactly the sums, the odd number last; the
count `CN' = 38` of the next round is the count `CN = 37` minus the pairs. A parity word
`PAR = 40` (`OB = 41` the word `[true]`, `ZB = 42` the word `[false]`) tells the two elements of a
pair apart.
-/

set_option maxRecDepth 8192

namespace SigabaNeo.Tape

namespace ValVM

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP SigabaNeo.Lattices.Algo

variable {V : ℕ} {f : List Bool → List Bool → List Bool}

abbrev LS : Fin 120 := 35
abbrev RB : Fin 120 := 36
abbrev CN : Fin 120 := 37
abbrev CN' : Fin 120 := 38
abbrev CTP : Fin 120 := 39
abbrev PAR : Fin 120 := 40
abbrev OB : Fin 120 := 41
abbrev ZB : Fin 120 := 42

/-- One element of a round. -/
def prBody : Code :=
  .ifb PAR (ofList [.mv 25 LS 14, modAddC, .mv RB 26 14, .drop RB 14, .tl CN', .cp PAR ZB])
    (ofList [.mv 24 LS 14, .cp PAR OB])

/-- **One round of the tree of additions.** -/
def prC : Code := ofList [.cp RB LS, .cp CN' CN, .cp PAR ZB, .cp CTP CN, .rep CTP prBody,
  .ifb PAR (ofList [.cp 26 24, .mv RB 26 14]) .nop]

/-- The sums of the first `p` pairs. -/
theorem pairRoundV_drop {α : Type*} (one : α) (step : α → α → α) (zv : α) (q k : ℕ) :
    ∀ (p : ℕ) (L : List (List α)), 2 * p ≤ L.length →
      pairRoundV one step zv q k L =
        (pairRoundV one step zv q k L).take p ++ pairRoundV one step zv q k (L.drop (2 * p))
  | 0, L, _ => by simp
  | p + 1, a :: b :: rest, h => by
    simp only [pairRoundV, List.take_succ_cons, List.cons_append]
    rw [show 2 * (p + 1) = 2 * p + 1 + 1 by ring, List.drop_succ_cons, List.drop_succ_cons,
      ← pairRoundV_drop one step zv q k p rest (by simp at h; omega)]
  | p + 1, [], h => by simp at h
  | p + 1, [_], h => by simp at h; omega

/-- Flattened numbers. -/
def fl (L : List (List (List Bool))) : List Bool := (L.map List.flatten).flatten

theorem fl_cons (x : List (List Bool)) (L : List (List (List Bool))) : fl (x :: L) = x.flatten ++ fl L := by
  simp [fl]

/-- The invariant after `i` elements of a round on the numbers `L` (`p = i / 2` pairs done). -/
structure PInv (V K : ℕ) (f : List Bool → List Bool → List Bool) (w₀ : St)
    (L : List (List (List Bool))) (i : ℕ) (w : St) : Prop where
  ls : w LS = fl (L.drop i)
  rb : w RB = fl (L.drop (2 * (i / 2))) ++
    fl ((pairRoundV (w₀ 10) (fV V f) (w₀ 11) (2 ^ K) (K + 1) L).take (i / 2))
  x : i % 2 = 1 → w 24 = (L[2 * (i / 2)]?.getD []).flatten
  c24 : (w 24).length = (K + 1) * V
  c25 : (w 25).length = (K + 1) * V
  par : hd (w PAR) = decide (i % 2 = 1)
  cn : (w CN').length = (w₀ CN).length - i / 2
  tm : Tmpl V K w
  hi : ∀ j : Fin 120, 41 ≤ j.val → j ≠ CN' → w j = w₀ j
  one : w 10 = w₀ 10
  zv : w 11 = w₀ 11

theorem Tmpl.upd {K : ℕ} {w : St} (h : Tmpl V K w) (x : Fin 120)
    (hx : x ∉ ([10, 11, 12, 13, 14, 15, 16, 20, 27, 29] : List (Fin 120))) (v : List Bool) :
    Tmpl V K (Function.update w x v) :=
  h.of_eq fun j hj => Function.update_of_ne (fun e => hx (by rw [← e]; exact hj)) _ _

theorem pairRoundV_take_succ {α : Type*} (one : α) (step : α → α → α) (zv : α) (q k : ℕ) :
    ∀ (p : ℕ) (L : List (List α)) (h : 2 * p + 1 < L.length),
    (pairRoundV one step zv q k L).take (p + 1) = (pairRoundV one step zv q k L).take p ++
      [modAddV one step zv q k L[2 * p] L[2 * p + 1]]
  | 0, a :: b :: rest, _ => by simp [pairRoundV]
  | p + 1, a :: b :: rest, h => by
    simp only [pairRoundV, List.take_succ_cons, List.cons_append]
    rw [pairRoundV_take_succ one step zv q k p rest (by simp at h; omega)]
    congr 2
  | 0, [], h => by simp at h
  | 0, [_], h => by simp at h
  | p + 1, [], h => by simp at h
  | p + 1, [_], h => by simp at h

theorem fl_len {K : ℕ} {L : List (List (List Bool))}
    (hL : ∀ x ∈ L, x.length = K + 1 ∧ ∀ y ∈ x, y.length = V) : (fl L).length = L.length * ((K + 1) * V) := by
  induction L with
  | nil => simp [fl]
  | cons x L ih =>
    obtain ⟨hl, hv⟩ := hL x (by simp)
    rw [fl_cons, List.length_append, length_flatten_of hv, hl, ih (fun y hy => hL y (by simp [hy])),
      List.length_cons]
    ring

theorem pinv_step (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) {K : ℕ}
    {w₀ : St} {L : List (List (List Bool))}
    (hL : ∀ x ∈ L, x.length = K + 1 ∧ ∀ y ∈ x, y.length = V) (hOB : w₀ OB = [true])
    (hZB : w₀ ZB = [false]) {i : ℕ} (hi : i < L.length) {w : St} (h : PInv V K f w₀ L i w) :
    PInv V K f w₀ L (i + 1) (exec V f prBody (Function.update w CTP (w CTP).tail)) := by
  set u0 := Function.update w CTP (w CTP).tail with hu0
  have u0_ : ∀ j, j ≠ CTP → u0 j = w j := fun j hj => by simp [u0, Function.update_of_ne hj]
  obtain ⟨hx, hxv⟩ := hL L[i] (List.getElem_mem hi)
  have hxf : L[i].flatten.length = (K + 1) * V := by rw [length_flatten_of hxv, hx]
  have hdrop : L.drop i = L[i] :: L.drop (i + 1) := List.drop_eq_getElem_cons hi
  rcases Nat.mod_two_eq_zero_or_one i with hpar | hpar
  · -- the first element of a pair
    have hp : hd (u0 PAR) = false := by rw [u0_ PAR (by decide), h.par]; simp [hpar]
    have e : exec V f prBody u0 = exec V f (ofList [.mv 24 LS 14, .cp PAR OB]) u0 := by
      simp only [prBody, exec, hp]; rfl
    rw [e]
    simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
    rw [exec_mv_pop (x := L[i].flatten) (L := fl (L.drop (i + 1))) (by decide)
      (by rw [u0_ 24 (by decide), u0_ 14 (by decide), h.c24, h.tm.h14])
      (by rw [u0_ 14 (by decide), h.tm.h14, hxf])
      (by rw [u0_ LS (by decide), h.ls, hdrop, fl_cons])]
    have hi2 : (i + 1) / 2 = i / 2 := by omega
    refine ⟨?_, ?_, fun ho => ?_, ?_, ?_, ?_, ?_, ?_, fun j hj hjc => ?_, ?_, ?_⟩
    · simp (config := {decide := true}) [Function.update_apply]
    · simp (config := {decide := true}) only [Function.update_apply, if_false]
      rw [u0_ RB (by decide), h.rb, hi2]
    · simp (config := {decide := true}) only [Function.update_apply, if_false, if_true]
      rw [hi2, show 2 * (i / 2) = i by omega, List.getElem?_eq_getElem hi]; rfl
    · simp (config := {decide := true}) only [Function.update_apply, if_false, if_true]; exact hxf
    · simp (config := {decide := true}) only [Function.update_apply, if_false]
      rw [u0_ 25 (by decide)]; exact h.c25
    · simp (config := {decide := true}) only [Function.update_apply, if_true]
      rw [u0_ OB (by decide), h.hi OB (by decide) (by decide), hOB]; simp; omega
    · simp (config := {decide := true}) only [Function.update_apply, if_false]
      rw [u0_ CN' (by decide), h.cn, hi2]
    · exact ((((h.tm.upd CTP (by decide) _).upd LS (by decide) _).upd 24 (by decide) _).upd PAR
        (by decide) _)
    · simp only [Function.update_apply]
      rw [if_neg (fun e => by subst e; simp at hj), if_neg (fun e => by subst e; simp at hj),
        if_neg (fun e => by subst e; simp at hj), u0_ j (fun e => by subst e; simp at hj)]
      exact h.hi j hj hjc
    · simp (config := {decide := true}) only [Function.update_apply, if_false]
      rw [u0_ 10 (by decide)]; exact h.one
    · simp (config := {decide := true}) only [Function.update_apply, if_false]
      rw [u0_ 11 (by decide)]; exact h.zv
  · -- the second element of a pair
    set p := i / 2 with hp
    have hi1 : 2 * p + 1 = i := by omega
    have hp' : hd (u0 PAR) = true := by rw [u0_ PAR (by decide), h.par]; simp [hpar]
    have e : exec V f prBody u0 = exec V f (ofList [.mv 25 LS 14, modAddC, .mv RB 26 14,
        .drop RB 14, .tl CN', .cp PAR ZB]) u0 := by
      simp only [prBody, exec, hp']; rfl
    rw [e, show [Code.mv 25 LS 14, modAddC, .mv RB 26 14, .drop RB 14, .tl CN', .cp PAR ZB] =
      [.mv 25 LS 14] ++ [modAddC, .mv RB 26 14, .drop RB 14, .tl CN', .cp PAR ZB] from rfl,
      exec_ofList_append]
    have e1 : exec V f (ofList [.mv 25 LS 14]) u0 = Function.update (Function.update u0 LS
        (fl (L.drop (i + 1)))) 25 L[i].flatten := by
      simp only [exec_ofList, List.foldl_cons, List.foldl_nil]
      exact exec_mv_pop (by decide) (by rw [u0_ 25 (by decide), u0_ 14 (by decide), h.c25, h.tm.h14])
        (by rw [u0_ 14 (by decide), h.tm.h14, hxf]) (by rw [u0_ LS (by decide), h.ls, hdrop, fl_cons])
    rw [e1]
    set u1 := Function.update (Function.update u0 LS (fl (L.drop (i + 1)))) 25 L[i].flatten with hu1
    have u1_ : ∀ j, j ≠ 25 → j ≠ LS → j ≠ CTP → u1 j = w j := fun j h25 hLS hc => by
      simp [u1, Function.update_of_ne h25, Function.update_of_ne hLS, u0_ j hc]
    have hi0 : 2 * p < L.length := by omega
    obtain ⟨hx0, hxv0⟩ := hL L[2 * p] (List.getElem_mem hi0)
    have hX : u1 24 = L[2 * p].flatten := by
      rw [u1_ 24 (by decide) (by decide) (by decide), h.x hpar, List.getElem?_eq_getElem hi0]; rfl
    have tm1 : Tmpl V K u1 := ((h.tm.upd CTP (by decide) _).upd LS (by decide) _).upd 25 (by decide) _
    have hadd := exec_modAddC (V := V) (f := f) hf u1 K L[2 * p] L[i] hx0 hx hxv0 hxv tm1.h10
      tm1.h11 hX (by simp [u1]) tm1.h12 tm1.h13 tm1.h14 tm1.h15 tm1.h16 tm1.h20 tm1.h27
    rw [u1_ 10 (by decide) (by decide) (by decide), u1_ 11 (by decide) (by decide) (by decide),
      h.one, h.zv] at hadd
    set Zv := modAddV (w₀ 10) (fV V f) (w₀ 11) (2 ^ K) (K + 1) L[2 * p] L[i]
    have hZl : Zv.flatten.length = (K + 1) * V := by
      obtain ⟨l, v⟩ := modAddV_shape hf (one := w₀ 10) (zv := w₀ 11) (by rw [← h.one]; exact h.tm.h10)
        (by rw [← h.zv]; exact h.tm.h11) (2 ^ K) (K + 1) L[2 * p] L[i] hx0 hx
      rw [length_flatten_of v, l]
    have u2_ : ∀ j : Fin 120, j ∉ wr modAddC → exec V f modAddC u1 j = u1 j :=
      fun j hj => exec_not_mem modAddC u1 j hj
    have tm2 : Tmpl V K (exec V f modAddC u1) := tm1.exec modAddC (by decide)
    simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
    generalize exec V f modAddC u1 = u2 at hadd u2_ tm2
    rw [exec_mv_push (by decide) (by rw [hadd, hZl, tm2.h14])]
    have u2hi : ∀ j : Fin 120, 27 ≤ j.val → u2 j = u1 j := fun j hj =>
      u2_ j (fun hm => by
        have : ∀ x ∈ wr modAddC, x.val < 27 := by decide
        have := this j hm; omega)
    simp only [exec, show ¬ (RB = (14 : Fin 120)) by decide, if_false, Function.update_self]
    have hi2 : (i + 1) / 2 = p + 1 := by omega
    have hil : 2 * p + 1 < L.length := by omega
    obtain ⟨hx1, hxv1⟩ := hL L[2 * p + 1] (List.getElem_mem hil)
    have e2p : L[2 * p + 1] = L[i] := by simp [hi1]
    refine ⟨?_, ?_, fun ho => by omega, ?_, ?_, ?_, ?_, ?_, fun j hj hjc => ?_, ?_, ?_⟩
    · simp (config := {decide := true}) only [Function.update_apply, if_false]
      rw [u2hi LS (by decide)]; simp (config := {decide := true}) [u1, Function.update_apply]
    · simp (config := {decide := true}) only [Function.update_apply, if_false, if_true]
      rw [u2hi RB (by decide), u1_ RB (by decide) (by decide) (by decide), h.rb, hadd, tm2.h14, hi2,
        List.drop_eq_getElem_cons hi0, List.drop_eq_getElem_cons hil, fl_cons, fl_cons,
        pairRoundV_take_succ _ _ _ _ _ p L hil]
      simp only [fl, List.map_append, List.flatten_append, List.map_cons, List.map_nil,
        List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
      rw [List.drop_left' (by rw [length_flatten_of hxv0, hx0]), List.drop_left' (by
          rw [length_flatten_of hxv1, hx1]), ← hp, show 2 * (p + 1) = 2 * p + 1 + 1 by ring, e2p]
    · simp (config := {decide := true}) only [Function.update_apply, if_false]
      rw [u2_ 24 (by decide), u1_ 24 (by decide) (by decide) (by decide)]; exact h.c24
    · simp (config := {decide := true}) only [Function.update_apply, if_false]
      rw [u2_ 25 (by decide)]; simp [u1, hxf]
    · simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
      rw [u2hi ZB (by decide), u1_ ZB (by decide) (by decide) (by decide),
        h.hi ZB (by decide) (by decide), hZB]; simp; omega
    · simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
      rw [List.length_tail, u2hi CN' (by decide), u1_ CN' (by decide) (by decide) (by decide), h.cn,
        hi2]
      omega
    · exact ((((tm2.upd 26 (by decide) _).upd RB (by decide) _).upd RB (by decide) _).upd CN'
        (by decide) _).upd PAR (by decide) _
    · simp only [Function.update_apply]
      rw [if_neg (fun e => by subst e; simp at hj), if_neg hjc,
        if_neg (fun e => by subst e; simp at hj), if_neg (fun e => by subst e; simp at hj),
        if_neg (fun e => by subst e; simp at hj), u2hi j (by omega),
        u1_ j (fun e => by subst e; simp at hj) (fun e => by subst e; simp at hj)
          (fun e => by subst e; simp at hj)]
      exact h.hi j hj hjc
    · simp (config := {decide := true}) only [Function.update_apply, if_false]
      rw [u2_ 10 (by decide), u1_ 10 (by decide) (by decide) (by decide)]; exact h.one
    · simp (config := {decide := true}) only [Function.update_apply, if_false]
      rw [u2_ 11 (by decide), u1_ 11 (by decide) (by decide) (by decide)]; exact h.zv

theorem length_pairRoundV {α : Type*} (one : α) (step : α → α → α) (zv : α) (q k : ℕ) :
    ∀ L : List (List α), (pairRoundV one step zv q k L).length = (L.length + 1) / 2
  | [] => by simp [pairRoundV]
  | [_] => by simp [pairRoundV]
  | a :: b :: rest => by
    simp only [pairRoundV, List.length_cons, length_pairRoundV one step zv q k rest]; omega

/-- **One round of the tree of additions**: `RB` ends with the flattened `pairRoundV` of the numbers
of `LS`, `CN'` with as many bits as the next round has numbers. -/
theorem exec_prC (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) {K : ℕ} (w : St)
    (L : List (List (List Bool))) (hL : ∀ x ∈ L, x.length = K + 1 ∧ ∀ y ∈ x, y.length = V)
    (htm : Tmpl V K w) (hOB : w OB = [true]) (hZB : w ZB = [false]) (hLS : w LS = fl L)
    (hCN : (w CN).length = L.length) (h24 : (w 24).length = (K + 1) * V)
    (h25 : (w 25).length = (K + 1) * V) :
    exec V f prC w RB = fl (pairRoundV (w 10) (fV V f) (w 11) (2 ^ K) (K + 1) L) ∧
      (exec V f prC w CN').length = (L.length + 1) / 2 ∧
      Tmpl V K (exec V f prC w) ∧ ((exec V f prC w) 24).length = (K + 1) * V ∧
      ((exec V f prC w) 25).length = (K + 1) * V ∧
      ∀ j : Fin 120, 41 ≤ j.val → j ≠ CN' → exec V f prC w j = w j := by
  rw [show prC = ofList ([.cp RB LS, .cp CN' CN, .cp PAR ZB, .cp CTP CN] ++
    [.rep CTP prBody, .ifb PAR (ofList [.cp 26 24, .mv RB 26 14]) .nop]) from rfl, exec_ofList_append]
  set w1 := Function.update (Function.update (Function.update (Function.update w RB (w LS)) CN'
    (w CN)) PAR (w ZB)) CTP (w CN) with hw1
  have hpre : exec V f (ofList [.cp RB LS, .cp CN' CN, .cp PAR ZB, .cp CTP CN]) w = w1 := by
    simp (config := {decide := true}) only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp',
      Function.update_apply, if_true, if_false, hw1]
  rw [hpre]
  have h0 : PInv V K f w L 0 w1 := by
    refine ⟨?_, ?_, fun h => by simp at h, ?_, ?_, ?_, ?_, ?_, fun j hj hjc => ?_, ?_, ?_⟩
    · simp (config := {decide := true}) [w1, Function.update_apply, hLS]
    · simp (config := {decide := true}) [w1, Function.update_apply, hLS, fl]
    · simp (config := {decide := true}) [w1, Function.update_apply, h24]
    · simp (config := {decide := true}) [w1, Function.update_apply, h25]
    · simp (config := {decide := true}) [w1, Function.update_apply, hZB, hd]
    · simp (config := {decide := true}) [w1, Function.update_apply]
    · exact (((htm.upd RB (by decide) _).upd CN' (by decide) _).upd PAR (by decide) _).upd CTP
        (by decide) _
    · simp only [w1, Function.update_apply]
      rw [if_neg (fun e => by subst e; simp at hj), if_neg (fun e => by subst e; simp at hj),
        if_neg hjc, if_neg (fun e => by subst e; simp at hj)]
    · simp (config := {decide := true}) [w1, Function.update_apply]
    · simp (config := {decide := true}) [w1, Function.update_apply]
  have hloop := exec_rep_inv (V := V) (f := f) (c := CTP) (B := prBody)
    (fun i w' => i ≤ L.length → PInv V K f w L i w')
    (fun i w' ih hi => pinv_step hf hL hOB hZB (by omega) (ih (by omega))) w1 (fun _ => h0)
  have hn : (w1 CTP).length = L.length := by simp [w1, hCN]
  rw [hn] at hloop
  have hP := hloop le_rfl
  simp only [exec_ofList, List.foldl_cons, List.foldl_nil]
  generalize exec V f (.rep CTP prBody) w1 = u at hP
  set p := L.length / 2 with hp
  have hdec := pairRoundV_drop (w 10) (fV V f) (w 11) (2 ^ K) (K + 1) p L (by omega)
  rcases Nat.mod_two_eq_zero_or_one L.length with hpar | hpar
  · have hb : hd (u PAR) = false := by rw [hP.par]; simp [hpar]
    simp only [exec, hb, Bool.false_eq_true, if_false]
    have hd0 : L.drop (2 * p) = [] := List.drop_eq_nil_of_le (by omega)
    refine ⟨?_, ?_, hP.tm, hP.c24, hP.c25, fun j hj hjc => hP.hi j hj hjc⟩
    · rw [hP.rb, ← hp, hd0]
      conv_rhs => rw [hdec, hd0]
      simp [fl, pairRoundV]
    · rw [hP.cn, hCN]; omega
  · have hb : hd (u PAR) = true := by rw [hP.par]; simp [hpar]
    simp only [exec, hb, if_true]
    have hlt : 2 * p < L.length := by omega
    have hd1 : L.drop (2 * p) = [L[2 * p]] := by
      rw [List.drop_eq_getElem_cons hlt, List.drop_eq_nil_of_le (by omega)]
    have hX : u 24 = L[2 * p].flatten := by
      rw [hP.x hpar, ← hp, List.getElem?_eq_getElem hlt]; rfl
    simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
    rw [exec_mv_push (by decide) (by simp [hP.c24, hP.tm.h14])]
    refine ⟨?_, ?_, ?_, ?_, ?_, fun j hj hjc => ?_⟩
    · simp (config := {decide := true}) only [Function.update_self, Function.update_apply, if_false]
      rw [hP.rb, ← hp, hd1, hX, hP.tm.h14]
      conv_rhs => rw [hdec, hd1]
      obtain ⟨hl, hv⟩ := hL _ (List.getElem_mem hlt)
      simp only [fl, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.map_append, List.flatten_append, pairRoundV]
      rw [List.append_assoc, List.drop_left' (by rw [length_flatten_of hv, hl])]
    · simp (config := {decide := true}) only [Function.update_apply, if_false]
      rw [hP.cn, hCN]; omega
    · exact ((hP.tm.upd 26 (by decide) _).upd 26 (by decide) _).upd RB (by decide) _
    · simp (config := {decide := true}) only [Function.update_apply, if_false]; exact hP.c24
    · simp (config := {decide := true}) only [Function.update_apply, if_false]; exact hP.c25
    · simp only [Function.update_apply]
      rw [if_neg (fun e => by subst e; simp at hj), if_neg (fun e => by subst e; simp at hj),
        if_neg (fun e => by subst e; simp at hj)]
      exact hP.hi j hj hjc

/-- The counter of the rounds and its template. -/
abbrev CTH : Fin 120 := 43
abbrev TH : Fin 120 := 44

/-- **The rounds**: `|TH|` rounds of `prC`, each round's sums becoming the next round's stream. -/
def roundsC : Code := ofList [.cp CTH TH, .rep CTH (ofList [prC, .cp LS RB, .cp CN CN'])]

theorem roundsV_eq_iterate {α : Type*} (one : α) (step : α → α → α) (zv : α) (q k : ℕ) :
    ∀ (h : ℕ) (L : List (List α)),
      roundsV one step zv q k h L = (pairRoundV one step zv q k)^[h] L
  | 0, L => rfl
  | h + 1, L => by
    rw [roundsV, roundsV_eq_iterate one step zv q k h, Function.iterate_succ_apply]

theorem pairRoundV_shape (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V)
    {one zv : List Bool} (h1 : one.length = V) (hz : zv.length = V) (K : ℕ) :
    ∀ L : List (List (List Bool)), (∀ x ∈ L, x.length = K + 1 ∧ ∀ y ∈ x, y.length = V) →
      ∀ x ∈ pairRoundV one (fV V f) zv (2 ^ K) (K + 1) L, x.length = K + 1 ∧ ∀ y ∈ x, y.length = V
  | [], _, x, hx => by simp [pairRoundV] at hx
  | [a], hL, x, hx => by simp [pairRoundV] at hx; subst hx; exact hL _ (by simp)
  | a :: b :: rest, hL, x, hx => by
    simp only [pairRoundV, List.mem_cons] at hx
    rcases hx with rfl | hx
    · obtain ⟨l, v⟩ := modAddV_shape hf h1 hz (2 ^ K) (K + 1) a b (hL a (by simp)).1
        (hL b (by simp)).1
      exact ⟨l, v⟩
    · exact pairRoundV_shape hf h1 hz K rest (fun y hy => hL y (by simp [hy])) x hx

theorem iterate_pairRoundV_shape (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V)
    {one zv : List Bool} (h1 : one.length = V) (hz : zv.length = V) (K : ℕ) :
    ∀ (h : ℕ) (L : List (List (List Bool))), (∀ x ∈ L, x.length = K + 1 ∧ ∀ y ∈ x, y.length = V) →
      ∀ x ∈ (pairRoundV one (fV V f) zv (2 ^ K) (K + 1))^[h] L,
        x.length = K + 1 ∧ ∀ y ∈ x, y.length = V
  | 0, L, hL => hL
  | h + 1, L, hL => by
    rw [Function.iterate_succ_apply']
    exact pairRoundV_shape hf h1 hz K _ (iterate_pairRoundV_shape hf h1 hz K h L hL)

/-- The invariant of the rounds. -/
structure RInv (V K : ℕ) (f : List Bool → List Bool → List Bool) (w₀ : St)
    (L : List (List (List Bool))) (h : ℕ) (w : St) : Prop where
  ls : w LS = fl ((pairRoundV (w₀ 10) (fV V f) (w₀ 11) (2 ^ K) (K + 1))^[h] L)
  cn : (w CN).length = ((pairRoundV (w₀ 10) (fV V f) (w₀ 11) (2 ^ K) (K + 1))^[h] L).length
  tm : Tmpl V K w
  c24 : (w 24).length = (K + 1) * V
  c25 : (w 25).length = (K + 1) * V
  hi : ∀ j : Fin 120, 41 ≤ j.val → j ≠ CTH → w j = w₀ j
  one : w 10 = w₀ 10
  zv : w 11 = w₀ 11

theorem exec_roundsC (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) {K : ℕ}
    (w : St) (L : List (List (List Bool)))
    (hL : ∀ x ∈ L, x.length = K + 1 ∧ ∀ y ∈ x, y.length = V)
    (htm : Tmpl V K w) (hOB : w OB = [true]) (hZB : w ZB = [false]) (hLS : w LS = fl L)
    (hCN : (w CN).length = L.length) (h24 : (w 24).length = (K + 1) * V)
    (h25 : (w 25).length = (K + 1) * V) :
    RInv V K f w L (w TH).length (exec V f roundsC w) := by
  have hone := htm.h10
  have hzv := htm.h11
  simp only [roundsC, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  have h0 : RInv V K f w L 0 (Function.update w CTH (w TH)) := by
    refine ⟨?_, ?_, htm.upd CTH (by decide) _, ?_, ?_, fun j hj hjc => ?_, ?_, ?_⟩
    · simp (config := {decide := true}) [Function.update_apply, hLS]
    · simp (config := {decide := true}) [Function.update_apply, hCN]
    · simp (config := {decide := true}) [Function.update_apply, h24]
    · simp (config := {decide := true}) [Function.update_apply, h25]
    · simp [Function.update_of_ne hjc]
    · simp (config := {decide := true}) [Function.update_apply]
    · simp (config := {decide := true}) [Function.update_apply]
  have := exec_rep_inv (V := V) (f := f) (c := CTH) (B := ofList [prC, .cp LS RB, .cp CN CN'])
    (fun h w' => RInv V K f w L h w')
    (fun h w' ih => by
      set u0 := Function.update w' CTH (w' CTH).tail
      have u0_ : ∀ j, j ≠ CTH → u0 j = w' j := fun j hj => by simp [u0, Function.update_of_ne hj]
      set Lh := (pairRoundV (w 10) (fV V f) (w 11) (2 ^ K) (K + 1))^[h] L
      have hLh : ∀ x ∈ Lh, x.length = K + 1 ∧ ∀ y ∈ x, y.length = V :=
        iterate_pairRoundV_shape hf hone hzv K h L hL
      obtain ⟨e1, e2, e3, e4, e5, e6⟩ := exec_prC hf u0 Lh hLh
        (ih.tm.upd CTH (by decide) _)
        (by rw [u0_ OB (by decide), ih.hi OB (by decide) (by decide), hOB])
        (by rw [u0_ ZB (by decide), ih.hi ZB (by decide) (by decide), hZB])
        (by rw [u0_ LS (by decide), ih.ls]) (by rw [u0_ CN (by decide), ih.cn])
        (by rw [u0_ 24 (by decide), ih.c24]) (by rw [u0_ 25 (by decide), ih.c25])
      simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
      have v10 : u0 10 = w 10 := by rw [u0_ 10 (by decide), ih.one]
      have v11 : u0 11 = w 11 := by rw [u0_ 11 (by decide), ih.zv]
      rw [v10, v11] at e1
      refine ⟨?_, ?_, ?_, ?_, ?_, fun j hj hjc => ?_, ?_, ?_⟩
      · simp (config := {decide := true}) only [Function.update_apply, if_false, if_true]
        rw [e1, Function.iterate_succ_apply']
      · simp (config := {decide := true}) [Function.update_apply]
        rw [e2, ← Function.iterate_succ_apply, Function.iterate_succ_apply', length_pairRoundV]
      · exact (e3.upd LS (by decide) _).upd CN (by decide) _
      · simp (config := {decide := true}) only [Function.update_apply, if_false]; exact e4
      · simp (config := {decide := true}) only [Function.update_apply, if_false]; exact e5
      · simp only [Function.update_apply]
        rw [if_neg (fun e => by subst e; simp at hj), if_neg (fun e => by subst e; simp at hj),
          e6 j hj (fun e => by subst e; simp at hj), u0_ j hjc, ih.hi j hj hjc]
      · simp (config := {decide := true}) only [Function.update_apply, if_false]
        rw [exec_not_mem prC u0 10 (by decide), v10]
      · simp (config := {decide := true}) only [Function.update_apply, if_false]
        rw [exec_not_mem prC u0 11 (by decide), v11])
    _ h0
  simpa using this

/-- **After enough rounds one number is left**: from `n ≤ 2^h` numbers (`n ≥ 1`), `h` rounds leave
exactly one, and `foldSumV` of it is that number. -/
theorem iterate_pairRoundV_single {α : Type*} (one : α) (step : α → α → α) (zv : α) (q k : ℕ) :
    ∀ (h : ℕ) (L : List (List α)), 1 ≤ L.length → L.length ≤ 2 ^ h →
      ((pairRoundV one step zv q k)^[h] L).length = 1
  | 0, L, h1, h2 => by simp at h2 ⊢; omega
  | h + 1, L, h1, h2 => by
    rw [Function.iterate_succ_apply]
    refine iterate_pairRoundV_single one step zv q k h _ ?_ ?_ <;>
      rw [length_pairRoundV]
    · omega
    · rw [pow_succ] at h2; omega

theorem foldSumV_single {α : Type*} (one : α) (step : α → α → α) (zv : α) (q k : ℕ)
    (L : List (List α)) (h : L.length = 1) : foldSumV one step zv q k L = L.head (by
      intro e; rw [e] at h; simp at h) := by
  match L, h with
  | [a], _ => rfl

end ValVM

end SigabaNeo.Tape
