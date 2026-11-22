import SigabaNeo.Lib.Lattices.ProgAlgo.ValBlock
import SigabaNeo.Lib.Encode.Enum

/-!
# A NAND block on the word machine

`nandC`: from the bundles `A` (word `IA = 61`) and `B` (`IB = 62`) of the two operands, in the order
of `BI N k` (`bw`), the bundle of the NAND block `nandV` (the shadow of `nandBlockL` at the orders
`enumT`, `enumO` and the gadget coefficients `gvExp q`, `q = 2 ^ K`, `k = K + 1`) is shifted into
`RES = 63` (`exec_nandC`). Loops, in the order of `BI`:

* `a` (`CA`): the reversed rows `rowRev A a c'` of the `2k` columns `c'` (`rrC` on each `k × N`
  block popped from the stream `SA` of `A`) into `RASB`;
* `col.1`, `col.2` (`C1`, `C2`): the digits of the column `col` of `B` (`DSSB`, from the streams
  `SB0`, `SB1` of the two halves of `B`), the constant `constV … (2 ^ col.2 mod q)` (`EC`), whether
  `a = col.1` (`DG`);
* `t` (`CT`): the constant of the coefficient (`CW`), the templates `TM0 = N − 1 − t`,
  `TT1 = t + 1`, `coefC`, its output shifted into `OUTB`;
* the `N × k` outputs of `(a, col)` transposed into `RES` (`trC`).
-/

namespace SigabaNeo.Tape

namespace ValVM

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP SigabaNeo.Lattices.Algo SigabaNeo.Encode

set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

variable {V : ℕ} {f : List Bool → List Bool → List Bool}

/-! ### Lists of uniform blocks -/

theorem length_flatten_unif {α : Type*} {C : ℕ} :
    ∀ (L : List (List α)), (∀ x ∈ L, x.length = C) → L.flatten.length = L.length * C
  | [], _ => by simp
  | x :: L, h => by
    rw [List.flatten_cons, List.length_append, h x (by simp),
      length_flatten_unif L (fun y hy => h y (by simp [hy])), List.length_cons, Nat.succ_mul]
    ring

theorem getElem_flatten_unif {α : Type*} {C : ℕ} :
    ∀ (L : List (List α)) (hL : ∀ x ∈ L, x.length = C) (i j : ℕ) (hi : i < L.length) (hj : j < C)
      (h : i * C + j < L.flatten.length),
      L.flatten[i * C + j] = L[i][j]'(by rw [hL _ (List.getElem_mem hi)]; exact hj)
  | [], _, i, j, hi, _, _ => absurd hi (by simp)
  | x :: L, hL, 0, j, _, hj, h => by
    have hx : x.length = C := hL x (by simp)
    simp only [Nat.zero_mul, Nat.zero_add, List.flatten_cons, List.getElem_cons_zero]
    rw [List.getElem_append_left (by omega)]
  | x :: L, hL, i + 1, j, hi, hj, h => by
    have hx : x.length = C := hL x (by simp)
    simp only [List.flatten_cons, List.getElem_cons_succ]
    rw [List.getElem_append_right (by rw [hx, Nat.succ_mul]; omega)]
    have e : (i + 1) * C + j - x.length = i * C + j := by rw [hx, Nat.succ_mul]; omega
    simp only [e]
    exact getElem_flatten_unif L (fun y hy => hL y (by simp [hy])) i j (by simpa using hi) hj _

/-- A product enumeration, mapped, at the index `i C + j`. -/
theorem getD_product_map {α β γ : Type*} (l₁ : List α) (l₂ : List β) (g : α × β → γ) (d : γ)
    {i j : ℕ} (hi : i < l₁.length) (hj : j < l₂.length) :
    ((l₁ ×ˢ l₂).map g).getD (i * l₂.length + j) d = g (l₁[i], l₂[j]) := by
  have hp : l₁ ×ˢ l₂ = l₁.flatMap fun a => l₂.map (a, ·) := rfl
  have hu : ∀ x ∈ l₁.map (fun a => (l₂.map (a, ·)).map g), x.length = l₂.length := by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨a, -, rfl⟩ := hx; simp
  have hlen : i * l₂.length + j < (l₁.map fun a => (l₂.map (a, ·)).map g).flatten.length := by
    rw [length_flatten_unif _ hu]
    have : (i + 1) * l₂.length ≤ l₁.length * l₂.length := Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at this; simp; omega
  rw [hp, List.map_flatMap, List.flatMap_def, List.getD_eq_getElem _ _ hlen,
    getElem_flatten_unif _ hu i j (by simpa using hi) hj hlen]
  simp

/-! ### Shifting values into a register -/

/-- Shifting the values `M` into a register holding the values `L`. -/
theorem shift_vals {L M : List (List Bool)} (hL : UV V L) (hM : UV V M) :
    (L.flatten ++ M.flatten).drop (M.length * V) = ((L ++ M).drop M.length).flatten := by
  rw [← List.flatten_append, ← drop_flatten_uv (hL.append hM)]

theorem shift_val {L : List (List Bool)} (hL : UV V L) {v : List Bool} (hv : v.length = V) :
    (L.flatten ++ v).drop V = ((L ++ [v]).drop 1).flatten := by
  have := shift_vals (M := [v]) hL (fun x hx => by simp at hx; subst hx; exact hv)
  simpa using this

/-! ### Registers of the block level -/

abbrev IA : Fin 128 := 61
abbrev IB : Fin 128 := 62
abbrev SA : Fin 128 := 64
abbrev SB0 : Fin 128 := 66
abbrev SB1 : Fin 128 := 67
abbrev DSSB : Fin 128 := 68
abbrev EC : Fin 128 := 69
abbrev FT : Fin 128 := 70
abbrev DG : Fin 128 := 71
abbrev CA : Fin 128 := 72
abbrev C1 : Fin 128 := 73
abbrev C2 : Fin 128 := 74
abbrev CT : Fin 128 := 75
abbrev CQ : Fin 128 := 85
abbrev CC2 : Fin 128 := 86
abbrev TT2 : Fin 128 := 90
abbrev TTk : Fin 128 := 91
abbrev TN1 : Fin 128 := 93
abbrev T2kNV : Fin 128 := 97
abbrev T2kkNV : Fin 128 := 98
abbrev ZKV : Fin 128 := 99

/-! ### The constant of a column -/

/-- One more `zv` shifted into `EC`. -/
def ecPush : Code := ofList [.cp rY 11, .mvV EC rY]

/-- `EC := constV one zv k (2 ^ col.2 mod 2 ^ K)`: `zv^K` then `one`, then `|C2| = K − col.2` more
`zv` (`col.2 < K`); `zv^k` when `C2` is empty (`col.2 = K`). -/
def ecC : Code :=
  .ifb C2 (ofList [.cp EC ZKV, .cp rY 10, .mvV EC rY, .cp CQ C2, .rep CQ ecPush]) (.cp EC ZKV)

theorem constV_two_pow {α : Type*} (one zv : α) :
    ∀ w c, c < w → constV one zv w (2 ^ c) = List.replicate c zv ++ one :: List.replicate (w - 1 - c) zv
  | 0, _, h => absurd h (by omega)
  | w + 1, 0, _ => by simp [constV, constV_zero]
  | w + 1, c + 1, h => by
    rw [constV, pow_succ, Nat.mul_mod_left, if_neg (by omega), Nat.mul_div_cancel _ (by norm_num),
      constV_two_pow one zv w c (by omega)]
    simp [List.replicate_succ, show w + 1 - 1 - (c + 1) = w - 1 - c by omega]
    omega

/-- The constant of the column `c` (`c ≤ K`): `2 ^ c mod 2 ^ K`. -/
theorem constV_gv {α : Type*} (one zv : α) (K c : ℕ) (hc : c ≤ K) :
    constV one zv (K + 1) (2 ^ c % 2 ^ K) =
      if c < K then List.replicate c zv ++ one :: List.replicate (K - c) zv
      else List.replicate (K + 1) zv := by
  split_ifs with h
  · rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) h), constV_two_pow one zv _ _ (by omega)]
    congr 3
  · rw [show c = K by omega, Nat.mod_self, constV_zero]

theorem ecPush_step {w₀ : St} (h11 : (w₀ 11).length = V) {base : List (List Bool)}
    (hb : UV V base) (_hbl : 0 < base.length) (r : ℕ) {w : St}
    (h : (∀ j, j ≠ EC → j ≠ rY → j ≠ CQ → w j = w₀ j) ∧
      w EC = ((base ++ List.replicate r (w₀ 11)).drop r).flatten) :
    (∀ j, j ≠ EC → j ≠ rY → j ≠ CQ →
        exec V f ecPush (Function.update w CQ (w CQ).tail) j = w₀ j) ∧
      exec V f ecPush (Function.update w CQ (w CQ).tail) EC =
        ((base ++ List.replicate (r + 1) (w₀ 11)).drop (r + 1)).flatten := by
  obtain ⟨hi, he⟩ := h
  simp only [ecPush, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  have h11' : w 11 = w₀ 11 := hi 11 (by decide) (by decide) (by decide)
  rw [exec_mvV_push (by decide) (by simp (config := {decide := true}) [Function.update_apply, h11', h11])]
  have hu : UV V ((base ++ List.replicate r (w₀ 11)).drop r) :=
    (hb.append (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact h11)).drop r
  refine ⟨fun j h1 h2 h3 => ?_, ?_⟩
  · simp only [Function.update_apply, if_neg h1, if_neg h2, if_neg h3]; exact hi j h1 h2 h3
  · simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [he, h11', shift_val hu h11, ← List.drop_append_of_le_length (by simp),
      List.drop_drop, List.append_assoc, ← List.replicate_succ']

/-- **The constant of a column**: with `|C2| = m ≤ K` (all `true`), `EC` gets the constant of
`2 ^ (K − m) mod 2 ^ K`. -/
theorem exec_ecC {K : ℕ} (w : St) (h10 : (w 10).length = V) (h11 : (w 11).length = V) {m : ℕ}
    (hm : m ≤ K) (hC2 : w C2 = List.replicate m true)
    (hZ : w ZKV = (List.replicate (K + 1) (w 11)).flatten) :
    exec V f ecC w EC = (constV (w 10) (w 11) (K + 1) (2 ^ (K - m) % 2 ^ K)).flatten ∧
      ∀ j, j ≠ EC → j ≠ rY → j ≠ CQ → exec V f ecC w j = w j := by
  rw [constV_gv _ _ K (K - m) (by omega)]
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have : hd (w C2) = false := by rw [hC2]; rfl
    simp only [ecC, exec_ifb', this, if_false, exec_cp', Function.update_self,
      if_neg (show ¬ K - 0 < K by omega), hZ]
    exact ⟨rfl, fun j h1 _ _ => Function.update_of_ne h1 _ _⟩
  · have : hd (w C2) = true := by
      rw [hC2]; obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩; rfl
    simp only [ecC, exec_ifb', this, if_true, exec_ofList, List.foldl_cons, List.foldl_nil,
      exec_cp']
    rw [if_pos (show K - m < K by omega)]
    set base := List.replicate K (w 11) ++ [w 10] with hbase
    have hb : UV V base := by
      intro x hx
      simp only [hbase, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · rw [List.eq_of_mem_replicate hx]; exact h11
      · exact h10
    rw [exec_mvV_push (by decide) (by
      simp (config := {decide := true}) [Function.update_apply, h10])]
    set w1 := Function.update (Function.update (Function.update (Function.update w EC (w ZKV))
      rY (Function.update w EC (w ZKV) 10)) rY []) EC
      ((Function.update (Function.update w EC (w ZKV)) rY (Function.update w EC (w ZKV) 10) EC ++
        Function.update (Function.update w EC (w ZKV)) rY (Function.update w EC (w ZKV) 10)
          rY).drop V) with hw1
    have w1EC : w1 EC = base.flatten := by
      simp (config := {decide := true}) only [hw1, Function.update_apply, if_true, if_false]
      rw [hZ, show ((List.replicate (K + 1) (w 11)).flatten ++ w 10) =
        (List.replicate (K + 1) (w 11) ++ [w 10]).flatten by simp,
        ← Nat.one_mul V, ← h10, drop_flatten_uv (V := (w 10).length) (by
          intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · rw [List.eq_of_mem_replicate hx, h11, h10]
          · rfl), hbase, List.replicate_succ, List.cons_append, List.drop_one, List.tail_cons]
    have w1o : ∀ j, j ≠ EC → j ≠ rY → w1 j = w j := fun j h1 h2 => by
      simp only [hw1, Function.update_apply, if_neg h1, if_neg h2]
    set w2 := Function.update w1 CQ (w1 C2) with hw2
    have I := exec_rep_inv (V := V) (f := f) (c := CQ) (B := ecPush)
      (fun r w' => (∀ j, j ≠ EC → j ≠ rY → j ≠ CQ → w' j = w2 j) ∧
        w' EC = ((base ++ List.replicate r (w2 11)).drop r).flatten)
      (fun r w' ih => ecPush_step (by
          rw [hw2, Function.update_of_ne (by decide), w1o 11 (by decide) (by decide)]; exact h11)
        hb (by simp [hbase]) r ih) w2 ⟨fun _ _ _ _ => rfl, by
          simp (config := {decide := true}) [hw2, Function.update_apply, w1EC]⟩
    have hn : (w2 CQ).length = m := by
      simp (config := {decide := true}) [hw2, Function.update_apply,
        w1o C2 (by decide) (by decide), hC2]
    obtain ⟨I1, I2⟩ := I
    rw [hn] at I2
    have w211 : w2 11 = w 11 := by
      rw [hw2, Function.update_of_ne (by decide), w1o 11 (by decide) (by decide)]
    refine ⟨?_, fun j h1 h2 h3 => ?_⟩
    · rw [I2, w211, hbase, List.append_assoc,
        List.drop_append_of_le_length (show m ≤ (List.replicate K (w 11)).length by simp; omega),
        List.drop_replicate, show K - (K - m) = m by omega]
      simp
    · rw [I1 j h1 h2 h3, hw2, Function.update_of_ne h3, w1o j h1 h2]

/-! ### The shape of an output coefficient -/

/-- **An output coefficient has `K + 1` values of `V` bits.** -/
theorem coefV_shape (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) {N K : ℕ}
    {one zv : List Bool} (h1 : one.length = V) (hz : zv.length = V)
    (A B : BI N (K + 1) → List Bool) (Gv : ℕ) (a : Fin 2) (col : Fin 2 × Fin (K + 1))
    (t : Fin N) : NShape V K (coefV one (fV V f) (enumT N (K + 1)) zv (2 ^ K) A B Gv a col t) := by
  set L := constV one zv (K + 1) Gv :: leavesV one (fV V f) zv (2 ^ K) (K + 1) A B a col t
    (enumT N (K + 1)) with hL
  have hLshape : ∀ x ∈ L, NShape V K x := by
    intro x hx
    rw [hL, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨constV_len _ _ _ _, constV_vals h1 hz _ _⟩
    · rw [leavesV_eq_map, List.mem_map] at hx
      obtain ⟨e, -, rfl⟩ := hx
      exact termV_shape hf K h1 hz A B a col t e
  have hLl : L.length = 2 * (K + 1) * N + 1 := by
    rw [hL, List.length_cons, leavesV_eq_map, List.length_map, enumT, List.length_product,
      List.length_product, List.length_finRange, List.length_finRange, List.length_finRange]
  have hpow : L.length ≤ 2 ^ treeHeight N (K + 1) := by
    rw [treeHeight, hLl]
    have := Nat.le_pow_clog (show 1 < 2 by norm_num)
      (Fintype.card ((Fin 2 × Fin (K + 1)) × Fin N) + 1)
    simp only [Fintype.card_prod, Fintype.card_fin] at this ⊢
    exact this
  have hsingle := iterate_pairRoundV_single one (fV V f) zv (2 ^ K) (K + 1)
    (treeHeight N (K + 1)) L (by omega) hpow
  obtain ⟨x, hx⟩ : ∃ x, (pairRoundV one (fV V f) zv (2 ^ K) (K + 1))^[treeHeight N (K + 1)] L =
      [x] := List.length_eq_one_iff.mp hsingle
  have hxs := iterate_pairRoundV_shape hf h1 hz K _ L hLshape x (by rw [hx]; simp)
  simp only [coefV]
  rw [roundsV_eq_iterate, ← hL, hx]
  exact hxs

/-! ### The data of a NAND block -/

/-- The read-only words of the block level: the templates of `coefC`, `one`, `zv`, the bits `OB`,
`ZB`, the templates of the loops and transposes, `zv^k`. -/
structure NCtx (V K N : ℕ) (one zv : List Bool) (w : St) : Prop where
  tm : Tmpl V K w
  vone : w 10 = one
  vzv : w 11 = zv
  ob : w OB = [true]
  zb : w ZB = [false]
  nv : (w TNV).length = N * V
  nkv : (w TNKV).length = N * ((K + 1) * V)
  t2k : (w T2K).length = 2 * (K + 1)
  tlb : (w TLB).length = (2 * (K + 1) * N + 1) * ((K + 1) * V)
  tcnt : (w TCNT).length = 2 * (K + 1) * N + 1
  th : (w TH).length = treeHeight N (K + 1)
  tt2 : w TT2 = [true, true]
  ttk : w TTk = List.replicate (K + 1) true
  tn : (w TN).length = N
  tn1 : (w TN1).length = N - 1
  tn1v : (w TN1V).length = (N - 1) * V
  tkv : (w TKV).length = K * V
  t2knv : (w T2kNV).length = 2 * (N * ((K + 1) * V))
  t2kknv : (w T2kkNV).length = 2 * (K + 1) * (N * ((K + 1) * V))
  zkv : w ZKV = (List.replicate (K + 1) zv).flatten

/-- The words of `NCtx`. -/
def nctxW : List (Fin 128) := [10, 11, 12, 13, 14, 15, 16, 20, 27, 29, OB, ZB, TNV, TNKV, T2K, TLB,
  TCNT, TH, TT2, TTk, TN, TN1, TN1V, TKV, T2kNV, T2kkNV, ZKV]

theorem NCtx.of_eq {K N : ℕ} {one zv : List Bool} {w w' : St} (h : NCtx V K N one zv w)
    (e : ∀ j ∈ nctxW, w' j = w j) : NCtx V K N one zv w' where
  tm := h.tm.of_eq fun j hj => e j (by revert j hj; decide)
  vone := by rw [e 10 (by decide)]; exact h.vone
  vzv := by rw [e 11 (by decide)]; exact h.vzv
  ob := by rw [e OB (by decide)]; exact h.ob
  zb := by rw [e ZB (by decide)]; exact h.zb
  nv := by rw [e TNV (by decide)]; exact h.nv
  nkv := by rw [e TNKV (by decide)]; exact h.nkv
  t2k := by rw [e T2K (by decide)]; exact h.t2k
  tlb := by rw [e TLB (by decide)]; exact h.tlb
  tcnt := by rw [e TCNT (by decide)]; exact h.tcnt
  th := by rw [e TH (by decide)]; exact h.th
  tt2 := by rw [e TT2 (by decide)]; exact h.tt2
  ttk := by rw [e TTk (by decide)]; exact h.ttk
  tn := by rw [e TN (by decide)]; exact h.tn
  tn1 := by rw [e TN1 (by decide)]; exact h.tn1
  tn1v := by rw [e TN1V (by decide)]; exact h.tn1v
  tkv := by rw [e TKV (by decide)]; exact h.tkv
  t2knv := by rw [e T2kNV (by decide)]; exact h.t2knv
  t2kknv := by rw [e T2kkNV (by decide)]; exact h.t2kknv
  zkv := by rw [e ZKV (by decide)]; exact h.zkv

/-- A code writing none of the words of `NCtx` keeps it. -/
theorem NCtx.exec {K N : ℕ} {one zv : List Bool} {w : St} (h : NCtx V K N one zv w) (c : Code)
    (hc : ∀ j ∈ nctxW, j ∉ wr c) : NCtx V K N one zv (exec V f c w) :=
  h.of_eq fun j hj => exec_not_mem c w j (hc j hj)

theorem NCtx.upd {K N : ℕ} {one zv : List Bool} {w : St} (h : NCtx V K N one zv w) (j : Fin 128)
    (hj : j ∉ nctxW) (x : List Bool) : NCtx V K N one zv (Function.update w j x) :=
  h.of_eq fun i hi => Function.update_of_ne (by rintro rfl; exact hj hi) _ _

/-- The digits of the column `col` of `B`, as `coefC` reads them. -/
def dssW {N K : ℕ} (B : BI N (K + 1) → List Bool) (col : Fin 2 × Fin (K + 1)) : List Bool :=
  (((cols (K + 1)).map (digitsOf B col)).map List.flatten).flatten

/-- The reversed rows of `A` at the row `a`, as `coefC` reads them. -/
def rasW {N K : ℕ} (A : BI N (K + 1) → List Bool) (a : Fin 2) : List Bool :=
  (((cols (K + 1)).map (rowRev A a)).map fl).flatten

/-- The output coefficients of `(a, col)` before `t`. -/
def outsT {N K : ℕ} (one zv : List Bool) (A B : BI N (K + 1) → List Bool) (a : Fin 2)
    (col : Fin 2 × Fin (K + 1)) (t : ℕ) : List (List Bool) :=
  ((List.finRange N).take t).flatMap fun t' =>
    coefV one (fV V f) (enumT N (K + 1)) zv (2 ^ K) A B (gvExp (2 ^ K) (a, col, t')) a col t'

/-! ### The loop over the coefficients `t` -/

/-- `CW := EC` at `t = 0`, `a = col.1`, else `zv^k`. -/
def cwC : Code := .ifb FT (.ifb DG (.cp CW EC) (.cp CW ZKV)) (.cp CW ZKV)

/-- The inputs of `coefC`. -/
def tPre : List Code :=
  [.cp TT1 TN, .drop TT1 TM0, cwC, .cp 30 14, .cp 31 10, .cp DSS DSSB, .cp RAS RASB]

/-- One coefficient: its inputs, `coefC`, its output shifted into `OUTB`. -/
def tBody : Code := ofList (tPre ++ [coefC, .mv OUTB OUT 14, .cp FT ZB, .tl TM0])

/-- **The coefficients of `(a, col)`**: `|TN| = N` rounds. -/
def tLoopC : Code := ofList [.cp FT OB, .cp TM0 TN1, .cp OUTB TNKV, .cp CT TN, .rep CT tBody]

/-- The invariant of the loop over `t`. -/
structure TInv (V K N : ℕ) (f : List Bool → List Bool → List Bool) (one zv : List Bool)
    (A B : BI N (K + 1) → List Bool) (a : Fin 2) (col : Fin 2 × Fin (K + 1)) (w₀ : St) (t : ℕ)
    (w : St) : Prop where
  ctx : NCtx V K N one zv w
  dssb : w DSSB = dssW B col
  rasb : w RASB = rasW A a
  ec : w EC = (constV one zv (K + 1) (2 ^ col.2.val % 2 ^ K)).flatten
  dg : w DG = [decide (a = col.1)]
  ft : w FT = [decide (t = 0)]
  tm0 : (w TM0).length = N - 1 - t
  outb : w OUTB = (w₀ OUTB ++ (outsT (V := V) (f := f) one zv A B a col t).flatten).drop
    (outsT (V := V) (f := f) one zv A B a col t).flatten.length

theorem exec_cwC {N K : ℕ} {one zv : List Bool} (a : Fin 2) (col : Fin 2 × Fin (K + 1)) (t : Fin N)
    (w : St) (hZ : w ZKV = (List.replicate (K + 1) zv).flatten)
    (hE : w EC = (constV one zv (K + 1) (2 ^ col.2.val % 2 ^ K)).flatten)
    (hD : w DG = [decide (a = col.1)]) (hF : w FT = [decide (t.val = 0)]) :
    exec V f cwC w = Function.update w CW
      (constV one zv (K + 1) (gvExp (2 ^ K) (a, col, t))).flatten := by
  simp only [cwC, exec_ifb', hF, hD, exec_cp', gvExp, hd]
  by_cases h0 : t.val = 0 <;> by_cases ha : a = col.1 <;>
    simp [h0, ha, hE, hZ, constV_zero]

theorem tInv_step (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) {N K : ℕ}
    {one zv : List Bool} (A B : BI N (K + 1) → List Bool) (hA : ∀ b, (A b).length = V)
    (hB : ∀ b, (B b).length = V) (a : Fin 2) (col : Fin 2 × Fin (K + 1)) {w₀ : St} {t : ℕ}
    (ht : t < N) {w : St} (h : TInv V K N f one zv A B a col w₀ t w) :
    TInv V K N f one zv A B a col w₀ (t + 1)
      (exec V f tBody (Function.update w CT (w CT).tail)) := by
  have c0 := h.ctx.upd CT (by decide) (w CT).tail
  have hw : ∀ j, j ≠ CT → Function.update w CT (w CT).tail j = w j :=
    fun j hj => Function.update_of_ne hj _ _
  have dss0 := (hw DSSB (by decide)).trans h.dssb
  have ras0 := (hw RASB (by decide)).trans h.rasb
  have ec0 := (hw EC (by decide)).trans h.ec
  have dg0 := (hw DG (by decide)).trans h.dg
  have ft0 := (hw FT (by decide)).trans h.ft
  have tm00 : (Function.update w CT (w CT).tail TM0).length = N - 1 - t :=
    ((congrArg List.length (hw TM0 (by decide)))).trans h.tm0
  have outb0 := (hw OUTB (by decide)).trans h.outb
  generalize Function.update w CT (w CT).tail = w' at c0 dss0 ras0 ec0 dg0 ft0 tm00 outb0
  obtain ⟨tt, htt⟩ : ∃ tt : Fin N, tt.val = t := ⟨⟨t, ht⟩, rfl⟩
  rw [tBody, exec_ofList_append]
  -- the inputs of `coefC`
  have pre : exec V f (ofList tPre) w' = Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update w' TT1 ((w' TN).drop (w' TM0).length))
      CW (constV one zv (K + 1) (gvExp (2 ^ K) (a, col, tt))).flatten) 30 (w' 14)) 31 (w' 10))
      DSS (w' DSSB)) RAS (w' RASB) := by
    simp only [tPre, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
    rw [exec_drop' (by decide)]
    simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    rw [exec_cwC (one := one) (zv := zv) a col tt _ (by simp (config := {decide := true}) [Function.update_apply, c0.zkv])
      (by simp (config := {decide := true}) [Function.update_apply, ec0])
      (by simp (config := {decide := true}) [Function.update_apply, dg0])
      (by simp (config := {decide := true}) [Function.update_apply, ft0, htt])]
    simp (config := {decide := true}) only [Function.update_apply, Function.update_idem, if_true,
      if_false]
  rw [pre]
  set u := Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update w' TT1 ((w' TN).drop (w' TM0).length))
      CW (constV one zv (K + 1) (gvExp (2 ^ K) (a, col, tt))).flatten) 30 (w' 14)) 31 (w' 10))
      DSS (w' DSSB)) RAS (w' RASB) with hu
  have cu : NCtx V K N one zv u := by
    refine c0.of_eq fun j hj => ?_
    have : j ≠ TT1 ∧ j ≠ CW ∧ j ≠ (30 : Fin 128) ∧ j ≠ (31 : Fin 128) ∧ j ≠ DSS ∧ j ≠ RAS := by
      revert j; decide
    simp [hu, Function.update_apply, this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1,
      this.2.2.2.2.2]
  have uo : ∀ j, j ≠ TT1 → j ≠ CW → j ≠ (30 : Fin 128) → j ≠ (31 : Fin 128) → j ≠ DSS →
      j ≠ RAS → u j = w' j := fun j h1 h2 h3 h4 h5 h6 => by
    simp [hu, Function.update_apply, h1, h2, h3, h4, h5, h6]
  have tmu : (u TM0).length = N - 1 - tt.val := by
    rw [uo TM0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), htt]
    exact tm00
  -- `coefC`
  have hC := exec_coefC (V := V) (f := f) hf u A B a col tt (gvExp (2 ^ K) (a, col, tt)) hA hB
    cu.tm (by simp (config := {decide := true}) [hu, Function.update_apply, c0.tm.h14])
    (by simp (config := {decide := true}) [hu, Function.update_apply, c0.tm.h10])
    cu.ob cu.zb (by simp (config := {decide := true}) [hu, Function.update_apply, cu.vone, cu.vzv,
      c0.vone, c0.vzv])
    (by simp (config := {decide := true}) [hu, Function.update_apply, dss0, dssW])
    (by simp (config := {decide := true}) [hu, Function.update_apply, ras0, rasW])
    cu.nv cu.nkv tmu
    (by simp (config := {decide := true}) only [hu, Function.update_apply, if_true, if_false]
        rw [List.length_drop, c0.tn, tm00]; omega)
    cu.t2k cu.tlb cu.tcnt cu.th
  rw [cu.vone, cu.vzv] at hC
  have hwr : ∀ j, j ∉ wr coefC → exec V f coefC u j = u j := fun j hj => exec_not_mem _ _ _ hj
  simp only [exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  generalize exec V f coefC u = v at hC hwr
  have hsh := coefV_shape (V := V) (f := f) hf (one := one) (zv := zv)
    (by rw [← c0.vone]; exact c0.tm.h10) (by rw [← c0.vzv]; exact c0.tm.h11) A B
    (gvExp (2 ^ K) (a, col, tt)) a col tt
  have hOl : (v OUT).length = (v 14).length := by
    rw [hC, length_flatten_of hsh.2, hsh.1, hwr 14 (by decide), cu.tm.h14]
  rw [exec_mv_push (by decide) hOl, exec_tl']
  have v_ : ∀ j ∈ nctxW, v j = w' j := fun j hj => by
    rw [hwr j (by revert j hj; decide), uo j (by revert j hj; decide) (by revert j hj; decide)
      (by revert j hj; decide) (by revert j hj; decide) (by revert j hj; decide)
      (by revert j hj; decide)]
  have cv : NCtx V K N one zv v := c0.of_eq v_
  have vo : ∀ j, j ∉ wr coefC → j ≠ TT1 → j ≠ CW → j ≠ (30 : Fin 128) → j ≠ (31 : Fin 128) →
      j ≠ DSS → j ≠ RAS → v j = w' j := fun j h0 h1 h2 h3 h4 h5 h6 => by
    rw [hwr j h0, uo j h1 h2 h3 h4 h5 h6]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine cv.of_eq fun j hj => ?_
    have : j ≠ OUTB ∧ j ≠ OUT ∧ j ≠ FT ∧ j ≠ TM0 := by revert j hj; decide
    simp [Function.update_apply, this.1, this.2.1, this.2.2.1, this.2.2.2]
  · simp (config := {decide := true}) only [Function.update_apply, if_false]
    rw [vo DSSB (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), dss0]
  · simp (config := {decide := true}) only [Function.update_apply, if_false]
    rw [vo RASB (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), ras0]
  · simp (config := {decide := true}) only [Function.update_apply, if_false]
    rw [vo EC (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), ec0]
  · simp (config := {decide := true}) only [Function.update_apply, if_false]
    rw [vo DG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), dg0]
  · simp (config := {decide := true}) only [Function.update_apply, if_false, if_true]
    rw [cv.zb]; simp
  · simp (config := {decide := true}) only [Function.update_apply, if_false, if_true,
      List.length_tail]
    rw [vo TM0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), tm00]
    omega
  · simp (config := {decide := true}) only [Function.update_apply, if_false, if_true]
    rw [vo OUTB (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), outb0, hC, hwr 14 (by decide), cu.tm.h14]
    have hl : (K + 1) * V = (coefV one (fV V f) (enumT N (K + 1)) zv (2 ^ K) A B
        (gvExp (2 ^ K) (a, col, tt)) a col tt).flatten.length := by
      rw [length_flatten_of hsh.2, hsh.1]
    rw [hl, shift_acc]
    have e : outsT (V := V) (f := f) one zv A B a col (t + 1) =
        outsT (V := V) (f := f) one zv A B a col t ++
          coefV one (fV V f) (enumT N (K + 1)) zv (2 ^ K) A B (gvExp (2 ^ K) (a, col, tt)) a
            col tt := by
      simp only [outsT]
      rw [List.take_succ, List.flatMap_append, List.getElem?_eq_getElem (by simpa using ht)]
      have : (List.finRange N)[t]'(by simpa using ht) = tt := Fin.ext (by simp [htt])
      simp [this]
    rw [e, List.flatten_append]

theorem outsT_shape (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) {N K : ℕ}
    {one zv : List Bool} (h1 : one.length = V) (hz : zv.length = V)
    (A B : BI N (K + 1) → List Bool) (a : Fin 2) (col : Fin 2 × Fin (K + 1)) (t : ℕ) :
    UV V (outsT (V := V) (f := f) one zv A B a col t) ∧
      (outsT (V := V) (f := f) one zv A B a col t).length = min t N * (K + 1) := by
  constructor
  · intro x hx
    simp only [outsT, List.mem_flatMap] at hx
    obtain ⟨t', -, hx⟩ := hx
    exact (coefV_shape hf h1 hz A B _ a col t').2 x hx
  · simp only [outsT, List.length_flatMap]
    rw [List.map_congr_left (fun t' _ => (coefV_shape hf h1 hz A B _ a col t').1),
      List.map_const', List.sum_replicate]
    simp

/-- **The coefficients of `(a, col)`**: `OUTB` ends with the `N` output coefficients. -/
theorem exec_tLoopC (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) {N K : ℕ}
    {one zv : List Bool} (A B : BI N (K + 1) → List Bool) (hA : ∀ b, (A b).length = V)
    (hB : ∀ b, (B b).length = V) (a : Fin 2) (col : Fin 2 × Fin (K + 1)) (w : St)
    (ctx : NCtx V K N one zv w) (hdss : w DSSB = dssW B col) (hras : w RASB = rasW A a)
    (hec : w EC = (constV one zv (K + 1) (2 ^ col.2.val % 2 ^ K)).flatten)
    (hdg : w DG = [decide (a = col.1)]) :
    exec V f tLoopC w OUTB = (outsT (V := V) (f := f) one zv A B a col N).flatten ∧
      NCtx V K N one zv (exec V f tLoopC w) ∧
      ∀ j ∉ wr tLoopC, exec V f tLoopC w j = w j := by
  refine ⟨?_, ctx.exec _ (by decide), fun j hj => exec_not_mem _ _ _ hj⟩
  simp only [tLoopC, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  set w1 := Function.update (Function.update (Function.update (Function.update w FT (w OB)) TM0
    (Function.update w FT (w OB) TN1)) OUTB (Function.update (Function.update w FT (w OB)) TM0
    (Function.update w FT (w OB) TN1) TNKV)) CT (Function.update (Function.update
    (Function.update w FT (w OB)) TM0 (Function.update w FT (w OB) TN1)) OUTB
    (Function.update (Function.update w FT (w OB)) TM0 (Function.update w FT (w OB) TN1) TNKV) TN)
    with hw1
  have e1 : ∀ j, j ≠ FT → j ≠ TM0 → j ≠ OUTB → j ≠ CT → w1 j = w j := fun j h1 h2 h3 h4 => by
    simp [hw1, Function.update_apply, h1, h2, h3, h4]
  have I := exec_rep_inv (V := V) (f := f) (c := CT) (B := tBody)
    (fun t w' => t ≤ N → TInv V K N f one zv A B a col w1 t w')
    (fun t w' ih ht => tInv_step hf A B hA hB a col (by omega) (ih (by omega))) w1
    (fun _ => ⟨ctx.of_eq fun j hj => e1 j (by revert j hj; decide) (by revert j hj; decide)
        (by revert j hj; decide) (by revert j hj; decide),
      by rw [e1 DSSB (by decide) (by decide) (by decide) (by decide), hdss],
      by rw [e1 RASB (by decide) (by decide) (by decide) (by decide), hras],
      by rw [e1 EC (by decide) (by decide) (by decide) (by decide), hec],
      by rw [e1 DG (by decide) (by decide) (by decide) (by decide), hdg],
      by simp (config := {decide := true}) [hw1, Function.update_apply, ctx.ob],
      by simp (config := {decide := true}) [hw1, Function.update_apply, ctx.tn1],
      by simp [outsT]⟩)
  have hn : (w1 CT).length = N := by
    simp (config := {decide := true}) [hw1, Function.update_apply, ctx.tn]
  rw [hn] at I
  have hI := (I le_rfl).outb
  rw [hI]
  have hw1O : w1 OUTB = w TNKV := by simp (config := {decide := true}) [hw1, Function.update_apply]
  obtain ⟨hu, hl⟩ := outsT_shape (V := V) (f := f) (one := one) (zv := zv) hf (by rw [← ctx.vone]; exact ctx.tm.h10)
    (by rw [← ctx.vzv]; exact ctx.tm.h11) A B a col N
  rw [hw1O, List.drop_left' (by rw [length_flatten_of hu, hl, ctx.nkv, min_self]; ring)]

/-! ### Blocks of a bundle -/

/-- The block `(a, c)` of a bundle: its `k × N` values `(i, j)`. -/
def blk {α : Type*} {N k : ℕ} (A : BI N k → α) (a : Fin 2) (c : Fin 2 × Fin k) : List α :=
  (List.finRange k ×ˢ List.finRange N).map fun p => A (a, c, p)

/-- The blocks of a bundle, in the order of `BI`. -/
def blocks {α : Type*} {N k : ℕ} (A : BI N k → α) : List (List α) :=
  (List.finRange 2 ×ˢ cols k).map fun q => blk A q.1 q.2

/-- **The word of a bundle**: its values in the order of `BI`. -/
def bw {N k : ℕ} (A : BI N k → List Bool) : List Bool := ((Enum.list (α := BI N k)).map A).flatten

theorem product_def' {α β : Type*} (l : List α) (m : List β) :
    l ×ˢ m = l.flatMap fun a => m.map (a, ·) := rfl

theorem cons_product' {α β : Type*} (a : α) (l : List α) (m : List β) :
    (a :: l) ×ˢ m = m.map (a, ·) ++ l ×ˢ m := rfl

theorem map_product_assoc {α β γ δ : Type*} (l₁ : List α) (l₂ : List β) (l₃ : List γ)
    (g : α × β × γ → δ) :
    (l₁ ×ˢ (l₂ ×ˢ l₃)).map g = ((l₁ ×ˢ l₂).map fun q => l₃.map fun p => g (q.1, q.2, p)).flatten := by
  induction l₁ with
  | nil => rfl
  | cons a l₁ ih =>
    rw [cons_product', cons_product', List.map_append, List.map_append, List.flatten_append, ih]
    congr 1
    rw [List.map_map, List.map_map]
    clear ih
    induction l₂ with
    | nil => rfl
    | cons b l₂ ih2 =>
      rw [cons_product', List.map_append, List.map_cons, List.flatten_cons, ih2, List.map_map]
      rfl

theorem bw_blocks {N k : ℕ} (A : BI N k → List Bool) :
    bw A = ((blocks A).map List.flatten).flatten := by
  have h : (Enum.list (α := BI N k)) =
      List.finRange 2 ×ˢ (cols k ×ˢ (List.finRange k ×ˢ List.finRange N)) := rfl
  rw [bw, h, map_product_assoc, blocks, List.map_map]
  simp only [Function.comp_def, blk]
  rw [List.flatten_flatten, List.map_map]
  rfl

/-! ### The outputs of `(a, col)` in the order of `BI` -/

theorem flatten_map_product {α β γ : Type*} (l₂ : List α) (l₃ : List β) (g : α × β → List γ) :
    ((l₂ ×ˢ l₃).map g).flatten = (l₂.map fun b => (l₃.map fun c => g (b, c)).flatten).flatten := by
  induction l₂ with
  | nil => rfl
  | cons b l₂ ih =>
    rw [cons_product', List.map_append, List.flatten_append, ih, List.map_map, List.map_cons,
      List.flatten_cons]
    rfl

theorem getElem_outsT (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) {N K : ℕ}
    {one zv : List Bool} (h1 : one.length = V) (hz : zv.length = V)
    (A B : BI N (K + 1) → List Bool) (a : Fin 2) (col : Fin 2 × Fin (K + 1)) (i : Fin (K + 1))
    (t : Fin N) :
    (outsT (V := V) (f := f) one zv A B a col N).getD (i.val + t.val * (K + 1)) [] =
      (coefV one (fV V f) (enumT N (K + 1)) zv (2 ^ K) A B (gvExp (2 ^ K) (a, col, t)) a col
        t).getD i.val one := by
  have hu : ∀ x ∈ (List.finRange N).map (fun t' => coefV one (fV V f) (enumT N (K + 1)) zv (2 ^ K)
      A B (gvExp (2 ^ K) (a, col, t')) a col t'), x.length = K + 1 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨t', -, rfl⟩ := hx
    exact (coefV_shape hf h1 hz A B _ a col t').1
  have e : outsT (V := V) (f := f) one zv A B a col N = ((List.finRange N).map fun t' =>
      coefV one (fV V f) (enumT N (K + 1)) zv (2 ^ K) A B (gvExp (2 ^ K) (a, col, t')) a col
        t').flatten := by
    rw [outsT, List.take_of_length_le (by simp), List.flatMap_def]
  have hsh := (coefV_shape hf h1 hz A B (gvExp (2 ^ K) (a, col, t)) a col t).1
  have hl : t.val * (K + 1) + i.val < (outsT (V := V) (f := f) one zv A B a col N).length := by
    rw [e, length_flatten_unif _ hu, List.length_map, List.length_finRange]
    have : (t.val + 1) * (K + 1) ≤ N * (K + 1) := Nat.mul_le_mul_right _ t.isLt
    rw [Nat.succ_mul] at this; have := i.isLt; omega
  rw [Nat.add_comm, List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ (by rw [hsh]; exact i.isLt)]
  simp only [e] at hl ⊢
  rw [getElem_flatten_unif _ hu t.val i.val (by simp) i.isLt hl]
  simp

/-- **The outputs of `(a, col)`, transposed, are the block `(a, col)` of the NAND's bundle.** -/
theorem trL_outsT (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) {N K : ℕ}
    {one zv : List Bool} (h1 : one.length = V) (hz : zv.length = V)
    (A B : BI N (K + 1) → List Bool) (a : Fin 2) (col : Fin 2 × Fin (K + 1)) :
    trL (outsT (V := V) (f := f) one zv A B a col N) (K + 1) N (K + 1) =
      blk (nandV one (fV V f) (enumT N (K + 1)) (enumO N (K + 1)) (gvExp (2 ^ K)) zv (2 ^ K) A B)
        a col := by
  rw [trL, blk, product_def', List.map_flatMap]
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
  congr 1
  funext i
  rw [colOf, ← List.map_coe_finRange_eq_range, List.map_map, List.map_map]
  congr 1
  funext t
  simp only [Function.comp_apply]
  rw [getElem_outsT hf h1 hz A B a col i t]
  simp [nandV, mem_enumO]

theorem dssW_eq {N K : ℕ} (B : BI N (K + 1) → List Bool) (col : Fin 2 × Fin (K + 1)) :
    dssW B col = (blk B 0 col).flatten ++ (blk B 1 col).flatten := by
  rw [dssW, blk, blk, flatten_map_product, flatten_map_product, List.map_map, cols,
    flatten_map_product, show List.finRange 2 = [0, 1] from rfl]
  simp [digitsOf, Function.comp_def]

theorem nandV_len (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) {N K : ℕ}
    {one zv : List Bool} (h1 : one.length = V) (hz : zv.length = V)
    (A B : BI N (K + 1) → List Bool) (hA : ∀ b, (A b).length = V) (hB : ∀ b, (B b).length = V)
    (b : BI N (K + 1)) :
    (nandV one (fV V f) (enumT N (K + 1)) (enumO N (K + 1)) (gvExp (2 ^ K)) zv (2 ^ K) A B b).length
      = V := by
  unfold nandV
  split_ifs
  · rw [List.getD_eq_getElem?_getD]
    rcases h : (coefV one (fV V f) (enumT N (K + 1)) zv (2 ^ K) A B
      (gvExp (2 ^ K) (b.1, b.2.1, b.2.2.2)) b.1 b.2.1 b.2.2.2)[b.2.2.1.val]? with _ | x
    · simpa using h1
    · simp only [Option.getD_some]
      exact (coefV_shape hf h1 hz A B _ _ _ _).2 x (List.mem_of_getElem? h)
  · exact h1

/-! ### One column -/

theorem exec_mv_shift {d s c : Fin 128} (h : ¬(d = s ∨ d = c ∨ s = c)) {w : St} {x L : List Bool}
    (hx : x.length = (w c).length) (hs : w s = x ++ L) :
    exec V f (.mv d s c) w = Function.update (Function.update w s L) d ((w d ++ x).drop x.length) := by
  simp only [exec, if_neg h, hs, shiftIn]
  rw [List.drop_left' hx, takeD_eq_take (by simp [hx]), List.take_left' hx, hx]

/-- The digits of the column. -/
def dsC : List Code := [.cp DSSB T2kNV, .mv DSSB SB0 TNKV, .mv DSSB SB1 TNKV]

/-- **One column `col`**: its digits, its constant, its `N` coefficients, transposed into `RES`. -/
def c2Body : Code := ofList (dsC ++ [ecC, tLoopC, trC])

/-- The words of a stream of blocks. -/
def bstream (L : List (List (List Bool))) : List Bool := (L.map List.flatten).flatten

theorem bstream_cons (x : List (List Bool)) (L : List (List (List Bool))) :
    bstream (x :: L) = x.flatten ++ bstream L := rfl

theorem blk_shape {N K : ℕ} {A : BI N (K + 1) → List Bool} (hA : ∀ b, (A b).length = V)
    (a : Fin 2) (c : Fin 2 × Fin (K + 1)) :
    UV V (blk A a c) ∧ (blk A a c).length = (K + 1) * N := by
  refine ⟨fun x hx => ?_, by simp [blk, List.length_product]⟩
  simp only [blk, List.mem_map] at hx
  obtain ⟨p, -, rfl⟩ := hx
  exact hA _

theorem blk_len {N K : ℕ} {A : BI N (K + 1) → List Bool} (hA : ∀ b, (A b).length = V)
    (a : Fin 2) (c : Fin 2 × Fin (K + 1)) : (blk A a c).flatten.length = N * ((K + 1) * V) := by
  rw [length_flatten_of (blk_shape hA a c).1, (blk_shape hA a c).2]; ring

/-- **One column**: with the streams of the blocks of `B` at `(0, col)` and `(1, col)`, `RES`
receives the block `(a, col)` of the NAND's bundle. -/
theorem exec_c2Body (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V) {N K : ℕ}
    {one zv : List Bool} (A B : BI N (K + 1) → List Bool)
    (hA : ∀ b, (A b).length = V) (hB : ∀ b, (B b).length = V) (a : Fin 2)
    (col : Fin 2 × Fin (K + 1)) (w : St) (ctx : NCtx V K N one zv w) (hras : w RASB = rasW A a)
    (hdg : w DG = [decide (a = col.1)]) {L0 L1 : List (List (List Bool))}
    (hs0 : w SB0 = bstream (blk B 0 col :: L0)) (hs1 : w SB1 = bstream (blk B 1 col :: L1))
    (hc2 : w C2 = List.replicate (K - col.2.val) true) :
    exec V f c2Body w RES = (w RES ++ (blk (nandV one (fV V f) (enumT N (K + 1)) (enumO N (K + 1))
        (gvExp (2 ^ K)) zv (2 ^ K) A B) a col).flatten).drop ((K + 1) * N * V) ∧
      exec V f c2Body w SB0 = bstream L0 ∧ exec V f c2Body w SB1 = bstream L1 ∧
      NCtx V K N one zv (exec V f c2Body w) ∧
      ∀ j ∉ wr c2Body, exec V f c2Body w j = w j := by
  have h1 : one.length = V := by rw [← ctx.vone]; exact ctx.tm.h10
  have hz : zv.length = V := by rw [← ctx.vzv]; exact ctx.tm.h11
  refine ⟨?_, ?_, ?_, ctx.exec _ (by decide), fun j hj => exec_not_mem _ _ _ hj⟩ <;>
    rw [c2Body, exec_ofList_append]
  all_goals
    -- the digits
    have hdD : exec V f (ofList dsC) w DSSB = dssW B col := by
      simp only [dsC, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
      rw [exec_mv_shift (d := DSSB) (s := SB0) (c := TNKV) (x := (blk B 0 col).flatten)
        (L := bstream L0) (by decide)
        (by simp (config := {decide := true}) [Function.update_apply, blk_len hB, ctx.nkv])
        (by simp (config := {decide := true}) [Function.update_apply, hs0, bstream_cons])]
      rw [exec_mv_shift (d := DSSB) (s := SB1) (c := TNKV) (x := (blk B 1 col).flatten)
        (L := bstream L1) (by decide)
        (by simp (config := {decide := true}) [Function.update_apply, blk_len hB, ctx.nkv])
        (by simp (config := {decide := true}) [Function.update_apply, hs1, bstream_cons])]
      simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
      rw [dssW_eq, drop_append_drop' (by rw [List.length_append, ctx.t2knv, blk_len hB]; omega),
        List.append_assoc, List.drop_left' (by rw [ctx.t2knv, blk_len hB, blk_len hB]; ring)]
    have hd0 : exec V f (ofList dsC) w SB0 = bstream L0 := by
      simp only [dsC, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
      rw [exec_mv_shift (d := DSSB) (s := SB0) (c := TNKV) (x := (blk B 0 col).flatten)
        (L := bstream L0) (by decide)
        (by simp (config := {decide := true}) [Function.update_apply, blk_len hB, ctx.nkv])
        (by simp (config := {decide := true}) [Function.update_apply, hs0, bstream_cons])]
      rw [exec_mv_shift (d := DSSB) (s := SB1) (c := TNKV) (x := (blk B 1 col).flatten)
        (L := bstream L1) (by decide)
        (by simp (config := {decide := true}) [Function.update_apply, blk_len hB, ctx.nkv])
        (by simp (config := {decide := true}) [Function.update_apply, hs1, bstream_cons])]
      simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    have hd1 : exec V f (ofList dsC) w SB1 = bstream L1 := by
      simp only [dsC, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
      rw [exec_mv_shift (d := DSSB) (s := SB0) (c := TNKV) (x := (blk B 0 col).flatten)
        (L := bstream L0) (by decide)
        (by simp (config := {decide := true}) [Function.update_apply, blk_len hB, ctx.nkv])
        (by simp (config := {decide := true}) [Function.update_apply, hs0, bstream_cons])]
      rw [exec_mv_shift (d := DSSB) (s := SB1) (c := TNKV) (x := (blk B 1 col).flatten)
        (L := bstream L1) (by decide)
        (by simp (config := {decide := true}) [Function.update_apply, blk_len hB, ctx.nkv])
        (by simp (config := {decide := true}) [Function.update_apply, hs1, bstream_cons])]
      simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
    have hdo : ∀ j, j ≠ DSSB → j ≠ SB0 → j ≠ SB1 → exec V f (ofList dsC) w j = w j :=
      fun j h1 h2 h3 => exec_not_mem _ _ _ (by simp [dsC, ofList, wr, h1, h2, h3])
    generalize exec V f (ofList dsC) w = u at hdD hd0 hd1 hdo
    have cu : NCtx V K N one zv u := ctx.of_eq fun j hj => hdo j (by revert j hj; decide)
      (by revert j hj; decide) (by revert j hj; decide)
    simp only [exec_ofList, List.foldl_cons, List.foldl_nil]
    -- the constant
    have hE := exec_ecC (V := V) (f := f) (K := K) u (by rw [cu.vone]; exact h1)
      (by rw [cu.vzv]; exact hz) (Nat.sub_le K col.2.val)
      (by rw [hdo C2 (by decide) (by decide) (by decide), hc2]) (by rw [cu.zkv, cu.vzv])
    rw [cu.vone, cu.vzv, show K - (K - col.2.val) = col.2.val by have := col.2.isLt; omega] at hE
    obtain ⟨hE1, hE2⟩ := hE
    generalize exec V f ecC u = u2 at hE1 hE2
    have cu2 : NCtx V K N one zv u2 := cu.of_eq fun j hj => hE2 j (by revert j hj; decide)
      (by revert j hj; decide) (by revert j hj; decide)
    -- the coefficients
    obtain ⟨hT1, cT, hT3⟩ := exec_tLoopC (V := V) (f := f) hf A B hA hB a col u2 cu2
      (by rw [hE2 DSSB (by decide) (by decide) (by decide), hdD])
      (by rw [hE2 RASB (by decide) (by decide) (by decide),
            hdo RASB (by decide) (by decide) (by decide), hras])
      hE1 (by rw [hE2 DG (by decide) (by decide) (by decide),
            hdo DG (by decide) (by decide) (by decide), hdg])
    generalize exec V f tLoopC u2 = u3 at hT1 cT hT3
    obtain ⟨hu3, hl3⟩ := outsT_shape (V := V) (f := f) (one := one) (zv := zv) hf h1 hz A B a col N
    -- the transpose
    obtain ⟨hR1, hR2⟩ := exec_trC (V := V) (f := f) hu3 (C := K + 1) (R := N) (Nat.succ_pos K)
      (by rw [hl3, min_self]) u3 hT1 (by rw [cT.vone]; exact h1) cT.tm.h12
      (by rw [cT.tkv]; simp) cT.tn
  · rw [hR1, trL_outsT hf h1 hz A B a col, hT3 RES (by decide),
      hE2 RES (by decide) (by decide) (by decide), hdo RES (by decide) (by decide) (by decide),
      length_flatten_of (blk_shape (nandV_len hf h1 hz A B hA hB) a col).1,
      (blk_shape (nandV_len hf h1 hz A B hA hB) a col).2]
  · rw [hR2 SB0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hT3 SB0 (by decide), hE2 SB0 (by decide) (by decide) (by decide), hd0]
  · rw [hR2 SB1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hT3 SB1 (by decide), hE2 SB1 (by decide) (by decide) (by decide), hd1]

end ValVM

end SigabaNeo.Tape
