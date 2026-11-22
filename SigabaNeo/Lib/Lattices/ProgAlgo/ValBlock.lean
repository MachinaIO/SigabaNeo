import SigabaNeo.Lib.Lattices.ProgAlgo.ValCoefFull

/-!
# Transposes of blocks of values on the word machine

The block level of a NAND (`ValNand`) reads the operands' coefficients in an order transposed from
the order of the bundles (`rowRev`: the coefficients of a row, the last first) and writes the output
coefficients transposed back. Both are **column loops** (`colC`): with a stream `Z` holding a
row-major list `L` of values (`V` bits each) from its entry `c` on, `R` rounds each move the first
value of `Z` into a buffer and skip `C − 1` values, so the buffer receives the column
`L[c], L[c + C], …, L[c + (R − 1) C]` (`exec_colLoop`).
-/

namespace SigabaNeo.Tape

namespace ValVM

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP SigabaNeo.Lattices.Algo

set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

variable {V : ℕ} {f : List Bool → List Bool → List Bool}

/-! ### Uniform lists of values -/

/-- Every value has `V` bits. -/
def UV (V : ℕ) (L : List (List Bool)) : Prop := ∀ x ∈ L, x.length = V

theorem UV.drop {L : List (List Bool)} (h : UV V L) (n : ℕ) : UV V (L.drop n) :=
  fun x hx => h x (List.mem_of_mem_drop hx)

theorem UV.take {L : List (List Bool)} (h : UV V L) (n : ℕ) : UV V (L.take n) :=
  fun x hx => h x (List.mem_of_mem_take hx)

theorem UV.append {L M : List (List Bool)} (h : UV V L) (h' : UV V M) : UV V (L ++ M) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  exacts [h x hx, h' x hx]

theorem drop_flatten_uv : ∀ {L : List (List Bool)}, UV V L → ∀ n : ℕ,
    L.flatten.drop (n * V) = (L.drop n).flatten
  | [], _, n => by simp
  | x :: L, h, 0 => by simp
  | x :: L, h, n + 1 => by
    have hx : x.length = V := h x (by simp)
    rw [List.flatten_cons, Nat.succ_mul, Nat.add_comm, ← List.drop_drop,
      List.drop_left' hx, drop_flatten_uv (fun y hy => h y (by simp [hy])) n]
    rfl

theorem flatten_drop_cons {L : List (List Bool)} {c : ℕ} (hc : c < L.length) :
    (L.drop c).flatten = L[c] ++ (L.drop (c + 1)).flatten := by
  rw [List.drop_eq_getElem_cons hc, List.flatten_cons]

/-! ### Small instructions -/

theorem exec_drop' {t c : Fin 128} (h : t ≠ c) (w : St) :
    exec V f (.drop t c) w = Function.update w t ((w t).drop (w c).length) := by
  simp [exec, h]

theorem exec_tl' {t : Fin 128} (w : St) : exec V f (.tl t) w = Function.update w t (w t).tail := rfl

theorem exec_clr' {t : Fin 128} (w : St) : exec V f (.clr t) w = Function.update w t [] := rfl

theorem exec_seq' {p q : Code} (w : St) : exec V f (.seq p q) w = exec V f q (exec V f p w) := rfl

theorem exec_ifb' {t : Fin 128} {p q : Code} (w : St) :
    exec V f (.ifb t p q) w = if hd (w t) = true then exec V f p w else exec V f q w := rfl

/-! ### The column loop -/

/-- One round: move a value from the stream `Z` into `OUT` (through `Y`, reset from the `V`-bit
word `10`), skip `|TS|` bits. -/
def colBodyC (Z Y O TS : Fin 128) : Code := ofList [.cp Y 10, .mvV Y Z, .mvV O Y, .drop Z TS]

/-- `|CR|` rounds. -/
def colLoopC (Z Y O TS CR : Fin 128) : Code := .rep CR (colBodyC Z Y O TS)

/-- The column `c` of a row-major list with `C` columns: its first `r` entries. -/
def colOf (L : List (List Bool)) (C c r : ℕ) : List (List Bool) :=
  (List.range r).map fun i => L.getD (c + i * C) []

theorem colOf_succ (L : List (List Bool)) (C c r : ℕ) :
    colOf L C c (r + 1) = colOf L C c r ++ [L.getD (c + r * C) []] := by
  simp [colOf, List.range_succ]

theorem UV.colOf {L : List (List Bool)} (h : UV V L) {C c r : ℕ}
    (hr : ∀ i < r, c + i * C < L.length) : UV V (colOf L C c r) := by
  intro x hx
  simp only [ValVM.colOf, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [List.getD_eq_getElem _ _ (hr i hi)]
  exact h _ (List.getElem_mem _)

/-- The invariant of the column loop after `r` rounds. -/
structure ColInv (V : ℕ) (Z Y O TS CR : Fin 128) (L : List (List Bool)) (C c : ℕ) (w₀ : St)
    (r : ℕ) (w : St) : Prop where
  z : w Z = (L.drop (c + r * C)).flatten
  o : w O = (w₀ O ++ (colOf L C c r).flatten).drop (r * V)
  hi : ∀ j, j ≠ Z → j ≠ Y → j ≠ O → j ≠ CR → w j = w₀ j

/-- Distinct words of the column loop. -/
structure ColRegs (Z Y O TS CR : Fin 128) : Prop where
  zy : Z ≠ Y
  zo : Z ≠ O
  zt : Z ≠ TS
  zc : Z ≠ CR
  yo : Y ≠ O
  yt : Y ≠ TS
  yc : Y ≠ CR
  ot : O ≠ TS
  oc : O ≠ CR
  tc : TS ≠ CR
  ty : (10 : Fin 128) ≠ Y
  tz : (10 : Fin 128) ≠ Z
  tO : (10 : Fin 128) ≠ O
  tcr : (10 : Fin 128) ≠ CR

theorem colInv_step {Z Y O TS CR : Fin 128} (hr : ColRegs Z Y O TS CR) {L : List (List Bool)}
    (hL : UV V L) {C c : ℕ} (hC : 0 < C) {w₀ : St} (hTS : (w₀ TS).length = (C - 1) * V)
    (h10 : (w₀ 10).length = V) {r : ℕ} (hlt : c + r * C < L.length) {w : St} (h : ColInv V Z Y O TS CR L C c w₀ r w) :
    ColInv V Z Y O TS CR L C c w₀ (r + 1)
      (exec V f (colBodyC Z Y O TS) (Function.update w CR (w CR).tail)) := by
  obtain ⟨zy, zo, zt, zc, yo, yt, yc, ot, oc, tc, ty, tz, tO, tcr⟩ := hr
  have w10 : (w 10).length = V := by rw [h.hi 10 tz ty tO tcr, h10]
  have hx : L[c + r * C].length = V := hL _ (List.getElem_mem _)
  have wTS : (w TS).length = (C - 1) * V := by rw [h.hi TS zt.symm yt.symm ot.symm tc, hTS]
  simp only [colBodyC, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  rw [exec_mvV_pop (L := (L.drop (c + r * C + 1)).flatten) zy.symm
    (by simp [Function.update_apply, tcr, w10]) hx
    (by simp [Function.update_apply, zy, zc, h.z, flatten_drop_cons hlt])]
  rw [exec_mvV_push yo.symm (by simp [Function.update_apply, yo, hx])]
  rw [exec_drop' zt]
  have hl : ((colOf L C c r).flatten).length = r * V := by
    rw [length_flatten_of (hL.colOf (fun i hi => by
      have : i * C ≤ r * C := Nat.mul_le_mul_right _ hi.le
      omega)), colOf]
    simp
  refine ⟨?_, ?_, fun j h1 h2 h3 h4 => ?_⟩
  · simp only [Function.update_apply, zo, yo, zy, ot, yt, zt, tc, if_true, if_false,
      Ne.symm zo, Ne.symm yo, Ne.symm zy, Ne.symm ot, Ne.symm yt, Ne.symm zt, Ne.symm tc, wTS]
    rw [drop_flatten_uv (hL.drop _), List.drop_drop]
    congr 2
    rw [Nat.succ_mul]; omega
  · simp only [Function.update_apply, zo, yo, zy, oc, if_true, if_false, Ne.symm zo,
      Ne.symm yo, Ne.symm zy, Ne.symm oc]
    rw [h.o, colOf_succ, List.flatten_append, List.flatten_singleton,
      List.getD_eq_getElem _ _ hlt,
      drop_append_drop' (by rw [List.length_append, hl]; omega), List.append_assoc, Nat.succ_mul]
  · simp only [Function.update_apply, h1, h2, h3, h4, if_false]
    exact h.hi j h1 h2 h3 h4

/-- **The column loop**: `|CR| = R` rounds move the column `c` of `L` into `O`. -/
theorem exec_colLoop {Z Y O TS CR : Fin 128} (hr : ColRegs Z Y O TS CR) {L : List (List Bool)}
    (hL : UV V L) {C c : ℕ} (hC : 0 < C) (w : St) (hTS : (w TS).length = (C - 1) * V)
    (hZ : w Z = (L.drop c).flatten) (h10 : (w 10).length = V)
    (hlt : ∀ i < (w CR).length, c + i * C < L.length) :
    ColInv V Z Y O TS CR L C c w (w CR).length (exec V f (colLoopC Z Y O TS CR) w) := by
  have := exec_rep_inv (V := V) (f := f) (c := CR) (B := colBodyC Z Y O TS)
    (fun r w' => r ≤ (w CR).length → ColInv V Z Y O TS CR L C c w r w')
    (fun r w' ih hr' => colInv_step hr hL hC hTS h10 (hlt r (by omega)) (ih (by omega))) w
    (fun _ => ⟨by simpa using hZ, by simp [colOf], fun _ _ _ _ _ => rfl⟩)
  exact this le_rfl

/-! ### Shift registers -/

/-- Shifting `Q` into a register holding the last bits of `O ++ P`. -/
theorem shift_acc (O P Q : List Bool) :
    ((O ++ P).drop P.length ++ Q).drop Q.length = (O ++ (P ++ Q)).drop (P ++ Q).length := by
  rw [drop_append_drop' (by simp), List.append_assoc, List.length_append]

theorem colOf_len {L : List (List Bool)} (hL : UV V L) {C c r : ℕ}
    (hr : ∀ i < r, c + i * C < L.length) : (colOf L C c r).flatten.length = r * V := by
  rw [length_flatten_of (hL.colOf hr), colOf]; simp

/-! ### The reversed transposed rows of a block -/

abbrev RASB : Fin 128 := 65
abbrev rX : Fin 128 := 77
abbrev rZ : Fin 128 := 78
abbrev rY : Fin 128 := 79
abbrev CMV : Fin 128 := 80
abbrev CNM : Fin 128 := 81
abbrev CR : Fin 128 := 82
abbrev TN : Fin 128 := 92
abbrev TN1V : Fin 128 := 94

/-- One column of the block on `X` (from the last), shifted into `RASB`. -/
def rrBody : Code :=
  ofList [.cp rZ rX, .drop rZ CMV, .cp CR 12, colLoopC rZ rY RASB TN1V CR, .drop CMV 10]

/-- **The reversed transposed rows**: the `|TN| = N` columns of the block `X` (`|12|` rows), the
last column first, each shifted into `RASB`. -/
def rrC : Code := ofList [.cp CMV TN1V, .cp CNM TN, .rep CNM rrBody]

/-- The values shifted by the first `r` rounds. -/
def rrL (L : List (List Bool)) (N R r : ℕ) : List (List Bool) :=
  (List.range r).flatMap fun m => colOf L N (N - 1 - m) R

theorem rrL_succ (L : List (List Bool)) (N R r : ℕ) :
    rrL L N R (r + 1) = rrL L N R r ++ colOf L N (N - 1 - r) R := by
  simp [rrL, List.range_succ, List.flatMap_append]

theorem colRegs_rr : ColRegs rZ rY RASB TN1V CR := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem wr_rrBody : wr rrBody = [rZ, rZ, CR, CR, rY, rY, rZ, RASB, rY, rZ, CMV] := by decide

/-- The invariant of `rrC` after `r` rounds. -/
structure RRInv (V : ℕ) (L : List (List Bool)) (N R : ℕ) (w₀ : St) (r : ℕ) (w : St) : Prop where
  cmv : (w CMV).length = (N - 1 - r) * V
  ras : w RASB = (w₀ RASB ++ (rrL L N R r).flatten).drop (rrL L N R r).flatten.length
  hi : ∀ j, j ≠ rZ → j ≠ rY → j ≠ RASB → j ≠ CMV → j ≠ CNM → j ≠ CR → w j = w₀ j

theorem rrInv_step {L : List (List Bool)} (hL : UV V L) {N R : ℕ} (hN : 0 < N)
    (hlen : L.length = R * N) {w₀ : St} (hX : w₀ rX = L.flatten) (h10 : (w₀ 10).length = V)
    (h12 : (w₀ 12).length = R) (hTS : (w₀ TN1V).length = (N - 1) * V) {r : ℕ} (hr : r < N)
    {w : St} (h : RRInv V L N R w₀ r w) :
    RRInv V L N R w₀ (r + 1) (exec V f rrBody (Function.update w CNM (w CNM).tail)) := by
  have hw : ∀ j, j ≠ rZ → j ≠ rY → j ≠ RASB → j ≠ CMV → j ≠ CNM → j ≠ CR →
      Function.update w CNM (w CNM).tail j = w₀ j := fun j h1 h2 h3 h4 h5 h6 => by
    rw [Function.update_of_ne h5]; exact h.hi j h1 h2 h3 h4 h5 h6
  have hcmv : (Function.update w CNM (w CNM).tail CMV).length = (N - 1 - r) * V := by
    rw [Function.update_of_ne (by decide)]; exact h.cmv
  have hras : Function.update w CNM (w CNM).tail RASB =
      (w₀ RASB ++ (rrL L N R r).flatten).drop (rrL L N R r).flatten.length := by
    rw [Function.update_of_ne (by decide)]; exact h.ras
  generalize Function.update w CNM (w CNM).tail = w' at hw hcmv hras
  rw [show rrBody = ofList ([.cp rZ rX, .drop rZ CMV, .cp CR 12] ++
    [colLoopC rZ rY RASB TN1V CR, .drop CMV 10]) from rfl, exec_ofList_append]
  have uZ : exec V f (ofList [.cp rZ rX, .drop rZ CMV, .cp CR 12]) w' rZ =
      (L.drop (N - 1 - r)).flatten := by
    simp (config := {decide := true}) only [exec_ofList, List.foldl_cons, List.foldl_nil,
      exec_cp', exec_drop', Function.update_apply, if_true, if_false]
    rw [hcmv, hw rX (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hX,
      drop_flatten_uv hL]
  have uCR : (exec V f (ofList [.cp rZ rX, .drop rZ CMV, .cp CR 12]) w' CR).length = R := by
    simp (config := {decide := true}) only [exec_ofList, List.foldl_cons, List.foldl_nil,
      exec_cp', exec_drop', Function.update_apply, if_true, if_false]
    rw [hw 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h12]
  have uo : ∀ j, j ≠ rZ → j ≠ CR → exec V f (ofList [.cp rZ rX, .drop rZ CMV, .cp CR 12]) w' j =
      w' j := fun j h1 h2 => exec_not_mem _ _ _ (by simp [wr, ofList, h1, h2])
  generalize exec V f (ofList [.cp rZ rX, .drop rZ CMV, .cp CR 12]) w' = u at uZ uCR uo
  have hlt : ∀ i < R, N - 1 - r + i * N < L.length := fun i hi => by
    rw [hlen]
    have : (i + 1) * N ≤ R * N := Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at this; omega
  have u10 : u 10 = w₀ 10 := by
    rw [uo 10 (by decide) (by decide),
      hw 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  have C := exec_colLoop (V := V) (f := f) colRegs_rr hL hN u
    (by rw [uo TN1V (by decide) (by decide),
      hw TN1V (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hTS])
    uZ (by rw [u10, h10]) (by rw [uCR]; exact hlt)
  rw [uCR] at C
  simp only [exec_ofList, List.foldl_cons, List.foldl_nil]
  generalize exec V f (colLoopC rZ rY RASB TN1V CR) u = v at C
  rw [exec_drop' (by decide)]
  have v10 : v 10 = w₀ 10 := by rw [C.hi 10 (by decide) (by decide) (by decide) (by decide), u10]
  refine ⟨?_, ?_, fun j h1 h2 h3 h4 h5 h6 => ?_⟩
  · simp only [Function.update_self, List.length_drop]
    rw [v10, h10, C.hi CMV (by decide) (by decide) (by decide) (by decide),
      uo CMV (by decide) (by decide), hcmv]
    rw [show N - 1 - (r + 1) = (N - 1 - r) - 1 by omega, Nat.sub_one_mul]
  · rw [Function.update_of_ne (by decide), C.o, uo RASB (by decide) (by decide), hras,
      ← colOf_len (V := V) hL (C := N) (c := N - 1 - r) hlt, shift_acc, rrL_succ, List.flatten_append]
  · rw [Function.update_of_ne h4, C.hi j h1 h2 h3 h6, uo j h1 h6]
    exact hw j h1 h2 h3 h4 h5 h6

/-- **The reversed transposed rows of a block** (`R` rows of `N` values on `X`). -/
theorem exec_rrC {L : List (List Bool)} (hL : UV V L) {N R : ℕ} (hN : 0 < N)
    (hlen : L.length = R * N) (w : St) (hX : w rX = L.flatten) (h10 : (w 10).length = V)
    (h12 : (w 12).length = R) (hTS : (w TN1V).length = (N - 1) * V) (hTN : (w TN).length = N) :
    exec V f rrC w RASB = (w RASB ++ (rrL L N R N).flatten).drop (rrL L N R N).flatten.length ∧
      ∀ j, j ≠ rZ → j ≠ rY → j ≠ RASB → j ≠ CMV → j ≠ CNM → j ≠ CR → exec V f rrC w j = w j := by
  simp only [rrC, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  set w1 := Function.update (Function.update w CMV (w TN1V)) CNM
    (Function.update w CMV (w TN1V) TN) with hw1
  have e1 : ∀ j, j ≠ CMV → j ≠ CNM → w1 j = w j := fun j h1 h2 => by
    simp [hw1, Function.update_of_ne h1, Function.update_of_ne h2]
  have I := exec_rep_inv (V := V) (f := f) (c := CNM) (B := rrBody)
    (fun r w' => r ≤ N → RRInv V L N R w1 r w')
    (fun r w' ih hr => rrInv_step hL hN hlen
      (by rw [e1 rX (by decide) (by decide), hX]) (by rw [e1 10 (by decide) (by decide), h10])
      (by rw [e1 12 (by decide) (by decide), h12])
      (by rw [e1 TN1V (by decide) (by decide), hTS]) (by omega) (ih (by omega))) w1
    (fun _ => ⟨by simp (config := {decide := true}) [hw1, Function.update_apply, hTS],
      by simp [rrL], fun _ _ _ _ _ _ _ => rfl⟩)
  have hn : (w1 CNM).length = N := by
    simp (config := {decide := true}) [hw1, Function.update_apply, hTN]
  rw [hn] at I
  obtain ⟨-, hras, hhi⟩ := I le_rfl
  refine ⟨by rw [hras, e1 RASB (by decide) (by decide)], fun j h1 h2 h3 h4 h5 h6 => ?_⟩
  rw [hhi j h1 h2 h3 h4 h5 h6, e1 j h4 h5]

/-! ### The transpose of the outputs -/

abbrev RES : Fin 128 := 63
abbrev OUTB : Fin 128 := 76
abbrev ZM : Fin 128 := 83
abbrev CI : Fin 128 := 84
abbrev TKV : Fin 128 := 95

/-- One column of the block on `ZM` (its first `i` values dropped), shifted into `RES`. -/
def trBody : Code := ofList [.cp rZ ZM, .cp CR TN, colLoopC rZ rY RES TKV CR, .drop ZM 10]

/-- **The transpose**: the `|12| = C` columns of the block `OUTB` (`|TN|` rows), each shifted into
`RES`. -/
def trC : Code := ofList [.cp ZM OUTB, .cp CI 12, .rep CI trBody]

/-- The values shifted by the first `r` rounds. -/
def trL (L : List (List Bool)) (C R r : ℕ) : List (List Bool) :=
  (List.range r).flatMap fun i => colOf L C i R

theorem trL_succ (L : List (List Bool)) (C R r : ℕ) :
    trL L C R (r + 1) = trL L C R r ++ colOf L C r R := by
  simp [trL, List.range_succ, List.flatMap_append]

theorem colRegs_tr : ColRegs rZ rY RES TKV CR := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The invariant of `trC` after `r` rounds. -/
structure TRInv (V : ℕ) (L : List (List Bool)) (C R : ℕ) (w₀ : St) (r : ℕ) (w : St) : Prop where
  zm : w ZM = (L.drop r).flatten
  res : w RES = (w₀ RES ++ (trL L C R r).flatten).drop (trL L C R r).flatten.length
  hi : ∀ j, j ≠ rZ → j ≠ rY → j ≠ RES → j ≠ ZM → j ≠ CI → j ≠ CR → w j = w₀ j

theorem trInv_step {L : List (List Bool)} (hL : UV V L) {C R : ℕ} (hC : 0 < C)
    (hlen : L.length = R * C) {w₀ : St} (h10 : (w₀ 10).length = V)
    (hTN : (w₀ TN).length = R) (hTS : (w₀ TKV).length = (C - 1) * V) {r : ℕ} (hr : r < C)
    {w : St} (h : TRInv V L C R w₀ r w) :
    TRInv V L C R w₀ (r + 1) (exec V f trBody (Function.update w CI (w CI).tail)) := by
  have hw : ∀ j, j ≠ rZ → j ≠ rY → j ≠ RES → j ≠ ZM → j ≠ CI → j ≠ CR →
      Function.update w CI (w CI).tail j = w₀ j := fun j h1 h2 h3 h4 h5 h6 => by
    rw [Function.update_of_ne h5]; exact h.hi j h1 h2 h3 h4 h5 h6
  have hzm : Function.update w CI (w CI).tail ZM = (L.drop r).flatten := by
    rw [Function.update_of_ne (by decide)]; exact h.zm
  have hres : Function.update w CI (w CI).tail RES =
      (w₀ RES ++ (trL L C R r).flatten).drop (trL L C R r).flatten.length := by
    rw [Function.update_of_ne (by decide)]; exact h.res
  generalize Function.update w CI (w CI).tail = w' at hw hzm hres
  rw [show trBody = ofList ([.cp rZ ZM, .cp CR TN] ++ [colLoopC rZ rY RES TKV CR, .drop ZM 10])
    from rfl, exec_ofList_append]
  have uZ : exec V f (ofList [.cp rZ ZM, .cp CR TN]) w' rZ = (L.drop r).flatten := by
    simp (config := {decide := true}) only [exec_ofList, List.foldl_cons, List.foldl_nil,
      exec_cp', Function.update_apply, if_true, if_false]
    exact hzm
  have uCR : (exec V f (ofList [.cp rZ ZM, .cp CR TN]) w' CR).length = R := by
    simp (config := {decide := true}) only [exec_ofList, List.foldl_cons, List.foldl_nil,
      exec_cp', Function.update_apply, if_true, if_false]
    rw [hw TN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hTN]
  have uo : ∀ j, j ≠ rZ → j ≠ CR → exec V f (ofList [.cp rZ ZM, .cp CR TN]) w' j = w' j :=
    fun j h1 h2 => exec_not_mem _ _ _ (by simp [wr, ofList, h1, h2])
  generalize exec V f (ofList [.cp rZ ZM, .cp CR TN]) w' = u at uZ uCR uo
  have hlt : ∀ i < R, r + i * C < L.length := fun i hi => by
    rw [hlen]
    have : (i + 1) * C ≤ R * C := Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at this; omega
  have u10 : u 10 = w₀ 10 := by
    rw [uo 10 (by decide) (by decide),
      hw 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  have Cl := exec_colLoop (V := V) (f := f) colRegs_tr hL hC u
    (by rw [uo TKV (by decide) (by decide),
      hw TKV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hTS])
    uZ (by rw [u10, h10]) (by rw [uCR]; exact hlt)
  rw [uCR] at Cl
  simp only [exec_ofList, List.foldl_cons, List.foldl_nil]
  generalize exec V f (colLoopC rZ rY RES TKV CR) u = v at Cl
  rw [exec_drop' (by decide)]
  have v10 : v 10 = w₀ 10 := by rw [Cl.hi 10 (by decide) (by decide) (by decide) (by decide), u10]
  refine ⟨?_, ?_, fun j h1 h2 h3 h4 h5 h6 => ?_⟩
  · simp only [Function.update_self]
    rw [v10, Cl.hi ZM (by decide) (by decide) (by decide) (by decide),
      uo ZM (by decide) (by decide), hzm, ← Nat.one_mul (w₀ 10).length, h10,
      drop_flatten_uv (hL.drop _), List.drop_drop]
  · rw [Function.update_of_ne (by decide), Cl.o, uo RES (by decide) (by decide), hres,
      ← colOf_len (V := V) hL (C := C) (c := r) hlt, shift_acc, trL_succ, List.flatten_append]
  · rw [Function.update_of_ne h4, Cl.hi j h1 h2 h3 h6, uo j h1 h6]
    exact hw j h1 h2 h3 h4 h5 h6

/-- **The transpose of a block** (`R` rows of `C` values on `OUTB`), into `RES`. -/
theorem exec_trC {L : List (List Bool)} (hL : UV V L) {C R : ℕ} (hC : 0 < C)
    (hlen : L.length = R * C) (w : St) (hO : w OUTB = L.flatten) (h10 : (w 10).length = V)
    (h12 : (w 12).length = C) (hTS : (w TKV).length = (C - 1) * V) (hTN : (w TN).length = R) :
    exec V f trC w RES = (w RES ++ (trL L C R C).flatten).drop (trL L C R C).flatten.length ∧
      ∀ j, j ≠ rZ → j ≠ rY → j ≠ RES → j ≠ ZM → j ≠ CI → j ≠ CR → exec V f trC w j = w j := by
  simp only [trC, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  set w1 := Function.update (Function.update w ZM (w OUTB)) CI
    (Function.update w ZM (w OUTB) 12) with hw1
  have e1 : ∀ j, j ≠ ZM → j ≠ CI → w1 j = w j := fun j h1 h2 => by
    simp [hw1, Function.update_of_ne h1, Function.update_of_ne h2]
  have I := exec_rep_inv (V := V) (f := f) (c := CI) (B := trBody)
    (fun r w' => r ≤ C → TRInv V L C R w1 r w')
    (fun r w' ih hr => trInv_step hL hC hlen
      (by rw [e1 10 (by decide) (by decide), h10]) (by rw [e1 TN (by decide) (by decide), hTN])
      (by rw [e1 TKV (by decide) (by decide), hTS]) (by omega) (ih (by omega))) w1
    (fun _ => ⟨by simp (config := {decide := true}) [hw1, Function.update_apply, hO],
      by simp [trL], fun _ _ _ _ _ _ _ => rfl⟩)
  have hn : (w1 CI).length = C := by
    simp (config := {decide := true}) [hw1, Function.update_apply, h12]
  rw [hn] at I
  obtain ⟨-, hres, hhi⟩ := I le_rfl
  refine ⟨by rw [hres, e1 RES (by decide) (by decide)], fun j h1 h2 h3 h4 h5 h6 => ?_⟩
  rw [hhi j h1 h2 h3 h4 h5 h6, e1 j h4 h5]

end ValVM

end SigabaNeo.Tape
