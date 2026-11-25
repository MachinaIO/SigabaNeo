import PE.Impl.ExpLUT.Prog.RedKeyPktMath

/-!
# The packet stream, part 3: rows of bits read column-wise (generic `N K`)

The programming bits `zr` sit in the raw secret row by row (`zrEnc`: for every programming column
`i`, the `m̄` bits `zr i w`). The slab `inl w₀` needs the **column** `w₀`. A *cursor* is the word of
the rows from the bit `w₀` on (`PtCur`): its head is the bit `w₀` of the first row, and dropping the
row width `m` (template `ptTm`) moves to the next row.

* `ptBitRowC q out`: for `|ptTC|` rows, append `ptOne` or `ptZero` by the head bit of the cursor
  `q`, then advance (**`exec_ptBitRowC`**): `out ++= ptEmit (ptCol w₀ rows)`;
* `ptDigRowsC q`: `|ptTD|` times a row of `|ptTC|` bits into `ptX`, appended twice to `rAinS`
  (**`exec_ptDigRowsC`**, the shape of `ptDig`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyPkt

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo.NegaG
open SigabaNeo.Lattices.Algo (encRM)
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

/-! ### Registers of the slab codes -/

/-- Cursor on the rows of `R^aut`. -/
@[simp, vmreg] abbrev ptCurA : Fin 64 := 32
/-- Cursor on the rows of `R₀`. -/
@[simp, vmreg] abbrev ptCurR0 : Fin 64 := 33
/-- Cursor on the rows of `Z`. -/
@[simp, vmreg] abbrev ptCurZ : Fin 64 := 34
/-- Cursor on the rows of `R^in`. -/
@[simp, vmreg] abbrev ptCurRin : Fin 64 := 35
/-- A row under construction. -/
@[simp, vmreg] abbrev ptX : Fin 64 := 36
/-- The word of `1`. -/
@[simp, vmreg] abbrev ptOne : Fin 64 := 37
/-- The word of `0`. -/
@[simp, vmreg] abbrev ptZero : Fin 64 := 39
/-- Unary row width `m̄`. -/
@[simp, vmreg] abbrev ptTm : Fin 64 := 40
/-- The digit counter. -/
@[simp, vmreg] abbrev ptCD : Fin 64 := 41
/-- Unary `|DigI K|`. -/
@[simp, vmreg] abbrev ptTD : Fin 64 := 42
/-- The column counter. -/
@[simp, vmreg] abbrev ptCC : Fin 64 := 43
/-- Unary `2K`. -/
@[simp, vmreg] abbrev ptTC : Fin 64 := 44
/-- The zero row. -/
@[simp, vmreg] abbrev ptZ2 : Fin 64 := 45
/-- `2^b − 1` zero rows. -/
@[simp, vmreg] abbrev ptZL : Fin 64 := 46

/-! ### Cursors and emitted words -/

/-- The bits `w₀` of the rows. -/
def ptCol (w0 : ℕ) (rows : List (List Bool)) : List Bool := rows.map fun r => r.getD w0 false

/-- The word emitted for bits: `O` for `true`, `Z` for `false`. -/
def ptEmit (O Z : List Bool) (bs : List Bool) : List Bool := (bs.map fun b => if b then O else Z).flatten

theorem ptEmit_append (O Z : List Bool) (a b : List Bool) :
    ptEmit O Z (a ++ b) = ptEmit O Z a ++ ptEmit O Z b := by
  simp [ptEmit]

theorem ptCol_append (w0 : ℕ) (a b : List (List Bool)) :
    ptCol w0 (a ++ b) = ptCol w0 a ++ ptCol w0 b := by
  simp [ptCol]

/-- **A cursor**: the rows (all of width `m`) from the bit `w₀` on, followed by anything. -/
def PtCur (m w0 : ℕ) (rows : List (List Bool)) (x : List Bool) : Prop :=
  (∀ r ∈ rows, r.length = m) ∧ ∃ T, x = (rows.flatten ++ T).drop w0

theorem PtCur.drop_rows {m w0 : ℕ} {rows : List (List Bool)} {x : List Bool}
    (h : PtCur m w0 rows x) (n : ℕ) : PtCur m w0 (rows.drop n) (x.drop (m * min n rows.length)) := by
  obtain ⟨hr, T, rfl⟩ := h
  refine ⟨fun r hr' => hr r (List.mem_of_mem_drop hr'), T, ?_⟩
  rw [List.drop_drop]
  have hl : ((rows.take n).flatten).length = m * min n rows.length := by
    rw [List.length_flatten]
    have : ∀ l : List (List Bool), (∀ r ∈ l, r.length = m) → (l.map List.length).sum = m * l.length := by
      intro l hl
      induction l with
      | nil => simp
      | cons a l ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rw [hl a (by simp), ih (fun r h => hl r (by simp [h]))]; ring
    rw [this _ (fun r h' => hr r (List.mem_of_mem_take h')), List.length_take]
  have e : rows.flatten ++ T = (rows.take n).flatten ++ ((rows.drop n).flatten ++ T) := by
    rw [← List.append_assoc, ← List.flatten_append, List.take_append_drop]
  rw [e, show w0 + m * min n rows.length = (rows.take n).flatten.length + w0 by rw [hl]; ring,
    ← List.drop_drop, List.drop_left]

/-! ### One row of bits -/

/-- The round: append `ptOne`/`ptZero` by the head of the cursor `q`, advance by a row. -/
def ptBitBody (q out : Fin 64) : Code :=
  .seq (.ifb q (.app out ptOne) (.app out ptZero)) (.drop q ptTm)

/-- **`|ptTC|` bits of the column `w₀`** onto `out`. -/
def ptBitRowC (q out : Fin 64) : Code := .seq (.cp ptCC ptTC) (.rep ptCC (ptBitBody q out))

theorem ptBitBody_writes (q out r : Fin 64) (h1 : r ≠ q) (h2 : r ≠ out) :
    (ptBitBody q out).writes r = false := by
  simp [ptBitBody, Code.writes, Ne.symm h1, Ne.symm h2]

theorem ptBitRowC_writes (q out r : Fin 64) (h1 : r ≠ q) (h2 : r ≠ out) (h3 : r ≠ ptCC) :
    (ptBitRowC q out).writes r = false := by
  simp [ptBitRowC, ptBitBody, Code.writes, Ne.symm h1, Ne.symm h2, Ne.symm h3]

theorem head_cursor {m w0 : ℕ} (hw0 : w0 < m) (r : List Bool) (hr : r.length = m) (X : List Bool) :
    hd ((r ++ X).drop w0) = r.getD w0 false := by
  rw [List.drop_append_of_le_length (by omega)]
  obtain ⟨y, ys, hy⟩ : ∃ y ys, r.drop w0 = y :: ys := by
    cases h : r.drop w0 with
    | nil => rw [List.drop_eq_nil_iff] at h; omega
    | cons y ys => exact ⟨y, ys, rfl⟩
  rw [hy]
  have h1 : r[w0]? = some y := by rw [← List.head?_drop, hy]; rfl
  rw [List.getD_eq_getElem?_getD, h1]; rfl

theorem drop_cursor {m w0 : ℕ} (r : List Bool) (hr : r.length = m) (X : List Bool) :
    ((r ++ X).drop w0).drop m = X.drop w0 := by
  rw [List.drop_drop, show w0 + m = r.length + w0 by omega, ← List.drop_drop, List.drop_left]

theorem exec_ptBitRowC {N K : ℕ} (q out : Fin 64)
    (hq : q ≠ ptCC ∧ q ≠ ptTC ∧ q ≠ ptTm ∧ q ≠ ptOne ∧ q ≠ ptZero ∧ q ≠ out)
    (ho : out ≠ ptCC ∧ out ≠ ptTC ∧ out ≠ ptTm ∧ out ≠ ptOne ∧ out ≠ ptZero)
    (w : St) {m w0 : ℕ} (hm : (w ptTm).length = m) (hw0 : w0 < m) (rows rest : List (List Bool))
    (hrows : ∀ r ∈ rows, r.length = m) (hlen : rows.length = (w ptTC).length) (T : List Bool)
    (hqv : w q = ((rows ++ rest).flatten ++ T).drop w0) :
    exec N K (ptBitRowC q out) w out = w out ++ ptEmit (w ptOne) (w ptZero) (ptCol w0 rows) ∧
      exec N K (ptBitRowC q out) w q = (rest.flatten ++ T).drop w0 ∧
      ∀ r, r ≠ q → r ≠ out → r ≠ ptCC → exec N K (ptBitRowC q out) w r = w r := by
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6⟩ := hq
  obtain ⟨ho1, ho2, ho3, ho4, ho5⟩ := ho
  set w1 := exec N K (.cp ptCC ptTC) w with hw1
  have hc : (w1 ptCC).length = rows.length := by simp [hw1, hlen]
  let P : ℕ → St → Prop := fun j v =>
    v out = w out ++ ptEmit (w ptOne) (w ptZero) (ptCol w0 (rows.take j)) ∧
    v q = (((rows.drop j) ++ rest).flatten ++ T).drop w0 ∧
    ∀ r, r ≠ q → r ≠ out → r ≠ ptCC → v r = w r
  have key := exec_rep_inv (N := N) (K := K) ptCC (ptBitBody q out)
    (ptBitBody_writes q out ptCC (Ne.symm hq1) (Ne.symm ho1)) P w1
    ⟨by simp [hw1, Function.update_apply, ho1, ptCol, ptEmit],
     by simp [hw1, Function.update_apply, hq1, hqv],
     fun r h1 h2 h3 => by simp [hw1, Function.update_apply, h3]⟩
    (by
      intro j v hj hP _
      rw [hc] at hj
      obtain ⟨h1, h2, h3⟩ := hP
      set vv := Function.update v ptCC (v ptCC).tail
      have e1 : vv out = v out := by simp [vv, Function.update_apply, ho1]
      have e2 : vv q = v q := by simp [vv, Function.update_apply, hq1]
      have eO : vv ptOne = w ptOne := by
        simp only [vv, Function.update_apply, show ptOne ≠ ptCC by decide, if_false]
        exact h3 _ (Ne.symm hq4) (Ne.symm ho4) (by decide)
      have eZ : vv ptZero = w ptZero := by
        simp only [vv, Function.update_apply, show ptZero ≠ ptCC by decide, if_false]
        exact h3 _ (Ne.symm hq5) (Ne.symm ho5) (by decide)
      have eT : vv ptTm = w ptTm := by
        simp only [vv, Function.update_apply, show ptTm ≠ ptCC by decide, if_false]
        exact h3 _ (Ne.symm hq3) (Ne.symm ho3) (by decide)
      have hrj : rows.drop j = rows[j] :: rows.drop (j + 1) := List.drop_eq_getElem_cons hj
      have hlj : rows[j].length = m := hrows _ (List.getElem_mem hj)
      have hqj : vv q = (rows[j] ++ ((rows.drop (j + 1) ++ rest).flatten ++ T)).drop w0 := by
        rw [e2, h2, hrj, List.cons_append, List.flatten_cons, List.append_assoc]
      have hhd : hd (vv q) = rows[j].getD w0 false := by rw [hqj]; exact head_cursor hw0 _ hlj _
      have hsplit : ptCol w0 (rows.take (j + 1)) = ptCol w0 (rows.take j) ++ [rows[j].getD w0 false] := by
        unfold ptCol
        rw [List.take_succ, List.getElem?_eq_getElem hj, Option.toList_some, List.map_append]; rfl
      show P (j + 1) (exec N K (.drop q ptTm) (exec N K (.ifb q (.app out ptOne) (.app out ptZero)) vv))
      simp only [exec_ifb, hhd]
      refine ⟨?_, ?_, ?_⟩
      · split_ifs with hb
        · rw [exec_drop, if_neg hq3, Function.update_of_ne (Ne.symm hq6), exec_app,
            Function.update_self, e1, eO, h1, hsplit, ptEmit_append]
          simp only [ptEmit, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hb,
            if_true, List.append_nil, List.append_assoc]
        · rw [exec_drop, if_neg hq3, Function.update_of_ne (Ne.symm hq6), exec_app,
            Function.update_self, e1, eZ, h1, hsplit, ptEmit_append]
          simp only [ptEmit, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hb,
            Bool.false_eq_true, if_false, List.append_nil, List.append_assoc]
      · split_ifs with hb
        · simp only [exec_app, exec_drop, if_neg hq3, Function.update_self,
            Function.update_of_ne hq6]
          rw [show (Function.update vv out (vv out ++ vv ptOne)) ptTm = w ptTm by
            rw [Function.update_of_ne (Ne.symm ho3), eT], hm, hqj]
          exact drop_cursor _ hlj _
        · simp only [exec_app, exec_drop, if_neg hq3, Function.update_self,
            Function.update_of_ne hq6]
          rw [show (Function.update vv out (vv out ++ vv ptZero)) ptTm = w ptTm by
            rw [Function.update_of_ne (Ne.symm ho3), eT], hm, hqj]
          exact drop_cursor _ hlj _
      · intro r r1 r2 r3
        split_ifs <;>
        · simp only [exec_app, exec_drop, if_neg hq3, Function.update_of_ne r1,
            Function.update_of_ne r2, vv, Function.update_of_ne r3]
          exact h3 r r1 r2 r3)
  rw [hc] at key
  obtain ⟨k1, k2, k3⟩ := key
  have hE : exec N K (ptBitRowC q out) w = exec N K (.rep ptCC (ptBitBody q out)) w1 := rfl
  rw [hE]
  exact ⟨by rw [k1, List.take_length], by rw [k2, List.drop_length, List.nil_append], k3⟩

/-! ### Rows over the digits, each twice -/

/-- The word of `nD` rows of `nC` bits of the column `w₀`, each row twice. -/
def ptDigW (O Z : List Bool) (w0 nC nD : ℕ) (rows : List (List Bool)) : List Bool :=
  (List.range nD).flatMap fun d =>
    ptEmit O Z (ptCol w0 ((rows.drop (d * nC)).take nC)) ++
      ptEmit O Z (ptCol w0 ((rows.drop (d * nC)).take nC))

/-- The round of the digit loop. -/
def ptDigBody (q : Fin 64) : Code :=
  .seq (.clr ptX) <| .seq (ptBitRowC q ptX) <| .seq (.app rAinS ptX) (.app rAinS ptX)

/-- **`|ptTD|` rows, each twice**, onto `rAinS`. -/
def ptDigRowsC (q : Fin 64) : Code := .seq (.cp ptCD ptTD) (.rep ptCD (ptDigBody q))

theorem ptDigBody_writes (q r : Fin 64) (h1 : r ≠ q) (h2 : r ≠ ptX) (h3 : r ≠ ptCC)
    (h4 : r ≠ rAinS) : (ptDigBody q).writes r = false := by
  simp [ptDigBody, ptBitRowC, ptBitBody, Code.writes, Ne.symm h1, Ne.symm h2, Ne.symm h3,
    Ne.symm h4]

theorem ptDigRowsC_writes (q r : Fin 64) (h1 : r ≠ q) (h2 : r ≠ ptX) (h3 : r ≠ ptCC)
    (h4 : r ≠ rAinS) (h5 : r ≠ ptCD) : (ptDigRowsC q).writes r = false := by
  simp [ptDigRowsC, ptDigBody, ptBitRowC, ptBitBody, Code.writes, Ne.symm h1, Ne.symm h2,
    Ne.symm h3, Ne.symm h4, Ne.symm h5]

/-- The registers a digit loop may not have as its cursor. -/
def ptDigQ (q : Fin 64) : Prop :=
  q ≠ ptCC ∧ q ≠ ptTC ∧ q ≠ ptTm ∧ q ≠ ptOne ∧ q ≠ ptZero ∧ q ≠ ptX ∧ q ≠ rAinS ∧ q ≠ ptCD ∧
    q ≠ ptTD

theorem exec_ptDigRowsC {N K : ℕ} (q : Fin 64) (hq : ptDigQ q) (w : St) {m w0 nC nD : ℕ}
    (hm : (w ptTm).length = m) (hw0 : w0 < m) (hC : (w ptTC).length = nC)
    (hD : (w ptTD).length = nD) (rows rest : List (List Bool))
    (hrows : ∀ r ∈ rows, r.length = m) (hlen : rows.length = nD * nC) (T : List Bool)
    (hqv : w q = ((rows ++ rest).flatten ++ T).drop w0) :
    exec N K (ptDigRowsC q) w rAinS = w rAinS ++ ptDigW (w ptOne) (w ptZero) w0 nC nD rows ∧
      exec N K (ptDigRowsC q) w q = (rest.flatten ++ T).drop w0 ∧
      ∀ r, r ≠ q → r ≠ ptX → r ≠ ptCC → r ≠ rAinS → r ≠ ptCD →
        exec N K (ptDigRowsC q) w r = w r := by
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9⟩ := hq
  set w1 := exec N K (.cp ptCD ptTD) w with hw1
  have hc : (w1 ptCD).length = nD := by simp [hw1, hD]
  let P : ℕ → St → Prop := fun d v =>
    v rAinS = w rAinS ++ ptDigW (w ptOne) (w ptZero) w0 nC d rows ∧
    v q = (((rows.drop (d * nC)) ++ rest).flatten ++ T).drop w0 ∧
    ∀ r, r ≠ q → r ≠ ptX → r ≠ ptCC → r ≠ rAinS → r ≠ ptCD → v r = w r
  have key := exec_rep_inv (N := N) (K := K) ptCD (ptDigBody q)
    (ptDigBody_writes q ptCD (Ne.symm hq8) (by decide) (by decide) (by decide)) P w1
    ⟨by simp [hw1, Function.update_apply, ptDigW],
     by rw [hw1, exec_cp, Function.update_of_ne hq8, hqv]; simp,
     fun r h1 h2 h3 h4 h5 => by simp [hw1, Function.update_apply, h5]⟩
    (by
      intro d v hd hP _
      rw [hc] at hd
      obtain ⟨h1, h2, h3⟩ := hP
      set vv := Function.update v ptCD (v ptCD).tail
      have fr : ∀ r, r ≠ q → r ≠ ptX → r ≠ ptCC → r ≠ rAinS → r ≠ ptCD → vv r = w r := by
        intro r a1 a2 a3 a4 a5
        simp only [vv, Function.update_apply, if_neg a5]; exact h3 r a1 a2 a3 a4 a5
      set v1 := exec N K (.clr ptX) vv with hv1
      have v1T : (v1 ptTm).length = m := by
        rw [hv1, exec_clr, Function.update_of_ne (by decide), fr _ (Ne.symm hq3) (by decide)
          (by decide) (by decide) (by decide), hm]
      have v1C : ((rows.drop (d * nC)).take nC).length = (v1 ptTC).length := by
        rw [hv1, exec_clr, Function.update_of_ne (by decide), fr _ (Ne.symm hq2) (by decide)
          (by decide) (by decide) (by decide), hC, List.length_take, List.length_drop, hlen]
        have : d * nC + nC ≤ nD * nC := by nlinarith
        omega
      have v1q : v1 q = ((((rows.drop (d * nC)).take nC) ++ (rows.drop ((d + 1) * nC) ++ rest)).flatten
          ++ T).drop w0 := by
        have e : rows.drop (d * nC) ++ rest =
            (rows.drop (d * nC)).take nC ++ (rows.drop ((d + 1) * nC) ++ rest) := by
          rw [show (d + 1) * nC = d * nC + nC by ring, ← List.drop_drop, ← List.append_assoc,
            List.take_append_drop]
        rw [hv1, exec_clr, Function.update_of_ne hq6, show vv q = v q by
          simp [vv, Function.update_apply, hq8], h2, e]
      obtain ⟨b1, b2, b3⟩ := exec_ptBitRowC (N := N) (K := K) q ptX
        ⟨hq1, hq2, hq3, hq4, hq5, hq6⟩ (by decide) v1 v1T hw0 _ _
        (fun r hr => hrows r (List.mem_of_mem_drop (List.mem_of_mem_take hr))) v1C T v1q
      set v2 := exec N K (ptBitRowC q ptX) v1 with hv2
      have v2X : v2 ptX = ptEmit (w ptOne) (w ptZero) (ptCol w0 ((rows.drop (d * nC)).take nC)) := by
        rw [b1, hv1]
        simp only [exec_clr, Function.update_self, List.nil_append]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          fr _ (Ne.symm hq4) (by decide) (by decide) (by decide) (by decide),
          fr _ (Ne.symm hq5) (by decide) (by decide) (by decide) (by decide)]
      have v20 : v2 rAinS = v rAinS := by
        rw [b3 _ (Ne.symm hq7) (by decide) (by decide), hv1, exec_clr,
          Function.update_of_ne (by decide)]
        simp [vv, Function.update_apply]
      show P (d + 1) (exec N K (.app rAinS ptX) (exec N K (.app rAinS ptX) v2))
      refine ⟨?_, ?_, ?_⟩
      · simp only [exec_app, Function.update_self, Function.update_of_ne (show ptX ≠ rAinS by decide),
          v2X, v20, h1, ptDigW, List.range_succ, List.flatMap_append, List.append_assoc]
        simp
      · simp only [exec_app, Function.update_of_ne hq7, b2]
      · intro r a1 a2 a3 a4 a5
        simp only [exec_app, Function.update_of_ne a4]
        rw [b3 r a1 a2 a3, hv1, exec_clr, Function.update_of_ne a2]
        exact fr r a1 a2 a3 a4 a5)
  rw [hc] at key
  obtain ⟨k1, k2, k3⟩ := key
  have hE : exec N K (ptDigRowsC q) w = exec N K (.rep ptCD (ptDigBody q)) w1 := rfl
  rw [hE]
  refine ⟨k1, ?_, k3⟩
  rw [k2, show rows.drop (nD * nC) = [] from List.drop_of_length_le (by rw [hlen]),
    List.nil_append]

end AdvancedEncryption.ExpLUT.Prog.RedKeyPkt
