import PE.Impl.ExpLUT.Prog.KeyTryVM
import PE.Impl.ExpLUT.Prog.KeyPublicRow

/-!
# `KGsim` on the VM (package G2, item 5): the correction `p − X u`

The last step of the simulated trapdoor correction (`RedKeyPLAN.md`, module 2): with the rows of
`X` in register `16` (row-major), the candidate `p` in register `9` and `u` in register `20`,

  `18 := [p_q − Σ_c X_{q,c} u_c]_q`,

one row at a time with F3's inner-product kernel `ipC` (registers `rQa … rQy`, `rIa`). The row
count is the unary template in register `22` (consumed), the row length the template in `21`.

* `mvSubC`, **`exec_mvSubC`** (any queues of canonical words), `wf_mvSubC`, `mvSubC_frame`;
* `rowsWord`, **`exec_mvSubC_enum`**: for enumerated index types, `18 := [p q − Σ_c X q c · u c]_q`.
-/

set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)

/-- The vector `u`. -/
@[simp, vmreg] abbrev rVu : Fin 64 := 20
/-- The unary template of the row length. -/
@[simp, vmreg] abbrev rVm : Fin 64 := 21
/-- The unary row counter. -/
@[simp, vmreg] abbrev rVn : Fin 64 := 22

variable {N K : ℕ}

/-- Before the inner product: `rIa := 0`, `rQb := u`, `rQc := |u|`. -/
def mvPre : Code := .seq (.cp rIa rZ) <| .seq (.cp rQb rVu) (.cp rQc rVm)

/-- After it: `18 := 18 ++ [p − rIa]`, consuming `p` from register `9`. -/
def mvPost : Code :=
  .seq (.cp rQx rZ) <| .seq (.mvR rQx 9) <| .seq (.op .sub rQy rQx rIa) (.app 18 rQy)

/-- One row. -/
def mvRowBody : Code := .seq mvPre (.seq ipC mvPost)

/-- **`18 := [p_q − Σ_c X_{q,c} u_c]_q`**. -/
def mvSubC : Code := .seq (.clr 18) <| .seq (.cp rQa 16) (.rep rVn mvRowBody)

theorem mvRowBody_writes_rVn : mvRowBody.writes rVn = false := by decide

theorem wf_mvSubC : mvSubC.WFc :=
  ⟨trivial, trivial, mvRowBody_writes_rVn, ⟨trivial, trivial, trivial⟩,
    ⟨ipBody_writes_rQc, trivial, trivial, trivial, trivial, trivial, trivial⟩, trivial, trivial,
    trivial, trivial⟩

/-- **The registers `mvSubC` writes.** -/
theorem mvSubC_frame : ∀ r : Fin 64, mvSubC.writes r = true →
    r ∈ [9, 18, rVn, rQa, rQb, rQc, rIa, rQx, rQy] := by decide

/-- The output of `mvSubC`: `p_q − Σ_c X_{q,c} u_c` for every row. -/
def mvSubOut (ps : List (Rq N K)) (rows : List (List (Rq N K))) (u : List (Rq N K)) :
    List (Rq N K) :=
  List.zipWith (fun p r => p - (List.zipWith (· * ·) r u).sum) ps rows

theorem mvSubOut_take_succ (ps : List (Rq N K)) (rows : List (List (Rq N K))) (u : List (Rq N K))
    {k : ℕ} (h1 : k < ps.length) (h2 : k < rows.length) :
    mvSubOut (ps.take (k + 1)) (rows.take (k + 1)) u =
      mvSubOut (ps.take k) (rows.take k) u ++ [ps[k] - (List.zipWith (· * ·) rows[k] u).sum] :=
  zipWith_take_succ' _ ps rows h1 h2
where
  zipWith_take_succ' {α β γ : Type} (f : α → β → γ) (l1 : List α) (l2 : List β) {m : ℕ}
      (h1 : m < l1.length) (h2 : m < l2.length) :
      List.zipWith f (l1.take (m + 1)) (l2.take (m + 1)) =
        List.zipWith f (l1.take m) (l2.take m) ++ [f l1[m] l2[m]] := by
    rw [take_succ_getElem l1 h1, take_succ_getElem l2 h2, List.zipWith_append (by simp; omega)]
    rfl

/-- **The correction `p − X u`**: for `n` rows of length `m` (row-major in `16`), `p` in `9`,
`u` in `20`, the templates `|21| = m`, `|22| = n` and `rZ = 0`, register `18` ends with
`p_q − Σ_c X_{q,c} u_c` for every row `q`. -/
theorem exec_mvSubC (hK : 0 < K) (w : St) (ps : List (Rq N K)) (rows : List (List (Rq N K)))
    (u : List (Rq N K)) (n m : ℕ) (hn : ps.length = n) (hr : rows.length = n)
    (hm : ∀ r ∈ rows, r.length = m) (hu : u.length = m)
    (h9 : w 9 = encL N K ps) (h16 : w 16 = encL N K rows.flatten) (hU : w rVu = encL N K u)
    (hM : w rVm = List.replicate m false) (hN : w rVn = List.replicate n false)
    (hZ : w rZ = encRM N K 0) :
    exec N K mvSubC w 18 = encL N K (mvSubOut ps rows u) := by
  unfold mvSubC
  rw [exec_seq, exec_seq]
  set w0 := exec N K (.cp rQa 16) (exec N K (.clr 18) w) with hw0
  have e0 : ∀ r : Fin 64, r ≠ 18 → r ≠ rQa → w0 r = w r := by
    intro r h1 h2
    simp [hw0, Function.update_of_ne h1, Function.update_of_ne h2]
  have key := exec_rep_inv2 (N := N) (K := K) rVn mvRowBody mvRowBody_writes_rVn
    (fun k w' => w' 18 = encL N K (mvSubOut (ps.take k) (rows.take k) u) ∧
      w' 9 = encL N K (ps.drop k) ∧ w' rQa = encL N K (rows.drop k).flatten) w0
    ⟨by simp [hw0, mvSubOut], by rw [e0 9 (by decide) (by decide), h9]; rfl,
      by simp [hw0, h16]⟩ ?_
  · rw [e0 rVn (by decide) (by decide), hN, List.length_replicate] at key
    rw [key.1, List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
  · intro k w' hk hP _ hfr
    rw [e0 rVn (by decide) (by decide), hN, List.length_replicate] at hk
    obtain ⟨p18, p9, pA⟩ := hP
    have hz : w' rZ = encRM N K 0 := by
      rw [hfr _ (by decide) (by decide), e0 _ (by decide) (by decide), hZ]
    have hu' : w' rVu = encL N K u := by
      rw [hfr _ (by decide) (by decide), e0 _ (by decide) (by decide), hU]
    have hm' : w' rVm = List.replicate m false := by
      rw [hfr _ (by decide) (by decide), e0 _ (by decide) (by decide), hM]
    have hrk : rows.drop k = rows[k]'(by omega) :: rows.drop (k + 1) := drop_cons_getElem rows (by omega)
    have hpk : ps.drop k = ps[k]'(by omega) :: ps.drop (k + 1) := drop_cons_getElem ps (by omega)
    have hlen : (rows[k]'(by omega)).length = m := hm _ (List.getElem_mem _)
    set v := Function.update w' rVn (w' rVn).tail
    have v18 : v 18 = w' 18 := Function.update_of_ne (by decide) _ _
    have v9 : v 9 = w' 9 := Function.update_of_ne (by decide) _ _
    have vA : v rQa = w' rQa := Function.update_of_ne (by decide) _ _
    have vZ : v rZ = w' rZ := Function.update_of_ne (by decide) _ _
    have vU : v rVu = w' rVu := Function.update_of_ne (by decide) _ _
    have vM : v rVm = w' rVm := Function.update_of_ne (by decide) _ _
    unfold mvRowBody
    rw [exec_seq, exec_seq]
    set a := exec N K mvPre v with ha
    have aI : a rIa = encRM N K 0 := by simp [ha, mvPre, exec_seq, vZ, hz]
    have aB : a rQb = encL N K (u ++ []) := by simp [ha, mvPre, exec_seq, vU, hu']
    have aC : a rQc = List.replicate m false := by simp [ha, mvPre, exec_seq, vM, hm']
    have aA : a rQa = encL N K (rows[k]'(by omega) ++ (rows.drop (k + 1)).flatten) := by
      simp only [ha, mvPre, exec_seq, exec_cp]
      simp only [rQa, rQb, rQc, rIa, rQx, rQy, rVu, rVm, rVn, rZ, Function.update_apply, Fin.reduceEq, ↓reduceIte]
      rw [vA, pA, hrk, List.flatten_cons]
    have aZ : a rZ = encRM N K 0 := by simp [ha, mvPre, exec_seq, vZ, hz]
    have a9 : a 9 = w' 9 := by simp [ha, mvPre, exec_seq, v9]
    have a18 : a 18 = w' 18 := by simp [ha, mvPre, exec_seq, v18]
    obtain ⟨bI, bA, -⟩ := exec_ipC hK a (rows[k]'(by omega)) u ((rows.drop (k + 1)).flatten) []
      m 0 hlen hu aA aB aC aI aZ
    set b := exec N K ipC a with hb
    have b9 : b 9 = w' 9 := by rw [hb, exec_writes _ _ _ (by decide), a9]
    have b18 : b 18 = w' 18 := by rw [hb, exec_writes _ _ _ (by decide), a18]
    have bZ : b rZ = encRM N K 0 := by rw [hb, exec_writes _ _ _ (by decide), aZ]
    refine ⟨?_, ?_, ?_⟩
    · simp only [mvPost, exec_seq, exec_cp, exec_mvR, exec_sub, exec_app]
      simp only [rQa, rQb, rQc, rIa, rQx, rQy, rVu, rVm, rVn, rZ, Function.update_apply, Fin.reduceEq, ↓reduceIte]
      rw [b18, b9, bI, bZ, p18, p9, hpk, encL_cons, shiftIn_encRM', takeD_encRM_append,
        takeD_encRM, takeD_encRM, canonW_sub hK, mvSubOut_take_succ ps rows u (by omega) (by omega),
        encL_append, encL_singleton, zero_add]
    · simp only [mvPost, exec_seq, exec_cp, exec_mvR, exec_sub, exec_app]
      simp only [rQa, rQb, rQc, rIa, rQx, rQy, rVu, rVm, rVn, rZ, Function.update_apply, Fin.reduceEq, ↓reduceIte]
      rw [b9, p9, hpk, encL_cons, List.drop_append_of_le_length (by simp [SigabaNeo.Lattices.Algo.length_encRM]),
        List.drop_of_length_le (by simp [SigabaNeo.Lattices.Algo.length_encRM])]
      rfl
    · simp only [mvPost, exec_seq, exec_cp, exec_mvR, exec_sub, exec_app]
      simp only [rQa, rQb, rQc, rIa, rQx, rQy, rVu, rVm, rVn, rZ, Function.update_apply, Fin.reduceEq, ↓reduceIte]
      exact bA

/-- The rows of a matrix over enumerated index types, row-major. -/
def rowsWord {α β : Type} [Enum α] [Enum β] (X : α → β → Rq N K) : List (Rq N K) :=
  ((Enum.list (α := α)).map fun q => (Enum.list (α := β)).map (X q)).flatten

/-- **The correction `p − X u` over enumerated index types.** -/
theorem exec_mvSubC_enum (hK : 0 < K) {α β : Type} [Enum α] [Enum β] [Fintype β] [DecidableEq β]
    (w : St) (p : α → Rq N K) (X : α → β → Rq N K) (u : β → Rq N K)
    (h9 : w 9 = encL N K (Enum.list.map p)) (h16 : w 16 = encL N K (rowsWord X))
    (hU : w rVu = encL N K (Enum.list.map u))
    (hM : w rVm = List.replicate (Enum.list (α := β)).length false)
    (hN : w rVn = List.replicate (Enum.list (α := α)).length false)
    (hZ : w rZ = encRM N K 0) :
    exec N K mvSubC w 18 = encL N K (Enum.list.map fun q => p q - ∑ c, X q c * u c) := by
  rw [exec_mvSubC hK w (Enum.list.map p) ((Enum.list (α := α)).map fun q => Enum.list.map (X q))
    (Enum.list.map u) _ _ (by simp) (by simp) (fun r hr => by
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp hr; simp) (by simp) h9 h16 hU hM hN hZ]
  congr 1
  unfold mvSubOut
  rw [List.zipWith_map, List.zipWith_self]
  refine List.map_congr_left fun q _ => ?_
  rw [zip_enum_sum]

end AdvancedEncryption.ExpLUT.Prog
