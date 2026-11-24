import PE.Impl.ExpLUT.Prog.KeyVM

/-!
# KeyGen (package F3): the routines of the lookup tables

VM code (`SigabaNeo.Tape.MVM`) for the lookup tables of `EvalPK` (§4.3–§4.4), generic in `N`, `K`:

* `matAddC`: `rAcc += rMOut` entrywise (`exec_matAddC`);
* `agC`: the matrix `α G` (`gM α`) in `rMA` from `α` in `rAl` (`exec_agC`);
* `bitLoopC`: from `e` bits of the stream `rCp`, `rE := X⁻ᶜ · rE` with `c` the complement of the
  bits, `Σ_{i<e} [¬ bit_i] 2^i` (`exec_bitLoopC`);
* `coefAC`, `coefVC`: the coefficients of a table: `α = 2^{K−b} (X_c Σ_{u<n} X^{−c_u} μ^u)` from
  the entries of `e` bits, `v = 2^{K−b} Σ_{u<n} [bit_u] μ^u` from bits (`exec_coefAC`,
  `exec_coefVC`).

Registers: the caller's are `0 … 28` (`rAinS … rT15`); the routines here use the library's
scratch registers (`rS … rCi`, `rRo0`, `rRo1`, `rX0`, `rX1`), never inside a library routine.
-/

set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Lattices.Algo.NegaG
  SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM decRM block concatN encM length_encM block_concatN)

/-! ### Registers -/

/-- The stream of the digit matrices `A^in` (one step per `16 K³` matrices). -/
@[simp, vmreg] abbrev rAinS : Fin 64 := 0
/-- The word of `A^aut` (all `t < b`). -/
@[simp, vmreg] abbrev rAautW : Fin 64 := 1
/-- The word of `H` (all helpers). -/
@[simp, vmreg] abbrev rHW : Fin 64 := 2
/-- The stream of the predicate word (the current table first). -/
@[simp, vmreg] abbrev rCs : Fin 64 := 3
/-- The current public matrix `A_i`. -/
@[simp, vmreg] abbrev rA : Fin 64 := 4
/-- The accumulator of a table. -/
@[simp, vmreg] abbrev rAcc : Fin 64 := 5
/-- The index `j` as a constant. -/
@[simp, vmreg] abbrev rJ : Fin 64 := 6
/-- `μ_j = σ_{g^j}(X⁻¹)`. -/
@[simp, vmreg] abbrev rMu : Fin 64 := 7
/-- The input of the table, `mulPK(A_i, A^in_i)`. -/
@[simp, vmreg] abbrev rB : Fin 64 := 8
/-- The counter of `j`. -/
@[simp, vmreg] abbrev rCj2 : Fin 64 := 9
/-- The counter of the steps. -/
@[simp, vmreg] abbrev rCst : Fin 64 := 10
/-- The coefficient `α_j`. -/
@[simp, vmreg] abbrev rAl : Fin 64 := 11
/-- The stream of `A^aut` in a chain. -/
@[simp, vmreg] abbrev rSs : Fin 64 := 12
/-- The stream of `H` in a chain. -/
@[simp, vmreg] abbrev rHs : Fin 64 := 13
/-- The counter of `t` in a chain. -/
@[simp, vmreg] abbrev rCt : Fin 64 := 14
/-- `2^t` in unary. -/
@[simp, vmreg] abbrev rPw2 : Fin 64 := 15
/-- Free. -/
@[simp, vmreg] abbrev rF16 : Fin 64 := 16
/-- Free. -/
@[simp, vmreg] abbrev rF17 : Fin 64 := 17
/-- The word of `1`. -/
@[simp, vmreg] abbrev rOne : Fin 64 := 18
/-- The word of `X⁻¹`. -/
@[simp, vmreg] abbrev rMu0 : Fin 64 := 19
/-- The word of `X_c` (`X^{2^e − 1}`). -/
@[simp, vmreg] abbrev rXc : Fin 64 := 20
/-- The template `[false]`. -/
@[simp, vmreg] abbrev rBit1 : Fin 64 := 21
/-- The template of `W`. -/
@[simp, vmreg] abbrev rTW : Fin 64 := 22
/-- The template of `b`. -/
@[simp, vmreg] abbrev rTb : Fin 64 := 23
/-- The template of `e` (bits per table entry). -/
@[simp, vmreg] abbrev rTe : Fin 64 := 24
/-- The template of a table (`e W` bits). -/
@[simp, vmreg] abbrev rTtab : Fin 64 := 25
/-- The template of a block of `A^aut` (`16 K³ N K` bits). -/
@[simp, vmreg] abbrev rTBlk : Fin 64 := 26
/-- The template of `4 K`. -/
@[simp, vmreg] abbrev rT4K : Fin 64 := 27
/-- The template of `15`. -/
@[simp, vmreg] abbrev rT15 : Fin 64 := 28

variable {N K : ℕ}

/-! ### Lists -/

theorem drop_cons_getElem {α : Type} (l : List α) {m : ℕ} (h : m < l.length) :
    l.drop m = l[m] :: l.drop (m + 1) := List.drop_eq_getElem_cons h

theorem take_succ_getElem {α : Type} (l : List α) {m : ℕ} (h : m < l.length) :
    l.take (m + 1) = l.take m ++ [l[m]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]; rfl

/-! ### Loops with a frame -/

/-- **A `rep` loop by an invariant, with the frame**: in every round, the registers the body does
not write (other than the counter) still hold their initial words. -/
theorem exec_rep_inv2 (c : Fin 64) (body : Code) (hb : body.writes c = false) (P : ℕ → St → Prop)
    (w : St) (h0 : P 0 w)
    (hs : ∀ m w', m < (w c).length → P m w' → w' c = (w c).drop m →
      (∀ r, body.writes r = false → r ≠ c → w' r = w r) →
      P (m + 1) (exec N K body (Function.update w' c (w' c).tail))) :
    P (w c).length (exec N K (.rep c body) w) := by
  have key := exec_rep_inv (N := N) (K := K) c body hb
    (fun m w' => P m w' ∧ ∀ r, body.writes r = false → r ≠ c → w' r = w r) w
    ⟨h0, fun _ _ _ => rfl⟩ (fun m w' hm hP hc => ⟨hs m w' hm hP.1 hc hP.2, fun r hr hrc => by
      rw [exec_writes body _ r hr, Function.update_of_ne hrc, hP.2 r hr hrc]⟩)
  exact key.1

/-! ### `rAcc += rMOut` -/

/-- One entry. -/
def maBody : Code :=
  .seq (.cp rX0 rZ) <| .seq (.mvR rX0 rRo0) <| .seq (.cp rX1 rZ) <| .seq (.mvR rX1 rRo1) <|
  .seq (.op .add rX0 rX0 rX1) (.app rAcc rX0)

/-- Before the loop of `matAddC`. -/
def maPre : Code := .seq (.cp rRo0 rAcc) <| .seq (.cp rRo1 rMOut) <| .seq (.clr rAcc) (.cp rCi rT4K)

/-- **`rAcc += rMOut`** entrywise (`|rT4K|` entries). -/
def matAddC : Code := .seq maPre (.rep rCi maBody)

theorem maBody_writes_rCi : maBody.writes rCi = false := by decide

theorem exec_maLoop (hK : 0 < K) (w : St) (l1 l2 : List (Rq N K)) (n : ℕ)
    (h1 : l1.length = n) (h2 : l2.length = n) (hA : w rRo0 = encL N K l1)
    (hO : w rRo1 = encL N K l2) (hC : w rCi = List.replicate n false) (hAcc : w rAcc = [])
    (hZ : w rZ = encRM N K 0) :
    exec N K (.rep rCi maBody) w rAcc = encL N K (List.zipWith (· + ·) l1 l2) := by
  have key := exec_rep_inv (N := N) (K := K) rCi maBody maBody_writes_rCi
    (fun m w' => w' rRo0 = encL N K (l1.drop m) ∧ w' rRo1 = encL N K (l2.drop m) ∧
      w' rAcc = encL N K (List.zipWith (· + ·) (l1.take m) (l2.take m)) ∧ w' rZ = encRM N K 0) w
    ⟨by simp [hA], by simp [hO], by simp [hAcc], hZ⟩ ?_
  · rw [hC, List.length_replicate] at key
    rw [key.2.2.1, List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
  · intro m w' hm hP _
    rw [hC, List.length_replicate] at hm
    obtain ⟨p1, p2, p3, p4⟩ := hP
    have e1 := drop_cons_getElem l1 (show m < l1.length by omega)
    have e2 := drop_cons_getElem l2 (show m < l2.length by omega)
    have t1 := take_succ_getElem l1 (show m < l1.length by omega)
    have t2 := take_succ_getElem l2 (show m < l2.length by omega)
    rw [e1, encL_cons] at p1
    rw [e2, encL_cons] at p2
    unfold maBody
    vm_simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [Function.update_apply, p1, p4]
    · simp [Function.update_apply, p2, p4]
    · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, p1, p2, p3, p4,
        shiftIn_encRM', takeD_encRM_append, takeD_encRM, canonW_add hK, t1, t2]
      rw [List.zipWith_append (by simp; omega), encL_append]
      simp
    · simp [Function.update_apply, p4]

theorem exec_matAddC (hK : 0 < K) (w : St) (l1 l2 : List (Rq N K)) (n : ℕ)
    (h1 : l1.length = n) (h2 : l2.length = n) (hA : w rAcc = encL N K l1)
    (hO : w rMOut = encL N K l2) (hT : w rT4K = List.replicate n false)
    (hZ : w rZ = encRM N K 0) :
    exec N K matAddC w rAcc = encL N K (List.zipWith (· + ·) l1 l2) := by
  rw [matAddC, exec_seq]
  refine exec_maLoop hK _ l1 l2 n h1 h2 ?_ ?_ ?_ ?_ ?_ <;>
    (unfold maPre; vm_simp; simp [hA, hO, hT, hZ])

theorem map_add_zip {α : Type} (L : List α) (f g : α → Rq N K) :
    L.map (fun x => f x + g x) = List.zipWith (· + ·) (L.map f) (L.map g) := by
  rw [List.zipWith_map, List.zipWith_self]

/-- Matrices add entrywise. -/
theorem matL_add (hK : 0 < K) (A B : Fin 2 → Fin 2 × Fin K → Rq N K) :
    matL (fun a c => A a c + B a c) = List.zipWith (· + ·) (matL A) (matL B) := by
  rw [matL_eq_range hK, matL_eq_range hK, matL_eq_range hK, List.zipWith_append (by simp),
    map_add_zip, map_add_zip]

/-! ### The matrix `α G` -/

/-- The matrix `α G`: `(α G)_{a, (r, i)} = [a = r] 2^i α`. -/
def gM (α : Rq N K) : Fin 2 → Fin 2 × Fin K → Rq N K := fun a c => if a = c.1 then 2 ^ (c.2 : ℕ) * α else 0

/-- One power: `rRo0 ++= x`, `x := 2 x`. -/
def agBody : Code := .seq (.app rRo0 rX0) (.op .add rX0 rX0 rX0)

/-- Before the loop of `agC`. -/
def agPre : Code := .seq (.clr rRo0) <| .seq (.cp rX0 rAl) (.cp rCi rTK)

/-- After the loop: the rows `[seg, 0]` and `[0, seg]`. -/
def agPost : Code :=
  .seq (.cp rMA rRo0) <| .seq (.app rMA rTKNK) <| .seq (.app rMA rTKNK) (.app rMA rRo0)

/-- **`rMA := α G`** (`α` in `rAl`). -/
def agC : Code := .seq agPre (.seq (.rep rCi agBody) agPost)

theorem agBody_writes_rCi : agBody.writes rCi = false := by decide

theorem exec_agLoop (hK : 0 < K) (w : St) (α : Rq N K) (hR : w rRo0 = []) (hX : w rX0 = encRM N K α)
    (hC : w rCi = List.replicate K false) :
    exec N K (.rep rCi agBody) w rRo0 = encL N K ((List.range K).map fun i => 2 ^ i * α) := by
  have key := exec_rep_inv2 (N := N) (K := K) rCi agBody agBody_writes_rCi
    (fun m w' => w' rRo0 = encL N K ((List.range m).map fun i => 2 ^ i * α) ∧
      w' rX0 = encRM N K (2 ^ m * α)) w ⟨by simp [hR], by simp [hX]⟩ ?_
  · rw [hC, List.length_replicate] at key
    exact key.1
  · intro m w' _ hP _ _
    obtain ⟨p1, p2⟩ := hP
    unfold agBody
    vm_simp
    refine ⟨?_, ?_⟩
    · simp [p1, p2, List.range_succ]
    · simp [p2, canonW_add hK, pow_succ]; ring_nf

theorem map_finRange_val {α : Type} (n : ℕ) (f : ℕ → α) :
    (List.finRange n).map (fun i => f i.val) = (List.range n).map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem matL_gM (α : Rq N K) :
    matL (gM α) = (List.range K).map (fun i => 2 ^ i * α) ++ List.replicate K 0 ++
      (List.replicate K 0 ++ (List.range K).map (fun i => 2 ^ i * α)) := by
  rw [matL_eq]
  simp only [segL, gM]
  congr 1
  · congr 1
    · exact map_finRange_val K (fun i => 2 ^ i * α)
    · simp
  · congr 1
    · simp
    · exact map_finRange_val K (fun i => 2 ^ i * α)

/-- **`agC` writes `α G`.** -/
theorem exec_agC (hK : 0 < K) (w : St) (α : Rq N K) (hA : w rAl = encRM N K α)
    (hT : MulTmpl N K w) :
    exec N K agC w rMA = encL N K (matL (gM α)) := by
  rw [agC, exec_seq, exec_seq]
  have hl := exec_agLoop hK (exec N K agPre w) α (by unfold agPre; vm_simp; simp)
    (by unfold agPre; vm_simp; simp [hA]) (by unfold agPre; vm_simp; simp [hT.tK])
  have hT' : exec N K (.rep rCi agBody) (exec N K agPre w) rTKNK = encL N K (List.replicate K 0) := by
    rw [exec_writes _ _ _ (by decide)]; unfold agPre; vm_simp; simp [hT.tKNK]
  unfold agPost; vm_simp
  simp [hl, hT', matL_gM]

/-! ### The coefficients of a table -/

/-- Scratch registers of the coefficient routines. -/
@[simp, vmreg] abbrev rPw : Fin 64 := 35
@[simp, vmreg] abbrev rCu : Fin 64 := 36
@[simp, vmreg] abbrev rE : Fin 64 := 37
@[simp, vmreg] abbrev rCnt : Fin 64 := 38
@[simp, vmreg] abbrev rCb : Fin 64 := 39
@[simp, vmreg] abbrev rCp : Fin 64 := 40

/-- The complement of the first `m` bits: `Σ_{i<m} [¬ C_i] 2^i`. -/
def cmpl (C : List Bool) (m : ℕ) : ℕ := ∑ i ∈ Finset.range m, if C.getD i false then 0 else 2 ^ i

theorem cmpl_succ (C : List Bool) (m : ℕ) :
    cmpl C (m + 1) = cmpl C m + (if C.getD m false then 0 else 2 ^ m) := Finset.sum_range_succ _ _

theorem headD_drop (C : List Bool) (m : ℕ) : (C.drop m).headD false = C.getD m false := by
  induction C generalizing m with
  | nil => simp
  | cons x C ih => cases m <;> simp [ih]

/-- One bit: `rE := X^{−2^m} rE` if the bit is `0`. -/
def bitBody : Code := .seq (.ifb rCp .nop (.op .rho rE rE rCnt)) <| .seq (.tl rCp) (.app rCnt rCnt)

theorem bitBody_writes_rCb : bitBody.writes rCb = false := by decide

theorem exec_bitLoop (hN : 0 < N) (hK : 0 < K) (w : St) (e : ℕ) (C : List Bool) (E0 : Rq N K)
    (hp : w rCp = C) (hE : w rE = encRM N K E0) (hc : w rCnt = [false])
    (hb : w rCb = List.replicate e false) :
    exec N K (.rep rCb bitBody) w rE = encRM N K (xInvG (ZMod (2 ^ K - 1)) N ^ cmpl C e * E0) ∧
    exec N K (.rep rCb bitBody) w rCp = C.drop e := by
  have key := exec_rep_inv2 (N := N) (K := K) rCb bitBody bitBody_writes_rCb
    (fun m w' => w' rCp = C.drop m ∧ w' rCnt = List.replicate (2 ^ m) false ∧
      w' rE = encRM N K (xInvG (ZMod (2 ^ K - 1)) N ^ cmpl C m * E0)) w
    ⟨by simp [hp], by simp [hc], by simp [hE, cmpl]⟩ ?_
  · rw [hb, List.length_replicate] at key
    exact ⟨key.2.2, key.1⟩
  · intro m w' _ hP _ _
    obtain ⟨p1, p2, p3⟩ := hP
    unfold bitBody
    rw [exec_seq, exec_ifb]
    have hh : hd (Function.update w' rCb (w' rCb).tail rCp) = C.getD m false := by
      rw [Function.update_of_ne (by decide), p1, hd, headD_drop]
    rw [hh]
    by_cases hbit : C.getD m false = true
    · rw [if_pos hbit]
      vm_simp
      refine ⟨?_, ?_, ?_⟩
      · simp [p1]
      · simp [p2, pow_succ, mul_two]
      · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, p3]
        rw [cmpl_succ, if_pos hbit, add_zero]
    · rw [if_neg hbit]
      vm_simp
      refine ⟨?_, ?_, ?_⟩
      · simp [p1]
      · simp [p2, pow_succ, mul_two]
      · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, p3, p2, takeD_encRM,
          canonW_rho hK hN, List.length_replicate]
        rw [cmpl_succ, if_neg hbit, pow_add]
        congr 1; ring

/-- One entry of an `α`-table: `rAl += X^{−c_u} pw`, `pw := pw μ`. -/
def uBody : Code := .seq (.cp rE rPw) <| .seq (.cp rCnt rBit1) <| .seq (.cp rCb rTe) <|
  .seq (.rep rCb bitBody) <| .seq (.op .add rAl rAl rE) (.op .mul rPw rPw rMu)

/-- Before the loop of a coefficient. -/
def coefPre : Code := .seq (.cp rAl rZ) <| .seq (.cp rPw rOne) (.cp rCu rTW)

/-- **The coefficient of an `α`-table** (stream `rCp`, `μ` in `rMu`): `rAl := α`. -/
def coefAC : Code :=
  .seq coefPre <| .seq (.rep rCu uBody) <| .seq (.op .mul rAl rAl rXc) (.op .rot rAl rAl rTb)

/-- The sum of an `α`-table: `Σ_{u<n} X^{−c_u} μ^u`, `c_u` the complement of entry `u`. -/
noncomputable def sumA (C : List Bool) (e n : ℕ) (μ : Rq N K) : Rq N K :=
  ∑ u ∈ Finset.range n, xInvG (ZMod (2 ^ K - 1)) N ^ cmpl (C.drop (e * u)) e * μ ^ u

theorem uBody_writes_rCu : uBody.writes rCu = false := by decide

theorem exec_uLoop (hN : 0 < N) (hK : 0 < K) (w : St) (e n : ℕ) (C : List Bool) (μ : Rq N K)
    (hp : w rCp = C) (hA : w rAl = encRM N K 0) (hP : w rPw = encRM N K 1)
    (hc : w rCu = List.replicate n false) (hM : w rMu = encRM N K μ) (h1 : w rBit1 = [false])
    (he : w rTe = List.replicate e false) :
    exec N K (.rep rCu uBody) w rAl = encRM N K (sumA C e n μ) ∧
    exec N K (.rep rCu uBody) w rCp = C.drop (e * n) := by
  have key := exec_rep_inv2 (N := N) (K := K) rCu uBody uBody_writes_rCu
    (fun m w' => w' rCp = C.drop (e * m) ∧ w' rPw = encRM N K (μ ^ m) ∧
      w' rAl = encRM N K (sumA C e m μ)) w
    ⟨by simp [hp], by simp [hP], by simp [hA, sumA]⟩ ?_
  · rw [hc, List.length_replicate] at key
    exact ⟨key.2.2, key.1⟩
  · intro m w' _ hP' _ hfr
    obtain ⟨p1, p2, p3⟩ := hP'
    have hMu : w' rMu = encRM N K μ := by rw [hfr _ (by decide) (by decide), hM]
    have hB1 : w' rBit1 = [false] := by rw [hfr _ (by decide) (by decide), h1]
    have hTe : w' rTe = List.replicate e false := by rw [hfr _ (by decide) (by decide), he]
    unfold uBody
    rw [exec_seq, exec_seq, exec_seq, exec_seq]
    set w1 := exec N K (.cp rCb rTe) (exec N K (.cp rCnt rBit1) (exec N K (.cp rE rPw)
      (Function.update w' rCu (w' rCu).tail))) with hw1
    obtain ⟨b1, b2⟩ := exec_bitLoop hN hK w1 e (C.drop (e * m)) (μ ^ m)
      (by rw [hw1]; vm_simp; simp [p1]) (by rw [hw1]; vm_simp; simp [p2])
      (by rw [hw1]; vm_simp; simp [hB1]) (by rw [hw1]; vm_simp; simp [hTe])
    have f3 : exec N K (.rep rCb bitBody) w1 rAl = encRM N K (sumA C e m μ) := by
      rw [exec_writes _ _ _ (by decide), hw1]; vm_simp; simp [p3]
    have f2 : exec N K (.rep rCb bitBody) w1 rPw = encRM N K (μ ^ m) := by
      rw [exec_writes _ _ _ (by decide), hw1]; vm_simp; simp [p2]
    have f4 : exec N K (.rep rCb bitBody) w1 rMu = encRM N K μ := by
      rw [exec_writes _ _ _ (by decide), hw1]; vm_simp; simp [hMu]
    vm_simp
    refine ⟨?_, ?_, ?_⟩
    · simp [b2, List.drop_drop, mul_add, add_comm]
    · simp [f2, f4, canonW_mul hK, pow_succ]
    · simp [f3, b1, canonW_add hK, sumA, Finset.sum_range_succ, List.drop_drop]

/-- **The coefficient of an `α`-table**: `2^{K−b} (X_c Σ_{u<n} X^{−c_u} μ^u)`. -/
theorem exec_coefAC (hN : 0 < N) (hK : 0 < K) (w : St) (e n b : ℕ) (hbK : b ≤ K) (C : List Bool)
    (μ xc : Rq N K) (hp : w rCp = C) (hM : w rMu = encRM N K μ) (hO : w rOne = encRM N K 1)
    (hX : w rXc = encRM N K xc) (h1 : w rBit1 = [false]) (he : w rTe = List.replicate e false)
    (hW : w rTW = List.replicate n false) (hb : w rTb = List.replicate b false)
    (hZ : w rZ = encRM N K 0) :
    exec N K coefAC w rAl =
      encRM N K ((2 : ZMod (2 ^ K - 1)) ^ (K - b) • (sumA C e n μ * xc)) ∧
    exec N K coefAC w rCp = C.drop (e * n) := by
  unfold coefAC
  rw [exec_seq, exec_seq]
  set w1 := exec N K coefPre w with hw1
  obtain ⟨u1, u2⟩ := exec_uLoop hN hK w1 e n C μ (by rw [hw1]; unfold coefPre; vm_simp; simp [hp])
    (by rw [hw1]; unfold coefPre; vm_simp; simp [hZ]) (by rw [hw1]; unfold coefPre; vm_simp; simp [hO])
    (by rw [hw1]; unfold coefPre; vm_simp; simp [hW]) (by rw [hw1]; unfold coefPre; vm_simp; simp [hM])
    (by rw [hw1]; unfold coefPre; vm_simp; simp [h1]) (by rw [hw1]; unfold coefPre; vm_simp; simp [he])
  have fX : exec N K (.rep rCu uBody) w1 rXc = encRM N K xc := by
    rw [exec_writes _ _ _ (by decide), hw1]; unfold coefPre; vm_simp; simp [hX]
  have fb : exec N K (.rep rCu uBody) w1 rTb = List.replicate b false := by
    rw [exec_writes _ _ _ (by decide), hw1]; unfold coefPre; vm_simp; simp [hb]
  vm_simp
  refine ⟨?_, ?_⟩
  · simp [u1, fX, fb, canonW_mul hK, canonW_rot hK hbK]
  · simp [u2]

/-- One entry of a `v`-table: `rAl += [bit] pw`, `pw := pw μ`. -/
def vBody : Code := .seq (.ifb rCp (.op .add rAl rAl rPw) .nop) <| .seq (.tl rCp) (.op .mul rPw rPw rMu)

/-- **The coefficient of a `v`-table**: `rAl := v`. -/
def coefVC : Code := .seq coefPre <| .seq (.rep rCu vBody) (.op .rot rAl rAl rTb)

/-- The sum of a `v`-table: `Σ_{u<n} [C_u] μ^u`. -/
noncomputable def sumV (C : List Bool) (n : ℕ) (μ : Rq N K) : Rq N K :=
  ∑ u ∈ Finset.range n, (if C.getD u false then μ ^ u else 0)

theorem sumV_succ (C : List Bool) (m : ℕ) (μ : Rq N K) :
    sumV C (m + 1) μ = sumV C m μ + (if C.getD m false then μ ^ m else 0) :=
  Finset.sum_range_succ _ _

theorem vBody_writes_rCu : vBody.writes rCu = false := by decide

/-- **The coefficient of a `v`-table**: `2^{K−b} Σ_{u<n} [C_u] μ^u`. -/
theorem exec_coefVC (hK : 0 < K) (w : St) (n b : ℕ) (hbK : b ≤ K) (C : List Bool)
    (μ : Rq N K) (hp : w rCp = C) (hM : w rMu = encRM N K μ) (hO : w rOne = encRM N K 1)
    (hW : w rTW = List.replicate n false) (hb : w rTb = List.replicate b false)
    (hZ : w rZ = encRM N K 0) :
    exec N K coefVC w rAl = encRM N K ((2 : ZMod (2 ^ K - 1)) ^ (K - b) • sumV C n μ) ∧
    exec N K coefVC w rCp = C.drop n := by
  unfold coefVC
  rw [exec_seq, exec_seq]
  set w1 := exec N K coefPre w with hw1
  have key := exec_rep_inv2 (N := N) (K := K) rCu vBody vBody_writes_rCu
    (fun m w' => w' rCp = C.drop m ∧ w' rPw = encRM N K (μ ^ m) ∧
      w' rAl = encRM N K (sumV C m μ)) w1
    ⟨by rw [hw1]; unfold coefPre; vm_simp; simp [hp],
      by rw [hw1]; unfold coefPre; vm_simp; simp [hO],
      by rw [hw1]; unfold coefPre; vm_simp; simp [hZ, sumV]⟩ ?_
  · have hc : (w1 rCu).length = n := by rw [hw1]; unfold coefPre; vm_simp; simp [hW]
    rw [hc] at key
    have fb : exec N K (.rep rCu vBody) w1 rTb = List.replicate b false := by
      rw [exec_writes _ _ _ (by decide), hw1]; unfold coefPre; vm_simp; simp [hb]
    vm_simp
    refine ⟨?_, ?_⟩
    · simp [key.2.2, fb, canonW_rot hK hbK]
    · simp [key.1]
  · intro m w' _ hP' _ hfr
    obtain ⟨p1, p2, p3⟩ := hP'
    have hMu : w' rMu = encRM N K μ := by
      rw [hfr _ (by decide) (by decide), hw1]; unfold coefPre; vm_simp; simp [hM]
    unfold vBody
    rw [exec_seq, exec_ifb]
    have hh : hd (Function.update w' rCu (w' rCu).tail rCp) = C.getD m false := by
      rw [Function.update_of_ne (by decide), p1, hd, headD_drop]
    rw [hh]
    by_cases hbit : C.getD m false = true
    · rw [if_pos hbit]
      vm_simp
      refine ⟨?_, ?_, ?_⟩
      · simp [p1]
      · simp [p2, hMu, canonW_mul hK, pow_succ]
      · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, p2, p3, takeD_encRM,
          canonW_add hK]
        rw [sumV_succ, if_pos hbit]
    · rw [if_neg hbit]
      vm_simp
      refine ⟨?_, ?_, ?_⟩
      · simp [p1]
      · simp [p2, hMu, canonW_mul hK, pow_succ]
      · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, p3]
        rw [sumV_succ, if_neg hbit, add_zero]

/-! ### The chains `A_j` -/

theorem hd_encRM (hN : 0 < N) (hK : 0 < K) (a : Rq N K) :
    hd (encRM N K a) = (a.coeffs ⟨0, hN⟩).val.testBit 0 := by
  have hb := block_concatN (n := N) (K := K) (f := fun i => encM K (coefG a i))
    (fun _ _ => length_encM _ _) 0
  rw [if_pos hN] at hb
  have e : hd (encRM N K a) = (block K 0 (encRM N K a)).headD false := by
    unfold hd block encRM
    rw [zero_mul, List.drop_zero]
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    cases concatN N (fun i => encM (K' + 1) (coefG a i)) <;> simp
  rw [e, encRM, hb, encM, coefG_of_lt a hN]
  have := getD_toBits K ((a.coeffs ⟨0, hN⟩).val) 0
  rw [List.getD_eq_getElem?_getD] at this
  rw [List.headD_eq_head?_getD, List.head?_eq_getElem?, this]
  simp [hK]

/-- The digit `t` of the constant `j < q` is the bit `t` of `j`. -/
theorem hd_dig_natCast (hN : 0 < N) (hK : 0 < K) (j t : ℕ) (hj : j < 2 ^ K - 1) :
    hd (encRM N K (binaryDigit (j : Rq N K) t)) = j.testBit t := by
  rw [hd_encRM hN hK, coeffs_binaryDigit, Negacyclic.coeffs_natCast]
  simp only [↓reduceIte]
  have hv : ((j : ZMod (2 ^ K - 1))).val = j := ZMod.val_natCast_of_lt hj
  rw [hv]
  haveI : NeZero (2 ^ K - 1) := ⟨by omega⟩
  by_cases h : j.testBit t
  · have hj0 : j ≠ 0 := by rintro rfl; simp at h
    rw [if_pos h, ZMod.val_one'' (by omega)]; simp [h]
  · rw [if_neg h, ZMod.val_zero]; simp [h]

/-- `Aut` as computed by `autPKC`: `H · G⁻¹(mulPK(σ_g^{m}(A), A^aut))`. -/
def autVM (g m : ℕ) (H : Fin 2 → Fin 2 × Fin K → Rq N K) (Aa : DigI K → Fin 2 → Fin 2 × Fin K → Rq N K)
    (A : Fin 2 → Fin 2 × Fin K → Rq N K) : Fin 2 → Fin 2 × Fin K → Rq N K :=
  ginvMulm H (mulPKm (fun a c => (aut N g)^[m] (A a c)) Aa)

/-- **The chain of `A_j`**: `Aut_{g_t}` (`σ_g^{2^t}`) for the set bits `t < b` of `j`. -/
def chainM (g : ℕ) (Hf : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K)
    (Aa : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (b j : ℕ)
    (B : Fin 2 → Fin 2 × Fin K → Rq N K) : Fin 2 → Fin 2 × Fin K → Rq N K :=
  bitChain (fun t M => autVM g (2 ^ t) (Hf t) (Aa t) M) b j B

/-- The `Aut` step of a chain: `rMA := Aut_{g_t}(rMA)`, the stream `rSs` advanced. -/
def autStep : Code :=
  .seq (.cp rMAd rSs) <| .seq (.cp rP rPw2) <| .seq autPKC <| .seq (.cp rMA rMOut) (.cp rSs rMAd)

/-- Before the branch: the digit `t` of `j` in `rS2`, `H_{g_t}` in `rGX`. -/
def chPre : Code :=
  .seq (.cp rS rTb) <| .seq (.tl rS) <| .seq (.drop rS rCt) <| .seq (.op .dig rS2 rJ rS) <|
  .seq (.cp rGX rT4KNK) <| .seq (.mv rGX rHs rT4KNK) (.drop rHs rT4KNK)

/-- One round `t` of a chain. -/
def chBody : Code := .seq chPre <| .seq (.ifb rS2 autStep (.drop rSs rTBlk)) (.app rPw2 rPw2)

/-- **The chain**: `rMA := A_j` from `rMA = B`, the streams of `A^aut` and `H` copied. -/
def chainC : Code :=
  .seq (.cp rSs rAautW) <| .seq (.cp rHs rHW) <| .seq (.cp rPw2 rBit1) <| .seq (.cp rCt rTb)
    (.rep rCt chBody)

theorem autPKC_writes_low : ∀ r : Fin 64, r.val < 29 → autPKC.writes r = false := by decide
theorem chBody_writes_rCt : chBody.writes rCt = false := by decide

/-- The word of a family of `H` matrices (`(t, 0)`, `(t, 1)` for each `t`). -/
def hL (Hf Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (l : List ℕ) : List (Rq N K) :=
  l.flatMap fun t => matL (Hf t) ++ matL (Hi t)

/-- The word of a family of digit matrices `A^aut_t`. -/
def aautL (Aa : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (l : List ℕ) : List (Rq N K) :=
  l.flatMap fun t => adL (Aa t)

theorem length_adL (Ad : DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) :
    (adL Ad).length = 16 * K ^ 3 := by
  rw [adL_eq, enum_fin2]
  simp only [List.length_flatMap, length_matL, List.map_const', List.sum_replicate,
    List.length_finRange, smul_eq_mul, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    length_enum_col]
  ring

/-- The registers a chain reads. -/
structure ChainIn (w : St) (g b j : ℕ) (Hf Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K)
    (Aa : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) : Prop where
  kc : w rKc = List.replicate g false
  aw : w rAautW = encL N K (aautL Aa (List.range b))
  hw : w rHW = encL N K (hL Hf Hi (List.range b))
  bit1 : w rBit1 = [false]
  tb : w rTb = List.replicate b false
  blk : w rTBlk = List.replicate (16 * K ^ 3 * (N * K)) false
  jw : w rJ = encRM N K (j : Rq N K)
  tm : MulTmpl N K w

theorem chBody_writes_ge : ∀ r : Fin 64, 57 ≤ r.val → chBody.writes r = false := by decide
theorem chBody_writes_in : ∀ r : Fin 64, (r = rKc ∨ r = rTb ∨ r = rTBlk ∨ r = rJ) →
    chBody.writes r = false := by decide

theorem drop_range_succ {n t : ℕ} (h : t < n) :
    (List.range n).drop t = t :: (List.range n).drop (t + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h)]; simp

theorem chainM_succ (g : ℕ) (Hf : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K)
    (Aa : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (t j : ℕ)
    (B : Fin 2 → Fin 2 × Fin K → Rq N K) :
    chainM g Hf Aa (t + 1) j B =
      if j.testBit t then autVM g (2 ^ t) (Hf t) (Aa t) (chainM g Hf Aa t j B)
      else chainM g Hf Aa t j B := rfl

/-- **The chain loop**: `b` rounds of `chBody`. -/
theorem exec_chainLoop (hN : 0 < N) (hK : 0 < K) (w : St) (g b j : ℕ) (hg : 0 < g)
    (hj : j < 2 ^ K - 1) (Hf Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K)
    (Aa : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (B : Fin 2 → Fin 2 × Fin K → Rq N K)
    (hin : ChainIn w g b j Hf Hi Aa) (hMA : w rMA = encL N K (matL B))
    (hSs : w rSs = encL N K (aautL Aa (List.range b)))
    (hHs : w rHs = encL N K (hL Hf Hi (List.range b))) (hP2 : w rPw2 = [false])
    (hCt : w rCt = List.replicate b false) :
    exec N K (.rep rCt chBody) w rMA = encL N K (matL (chainM g Hf Aa b j B)) := by
  have key := exec_rep_inv2 (N := N) (K := K) rCt chBody chBody_writes_rCt
    (fun t w' => w' rMA = encL N K (matL (chainM g Hf Aa t j B)) ∧
      w' rSs = encL N K (aautL Aa ((List.range b).drop t)) ∧
      w' rHs = encL N K (hL Hf Hi ((List.range b).drop t)) ∧
      w' rPw2 = List.replicate (2 ^ t) false) w
    ⟨by simp [hMA, chainM, bitChain], by simp [hSs], by simp [hHs], by simp [hP2]⟩ ?_
  · rw [hCt, List.length_replicate] at key
    exact key.1
  · intro t w' ht hP hc hfr
    rw [hCt, List.length_replicate] at ht
    rw [hCt, List.drop_replicate] at hc
    obtain ⟨p1, p2, p3, p4⟩ := hP
    have hT' : MulTmpl N K w' :=
      hin.tm.of_writes fun r hr => hfr r (chBody_writes_ge r hr) (by intro e; subst e; simp at hr)
    have fKc : w' rKc = List.replicate g false := by rw [hfr _ (by decide) (by decide), hin.kc]
    have fTb : w' rTb = List.replicate b false := by rw [hfr _ (by decide) (by decide), hin.tb]
    have fBlk : w' rTBlk = List.replicate (16 * K ^ 3 * (N * K)) false := by
      rw [hfr _ (by decide) (by decide), hin.blk]
    have fJ : w' rJ = encRM N K (j : Rq N K) := by rw [hfr _ (by decide) (by decide), hin.jw]
    have hT : MulTmpl N K (Function.update w' rCt (w' rCt).tail) :=
      hT'.of_writes fun r hr => Function.update_of_ne (by intro e; subst e; simp at hr) _ _
    have h4K := hT'.t4KNK
    have l4K : (w' rT4KNK).length = 2 * (2 * K) * (N * K) := by rw [h4K]; simp
    rw [drop_range_succ ht] at p2 p3
    simp only [aautL, hL, List.flatMap_cons] at p2 p3
    unfold chBody
    rw [exec_seq, exec_seq]
    set w1 := exec N K chPre (Function.update w' rCt (w' rCt).tail) with hw1
    have hT1 : MulTmpl N K w1 := hT.of_writes fun r hr => by
      rw [hw1, exec_writes _ _ _ (by revert r hr; decide)]
    have q1 : w1 rS2 = encRM N K (binaryDigit (j : Rq N K) t) := by
      rw [hw1]; unfold chPre; vm_simp
      simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, fTb, fJ, hc,
        takeD_encRM, List.length_drop, List.length_tail, List.length_replicate]
      rw [show b - 1 - (b - t - 1) = t by omega, canonW_dig hK]
    have q2 : w1 rGX = encL N K (matL (Hf t)) := by
      rw [hw1]; unfold chPre; vm_simp
      simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, p3, l4K]
      rw [h4K, shiftIn_encL' _ _ (by simp), List.append_assoc, encL_append,
        takeD_encL' _ _ (by simp; ring)]
    have q3 : w1 rHs = encL N K (hL Hf Hi ((List.range b).drop (t + 1))) := by
      rw [hw1]; unfold chPre; vm_simp
      simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, p3, l4K, List.drop_drop, hL]
      rw [encL_append, encL_append, List.append_assoc, show 2 * (2 * K) * (N * K) +
        2 * (2 * K) * (N * K) = 2 * (2 * K) * (N * K) + 2 * (2 * K) * (N * K) from rfl,
        ← List.drop_drop, drop_encL' _ _ (by simp; ring), drop_encL' _ _ (by simp; ring)]
    have q4 : w1 rMA = encL N K (matL (chainM g Hf Aa t j B)) := by
      rw [hw1]; unfold chPre; vm_simp; simp [p1]
    have q5 : w1 rSs = encL N K (adL (Aa t) ++ aautL Aa ((List.range b).drop (t + 1))) := by
      rw [hw1]; unfold chPre; vm_simp; simp [p2, aautL]
    have q6 : w1 rPw2 = List.replicate (2 ^ t) false := by
      rw [hw1]; unfold chPre; vm_simp; simp [p4]
    have q7 : w1 rKc = List.replicate g false := by
      rw [hw1]; unfold chPre; vm_simp; simp [fKc]
    have q8 : w1 rTBlk = List.replicate (16 * K ^ 3 * (N * K)) false := by
      rw [hw1]; unfold chPre; vm_simp; simp [fBlk]
    rw [exec_ifb, q1, hd_dig_natCast hN hK j t hj]
    by_cases hbit : j.testBit t
    · rw [if_pos hbit]
      unfold autStep
      rw [exec_seq, exec_seq, exec_seq]
      set w2 := exec N K (.cp rP rPw2) (exec N K (.cp rMAd rSs) w1) with hw2
      have hT2 : MulTmpl N K w2 := hT1.of_writes fun r hr => by
        rw [hw2]; vm_simp
        rw [Function.update_of_ne (by intro e; subst e; simp at hr),
          Function.update_of_ne (by intro e; subst e; simp at hr)]
      obtain ⟨a1, a2⟩ := exec_autPKC hN hK w2 (chainM g Hf Aa t j B) (Hf t) (Aa t)
        (aautL Aa ((List.range b).drop (t + 1))) (by rw [hw2]; vm_simp; simp [q4])
        (by rw [hw2]; vm_simp; simp [q5]) (by rw [hw2]; vm_simp; simp [q2])
        (by rw [hw2]; vm_simp; simp [q7]; omega) hT2
      have e1 : w2 rP = List.replicate (2 ^ t) false := by rw [hw2]; vm_simp; simp [q6]
      have e2 : w2 rKc = List.replicate g false := by rw [hw2]; vm_simp; simp [q7]
      rw [e1, e2, List.length_replicate, List.length_replicate] at a1
      have f6 : exec N K autPKC w2 rPw2 = List.replicate (2 ^ t) false := by
        rw [exec_writes _ _ _ (autPKC_writes_low _ (by decide)), hw2]; vm_simp; simp [q6]
      have f3 : exec N K autPKC w2 rHs = encL N K (hL Hf Hi ((List.range b).drop (t + 1))) := by
        rw [exec_writes _ _ _ (autPKC_writes_low _ (by decide)), hw2]; vm_simp; simp [q3]
      vm_simp
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, a1, chainM_succ, hbit]; rfl
      · simp [a2]
      · simp [f3]
      · simp [f6, pow_succ, mul_two]
    · rw [if_neg hbit]
      vm_simp
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, q4, chainM_succ, hbit]; rfl
      · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, q5, q8, List.length_replicate]
        rw [encL_append, drop_encL' _ _ (length_adL _)]
      · simp [q3]
      · simp [q6, pow_succ, mul_two]

end AdvancedEncryption.ExpLUT.Prog
