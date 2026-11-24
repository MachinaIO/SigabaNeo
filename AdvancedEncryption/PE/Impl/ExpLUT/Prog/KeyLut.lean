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
structure ChainIn (w : St) (g b : ℕ) (Hf Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K)
    (Aa : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) : Prop where
  kc : w rKc = List.replicate g false
  aw : w rAautW = encL N K (aautL Aa (List.range b))
  hw : w rHW = encL N K (hL Hf Hi (List.range b))
  bit1 : w rBit1 = [false]
  tb : w rTb = List.replicate b false
  blk : w rTBlk = List.replicate (16 * K ^ 3 * (N * K)) false
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
    (hin : ChainIn w g b Hf Hi Aa) (hJ : w rJ = encRM N K (j : Rq N K))
    (hMA : w rMA = encL N K (matL B))
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
    have fJ : w' rJ = encRM N K (j : Rq N K) := by rw [hfr _ (by decide) (by decide), hJ]
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

theorem chainC_writes : ∀ r : Fin 64, chainC.writes r = true →
    r = rSs ∨ r = rHs ∨ r = rPw2 ∨ r = rCt ∨ 29 ≤ r.val ∧ r.val < 57 := by decide

theorem ChainIn.of_writes {w w' : St} {g b : ℕ} {Hf Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K}
    {Aa : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K} (h : ChainIn w g b Hf Hi Aa)
    (hw : ∀ r : Fin 64, (r.val < 29 ∨ r = rKc ∨ 57 ≤ r.val) → r ≠ rSs → r ≠ rHs → r ≠ rPw2 →
      r ≠ rCt → w' r = w r) : ChainIn w' g b Hf Hi Aa :=
  ⟨by rw [hw _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.kc,
   by rw [hw _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.aw,
   by rw [hw _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.hw,
   by rw [hw _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.bit1,
   by rw [hw _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.tb,
   by rw [hw _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.blk,
   h.tm.of_writes fun r hr => hw r (Or.inr (Or.inr hr)) (by intro e; subst e; simp at hr)
     (by intro e; subst e; simp at hr) (by intro e; subst e; simp at hr)
     (by intro e; subst e; simp at hr)⟩

/-- **`chainC` computes `A_j`** from `B` in `rMA`. -/
theorem exec_chainC (hN : 0 < N) (hK : 0 < K) (w : St) (g b j : ℕ) (hg : 0 < g)
    (hj : j < 2 ^ K - 1) (Hf Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K)
    (Aa : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (B : Fin 2 → Fin 2 × Fin K → Rq N K)
    (hin : ChainIn w g b Hf Hi Aa) (hJ : w rJ = encRM N K (j : Rq N K))
    (hMA : w rMA = encL N K (matL B)) :
    exec N K chainC w rMA = encL N K (matL (chainM g Hf Aa b j B)) := by
  unfold chainC
  rw [exec_seq, exec_seq, exec_seq, exec_seq]
  set w1 := exec N K (.cp rCt rTb) (exec N K (.cp rPw2 rBit1) (exec N K (.cp rHs rHW)
    (exec N K (.cp rSs rAautW) w))) with hw1
  have hin1 : ChainIn w1 g b Hf Hi Aa := hin.of_writes fun r _ h1 h2 h3 h4 => by
    rw [hw1]; vm_simp
    rw [Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2,
      Function.update_of_ne h1]
  exact exec_chainLoop hN hK w1 g b j hg hj Hf Hi Aa B hin1 (by rw [hw1]; vm_simp; simp [hJ])
    (by rw [hw1]; vm_simp; simp [hMA]) (by rw [hw1]; vm_simp; simp [hin.aw])
    (by rw [hw1]; vm_simp; simp [hin.hw]) (by rw [hw1]; vm_simp; simp [hin.bit1])
    (by rw [hw1]; vm_simp; simp [hin.tb])

/-! ### The table: the loop over `j` -/

/-- The registers the `j` loop only reads: the caller's registers but `rAcc`, `rJ`, `rMu`,
`rCj2`, `rAl`, `rSs`, `rHs`, `rCt`, `rPw2`, and `rKc`, the templates `57 … 63`. -/
def roJ (r : Fin 64) : Bool :=
  (decide (r.val < 29) && !([5, 6, 7, 9, 11, 12, 13, 14, 15] : List ℕ).contains r.val) ||
    r == rKc || decide (57 ≤ r.val)

/-- One `j`: the coefficient (`cf`, into `rAl`), `A_j`, `rAcc += A_j G⁻¹(α G)`, `μ := σ_g(μ)`,
`j := j + 1`. -/
def jBodyK (cf : Code) : Code :=
  .seq cf <| .seq (.cp rMA rB) <| .seq chainC <| .seq (.cp rGX rMA) <| .seq agC <|
  .seq ginvMulC <| .seq matAddC <| .seq (.op .aut rMu rMu rKc) (.op .add rJ rJ rOne)

/-- A coefficient routine: writes `rAl` and the scratch registers `35 … 40` only. -/
def CoefW (cf : Code) : Prop := ∀ r : Fin 64, cf.writes r = true → r = rAl ∨ (35 ≤ r.val ∧ r.val ≤ 40)

theorem jBodyK_writes (cf : Code) (hcf : CoefW cf) :
    ∀ r : Fin 64, roJ r = true → (jBodyK cf).writes r = false := by
  intro r hr
  have h1 : cf.writes r = false := by
    by_contra h
    rcases hcf r (by simpa using h) with e | ⟨a, b⟩
    · subst e; simp [roJ] at hr
    · have key : ∀ r : Fin 64, 35 ≤ r.val → r.val ≤ 40 → roJ r = false := by decide
      rw [key r a b] at hr; exact absurd hr (by simp)
  have h2 : ∀ r : Fin 64, roJ r = true → (jBodyK .nop).writes r = false := by decide
  have := h2 r hr
  simp only [jBodyK, Code.writes, Bool.or_eq_false_iff] at this ⊢
  exact ⟨h1, this.2⟩

theorem ChainIn.of_roJ {w w' : St} {g b : ℕ} {Hf Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K}
    {Aa : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K} (h : ChainIn w g b Hf Hi Aa)
    (hw : ∀ r : Fin 64, roJ r = true → w' r = w r) : ChainIn w' g b Hf Hi Aa :=
  ⟨by rw [hw _ (by decide)]; exact h.kc, by rw [hw _ (by decide)]; exact h.aw,
   by rw [hw _ (by decide)]; exact h.hw, by rw [hw _ (by decide)]; exact h.bit1,
   by rw [hw _ (by decide)]; exact h.tb, by rw [hw _ (by decide)]; exact h.blk,
   h.tm.of_writes fun r hr => hw r (by simp [roJ, hr])⟩

/-- A code that never writes the registers of `roJ` keeps them. -/
theorem roJ_frame (c : Code) (hc : ∀ r : Fin 64, roJ r = true → c.writes r = false) {w w0 : St}
    (h : ∀ r : Fin 64, roJ r = true → w r = w0 r) :
    ∀ r : Fin 64, roJ r = true → exec N K c w r = w0 r :=
  fun r hr => by rw [exec_writes _ _ _ (hc r hr), h r hr]

theorem CoefW.frame {cf : Code} (hcf : CoefW cf) (w : St) (r : Fin 64) (h1 : r ≠ rAl)
    (h2 : r.val < 35 ∨ 40 < r.val) : exec N K cf w r = w r := by
  refine exec_writes _ _ _ ?_
  by_contra h
  rcases hcf r (by simpa using h) with e | ⟨a, b⟩
  · exact h1 e
  · omega

theorem CoefW.ro {cf : Code} (hcf : CoefW cf) : ∀ r : Fin 64, roJ r = true → cf.writes r = false := by
  intro r hr
  by_contra h
  rcases hcf r (by simpa using h) with e | ⟨a, b⟩
  · subst e; simp [roJ] at hr
  · have key : ∀ r : Fin 64, 35 ≤ r.val → r.val ≤ 40 → roJ r = false := by decide
    rw [key r a b] at hr; exact absurd hr (by simp)

/-- The table after `n` values of `j`: `Σ_{j<n} A_j G⁻¹(α_j G)`, `α_j = cv(σ_g^{j}(μ₀))`. -/
def accM (cv : Rq N K → Rq N K) (g : ℕ) (Hf : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K)
    (Aa : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (b : ℕ)
    (B : Fin 2 → Fin 2 × Fin K → Rq N K) (μ0 : Rq N K) (n : ℕ) : Fin 2 → Fin 2 × Fin K → Rq N K :=
  ∑ j ∈ Finset.range n, ginvMulm (chainM g Hf Aa b j B) (gM (cv ((aut N g)^[j] μ0)))

theorem jBodyK_writes_rCj2 (cf : Code) (hcf : CoefW cf) : (jBodyK cf).writes rCj2 = false := by
  have h1 : cf.writes rCj2 = false := by
    cases hw : cf.writes rCj2
    · rfl
    · rcases hcf _ hw with e | ⟨a, b⟩
      · exact absurd e (by decide)
      · simp at a
  have h2 : (jBodyK .nop).writes rCj2 = false := by decide
  simp only [jBodyK, Code.writes, Bool.or_eq_false_iff] at h2 ⊢
  exact ⟨h1, h2.2⟩

/-- **The loop over `j`**: `rAcc := Σ_{j<n} A_j G⁻¹(α_j G)`. -/
theorem exec_jLoopK (hN : 0 < N) (hK : 0 < K) (cf : Code) (hcfw : CoefW cf)
    (cv : Rq N K → Rq N K) (w : St)
    (hcf : ∀ w' : St, (∀ r : Fin 64, roJ r = true → w' r = w r) → ∀ μ : Rq N K,
      w' rMu = encRM N K μ → exec N K cf w' rAl = encRM N K (cv μ))
    (g b n : ℕ) (hg : 0 < g) (hn : n ≤ 2 ^ K - 1) (Hf Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K)
    (Aa : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (B : Fin 2 → Fin 2 × Fin K → Rq N K)
    (μ0 : Rq N K) (hin : ChainIn w g b Hf Hi Aa) (hB : w rB = encL N K (matL B))
    (hO : w rOne = encRM N K 1) (h4K : w rT4K = List.replicate (4 * K) false)
    (hAcc : w rAcc = encL N K (matL (fun _ _ => 0))) (hJ : w rJ = encRM N K 0)
    (hMu : w rMu = encRM N K μ0) (hC : w rCj2 = List.replicate n false) :
    exec N K (.rep rCj2 (jBodyK cf)) w rAcc = encL N K (matL (accM cv g Hf Aa b B μ0 n)) := by
  have key := exec_rep_inv2 (N := N) (K := K) rCj2 (jBodyK cf) (jBodyK_writes_rCj2 cf hcfw)
    (fun j w' => w' rAcc = encL N K (matL (accM cv g Hf Aa b B μ0 j)) ∧
      w' rJ = encRM N K (j : Rq N K) ∧ w' rMu = encRM N K ((aut N g)^[j] μ0)) w
    ⟨by simp only [accM, Finset.sum_range_zero]; exact hAcc, by simpa using hJ,
      by simpa using hMu⟩ ?_
  · rw [hC, List.length_replicate] at key
    exact key.1
  · intro j w' hj hP _ hfr
    rw [hC, List.length_replicate] at hj
    obtain ⟨p1, p2, p3⟩ := hP
    generalize hW0 : Function.update w' rCj2 (w' rCj2).tail = W0
    have f0 : ∀ r : Fin 64, roJ r = true → W0 r = w r := fun r hr => by
      have hr' : r ≠ rCj2 := by intro e; subst e; simp [roJ] at hr
      rw [← hW0, Function.update_of_ne hr', hfr r (jBodyK_writes cf hcfw r hr) hr']
    have q1 : W0 rAcc = encL N K (matL (accM cv g Hf Aa b B μ0 j)) := by
      rw [← hW0, Function.update_of_ne (by decide), p1]
    have q2 : W0 rJ = encRM N K (j : Rq N K) := by rw [← hW0, Function.update_of_ne (by decide), p2]
    have q3 : W0 rMu = encRM N K ((aut N g)^[j] μ0) := by
      rw [← hW0, Function.update_of_ne (by decide), p3]
    unfold jBodyK
    simp only [exec_seq]
    -- the coefficient
    generalize hW1 : exec N K cf W0 = W1
    have c1 : W1 rAl = encRM N K (cv ((aut N g)^[j] μ0)) := hW1 ▸ hcf W0 f0 _ q3
    have g1 : ∀ r : Fin 64, roJ r = true → W1 r = w r :=
      hW1 ▸ roJ_frame (N := N) (K := K) cf hcfw.ro f0
    have a1 : W1 rAcc = W0 rAcc := hW1 ▸ hcfw.frame _ _ (by decide) (by decide)
    have j1 : W1 rJ = W0 rJ := hW1 ▸ hcfw.frame _ _ (by decide) (by decide)
    have m1 : W1 rMu = W0 rMu := hW1 ▸ hcfw.frame _ _ (by decide) (by decide)
    -- `A_j`
    generalize hW2 : exec N K (.cp rMA rB) W1 = W2
    have g2 : ∀ r : Fin 64, roJ r = true → W2 r = w r :=
      hW2 ▸ roJ_frame (N := N) (K := K) (.cp rMA rB) (by decide) g1
    have c2 : W2 rMA = encL N K (matL B) := by rw [← hW2]; vm_simp; simp [g1 rB (by decide), hB]
    have j2 : W2 rJ = encRM N K (j : Rq N K) := by rw [← hW2]; vm_simp; simp [j1, q2]
    have w2 : ∀ r : Fin 64, (r = rAl ∨ r = rAcc ∨ r = rJ ∨ r = rMu) → W2 r = W1 r := by
      intro r hr
      rw [← hW2, exec_cp, Function.update_of_ne (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]
    generalize hW3 : exec N K chainC W2 = W3
    have c3 : W3 rMA = encL N K (matL (chainM g Hf Aa b j B)) :=
      hW3 ▸ exec_chainC hN hK W2 g b j hg (by omega) Hf Hi Aa B (hin.of_roJ g2) j2 c2
    have g3 : ∀ r : Fin 64, roJ r = true → W3 r = w r :=
      hW3 ▸ roJ_frame (N := N) (K := K) chainC (by decide) g2
    have w3 : ∀ r : Fin 64, (r = rAl ∨ r = rAcc ∨ r = rJ ∨ r = rMu) → W3 r = W1 r := by
      intro r hr
      rw [← hW3, exec_writes _ _ _ (by rcases hr with rfl | rfl | rfl | rfl <;> decide), w2 r hr]
    -- `α G`, `A_j G⁻¹(α G)`
    generalize hW4 : exec N K (.cp rGX rMA) W3 = W4
    have g4 : ∀ r : Fin 64, roJ r = true → W4 r = w r :=
      hW4 ▸ roJ_frame (N := N) (K := K) (.cp rGX rMA) (by decide) g3
    have w4 : ∀ r : Fin 64, (r = rAl ∨ r = rAcc ∨ r = rJ ∨ r = rMu) → W4 r = W1 r := by
      intro r hr
      rw [← hW4, exec_cp, Function.update_of_ne (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
        w3 r hr]
    have x4 : W4 rGX = encL N K (matL (chainM g Hf Aa b j B)) := by
      rw [← hW4]; vm_simp; simp [c3]
    generalize hW5 : exec N K agC W4 = W5
    have c5 : W5 rMA = encL N K (matL (gM (cv ((aut N g)^[j] μ0)))) :=
      hW5 ▸ exec_agC hK W4 _ (by rw [w4 rAl (by decide), c1])
        (hin.tm.of_writes fun r hr => g4 r (by simp [roJ, hr]))
    have g5 : ∀ r : Fin 64, roJ r = true → W5 r = w r :=
      hW5 ▸ roJ_frame (N := N) (K := K) agC (by decide) g4
    have x5 : W5 rGX = encL N K (matL (chainM g Hf Aa b j B)) := by
      rw [← hW5, exec_writes _ _ _ (by decide), x4]
    have w5 : ∀ r : Fin 64, (r = rAcc ∨ r = rJ ∨ r = rMu) → W5 r = W1 r := by
      intro r hr
      rw [← hW5, exec_writes _ _ _ (by rcases hr with rfl | rfl | rfl <;> decide),
        w4 r (by tauto)]
    generalize hW6 : exec N K ginvMulC W5 = W6
    have c6 : W6 rMOut = encL N K (matL (ginvMulm (chainM g Hf Aa b j B)
        (gM (cv ((aut N g)^[j] μ0))))) :=
      hW6 ▸ exec_ginvMulC hK W5 _ _ x5 c5 (hin.tm.of_writes fun r hr => g5 r (by simp [roJ, hr]))
    have g6 : ∀ r : Fin 64, roJ r = true → W6 r = w r :=
      hW6 ▸ roJ_frame (N := N) (K := K) ginvMulC (by decide) g5
    have w6 : ∀ r : Fin 64, (r = rAcc ∨ r = rJ ∨ r = rMu) → W6 r = W1 r := by
      intro r hr
      rw [← hW6, exec_writes _ _ _ (by rcases hr with rfl | rfl | rfl <;> decide), w5 r hr]
    -- `rAcc += …`
    generalize hW7 : exec N K matAddC W6 = W7
    have c7 := exec_matAddC hK W6 (matL (accM cv g Hf Aa b B μ0 j))
      (matL (ginvMulm (chainM g Hf Aa b j B) (gM (cv ((aut N g)^[j] μ0))))) (4 * K)
      (by simp) (by simp)
      (by rw [w6 _ (by decide), a1, q1]) c6
      (by rw [g6 _ (by decide), h4K]) (by rw [g6 _ (by decide), hin.tm.z])
    rw [hW7] at c7
    have w7 : ∀ r : Fin 64, (r = rJ ∨ r = rMu) → W7 r = W1 r := by
      intro r hr
      rw [← hW7, exec_writes _ _ _ (by rcases hr with rfl | rfl <;> decide), w6 r (by tauto)]
    have g7 : ∀ r : Fin 64, roJ r = true → W7 r = w r :=
      hW7 ▸ roJ_frame (N := N) (K := K) matAddC (by decide) g6
    vm_simp
    refine ⟨?_, ?_, ?_⟩
    · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]
      rw [c7, ← matL_add hK]
      congr 2
      funext a c
      simp [accM, Finset.sum_range_succ]
    · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, w7 rJ (by decide), j1, q2,
        g7 rOne (by decide), hO, takeD_encRM, canonW_add hK, Nat.cast_succ]
    · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, w7 rMu (by decide), m1, q3,
        takeD_encRM, g7 rKc (by decide), hin.kc, List.length_replicate]
      rw [canonW_aut hK hN hg, Function.iterate_succ_apply']

/-! ### One step: `Mul` by `A^in_i`, then the table -/

theorem matL_zero : matL (fun _ _ => (0 : Rq N K)) = List.replicate (2 * (2 * K)) 0 := by
  rw [matL, enum_fin2]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_const',
    length_enum_col, List.replicate_append_replicate]
  congr 1; ring

/-- The registers a coefficient routine reads. -/
def roC (r : Fin 64) : Bool := ([3, 18, 20, 21, 22, 23, 24, 63] : List ℕ).contains r.val

theorem roJ_of_roC : ∀ r : Fin 64, roC r = true → roJ r = true := by decide

/-- Before the loop over `j`: `rB := mulPK(rA, A^in_i)`, the accumulator, `j`, `μ`. -/
def stepPre : Code :=
  .seq (.cp rMA rA) <| .seq (.cp rMAd rAinS) <| .seq mulPKC <| .seq (.cp rAinS rMAd) <|
  .seq (.cp rB rMOut) <| .seq (.cp rAcc rT4KNK) <| .seq (.cp rJ rZ) <| .seq (.cp rMu rMu0)
    (.cp rCj2 rTW)

/-- **One step** with the coefficient routine `cf`: `rA := LUT(mulPK(rA, A^in_i))`, the table
stream advanced by `|rTtab|` bits. -/
def stepK (cf : Code) : Code :=
  .seq stepPre <| .seq (.rep rCj2 (jBodyK cf)) <| .seq (.cp rA rAcc) (.drop rCs rTtab)

/-- The registers of a step (read only). -/
structure StepIn (w : St) (g b n tl : ℕ) (Hf Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K)
    (Aa : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (μ0 : Rq N K) : Prop where
  ch : ChainIn w g b Hf Hi Aa
  one : w rOne = encRM N K 1
  mu0 : w rMu0 = encRM N K μ0
  t4K : w rT4K = List.replicate (4 * K) false
  tw : w rTW = List.replicate n false
  ttab : w rTtab = List.replicate tl false

/-- The registers no step writes. -/
def roS (r : Fin 64) : Bool := ([1, 2, 10, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 31,
  57, 58, 59, 60, 61, 62, 63] : List ℕ).contains r.val

theorem StepIn.of_roS {w w' : St} {g b n tl : ℕ} {Hf Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K}
    {Aa : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K} {μ0 : Rq N K}
    (h : StepIn w g b n tl Hf Hi Aa μ0) (hw : ∀ r : Fin 64, roS r = true → r ≠ rCst → w' r = w r) :
    StepIn w' g b n tl Hf Hi Aa μ0 :=
  ⟨⟨by rw [hw _ (by decide) (by decide)]; exact h.ch.kc,
    by rw [hw _ (by decide) (by decide)]; exact h.ch.aw,
    by rw [hw _ (by decide) (by decide)]; exact h.ch.hw,
    by rw [hw _ (by decide) (by decide)]; exact h.ch.bit1,
    by rw [hw _ (by decide) (by decide)]; exact h.ch.tb,
    by rw [hw _ (by decide) (by decide)]; exact h.ch.blk,
    h.ch.tm.of_writes fun r hr => hw r (by revert r; decide) (by intro e; subst e; simp at hr)⟩,
   by rw [hw _ (by decide) (by decide)]; exact h.one, by rw [hw _ (by decide) (by decide)]; exact h.mu0,
   by rw [hw _ (by decide) (by decide)]; exact h.t4K, by rw [hw _ (by decide) (by decide)]; exact h.tw,
   by rw [hw _ (by decide) (by decide)]; exact h.ttab⟩

theorem stepK_writes (cf : Code) (hcf : CoefW cf) : ∀ r : Fin 64, roS r = true →
    (stepK cf).writes r = false := by
  intro r hr
  have h1 : cf.writes r = false := by
    cases hw : cf.writes r
    · rfl
    · rcases hcf r hw with e | ⟨a, b⟩
      · subst e; exact absurd hr (by decide)
      · have key : ∀ r : Fin 64, 35 ≤ r.val → r.val ≤ 40 → roS r = false := by decide
        rw [key r a b] at hr; exact absurd hr (by simp)
  have h2 : ∀ r : Fin 64, roS r = true → (stepK .nop).writes r = false := by decide
  have := h2 r hr
  simp only [stepK, jBodyK, Code.writes, Bool.or_eq_false_iff] at this ⊢
  exact ⟨this.1, ⟨⟨this.2.1.1, h1, this.2.1.2.2⟩, this.2.2⟩⟩

/-- **One step**: `rA := Σ_{j<n} A_j G⁻¹(α_j G)` for `B = mulPK(rA, A^in_i)`. -/
theorem exec_stepK (hN : 0 < N) (hK : 0 < K) (cf : Code) (hcfw : CoefW cf)
    (cv : Rq N K → Rq N K) (w : St)
    (hcf : ∀ w' : St, (∀ r : Fin 64, roC r = true → w' r = w r) → ∀ μ : Rq N K,
      w' rMu = encRM N K μ → exec N K cf w' rAl = encRM N K (cv μ))
    (g b n tl : ℕ) (hg : 0 < g) (hn : n ≤ 2 ^ K - 1) (Hf Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K)
    (Aa : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (μ0 : Rq N K)
    (hin : StepIn w g b n tl Hf Hi Aa μ0) (A : Fin 2 → Fin 2 × Fin K → Rq N K)
    (Ad : DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (rest : List (Rq N K))
    (hA : w rA = encL N K (matL A)) (hS : w rAinS = encL N K (adL Ad ++ rest)) :
    exec N K (stepK cf) w rA = encL N K (matL (accM cv g Hf Aa b (mulPKm A Ad) μ0 n)) ∧
    exec N K (stepK cf) w rAinS = encL N K rest ∧
    exec N K (stepK cf) w rCs = (w rCs).drop tl := by
  unfold stepK
  simp only [exec_seq]
  generalize hW1 : exec N K stepPre w = W1
  have r1 : ∀ r : Fin 64, (roS r = true ∨ r = rCs) → W1 r = w r := by
    intro r hr
    have hw : stepPre.writes r = false := by
      rcases hr with hr | rfl
      · exact (by decide : ∀ r : Fin 64, roS r = true → stepPre.writes r = false) r hr
      · decide
    rw [← hW1, exec_writes _ _ _ hw]
  have hT := hin.ch.tm
  -- `mulPK`
  have hm : W1 rB = encL N K (matL (mulPKm A Ad)) ∧ W1 rAinS = encL N K rest ∧
      W1 rAcc = encL N K (matL (fun _ _ => 0)) ∧ W1 rJ = encRM N K 0 ∧
      W1 rMu = encRM N K μ0 ∧ W1 rCj2 = List.replicate n false := by
    rw [← hW1]
    unfold stepPre
    simp only [exec_seq]
    generalize hV : exec N K (.cp rMAd rAinS) (exec N K (.cp rMA rA) w) = V
    have hVMA : V rMA = encL N K (matL A) := by rw [← hV]; vm_simp; simp [hA]
    have hVMAd : V rMAd = encL N K (adL Ad ++ rest) := by rw [← hV]; vm_simp; simp [hS]
    have hVT : MulTmpl N K V := hT.of_writes fun r hr => by
      rw [← hV]; vm_simp
      rw [Function.update_of_ne (by intro e; subst e; simp at hr),
        Function.update_of_ne (by intro e; subst e; simp at hr)]
    obtain ⟨m1, m2⟩ := exec_mulPKC hK V A Ad rest hVMA hVMAd hVT
    have mT : MulTmpl N K (exec N K mulPKC V) :=
      hVT.of_writes fun r hr => exec_writes _ _ _ (mulPKC_writes_ge r hr)
    have m0 : exec N K mulPKC V rMu0 = encRM N K μ0 := by
      rw [exec_writes _ _ _ (by decide), ← hV]; vm_simp; simp [hin.mu0]
    have mW : exec N K mulPKC V rTW = List.replicate n false := by
      rw [exec_writes _ _ _ (by decide), ← hV]; vm_simp; simp [hin.tw]
    vm_simp
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, m1, m2, mT.t4KNK, mT.z, m0, mW,
      true_and]
    rw [matL_zero]; exact ⟨rfl, trivial⟩
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hm
  have hin1 : StepIn W1 g b n tl Hf Hi Aa μ0 := hin.of_roS fun r hr _ => r1 r (Or.inl hr)
  -- the loop over `j`
  generalize hW2 : exec N K (.rep rCj2 (jBodyK cf)) W1 = W2
  have l2 := exec_jLoopK hN hK cf hcfw cv W1
    (fun w' hw' μ hμ => hcf w' (fun r hr => by rw [hw' r (roJ_of_roC r hr),
      r1 r (by revert r; decide)]) μ hμ)
    g b n hg hn Hf Hi Aa (mulPKm A Ad) μ0 hin1.ch b1 hin1.one hin1.t4K b3 b4 b5 b6
  rw [hW2] at l2
  have s2 : W2 rAinS = encL N K rest := by
    rw [← hW2, exec_writes _ _ _ (by have := jBodyK_writes cf hcfw rAinS (by decide); simp [Code.writes, this]), b2]
  have c2 : W2 rCs = w rCs := by
    rw [← hW2, exec_writes _ _ _ (by have := jBodyK_writes cf hcfw rCs (by decide); simp [Code.writes, this]), r1 _ (Or.inr rfl)]
  have t2 : W2 rTtab = List.replicate tl false := by
    rw [← hW2, exec_writes _ _ _ (by have := jBodyK_writes cf hcfw rTtab (by decide); simp [Code.writes, this]), hin1.ttab]
  vm_simp
  refine ⟨?_, ?_, ?_⟩
  · simp [l2]
  · simp [s2]
  · simp [c2, t2]

/-! ### The coefficient routines of the steps -/

/-- The coefficient routine of an `α`-step (the table at the head of `rCs`). -/
def cfA : Code := .seq (.cp rCp rCs) coefAC

/-- The coefficient routine of the `v`-step. -/
def cfV : Code := .seq (.cp rCp rCs) coefVC

theorem coefW_cfA : CoefW cfA := by unfold CoefW; decide
theorem coefW_cfV : CoefW cfV := by unfold CoefW; decide

/-- The coefficient of an `α`-table `Cs` (entries of `e` bits, `n` entries). -/
noncomputable def cvA (e n b : ℕ) (xc : Rq N K) (Cs : List Bool) (μ : Rq N K) : Rq N K :=
  (2 : ZMod (2 ^ K - 1)) ^ (K - b) • (sumA Cs e n μ * xc)

/-- The coefficient of a `v`-table `Cs`. -/
noncomputable def cvV (n b : ℕ) (Cs : List Bool) (μ : Rq N K) : Rq N K :=
  (2 : ZMod (2 ^ K - 1)) ^ (K - b) • sumV Cs n μ

/-- The templates of the coefficient routines. -/
structure CoefIn (w : St) (e n b : ℕ) (xc : Rq N K) : Prop where
  one : w rOne = encRM N K 1
  xc : w rXc = encRM N K xc
  bit1 : w rBit1 = [false]
  te : w rTe = List.replicate e false
  tw : w rTW = List.replicate n false
  tb : w rTb = List.replicate b false
  z : w rZ = encRM N K 0

theorem hcf_cfA (hN : 0 < N) (hK : 0 < K) (w : St) (e n b : ℕ) (hb : b ≤ K) (xc : Rq N K)
    (hw : CoefIn w e n b xc) :
    ∀ w' : St, (∀ r : Fin 64, roC r = true → w' r = w r) → ∀ μ : Rq N K,
      w' rMu = encRM N K μ → exec N K cfA w' rAl = encRM N K (cvA e n b xc (w rCs) μ) := by
  intro w' hw' μ hμ
  rw [cfA, exec_seq]
  exact (exec_coefAC hN hK _ e n b hb (w rCs) μ xc (by vm_simp; simp [hw' rCs (by decide)])
    (by vm_simp; simp [hμ]) (by vm_simp; simp [hw' rOne (by decide), hw.one])
    (by vm_simp; simp [hw' rXc (by decide), hw.xc]) (by vm_simp; simp [hw' rBit1 (by decide), hw.bit1])
    (by vm_simp; simp [hw' rTe (by decide), hw.te]) (by vm_simp; simp [hw' rTW (by decide), hw.tw])
    (by vm_simp; simp [hw' rTb (by decide), hw.tb]) (by vm_simp; simp [hw' rZ (by decide), hw.z])).1

theorem hcf_cfV (hK : 0 < K) (w : St) (e n b : ℕ) (hb : b ≤ K) (xc : Rq N K)
    (hw : CoefIn w e n b xc) :
    ∀ w' : St, (∀ r : Fin 64, roC r = true → w' r = w r) → ∀ μ : Rq N K,
      w' rMu = encRM N K μ → exec N K cfV w' rAl = encRM N K (cvV n b (w rCs) μ) := by
  intro w' hw' μ hμ
  rw [cfV, exec_seq]
  exact (exec_coefVC hK _ n b hb (w rCs) μ (by vm_simp; simp [hw' rCs (by decide)])
    (by vm_simp; simp [hμ]) (by vm_simp; simp [hw' rOne (by decide), hw.one])
    (by vm_simp; simp [hw' rTW (by decide), hw.tw]) (by vm_simp; simp [hw' rTb (by decide), hw.tb])
    (by vm_simp; simp [hw' rZ (by decide), hw.z])).1

/-! ### `EvalPK` -/

/-- **`EvalPK` of the VM**: `A_0`, then `T − 1` steps with `α`-tables (the tables of `tl` bits of
`C`, in order) and the last step with the `v`-table. -/
def evalC : Code := .seq (.cp rCst rT15) <| .seq (.rep rCst (stepK cfA)) (stepK cfV)

/-- The public matrices of `EvalPK` as computed by the VM (`cvs i` the coefficients of step `i`). -/
def evalVM (cvs : ℕ → Rq N K → Rq N K) (g : ℕ) (Hf : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K)
    (Aa : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (b : ℕ) (μ0 : Rq N K) (n : ℕ)
    (Ain : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (A0 : Fin 2 → Fin 2 × Fin K → Rq N K) :
    ℕ → Fin 2 → Fin 2 × Fin K → Rq N K
  | 0 => A0
  | i + 1 => accM (cvs i) g Hf Aa b (mulPKm (evalVM cvs g Hf Aa b μ0 n Ain A0 i) (Ain i)) μ0 n

/-- The stream of the digit matrices `A^in_i`, `i ∈ l`. -/
def ainL (Ain : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (l : List ℕ) : List (Rq N K) :=
  l.flatMap fun i => adL (Ain i)

theorem stepK_writes_roC (cf : Code) (hcf : CoefW cf) : ∀ r : Fin 64, roC r = true → r ≠ rCs →
    (stepK cf).writes r = false := by
  intro r hr hrc
  exact stepK_writes cf hcf r (by revert r; decide)

/-- **`evalC` computes `EvalPK`** (`T = 16`: 15 `α`-steps and the `v`-step). -/
theorem exec_evalC (hN : 0 < N) (hK : 0 < K) (w : St) (g b n tl e : ℕ) (hg : 0 < g)
    (hb : b ≤ K) (hn : n ≤ 2 ^ K - 1) (Hf Hi : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K)
    (Aa : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (μ0 xc : Rq N K)
    (hin : StepIn w g b n tl Hf Hi Aa μ0) (hco : CoefIn w e n b xc)
    (Ain : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (A0 : Fin 2 → Fin 2 × Fin K → Rq N K)
    (C : List Bool) (hA : w rA = encL N K (matL A0))
    (hS : w rAinS = encL N K (ainL Ain (List.range 16))) (hC : w rCs = C)
    (h15 : w rT15 = List.replicate 15 false) :
    exec N K evalC w rA = encL N K (matL (evalVM (fun i => if i < 15 then
      cvA e n b xc (C.drop (tl * i)) else cvV n b (C.drop (tl * 15))) g Hf Aa b μ0 n Ain A0 16)) := by
  set cvs : ℕ → Rq N K → Rq N K := fun i => if i < 15 then
      cvA e n b xc (C.drop (tl * i)) else cvV n b (C.drop (tl * 15)) with hcvs
  unfold evalC
  simp only [exec_seq]
  generalize hW1 : exec N K (.cp rCst rT15) w = W1
  have r1 : ∀ r : Fin 64, r ≠ rCst → W1 r = w r := fun r hr => by
    rw [← hW1, exec_cp, Function.update_of_ne hr]
  have key := exec_rep_inv2 (N := N) (K := K) rCst (stepK cfA)
    (stepK_writes cfA coefW_cfA rCst (by decide))
    (fun i w' => w' rA = encL N K (matL (evalVM cvs g Hf Aa b μ0 n Ain A0 i)) ∧
      w' rAinS = encL N K (ainL Ain ((List.range 16).drop i)) ∧ w' rCs = C.drop (tl * i)) W1
    ⟨by rw [r1 _ (by decide), hA]; rfl, by rw [r1 _ (by decide), hS]; rfl,
      by rw [r1 _ (by decide), hC]; simp⟩ ?_
  · have hc : (W1 rCst).length = 15 := by rw [← hW1]; vm_simp; simp [h15]
    rw [hc] at key
    obtain ⟨k1, k2, k3⟩ := key
    generalize hW2 : exec N K (.rep rCst (stepK cfA)) W1 = W2
    rw [hW2] at k1 k2 k3
    have f2 : ∀ r : Fin 64, roS r = true → r ≠ rCst → W2 r = w r := fun r hr hrc => by
      have hw : (Code.rep rCst (stepK cfA)).writes r = false := by
        simp only [Code.writes, stepK_writes cfA coefW_cfA r hr, Bool.or_false,
          beq_eq_false_iff_ne]
        exact Ne.symm hrc
      rw [← hW2, exec_writes _ _ _ hw, r1 r hrc]
    have hin2 := hin.of_roS f2
    rw [drop_range_succ (by norm_num : 15 < 16)] at k2
    simp only [ainL, List.flatMap_cons] at k2
    have hco2 : CoefIn W2 e n b xc :=
      ⟨by rw [f2 _ (by decide) (by decide), hco.one], by rw [f2 _ (by decide) (by decide), hco.xc],
        by rw [f2 _ (by decide) (by decide), hco.bit1], by rw [f2 _ (by decide) (by decide), hco.te],
        by rw [f2 _ (by decide) (by decide), hco.tw], by rw [f2 _ (by decide) (by decide), hco.tb],
        by rw [f2 _ (by decide) (by decide), hco.z]⟩
    have := (exec_stepK hN hK cfV coefW_cfV (cvV n b (W2 rCs)) W2 (hcf_cfV hK W2 e n b hb xc hco2)
      g b n tl hg hn Hf Hi Aa μ0 hin2 _ (Ain 15) _ k1 k2).1
    rw [this, k3]
    rfl
  · intro i w' hi hP _ hfr
    have hc : (W1 rCst).length = 15 := by rw [← hW1]; vm_simp; simp [h15]
    rw [hc] at hi
    obtain ⟨p1, p2, p3⟩ := hP
    generalize hW0 : Function.update w' rCst (w' rCst).tail = W0
    have f0 : ∀ r : Fin 64, roS r = true → r ≠ rCst → W0 r = w r := fun r hr hr' => by
      rw [← hW0, Function.update_of_ne hr', hfr r (stepK_writes cfA coefW_cfA r hr) hr',
        r1 r hr']
    have hin0 := hin.of_roS f0
    have hco0 : CoefIn W0 e n b xc :=
      ⟨by rw [f0 _ (by decide) (by decide), hco.one], by rw [f0 _ (by decide) (by decide), hco.xc],
        by rw [f0 _ (by decide) (by decide), hco.bit1], by rw [f0 _ (by decide) (by decide), hco.te],
        by rw [f0 _ (by decide) (by decide), hco.tw], by rw [f0 _ (by decide) (by decide), hco.tb],
        by rw [f0 _ (by decide) (by decide), hco.z]⟩
    have q1 : W0 rA = encL N K (matL (evalVM cvs g Hf Aa b μ0 n Ain A0 i)) := by
      rw [← hW0, Function.update_of_ne (by decide), p1]
    have q2 : W0 rAinS = encL N K (adL (Ain i) ++ ainL Ain ((List.range 16).drop (i + 1))) := by
      rw [← hW0, Function.update_of_ne (by decide), p2, drop_range_succ (by omega)]
      simp [ainL]
    have q3 : W0 rCs = C.drop (tl * i) := by rw [← hW0, Function.update_of_ne (by decide), p3]
    obtain ⟨s1, s2, s3⟩ := exec_stepK hN hK cfA coefW_cfA (cvA e n b xc (W0 rCs)) W0
      (hcf_cfA hN hK W0 e n b hb xc hco0) g b n tl hg hn Hf Hi Aa μ0 hin0 _ (Ain i) _ q1 q2
    refine ⟨?_, s2, ?_⟩
    · rw [s1, q3]
      show _ = encL N K (matL (accM (cvs i) g Hf Aa b _ μ0 n))
      rw [hcvs]
      simp only [if_pos (show i < 15 by omega)]
    · rw [s3, q3, List.drop_drop]
      congr 1

end AdvancedEncryption.ExpLUT.Prog
