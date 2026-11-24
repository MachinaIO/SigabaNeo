import PE.Impl.ExpLUT.Prog.KeyLut

/-!
# KeyGen (package F3): queue routines of the box try

VM routines on queues of canonical ring words, for the try of box rejection (after `EvalPK`, so
they use the registers `0 … 56` freely; the library templates `57 … 63` are kept):

* `ipC`: `rIa += Σ_{t<n} a_t b_t` from the streams `rQa`, `rQb` (`exec_ipC`);
* `autQC`: `σ_k` on the `n` words of the queue `rQa` (`exec_autQC`);
* `gadRecC`: `rIa += Σ_{j<n} 2^j a_j` from the stream `rQa` (`exec_gadRecC`).
-/

set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.MVM
  Cslib
open SigabaNeo.Lattices.Algo (encRM decRM)

/-- Registers of the queue routines. -/
@[simp, vmreg] abbrev rQa : Fin 64 := 50
@[simp, vmreg] abbrev rQb : Fin 64 := 51
@[simp, vmreg] abbrev rQc : Fin 64 := 52
@[simp, vmreg] abbrev rIa : Fin 64 := 53
@[simp, vmreg] abbrev rQx : Fin 64 := 54
@[simp, vmreg] abbrev rQy : Fin 64 := 55
@[simp, vmreg] abbrev rQk : Fin 64 := 49

variable {N K : ℕ}

theorem zipWith_take_succ {α : Type} (f : α → α → α) (l1 l2 : List α) {m : ℕ} (h1 : m < l1.length)
    (h2 : m < l2.length) :
    List.zipWith f (l1.take (m + 1)) (l2.take (m + 1)) =
      List.zipWith f (l1.take m) (l2.take m) ++ [f l1[m] l2[m]] := by
  rw [take_succ_getElem l1 h1, take_succ_getElem l2 h2, List.zipWith_append (by simp; omega)]
  rfl

/-! ### Inner products -/

/-- One product. -/
def ipBody : Code :=
  .seq (.cp rQx rZ) <| .seq (.mvR rQx rQa) <| .seq (.cp rQy rZ) <| .seq (.mvR rQy rQb) <|
  .seq (.op .mul rQx rQx rQy) (.op .add rIa rIa rQx)

/-- **`rIa += Σ_{t<n} a_t b_t`** (`n = |rQc|`). -/
def ipC : Code := .rep rQc ipBody

theorem ipBody_writes_rQc : ipBody.writes rQc = false := by decide

theorem exec_ipC (hK : 0 < K) (w : St) (la lb ra rb : List (Rq N K)) (n : ℕ) (acc : Rq N K)
    (h1 : la.length = n) (h2 : lb.length = n) (hA : w rQa = encL N K (la ++ ra))
    (hB : w rQb = encL N K (lb ++ rb)) (hC : w rQc = List.replicate n false)
    (hI : w rIa = encRM N K acc) (hZ : w rZ = encRM N K 0) :
    exec N K ipC w rIa = encRM N K (acc + (List.zipWith (· * ·) la lb).sum) ∧
    exec N K ipC w rQa = encL N K ra ∧ exec N K ipC w rQb = encL N K rb := by
  unfold ipC
  have key := exec_rep_inv2 (N := N) (K := K) rQc ipBody ipBody_writes_rQc
    (fun m w' => w' rQa = encL N K (la.drop m ++ ra) ∧ w' rQb = encL N K (lb.drop m ++ rb) ∧
      w' rIa = encRM N K (acc + (List.zipWith (· * ·) (la.take m) (lb.take m)).sum)) w
    ⟨by simp [hA], by simp [hB], by simp [hI]⟩ ?_
  · rw [hC, List.length_replicate] at key
    obtain ⟨k1, k2, k3⟩ := key
    refine ⟨?_, ?_, ?_⟩
    · rw [k3, List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    · rw [k1, List.drop_of_length_le (by omega)]; rfl
    · rw [k2, List.drop_of_length_le (by omega)]; rfl
  · intro m w' hm hP _ hfr
    rw [hC, List.length_replicate] at hm
    obtain ⟨p1, p2, p3⟩ := hP
    have hz : w' rZ = encRM N K 0 := by rw [hfr _ (by decide) (by decide), hZ]
    rw [drop_cons_getElem la (by omega), List.cons_append, encL_cons] at p1
    rw [drop_cons_getElem lb (by omega), List.cons_append, encL_cons] at p2
    unfold ipBody
    vm_simp
    refine ⟨?_, ?_, ?_⟩
    · simp [p1, hz]
    · simp [p2, hz]
    · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, p1, p2, p3, hz,
        shiftIn_encRM', takeD_encRM_append, takeD_encRM, canonW_mul hK, canonW_add hK]
      rw [zipWith_take_succ _ la lb (by omega) (by omega), List.sum_append, List.sum_singleton,
        add_assoc]

/-! ### `σ_k` on a queue -/

/-- One word: `σ_k` (`k = |rQk|`), to the tail. -/
def autQBody : Code := .seq (.cp rQx rZ) <| .seq (.mvR rQx rQa) <|
  .seq (.op .aut rQy rQx rQk) (.app rQa rQy)

/-- **`σ_k` on the `n` words of the queue `rQa`** (`n = |rQc|`, `k = |rQk|`). -/
def autQC : Code := .rep rQc autQBody

theorem autQBody_writes_rQc : autQBody.writes rQc = false := by decide

theorem exec_autQC (hN : 0 < N) (hK : 0 < K) (w : St) (l : List (Rq N K)) (n k : ℕ) (hk : 0 < k)
    (hl : l.length = n) (hA : w rQa = encL N K l) (hC : w rQc = List.replicate n false)
    (hQk : w rQk = List.replicate k false) (hZ : w rZ = encRM N K 0) :
    exec N K autQC w rQa = encL N K (l.map (aut N k)) := by
  unfold autQC
  have key := exec_rep_inv2 (N := N) (K := K) rQc autQBody autQBody_writes_rQc
    (fun m w' => w' rQa = encL N K (l.drop m ++ (l.take m).map (aut N k))) w
    (by simp [hA]) ?_
  · rw [hC, List.length_replicate] at key
    rw [key, List.drop_of_length_le (by omega), List.take_of_length_le (by omega)]; rfl
  · intro m w' hm hP _ hfr
    rw [hC, List.length_replicate] at hm
    have hz : w' rZ = encRM N K 0 := by rw [hfr _ (by decide) (by decide), hZ]
    have hq : w' rQk = List.replicate k false := by rw [hfr _ (by decide) (by decide), hQk]
    rw [drop_cons_getElem l (by omega), List.cons_append, encL_cons] at hP
    unfold autQBody
    vm_simp
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, hP, hz, hq, shiftIn_encRM',
      takeD_encRM_append, takeD_encRM, drop_encRM_append, List.length_replicate,
      canonW_aut hK hN hk]
    rw [take_succ_getElem l (by omega), List.map_append, ← List.append_assoc, encL_append,
      encL_append, encL_append]
    simp

/-! ### Gadget recomposition -/

/-- One digit: `rIa += pw · a`, `pw := 2 pw`. -/
def grBody : Code := .seq (.cp rQx rZ) <| .seq (.mvR rQx rQa) <| .seq (.op .mul rQx rQx rQy) <|
  .seq (.op .add rIa rIa rQx) (.op .add rQy rQy rQy)

/-- **`rIa += Σ_{j<n} 2^j a_j`** from the stream `rQa` (`n = |rQc|`, `rQy := 1` first). -/
def gadRecC (rOneW : Fin 64) : Code := .seq (.cp rQy rOneW) (.rep rQc grBody)

theorem grBody_writes_rQc : grBody.writes rQc = false := by decide

theorem exec_gadRecC (hK : 0 < K) (w : St) (rOneW : Fin 64) (hO1 : rOneW ≠ rQc)
    (la ra : List (Rq N K)) (n : ℕ) (acc : Rq N K) (h1 : la.length = n)
    (hA : w rQa = encL N K (la ++ ra)) (hC : w rQc = List.replicate n false)
    (hI : w rIa = encRM N K acc) (hZ : w rZ = encRM N K 0) (hO : w rOneW = encRM N K 1) :
    exec N K (gadRecC rOneW) w rIa =
      encRM N K (acc + ∑ j ∈ Finset.range n, 2 ^ j * la.getD j 0) ∧
    exec N K (gadRecC rOneW) w rQa = encL N K ra := by
  unfold gadRecC
  rw [exec_seq]
  generalize hW1 : exec N K (.cp rQy rOneW) w = W1
  have e1 : ∀ r : Fin 64, r ≠ rQy → W1 r = w r := fun r hr => by
    rw [← hW1, exec_cp, Function.update_of_ne hr]
  have key := exec_rep_inv2 (N := N) (K := K) rQc grBody grBody_writes_rQc
    (fun m w' => w' rQa = encL N K (la.drop m ++ ra) ∧ w' rQy = encRM N K (2 ^ m) ∧
      w' rIa = encRM N K (acc + ∑ j ∈ Finset.range m, 2 ^ j * la.getD j 0)) W1
    ⟨by rw [e1 _ (by decide), hA]; simp, by rw [← hW1]; vm_simp; simp [hO],
      by rw [e1 _ (by decide), hI]; simp⟩ ?_
  · have hc : (W1 rQc).length = n := by rw [e1 _ (by decide), hC, List.length_replicate]
    rw [hc] at key
    refine ⟨key.2.2, ?_⟩
    rw [key.1, List.drop_of_length_le (by omega)]; rfl
  · intro m w' hm hP _ hfr
    have hc : (W1 rQc).length = n := by rw [e1 _ (by decide), hC, List.length_replicate]
    rw [hc] at hm
    obtain ⟨p1, p2, p3⟩ := hP
    have hz : w' rZ = encRM N K 0 := by
      rw [hfr _ (by decide) (by decide), e1 _ (by decide), hZ]
    rw [drop_cons_getElem la (by omega), List.cons_append, encL_cons] at p1
    unfold grBody
    vm_simp
    refine ⟨?_, ?_, ?_⟩
    · simp [p1, hz]
    · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, p2, takeD_encRM, canonW_add hK]
      rw [pow_succ]; congr 1; ring
    · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, p1, p2, p3, hz, shiftIn_encRM',
        takeD_encRM_append, takeD_encRM, canonW_mul hK, canonW_add hK]
      rw [Finset.sum_range_succ, List.getD_eq_getElem _ _ (by omega), add_assoc]
      congr 2; ring

/-! ### The test of the small box -/

@[simp, vmreg] abbrev rTx : Fin 64 := 48
@[simp, vmreg] abbrev rRR : Fin 64 := 47
@[simp, vmreg] abbrev rFa : Fin 64 := 46
@[simp, vmreg] abbrev rDi : Fin 64 := 45
@[simp, vmreg] abbrev rDc : Fin 64 := 44
@[simp, vmreg] abbrev rTBk : Fin 64 := 43
@[simp, vmreg] abbrev rTKB : Fin 64 := 42
@[simp, vmreg] abbrev rTa : Fin 64 := 41
@[simp, vmreg] abbrev rTnb : Fin 64 := 40
@[simp, vmreg] abbrev rTd : Fin 64 := 39
@[simp, vmreg] abbrev rB1 : Fin 64 := 38

/-- The test material of one digit `i`: the digits `i` of `x + R` and `R − x`. -/
noncomputable def tstD (x R : Rq N K) (i : ℕ) : Rq N K :=
  binaryDigit (x + R) i + binaryDigit (R - x) i

/-- One digit `i = |rDi|`: `rFa += digit_i(x + R) + digit_i(R − x)`, `i := i + 1`. -/
def tstBody : Code :=
  .seq (.op .dig rTd rTa rDi) <| .seq (.op .add rFa rFa rTd) <| .seq (.op .dig rTd rTnb rDi) <|
  .seq (.op .add rFa rFa rTd) (.app rDi rB1)

/-- **The test of `x` (`rTx`)**: `rFa += Σ_{m<n} tstD x R (B + m)`, `B = |rTBk|`, `n = |rTKB|`. -/
def tstC : Code :=
  .seq (.op .add rTa rTx rRR) <| .seq (.op .sub rTnb rRR rTx) <| .seq (.cp rDi rTBk) <|
  .seq (.cp rDc rTKB) (.rep rDc tstBody)

theorem tstBody_writes_rDc : tstBody.writes rDc = false := by decide

theorem exec_tstC (hK : 0 < K) (w : St) (x R F : Rq N K) (B n : ℕ) (hx : w rTx = encRM N K x)
    (hR : w rRR = encRM N K R) (hF : w rFa = encRM N K F) (hB : w rTBk = List.replicate B false)
    (hn : w rTKB = List.replicate n false) (h1 : w rB1 = [false]) :
    exec N K tstC w rFa = encRM N K (F + ∑ m ∈ Finset.range n, tstD x R (B + m)) := by
  unfold tstC
  simp only [exec_seq]
  generalize hW1 : exec N K (.cp rDc rTKB) (exec N K (.cp rDi rTBk) (exec N K (.op .sub rTnb rRR rTx)
    (exec N K (.op .add rTa rTx rRR) w))) = W1
  have f1 : W1 rTa = encRM N K (x + R) ∧ W1 rTnb = encRM N K (R - x) ∧
      W1 rDi = List.replicate B false ∧ W1 rDc = List.replicate n false ∧ W1 rFa = encRM N K F ∧
      W1 rB1 = [false] := by
    rw [← hW1]; vm_simp
    simp [hx, hR, hF, hB, hn, h1, canonW_add hK, canonW_sub hK]
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := f1
  have key := exec_rep_inv2 (N := N) (K := K) rDc tstBody tstBody_writes_rDc
    (fun m w' => w' rDi = List.replicate (B + m) false ∧
      w' rFa = encRM N K (F + ∑ j ∈ Finset.range m, tstD x R (B + j))) W1
    ⟨by simp [a3], by simp [a5]⟩ ?_
  · rw [a4, List.length_replicate] at key
    exact key.2
  · intro m w' _ hP _ hfr
    obtain ⟨p1, p2⟩ := hP
    have ta : w' rTa = encRM N K (x + R) := by rw [hfr _ (by decide) (by decide), a1]
    have tb : w' rTnb = encRM N K (R - x) := by rw [hfr _ (by decide) (by decide), a2]
    have t1 : w' rB1 = [false] := by rw [hfr _ (by decide) (by decide), a6]
    unfold tstBody
    vm_simp
    refine ⟨?_, ?_⟩
    · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, p1, t1]
      rw [← add_assoc, List.replicate_succ']
    · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, p1, p2, ta, tb, takeD_encRM,
        List.length_replicate, canonW_dig hK, canonW_add hK]
      rw [Finset.sum_range_succ, tstD]
      congr 1; ring

/-! ### Decoding a ring element from coins -/

@[simp, vmreg] abbrev rCoin : Fin 64 := 37
@[simp, vmreg] abbrev rDw : Fin 64 := 36
@[simp, vmreg] abbrev rDx : Fin 64 := 35
@[simp, vmreg] abbrev rDn : Fin 64 := 34
@[simp, vmreg] abbrev rTN : Fin 64 := 33
@[simp, vmreg] abbrev rTKmB : Fin 64 := 32
@[simp, vmreg] abbrev rC2 : Fin 64 := 30
@[simp, vmreg] abbrev rDo : Fin 64 := 29

/-- The chunk of `B` coins of coefficient `j`. -/
def chunk (cs : List Bool) (B j : ℕ) : List Bool := (cs.drop (B * j)).take B

/-- The ring element of `N` chunks of `B` coins, shifted by `c`. -/
noncomputable def decCoins (N K : ℕ) (cs : List Bool) (B : ℕ) (c : ZMod (2 ^ K - 1)) : Rq N K :=
  Negacyclic.ofCoeffs fun j => ((Algo.val (chunk cs B j.val) : ℕ) : ZMod (2 ^ K - 1)) - c

/-- One coefficient: `B` coins, then `K − B` zeros. -/
def decBody : Code :=
  .seq (.cp rDx rTBk) <| .seq (.mv rDx rCoin rTBk) <| .seq (.app rDw rDx) (.app rDw rTKmB)

/-- **One ring element from coins**: `rDo := decCoins (B coins per coefficient) − c₂`. -/
def decC : Code := .seq (.clr rDw) <| .seq (.cp rDn rTN) <| .seq (.rep rDn decBody)
  (.op .sub rDo rDw rC2)

theorem decBody_writes_rDn : decBody.writes rDn = false := by decide

theorem shiftIn_replicate (n : ℕ) (s : List Bool) :
    ValVM.shiftIn n (List.replicate n false) s = takeD n s := by
  unfold ValVM.shiftIn
  rw [List.drop_left' (by simp)]

theorem val_append_replicate (u : List Bool) (n : ℕ) :
    Algo.val (u ++ List.replicate n false) = Algo.val u := by
  rw [Algo.val_append]
  have : Algo.val (List.replicate n false) = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, ih]
  rw [this]; ring

theorem exec_decC (hK : 0 < K) (w : St) (cs rest : List Bool) (B : ℕ) (hBK : B ≤ K)
    (hcs : cs.length = N * B) (c2 : ZMod (2 ^ K - 1)) (hC : w rCoin = cs ++ rest)
    (hB : w rTBk = List.replicate B false) (hKB : w rTKmB = List.replicate (K - B) false)
    (hN : w rTN = List.replicate N false)
    (h2 : w rC2 = encRM N K (Negacyclic.ofCoeffs fun _ => c2)) :
    exec N K decC w rDo = encRM N K (decCoins N K cs B c2) ∧
    exec N K decC w rCoin = rest := by
  unfold decC
  simp only [exec_seq]
  generalize hW1 : exec N K (.cp rDn rTN) (exec N K (.clr rDw) w) = W1
  have f1 : W1 rDw = [] ∧ W1 rDn = List.replicate N false ∧ W1 rCoin = cs ++ rest := by
    rw [← hW1]; vm_simp; simp [hN, hC]
  obtain ⟨a1, a2, a3⟩ := f1
  have fr1 : ∀ r : Fin 64, r ≠ rDw → r ≠ rDn → W1 r = w r := fun r h1 h2 => by
    rw [← hW1]; vm_simp; rw [Function.update_of_ne h2, Function.update_of_ne h1]
  have key := exec_rep_inv2 (N := N) (K := K) rDn decBody decBody_writes_rDn
    (fun m w' => w' rDw = Algo.concatN m (fun j => chunk cs B j ++ List.replicate (K - B) false) ∧
      w' rCoin = cs.drop (B * m) ++ rest) W1
    ⟨by simp [a1, Algo.concatN], by simp [a3]⟩ ?_
  · rw [a2, List.length_replicate] at key
    obtain ⟨k1, k2⟩ := key
    generalize hW2 : exec N K (.rep rDn decBody) W1 = W2
    rw [hW2] at k1 k2
    have hlen : ∀ j < N, (chunk cs B j ++ List.replicate (K - B) false).length = K := by
      intro j hj
      simp only [chunk, List.length_append, List.length_take, List.length_drop, hcs,
        List.length_replicate]
      have : B ≤ N * B - B * j := by
        have : B * (j + 1) ≤ N * B := by rw [mul_comm N B]; exact Nat.mul_le_mul_left _ hj
        rw [mul_add, mul_one] at this; omega
      omega
    have hw : (W2 rDw).length = N * K := by rw [k1]; exact Algo.length_concatN hlen
    have c2' : W2 rC2 = encRM N K (Negacyclic.ofCoeffs fun _ => c2) := by
      rw [← hW2, exec_writes _ _ _ (by decide), fr1 _ (by decide) (by decide), h2]
    refine ⟨?_, ?_⟩
    · vm_simp
      simp only [Function.update_self, c2', takeD_encRM]
      rw [takeD_of_length' hw, canonW_eq hK (Algo.length_subRMW _ _ hw _),
        Algo.decRM_subRMW hw (Algo.length_encRM _ _ _), Algo.decRM_encRM hK, k1,
        Algo.decRM_concatN hlen]
      congr 1
      apply Negacyclic.coeffs_injective
      funext j
      simp [decCoins, Algo.decM, val_append_replicate]
    · rw [exec_writes _ _ _ (by decide), k2, List.drop_of_length_le (by rw [hcs, mul_comm])]
      rfl
  · intro m w' hm hP _ hfr
    rw [a2, List.length_replicate] at hm
    obtain ⟨p1, p2⟩ := hP
    have tB : w' rTBk = List.replicate B false := by
      rw [hfr _ (by decide) (by decide), fr1 _ (by decide) (by decide), hB]
    have tK : w' rTKmB = List.replicate (K - B) false := by
      rw [hfr _ (by decide) (by decide), fr1 _ (by decide) (by decide), hKB]
    have hle : B * (m + 1) ≤ cs.length := by
      rw [hcs, mul_comm N B]; exact Nat.mul_le_mul_left _ hm
    unfold decBody
    vm_simp
    refine ⟨?_, ?_⟩
    · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, p1, p2, tB, tK,
        List.length_replicate, shiftIn_replicate]
      rw [takeD_eq_take (by simp; rw [mul_add, mul_one] at hle; omega), List.take_append_of_le_length
        (by simp; rw [mul_add, mul_one] at hle; omega)]
      simp [Algo.concatN, chunk, List.append_assoc]
    · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, p2, tB, List.length_replicate]
      rw [List.drop_append_of_le_length (by simp; rw [mul_add, mul_one] at hle; omega),
        List.drop_drop, mul_add, mul_one]

end AdvancedEncryption.ExpLUT.Prog
