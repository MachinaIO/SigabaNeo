import PE.Impl.ExpLUT.Prog.RedKeyPktStateD
/-!
# The packet stream, part 11: the public words (generic `N K`)

The public segments of every packet are computed once, into the skeleton's queues
`ptPB = ∏_{t<b} (G_t ++ Aa_t ++ Hf_t)` and `ptPS = ∏_{i<16} (SP_i ++ PU_i)` and the word `ptA0`:

* **`pbGC`** (`G_t = C_{g_t}` entrywise): row `0` is `σ(H₁[0, c])`, row `1` is `σ(H₁[1, c]) − σ(h₁[c])`
  with `σ = σ_g^{|P|}` (`pbAutC`: `|P|` rounds of `op aut`), **`exec_pbGC`** (`pbGL`);
* **`pbBitC`**: for `t < b` pop `H_{(t,0)}`, `H_{(t,1)}` (queue `pbQH`), `h_{(t,0)}`, `h_{(t,1)}` (queue
  `pbQh`), `A^aut_t` (queue `pbQA`), append `G_t ++ Aa_t ++ Hf_t` to `ptPB`, double `P`
  (**`exec_pbBitC`**);
* **`pbStepC`**: for `i < 16` append `Ain_i ++ a_i ++ cb_i ++ pz_i` then `pu_i` to `ptPS` (queues `pbQAin`,
  `pbQa`, `pbQcb`, `swQZ`, `swQU`) (**`exec_pbStepC`**);
* **`pbPubC`**: the cursors (copies of the public-key word `2` and the ciphertext word `1` with the
  offsets dropped), both loops and `A₀` (**`exec_pbPubC`**).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyPkt

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo.NegaG
open SigabaNeo.Lattices.Algo (encRM)
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

/-! ### Registers (before the slab loops) -/

/-- Unary width of a row word (`2K · NK`). -/
@[simp, vmreg] abbrev pbTV : Fin 64 := 6
/-- Unary number of entries of a row (`2K`). -/
@[simp, vmreg] abbrev pbTC : Fin 64 := 7
/-- Unary `g` (the generator of the automorphisms). -/
@[simp, vmreg] abbrev pbKg : Fin 64 := 8
/-- Unary `2^t`. -/
@[simp, vmreg] abbrev pbP : Fin 64 := 9
/-- Unary `NK` (also `ptTPU`). -/
@[simp, vmreg] abbrev pbTN : Fin 64 := 29
/-- The popped `A^aut_t`. -/
@[simp, vmreg] abbrev pbAa : Fin 64 := 17
/-- The queue of `H`. -/
@[simp, vmreg] abbrev pbQH : Fin 64 := 32
/-- The queue of `h`. -/
@[simp, vmreg] abbrev pbQh : Fin 64 := 33
/-- The queue of `A^aut`. -/
@[simp, vmreg] abbrev pbQA : Fin 64 := 34
/-- The popped `H_{(t,0)}` (scratch in the step loop). -/
@[simp, vmreg] abbrev pbH0 : Fin 64 := 35
/-- The popped `H_{(t,1)}`. -/
@[simp, vmreg] abbrev pbH1 : Fin 64 := 36
/-- The popped `h_{(t,1)}`. -/
@[simp, vmreg] abbrev pbh1 : Fin 64 := 37
/-- The word `G_t`. -/
@[simp, vmreg] abbrev pbG : Fin 64 := 39
/-- An entry. -/
@[simp, vmreg] abbrev pbE : Fin 64 := 40
/-- A second entry. -/
@[simp, vmreg] abbrev pbF : Fin 64 := 41
/-- The entry counter. -/
@[simp, vmreg] abbrev pbCE : Fin 64 := 44
/-- The automorphism counter. -/
@[simp, vmreg] abbrev pbCA : Fin 64 := 45
/-- The loop counter. -/
@[simp, vmreg] abbrev pbCT : Fin 64 := 46
/-- Offset of the `H` field in the public-key word. -/
@[simp, vmreg] abbrev pbOH : Fin 64 := 47
/-- Offset of the `h` field in the ciphertext word. -/
@[simp, vmreg] abbrev pbOh : Fin 64 := 48
/-- Offset of the `A^aut` field. -/
@[simp, vmreg] abbrev pbOAa : Fin 64 := 49
/-- Offset of the `A^in` field. -/
@[simp, vmreg] abbrev pbOAin : Fin 64 := 50
/-- Offset of the `a` field. -/
@[simp, vmreg] abbrev pbOa : Fin 64 := 51
/-- Offset of the `cinBot` field in the ciphertext word. -/
@[simp, vmreg] abbrev pbOcb : Fin 64 := 52
/-- Offset of the `A₀` field. -/
@[simp, vmreg] abbrev pbOA0 : Fin 64 := 53
/-- The queue of `A^in` (step loop). -/
@[simp, vmreg] abbrev pbQAin : Fin 64 := 32
/-- The queue of `a` (step loop). -/
@[simp, vmreg] abbrev pbQa : Fin 64 := 33
/-- The queue of `cinBot` (step loop). -/
@[simp, vmreg] abbrev pbQcb : Fin 64 := 34

/-! ### Pops -/

/-- **`d :=` the first `|T|` bits of `q`** (which loses them). -/
def pbPopC (d q T : Fin 64) : Code := .seq (.cp d T) (.mv d q T)

theorem shiftIn_self (T u v : List Bool) (hu : u.length = T.length) :
    ValVM.shiftIn T.length T (u ++ v) = u := by
  unfold ValVM.shiftIn
  rw [List.drop_left' rfl, takeD_eq_take (by simp; omega), ← hu, List.take_left' rfl]

theorem exec_pbPopC {N K : ℕ} (d q T : Fin 64) (h1 : d ≠ q) (h2 : d ≠ T) (h3 : q ≠ T) (w : St)
    (u v : List Bool) (hq : w q = u ++ v) (hu : u.length = (w T).length) :
    exec N K (pbPopC d q T) w = Function.update (Function.update w q v) d u := by
  have hne : ¬(d = q ∨ d = T ∨ q = T) := by tauto
  simp only [pbPopC, exec_seq, exec_cp, exec_mv, if_neg hne, Function.update_self,
    Function.update_of_ne (Ne.symm h1), Function.update_of_ne (Ne.symm h2), hq]
  rw [shiftIn_self _ _ _ hu, ← hu, List.drop_left]
  funext r
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem pbPopC_writes (d q T r : Fin 64) (h1 : r ≠ d) (h2 : r ≠ q) : (pbPopC d q T).writes r = false := by
  simp [pbPopC, Code.writes, Ne.symm h1, Ne.symm h2]

/-! ### `σ_g^{|P|}` on an entry -/

/-- `σ_g^m`. -/
def pbSig {N K : ℕ} (g m : ℕ) : Rq N K → Rq N K := (SigabaNeo.Lattices.aut N g)^[m]

/-- **`e := σ_g^{|P|}(e)`** (`|pbKg| = g`). -/
def pbAutC (e : Fin 64) : Code := .seq (.cp pbCA pbP) (.rep pbCA (.op .aut e e pbKg))

theorem exec_pbAutC {N K : ℕ} (hN : 0 < N) (hK : 0 < K) (e : Fin 64) (he1 : e ≠ pbCA)
    (he2 : e ≠ pbKg) (he3 : e ≠ pbP) (w : St) (a : Rq N K) (hE : w e = encRM N K a)
    (hg : 0 < (w pbKg).length) :
    exec N K (pbAutC e) w = Function.update (Function.update w pbCA []) e
      (encRM N K (pbSig (w pbKg).length (w pbP).length a)) := by
  set g := (w pbKg).length
  set w1 := Function.update w pbCA (w pbP) with hw1
  have hwr : (Code.op .aut e e pbKg).writes pbCA = false := by
    simp [Code.writes, he1]
  have key := exec_rep_inv (N := N) (K := K) pbCA (.op .aut e e pbKg) hwr
    (fun m v => v = Function.update (Function.update w pbCA ((w pbP).drop m)) e
      (encRM N K ((SigabaNeo.Lattices.aut N g)^[m] a))) w1
    (by
      rw [hw1]; funext r
      simp only [Function.update_apply, List.drop_zero, Function.iterate_zero, id]
      split_ifs with h h' <;> simp_all)
    (by
      intro m v _ hv _
      subst hv
      have hKe : pbKg ≠ e := Ne.symm he2
      have hCe : pbCA ≠ e := Ne.symm he1
      have hKC : pbKg ≠ pbCA := by decide
      funext r
      simp only [exec_aut, Function.update_apply, hKe, hCe, hKC, if_false, if_true]
      by_cases hr : r = e
      · subst hr
        simp only [if_true, if_neg he1]
        rw [takeD_encRM, canonW_aut hK hN hg, Function.iterate_succ_apply']
      · simp only [if_neg hr]
        by_cases hc : r = pbCA
        · subst hc; simp [List.tail_drop]
        · simp [hc])
  have e1 : exec N K (pbAutC e) w = exec N K (.rep pbCA (.op .aut e e pbKg)) w1 := rfl
  have hl : (w1 pbCA).length = (w pbP).length := by simp [hw1]
  rw [e1]
  rw [hl] at key
  rw [key, List.drop_length]; rfl

theorem pbAutC_writes (e r : Fin 64) (h1 : r ≠ e) (h2 : r ≠ pbCA) : (pbAutC e).writes r = false := by
  simp [pbAutC, Code.writes, Ne.symm h1, Ne.symm h2]

/-! ### `G_t` -/

/-- The entries of `G` from the rows `l0`, `l1` of `H` and the row `l2` of `h`. -/
def pbGL {N K : ℕ} (f : Rq N K → Rq N K) (l0 l1 l2 : List (Rq N K)) : List (Rq N K) :=
  l0.map f ++ List.zipWith (fun a b => f a - f b) l1 l2

/-- One entry of row `0`. -/
def pbRow0Body : Code := .seq (pbPopC pbE pbH1 pbTN) (.seq (pbAutC pbE) (.app pbG pbE))

/-- One entry of row `1`. -/
def pbRow1Body : Code :=
  .seq (pbPopC pbE pbH1 pbTN) <| .seq (pbPopC pbF pbh1 pbTN) <| .seq (pbAutC pbE) <|
  .seq (pbAutC pbF) <| .seq (.op .sub pbE pbE pbF) (.app pbG pbE)

/-- Row `0`. -/
def pbRow0C : Code := .seq (.cp pbCE pbTC) (.rep pbCE pbRow0Body)

/-- Row `1`. -/
def pbRow1C : Code := .seq (.cp pbCE pbTC) (.rep pbCE pbRow1Body)

/-- **`G := C_g`** entrywise. -/
def pbGC : Code := .seq (.clr pbG) (.seq pbRow0C pbRow1C)

theorem length_encRM' {N K : ℕ} (a : Rq N K) : (encRM N K a).length = N * K :=
  SigabaNeo.Lattices.Algo.length_encRM _ _ _

theorem exec_pbRow0Body {N K : ℕ} (hN : 0 < N) (hK : 0 < K) (w : St) (a : Rq N K)
    (rest : List Bool) (hH : w pbH1 = encRM N K a ++ rest) (hTN : (w pbTN).length = N * K)
    (hg : 0 < (w pbKg).length) :
    exec N K pbRow0Body w pbG =
        w pbG ++ encRM N K (pbSig (w pbKg).length (w pbP).length a) ∧
      exec N K pbRow0Body w pbH1 = rest := by
  have e1 := exec_pbPopC (N := N) (K := K) pbE pbH1 pbTN (by decide) (by decide) (by decide) w _ _
    hH (by rw [length_encRM', hTN])
  simp only [pbRow0Body, exec_seq, e1]
  rw [exec_pbAutC hN hK pbE (by decide) (by decide) (by decide) _ a (by simp)
    (by simpa [Function.update_apply] using hg)]
  simp [Function.update_apply]

theorem exec_pbRow1Body {N K : ℕ} (hN : 0 < N) (hK : 0 < K) (w : St) (a c : Rq N K)
    (rest rest' : List Bool) (hH : w pbH1 = encRM N K a ++ rest) (hh : w pbh1 = encRM N K c ++ rest')
    (hTN : (w pbTN).length = N * K) (hg : 0 < (w pbKg).length) :
    exec N K pbRow1Body w pbG = w pbG ++
        encRM N K (pbSig (w pbKg).length (w pbP).length a -
          pbSig (w pbKg).length (w pbP).length c) ∧
      exec N K pbRow1Body w pbH1 = rest ∧ exec N K pbRow1Body w pbh1 = rest' := by
  have e1 := exec_pbPopC (N := N) (K := K) pbE pbH1 pbTN (by decide) (by decide) (by decide) w _ _
    hH (by rw [length_encRM', hTN])
  set w1 := exec N K (pbPopC pbE pbH1 pbTN) w with hw1
  have e2 := exec_pbPopC (N := N) (K := K) pbF pbh1 pbTN (by decide) (by decide) (by decide) w1 _ _
    (by rw [e1]; simpa [Function.update_apply] using hh)
    (by rw [e1, length_encRM']; simpa [Function.update_apply] using hTN.symm)
  set w2 := exec N K (pbPopC pbF pbh1 pbTN) w1 with hw2
  have e3 := exec_pbAutC hN hK pbE (by decide) (by decide) (by decide) w2 a
    (by rw [e2, e1]; simp [Function.update_apply])
    (by rw [e2, e1]; simpa [Function.update_apply] using hg)
  set w3 := exec N K (pbAutC pbE) w2 with hw3
  have e4 := exec_pbAutC hN hK pbF (by decide) (by decide) (by decide) w3 c
    (by rw [e3, e2, e1]; simp [Function.update_apply])
    (by rw [e3, e2, e1]; simpa [Function.update_apply] using hg)
  have hE : exec N K pbRow1Body w = exec N K (.app pbG pbE)
      (exec N K (.op .sub pbE pbE pbF) (exec N K (pbAutC pbF) w3)) := rfl
  rw [hE, e4, e3, e2, e1]
  simp only [exec_app, exec_sub, Function.update_apply]
  simp [takeD_encRM, canonW_sub hK]

theorem take_succ_map {α β : Type*} (f : α → β) (l : List α) (j : ℕ) (hj : j < l.length) :
    (l.take (j + 1)).map f = (l.take j).map f ++ [f l[j]] := by
  rw [List.take_succ, List.getElem?_eq_getElem hj, List.map_append]; simp

theorem pbDrop_encL {N K : ℕ} (l : List (Rq N K)) (j : ℕ) (hj : j < l.length) (u : List Bool) :
    encL N K (l.drop j) ++ u = encRM N K l[j] ++ (encL N K (l.drop (j + 1)) ++ u) := by
  rw [List.drop_eq_getElem_cons hj, encL_cons, List.append_assoc]

theorem exec_pbRow0C {N K : ℕ} (hN : 0 < N) (hK : 0 < K) (w : St) (l0 : List (Rq N K))
    (rest : List Bool) (hH : w pbH1 = encL N K l0 ++ rest) (hTC : (w pbTC).length = l0.length)
    (hTN : (w pbTN).length = N * K) (hg : 0 < (w pbKg).length) :
    exec N K pbRow0C w pbG = w pbG ++ encL N K
        (l0.map (pbSig (w pbKg).length (w pbP).length)) ∧
      exec N K pbRow0C w pbH1 = rest := by
  set f := pbSig (w pbKg).length (w pbP).length
  set w1 := Function.update w pbCE (w pbTC) with hw1
  have hc : (w1 pbCE).length = l0.length := by simp [hw1, hTC]
  have key := exec_rep_inv2 (N := N) (K := K) pbCE pbRow0Body (by decide)
    (fun j v => v pbG = w pbG ++ encL N K ((l0.take j).map f) ∧
      v pbH1 = encL N K (l0.drop j) ++ rest) w1
    ⟨by simp [hw1], by simp [hw1, hH]⟩
    (by
      intro j v hj hP _ hfr
      rw [hc] at hj
      obtain ⟨h1, h2⟩ := hP
      have fr : ∀ r, pbRow0Body.writes r = false → r ≠ pbCE →
          Function.update v pbCE (v pbCE).tail r = w r := fun r hr hrc => by
        rw [Function.update_of_ne hrc, hfr r hr hrc, hw1, Function.update_of_ne hrc]
      obtain ⟨o1, o2⟩ := exec_pbRow0Body (N := N) (K := K) hN hK
        (Function.update v pbCE (v pbCE).tail) l0[j] (encL N K (l0.drop (j + 1)) ++ rest)
        (by rw [Function.update_of_ne (by decide), h2, pbDrop_encL l0 j hj])
        (by rw [fr _ (by decide) (by decide), hTN]) (by rw [fr _ (by decide) (by decide)]; exact hg)
      refine ⟨?_, o2⟩
      rw [o1, fr pbKg (by decide) (by decide), fr pbP (by decide) (by decide),
        Function.update_of_ne (show pbG ≠ pbCE by decide), h1, take_succ_map f l0 j hj]
      simp [encL_append, List.append_assoc, f])
  rw [hc, List.take_length, List.drop_length] at key
  have e : exec N K pbRow0C w = exec N K (.rep pbCE pbRow0Body) w1 := rfl
  rw [e]
  exact ⟨key.1, by simpa using key.2⟩

theorem take_succ_zipWith {α β γ : Type*} (g : α → β → γ) (l : List α) (l' : List β) (j : ℕ)
    (hj : j < l.length) (hj' : j < l'.length) :
    (List.zipWith g l l').take (j + 1) = (List.zipWith g l l').take j ++ [g l[j] l'[j]] := by
  have h : j < (List.zipWith g l l').length := by simp; omega
  rw [List.take_succ, List.getElem?_eq_getElem h, List.getElem_zipWith]; rfl

theorem exec_pbRow1C {N K : ℕ} (hN : 0 < N) (hK : 0 < K) (w : St) (l1 l2 : List (Rq N K))
    (rest rest' : List Bool) (hH : w pbH1 = encL N K l1 ++ rest) (hh : w pbh1 = encL N K l2 ++ rest')
    (hl : l2.length = l1.length) (hTC : (w pbTC).length = l1.length)
    (hTN : (w pbTN).length = N * K) (hg : 0 < (w pbKg).length) :
    exec N K pbRow1C w pbG = w pbG ++ encL N K (List.zipWith
        (fun a c => pbSig (w pbKg).length (w pbP).length a -
          pbSig (w pbKg).length (w pbP).length c) l1 l2) := by
  set f := pbSig (w pbKg).length (w pbP).length
  set w1 := Function.update w pbCE (w pbTC) with hw1
  have hc : (w1 pbCE).length = l1.length := by simp [hw1, hTC]
  have key := exec_rep_inv2 (N := N) (K := K) pbCE pbRow1Body (by decide)
    (fun j v => v pbG = w pbG ++ encL N K ((List.zipWith (fun a c => f a - f c) l1 l2).take j) ∧
      v pbH1 = encL N K (l1.drop j) ++ rest ∧ v pbh1 = encL N K (l2.drop j) ++ rest') w1
    ⟨by simp [hw1], by simp [hw1, hH], by simp [hw1, hh]⟩
    (by
      intro j v hj hP _ hfr
      rw [hc] at hj
      obtain ⟨h1, h2, h3⟩ := hP
      have fr : ∀ r, pbRow1Body.writes r = false → r ≠ pbCE →
          Function.update v pbCE (v pbCE).tail r = w r := fun r hr hrc => by
        rw [Function.update_of_ne hrc, hfr r hr hrc, hw1, Function.update_of_ne hrc]
      obtain ⟨o1, o2, o3⟩ := exec_pbRow1Body (N := N) (K := K) hN hK
        (Function.update v pbCE (v pbCE).tail) l1[j] (l2[j]'(by omega))
        (encL N K (l1.drop (j + 1)) ++ rest) (encL N K (l2.drop (j + 1)) ++ rest')
        (by rw [Function.update_of_ne (by decide), h2, pbDrop_encL l1 j hj])
        (by rw [Function.update_of_ne (by decide), h3, pbDrop_encL l2 j (by omega)])
        (by rw [fr _ (by decide) (by decide), hTN]) (by rw [fr _ (by decide) (by decide)]; exact hg)
      refine ⟨?_, o2, o3⟩
      rw [o1, fr pbKg (by decide) (by decide), fr pbP (by decide) (by decide),
        Function.update_of_ne (show pbG ≠ pbCE by decide), h1, take_succ_zipWith _ l1 l2 j hj (by omega)]
      simp [encL_append, List.append_assoc, f])
  rw [hc] at key
  have e : exec N K pbRow1C w = exec N K (.rep pbCE pbRow1Body) w1 := rfl
  rw [e, key.1, List.take_of_length_le (by simp [hl])]

/-- **`G := C_g`**: the entries of `G` are `pbGL σ l0 l1 l2` for `σ = σ_g^{|P|}`. -/
theorem exec_pbGC {N K : ℕ} (hN : 0 < N) (hK : 0 < K) (w : St) (l0 l1 l2 : List (Rq N K))
    (hH : w pbH1 = encL N K (l0 ++ l1)) (hh : w pbh1 = encL N K l2)
    (h0 : l0.length = (w pbTC).length) (h1 : l1.length = (w pbTC).length)
    (h2 : l2.length = (w pbTC).length)
    (hTN : (w pbTN).length = N * K) (hg : 0 < (w pbKg).length) :
    exec N K pbGC w pbG = encL N K
      (pbGL (pbSig (w pbKg).length (w pbP).length) l0 l1 l2) := by
  set w1 := Function.update w pbG [] with hw1
  have fr1 : ∀ r, r ≠ pbG → w1 r = w r := fun r h => Function.update_of_ne h _ _
  obtain ⟨a1, a2⟩ := exec_pbRow0C (N := N) (K := K) hN hK w1 l0 (encL N K l1)
    (by rw [fr1 _ (by decide), hH, encL_append]) (by rw [fr1 _ (by decide), h0])
    (by rw [fr1 _ (by decide), hTN]) (by rw [fr1 _ (by decide)]; exact hg)
  set w2 := exec N K pbRow0C w1 with hw2
  have fr2 : ∀ r, pbRow0C.writes r = false → w2 r = w1 r := fun r h => exec_writes _ _ _ h
  have b1 := exec_pbRow1C (N := N) (K := K) hN hK w2 l1 l2 [] []
    (by rw [a2, List.append_nil]) (by rw [fr2 _ (by decide), fr1 _ (by decide), hh, List.append_nil])
    (by rw [h1, h2]) (by rw [fr2 _ (by decide), fr1 _ (by decide), h1])
    (by rw [fr2 _ (by decide), fr1 _ (by decide), hTN])
    (by rw [fr2 _ (by decide), fr1 _ (by decide)]; exact hg)
  have e : exec N K pbGC w = exec N K pbRow1C w2 := rfl
  rw [e, b1, a1, fr2 pbKg (by decide), fr2 pbP (by decide), fr1 pbKg (by decide),
    fr1 pbP (by decide)]
  simp [pbGL, hw1, encL_append]

end AdvancedEncryption.ExpLUT.Prog.RedKeyPkt
