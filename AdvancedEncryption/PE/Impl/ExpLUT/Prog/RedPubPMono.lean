import PE.Impl.ExpLUT.Prog.RedPubPPrep
open SigabaNeo.Tape.RingVM.Hash
/-!
# The monomials `X^{w x_t}` (package G2, `pubP`)

**`exec_monoC`**: from the next 8 attribute bits (the bits of the symbol `x_t`, most significant
first), `monoC` leaves the word of `X^{w x_t}` in `rU` (the bit `7 − j` multiplies by
`X^{w 2^{7 − j}}`, a `rhoJ` with the template `2N − w 2^{7 − j}`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedPubP

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG AdvancedEncryption.PE
  AdvancedEncryption.PE.BranchingProgram
open SigabaNeo.Tape.RingVM.Hash

variable {D : Dims}

/-- The weighted bits `j' < j` of a symbol (most significant first). -/
def symSum (a : ℕ) (j : ℕ) : ℕ :=
  ((List.range j).map fun j' => if a.testBit (7 - j') then 2 ^ (7 - j') else 0).sum

theorem symSum_succ (a j : ℕ) :
    symSum a (j + 1) = symSum a j + if a.testBit (7 - j) then 2 ^ (7 - j) else 0 := by
  simp [symSum, List.range_succ]

theorem symSum_eight : ∀ a : Fin 256, symSum a.val 8 = a.val := by decide +kernel

theorem symbolBits_w8 (a : Symbol w8) :
    symbolBits w8 a = (List.range 8).map fun j => a.val.testBit (7 - j) := by
  rw [symbolBits, List.ofFn_eq_map]
  refine List.ext_getElem (by simp; rfl) fun j h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_finRange, List.getElem_range]
  rfl

/-- **One attribute bit.** -/
theorem exec_rhoStep (hN : 2 ≤ D.N) (hW : wSt * 2 ^ 7 ≤ 2 * D.N) (j : ℕ) (hj : j < 8) (b : Bool)
    (rest : List Bool) (u : Rg D) (w : St) (hT : TmplOK D w) (hA : w rAttr = b :: rest)
    (hBit : (w rBit).length = 1) (hUl : (w rU).length = D.N * D.K) (hUv : decRM D.N D.K (w rU) = u) :
    let w' := exec D.N D.K (rhoStep j) w
    w' rAttr = rest ∧ (w' rU).length = D.N * D.K ∧
      decRM D.N D.K (w' rU) = (setting D).E.X ^ (wSt * if b then 2 ^ (7 - j) else 0) * u ∧
      (w' rBit).length = 1 ∧ ∀ j', j' ∉ [rU, rAttr, rBit] → w' j' = w j' := by
  intro w'
  have e1 := exec_mv_pop (N := D.N) (K := D.K) (d := rBit) (s := rAttr) (c := xC1) (by decide)
    (w := w) (v := [b]) (L := rest) (by rw [hBit, hT.len xC1]; rfl) (by rw [hT.len xC1]; rfl)
    (by rw [hA]; rfl)
  set w1 := Function.update (Function.update w rAttr rest) rBit [b]
  have hw' : w' = exec D.N D.K (.ifb rBit (.rhoJ rU rU (rhoR j)) .nop) w1 := by
    show exec D.N D.K (.ifb rBit (.rhoJ rU rU (rhoR j)) .nop) (exec D.N D.K (.mv rBit rAttr xC1) w) = _
    rw [e1]
  have hrR : (w1 (rhoR j)).length = 2 * D.N - wSt * 2 ^ (7 - j) := by
    have hne1 : rhoR j ≠ rBit := fun h => by
      have := congrArg Fin.val h; simp [rhoR, Nat.mod_eq_of_lt hj] at this; omega
    have hne2 : rhoR j ≠ rAttr := fun h => by
      have := congrArg Fin.val h; simp [rhoR, Nat.mod_eq_of_lt hj] at this; omega
    have hisT : isT (rhoR j) = true := by
      simp [isT, rhoR, Nat.mod_eq_of_lt hj]; omega
    have hne3 : rhoR j ≠ r1 := fun h => by
      have := congrArg Fin.val h; simp [rhoR, Nat.mod_eq_of_lt hj] at this; omega
    simp only [w1, Function.update_of_ne hne1, Function.update_of_ne hne2]
    rw [hT.len (rhoR j) hisT hne3, tm_rhoR j hj]
  have hU1 : w1 rU = w rU := by simp [w1, Function.update_apply]
  have hpow : 2 ^ (7 - j) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hle : wSt * 2 ^ (7 - j) ≤ 2 * D.N := le_trans (Nat.mul_le_mul_left _ hpow) hW
  cases b with
  | false =>
    have : w' = w1 := by rw [hw']; simp [exec, w1]
    rw [this]
    refine ⟨by simp [w1, Function.update_apply], by rw [hU1, hUl], ?_, by simp [w1], ?_⟩
    · rw [hU1, hUv]; simp
    · intro j' hj'
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj'
      simp [w1, Function.update_apply, hj'.2.1, hj'.2.2]
  | true =>
    have : w' = Function.update w1 rU ((rhoMW D.K)^[2 * D.N - wSt * 2 ^ (7 - j)] (w rU)) := by
      rw [hw']
      have hb1 : hd (w1 rBit) = true := by simp [w1, hd]
      show (if hd (w1 rBit) = true then exec D.N D.K (.rhoJ rU rU (rhoR j)) w1 else w1) = _
      rw [if_pos hb1]
      show Function.update w1 rU ((rhoMW D.K)^[(w1 (rhoR j)).length] (opd D.N D.K (w1 rU))) = _
      rw [hrR, hU1, opd_eq hUl]
    rw [this]
    refine ⟨by simp [w1, Function.update_apply], by simp [hUl], ?_, by simp [w1], ?_⟩
    · rw [Function.update_self, decRM_rhoMW_iter_mul D.N_pos hUl, hUv,
        xInvG_pow_eq hN (Nat.sub_le _ _), Nat.sub_sub_self hle, if_pos rfl]
      rfl
    · intro j' hj'
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj'
      simp [w1, Function.update_apply, hj'.1, hj'.2.1, hj'.2.2]

/-- A state agreeing off a list of non-template registers keeps the templates. -/
theorem tmplOK_frame {w w' : St} (L : List (Fin 200)) (hL : L.all (fun r => !isT r) = true)
    (hT : TmplOK D w) (hf : ∀ j, j ∉ L → w' j = w j) : TmplOK D w' :=
  tmplOK_of_agree hT fun r hr => hf r fun hm => by
    have := List.all_eq_true.mp hL r hm
    simp [hr] at this

theorem exec_ofList_single {N K : ℕ} (c : Code) (w : St) : exec N K (ofList [c]) w = exec N K c w :=
  rfl

/-- The bits of a symbol, most significant first. -/
def symBits (a : ℕ) : List Bool := (List.range 8).map fun j => a.testBit (7 - j)

theorem decRM_r1 : decRM D.N D.K (true :: List.replicate (D.N * D.K - 1) false) = 1 :=
  decRM_one D.K_pos D.N_pos

/-- **The monomial `X^{w x_t}`.** -/
theorem exec_monoC (hN : 2 ≤ D.N) (hW : wSt * 2 ^ 7 ≤ 2 * D.N) (a : Symbol w8) (rest : List Bool)
    (w : St) (hT : TmplOK D w) (hA : w rAttr = symbolBits w8 a ++ rest)
    (hBit : (w rBit).length = 1) :
    let w' := exec D.N D.K monoC w
    w' rAttr = rest ∧ (w' rU).length = D.N * D.K ∧
      decRM D.N D.K (w' rU) = (setting D).E.X ^ (wSt * a.val) ∧
      (w' rBit).length = 1 ∧ ∀ j', j' ∉ [rU, rAttr, rBit] → w' j' = w j' := by
  intro w'
  set w0 := Function.update w rU (w r1)
  have ex : w' = exec D.N D.K (ofList ((List.range 8).map rhoStep)) w0 := rfl
  have hbits : symbolBits w8 a = symBits a.val := symbolBits_w8 a
  have hNK : 1 ≤ D.N * D.K := Nat.mul_pos D.N_pos D.K_pos
  have hT0 : TmplOK D w0 := tmplOK_of_agree hT fun r hr => by
    simp only [w0]; rw [Function.update_of_ne (fun h => by subst h; revert hr; decide)]
  have key : ∀ n ≤ 8, let wn := exec D.N D.K (ofList ((List.range n).map rhoStep)) w0
      wn rAttr = (symBits a.val).drop n ++ rest ∧ (wn rU).length = D.N * D.K ∧
      decRM D.N D.K (wn rU) = (setting D).E.X ^ (wSt * symSum a.val n) ∧
      (wn rBit).length = 1 ∧ TmplOK D wn ∧ ∀ j', j' ∉ [rU, rAttr, rBit] → wn j' = w0 j' := by
    intro n
    induction n with
    | zero =>
      intro _
      simp only [List.range_zero, List.map_nil, exec_ofList_nil]
      refine ⟨by simp [w0, Function.update_apply, hA, hbits], ?_, ?_, ?_, hT0, by simp⟩
      · simp [w0, hT.2]; omega
      · simp only [w0, Function.update_self, hT.2, decRM_r1]
        simp [symSum]
      · simp [w0, Function.update_apply, hBit]
    | succ n ih =>
      intro hn
      obtain ⟨i1, i2, i3, i4, i5, i6⟩ := ih (by omega)
      rw [List.range_succ, List.map_append, exec_ofList_append, List.map_singleton,
        exec_ofList_single]
      set wn := exec D.N D.K (ofList ((List.range n).map rhoStep)) w0
      have hnb : n < (symBits a.val).length := by simp [symBits]; omega
      obtain ⟨s1, s2, s3, s4, s5⟩ := exec_rhoStep (D := D) hN hW n (by omega) (symBits a.val)[n]
        ((symBits a.val).drop (n + 1) ++ rest) ((setting D).E.X ^ (wSt * symSum a.val n)) wn i5
        (by rw [i1, List.drop_eq_getElem_cons hnb, List.cons_append]) i4 i2 i3
      have hbn : (symBits a.val)[n] = a.val.testBit (7 - n) := by simp [symBits]
      have hexp : wSt * (if (symBits a.val)[n] then 2 ^ (7 - n) else 0) + wSt * symSum a.val n =
          wSt * symSum a.val (n + 1) := by
        rw [symSum_succ, hbn, Nat.mul_add, Nat.add_comm]
      refine ⟨s1, s2, ?_, s4, ?_, ?_⟩
      · rw [s3, ← pow_add, hexp]
      · exact tmplOK_frame [rU, rAttr, rBit] (by decide) i5 s5
      · intro j' hj'; rw [s5 j' hj', i6 j' hj']
  obtain ⟨k1, k2, k3, k4, -, k6⟩ := key 8 le_rfl
  rw [ex]
  refine ⟨by rw [k1]; simp [symBits], k2, by rw [k3, symSum_eight a], k4, fun j' hj' => ?_⟩
  rw [k6 j' hj']
  simp only [w0]
  rw [Function.update_of_ne (fun h => hj' (by simp [h]))]

end AdvancedEncryption.ExpLUT.Prog.RedPubP
