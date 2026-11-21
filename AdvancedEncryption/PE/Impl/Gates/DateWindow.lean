import PE.DateWindow
import PE.Impl.Gates.Eval
import SigabaNeo.Lib.Machines.GatesSLP
import SigabaNeo.Lib.Lattices.Homomorphic.BoolCompare

/-!
# Date-window predicates as gate lists

For a window `[a, b]` the predicate `winWord w` is the gate list of the expression `winExp a b`
(`a ≤ x`, `x ≤ b` on the 10 bits, and the format check `valid x` from comparisons of the month
and the day with constants), followed by its negation. With `Eval` the gate-list evaluation
(`Gates.evalMachine L`) and `L` at least the longest input word of these predicates (`dateBound`),
the implementation is expressive (`expressive`).
-/

namespace AdvancedEncryption.PE.Gates.DateWindow

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Lattices.SLP AdvancedEncryption.PE.DateWindow

/-- The month's bits, the day's bits, and all bits. -/
def M : List (Fin 10) := [0, 1, 2, 3, 4]
def D : List (Fin 10) := [5, 6, 7, 8, 9]
def A : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- `is = c`. -/
def eqE (is : List (Fin 10)) (c : Sym) : BExp (Fin 10) := .and (.ge is (symBits c)) (.le is (symBits c))

/-- The format check. -/
def validExp : BExp (Fin 10) :=
  .and (.ge M (symBits 1)) <| .and (.le M (symBits 12)) <| .and (.ge D (symBits 1)) <|
    .and (.or (.not (eqE M 2)) (.le D (symBits 29)))
      (.or (.not (.or (eqE M 4) (.or (eqE M 6) (.or (eqE M 9) (eqE M 11))))) (.le D (symBits 30)))

/-- The window `[a, b]`. -/
def winExp (a b : Date) : BExp (Fin 10) := .and (.ge A (encDate a)) (.and (.le A (encDate b)) validExp)

theorem length_encDate (x : Date) : (encDate x).length = 10 := by
  show (symBits x.1 ++ symBits x.2).length = 10
  simp [length_symBits]

theorem winExp_wf (a b : Date) : (winExp a b).WF := by
  simp [winExp, validExp, eqE, BExp.WF, M, D, A, length_symBits, length_encDate]

/-- The gate list of a window. -/
def winGates (w : Window) : GateList :=
  let r := compile [] (winExp w.1.1 w.1.2)
  predGates r.1 r.2

/-- The predicate of a window. -/
def winWord (w : Window) : List Bool := unparse (winGates w)

/-! ### Its size -/

theorem size_winExp (a b : Date) : (winExp a b).size = 374 := by
  simp [winExp, validExp, eqE, BExp.size, M, D, A]

/-- **A window predicate has at most 375 gates.** -/
theorem length_winGates (w : Window) : (winGates w).length ≤ 375 := by
  have h := SLP.length_compile (winExp w.1.1 w.1.2) []
  rw [size_winExp] at h
  simp only [winGates, predGates, toGates, List.length_map, List.length_append,
    List.length_singleton]
  simp at h
  omega

/-! ### Its value -/

/-- The bits of a date as inputs. -/
def bitsOf (x : Date) (i : Fin 10) : Bool := (encDate x).getD i false

theorem ofFn_bitsOf (x : Date) : List.ofFn (bitsOf x) = encDate x := by
  apply List.ext_getElem (by simp [length_encDate])
  intro i h1 h2
  rw [List.getElem_ofFn]
  simp only [bitsOf]
  rw [List.getD_eq_getElem _ _ h2]

theorem msbVal_symBits (s : Sym) : msbVal (symBits s) = s.val := by
  rw [← ofBits_symBits s, ofBits, foldl_msb]; simp

theorem msbVal_append (l l' : List Bool) :
    msbVal (l ++ l') = msbVal l * 2 ^ l'.length + msbVal l' := by
  induction l with
  | nil => simp [msbVal]
  | cons b l ih => simp only [List.cons_append, msbVal, ih, List.length_append, pow_add]; ring

theorem map_M (x : Date) : M.map (bitsOf x) = symBits x.1 := by
  simp [M, bitsOf, encDate, symBits, List.ofFn_succ]

theorem map_D (x : Date) : D.map (bitsOf x) = symBits x.2 := by
  simp [D, bitsOf, encDate, symBits, List.ofFn_succ]

theorem map_A (x : Date) : A.map (bitsOf x) = encDate x := by
  simp [A, bitsOf, encDate, symBits, List.ofFn_succ]

theorem msbVal_encDate (x : Date) : msbVal (encDate x) = 32 * x.1.val + x.2.val := by
  show msbVal (symBits x.1 ++ symBits x.2) = _
  rw [msbVal_append, msbVal_symBits, msbVal_symBits, length_symBits]; ring

theorem eval_validExp (x : Date) : validExp.eval (bitsOf x) = valid x := by
  simp only [validExp, eqE, BExp.eval, map_M, map_D, msbVal_symBits]
  revert x
  decide +kernel

theorem dateLe_iff (a x : Date) : dateLe a x = decide (32 * a.1.val + a.2.val ≤ 32 * x.1.val + x.2.val) := by
  have := a.2.isLt; have := x.2.isLt
  rw [Bool.eq_iff_iff]
  simp only [dateLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
  rw [Fin.lt_def, Fin.le_def, Fin.ext_iff]
  omega

theorem eval_winExp (w : Window) (x : Date) :
    (winExp w.1.1 w.1.2).eval (bitsOf x) = accepts w x := by
  simp only [winExp, BExp.eval, map_A, msbVal_encDate, eval_validExp, accepts, dateLe_iff]
  cases valid x <;> simp [Bool.and_comm]

/-- **The predicate of a window evaluates to its negated acceptance.** -/
theorem evalGates_winGates (w : Window) (x : Date) :
    evalGates (encDate x, winGates w) = !accepts w x := by
  rw [← ofFn_bitsOf, winGates, evalGates_predGates,
    (compile_spec (bitsOf x) (winExp w.1.1 w.1.2) [] (winExp_wf _ _)).value, eval_winExp]

/-! ### Expressiveness -/

instance : Fintype Window := by unfold Window; infer_instance

/-- The longest input word of `Eval` on a window predicate. -/
noncomputable def dateBound : ℕ :=
  Finset.univ.sup fun wx : Window × Date =>
    (encodeTuple [paramsWord dateUniverse params, winWord wx.1, dateUniverse.encAttr wx.2]).length

/-- **Expressiveness** of every implementation whose `Eval` is the gate-list evaluation with
`L ≥ dateBound`. -/
theorem expressive (impl : Impl sig) {L : ℕ} (h : impl.machine .eval = evalMachine L)
    (hL : dateBound ≤ L) : Expressive dateUniverse params impl := by
  intro (w : Window)
  refine ⟨winWord w, fun (x : Date) => ?_⟩
  rw [authorized_iff (U := dateUniverse) params impl h (winWord w) x]
  have hlen := (Finset.le_sup (f := fun wx : Window × Date =>
      (encodeTuple [paramsWord dateUniverse params, winWord wx.1, dateUniverse.encAttr wx.2]).length)
      (Finset.mem_univ (α := Window × Date) (w, x))).trans hL
  have he : evalGates (dateUniverse.encAttr x, parse (winWord w)) = !accepts w x := by
    rw [winWord, parse_unparse]; exact evalGates_winGates w x
  rw [he, Bool.not_eq_false']
  exact ⟨fun h => h.2, fun h' => ⟨hlen, h'⟩⟩

/-! ### Evaluation of window predicates only

`Eval` may accept only the window predicates: `winEvalMachine L` authorizes `C` for `x` iff the
input is at most `L` long, `C` is the predicate of a window, and its last gate is `false` on `x`.
Correctness then concerns these finitely many predicates only. -/

open Classical in
/-- `Eval` on `(pw, C, x)` for window predicates only. -/
noncomputable def winEvalFun (L : ℕ) (xs : List (List Bool)) : List (List Bool) :=
  [[decide ((encodeTuple xs).length ≤ L) && decide (∃ w : Window, winWord w = xs.getD 1 []) &&
    !evalGates (xs.getD 2 [], parse (xs.getD 1 []))]]

theorem winEvalFun_almostConst (L : ℕ) : ∃ b, {xs | winEvalFun L xs ≠ b}.Finite := by
  refine ⟨[[false]], Set.Finite.subset ((List.finite_length_le Bool L).preimage
    (encodeTuple_injective.injOn)) fun xs hxs => ?_⟩
  by_contra h
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at h
  exact hxs (by simp [winEvalFun, h])

/-- The machine of `Eval` for window predicates. -/
noncomputable def winEvalMachine (L : ℕ) : Machine :=
  Classical.choose (Machine.exists_of_almostConst (encIn := encTuple) (encOut := encTuple)
    (winEvalFun_almostConst L))

theorem winEvalMachine_deterministic (L : ℕ) : (winEvalMachine L).Deterministic :=
  (Classical.choose_spec (Machine.exists_of_almostConst (encIn := encTuple) (encOut := encTuple)
    (winEvalFun_almostConst L))).1

theorem winEvalMachine_run (L : ℕ) (xs : List (List Bool)) :
    (winEvalMachine L).run (encodeTuple xs) = PMF.pure (encodeTuple (winEvalFun L xs)) :=
  (Classical.choose_spec (Machine.exists_of_almostConst (encIn := encTuple) (encOut := encTuple)
    (winEvalFun_almostConst L))).2 xs

/-- **Authorization** for window predicates. -/
theorem win_authorized_iff (impl : Impl sig) {L : ℕ} (h : impl.machine .eval = winEvalMachine L)
    (C : List Bool) (x : Date) : Authorized (U := dateUniverse) params impl C x ↔
      (encodeTuple [paramsWord dateUniverse params, C, encDate x]).length ≤ L ∧
        (∃ w : Window, winWord w = C) ∧ evalGates (encDate x, parse C) = false := by
  classical
  have he : eval (U := dateUniverse) params impl C x =
      PMF.pure ((winEvalFun L [paramsWord dateUniverse params, C, encDate x]).getD 0 []) := by
    unfold eval Impl.run
    rw [h, winEvalMachine_run, PMF.pure_map, PMF.pure_map]
    have : (sig Alg.eval).outputs.length =
        (winEvalFun L [paramsWord dateUniverse params, C, encDate x]).length := rfl
    rw [this]
    exact congrArg (fun l => PMF.pure (List.getD l 0 []))
      (decodeTuple_encodeTuple (winEvalFun L [paramsWord dateUniverse params, C, encDate x]))
  unfold Authorized
  rw [he, PMF.pure_apply]
  split_ifs with hw
  · simp only [winEvalFun, List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq,
      and_true] at hw
    simp only [true_iff]
    have := hw.symm
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · simp only [zero_ne_one, false_iff]
    rintro ⟨h1, h2, h3⟩
    exact hw (by simp [winEvalFun, h1, h2, h3])

/-- **Expressiveness** with `Eval` the evaluation of window predicates and `L ≥ dateBound`. -/
theorem expressive_win (impl : Impl sig) {L : ℕ} (h : impl.machine .eval = winEvalMachine L)
    (hL : dateBound ≤ L) : Expressive dateUniverse params impl := by
  intro (w : Window)
  refine ⟨winWord w, fun (x : Date) => ?_⟩
  rw [win_authorized_iff impl h (winWord w) x]
  have hlen := (Finset.le_sup (f := fun wx : Window × Date =>
      (encodeTuple [paramsWord dateUniverse params, winWord wx.1, dateUniverse.encAttr wx.2]).length)
      (Finset.mem_univ (α := Window × Date) (w, x))).trans hL
  have he : evalGates (encDate x, parse (winWord w)) = !accepts w x := by
    rw [winWord, parse_unparse]; exact evalGates_winGates w x
  rw [he, Bool.not_eq_false']
  exact ⟨fun h => h.2.2, fun h' => ⟨hlen, ⟨w, rfl⟩, h'⟩⟩

end AdvancedEncryption.PE.Gates.DateWindow
