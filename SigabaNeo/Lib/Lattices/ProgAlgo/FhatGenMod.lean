import SigabaNeo.Lib.Lattices.ProgAlgo.FhatGenArith

/-!
# Generating gate tapes: modular addition and subtraction

Moving a prefix of a list (`takeC`), constant lists of wires by a test on the bit index
(`constC`), and the register code of `modAdd`, `modSub`.
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Lattices

namespace FhatGen

open SigabaNeo.Tape SigabaNeo.Tape.RegVM SLP

variable {ι : Type*} {E : Env} {ix : ι → ℕ}

theorem exec_lpush_lt (σ : St) (l : LR) (r : SR) (hl : (σ.ls l).length < E.C)
    (hr : σ.sc r ≤ E.M) :
    exec E (.lpush l r) σ = { σ with ls := Function.update σ.ls l (σ.ls l ++ [σ.sc r]) } := by
  simp [exec, hl, min_eq_left hr]

/-! ### Moving a prefix -/

/-- Move the first `|n|` elements of `lA` to the end of `lR` (through the register `41`). -/
def takeC (n : SR) (lA lR : LR) : Code := .rep n (.seq (.lpop 41 lA) (.lpush lR 41))

theorem iter_take {lA lR : LR} (hAR : lA ≠ lR) :
    ∀ (X Y L0 : List ℕ) (σ : St), Inv E σ → σ.ls lA = X ++ Y → σ.ls lR = L0 →
      L0.length + X.length ≤ E.C →
      ∃ sc', (exec E (.seq (.lpop 41 lA) (.lpush lR 41)))^[X.length] σ =
        { σ with sc := sc', ls := Function.update (Function.update σ.ls lA Y) lR (L0 ++ X) } ∧
        Fr [41] σ.sc sc'
  | [], Y, L0, σ, _, hA, hR, _ => by
    refine ⟨σ.sc, ?_, Fr.refl _ _⟩
    simp only [List.length_nil, Function.iterate_zero, id, List.append_nil]
    rw [List.nil_append] at hA
    rw [← hA, ← hR]; simp
  | x :: X, Y, L0, σ, hInv, hA, hR, hcap => by
    simp only [List.length_cons] at hcap ⊢
    rw [Function.iterate_succ_apply]
    have hx : x ≤ E.M := (hInv.1 lA).2 x (by simp [hA])
    set sc1 := Function.update σ.sc 41 x
    set ls1 := Function.update (Function.update σ.ls lA (X ++ Y)) lR (L0 ++ [x])
    set σ1 : St := { σ with sc := sc1, ls := ls1 }
    have e1 : exec E (.seq (.lpop 41 lA) (.lpush lR 41)) σ = σ1 := by
      simp only [exec_seq]
      rw [exec_lpush_lt _ _ _ (by simp [exec, Function.update_of_ne hAR.symm, hR]; omega)
        (by simp [exec, hA]; exact hx)]
      simp [exec, hA, Function.update_of_ne hAR.symm, hR, σ1, sc1, ls1]
    rw [e1]
    have hI1 : Inv E σ1 := by
      have := inv_exec E (.seq (.lpop 41 lA) (.lpush lR 41)) σ hInv; rw [e1] at this; exact this
    obtain ⟨sc', h, f⟩ := iter_take hAR X Y (L0 ++ [x]) σ1 hI1
      (by simp [σ1, ls1, Function.update_of_ne hAR]) (by simp [σ1, ls1]) (by simp; omega)
    refine ⟨sc', ?_, fun r hr => (f r hr).trans ?_⟩
    · rw [h]; simp only [σ1, ls1]
      congr 1
      funext l; simp only [Function.update_apply]; split_ifs <;> simp
    · simp only [σ1, sc1]; exact Function.update_of_ne (by simpa using hr) _ _

/-- **Moving a prefix.** -/
theorem exec_takeC {n : SR} {lA lR : LR} (hAR : lA ≠ lR) (X Y L0 : List ℕ) (σ : St)
    (hInv : Inv E σ) (hA : σ.ls lA = X ++ Y) (hR : σ.ls lR = L0) (hn : σ.sc n = X.length)
    (hcap : L0.length + X.length ≤ E.C) :
    ∃ sc', exec E (takeC n lA lR) σ =
        { σ with sc := sc', ls := Function.update (Function.update σ.ls lA Y) lR (L0 ++ X) } ∧
      Fr [41] σ.sc sc' := by
  rw [takeC, exec_rep, hn]; exact iter_take hAR X Y L0 σ hInv hA hR hcap

/-- Codes without `nand`. -/
def NoNand : Code → Prop
  | .nand _ _ _ => False
  | .seq p q | .ifLt _ _ p q => NoNand p ∧ NoNand q
  | .rep _ body => NoNand body
  | _ => True

/-- **A code without `nand` leaves the program alone.** -/
theorem exec_out_t : ∀ (c : Code), NoNand c → ∀ (σ : St) (o : List Bool) (t : ℕ),
    exec E c { σ with out := o, t := t } = { exec E c σ with out := o, t := t }
  | .nand _ _ _, h, _, _, _ => h.elim
  | .one _, _, _, _, _ | .zero _, _, _, _, _ | .mov _ _, _, _, _, _ | .inc _, _, _, _, _
  | .add _ _, _, _, _, _ | .sub _ _, _, _, _, _ | .lnil _, _, _, _, _ | .lpush _ _, _, _, _, _
  | .lpop _ _, _, _, _, _ | .lmov _ _, _, _, _, _ | .rdsrc _, _, _, _, _ | .skip, _, _, _, _ => rfl
  | .seq p q, h, σ, o, t => by
    simp only [exec_seq]; rw [exec_out_t p h.1, exec_out_t q h.2]
  | .ifLt a b p q, h, σ, o, t => by
    simp only [exec]; split_ifs
    · exact exec_out_t p h.1 σ o t
    · exact exec_out_t q h.2 σ o t
  | .rep a body, h, σ, o, t => by
    simp only [exec]
    generalize σ.sc a = m
    induction m generalizing σ with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        exec_out_t body h, ih]

theorem exec_mk_noNand (c : Code) (hc : NoNand c) (P : SLP ι) (σ : St) :
    exec E c (mk E ix P σ) = mk E ix P (exec E c σ) := exec_out_t c hc σ _ _

/-! ### Constant lists -/

/-- `σ` with new registers and lists. -/
def setSL (σ : St) (sc : SR → ℕ) (ls : LR → List ℕ) : St := { σ with sc := sc, ls := ls }

/-- `l :=` the list of `f 0, …, f (|cnt| - 1)`, the body pushing `f i` with the index `i` in the
register `42`. -/
def constC (cnt : SR) (l : LR) (body : Code) : Code :=
  .seq (.lnil l) (.seq (.zero 42) (.rep cnt (.seq body (.inc 42))))

theorem iter_const {body : Code} {l : LR} {f : ℕ → ℕ} {Q : St → Prop}
    (hQ : ∀ σ : St, Q σ → ∀ v ls', Q (setSL σ (Function.update σ.sc 42 v) ls'))
    (hb : ∀ (σ : St) (i : ℕ), Q σ → σ.sc 42 = i → (σ.ls l).length < E.C →
      exec E body σ = { σ with ls := Function.update σ.ls l (σ.ls l ++ [f i]) }) :
    ∀ (j : ℕ) (σ : St) (i : ℕ), Q σ → σ.sc 42 = i → i + j ≤ E.M → (σ.ls l).length + j ≤ E.C →
      (exec E (.seq body (.inc 42)))^[j] σ = setSL σ (Function.update σ.sc 42 (i + j))
        (Function.update σ.ls l (σ.ls l ++ (List.range j).map (fun x => f (i + x))))
  | 0, σ, i, _, hi, _, _ => by
    simp only [Function.iterate_zero, id, Nat.add_zero, List.range_zero, List.map_nil,
      List.append_nil, Function.update_eq_self, setSL]
    rw [← hi]; simp
  | j + 1, σ, i, hq, hi, hM, hC => by
    rw [Function.iterate_succ_apply, exec_seq, hb σ i hq hi (by omega)]
    set σ1 : St := { σ with ls := Function.update σ.ls l (σ.ls l ++ [f i]) }
    have e2 : exec E (.inc 42) σ1 = setSL σ (Function.update σ.sc 42 (i + 1))
        (Function.update σ.ls l (σ.ls l ++ [f i])) := by
      simp only [exec, σ1, hi, setSL]; rw [min_eq_left (by omega)]
    rw [e2]
    rw [iter_const hQ hb j _ (i + 1) (hQ σ hq _ _) (by simp [setSL]) (by omega)
      (by simp [setSL]; omega)]
    simp only [setSL, Function.update_idem, Function.update_self, List.append_assoc]
    have e3 : (List.range (j + 1)).map (fun x => f (i + x)) =
        f i :: (List.range j).map (fun x => f (i + 1 + x)) := by
      rw [List.range_succ_eq_map]; simp only [List.map_cons, List.map_map]
      congr 1; apply List.map_congr_left; intro x _; simp only [Function.comp]; congr 1; omega
    rw [e3, show i + 1 + j = i + (j + 1) by omega]
    rfl

theorem exec_constC {body : Code} {l : LR} {f : ℕ → ℕ} {Q : St → Prop} {cnt : SR}
    (hcnt : cnt ≠ 42)
    (hQ : ∀ σ : St, Q σ → ∀ v ls', Q (setSL σ (Function.update σ.sc 42 v) ls'))
    (hb : ∀ (σ : St) (i : ℕ), Q σ → σ.sc 42 = i → (σ.ls l).length < E.C →
      exec E body σ = { σ with ls := Function.update σ.ls l (σ.ls l ++ [f i]) })
    (σ : St) (hq : Q σ) (hM : σ.sc cnt ≤ E.M) (hC : σ.sc cnt ≤ E.C) :
    exec E (constC cnt l body) σ = setSL σ (Function.update σ.sc 42 (σ.sc cnt))
      (Function.update σ.ls l ((List.range (σ.sc cnt)).map f)) := by
  simp only [constC, exec_seq]
  have e1 : exec E (.zero 42) (exec E (.lnil l) σ) =
      setSL σ (Function.update σ.sc 42 0) (Function.update σ.ls l []) := rfl
  rw [e1, exec_rep]
  have hc : (setSL σ (Function.update σ.sc 42 0) (Function.update σ.ls l [])).sc cnt = σ.sc cnt := by
    simp [setSL, Function.update_of_ne hcnt]
  rw [hc, iter_const hQ hb (σ.sc cnt) _ 0 (hQ σ hq _ _) (by simp [setSL]) (by omega)
    (by simp [setSL]; omega)]
  simp [setSL, Function.update_idem]

theorem constL_eq_map (z : Wire ι) : ∀ (w m : ℕ),
    constL z w m = (List.range w).map (fun i => if m.testBit i then .one else z)
  | 0, m => rfl
  | w + 1, m => by
    rw [constL, constL_eq_map z w (m / 2), List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · simp only [Nat.testBit_zero]
      by_cases h : m % 2 = 1 <;> simp [h]
    · apply List.map_congr_left; intro i _
      simp only [Function.comp, Nat.testBit_succ]

theorem testBit_two_pow_sub_two_pow {k K i : ℕ} (hK : K ≤ k + 1) :
    (2 ^ (k + 1) - 2 ^ K).testBit i = decide (K ≤ i ∧ i < k + 1) := by
  have e : 2 ^ (k + 1) - 2 ^ K = (2 ^ (k + 1 - K) - 1) * 2 ^ K := by
    rw [Nat.sub_mul, one_mul, ← pow_add, Nat.sub_add_cancel hK]
  rw [e, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases h : K ≤ i <;> simp [h] <;> omega

/-- The constant registers of the arithmetic: `1`, `z`, `k`, `k + 1`, `K`. -/
def Cst (k K : ℕ) (σ : St) : Prop := Consts E σ ∧ σ.sc 2 = k ∧ σ.sc 3 = k + 1 ∧ σ.sc 4 = K

theorem cst_setSL {k K : ℕ} {σ : St} (h : Cst (E := E) k K σ) {r : SR} (hr : 4 < r.val) (v : ℕ)
    (ls' : LR → List ℕ) : Cst (E := E) k K (setSL σ (Function.update σ.sc r v) ls') := by
  obtain ⟨⟨h0, h1⟩, h2, h3, h4⟩ := h
  have ne : ∀ s : SR, s.val ≤ 4 → s ≠ r := fun s hs e => by subst e; omega
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> simp only [setSL] <;>
    rw [Function.update_of_ne (ne _ (by decide))]
  all_goals assumption

/-- The body pushing the bits of `2^(k+1) - 2^K` (`1` from the bit `K` on). -/
def addConstBody (l : LR) : Code := .ifLt 42 4 (.lpush l rZ) (.lpush l rONE)

/-- The body pushing the bits of `2^K`. -/
def qConstBody (l : LR) : Code := .ifLt 42 4 (.lpush l rZ) (.ifLt 4 42 (.lpush l rZ) (.lpush l rONE))

theorem exec_addConstBody (hnM : E.n + 1 ≤ E.M) {k K : ℕ} (l : LR) (σ : St) (i : ℕ)
    (hc : Cst (E := E) k K σ) (hi : σ.sc 42 = i) (hl : (σ.ls l).length < E.C) :
    exec E (addConstBody l) σ =
      { σ with ls := Function.update σ.ls l (σ.ls l ++ [if i < K then E.n + 1 else E.n]) } := by
  simp only [addConstBody, exec, hi, hc.2.2.2, hl, ite_true, hc.1.1, hc.1.2]
  split_ifs <;> simp only [min_eq_left (show E.n + 1 ≤ E.M by omega),
    min_eq_left (show E.n ≤ E.M by omega)]

theorem exec_qConstBody (hnM : E.n + 1 ≤ E.M) {k K : ℕ} (l : LR) (σ : St) (i : ℕ)
    (hc : Cst (E := E) k K σ) (hi : σ.sc 42 = i) (hl : (σ.ls l).length < E.C) :
    exec E (qConstBody l) σ =
      { σ with ls := Function.update σ.ls l (σ.ls l ++ [if i = K then E.n else E.n + 1]) } := by
  simp only [qConstBody, exec, hi, hc.2.2.2, hl, ite_true, hc.1.1, hc.1.2]
  split_ifs <;> simp only [min_eq_left (show E.n + 1 ≤ E.M by omega),
    min_eq_left (show E.n ≤ E.M by omega)] <;> first | rfl | (exfalso; omega)

/-! ### Modular addition -/

theorem is_exec (hnM : E.n ≤ E.M) (hWM : E.W ≤ E.M) {c : Code} {τ τ' : St} (h : exec E c τ = τ')
    (hτ : Inv E τ ∧ ScOK E τ) : Inv E τ' ∧ ScOK E τ' :=
  h ▸ ⟨inv_exec E c τ hτ.1, scOK_exec E hnM hWM c τ hτ.1 hτ.2⟩

/-- `(exec a τ).t ≤ (exec b₁ (… (exec a τ))).t`. -/
macro "t_chain" : tactic => `(tactic| (repeat (first | (with_reducible exact le_rfl) |
  (with_reducible refine le_trans ?_ (t_le_exec _ _ _)))))

/-- Registers outside `16 … 42` are in no list of registers inside. -/
theorem not_mem_of_out (L : List SR) (h : ∀ x ∈ L, 16 ≤ x.val ∧ x.val ≤ 42) {r : SR}
    (hr : r.val < 16 ∨ 42 < r.val) : r ∉ L := fun hm => by have := h r hm; omega

theorem hM_left {a b : Code} {τ : St} (h : E.n + (exec E (.seq a b) τ).t ≤ E.M) :
    E.n + (exec E a τ).t ≤ E.M := le_trans (by have := t_le_exec E b (exec E a τ); simp; omega) h

/-- **`modAdd` as register code**: the summands in the lists `0`, `1`, the result in `2`
(scratch: the lists `3 … 8`, the registers `16 … 42`). -/
def modAddC : Code :=
  .seq (.lnil 3) <| .seq (.mov 18 rZ) <| .seq (rippleAddC 2 0 1 3) <| .seq (.lmov 4 3) <|
  .seq (constC 3 5 (addConstBody 5)) <| .seq (.lnil 6) <| .seq (.mov 18 rZ) <|
  .seq (rippleAddC 3 4 5 6) <| .seq (.lnil 7) <| .seq (takeC 3 6 7) <| .seq (.lpop 36 6) <|
  .seq (.lnil 8) <| .seq (muxLC 3 7 3 8) <| .seq (.lnil 2) (takeC 2 8 2)

theorem length_rippleAdd_eq (p : SLP ι) (as bs : List (Wire ι)) (c : Wire ι)
    (h : as.length = bs.length) : (rippleAdd p as bs c).2.length = as.length + 1 := by
  rw [rippleAdd_eq p as bs c h]; simp [length_zipB _ _ _ _ _ h]

theorem length_muxL_eq (s : Wire ι) (p : SLP ι) (as bs : List (Wire ι))
    (h : as.length = bs.length) : (muxL s p as bs).2.length = as.length := by
  rw [muxL_eq s p as bs .one h]; simp [length_zipB _ _ _ _ _ h]

theorem le_modAdd_r1 (z : Wire ι) (q w : ℕ) (p : SLP ι) (as bs : List (Wire ι)) :
    (rippleAdd p as bs z).1.length ≤ (modAdd z q w p as bs).1.length :=
  (le_length_rippleAdd _ _ _ _).trans (le_length_muxL _ _ _ _)

theorem le_modAdd_r2 (z : Wire ι) (q w : ℕ) (p : SLP ι) (as bs : List (Wire ι)) :
    (rippleAdd (rippleAdd p as bs z).1 (rippleAdd p as bs z).2 (constL z (w + 1) (2 ^ (w + 1) - q))
      z).1.length ≤ (modAdd z q w p as bs).1.length := le_length_muxL _ _ _ _

theorem le_length_modAdd (z : Wire ι) (q w : ℕ) (p : SLP ι) (as bs : List (Wire ι)) :
    p.length ≤ (modAdd z q w p as bs).1.length :=
  (le_length_rippleAdd _ _ _ _).trans (le_modAdd_r1 z q w p as bs)

theorem exec_modAddC (hnM : E.n + 1 ≤ E.M) (hWM : E.W ≤ E.M) (hix : ∀ i, ix i < E.n) {k K : ℕ}
    (hK : K ≤ k + 1) (as bs : List (Wire ι)) (P : SLP ι) (σ : St) (hc : Cst (E := E) k K σ)
    (hI : Inv E σ) (hS : ScOK E σ) (hA : σ.ls 0 = as.map (pos E ix))
    (hB : σ.ls 1 = bs.map (pos E ix)) (hla : as.length = k) (hlb : bs.length = k)
    (hcap : k + 3 ≤ E.C) (hkM : k + 2 ≤ E.M)
    (hM : E.n + (modAdd (.gate 0) (2 ^ K) k P as bs).1.length ≤ E.M) :
    ∃ sc' ls', exec E modAddC (mk E ix P σ) =
        mk E ix (modAdd (.gate 0) (2 ^ K) k P as bs).1 (setSL σ sc' ls') ∧
      ls' 2 = (modAdd (.gate 0) (2 ^ K) k P as bs).2.map (pos E ix) ∧
      (∀ r : SR, r.val < 16 ∨ 42 < r.val → sc' r = σ.sc r) ∧ (∀ l : LR, 8 < l.val → ls' l = σ.ls l) := by
  have hnM' : E.n ≤ E.M := by omega
  have hz : pos E ix (.gate 0 : Wire ι) = E.n + 1 := rfl
  -- 1, 2: `lnil 3`, `mov 18 z`
  set σ2 := setSL σ (Function.update σ.sc 18 (E.n + 1)) (Function.update σ.ls 3 []) with hσ2
  have e2 : exec E (.mov 18 rZ) (exec E (.lnil 3) (mk E ix P σ)) = mk E ix P σ2 := by
    simp only [exec, mk, σ2, setSL, hc.1.2]
  have hIS2 : Inv E σ2 ∧ ScOK E σ2 := is_exec (τ := mk E ix P σ) (τ' := mk E ix P σ2) hnM' hWM
    (c := .seq (.lnil 3) (.mov 18 rZ)) e2 ⟨hI, hS⟩
  simp only [modAddC, exec_seq]
  rw [e2]
  -- 3: the first ripple addition
  have hc2 : Consts E σ2 := ⟨by simp [σ2, setSL, rONE, Function.update_apply, ← hc.1.1],
    by simp [σ2, setSL, rZ, Function.update_apply, ← hc.1.2]⟩
  obtain ⟨sc3, h3, f3⟩ := exec_rippleAddC (lA := 0) (lB := 1) (lR := 3) (n := 2) hnM' hWM hix
    (by decide) (by decide) (by decide) as bs P σ2 (.gate 0) [] (by omega) hc2 hIS2.1 hIS2.2
    (by simp [σ2, setSL, hA]) (by simp [σ2, setSL, hB]) (by simp [σ2, setSL])
    (by simp [σ2, setSL, pos]) (by simp [σ2, setSL, hc.2.1, hla]) (by simp; omega)
    (le_trans (Nat.add_le_add_left (le_modAdd_r1 _ _ _ _ _ _) _) hM)
  set r1 := rippleAdd P as bs (.gate 0)
  have hl1 : r1.2.length = k + 1 := by rw [length_rippleAdd_eq _ _ _ _ (by omega), hla]
  set ls3' := ls3 σ2.ls 0 1 3 ([] ++ r1.2.map (pos E ix))
  have e3 : ({ σ2 with sc := sc3, ls := ls3' } : St) = setSL σ sc3 ls3' := rfl
  rw [e3] at h3
  have hIS3 := is_exec hnM' hWM h3 (by exact hIS2)
  rw [h3]
  -- 4: copy
  set σ4 := setSL σ sc3 (Function.update ls3' 4 (r1.2.map (pos E ix)))
  have e4 : exec E (.lmov 4 3) (mk E ix r1.1 (setSL σ sc3 ls3')) = mk E ix r1.1 σ4 := by
    rw [exec_mk_noNand (.lmov 4 3) trivial]; simp [exec, σ4, setSL, ls3', ls3]
  have hIS4 := is_exec hnM' hWM e4 hIS3
  rw [e4]
  -- 5: the constant
  have fr3 : ∀ r : SR, r.val < 16 ∨ 42 < r.val → sc3 r = σ.sc r := fun r hr => by
    rw [f3 r (not_mem_of_out _ (by decide) hr)]
    simp only [σ2, setSL]
    exact Function.update_of_ne (fun h => by subst h; revert hr; decide) _ _
  have hc4 : Cst (E := E) k K σ4 := ⟨⟨by rw [← hc.1.1]; exact fr3 0 (by decide),
    by rw [← hc.1.2]; exact fr3 1 (by decide)⟩, by rw [← hc.2.1]; exact fr3 2 (by decide),
    by rw [← hc.2.2.1]; exact fr3 3 (by decide), by rw [← hc.2.2.2]; exact fr3 4 (by decide)⟩
  have h5 := exec_constC (E := E) (l := 5) (cnt := 3) (Q := Cst (E := E) k K) (by decide)
    (fun σ h v ls' => cst_setSL h (by decide) v ls')
    (fun σ i hq hi hl => exec_addConstBody (E := E) hnM 5 σ i hq hi hl) σ4 hc4
    (by rw [hc4.2.2.1]; omega) (by rw [hc4.2.2.1]; omega)
  rw [exec_mk_noNand _ (by simp [NoNand, constC, addConstBody]), h5]
  have hIS5 := is_exec hnM' hWM (c := constC 3 5 (addConstBody 5)) (τ := mk E ix r1.1 σ4)
    (by rw [exec_mk_noNand _ (by simp [NoNand, constC, addConstBody]), h5]) hIS4
  set KC : List (Wire ι) := constL (.gate 0) (k + 1) (2 ^ (k + 1) - 2 ^ K)
  have hKC : (List.range (σ4.sc 3)).map (fun i => if i < K then E.n + 1 else E.n) =
      KC.map (pos E ix) := by
    rw [hc4.2.2.1, show KC = _ from constL_eq_map _ _ _, List.map_map]
    apply List.map_congr_left; intro i hi
    simp only [List.mem_range] at hi
    simp only [Function.comp, testBit_two_pow_sub_two_pow hK]
    by_cases h : K ≤ i
    · simp [h, hi, pos, show ¬ i < K by omega]
    · simp [h, pos, show i < K by omega]
  rw [hKC] at ⊢ hIS5
  set sc5 := Function.update σ4.sc 42 (σ4.sc 3)
  set ls5 := Function.update σ4.ls 5 (KC.map (pos E ix))
  have e5 : setSL σ4 sc5 ls5 = setSL σ sc5 ls5 := rfl
  rw [e5] at ⊢ hIS5
  -- 6, 7: `lnil 6`, `mov 18 z`
  set σ7 := setSL σ (Function.update sc5 18 (E.n + 1)) (Function.update ls5 6 [])
  have e7 : exec E (.mov 18 rZ) (exec E (.lnil 6) (mk E ix r1.1 (setSL σ sc5 ls5))) =
      mk E ix r1.1 σ7 := by
    have hz5 : sc5 rZ = E.n + 1 := by
      simp only [sc5]; rw [Function.update_of_ne (by decide)]; exact hc4.1.2
    simp only [exec, mk, σ7, setSL, hz5]
  have hIS7 := is_exec hnM' hWM (c := .seq (.lnil 6) (.mov 18 rZ)) e7 hIS5
  rw [e7]
  -- 8: the second ripple addition
  have fr5 : ∀ r : SR, r.val < 16 ∨ 42 < r.val → Function.update sc5 18 (E.n + 1) r = σ.sc r :=
    fun r hr => by
      simp only [sc5]
      rw [Function.update_of_ne (fun h => by subst h; revert hr; decide),
        Function.update_of_ne (fun h => by subst h; revert hr; decide)]
      exact fr3 r hr
  have hc7 : Consts E σ7 := ⟨by rw [← hc.1.1]; exact fr5 0 (by decide),
    by rw [← hc.1.2]; exact fr5 1 (by decide)⟩
  have hl4 : σ7.ls 4 = r1.2.map (pos E ix) := by
    simp [σ7, setSL, ls5, σ4, Function.update_apply]
  have hl5 : σ7.ls 5 = KC.map (pos E ix) := by simp [σ7, setSL, ls5, Function.update_apply]
  have hl6 : σ7.ls 6 = [] := by simp [σ7, setSL]
  have hKCl : KC.length = k + 1 := constL_length _ _ _
  obtain ⟨sc8, h8, f8⟩ := exec_rippleAddC (lA := 4) (lB := 5) (lR := 6) (n := 3) hnM' hWM hix
    (by decide) (by decide) (by decide) r1.2 KC r1.1 σ7 (.gate 0) [] (by omega) hc7 hIS7.1 hIS7.2
    hl4 hl5 hl6 (by simp [σ7, setSL, pos])
    (by rw [hl1, ← hc.2.2.1]; exact fr5 3 (by decide)) (by simp; omega)
    (le_trans (Nat.add_le_add_left (le_modAdd_r2 _ _ _ _ _ _) _) hM)
  set r2 := rippleAdd r1.1 r1.2 KC (.gate 0)
  have hl2 : r2.2.length = k + 2 := by rw [length_rippleAdd_eq _ _ _ _ (by omega), hl1]
  set ls8 := ls3 σ7.ls 4 5 6 ([] ++ r2.2.map (pos E ix))
  have e8 : ({ σ7 with sc := sc8, ls := ls8 } : St) = setSL σ sc8 ls8 := rfl
  rw [e8] at h8
  have hIS8 := is_exec hnM' hWM h8 hIS7
  rw [h8]
  have fr8 : ∀ r : SR, r.val < 16 ∨ 42 < r.val → sc8 r = σ.sc r := fun r hr => by
    rw [f8 r (not_mem_of_out _ (by decide) hr)]; exact fr5 r hr
  -- 9, 10: `lnil 7`, the first `k + 1` wires of `r2` into `7`
  have hsplit : r2.2.map (pos E ix) = (r2.2.take (k + 1)).map (pos E ix) ++
      (r2.2.drop (k + 1)).map (pos E ix) := by rw [← List.map_append, List.take_append_drop]
  obtain ⟨sc10, h10, f10⟩ := exec_takeC (E := E) (n := 3) (lA := 6) (lR := 7) (by decide)
    ((r2.2.take (k + 1)).map (pos E ix)) ((r2.2.drop (k + 1)).map (pos E ix)) []
    (exec E (.lnil 7) (setSL σ sc8 ls8)) (by exact (is_exec hnM' hWM (c := .lnil 7) rfl hIS8).1)
    (by show (Function.update ls8 7 []) 6 = _
        rw [Function.update_of_ne (by decide)]
        simp only [ls8, ls3, Function.update_self]; rw [List.nil_append, hsplit])
    (by simp [exec])
    (by simp [exec, setSL]; rw [fr8 3 (by decide), hc.2.2.1]; simp [hl2]) (by simp; omega)
  rw [exec_mk_noNand (.lnil 7) trivial, exec_mk_noNand (takeC 3 6 7)
    (by simp [NoNand, takeC]), h10]
  set τ9 := exec E (.lnil 7) (setSL σ sc8 ls8)
  set ls10 := Function.update (Function.update τ9.ls 6
    ((r2.2.drop (k + 1)).map (pos E ix))) 7 ([] ++ (r2.2.take (k + 1)).map (pos E ix))
  have e10 : ({ out := τ9.out, t := τ9.t, sc := sc10, ls := ls10, src := τ9.src } : St) =
      setSL σ sc10 ls10 := rfl
  rw [e10]
  have hIS10 : Inv E (mk E ix r2.1 (setSL σ sc10 ls10)) ∧ ScOK E (mk E ix r2.1 (setSL σ sc10 ls10)) :=
    is_exec hnM' hWM (c := .seq (.lnil 7) (takeC 3 6 7)) (τ := mk E ix r2.1 (setSL σ sc8 ls8))
      (by rw [exec_seq, exec_mk_noNand (.lnil 7) trivial, exec_mk_noNand (takeC 3 6 7)
        (by simp [NoNand, takeC]), h10, e10]) hIS8
  have fr10 : ∀ r : SR, r.val < 16 ∨ 42 < r.val → sc10 r = σ.sc r := fun r hr => by
    rw [f10 r (not_mem_of_out _ (by decide) hr)]; exact fr8 r hr
  -- 11, 12: the carry into `36`, `lnil 8`
  set w36 := r2.2.getD (k + 1) .one
  have hY : r2.2.drop (k + 1) = [w36] := by
    rw [List.drop_eq_getElem_cons (by omega), List.drop_of_length_le (by omega)]
    simp only [w36, List.getD_eq_getElem _ _ (show k + 1 < r2.2.length by omega)]
  set σ12 := setSL σ (Function.update sc10 36 (pos E ix w36)) (Function.update (Function.update
    ls10 6 []) 8 [])
  have e12 : exec E (.lnil 8) (exec E (.lpop 36 6) (mk E ix r2.1 (setSL σ sc10 ls10))) =
      mk E ix r2.1 σ12 := by
    rw [exec_mk_noNand (.lpop 36 6) trivial, exec_mk_noNand (.lnil 8) trivial]
    have h6 : ls10 6 = [pos E ix w36] := by simp [ls10, hY]
    simp only [exec, σ12, setSL, h6, List.headD_cons, List.tail_cons]
  have hIS12 := is_exec hnM' hWM (c := .seq (.lpop 36 6) (.lnil 8)) e12 hIS10
  rw [e12]
  -- 13: the mux
  have fr12 : ∀ r : SR, r.val < 16 ∨ 42 < r.val → σ12.sc r = σ.sc r := fun r hr => by
    simp only [σ12, setSL]
    rw [Function.update_of_ne (fun h => by subst h; revert hr; decide)]; exact fr10 r hr
  have hc12 : Consts E σ12 := ⟨by rw [← hc.1.1]; exact fr12 0 (by decide),
    by rw [← hc.1.2]; exact fr12 1 (by decide)⟩
  have hl12_3 : σ12.ls 3 = r1.2.map (pos E ix) := by
    simp [σ12, setSL, ls10, τ9, exec, ls8, ls3, σ7, ls5, σ4, ls3', Function.update_apply]
  obtain ⟨sc13, h13, f13⟩ := exec_muxLC (lA := 7) (lB := 3) (lR := 8) (n := 3) hnM' hWM hix
    (by decide) (by decide) (by decide) w36 (r2.2.take (k + 1)) r1.2 r2.1 σ12 []
    (by simp; omega) hc12 hIS12.1 hIS12.2 (by simp [σ12, setSL])
    (by simp [σ12, setSL, ls10, Function.update_apply]) hl12_3 (by simp [σ12, setSL])
    (by rw [fr12 3 (by decide), hc.2.2.1]; simp; omega) (by decide) (by simp; omega)
    hM
  set r3 := muxL w36 r2.1 (r2.2.take (k + 1)) r1.2
  have hl3 : r3.2.length = k + 1 := by rw [length_muxL_eq _ _ _ _ (by simp; omega)]; simp; omega
  set ls13 := ls3 σ12.ls 7 3 8 ([] ++ r3.2.map (pos E ix))
  have e13 : ({ σ12 with sc := sc13, ls := ls13 } : St) = setSL σ sc13 ls13 := rfl
  rw [e13] at h13
  have hIS13 := is_exec hnM' hWM h13 hIS12
  rw [h13]
  have fr13 : ∀ r : SR, r.val < 16 ∨ 42 < r.val → sc13 r = σ.sc r := fun r hr => by
    rw [f13 r (not_mem_of_out _ (by decide) hr)]; exact fr12 r hr
  -- 14, 15: `lnil 2`, the first `k` wires of `r3` into `2`
  obtain ⟨sc15, h15, f15⟩ := exec_takeC (E := E) (n := 2) (lA := 8) (lR := 2) (by decide)
    ((r3.2.take k).map (pos E ix)) ((r3.2.drop k).map (pos E ix)) []
    (exec E (.lnil 2) (setSL σ sc13 ls13)) (by exact (is_exec hnM' hWM (c := .lnil 2) rfl hIS13).1)
    (by show (Function.update ls13 2 []) 8 = _
        rw [Function.update_of_ne (by decide)]
        simp only [ls13, ls3, Function.update_self]
        rw [List.nil_append, ← List.map_append, List.take_append_drop])
    (by simp [exec])
    (by simp [exec, setSL]; rw [fr13 2 (by decide), hc.2.1]; simp; omega) (by simp; omega)
  rw [exec_mk_noNand (.lnil 2) trivial, exec_mk_noNand (takeC 2 8 2)
    (by simp [NoNand, takeC]), h15]
  refine ⟨sc15, _, rfl, by simp [modAdd, List.map_take]; rfl, fun r hr => ?_, fun l hl => ?_⟩
  · rw [f15 r (by simp; intro h; subst h; revert hr; decide)]; exact fr13 r hr
  · have h2 : l ≠ 2 := fun h => by subst h; revert hl; decide
    have h8 : l ≠ 8 := fun h => by subst h; revert hl; decide
    have h7 : l ≠ 7 := fun h => by subst h; revert hl; decide
    have h6 : l ≠ 6 := fun h => by subst h; revert hl; decide
    have h5 : l ≠ 5 := fun h => by subst h; revert hl; decide
    have h4 : l ≠ 4 := fun h => by subst h; revert hl; decide
    have h3 : l ≠ 3 := fun h => by subst h; revert hl; decide
    have h1 : l ≠ 1 := fun h => by subst h; revert hl; decide
    have h0 : l ≠ 0 := fun h => by subst h; revert hl; decide
    simp [exec, setSL, ls13, ls3, σ12, ls10, τ9, ls8, σ7, ls5, σ4, ls3', σ2, Function.update_apply,
      h0, h1, h2, h3, h4, h5, h6, h7, h8]

end FhatGen

end SigabaNeo.Lattices
