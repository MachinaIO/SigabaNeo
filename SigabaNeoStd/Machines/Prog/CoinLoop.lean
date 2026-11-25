import SigabaNeoStd.Machines.Prog.Stream
import SigabaNeoStd.Machines.Prog.Macros
import CslibFrontier.Probability.BitString

/-!
# Loops that draw coins

The fragment `NoGrow` has no coin. Here the laws of loops whose body is randomized:

* `law_loop_iter`: a loop whose body acts on an abstract state `a` by a random step `μ a` (with the
  counter left alone) has the law of `|counter|` steps of the Markov kernel `μ` (`kIter`).
* `coinsP : Prog 4` (tapes `0` the register, `1` a template of length `m`, `2` `3` scratch): draw
  `m` fair coins into the register. **`law_coinsP`**: `law coinsP s` is the image of
  `uniformList m` under `l ↦ Function.update s 0 l`.
* `law_seq_coins`: a program drawing coins followed by a program of the fragment `NoGrow` has the
  image of the coins' law under the pure semantics.
-/

namespace SigabaNeo.Tape

open Cslib Probability

variable {k : ℕ}

namespace Prog

open scoped Prog

/-! ### Iterated kernels -/

/-- `n` steps of a Markov kernel, the first step first. -/
noncomputable def kIter {σ : Type} (μ : σ → PMF σ) : ℕ → σ → PMF σ
  | 0, a => PMF.pure a
  | n + 1, a => (μ a).bind (kIter μ n)

/-- **Loops with a random body on an abstract state.** -/
theorem law_loop_iter {σ : Type} (i : Fin k) (body : Prog k) (G : σ → Store k) (μ : σ → PMF σ)
    (hstep : ∀ a w, law body (Function.update (G a) i w) =
      (μ a).map (fun a' => Function.update (G a') i w)) :
    ∀ (w : List Bool) (a : σ), law (loop i body) (Function.update (G a) i w) =
      (kIter μ w.length a).map (fun a' => Function.update (G a') i []) := by
  have key : ∀ (w : List Bool) (a : σ),
      ProbComp.eval (OracleComp.iterate w.length (fun t => denote body (tailAt i t))
        (Function.update (G a) i w)) =
      (kIter μ w.length a).map (fun a' => Function.update (G a') i []) := by
    intro w
    induction w with
    | nil =>
      intro a
      simp [kIter, OracleComp.iterate]
    | cons x w ih =>
      intro a
      rw [List.length_cons, OracleComp.iterate_succ_bind, ProbComp.eval_bind]
      have h1 : ProbComp.eval (denote body (tailAt i (Function.update (G a) i (x :: w)))) =
          (μ a).map (fun a' => Function.update (G a') i w) := by
        rw [tailAt, Function.update_self, Function.update_idem]
        exact hstep a w
      rw [h1, PMF.bind_map, kIter, PMF.map_bind]
      congr 1
      funext a'
      exact ih a'
  intro w a
  have := key w a
  rw [law, denote, Function.update_self]
  exact this

/-! ### Drawing coins -/

/-- One round: a coin on tape `3`, shifted into the register `0`. -/
def coinBody : Prog 4 := coin 3 ⨾ push 0 3 ⨾ clr 3

/-- **`m = |s 1|` fair coins into the register `0`.** -/
def coinsP : Prog 4 := cp 0 1 ⨾ forN 2 1 coinBody

theorem law_coinBody (s : Store 4) (h3 : s 3 = []) :
    law coinBody s = (PMF.uniformOfFintype Bool).map
      (fun b => Function.update s 0 ((s 0 ++ [b]).tail)) := by
  have hrest : ∀ b : Bool, law (push 0 3 ⨾ clr 3) (Function.update s 3 [b]) =
      PMF.pure (Function.update s 0 ((s 0 ++ [b]).tail)) := by
    intro b
    rw [law_eq_run _ (by rfl)]
    congr 1
    funext t
    fin_cases t <;> simp [h3, hd]
  rw [coinBody, law_seq, law, denote, ProbComp.eval_map, ProbComp.eval_uniform, PMF.bind_map]
  simp only [Function.comp_def, hrest]
  exact PMF.bind_pure_comp _ _

/-- The register after `m` shifted coins. -/
theorem kIter_coins (m : ℕ) : ∀ r : List Bool,
    kIter (fun r => (PMF.uniformOfFintype Bool).map (fun b => (r ++ [b]).tail)) m r =
      (BitString.uniformList m).map (fun l => (r ++ l).drop m) := by
  induction m with
  | zero => intro r; simp [kIter]
  | succ m ih =>
    intro r
    rw [kIter, BitString.uniformList_succ, PMF.bind_map, PMF.map_bind]
    congr 1
    funext b
    rw [Function.comp_apply, ih, PMF.map_comp]
    congr 1
    funext l
    simp only [Function.comp_apply]
    rw [← List.drop_one, ← List.drop_append_of_le_length (show 1 ≤ (r ++ [b]).length by simp),
      List.drop_drop, List.append_assoc, List.singleton_append, Nat.add_comm]

/-- **The law of `coinsP`**: `|s 1|` fair coins on tape `0`. -/
theorem law_coinsP (s : Store 4) (h2 : s 2 = []) (h3 : s 3 = []) :
    law coinsP s = (BitString.uniformList (s 1).length).map (fun l => Function.update s 0 l) := by
  let μ : List Bool → PMF (List Bool) :=
    fun r => (PMF.uniformOfFintype Bool).map (fun b => (r ++ [b]).tail)
  have hloop := law_loop_iter (2 : Fin 4) coinBody (fun r => Function.update s 0 r) μ (by
    intro r w
    rw [law_coinBody _ (by simp [h3]), PMF.map_comp]
    congr 1
    funext b
    funext t
    fin_cases t <;> simp)
  have e1 : law (cp 0 1) s = PMF.pure (Function.update s 0 (s 1)) := law_prim _ _
  have e2 : law (cp 2 1) (Function.update s 0 (s 1)) =
      PMF.pure (Function.update (Function.update s 0 (s 1)) 2 (s 1)) := by
    rw [law_prim]; simp [Prim.apply]
  rw [coinsP, forN, law_seq_pure e1, law_seq_pure e2, hloop, kIter_coins, PMF.map_comp]
  congr 1
  funext l
  simp only [Function.comp_apply, List.drop_left]
  funext t
  fin_cases t <;> simp [h2]

/-! ### Drawing coins on any distinct tapes -/

/-- **`|s t|` fair coins into the register `r`** (counter `c`, coin `b`). -/
def coinsAt (r t c b : Fin k) : Prog k := cp r t ⨾ forN c t (coin b ⨾ push r b ⨾ clr b)

theorem law_coinsAt {r t c b : Fin k} (hrt : r ≠ t) (hrc : r ≠ c) (hrb : r ≠ b) (htc : t ≠ c)
    (hcb : c ≠ b) (s : Store k) (hc : s c = []) (hb : s b = []) :
    law (coinsAt r t c b) s =
      (BitString.uniformList (s t).length).map (fun l => Function.update s r l) := by
  let μ : List Bool → PMF (List Bool) :=
    fun x => (PMF.uniformOfFintype Bool).map (fun bit => (x ++ [bit]).tail)
  have hbody : ∀ x : Store k, x b = [] → law (coin b ⨾ push r b ⨾ clr b) x =
      (PMF.uniformOfFintype Bool).map (fun bit => Function.update x r ((x r ++ [bit]).tail)) := by
    intro x hx
    have hrest : ∀ bit : Bool, law (push r b ⨾ clr b) (Function.update x b [bit]) =
        PMF.pure (Function.update x r ((x r ++ [bit]).tail)) := by
      intro bit
      rw [law_eq_run _ (by rfl)]
      congr 1
      funext j
      simp only [run_seq, run_push, run_clear, Function.update_apply]
      by_cases hjb : j = b
      · subst hjb; simp [Ne.symm hrb, hx]
      · by_cases hjr : j = r
        · subst hjr; simp [hrb, hd]
        · simp [hjb, hjr]
    rw [law_seq, law, denote, ProbComp.eval_map, ProbComp.eval_uniform, PMF.bind_map]
    simp only [Function.comp_def, hrest]
    exact PMF.bind_pure_comp _ _
  have hloop := law_loop_iter c (coin b ⨾ push r b ⨾ clr b) (fun x => Function.update s r x) μ (by
    intro x w
    rw [hbody _ (by simp [Function.update_apply, Ne.symm hcb, Ne.symm hrb, hb]), PMF.map_comp]
    congr 1
    funext bit
    funext j
    simp only [Function.comp_apply, Function.update_apply]
    by_cases hjc : j = c
    · subst hjc; simp [hrc, Ne.symm hrc]
    · by_cases hjr : j = r
      · subst hjr; simp [hrc]
      · simp [hjc, hjr])
  have e1 : law (cp r t) s = PMF.pure (Function.update s r (s t)) := law_prim _ _
  have e2 : law (cp c t) (Function.update s r (s t)) =
      PMF.pure (Function.update (Function.update s r (s t)) c (s t)) := by
    rw [law_prim]; simp [Prim.apply, Function.update_apply, Ne.symm hrt]
  rw [coinsAt, forN, law_seq_pure e1, law_seq_pure e2, hloop, kIter_coins, PMF.map_comp]
  congr 1
  funext l
  simp only [Function.comp_apply, List.drop_left]
  funext j
  simp only [Function.update_apply]
  by_cases hjc : j = c
  · subst hjc; simp [Ne.symm hrc, hc]
  · simp [hjc]

theorem wf_coinsAt (r t c b : Fin k) (hc : c ≠ r) (hc' : c ≠ b) : (coinsAt r t c b).WF := by
  simp [coinsAt, forN, WF, Preserves, push, sin, Prim.writes, hc, hc', Ne.symm hc', Ne.symm hc]

/-! ### Bounds of the coin loop -/

theorem lenBound_coinBodyAt (r b : Fin k) :
    lenBound (coin b ⨾ push r b ⨾ clr b) = fun L => L + 1 := by
  funext L
  simp [lenBound, push, sin, Prim.grow]

theorem timeBound_coinBodyAt (r b : Fin k) (L : ℕ) :
    timeBound (coin b ⨾ push r b ⨾ clr b) L = 6 * L + 15 := by
  simp [timeBound, lenBound, push, sin, Prim.grow, Prim.pad]
  omega

theorem iterate_succ_eq (L : ℕ) : ∀ j, (fun L : ℕ => L + 1)^[j] L = L + j
  | 0 => rfl
  | j + 1 => by rw [Function.iterate_succ_apply', iterate_succ_eq L j]; rfl

theorem lenBound_coinsAt_le (r t c b : Fin k) (L : ℕ) : lenBound (coinsAt r t c b) L ≤ 2 * L := by
  have e : lenBound (coinsAt r t c b) L = iterMax (lenBound (coin b ⨾ push r b ⨾ clr b)) L := rfl
  rw [e, lenBound_coinBodyAt, iterMax]
  apply Finset.sup_le
  intro j hj
  rw [iterate_succ_eq]
  simp at hj
  omega

theorem timeBound_coinsAt_le (r t c b : Fin k) (L : ℕ) :
    timeBound (coinsAt r t c b) L ≤ 23 * (L + 1) ^ 2 := by
  have hsup : (Finset.range L).sup (fun j => roundTime (timeBound (coin b ⨾ push r b ⨾ clr b))
      ((lenBound (coin b ⨾ push r b ⨾ clr b))^[j] L)) ≤ 16 * L + 18 := by
    apply Finset.sup_le
    intro j hj
    rw [lenBound_coinBodyAt, iterate_succ_eq, roundTime, timeBound_coinBodyAt]
    simp at hj
    omega
  have e : timeBound (coinsAt r t c b) L = (2 * L + 3) + ((2 * L + 3) +
      (L * ((Finset.range L).sup (fun j => roundTime (timeBound (coin b ⨾ push r b ⨾ clr b))
        ((lenBound (coin b ⨾ push r b ⨾ clr b))^[j] L)) + 1) + 2)) := rfl
  rw [e]
  have h2 := Nat.mul_le_mul_left L (Nat.add_le_add_right hsup 1)
  nlinarith

theorem wf_coinsP : coinsP.WF :=
  wf_of_wfB (by decide)

/-- **Coins, then a program of the fragment**: the image of the coins' law under the pure
semantics. -/
theorem law_seq_noGrow (p q : Prog k) (hq : q.NoGrow) (s : Store k) :
    law (p ⨾ q) s = (law p s).map (run q) := by
  rw [law_seq, show law q = PMF.pure ∘ run q from funext fun t => law_eq_run q hq t]
  exact PMF.bind_pure_comp _ _

end Prog

end SigabaNeo.Tape
