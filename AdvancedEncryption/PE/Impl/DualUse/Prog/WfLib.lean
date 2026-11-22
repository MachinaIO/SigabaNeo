import PE.Impl.DualUse.Prog.KeyPTime
import PE.Impl.DualUse.Prog.KeyWfWords

/-!
# Loop helpers of the `W_f` block

Small coin-free tape programs (`Prog k`) used by the `W_f` block (`PE.Impl.DualUse.Prog.WfB`):

* `mvAppP src dst a c t`: move `|s t|` bits from the stream `src` to the end of `dst`
  (`run_mvAppP`);
* `appP dst src a b c`: `dst := dst ++ src`, `src` kept (`run_appP`);
* `padP dst c t V`: `dst := dst ++ replicate (|s t| · V) false` (`run_padP`).

Each comes with `CoinFree` and `WF`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog
open scoped SigabaNeo.Tape.Prog

set_option linter.unusedSimpArgs false

variable {k : ℕ}

/-! ### Moving a prefix of a stream -/

/-- Move `|s t|` bits of the stream `src` to the end of `dst` (scratch `a`, counter `c`). -/
def mvAppP (src dst a c t : Fin k) : Prog k := forN c t (stepF src dst a)

/-- The abstract round of `mvAppP`. -/
def mvAStep (x : List Bool × List Bool) : List Bool × List Bool := (x.1.tail, x.2 ++ x.1.take 1)

theorem mvAStep_iter : ∀ (n : ℕ) (x : List Bool × List Bool),
    mvAStep^[n] x = (x.1.drop n, x.2 ++ x.1.take n)
  | 0, x => by simp
  | n + 1, x => by
    rw [Function.iterate_succ_apply, mvAStep_iter n]
    simp only [mvAStep, List.drop_tail, List.append_assoc, take_one_append_take_tail]

theorem run_mvAppP {src dst a c t : Fin k} (h1 : src ≠ dst) (h2 : src ≠ a) (h3 : src ≠ c)
    (h4 : dst ≠ a) (h5 : dst ≠ c) (h6 : a ≠ c) (s : Store k) (ha : s a = []) (hc : s c = []) :
    run (mvAppP src dst a c t) s = Function.update (Function.update s src ((s src).drop (s t).length))
      dst (s dst ++ (s src).take (s t).length) := by
  let G : List Bool × List Bool → Store k := fun x =>
    Function.update (Function.update s src x.1) dst x.2
  have h := run_forN c t (stepF src dst a) G mvAStep (fun x w => by
      funext j
      simp only [G, stepF, mvAStep, run_seq, run_pop, run_prim, Prim.apply, run_clear,
        Function.update_apply]
      by_cases hj1 : j = a <;> by_cases hj2 : j = dst <;> by_cases hj3 : j = src <;>
        by_cases hj4 : j = c <;> simp_all [Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4,
          Ne.symm h5, Ne.symm h6]) (s src, s dst) s (by
      funext j
      simp only [G, Function.update_apply]
      by_cases hj2 : j = dst <;> by_cases hj3 : j = src <;> by_cases hj4 : j = c <;> simp_all)
  rw [mvAppP, h, mvAStep_iter]
  funext j
  simp only [G, Function.update_apply]
  by_cases hj2 : j = dst <;> by_cases hj3 : j = src <;> by_cases hj4 : j = c <;> simp_all

theorem coinFree_mvAppP (src dst a c t : Fin k) : (mvAppP src dst a c t).CoinFree := rfl

theorem wf_mvAppP {src dst a c t : Fin k} (h3 : src ≠ c) (h5 : dst ≠ c) (h6 : a ≠ c) :
    (mvAppP src dst a c t).WF :=
  ⟨trivial, ⟨trivial, trivial, trivial⟩, by
    simp [stepF, Preserves, Prim.writes, Ne.symm h3, Ne.symm h5, Ne.symm h6]⟩

/-! ### Appending a word -/

/-- `dst := dst ++ src`, `src` kept (scratch `a`, `b`, counter `c`). -/
def appP (dst src a b c : Fin k) : Prog k := cp a src ⨾ mvAppP a dst b c src

theorem run_appP {dst src a b c : Fin k} (h1 : a ≠ dst) (h2 : a ≠ b) (h3 : a ≠ c) (h4 : dst ≠ b)
    (h5 : dst ≠ c) (h6 : b ≠ c) (h7 : src ≠ a) (h8 : src ≠ dst)
    (s : Store k) (ha : s a = []) (hb : s b = []) (hc : s c = []) :
    run (appP dst src a b c) s = Function.update s dst (s dst ++ s src) := by
  rw [appP, run_seq, run_copy, run_mvAppP h1 h2 h3 h4 h5 h6 _
    (by simp [Function.update_apply, Ne.symm h2, hb]) (by simp [Function.update_apply, Ne.symm h3, hc])]
  funext j
  simp only [Function.update_apply]
  by_cases hj1 : j = dst <;> by_cases hj2 : j = a <;> simp_all [Ne.symm h7, Ne.symm h8]

theorem coinFree_appP (dst src a b c : Fin k) : (appP dst src a b c).CoinFree := rfl

theorem wf_appP {dst src a b c : Fin k} (h3 : a ≠ c) (h5 : dst ≠ c) (h6 : b ≠ c) :
    (appP dst src a b c).WF := ⟨trivial, wf_mvAppP h3 h5 h6⟩

/-! ### Padding -/

/-- `dst := dst ++ replicate (|s t| · V) false` (counter `c`, scratch `a`). -/
def padP (dst c t a : Fin k) (V : ℕ) : Prog k :=
  forN c t (SigabaNeo.Tape.Prog.putW a (List.replicate V false) ⨾ appendP dst a V ⨾ clr a)

theorem run_padP {dst c t a : Fin k} (h1 : dst ≠ c) (h2 : dst ≠ a) (h3 : c ≠ a)
    (V : ℕ) (s : Store k) (ha : s a = []) (hc : s c = []) :
    run (padP dst c t a V) s =
      Function.update s dst (s dst ++ List.replicate ((s t).length * V) false) := by
  let G : List Bool → Store k := fun x => Function.update s dst x
  have h := run_forN c t (SigabaNeo.Tape.Prog.putW a (List.replicate V false) ⨾ appendP dst a V ⨾ clr a) G
    (fun x => x ++ List.replicate V false) (fun x w => by
      funext j
      simp only [G, run_seq, SigabaNeo.Tape.Prog.run_putW, run_appendP h2, run_clear, Function.update_apply]
      by_cases hj1 : j = a <;> by_cases hj2 : j = dst <;> by_cases hj4 : j = c <;>
        simp_all [Ne.symm h1, Ne.symm h2, Ne.symm h3]) (s dst) s (by
      funext j
      simp only [G, Function.update_apply]
      by_cases hj2 : j = dst <;> by_cases hj4 : j = c <;> simp_all)
  rw [padP, h]
  have e : ∀ n (x : List Bool), (fun x => x ++ List.replicate V false)^[n] x =
      x ++ List.replicate (n * V) false := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', ih, List.append_assoc, ← List.replicate_add, Nat.succ_mul]
  rw [e]
  funext j
  simp only [G, Function.update_apply]
  by_cases hj2 : j = dst <;> by_cases hj4 : j = c <;> simp_all

theorem coinFree_appendP (i j : Fin k) : ∀ m, (appendP i j m).CoinFree
  | 0 => rfl
  | m + 1 => by
    simp only [CoinFree, appendP, coinFreeB, Bool.and_eq_true]
    exact ⟨trivial, trivial, coinFree_appendP i j m⟩

theorem wf_appendP (i j : Fin k) : ∀ m, (appendP i j m).WF
  | 0 => trivial
  | m + 1 => ⟨trivial, trivial, wf_appendP i j m⟩

theorem preserves_appendP {i j t : Fin k} (hi : i ≠ t) (hj : j ≠ t) : ∀ m, (appendP i j m).Preserves t
  | 0 => by simp [appendP, Preserves, Prim.writes, Ne.symm hi]
  | m + 1 => ⟨by simp [Preserves, Prim.writes, Ne.symm hi], by simp [Preserves, Prim.writes, Ne.symm hj],
      preserves_appendP hi hj m⟩

theorem preserves_putW {o t : Fin k} (h : o ≠ t) : ∀ w, (SigabaNeo.Tape.Prog.putW o w).Preserves t
  | [] => by simp [SigabaNeo.Tape.Prog.putW, Preserves, Prim.writes, Ne.symm h]
  | _ :: w => ⟨preserves_putW h w, by simp [Preserves, Prim.writes, Ne.symm h]⟩

theorem coinFree_padP (dst c t a : Fin k) (V : ℕ) : (padP dst c t a V).CoinFree := by
  simp only [CoinFree, padP, forN, coinFreeB, Bool.and_eq_true]
  exact ⟨trivial, SigabaNeo.Tape.Prog.coinFree_putW _ _, coinFree_appendP _ _ _, trivial⟩

theorem wf_padP {dst c t a : Fin k} (h1 : dst ≠ c) (h3 : c ≠ a) (V : ℕ) : (padP dst c t a V).WF :=
  ⟨trivial, ⟨SigabaNeo.Tape.Prog.wf_putW _ _, wf_appendP _ _ _, trivial⟩,
    ⟨preserves_putW (Ne.symm h3) _, preserves_appendP h1 (Ne.symm h3) _, by
      simp [Preserves, Prim.writes, h3]⟩⟩

end AdvancedEncryption.DualUse.Prog
