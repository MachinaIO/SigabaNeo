import SigabaNeo.Lib.Machines.Prog.Frame
import SigabaNeo.Lib.Machines.Prog.Stream
import SigabaNeo.Lib.Encode.Laws

/-!
# Sampling programs: laws of framed programs with coins

The laws of `XProg` programs that flip coins, compositionally:

* `law_seq`, `law_prog`, `law_prog_run`, `law_coin`, `law_frame`: the law of each construct;
* `law_loop_iter`: a loop whose body acts on an abstract state by a kernel `K` (the counter left
  alone) runs the iterated kernel `kIter K` once per bit of its counter;
* **shift laws** (`ShiftLaw p r P μ m`): on the stores satisfying `P`, `p` shifts a random word
  drawn from `μ` (of `m` bits) in at the end of the register `r` (`r := (r ++ u).drop m`) and
  changes nothing else. Shift laws compose: `ShiftLaw.seq` (the words concatenate, independent),
  `ShiftLaw.forN` (`n` rounds: `catPow μ n`);
* `coinSh r b`: one fair bit (`uniformList 1`); `coinsP r b c t`: `|s t|` fair bits
  (`uniformList |s t|`, `shiftLaw_coinsP`).

A register of width `n` (initialised from a template of length `n`) into which `n` bits are
shifted holds exactly those bits, so a sampler writes a fixed-length encoding of its sample.
-/

namespace SigabaNeo.Tape

open Cslib Cslib.Probability SigabaNeo.Encode

variable {k : ℕ}

namespace XProg

/-! ### The law of each construct -/

theorem law_seq (p q : XProg k) (s : Store k) : (seq p q).law s = (p.law s).bind q.law := by
  simp only [law, denote, ProbComp.eval_bind]
  rfl

theorem law_prog (p : Prog k) (s : Store k) : (prog p).law s = p.law s := rfl

theorem law_prog_run (p : Prog k) (hp : p.NoGrow) (s : Store k) :
    (prog p).law s = PMF.pure (p.run s) := Prog.law_eq_run p hp s

theorem law_coin (i : Fin k) (s : Store k) :
    (prog (.coin i)).law s = (PMF.uniformOfFintype Bool).map fun b => Function.update s i [b] := by
  simp [law, denote, Prog.denote]

theorem law_frame {m : ℕ} (e : Fin m ↪ Fin k) (p : XProg m) (s : Store k) :
    (frame e p).law s = (p.law (fun j => s (e j))).map (embedF e s) := by
  simp [law, denote]

/-! ### Loops -/

/-- The kernel `K` iterated `n` times. -/
noncomputable def kIter {σ : Type} (K : σ → PMF σ) : ℕ → σ → PMF σ
  | 0, a => PMF.pure a
  | n + 1, a => (kIter K n a).bind K

/-- **Loops with a randomized body acting on an abstract state.** -/
theorem law_loop_iter {σ : Type} (i : Fin k) (body : XProg k) (G : σ → Store k) (K : σ → PMF σ)
    (h : ∀ a w, body.law (Function.update (G a) i w) =
      (K a).map fun a' => Function.update (G a') i w)
    (a : σ) (w : List Bool) :
    (loop i body).law (Function.update (G a) i w) =
      (kIter K w.length a).map fun a' => Function.update (G a') i [] := by
  have key : ∀ j, ProbComp.eval (OracleComp.iterate j (fun t => denote body (tailAt i t))
      (Function.update (G a) i w)) =
      (kIter K j a).map fun a' => Function.update (G a') i (w.drop j) := by
    intro j
    induction j with
    | zero => simp [kIter]
    | succ j ih =>
      rw [OracleComp.iterate_succ, ProbComp.eval_bind, ih, kIter, PMF.bind_map, PMF.map_bind]
      congr 1
      funext a'
      simp only [Function.comp_apply, tailAt, Function.update_self, Function.update_idem]
      have := h a' (w.drop j).tail
      simp only [law] at this
      rw [this, List.tail_drop]
  show ProbComp.eval (denote (loop i body) (Function.update (G a) i w)) = _
  simp only [denote, Function.update_self]
  rw [key, List.drop_length]

/-! ### Shift laws -/

/-- **`p` shifts a random word from `μ` (of `m` bits) into the register `r`** on the stores
satisfying `P`, and changes nothing else. -/
def ShiftLaw (p : XProg k) (r : Fin k) (P : Store k → Prop) (μ : PMF (List Bool)) (m : ℕ) :
    Prop :=
  ∀ s, P s → p.law s = μ.map fun u => Function.update s r ((s r ++ u).drop m)

/-- Every word of `μ` has `m` bits. -/
def LenSupp (μ : PMF (List Bool)) (m : ℕ) : Prop := ∀ u ∈ μ.support, u.length = m

theorem drop_shift {a u v : List Bool} {m m' : ℕ} (hu : u.length = m) :
    ((a ++ u).drop m ++ v).drop m' = (a ++ (u ++ v)).drop (m + m') := by
  rw [← List.drop_append_of_le_length (l₂ := v) (show m ≤ (a ++ u).length by simp [hu]),
    List.drop_drop, List.append_assoc, Nat.add_comm]

/-- **Two shifts in a row** shift the concatenation of independent words. -/
theorem ShiftLaw.seq {p q : XProg k} {r : Fin k} {P : Store k → Prop} {μ ν : PMF (List Bool)}
    {m m' : ℕ} (hp : ShiftLaw p r P μ m) (hq : ShiftLaw q r P ν m')
    (hP : ∀ s w, P s → P (Function.update s r w)) (hμ : LenSupp μ m) :
    ShiftLaw (XProg.seq p q) r P (μ.bind fun u => ν.map (u ++ ·)) (m + m') := by
  intro s hs
  rw [law_seq, hp s hs, PMF.bind_map, PMF.map_bind]
  refine PMF.bind_congr_on_support _ _ _ fun u hu => ?_
  simp only [Function.comp_apply]
  rw [hq _ (hP s _ hs), PMF.map_comp]
  congr 1
  funext v
  simp only [Function.comp_apply, Function.update_self, Function.update_idem]
  rw [drop_shift (hμ u hu)]

theorem lenSupp_bind {μ ν : PMF (List Bool)} {m m' : ℕ} (hμ : LenSupp μ m) (hν : LenSupp ν m') :
    LenSupp (μ.bind fun u => ν.map (u ++ ·)) (m + m') := by
  intro w hw
  rw [PMF.mem_support_bind_iff] at hw
  obtain ⟨u, hu, hw⟩ := hw
  rw [PMF.mem_support_map_iff] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  rw [List.length_append, hμ u hu, hν v hv]

theorem lenSupp_catPow {μ : PMF (List Bool)} {m : ℕ} (hμ : LenSupp μ m) (n : ℕ) :
    LenSupp (catPow μ n) (n * m) := length_of_mem_support_catPow hμ n

theorem lenSupp_uniformList (n : ℕ) : LenSupp (BitString.uniformList n) n :=
  fun _ h => BitString.length_of_mem_support_uniformList h

theorem lenSupp_map {μ : PMF (List Bool)} {m n : ℕ} (f : List Bool → List Bool)
    (hf : ∀ u, u.length = m → (f u).length = n) (hμ : LenSupp μ m) : LenSupp (μ.map f) n := by
  intro w hw
  rw [PMF.mem_support_map_iff] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  exact hf u (hμ u hu)

/-- The iterated shift kernel. -/
theorem kIter_shift {μ : PMF (List Bool)} {m : ℕ} (hμ : LenSupp μ m) : ∀ (n : ℕ) (a : List Bool),
    kIter (fun a => μ.map fun u => (a ++ u).drop m) n a =
      (catPow μ n).map fun u => (a ++ u).drop (n * m)
  | 0, a => by simp [kIter]
  | n + 1, a => by
    rw [kIter, kIter_shift hμ n a, catPow_succ, PMF.bind_map, PMF.map_bind]
    refine PMF.bind_congr_on_support _ _ _ fun u hu => ?_
    simp only [Function.comp_apply]
    rw [PMF.map_comp]
    congr 1
    funext v
    simp only [Function.comp_apply]
    rw [drop_shift (lenSupp_catPow hμ n u hu), Nat.succ_mul]

/-- `for i < |s t|: body` with the counter on tape `c`. -/
def forN (c t : Fin k) (body : XProg k) : XProg k :=
  seq (prog (.prim (.copy c t))) (loop c body)

/-- **`n` rounds of a shift** shift `n` independent words. -/
theorem ShiftLaw.forN {body : XProg k} {r c t : Fin k} {P : Store k → Prop} {μ : PMF (List Bool)}
    {m n : ℕ} (hb : ShiftLaw body r P μ m) (hPr : ∀ s w, P s → P (Function.update s r w))
    (hPc : ∀ s w, P s → P (Function.update s c w)) (hμ : LenSupp μ m) (hcr : c ≠ r) :
    ShiftLaw (forN c t body) r (fun s => P s ∧ s c = [] ∧ (s t).length = n) (catPow μ n)
      (n * m) := by
  rintro s ⟨hs, hc, hn⟩
  rw [XProg.forN, law_seq, law_prog_run (.prim (.copy c t)) rfl, PMF.pure_bind]
  simp only [Prog.run_copy]
  let G : List Bool → Store k := fun a => Function.update s r a
  have hstart : Function.update s c (s t) = Function.update (G (s r)) c (s t) := by
    simp [G]
  rw [hstart, law_loop_iter c body G (fun a => μ.map fun u => (a ++ u).drop m)]
  · rw [kIter_shift hμ, hn, PMF.map_comp]
    congr 1
    funext u
    simp only [Function.comp_apply, G]
    rw [Function.update_eq_self_iff.mpr (by rw [Function.update_of_ne hcr]; exact hc.symm)]
  · intro a w
    rw [hb _ (hPc _ w (hPr s a hs)), PMF.map_comp]
    congr 1
    funext u
    simp only [Function.comp_apply, G, Function.update_of_ne hcr.symm, Function.update_self]
    rw [Function.update_comm hcr.symm, Function.update_idem]
    exact Function.update_comm hcr _ _ _

/-! ### Fair bits -/

/-- Flip a coin onto tape `b` and shift it into the register `r`. -/
def coinSh (r b : Fin k) : XProg k :=
  seq (prog (.coin b)) (prog (.seq (Prog.push r b) (.prim (.clear b))))

theorem uniformList_one :
    BitString.uniformList 1 = (PMF.uniformOfFintype Bool).map fun b => [b] := by
  rw [BitString.uniformList_succ, BitString.uniformList_zero]
  simp only [PMF.pure_map]
  rfl

/-- **One fair bit.** -/
theorem shiftLaw_coinSh {r b : Fin k} (hrb : r ≠ b) :
    ShiftLaw (coinSh r b) r (fun s => s b = []) (BitString.uniformList 1) 1 := by
  intro s hs
  rw [coinSh, law_seq, law_coin, PMF.bind_map, uniformList_one, PMF.map_comp]
  simp only [Function.comp_def]
  rw [show (fun x => (prog (.seq (Prog.push r b) (.prim (.clear b)))).law
      (Function.update s b [x])) = fun x => PMF.pure ((Prog.seq (Prog.push r b)
        (.prim (.clear b))).run (Function.update s b [x])) from
    funext fun x => law_prog_run (.seq (Prog.push r b) (.prim (.clear b))) rfl _]
  rw [show ∀ f : Bool → Store k, (PMF.uniformOfFintype Bool).bind (fun x => PMF.pure (f x)) =
    (PMF.uniformOfFintype Bool).map f from fun f => PMF.bind_pure_comp f _]
  congr 1
  funext x
  simp only [Prog.run_seq, Prog.run_push, Prog.run_clear, Function.update_self,
    Function.update_of_ne hrb, hd, List.headD_cons]
  rw [Function.update_comm hrb, Function.update_idem,
    (Function.update_eq_self_iff (f := s) (a := b)).mpr hs.symm, List.drop_one]

theorem lenSupp_one : LenSupp (BitString.uniformList 1) 1 := lenSupp_uniformList 1

/-- `|s t|` fair bits shifted into `r` (coin tape `b`, counter `c`). -/
def coinsP (r b c t : Fin k) : XProg k := forN c t (coinSh r b)

/-- **`n` fair bits**: `|s t| = n` uniform bits shifted into the register `r`. -/
theorem shiftLaw_coinsP {r b c t : Fin k} (hrb : r ≠ b) (hcr : c ≠ r) (hcb : c ≠ b) (n : ℕ) :
    ShiftLaw (coinsP r b c t) r (fun s => s b = [] ∧ s c = [] ∧ (s t).length = n)
      (BitString.uniformList n) n := by
  have h := ShiftLaw.forN (t := t) (n := n) (shiftLaw_coinSh hrb)
    (fun s w hs => by rwa [Function.update_of_ne hrb.symm])
    (fun s w hs => by rwa [Function.update_of_ne hcb.symm]) lenSupp_one hcr
  rw [catPow_uniformList, Nat.mul_one] at h
  exact h

end XProg

end SigabaNeo.Tape
