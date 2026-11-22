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

theorem law_prim (p : Prim k) (s : Store k) : (prog (.prim p)).law s = PMF.pure (p.apply s) := by
  simp [law, denote, Prog.denote]

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


/-! ### Append laws -/

/-- The values `a`, `b` on the tapes `0`, `1`, `d` on the others (the components' layout). -/
def ioS {R : ℕ} {α : Type} (a b d : α) : Fin (R + 2) → α :=
  fun j => if j.val = 0 then a else if j.val = 1 then b else d

/-- **`p` appends a random word from `μ` to the tape `r`** on the stores satisfying `P`, and
changes nothing else. -/
def AppendLaw (p : XProg k) (r : Fin k) (P : Store k → Prop) (μ : PMF (List Bool)) : Prop :=
  ∀ s, P s → p.law s = μ.map fun u => Function.update s r (s r ++ u)

/-- **Two appends in a row** append the concatenation of independent words. -/
theorem AppendLaw.seq {p q : XProg k} {r : Fin k} {P : Store k → Prop} {μ ν : PMF (List Bool)}
    (hp : AppendLaw p r P μ) (hq : AppendLaw q r P ν)
    (hP : ∀ s w, P s → P (Function.update s r w)) :
    AppendLaw (XProg.seq p q) r P (cat μ ν) := by
  intro s hs
  rw [law_seq, hp s hs, PMF.bind_map, cat, PMF.map_bind]
  congr 1
  funext u
  simp only [Function.comp_apply]
  rw [hq _ (hP s _ hs), PMF.map_comp]
  congr 1
  funext v
  simp [List.append_assoc]

/-- An append law on fewer stores, or along an equal law. -/
theorem AppendLaw.mono {p : XProg k} {r : Fin k} {P Q : Store k → Prop} {μ ν : PMF (List Bool)}
    (h : AppendLaw p r P μ) (hQ : ∀ s, Q s → P s) (hμ : μ = ν) : AppendLaw p r Q ν :=
  fun s hs => hμ ▸ h s (hQ s hs)

theorem kIter_append (μ : PMF (List Bool)) : ∀ (n : ℕ) (a : List Bool),
    kIter (fun a => μ.map fun u => a ++ u) n a = (catPow μ n).map fun u => a ++ u
  | 0, a => by simp [kIter]
  | n + 1, a => by
    rw [kIter, kIter_append μ n a, catPow_succ, PMF.bind_map, PMF.map_bind]
    congr 1
    funext u
    simp only [Function.comp_apply, PMF.map_comp]
    congr 1
    funext v
    simp [List.append_assoc]

/-- **`n` rounds of an append** append `n` independent words. -/
theorem AppendLaw.forN {body : XProg k} {r c t : Fin k} {P : Store k → Prop}
    {μ : PMF (List Bool)} {n : ℕ} (hb : AppendLaw body r P μ)
    (hPr : ∀ s w, P s → P (Function.update s r w)) (hPc : ∀ s w, P s → P (Function.update s c w))
    (hcr : c ≠ r) :
    AppendLaw (forN c t body) r (fun s => P s ∧ s c = [] ∧ (s t).length = n) (catPow μ n) := by
  rintro s ⟨hs, hc, hn⟩
  rw [XProg.forN, law_seq, law_prog_run (.prim (.copy c t)) rfl, PMF.pure_bind]
  simp only [Prog.run_copy]
  let G : List Bool → Store k := fun a => Function.update s r a
  have hstart : Function.update s c (s t) = Function.update (G (s r)) c (s t) := by
    simp [G]
  rw [hstart, law_loop_iter c body G (fun a => μ.map fun u => a ++ u)]
  · rw [kIter_append, hn, PMF.map_comp]
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

/-- A deterministic program appending a fixed word. -/
theorem AppendLaw.pure {p : XProg k} {r : Fin k} {P : Store k → Prop} (u : List Bool)
    (h : ∀ s, P s → p.law s = PMF.pure (Function.update s r (s r ++ u))) :
    AppendLaw p r P (PMF.pure u) := fun s hs => by rw [h s hs, PMF.pure_map]

/-! ### Appending fair bits and constant bits -/

/-- Flip a coin onto tape `b` and append it to `r`. -/
def coinAp (r b : Fin k) : XProg k :=
  seq (prog (.coin b)) (prog (.seq (.prim (.snocHead r b)) (.prim (.clear b))))

/-- **One fair bit.** -/
theorem appendLaw_coinAp {r b : Fin k} (hrb : r ≠ b) :
    AppendLaw (coinAp r b) r (fun s => s b = []) (BitString.uniformList 1) := by
  intro s hs
  rw [coinAp, law_seq, law_coin, PMF.bind_map, uniformList_one, PMF.map_comp]
  simp only [Function.comp_def, law_prog, Prog.law, Prog.denote, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.pure_bind]
  rw [show ∀ f : Bool → Store k, (PMF.uniformOfFintype Bool).bind (fun x => PMF.pure (f x)) =
    (PMF.uniformOfFintype Bool).map f from fun f => PMF.bind_pure_comp f _]
  congr 1
  funext x
  simp only [Prim.apply, Function.update_self, Function.update_of_ne hrb, List.take_one,
    List.head?_cons, Option.toList_some]
  rw [Function.update_comm hrb, Function.update_idem,
    (Function.update_eq_self_iff (f := s) (a := b)).mpr hs.symm]

/-- Append the bit `b`. -/
def bitAp (r : Fin k) (b : Bool) : XProg k := prog (.prim (.snoc r b))

theorem appendLaw_bitAp (r : Fin k) (b : Bool) (P : Store k → Prop) :
    AppendLaw (bitAp r b) r P (PMF.pure [b]) :=
  AppendLaw.pure [b] fun s _ => law_prim _ s

/-- **`n` fair bits** appended to `r` (`|s t| = n`). -/
theorem appendLaw_coins {r b c t : Fin k} (hrb : r ≠ b) (hcr : c ≠ r) (hcb : c ≠ b) (n : ℕ) :
    AppendLaw (forN c t (coinAp r b)) r (fun s => s b = [] ∧ s c = [] ∧ (s t).length = n)
      (BitString.uniformList n) := by
  have h := AppendLaw.forN (t := t) (n := n) (appendLaw_coinAp hrb)
    (fun s w hs => by rwa [Function.update_of_ne hrb.symm])
    (fun s w hs => by rwa [Function.update_of_ne hcb.symm]) hcr
  rw [catPow_uniformList, Nat.mul_one] at h
  exact h

/-- **`n` copies of the bit `v`** appended to `r` (`|s t| = n`). -/
theorem appendLaw_bits {r c t : Fin k} (hcr : c ≠ r) (v : Bool) (n : ℕ) (P : Store k → Prop)
    (hPr : ∀ s w, P s → P (Function.update s r w)) (hPc : ∀ s w, P s → P (Function.update s c w)) :
    AppendLaw (forN c t (bitAp r v)) r (fun s => P s ∧ s c = [] ∧ (s t).length = n)
      (PMF.pure (List.replicate n v)) := by
  have h := AppendLaw.forN (t := t) (n := n) (appendLaw_bitAp r v P) hPr hPc hcr
  have e : ∀ m, catPow (PMF.pure [v]) m = PMF.pure (List.replicate m v) := by
    intro m; induction m with
    | zero => rfl
    | succ m ih => rw [catPow_succ, ih, PMF.pure_bind, PMF.pure_map, List.replicate_succ']
  rwa [e] at h

/-! ### Counters from nothing -/

/-- Double the all-`false` word on tape `t` (counter `c`). -/
def dblP (t c : Fin k) : XProg k := forN c t (bitAp t false)

/-- `t := replicate n false` (from a blank `t`), by doubling along the bits of `n`. -/
def natP (t c : Fin k) : ℕ → XProg k
  | 0 => prog (.prim (.clear t))
  | n + 1 =>
    if h : (n + 1) % 2 = 0 then seq (natP t c ((n + 1) / 2)) (dblP t c)
    else seq (seq (natP t c ((n + 1) / 2)) (dblP t c)) (bitAp t false)
  decreasing_by all_goals omega

theorem law_dblP {t c : Fin k} (hct : c ≠ t) (s : Store k) (hc : s c = []) (m : ℕ)
    (ht : s t = List.replicate m false) :
    (dblP t c).law s = PMF.pure (Function.update s t (List.replicate (m + m) false)) := by
  -- the loop body appends `false` to `t`, so tape `t` is the counter's template and register
  rw [dblP, XProg.forN, law_seq, law_prog_run (.prim (.copy c t)) rfl, PMF.pure_bind]
  simp only [Prog.run_copy]
  let G : List Bool → Store k := fun a => Function.update s t a
  have hstart : Function.update s c (s t) = Function.update (G (s t)) c (s t) := by simp [G]
  rw [hstart, law_loop_iter c (bitAp t false) G (fun a => PMF.pure (a ++ [false]))]
  · have hk : ∀ j a, kIter (fun a => PMF.pure (a ++ [false])) j a =
        PMF.pure (a ++ List.replicate j false) := by
      intro j; induction j with
      | zero => intro a; simp [kIter]
      | succ j ih => intro a; rw [kIter, ih, PMF.pure_bind, List.replicate_succ', List.append_assoc]
    rw [hk, PMF.pure_map, ht, List.length_replicate, List.replicate_add]
    simp only [G]
    congr 1
    exact (Function.update_eq_self_iff).mpr (by rw [Function.update_of_ne hct]; exact hc.symm)
  · intro a w
    rw [bitAp, law_prim, PMF.pure_map]
    congr 1
    simp only [G, Prim.apply, Function.update_of_ne hct.symm, Function.update_self]
    rw [Function.update_comm hct.symm, Function.update_idem]
    exact Function.update_comm hct _ _ _

/-- **The counter `replicate n false`.** -/
theorem law_natP {t c : Fin k} (hct : c ≠ t) : ∀ (n : ℕ) (s : Store k), s c = [] →
    (natP t c n).law s = PMF.pure (Function.update s t (List.replicate n false))
  | 0, s, _ => by rw [natP, law_prim]; rfl
  | n + 1, s, hc => by
    have ih := law_natP hct ((n + 1) / 2) s hc
    have hc' : Function.update s t (List.replicate ((n + 1) / 2) false) c = [] := by
      rw [Function.update_of_ne hct]; exact hc
    rw [natP]
    split_ifs with h
    · rw [law_seq, ih, PMF.pure_bind, law_dblP hct _ hc' ((n + 1) / 2) (by simp), Function.update_idem]
      congr 3; omega
    · rw [law_seq, law_seq, ih, PMF.pure_bind, law_dblP hct _ hc' ((n + 1) / 2) (by simp),
        Function.update_idem, PMF.pure_bind, bitAp, law_prim]
      congr 1
      simp only [Prim.apply, Function.update_self, Function.update_idem,
        ← List.replicate_succ']
      congr 2; omega

end XProg

end SigabaNeo.Tape
