import SigabaNeoStd.Machines.Prog.Frame

/-!
# Cost certificate of `mid`, phase M1 (generic): programs that avoid a set of tapes

A tape program that never mentions the tapes of a set `S` (`c1XAv S p`) carries their static
length bounds through unchanged, and pays at most a factor `V + 1` in time when those bounds are
`≤ V` (the column machine of each primitive sweeps every tape, so `supB` grows by at most `V`):

* **`c1X_len`**: `lenBoundT p (c1Mix S ℓ g) = c1Mix S (lenBoundT p ℓ) g`;
* **`c1X_time`**: `(∀ t, S t → g t ≤ V) → timeBoundT p (c1Mix S ℓ g) ≤ (V + 1) * timeBoundT p ℓ`,

where `c1Mix S ℓ g` is `g` on `S` and `ℓ` elsewhere. Used for the parked stash of
`RedKeyMid.ringIOS` while `preP` builds the templates.
-/

set_option linter.unusedSectionVars false

namespace SigabaNeo.Tape.XProg.Avoid
open SigabaNeo SigabaNeo.Tape

variable {k : ℕ}

/-- `g` on the tapes of `S`, `ℓ` elsewhere. -/
def c1Mix (S : Fin k → Prop) [DecidablePred S] (ℓ g : Fin k → ℕ) : Fin k → ℕ :=
  fun t => if S t then g t else ℓ t

/-- The primitive never mentions a tape of `S`. -/
def c1PrimAv (S : Fin k → Prop) : Prim k → Prop
  | .clear i | .tail i | .cons i _ | .snoc i _ => ¬ S i
  | .copy i j | .carry _ i j | .pop i j | .consHead i j | .snocHead i j => ¬ S i ∧ ¬ S j
  | .eq i j f => ¬ S i ∧ ¬ S j ∧ ¬ S f

/-- The program never mentions a tape of `S`. -/
def c1ProgAv (S : Fin k → Prop) : Prog k → Prop
  | .prim p => c1PrimAv S p
  | .coin i => ¬ S i
  | .seq p q => c1ProgAv S p ∧ c1ProgAv S q
  | .ifBlank _ p q => c1ProgAv S p ∧ c1ProgAv S q
  | .ifBit _ p q => c1ProgAv S p ∧ c1ProgAv S q
  | .loop i body => ¬ S i ∧ c1ProgAv S body

/-- The framed program never mentions a tape of `S`. -/
def c1XAv : {k : ℕ} → (Fin k → Prop) → XProg k → Prop
  | _, S, .prog p => c1ProgAv S p
  | _, S, .frame e _ => ∀ j, ¬ S (e j)
  | _, S, .seq p q => c1XAv S p ∧ c1XAv S q
  | _, S, .ifBlank _ p q => c1XAv S p ∧ c1XAv S q
  | _, S, .ifBit _ p q => c1XAv S p ∧ c1XAv S q
  | _, S, .loop i body => ¬ S i ∧ c1XAv S body

section

variable (S : Fin k → Prop) [DecidablePred S]

theorem c1Mix_of (ℓ g : Fin k → ℕ) {t : Fin k} (h : S t) : c1Mix S ℓ g t = g t := by
  simp [c1Mix, h]

theorem c1Mix_off (ℓ g : Fin k → ℕ) {t : Fin k} (h : ¬ S t) : c1Mix S ℓ g t = ℓ t := by
  simp [c1Mix, h]

theorem c1Mix_update (ℓ g : Fin k → ℕ) (i : Fin k) (hi : ¬ S i) (v : ℕ) :
    Function.update (c1Mix S ℓ g) i v = c1Mix S (Function.update ℓ i v) g := by
  funext t
  by_cases ht : t = i
  · subst ht; simp [c1Mix, hi]
  · by_cases hs : S t <;> simp [c1Mix, hs, Function.update_of_ne ht]

theorem c1Mix_tailB (ℓ g : Fin k → ℕ) (i : Fin k) (hi : ¬ S i) :
    tailB i (c1Mix S ℓ g) = c1Mix S (tailB i ℓ) g := by
  rw [tailB, c1Mix_update S ℓ g i hi, c1Mix_off S ℓ g hi]; rfl

theorem c1Prim_len (p : Prim k) (hp : c1PrimAv S p) (ℓ g : Fin k → ℕ) :
    p.lenT (c1Mix S ℓ g) = c1Mix S (p.lenT ℓ) g := by
  cases p with
  | clear i => exact c1Mix_update S ℓ g i hp 0
  | copy i j =>
    show Function.update _ i _ = _
    rw [c1Mix_off S ℓ g hp.2, c1Mix_update S ℓ g i hp.1]; rfl
  | carry f i j => rfl
  | tail i =>
    show Function.update _ i _ = _
    rw [c1Mix_off S ℓ g hp, c1Mix_update S ℓ g i hp]; rfl
  | pop i j =>
    show Function.update (Function.update _ i _) j _ = _
    rw [c1Mix_off S ℓ g hp.1, c1Mix_update S ℓ g i hp.1, c1Mix_update S _ g j hp.2]; rfl
  | eq i j f =>
    show Function.update _ f _ = _
    rw [c1Mix_update S ℓ g f hp.2.2]; rfl
  | cons i b =>
    show Function.update _ i _ = _
    rw [c1Mix_off S ℓ g hp, c1Mix_update S ℓ g i hp]; rfl
  | snoc i b =>
    show Function.update _ i _ = _
    rw [c1Mix_off S ℓ g hp, c1Mix_update S ℓ g i hp]; rfl
  | consHead i j =>
    show Function.update _ i _ = _
    rw [c1Mix_off S ℓ g hp.1, c1Mix_update S ℓ g i hp.1]; rfl
  | snocHead i j =>
    show Function.update _ i _ = _
    rw [c1Mix_off S ℓ g hp.1, c1Mix_update S ℓ g i hp.1]; rfl

theorem c1Mix_max (a b g : Fin k → ℕ) :
    (fun t => max (c1Mix S a g t) (c1Mix S b g t)) = c1Mix S (fun t => max (a t) (b t)) g := by
  funext t; by_cases h : S t <;> simp [c1Mix, h]

theorem c1Mix_iterSupT (F : (Fin k → ℕ) → (Fin k → ℕ)) (g : Fin k → ℕ)
    (hF : ∀ ℓ, F (c1Mix S ℓ g) = c1Mix S (F ℓ) g) (n : ℕ) (ℓ : Fin k → ℕ) :
    iterSupT F n (c1Mix S ℓ g) = c1Mix S (iterSupT F n ℓ) g := by
  have hit : ∀ j, F^[j] (c1Mix S ℓ g) = c1Mix S (F^[j] ℓ) g := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hF]
  funext t
  simp only [iterSupT, hit]
  by_cases h : S t
  · simp only [c1Mix, h, ite_true]
    apply le_antisymm
    · exact Finset.sup_le fun _ _ => le_rfl
    · exact Finset.le_sup (f := fun _ => g t) (Finset.mem_range.mpr (Nat.succ_pos n))
  · simp only [c1Mix, h, ite_false, iterSupT]

end

theorem c1Prog_len (S : Fin k → Prop) [DecidablePred S] :
    ∀ (p : Prog k), c1ProgAv S p → ∀ ℓ g : Fin k → ℕ,
      p.lenBoundT (c1Mix S ℓ g) = c1Mix S (p.lenBoundT ℓ) g := by
  intro p
  induction p with
  | prim p => intro hp ℓ g; exact c1Prim_len S p hp ℓ g
  | coin i => intro hp ℓ g; exact c1Mix_update S ℓ g i hp 1
  | seq p q ihp ihq =>
    intro hp ℓ g
    show q.lenBoundT (p.lenBoundT _) = _
    rw [ihp hp.1, ihq hp.2]; rfl
  | ifBlank i p q ihp ihq =>
    intro hp ℓ g
    show (fun t => max _ _) = _
    rw [ihp hp.1, ihq hp.2]
    exact c1Mix_max S _ _ g
  | ifBit i p q ihp ihq =>
    intro hp ℓ g
    show (fun t => max _ _) = _
    rw [ihp hp.1, ihq hp.2]
    exact c1Mix_max S _ _ g
  | loop i body ih =>
    intro hp ℓ g
    show iterSupT _ (c1Mix S ℓ g i) _ = _
    rw [c1Mix_off S ℓ g hp.1]
    refine c1Mix_iterSupT S _ g (fun ℓ' => ?_) _ ℓ
    rw [c1Mix_tailB S ℓ' g i hp.1, ih hp.2]

theorem c1_supB_mix (S : Fin k → Prop) [DecidablePred S] (ℓ g : Fin k → ℕ) (V : ℕ)
    (hg : ∀ t, S t → g t ≤ V) : supB (c1Mix S ℓ g) ≤ supB ℓ + V := by
  apply Finset.sup_le
  intro t _
  by_cases h : S t
  · rw [c1Mix_of S ℓ g h]; have := hg t h; omega
  · rw [c1Mix_off S ℓ g h]; have := le_supB ℓ t; omega

theorem c1_sup_mul (s : Finset ℕ) (f h : ℕ → ℕ) (V : ℕ) (hf : ∀ j ∈ s, f j ≤ (V + 1) * h j) :
    s.sup f ≤ (V + 1) * s.sup h :=
  Finset.sup_le fun j hj => (hf j hj).trans (Nat.mul_le_mul_left _ (Finset.le_sup hj))

theorem c1Prog_time (S : Fin k → Prop) [DecidablePred S] (V : ℕ) :
    ∀ (p : Prog k), c1ProgAv S p → ∀ ℓ g : Fin k → ℕ, (∀ t, S t → g t ≤ V) →
      p.timeBoundT (c1Mix S ℓ g) ≤ (V + 1) * p.timeBoundT ℓ := by
  intro p
  induction p with
  | prim p =>
    intro _ ℓ g hg
    show 2 * (supB _ + p.pad) + 3 ≤ (V + 1) * (2 * (supB ℓ + p.pad) + 3)
    have := c1_supB_mix S ℓ g V hg
    nlinarith
  | coin i =>
    intro _ ℓ g hg
    show 2 * supB _ + 4 ≤ (V + 1) * (2 * supB ℓ + 4)
    have := c1_supB_mix S ℓ g V hg
    nlinarith
  | seq p q ihp ihq =>
    intro hp ℓ g hg
    show p.timeBoundT _ + q.timeBoundT (p.lenBoundT _) ≤ _
    rw [c1Prog_len S p hp.1]
    have h1 := ihp hp.1 ℓ g hg
    have h2 := ihq hp.2 (p.lenBoundT ℓ) g hg
    show _ ≤ (V + 1) * (p.timeBoundT ℓ + q.timeBoundT (p.lenBoundT ℓ))
    rw [Nat.mul_add]; omega
  | ifBlank i p q ihp ihq =>
    intro hp ℓ g hg
    show max _ _ + 1 ≤ (V + 1) * (max _ _ + 1)
    have h1 := ihp hp.1 ℓ g hg
    have h2 := ihq hp.2 ℓ g hg
    have h3 : max (p.timeBoundT (c1Mix S ℓ g)) (q.timeBoundT (c1Mix S ℓ g)) ≤
        (V + 1) * max (p.timeBoundT ℓ) (q.timeBoundT ℓ) :=
      max_le (h1.trans (Nat.mul_le_mul_left _ (le_max_left _ _)))
        (h2.trans (Nat.mul_le_mul_left _ (le_max_right _ _)))
    nlinarith
  | ifBit i p q ihp ihq =>
    intro hp ℓ g hg
    show max _ _ + 1 ≤ (V + 1) * (max _ _ + 1)
    have h1 := ihp hp.1 ℓ g hg
    have h2 := ihq hp.2 ℓ g hg
    have h3 : max (p.timeBoundT (c1Mix S ℓ g)) (q.timeBoundT (c1Mix S ℓ g)) ≤
        (V + 1) * max (p.timeBoundT ℓ) (q.timeBoundT ℓ) :=
      max_le (h1.trans (Nat.mul_le_mul_left _ (le_max_left _ _)))
        (h2.trans (Nat.mul_le_mul_left _ (le_max_right _ _)))
    nlinarith
  | loop i body ih =>
    intro hp ℓ g hg
    have hit : ∀ j, (Prog.loopStepT i body)^[j] (c1Mix S ℓ g) =
        c1Mix S ((Prog.loopStepT i body)^[j] ℓ) g := by
      intro j
      induction j with
      | zero => rfl
      | succ j ihj =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ihj, Prog.loopStepT,
          Prog.loopStepT, c1Mix_tailB S _ g i hp.1, c1Prog_len S body hp.2]
    show c1Mix S ℓ g i * ((Finset.range (c1Mix S ℓ g i)).sup (fun j => Prog.roundTimeT
      (body.timeBoundT) i ((Prog.loopStepT i body)^[j] (c1Mix S ℓ g))) + 1) + 2 ≤
      (V + 1) * (ℓ i * ((Finset.range (ℓ i)).sup (fun j => Prog.roundTimeT
      (body.timeBoundT) i ((Prog.loopStepT i body)^[j] ℓ)) + 1) + 2)
    rw [c1Mix_off S ℓ g hp.1]
    have hs := c1_sup_mul (Finset.range (ℓ i)) (fun j => Prog.roundTimeT
      (body.timeBoundT) i ((Prog.loopStepT i body)^[j] (c1Mix S ℓ g))) (fun j => Prog.roundTimeT
      (body.timeBoundT) i ((Prog.loopStepT i body)^[j] ℓ)) V (fun j _ => by
        simp only [hit, Prog.roundTimeT]
        rw [c1Mix_tailB S _ g i hp.1]
        have h1 := ih hp.2 (tailB i ((Prog.loopStepT i body)^[j] ℓ)) g hg
        have h2 := c1_supB_mix S ((Prog.loopStepT i body)^[j] ℓ) g V hg
        nlinarith)
    set A := (Finset.range (ℓ i)).sup (fun j => Prog.roundTimeT
      (body.timeBoundT) i ((Prog.loopStepT i body)^[j] (c1Mix S ℓ g)))
    set B := (Finset.range (ℓ i)).sup (fun j => Prog.roundTimeT
      (body.timeBoundT) i ((Prog.loopStepT i body)^[j] ℓ))
    have : ℓ i * (A + 1) ≤ ℓ i * ((V + 1) * B + (V + 1)) :=
      Nat.mul_le_mul_left _ (by nlinarith)
    nlinarith

/-! ### Framed programs -/

theorem c1_embedF_mix (S : Fin k → Prop) [DecidablePred S] {m : ℕ} (e : Fin m ↪ Fin k)
    (he : ∀ j, ¬ S (e j)) (ℓ g : Fin k → ℕ) (b : Fin m → ℕ) :
    embedF e (c1Mix S ℓ g) b = c1Mix S (embedF e ℓ b) g := by
  funext t
  rcases embedF_cases e (c1Mix S ℓ g) b t with ⟨hn, h⟩ | ⟨j, hj, h⟩
  · rw [h]
    rcases embedF_cases e ℓ b t with ⟨-, h'⟩ | ⟨j, hj, -⟩
    · by_cases hs : S t <;> simp [c1Mix, hs, h']
    · rw [← hj, partialInv_self] at hn; cases hn
  · subst hj
    rw [h, c1Mix_off S _ g (he j), embedF_apply_self]

theorem c1_comp_mix (S : Fin k → Prop) [DecidablePred S] {m : ℕ} (e : Fin m ↪ Fin k)
    (he : ∀ j, ¬ S (e j)) (ℓ g : Fin k → ℕ) :
    (fun j => c1Mix S ℓ g (e j)) = fun j => ℓ (e j) := by
  funext j; exact c1Mix_off S ℓ g (he j)

theorem c1X_len : ∀ {k : ℕ} (S : Fin k → Prop) [DecidablePred S] (p : XProg k), c1XAv S p →
    ∀ ℓ g : Fin k → ℕ, p.lenBoundT (c1Mix S ℓ g) = c1Mix S (p.lenBoundT ℓ) g := by
  intro k S _ p
  induction p with
  | prog p => intro hp ℓ g; exact c1Prog_len S p hp ℓ g
  | frame e p _ =>
    intro hp ℓ g
    show embedF e _ (XProg.lenBoundT p (fun j => c1Mix S ℓ g (e j))) = _
    rw [c1_comp_mix S e hp, c1_embedF_mix S e hp]; rfl
  | seq p q ihp ihq =>
    intro hp ℓ g
    show XProg.lenBoundT q (XProg.lenBoundT p _) = _
    rw [ihp S hp.1, ihq S hp.2]; rfl
  | ifBlank i p q ihp ihq =>
    intro hp ℓ g
    show (fun t => max _ _) = _
    rw [ihp S hp.1, ihq S hp.2]
    exact c1Mix_max S _ _ g
  | ifBit i p q ihp ihq =>
    intro hp ℓ g
    show (fun t => max _ _) = _
    rw [ihp S hp.1, ihq S hp.2]
    exact c1Mix_max S _ _ g
  | loop i body ih =>
    intro hp ℓ g
    show iterSupT _ (c1Mix S ℓ g i) _ = _
    rw [c1Mix_off S ℓ g hp.1]
    refine c1Mix_iterSupT S _ g (fun ℓ' => ?_) _ ℓ
    rw [c1Mix_tailB S ℓ' g i hp.1, ih S hp.2]

theorem c1X_time : ∀ {k : ℕ} (S : Fin k → Prop) [DecidablePred S] (V : ℕ) (p : XProg k),
    c1XAv S p → ∀ ℓ g : Fin k → ℕ, (∀ t, S t → g t ≤ V) →
      p.timeBoundT (c1Mix S ℓ g) ≤ (V + 1) * p.timeBoundT ℓ := by
  intro k S _ V p
  induction p with
  | prog p => intro hp ℓ g hg; exact c1Prog_time S V p hp ℓ g hg
  | frame e p _ =>
    intro hp ℓ g _
    show XProg.timeBoundT p (fun j => c1Mix S ℓ g (e j)) ≤ (V + 1) * XProg.timeBoundT p _
    rw [c1_comp_mix S e hp]
    exact Nat.le_mul_of_pos_left _ (Nat.succ_pos V)
  | seq p q ihp ihq =>
    intro hp ℓ g hg
    show XProg.timeBoundT p _ + XProg.timeBoundT q (XProg.lenBoundT p _) ≤ _
    rw [c1X_len S p hp.1]
    have h1 := ihp S hp.1 ℓ g hg
    have h2 := ihq S hp.2 (XProg.lenBoundT p ℓ) g hg
    show _ ≤ (V + 1) * (XProg.timeBoundT p ℓ + XProg.timeBoundT q (XProg.lenBoundT p ℓ))
    rw [Nat.mul_add]; omega
  | ifBlank i p q ihp ihq =>
    intro hp ℓ g hg
    show max _ _ + 1 ≤ (V + 1) * (max _ _ + 1)
    have h1 := ihp S hp.1 ℓ g hg
    have h2 := ihq S hp.2 ℓ g hg
    have h3 : max (XProg.timeBoundT p (c1Mix S ℓ g)) (XProg.timeBoundT q (c1Mix S ℓ g)) ≤
        (V + 1) * max (XProg.timeBoundT p ℓ) (XProg.timeBoundT q ℓ) :=
      max_le (h1.trans (Nat.mul_le_mul_left _ (le_max_left _ _)))
        (h2.trans (Nat.mul_le_mul_left _ (le_max_right _ _)))
    nlinarith
  | ifBit i p q ihp ihq =>
    intro hp ℓ g hg
    show max _ _ + 1 ≤ (V + 1) * (max _ _ + 1)
    have h1 := ihp S hp.1 ℓ g hg
    have h2 := ihq S hp.2 ℓ g hg
    have h3 : max (XProg.timeBoundT p (c1Mix S ℓ g)) (XProg.timeBoundT q (c1Mix S ℓ g)) ≤
        (V + 1) * max (XProg.timeBoundT p ℓ) (XProg.timeBoundT q ℓ) :=
      max_le (h1.trans (Nat.mul_le_mul_left _ (le_max_left _ _)))
        (h2.trans (Nat.mul_le_mul_left _ (le_max_right _ _)))
    nlinarith
  | loop i body ih =>
    intro hp ℓ g hg
    have hit : ∀ j, (XProg.loopStepT i body)^[j] (c1Mix S ℓ g) =
        c1Mix S ((XProg.loopStepT i body)^[j] ℓ) g := by
      intro j
      induction j with
      | zero => rfl
      | succ j ihj =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ihj, XProg.loopStepT,
          XProg.loopStepT, c1Mix_tailB S _ g i hp.1, c1X_len S body hp.2]
    show c1Mix S ℓ g i * ((Finset.range (c1Mix S ℓ g i)).sup (fun j => Prog.roundTimeT
      (XProg.timeBoundT body) i ((XProg.loopStepT i body)^[j] (c1Mix S ℓ g))) + 1) + 2 ≤
      (V + 1) * (ℓ i * ((Finset.range (ℓ i)).sup (fun j => Prog.roundTimeT
      (XProg.timeBoundT body) i ((XProg.loopStepT i body)^[j] ℓ)) + 1) + 2)
    rw [c1Mix_off S ℓ g hp.1]
    have hs := c1_sup_mul (Finset.range (ℓ i)) (fun j => Prog.roundTimeT
      (XProg.timeBoundT body) i ((XProg.loopStepT i body)^[j] (c1Mix S ℓ g)))
      (fun j => Prog.roundTimeT (XProg.timeBoundT body) i ((XProg.loopStepT i body)^[j] ℓ)) V
      (fun j _ => by
        simp only [hit, Prog.roundTimeT]
        rw [c1Mix_tailB S _ g i hp.1]
        have h1 := ih S hp.2 (tailB i ((XProg.loopStepT i body)^[j] ℓ)) g hg
        have h2 := c1_supB_mix S ((XProg.loopStepT i body)^[j] ℓ) g V hg
        nlinarith)
    set A := (Finset.range (ℓ i)).sup (fun j => Prog.roundTimeT
      (XProg.timeBoundT body) i ((XProg.loopStepT i body)^[j] (c1Mix S ℓ g)))
    set B := (Finset.range (ℓ i)).sup (fun j => Prog.roundTimeT
      (XProg.timeBoundT body) i ((XProg.loopStepT i body)^[j] ℓ))
    have : ℓ i * (A + 1) ≤ ℓ i * ((V + 1) * B + (V + 1)) :=
      Nat.mul_le_mul_left _ (by nlinarith)
    nlinarith

end SigabaNeo.Tape.XProg.Avoid