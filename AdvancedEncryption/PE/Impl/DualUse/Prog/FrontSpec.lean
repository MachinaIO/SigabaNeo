import PE.Impl.DualUse.ImplBase
import SigabaNeo.Lib.Machines.Prog.PhaseB
import SigabaNeo.Lib.Machines.Prog.FrameSize
import SigabaNeo.Lib.Machines.Prog.CoinFreeX
import SigabaNeo.Lib.Machines.Prog.Sample
import SigabaNeo.Lib.Machines.Inline.Regions

/-!
# The front end of `KeyGen`, `Dec` and the key component, as an interface

The front end reads a predicate word `C` (tape `0` of its own `R + 2` tapes) and writes

* `[]` if `C` is longer than the bound `n` (in the shells `n = c.L`),
* `[false]` if it is short but not in the class `V` (`ValidC`),
* `true :: bw C` otherwise, where `bw C` is the input word of the `W_f` block (`blockWord W C`),

every other tape blank (`frontG`). **`FrontSpecG fr n V bw FT FL FS`** says this of a program
`fr : XProg (R + 2)`, together with its cost: from a query of at most `T` bits, at most `FT T` steps
and at most `FL T` bits on tape `0` (the other tapes blank), and at most `FS` states.

`FrontSpec fr n W` is the instance at the neutral names `ValidC`, `blockWord W` of `ImplBase`. The
date-window instance is `frontP` (`R = 6`, `KeyFront.frontSpec_frontP`); the branching-program
instance is `frontBP` (`R = 70`, `FrontBP`: the length tests and the compiler `bpCompC`, which needs
`64` tapes of its own).

The shells frame the front end on the tapes `1, 83, 84, …, R + 83` by an embedding `e` with
`FrEmb e` (`eFr` for `R = 6`, `eF` for `R = 70`): tape `0` holds the data word of the shell (`msk`,
`sk ++ ct`, `sdEnc sd`), the tapes above `R + 83` are not touched.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

/-- An embedded store, from its values on and off the frame. -/
theorem embedF_eq_of {n m : ℕ} {α : Type} (e : Fin m ↪ Fin n) (s s' : Fin n → α) (g : Fin m → α)
    (h1 : ∀ j, s' (e j) = g j) (h2 : ∀ t, (∀ j, e j ≠ t) → s' t = s t) : embedF e s g = s' := by
  funext t
  rcases embedF_cases e s g t with ⟨hn, h⟩ | ⟨j, rfl, h⟩
  · rw [h, h2 t]
    intro j hj
    subst hj
    rw [partialInv_self] at hn
    exact Option.some_ne_none _ hn
  · rw [h, h1]

/-! ### The output of a front end -/

open Classical in
/-- **What the shells need of `C`**, for a length bound `n`, a class `V` and a block word `bw`. -/
noncomputable def frontG (n : ℕ) (V : List Bool → Prop) (bw : List Bool → List Bool)
    (C : List Bool) : List Bool :=
  if C.length ≤ n then (if V C then true :: bw C else [false]) else []

theorem frontG_long {n : ℕ} {V : List Bool → Prop} {bw : List Bool → List Bool} {C : List Bool}
    (h : ¬ C.length ≤ n) : frontG n V bw C = [] := by
  simp [frontG, h]

theorem frontG_short_not {n : ℕ} {V : List Bool → Prop} {bw : List Bool → List Bool}
    {C : List Bool} (h : C.length ≤ n) (hv : ¬ V C) : frontG n V bw C = [false] := by
  simp [frontG, h, hv]

theorem frontG_valid {n : ℕ} {V : List Bool → Prop} {bw : List Bool → List Bool} {C : List Bool}
    (h : C.length ≤ n) (hv : V C) : frontG n V bw C = true :: bw C := by
  simp [frontG, h, hv]

/-- The output of the front end at the neutral names. -/
noncomputable abbrev frontW (n W : ℕ) : List Bool → List Bool := frontG n ValidC (blockWord W)

/-! ### The interface -/

/-- **A front end**: well formed, coin-free, with the law `frontG n V bw` and the cost
`FT`, `FL`, `FS`. -/
structure FrontSpecG {R : ℕ} (fr : XProg (R + 2)) (n : ℕ) (V : List Bool → Prop)
    (bw : List Bool → List Bool) (FT FL : ℕ → ℕ) (FS : ℕ) : Prop where
  wf : fr.WF
  coinFree : fr.CoinFree
  law : ∀ C, fr.law (io2 (R := R) C [] []) = PMF.pure (io2 (R := R) (frontG n V bw C) [] [])
  ph : ∀ T, Ph fr (io2 (R := R) T 0 0) (FT T) (io2 (R := R) (FL T) 0 0)
  size : fr.size ≤ FS

/-- **The front end at the neutral names** `ValidC`, `blockWord W`. -/
abbrev FrontSpec {R : ℕ} (fr : XProg (R + 2)) (n W : ℕ) (FT FL : ℕ → ℕ) (FS : ℕ) : Prop :=
  FrontSpecG fr n ValidC (blockWord W) FT FL FS

section
variable {R : ℕ} {fr : XProg (R + 2)} {n : ℕ} {V : List Bool → Prop} {bw : List Bool → List Bool}
  {FT FL : ℕ → ℕ} {FS : ℕ}

theorem FrontSpecG.time (h : FrontSpecG fr n V bw FT FL FS) (T : ℕ) :
    timeBoundT fr (io2 (R := R) T 0 0) ≤ FT T :=
  (h.ph T _ le_rfl).1

theorem FrontSpecG.len (h : FrontSpecG fr n V bw FT FL FS) (T : ℕ) :
    lenBoundT fr (io2 (R := R) T 0 0) ≤ io2 (R := R) (FL T) 0 0 :=
  (h.ph T _ le_rfl).2

end

/-! ### The tapes of the front end in a shell -/

/-- **The frame of a front end in a shell**: `0 ↦ 1`, `j ↦ j + 82`. -/
def FrEmb {R : ℕ} (e : Fin (R + 2) ↪ Fin 256) : Prop :=
  ∀ j : Fin (R + 2), (e j).val = if j.val = 0 then 1 else j.val + 82

section
variable {R : ℕ} {e : Fin (R + 2) ↪ Fin 256}

theorem FrEmb.zero (he : FrEmb e) : e 0 = 1 := Fin.ext (by rw [he]; rfl)

theorem FrEmb.ne_zero (he : FrEmb e) (j : Fin (R + 2)) : e j ≠ 0 := by
  intro h; have := congrArg Fin.val h; rw [he] at this; split_ifs at this <;> omega

/-- The tapes of a framed front end other than its input are `83 …`. -/
theorem FrEmb.range (he : FrEmb e) (j : Fin (R + 2)) :
    (e j).val = 1 ∨ (83 ≤ (e j).val ∧ (e j).val ≤ R + 83) := by
  rw [he]; have := j.isLt; split_ifs <;> omega

theorem io2_frEmb (he : FrEmb e) {α : Type} (a b d : α) :
    (fun j => io2 (R := 254) a b d (e j)) = io2 (R := R) b d d := by
  funext j
  have h := he j
  by_cases h0 : j.val = 0
  · rw [if_pos h0] at h; simp [io2, h, h0]
  · rw [if_neg h0] at h
    have h1 : (e j).val ≠ 0 := by omega
    have h2 : (e j).val ≠ 1 := by omega
    simp [io2, h1, h2, h0]

theorem embedF_frEmb (he : FrEmb e) {α : Type} (a b b' d : α) :
    embedF e (io2 (R := 254) a b d) (io2 (R := R) b' d d) = io2 (R := 254) a b' d := by
  refine embedF_eq_of _ _ _ _ (fun j => ?_) (fun t ht => ?_)
  · have h := he j
    by_cases h0 : j.val = 0
    · rw [if_pos h0] at h; simp [io2, h, h0]
    · rw [if_neg h0] at h
      have h1 : (e j).val ≠ 0 := by omega
      have h2 : (e j).val ≠ 1 := by omega
      simp [io2, h1, h2, h0]
  · have h1 : t.val ≠ 1 := fun h => ht 0 (Fin.ext (by rw [he]; simp [h]))
    simp only [io2, h1, ite_false]

/-- **The framed front end**: `C` on tape `1` becomes `frontG n V bw C`. -/
theorem law_frame_frEmb (he : FrEmb e) {fr : XProg (R + 2)} {n : ℕ} {V : List Bool → Prop}
    {bw : List Bool → List Bool} {FT FL : ℕ → ℕ} {FS : ℕ} (h : FrontSpecG fr n V bw FT FL FS)
    (a C : List Bool) :
    (frame e fr).law (io2 (R := 254) a C []) =
      PMF.pure (io2 (R := 254) a (frontG n V bw C) []) := by
  rw [XProg.law_frame, io2_frEmb he, h.law, PMF.pure_map, embedF_frEmb he]

end

/-- The frame of a front end of `72` tapes: `1`, then `83, …, 153`. -/
def eF : Fin 72 ↪ Fin 256 :=
  ⟨fun j => ⟨if j.val = 0 then 1 else j.val + 82, by split_ifs <;> omega⟩, by
    intro a b h
    simp only [Fin.mk.injEq] at h
    ext
    split_ifs at h <;> omega⟩

theorem frEmb_eF : FrEmb eF := fun _ => rfl

end AdvancedEncryption.DualUse.Prog
