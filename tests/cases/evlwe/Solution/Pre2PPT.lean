import Solution.Pre2Red
import Solution.AttackPPT
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Computability.Probabilistic.PPT.Capture

/-!
# The Pre2 reduction is uniform strict PPT

`red D` reads the LWE word, draws `x ← sampleModNat (width κ) M` (a residue of `width κ` fair bits),
runs `D` on `build κ word x` and outputs `D`'s bit XOR the digit `h` of `x`. Certificates in
cslib-frontier's polynomial-time calculus for every function of `Solution/Pre2Red.lean`, and
`red_isPPT`.
-/

namespace TestCase.EvLWE

open SigabaNeo.Lattices

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM TestCase TestCase.EvLWE

/-- The number of fair bits: `M ≤ 2^{width − κ}`. -/
def width (κ : ℕ) : ℕ := (2 * κ + 3) * (n κ * k κ) + (8 * κ + 9) * k κ + κ + 1

/-- The reduction. -/
noncomputable def red (D : Distinguisher) : Distinguisher := fun κ word => do
  let x ← ProbComp.sampleModNat (width κ) (Mval κ word)
  let o ← D κ (build κ word x)
  pure (o ^^ hbit κ word x)

section
variable {α : Type} {input : α ↪ List Bool} {l : α → ℕ} {word : α → List Bool} {x : α → ℕ}

@[fun_prop] theorem ell_tidy : ComputableTidilyInPolyTime ell encUnary encUnary := by
  unfold ell; fun_prop

theorem κR_t (hl : ComputableTidilyInPolyTime l input encUnary) :
    ComputableTidilyInPolyTime (fun a => κR (l a)) input encNat := by
  unfold κR
  exact ComputableTidilyInPolyTime.binary_two_pow.comp (by fun_prop)

theorem RRc_t (hl : ComputableTidilyInPolyTime l input encUnary) :
    ComputableTidilyInPolyTime (fun a => RRc (l a)) input encNat := by
  unfold RRc
  exact ComputableTidilyInPolyTime.binary_add' (κR_t hl) (.const 1)

theorem NTw_t (hl : ComputableTidilyInPolyTime l input encUnary)
    (hw : ComputableInPolyTime word input encBits) :
    ComputableTidilyInPolyTime (fun a => NTw (l a) (word a)) input encNat := by
  have hq := (qOf_poly (.of_tidy hl) hw).tidy
  unfold NTw
  exact ComputableTidilyInPolyTime.binary_add' (ComputableTidilyInPolyTime.binary_div'
    (ComputableTidilyInPolyTime.binary_sub' hq (.const 1)) (.const 2)) (.const 1)

theorem bigT_t (hl : ComputableTidilyInPolyTime l input encUnary)
    (hw : ComputableInPolyTime word input encBits) :
    ComputableTidilyInPolyTime (fun a => bigT (l a) (word a)) input encNat := by
  unfold bigT
  exact ComputableTidilyInPolyTime.binary_pow' (NTw_t hl hw) (by fun_prop)

theorem bigR_t (hl : ComputableTidilyInPolyTime l input encUnary) :
    ComputableTidilyInPolyTime (fun a => bigR (l a)) input encNat := by
  unfold bigR
  exact ComputableTidilyInPolyTime.binary_pow' (RRc_t hl) (by fun_prop)

theorem bigRT_t (hl : ComputableTidilyInPolyTime l input encUnary)
    (hw : ComputableInPolyTime word input encBits) :
    ComputableTidilyInPolyTime (fun a => bigRT (l a) (word a)) input encNat := by
  unfold bigRT
  exact ComputableTidilyInPolyTime.binary_mul' (bigR_t hl) (bigT_t hl hw)

theorem Mval_t (hl : ComputableTidilyInPolyTime l input encUnary)
    (hw : ComputableInPolyTime word input encBits) :
    ComputableTidilyInPolyTime (fun a => Mval (l a) (word a)) input encNat := by
  unfold Mval
  exact ComputableTidilyInPolyTime.binary_mul' (.const 2) (bigRT_t hl hw)

theorem hbit_t (hl : ComputableTidilyInPolyTime l input encUnary)
    (hw : ComputableInPolyTime word input encBits)
    (hx : ComputableTidilyInPolyTime x input encNat) :
    ComputableTidilyInPolyTime (fun a => hbit (l a) (word a) (x a)) input encBool := by
  unfold hbit
  exact ComputableTidilyInPolyTime.binary_le' (bigRT_t hl hw) hx

theorem rDig_t {i j : α → ℕ} (hl : ComputableTidilyInPolyTime l input encUnary)
    (hw : ComputableInPolyTime word input encBits)
    (hx : ComputableTidilyInPolyTime x input encNat)
    (hi : ComputableTidilyInPolyTime i input encUnary)
    (hj : ComputableTidilyInPolyTime j input encUnary) :
    ComputableTidilyInPolyTime (fun a => rDig (l a) (word a) (x a) (i a) (j a)) input encNat := by
  unfold rDig
  have hp : ComputableTidilyInPolyTime (fun a => RRc (l a) ^ (i a * k (l a) + j a)) input encNat :=
    ComputableTidilyInPolyTime.binary_pow' (RRc_t hl) (by fun_prop)
  exact ComputableTidilyInPolyTime.binary_mod' (ComputableTidilyInPolyTime.binary_div'
    (ComputableTidilyInPolyTime.binary_div' (ComputableTidilyInPolyTime.binary_mod' hx
      (bigRT_t hl hw)) (bigT_t hl hw)) hp) (RRc_t hl)

theorem tDig_t {j : α → ℕ} (hl : ComputableTidilyInPolyTime l input encUnary)
    (hw : ComputableInPolyTime word input encBits)
    (hx : ComputableTidilyInPolyTime x input encNat)
    (hj : ComputableTidilyInPolyTime j input encUnary) :
    ComputableTidilyInPolyTime (fun a => tDig (l a) (word a) (x a) (j a)) input encNat := by
  unfold tDig
  exact ComputableTidilyInPolyTime.binary_mod' (ComputableTidilyInPolyTime.binary_div'
    (ComputableTidilyInPolyTime.binary_mod' (ComputableTidilyInPolyTime.binary_mod' hx
      (bigRT_t hl hw)) (bigT_t hl hw))
    (ComputableTidilyInPolyTime.binary_pow' (NTw_t hl hw) hj)) (NTw_t hl hw)

theorem pEntry_t {i j : α → ℕ} (hl : ComputableTidilyInPolyTime l input encUnary)
    (hw : ComputableInPolyTime word input encBits)
    (hx : ComputableTidilyInPolyTime x input encNat)
    (hi : ComputableTidilyInPolyTime i input encUnary)
    (hj : ComputableTidilyInPolyTime j input encUnary) :
    ComputableTidilyInPolyTime (fun a => pEntry (l a) (word a) (x a) (i a) (j a)) input encNat := by
  have hq := (qOf_poly (.of_tidy hl) hw).tidy
  have ha := (entryAt_poly (idx := fun a => 1 + i a * k (l a) + j a) (.of_tidy hl) hw
    (.of_tidy (by fun_prop))).tidy
  unfold pEntry aAt
  exact ComputableTidilyInPolyTime.binary_mod' (ComputableTidilyInPolyTime.binary_add'
    (ComputableTidilyInPolyTime.binary_mul' (.const 2) ha)
    (ComputableTidilyInPolyTime.ite' (encC := encBool) (hbit_t hl hw hx)
      (rDig_t hl hw hx hi hj) (.const 0))) hq

theorem auxEntry_t {j : α → ℕ} (hl : ComputableTidilyInPolyTime l input encUnary)
    (hw : ComputableInPolyTime word input encBits)
    (hx : ComputableTidilyInPolyTime x input encNat)
    (hj : ComputableTidilyInPolyTime j input encUnary) :
    ComputableTidilyInPolyTime (fun a => auxEntry (l a) (word a) (x a) (j a)) input encNat := by
  have hq := (qOf_poly (.of_tidy hl) hw).tidy
  have hb := (entryAt_poly (idx := fun a => 1 + n (l a) * k (l a) + j a) (.of_tidy hl) hw
    (.of_tidy (by fun_prop))).tidy
  unfold auxEntry bAt
  exact ComputableTidilyInPolyTime.binary_mod' (ComputableTidilyInPolyTime.binary_add'
    (ComputableTidilyInPolyTime.binary_mul' (.const 2) hb)
    (ComputableTidilyInPolyTime.binary_mul' (.const 2)
      (ComputableTidilyInPolyTime.binary_sub' hq (tDig_t hl hw hx hj)))) hq

theorem bitsOf_eq (W v : ℕ) : bitsOf W v = Cslib.BitString.lowBits W v := rfl

theorem build_t (hl : ComputableTidilyInPolyTime l input encUnary)
    (hw : ComputableInPolyTime word input encBits)
    (hx : ComputableTidilyInPolyTime x input encNat) :
    ComputableTidilyInPolyTime (fun a => build (l a) (word a) (x a)) input encBits := by
  have hq := (qOf_poly (.of_tidy hl) hw).tidy
  have hw2 : ComputableInPolyTime (fun p : (α × ℕ) × ℕ => word p.1.1)
      (encPair (encPair input encUnary) encUnary) encBits := by fun_prop
  have hp := pEntry_t (input := encPair (encPair input encUnary) encUnary)
    (l := fun p => l p.1.1) (word := fun p => word p.1.1) (x := fun p => x p.1.1)
    (i := fun p => p.1.2) (j := fun p => p.2) (by fun_prop) hw2 (by fun_prop) (by fun_prop)
    (by fun_prop)
  have hau := auxEntry_t (input := encPair (encPair input encUnary) encUnary)
    (l := fun p => l p.1.1) (word := fun p => word p.1.1) (x := fun p => x p.1.1)
    (j := fun p => p.2) (by fun_prop) hw2 (by fun_prop) (by fun_prop)
  have hrow1 : ComputableTidilyInPolyTime (fun p : α × ℕ =>
      (List.range (k (l p.1))).map (pEntry (l p.1) (word p.1) (x p.1) p.2))
      (encPair input encUnary) (encList encNat) :=
    ComputableTidilyInPolyTime.mapWithInput (ComputableTidilyInPolyTime.range.comp (by fun_prop))
      hp
  have hrow2 : ComputableTidilyInPolyTime (fun p : α × ℕ =>
      (List.range (k (l p.1))).map (auxEntry (l p.1) (word p.1) (x p.1)))
      (encPair input encUnary) (encList encNat) :=
    ComputableTidilyInPolyTime.mapWithInput (ComputableTidilyInPolyTime.range.comp (by fun_prop))
      hau
  have hflat1 := ComputableTidilyInPolyTime.flatMapWithInput
    (f := fun a i => (List.range (k (l a))).map (pEntry (l a) (word a) (x a) i))
    (ComputableTidilyInPolyTime.range.comp (by fun_prop :
      ComputableTidilyInPolyTime (fun a => n (l a)) input encUnary)) hrow1
  have hflat2 := ComputableTidilyInPolyTime.flatMapWithInput
    (f := fun a _ => (List.range (k (l a))).map (auxEntry (l a) (word a) (x a)))
    (ComputableTidilyInPolyTime.range.comp (by fun_prop :
      ComputableTidilyInPolyTime (fun a => ell (l a)) input encUnary)) hrow2
  have hlist := ComputableTidilyInPolyTime.cons' hq
    (ComputableTidilyInPolyTime.listAppend' hflat1 hflat2)
  have hbits : ComputableTidilyInPolyTime (fun p : α × ℕ => Cslib.BitString.lowBits (W (l p.1)) p.2)
      (encPair input encNat) encBits :=
    ComputableTidilyInPolyTime.bitsLow (by fun_prop) (by fun_prop)
  unfold build encEntries
  exact ComputableTidilyInPolyTime.flatMapToBitsWithInput hlist hbits

end

@[fun_prop] theorem width_tidy : ComputableTidilyInPolyTime width encUnary encUnary := by
  unfold width; fun_prop

/-- The reduction is uniform strict PPT whenever `D` is. -/
theorem red_isPPT {D : Distinguisher} (hD : IsPPT encBool D) : IsPPT encBool (red D) := by
  have hfirst : IsPPTOn (encPair encUnary encBits) encNat
      (fun p : ℕ × List Bool => ProbComp.sampleModNat (width p.1) (Mval p.1 p.2)) :=
    isPPTOn_sampleModNat (by fun_prop)
      (.of_tidy (Mval_t (l := fun p : ℕ × List Bool => p.1) (by fun_prop) (by fun_prop)))
  have hprep : ComputableInPolyTime (fun pr : (ℕ × List Bool) × ℕ =>
      (pr.1.1, build pr.1.1 pr.1.2 pr.2))
      (encPair (encPair encUnary encBits) encNat) (encPair encUnary encBits) :=
    .of_tidy (ComputableTidilyInPolyTime.prod (by fun_prop)
      (build_t (l := fun pr : (ℕ × List Bool) × ℕ => pr.1.1) (by fun_prop) (by fun_prop)
        (by fun_prop)))
  have hD' := hD.on.preprocess hprep
  have hxor : ComputableInPolyTime (fun pp : ((ℕ × List Bool) × ℕ) × Bool =>
      pp.2 ^^ hbit pp.1.1.1 pp.1.1.2 pp.1.2)
      (encPair (encPair (encPair encUnary encBits) encNat) encBool) encBool :=
    .of_tidy (ComputableTidilyInPolyTime.bool_xor.comp (ComputableTidilyInPolyTime.prod
      (by fun_prop) (hbit_t (l := fun pp : ((ℕ × List Bool) × ℕ) × Bool => pp.1.1.1)
        (by fun_prop) (by fun_prop) (by fun_prop))))
  have hsecond := hD'.map_with (f := fun (pr : (ℕ × List Bool) × ℕ) (o : Bool) =>
    o ^^ hbit pr.1.1 pr.1.2 pr.2) hxor
  have h := hfirst.bind_with (second := fun (p : ℕ × List Bool) (x : ℕ) =>
    (fun o => o ^^ hbit p.1 p.2 x) <$> D p.1 (build p.1 p.2 x)) hsecond
  refine IsPPTOn.isPPT ?_
  refine h.congr fun p => ?_
  simp only [red, map_eq_bind_pure_comp, Function.comp_def]

end TestCase.EvLWE
