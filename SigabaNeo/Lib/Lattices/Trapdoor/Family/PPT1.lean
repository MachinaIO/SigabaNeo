import SigabaNeo.Lib.Lattices.Trapdoor.Family.Samp1
import SigabaNeo.Lib.Lattices.Trapdoor.Family.Helpers
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Factorial
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Probabilistic.Retry
import CslibFrontier.Computability.Probabilistic.UniformNat

/-!
# Trapdoor sampler: the `D_{Z,τ}` sampler is strict PPT

Certificates in cslib-frontier's polynomial-time calculus for the parameters (unary in `κ`),
`π̂ · 2^P` (`piNat`), the exact acceptance test `accept`, one attempt, and the loop:
`samp1_isPPT : IsPPTOn encUnary encIntBin samp1`.
-/

namespace SigabaNeo.Lattices.Trapdoor.Family

open Cslib Cslib.Probability Turing.MultiTapeTM SigabaNeo.Lattices

theorem sum_range_eq_list {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ i ∈ Finset.range N, f i = ((List.range N).map f).sum := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

theorem cip_congr {α β : Type} {enc : α ↪ List Bool} {enc' : β ↪ List Bool} {f g : α → β}
    (hf : ComputableInPolyTime f enc enc') (h : ∀ a, f a = g a) : ComputableInPolyTime g enc enc' := by
  have : f = g := funext h
  subst this; exact hf

/-! ### Parameters -/

@[fun_prop] theorem Lg_plain : ComputableInPolyTime Lg encUnary encUnary := by
  unfold Lg
  have h := ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.unary_log_two.comp m_tidy)
  fun_prop

theorem two_pow_Lg_le (κ : ℕ) : 2 ^ Lg κ ≤ 2 * m κ := by
  unfold Lg
  rw [pow_succ, mul_comm]
  exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (m_pos κ).ne')

@[fun_prop] theorem Aex_plain : ComputableInPolyTime Aex encUnary encUnary := by
  unfold Aex; fun_prop
@[fun_prop] theorem Pbits_plain : ComputableInPolyTime Pbits encUnary encUnary := by
  unfold Pbits; fun_prop
@[fun_prop] theorem Nterms_plain : ComputableInPolyTime Nterms encUnary encUnary := by
  unfold Nterms; fun_prop

@[fun_prop] theorem Ecnt_plain : ComputableInPolyTime Ecnt encUnary encUnary := by
  have hv : ComputableInPolyTime (fun κ => 4 ^ (Lg κ + 2)) encUnary encNat := by fun_prop
  have hb : ComputableInPolyTime (fun κ => 64 * m κ * m κ) encUnary encUnary := by fun_prop
  refine ComputableInPolyTime.binary_to_unary_bounded hv hb fun κ => ?_
  have h := two_pow_Lg_le κ
  calc 4 ^ (Lg κ + 2) = 16 * (2 ^ Lg κ) ^ 2 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; ring
    _ ≤ 16 * (2 * m κ) ^ 2 := by gcongr
    _ = 64 * m κ * m κ := by ring

@[fun_prop] theorem Tbits_plain : ComputableInPolyTime Tbits encUnary encUnary := by
  unfold Tbits; fun_prop

@[fun_prop] theorem Rt_plain : ComputableInPolyTime Rt encUnary encUnary := by
  have hL : ComputableInPolyTime (fun κ => Lg κ + 8) encUnary encUnary := by fun_prop
  have hv : ComputableInPolyTime (fun κ => 2 ^ (Lg κ + 8)) encUnary encNat :=
    ComputableInPolyTime.binary_two_pow.comp hL
  have hb : ComputableInPolyTime (fun κ => 512 * m κ) encUnary encUnary := by fun_prop
  have h2 := ComputableInPolyTime.binary_to_unary_bounded hv hb fun κ => by
    have h := two_pow_Lg_le κ
    rw [pow_add]; omega
  have h3 : ComputableInPolyTime (fun κ : ℕ => κ + 1) encUnary encUnary := by fun_prop
  exact ComputableInPolyTime.unary_mul' h2 h3

/-! ### `π̂` -/

theorem fpSum_list (d P J : ℕ) :
    fpSum d P J = ((List.range J).map fun j => (-1 : ℤ) ^ j * (fpTerm d P j : ℤ)).sum := by
  unfold fpSum; exact sum_range_eq_list _ _

theorem fpTerm_plain (d : ℕ) : ComputableInPolyTime (fun p : ℕ × ℕ => fpTerm d p.1 p.2)
    (encPair encUnary encUnary) encNat := by
  unfold fpTerm; fun_prop

theorem fpSum_plain (d : ℕ) : ComputableInPolyTime (fun P : ℕ => fpSum d P P) encUnary encIntBin := by
  have hf := fpTerm_plain d
  have hbody : ComputableInPolyTime (fun p : ℕ × ℕ => (-1 : ℤ) ^ p.2 * (fpTerm d p.1 p.2 : ℤ))
      (encPair encUnary encUnary) encIntBin := by fun_prop
  have hl := ComputableInPolyTime.mapWithInput (f := fun (P j : ℕ) => (-1 : ℤ) ^ j * (fpTerm d P j : ℤ))
    (list := fun P => List.range P) (by fun_prop) hbody
  exact cip_congr (ComputableInPolyTime.intBin_sum.comp hl) fun P => by rw [fpSum_list]; rfl

@[fun_prop] theorem piNat_plain : ComputableInPolyTime piNat encUnary encNat := by
  unfold piNat piInt
  have h5 := (fpSum_plain 5).comp Pbits_plain
  have h239 := (fpSum_plain 239).comp Pbits_plain
  fun_prop

/-! ### The acceptance test -/

/-- `κ` in unary, `v` and `u` in binary. -/
abbrev encT3 : ℕ × ℕ × ℕ ↪ List Bool := encPair encUnary (encPair encNat encNat)

theorem natAbs_zOf (κ v : ℕ) : (zOf κ v).natAbs = (v - 2 ^ Aex κ) + (2 ^ Aex κ - v) := by
  unfold zOf
  have : ((2 ^ Aex κ : ℕ) : ℤ) = (2 : ℤ) ^ Aex κ := by push_cast; rfl
  omega

theorem sNum_list (yN yD E N : ℕ) : sNum yN yD E N =
    ((List.range N).map fun i => yN ^ i * (E * yD) ^ (N - 1 - i) * ((N - 1).factorial / i.factorial)).sum := by
  unfold sNum; exact sum_range_eq_list _ _

theorem sNum_plain {γ : Type} {encIn : γ ↪ List Bool} {yN yD E N : γ → ℕ}
    (hyN : ComputableInPolyTime yN encIn encNat) (hyD : ComputableInPolyTime yD encIn encNat)
    (hE : ComputableInPolyTime E encIn encUnary) (hN : ComputableInPolyTime N encIn encUnary) :
    ComputableInPolyTime (fun a => sNum (yN a) (yD a) (E a) (N a)) encIn encNat := by
  have hbody : ComputableInPolyTime (fun p : γ × ℕ => yN p.1 ^ p.2 * (E p.1 * yD p.1) ^ (N p.1 - 1 - p.2) *
      ((N p.1 - 1).factorial / p.2.factorial)) (encPair encIn encUnary) encNat := by
    have hyN' : ComputableInPolyTime (fun p : γ × ℕ => yN p.1) (encPair encIn encUnary) encNat :=
      hyN.comp (by fun_prop)
    have hyD' : ComputableInPolyTime (fun p : γ × ℕ => yD p.1) (encPair encIn encUnary) encNat :=
      hyD.comp (by fun_prop)
    have hE' : ComputableInPolyTime (fun p : γ × ℕ => E p.1) (encPair encIn encUnary) encUnary :=
      hE.comp (by fun_prop)
    have hN' : ComputableInPolyTime (fun p : γ × ℕ => N p.1) (encPair encIn encUnary) encUnary :=
      hN.comp (by fun_prop)
    fun_prop
  have hl := ComputableInPolyTime.mapWithInput
    (f := fun a i => yN a ^ i * (E a * yD a) ^ (N a - 1 - i) * ((N a - 1).factorial / i.factorial))
    (list := fun a => List.range (N a)) (by fun_prop) hbody
  exact cip_congr (ComputableInPolyTime.binary_sum.comp hl) fun a => by rw [sNum_list]; rfl

@[fun_prop] theorem yD_plain : ComputableInPolyTime yD encUnary encNat := by
  unfold yD; fun_prop

theorem yN_plain : ComputableInPolyTime (fun t : ℕ × ℕ × ℕ => yN t.1 t.2.1) encT3 encNat := by
  have hκ : ComputableInPolyTime (fun t : ℕ × ℕ × ℕ => t.1) encT3 encUnary := by fun_prop
  have hA : ComputableInPolyTime (fun t : ℕ × ℕ × ℕ => Aex t.1) encT3 encUnary := Aex_plain.comp hκ
  have hp : ComputableInPolyTime (fun t : ℕ × ℕ × ℕ => piNat t.1) encT3 encNat := piNat_plain.comp hκ
  have hv : ComputableInPolyTime (fun t : ℕ × ℕ × ℕ => t.2.1) encT3 encNat := by fun_prop
  have h2A : ComputableInPolyTime (fun t : ℕ × ℕ × ℕ => 2 ^ Aex t.1) encT3 encNat :=
    ComputableInPolyTime.binary_two_pow.comp hA
  have hd := ComputableInPolyTime.binary_add' (ComputableInPolyTime.binary_sub' hv h2A)
    (ComputableInPolyTime.binary_sub' h2A hv)
  have h : ComputableInPolyTime (fun t : ℕ × ℕ × ℕ =>
      piNat t.1 * ((t.2.1 - 2 ^ Aex t.1) + (2 ^ Aex t.1 - t.2.1)) ^ 2) encT3 encNat :=
    ComputableInPolyTime.binary_mul' hp (ComputableInPolyTime.binary_pow' hd (ComputableInPolyTime.const 2))
  exact cip_congr h fun t => by unfold yN; rw [natAbs_zOf]

theorem accept_plain : ComputableInPolyTime (fun t : ℕ × ℕ × ℕ => accept t.1 t.2.1 t.2.2) encT3 encBool := by
  have hκ : ComputableInPolyTime (fun t : ℕ × ℕ × ℕ => t.1) encT3 encUnary := by fun_prop
  have hE := Ecnt_plain.comp hκ
  have hN := Nterms_plain.comp hκ
  have hyD := yD_plain.comp hκ
  have hT := Tbits_plain.comp hκ
  have hs := sNum_plain yN_plain hyD hE hN
  have hnum : ComputableInPolyTime (fun t : ℕ × ℕ × ℕ => Lnum t.1 t.2.1) encT3 encNat :=
    ComputableInPolyTime.binary_pow' hs hE
  have hN1 := ComputableInPolyTime.unary_sub' hN (ComputableInPolyTime.const 1)
  have hden : ComputableInPolyTime (fun t : ℕ × ℕ × ℕ => Lden t.1) encT3 encNat :=
    ComputableInPolyTime.binary_pow' (ComputableInPolyTime.binary_mul'
      (ComputableInPolyTime.binary_pow' (ComputableInPolyTime.binary_mul'
        (ComputableInPolyTime.unary_to_binary.comp hE) hyD) hN1)
      (ComputableInPolyTime.binary_factorial.comp hN1)) hE
  have hu : ComputableInPolyTime (fun t : ℕ × ℕ × ℕ => t.2.2) encT3 encNat := by fun_prop
  exact ComputableInPolyTime.binary_lt' (ComputableInPolyTime.binary_mul' hu hnum)
    (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.binary_two_pow.comp hT) hden)

/-! ### The sampler -/

theorem attempt_isPPT : IsPPTOn encUnary encT3 attempt := by
  have hv := ComputableInPolyTime.sampleBinaryNat (input := encUnary)
    (width := fun κ => Aex κ + 1) (by fun_prop)
  have hu := ComputableInPolyTime.sampleBinaryNat (input := encPair encUnary encNat)
    (width := fun p : ℕ × ℕ => Tbits p.1) (Tbits_plain.comp (by fun_prop))
  have hpack : ComputableInPolyTime (fun pp : (ℕ × ℕ) × ℕ => (pp.1.1, pp.1.2, pp.2))
      (encPair (encPair encUnary encNat) encNat) encT3 := by fun_prop
  have h2 := hu.map_with (f := fun (p : ℕ × ℕ) (u : ℕ) => (p.1, p.2, u)) hpack
  have h := hv.bind_with (second := fun (κ : ℕ) (v : ℕ) =>
    (fun u => (κ, v, u)) <$> ProbComp.sampleBinaryNat (Tbits κ)) h2
  refine h.congr fun κ => ?_
  simp only [attempt, map_eq_bind_pure_comp, Function.comp_def]

theorem outZ_plain : ComputableInPolyTime outZ (encOption encT3) encIntBin := by
  have hbody : ComputableInPolyTime (fun p : Option (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) =>
      ((p.2.2.1 : ℤ) - ((2 ^ Aex p.2.1 : ℕ) : ℤ)))
      (encPair (encOption encT3) encT3) encIntBin := by
    have hA : ComputableInPolyTime (fun p : Option (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) => Aex p.2.1)
        (encPair (encOption encT3) encT3) encUnary := Aex_plain.comp (by fun_prop)
    have hv : ComputableInPolyTime (fun p : Option (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) => p.2.2.1)
        (encPair (encOption encT3) encT3) encNat := by fun_prop
    exact ComputableInPolyTime.intBin_sub' (ComputableInPolyTime.intBin_natCast.comp hv)
      (ComputableInPolyTime.intBin_natCast.comp (ComputableInPolyTime.binary_two_pow.comp hA))
  have h := ComputableInPolyTime.optionElimWithInput (value := fun o : Option (ℕ × ℕ × ℕ) => o)
    (fallback := fun _ => (0 : ℤ))
    (body := fun (_ : Option (ℕ × ℕ × ℕ)) (t : ℕ × ℕ × ℕ) => ((t.2.1 : ℤ) - ((2 ^ Aex t.1 : ℕ) : ℤ)))
    ComputableInPolyTime.id' (ComputableInPolyTime.const 0) hbody
  refine cip_congr h fun o => ?_
  cases o with
  | none => rfl
  | some t => simp [outZ, zOf]

theorem samp1_isPPT : IsPPTOn encUnary encIntBin samp1 := by
  have hr := IsPPTOn.retry (program := attempt) (good := fun t : ℕ × ℕ × ℕ => accept t.1 t.2.1 t.2.2)
    (fuel := Rt) attempt_isPPT accept_plain Rt_plain
  exact hr.map outZ_plain

end SigabaNeo.Lattices.Trapdoor.Family
