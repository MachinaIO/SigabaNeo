import SigabaNeoStd.Lattices.Trapdoor.Family.AlgLaw
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Traverse

/-!
# Trapdoor sampler: `GenTrap` and `SamplePre` are strict PPT

Certificates in cslib-frontier's polynomial-time calculus for the list functions of
`Family/Alg.lean`, then `genAlg_isPPT` and `preAlg_isPPT`.
-/

namespace SigabaNeo.Lattices.Trapdoor.Family

open Cslib Cslib.Probability Turing.MultiTapeTM SigabaNeo.Lattices

/-! ### Dimensions -/

@[fun_prop] theorem n_plain : ComputableInPolyTime n encUnary encUnary := by unfold n; fun_prop
@[fun_prop] theorem w_plain : ComputableInPolyTime w encUnary encUnary := by unfold w; fun_prop
@[fun_prop] theorem mb_plain : ComputableInPolyTime mb encUnary encUnary := by unfold mb; fun_prop
@[fun_prop] theorem wdA_plain : ComputableInPolyTime wdA encUnary encUnary := by unfold wdA; fun_prop

section
variable {γ : Type} {encIn : γ ↪ List Bool}

/-! ### Entries -/

theorem aAtL_poly {κ : γ → ℕ} {L : γ → List ℕ} {i a : γ → ℕ}
    (hκ : ComputableInPolyTime κ encIn encUnary) (hL : ComputableInPolyTime L encIn (encList encNat))
    (hi : ComputableInPolyTime i encIn encUnary) (ha : ComputableInPolyTime a encIn encUnary) :
    ComputableInPolyTime (fun x => aAtL (κ x) (L x) (i x) (a x)) encIn encIntBin := by
  unfold aAtL
  have hmb := mb_plain.comp hκ
  have hidx : ComputableInPolyTime (fun x => i x * mb (κ x) + a x) encIn encUnary :=
    ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' hi hmb) ha
  exact ComputableInPolyTime.intBin_natCast.comp (ComputableInPolyTime.listGetDWithInput hL hidx 0)

theorem dec4N_poly {X : γ → ℕ} (hX : ComputableInPolyTime X encIn encNat) :
    ComputableInPolyTime (fun x => dec4N (X x)) encIn encIntBin := by
  unfold dec4N
  have hm : ComputableInPolyTime (fun x => X x % 4) encIn encNat :=
    ComputableInPolyTime.binary_mod' hX (ComputableInPolyTime.const 4)
  have h0 : ComputableInPolyTime (fun x => decide (X x % 4 = 0)) encIn encBool :=
    ComputableInPolyTime.decide_eq' hm (ComputableInPolyTime.const 0)
  have h3 : ComputableInPolyTime (fun x => decide (X x % 4 = 3)) encIn encBool :=
    ComputableInPolyTime.decide_eq' hm (ComputableInPolyTime.const 3)
  exact ComputableInPolyTime.ite_decide h0 (ComputableInPolyTime.const (-1))
    (ComputableInPolyTime.ite_decide h3 (ComputableInPolyTime.const 1) (ComputableInPolyTime.const 0))

theorem rAtL_poly {κ : γ → ℕ} {L : γ → List ℕ} {a c : γ → ℕ}
    (hκ : ComputableInPolyTime κ encIn encUnary) (hL : ComputableInPolyTime L encIn (encList encNat))
    (ha : ComputableInPolyTime a encIn encUnary) (hc : ComputableInPolyTime c encIn encUnary) :
    ComputableInPolyTime (fun x => rAtL (κ x) (L x) (a x) (c x)) encIn encIntBin := by
  unfold rAtL
  have hmb := mb_plain.comp hκ
  have hidx : ComputableInPolyTime (fun x => c x * mb (κ x) + a x) encIn encUnary :=
    ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' hc hmb) ha
  exact dec4N_poly (ComputableInPolyTime.listGetDWithInput hL hidx 0)

theorem gEntL_poly {κ : γ → ℕ} {i c : γ → ℕ}
    (hκ : ComputableInPolyTime κ encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary) (hc : ComputableInPolyTime c encIn encUnary) :
    ComputableInPolyTime (fun x => gEntL (κ x) (i x) (c x)) encIn encIntBin := by
  unfold gEntL
  have hw : ComputableInPolyTime (fun x => w (κ x) + 1) encIn encUnary :=
    ComputableInPolyTime.unary_add' (w_plain.comp hκ) (ComputableInPolyTime.const 1)
  have hd : ComputableInPolyTime (fun x => decide (c x / (w (κ x) + 1) = i x)) encIn encBool :=
    ComputableInPolyTime.decide_eq' (ComputableInPolyTime.unary_div' hc hw) hi
  have hp : ComputableInPolyTime (fun x => ((2 ^ (c x % (w (κ x) + 1)) : ℕ) : ℤ)) encIn encIntBin :=
    ComputableInPolyTime.intBin_natCast.comp
      (ComputableInPolyTime.binary_two_pow.comp (ComputableInPolyTime.unary_mod' hc hw))
  refine cip_congr (ComputableInPolyTime.ite_decide hd hp (ComputableInPolyTime.const 0)) fun x => ?_
  push_cast; rfl

/-- A sum over `range count`, in binary integers. -/
theorem intSumRange {count : γ → ℕ} {f : γ → ℕ → ℤ}
    (hc : ComputableInPolyTime count encIn encUnary)
    (hf : ComputableInPolyTime (fun p : γ × ℕ => f p.1 p.2) (encPair encIn encUnary) encIntBin) :
    ComputableInPolyTime (fun x => ((List.range (count x)).map (f x)).sum) encIn encIntBin :=
  ComputableInPolyTime.intBin_sum.comp (ComputableInPolyTime.mapWithInput
    (ComputableInPolyTime.range.comp hc) hf)

theorem bEntZ_poly {κ : γ → ℕ} {aL rL : γ → List ℕ} {i j : γ → ℕ}
    (hκ : ComputableInPolyTime κ encIn encUnary)
    (haL : ComputableInPolyTime aL encIn (encList encNat)) (hrL : ComputableInPolyTime rL encIn (encList encNat))
    (hi : ComputableInPolyTime i encIn encUnary) (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun x => bEntZ (κ x) (aL x) (rL x) (i x) (j x)) encIn encIntBin := by
  unfold bEntZ
  have hmb := mb_plain.comp hκ
  have hlt : ComputableInPolyTime (fun x => decide (j x < mb (κ x))) encIn encBool :=
    ComputableInPolyTime.unary_lt' hj hmb
  have hjm : ComputableInPolyTime (fun x => j x - mb (κ x)) encIn encUnary :=
    ComputableInPolyTime.unary_sub' hj hmb
  have hsum : ComputableInPolyTime (fun x => ((List.range (mb (κ x))).map fun a =>
      aAtL (κ x) (aL x) (i x) a * rAtL (κ x) (rL x) a (j x - mb (κ x))).sum) encIn encIntBin := by
    refine intSumRange hmb ?_
    have hκ' : ComputableInPolyTime (fun p : γ × ℕ => κ p.1) (encPair encIn encUnary) encUnary :=
      hκ.comp (by fun_prop)
    exact ComputableInPolyTime.intBin_mul'
      (aAtL_poly hκ' (haL.comp (by fun_prop)) (hi.comp (by fun_prop)) (by fun_prop))
      (rAtL_poly hκ' (hrL.comp (by fun_prop)) (by fun_prop) (hjm.comp (by fun_prop)))
  exact ComputableInPolyTime.ite_decide hlt (aAtL_poly hκ haL hi hj)
    (ComputableInPolyTime.intBin_sub' (gEntL_poly hκ hi hjm) hsum)

theorem bL_poly {κ Q : γ → ℕ} {aL rL : γ → List ℕ}
    (hκ : ComputableInPolyTime κ encIn encUnary) (hQ : ComputableInPolyTime Q encIn encNat)
    (haL : ComputableInPolyTime aL encIn (encList encNat)) (hrL : ComputableInPolyTime rL encIn (encList encNat)) :
    ComputableInPolyTime (fun x => bL (κ x) (Q x) (aL x) (rL x)) encIn (encList encNat) := by
  unfold bL
  have hrow : ComputableInPolyTime (fun p : γ × ℕ => (List.range (m (κ p.1))).map
      (bEntL (κ p.1) (Q p.1) (aL p.1) (rL p.1) p.2)) (encPair encIn encUnary) (encList encNat) := by
    have hκ' : ComputableInPolyTime (fun p : γ × ℕ => κ p.1) (encPair encIn encUnary) encUnary :=
      hκ.comp (by fun_prop)
    have hent : ComputableInPolyTime (fun pq : (γ × ℕ) × ℕ =>
        bEntL (κ pq.1.1) (Q pq.1.1) (aL pq.1.1) (rL pq.1.1) pq.1.2 pq.2)
        (encPair (encPair encIn encUnary) encUnary) encNat := by
      unfold bEntL
      exact ComputableInPolyTime.intBin_emodNat'
        (bEntZ_poly (hκ.comp (by fun_prop)) (haL.comp (by fun_prop)) (hrL.comp (by fun_prop))
          (by fun_prop) (by fun_prop)) (hQ.comp (by fun_prop))
    exact ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp (m_plain.comp hκ')) hent
  exact ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp (n_plain.comp hκ)) hrow

/-! ### The column map -/

/-- The data of one column with the draws: `((κ, Q), (Ā, R), u)` and `y`. -/
abbrev encInp : (ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ ↪ List Bool :=
  encPair (encPair encUnary encNat) (encPair (encPair (encList encNat) (encList encNat)) (encList encNat))

theorem synL_poly {κ Q : γ → ℕ} {aL rL uL : γ → List ℕ} {y : γ → List ℤ} {i : γ → ℕ}
    (hκ : ComputableInPolyTime κ encIn encUnary) (hQ : ComputableInPolyTime Q encIn encNat)
    (haL : ComputableInPolyTime aL encIn (encList encNat)) (hrL : ComputableInPolyTime rL encIn (encList encNat))
    (huL : ComputableInPolyTime uL encIn (encList encNat)) (hy : ComputableInPolyTime y encIn (encList encIntBin))
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => synL (κ x) (Q x) (aL x) (rL x) (uL x) (y x) (i x)) encIn encNat := by
  unfold synL
  have hsum : ComputableInPolyTime (fun x => ((List.range (m (κ x))).map fun j =>
      bEntZ (κ x) (aL x) (rL x) (i x) j * (y x).getD j 0).sum) encIn encIntBin := by
    refine intSumRange (m_plain.comp hκ) ?_
    exact ComputableInPolyTime.intBin_mul'
      (bEntZ_poly (hκ.comp (by fun_prop)) (haL.comp (by fun_prop)) (hrL.comp (by fun_prop))
        (hi.comp (by fun_prop)) (by fun_prop))
      (ComputableInPolyTime.listGetDWithInput (hy.comp (by fun_prop)) (by fun_prop) 0)
  exact ComputableInPolyTime.intBin_emodNat' (ComputableInPolyTime.intBin_sub'
    (ComputableInPolyTime.intBin_natCast.comp (ComputableInPolyTime.listGetDWithInput huL hi 0)) hsum) hQ

theorem zL_poly {κ Q : γ → ℕ} {aL rL uL : γ → List ℕ} {y : γ → List ℤ} {c : γ → ℕ}
    (hκ : ComputableInPolyTime κ encIn encUnary) (hQ : ComputableInPolyTime Q encIn encNat)
    (haL : ComputableInPolyTime aL encIn (encList encNat)) (hrL : ComputableInPolyTime rL encIn (encList encNat))
    (huL : ComputableInPolyTime uL encIn (encList encNat)) (hy : ComputableInPolyTime y encIn (encList encIntBin))
    (hc : ComputableInPolyTime c encIn encUnary) :
    ComputableInPolyTime (fun x => zL (κ x) (Q x) (aL x) (rL x) (uL x) (y x) (c x)) encIn encIntBin := by
  unfold zL
  have hw : ComputableInPolyTime (fun x => w (κ x) + 1) encIn encUnary :=
    ComputableInPolyTime.unary_add' (w_plain.comp hκ) (ComputableInPolyTime.const 1)
  have hs := synL_poly hκ hQ haL hrL huL hy (ComputableInPolyTime.unary_div' hc hw)
  have hb := ComputableInPolyTime.binary_testBit hs (ComputableInPolyTime.unary_mod' hc hw)
  exact ComputableInPolyTime.ite_decide (condition := fun x => (synL (κ x) (Q x) (aL x) (rL x) (uL x) (y x)
    (c x / (w (κ x) + 1))).testBit (c x % (w (κ x) + 1)) = true)
    (by simpa only [Bool.decide_eq_true] using hb) (ComputableInPolyTime.const 1) (ComputableInPolyTime.const 0)

theorem gsynL_poly : ComputableInPolyTime
    (fun p : ((ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) × List ℤ =>
      gsynL p.1.1.1 p.1.1.2 p.1.2.1.1 p.1.2.1.2 p.1.2.2 p.2)
    (encPair encInp (encList encIntBin)) (encList encIntBin) := by
  unfold gsynL
  set E := encPair encInp (encList encIntBin)
  have hκ : ComputableInPolyTime (fun p : ((ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) × List ℤ => p.1.1.1)
      E encUnary := by fun_prop
  refine ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp (m_plain.comp hκ)) ?_
  set F := encPair E encUnary
  have hκ' : ComputableInPolyTime (fun q : (((ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) × List ℤ) × ℕ =>
      q.1.1.1.1) F encUnary := by fun_prop
  have hQ : ComputableInPolyTime (fun q : (((ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) × List ℤ) × ℕ =>
      q.1.1.1.2) F encNat := by fun_prop
  have haL : ComputableInPolyTime (fun q : (((ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) × List ℤ) × ℕ =>
      q.1.1.2.1.1) F (encList encNat) := by fun_prop
  have hrL : ComputableInPolyTime (fun q : (((ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) × List ℤ) × ℕ =>
      q.1.1.2.1.2) F (encList encNat) := by fun_prop
  have huL : ComputableInPolyTime (fun q : (((ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) × List ℤ) × ℕ =>
      q.1.1.2.2) F (encList encNat) := by fun_prop
  have hy : ComputableInPolyTime (fun q : (((ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) × List ℤ) × ℕ =>
      q.1.2) F (encList encIntBin) := by fun_prop
  have hj : ComputableInPolyTime (fun q : (((ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) × List ℤ) × ℕ =>
      q.2) F encUnary := by fun_prop
  have hmb := mb_plain.comp hκ'
  have hx : ComputableInPolyTime (fun q : (((ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) × List ℤ) × ℕ =>
      xPreL q.1.1.1.1 q.1.1.1.2 q.1.1.2.1.1 q.1.1.2.1.2 q.1.1.2.2 q.1.2 q.2) F encIntBin := by
    unfold xPreL
    have hlt : ComputableInPolyTime (fun q : (((ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) × List ℤ) × ℕ =>
        decide (q.2 < mb q.1.1.1.1)) F encBool := ComputableInPolyTime.unary_lt' hj hmb
    have hsum : ComputableInPolyTime (fun q : (((ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) × List ℤ) × ℕ =>
        ((List.range (mb q.1.1.1.1)).map fun c => rAtL q.1.1.1.1 q.1.1.2.1.2 q.2 c *
          zL q.1.1.1.1 q.1.1.1.2 q.1.1.2.1.1 q.1.1.2.1.2 q.1.1.2.2 q.1.2 c).sum) F encIntBin := by
      refine intSumRange hmb ?_
      exact ComputableInPolyTime.intBin_mul'
        (rAtL_poly (hκ'.comp (by fun_prop)) (hrL.comp (by fun_prop)) (hj.comp (by fun_prop)) (by fun_prop))
        (zL_poly (hκ'.comp (by fun_prop)) (hQ.comp (by fun_prop)) (haL.comp (by fun_prop))
          (hrL.comp (by fun_prop)) (huL.comp (by fun_prop)) (hy.comp (by fun_prop)) (by fun_prop))
    exact ComputableInPolyTime.ite_decide hlt hsum
      (zL_poly hκ' hQ haL hrL huL hy (ComputableInPolyTime.unary_sub' hj hmb))
  exact ComputableInPolyTime.intBin_add' (ComputableInPolyTime.listGetDWithInput hy hj 0) hx

theorem colInputs_poly : ComputableInPolyTime colInputs encInp (encList encInp) := by
  unfold colInputs
  have hκ : ComputableInPolyTime (fun inp : (ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ => inp.1.1) encInp encUnary := by
    fun_prop
  refine ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp (k_plain.comp hκ)) ?_
  set F := encPair encInp encUnary
  have hκ' : ComputableInPolyTime (fun q : ((ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) × ℕ => q.1.1.1) F encUnary := by
    fun_prop
  have hu : ComputableInPolyTime (fun q : ((ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) × ℕ =>
      (List.range (n q.1.1.1)).map fun i => q.1.2.2.getD (i * k q.1.1.1 + q.2) 0) F (encList encNat) := by
    refine ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp (n_plain.comp hκ')) ?_
    have hL : ComputableInPolyTime (fun r : (((ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) × ℕ) × ℕ => r.1.1.2.2)
        (encPair F encUnary) (encList encNat) := by fun_prop
    have hidx : ComputableInPolyTime (fun r : (((ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) × ℕ) × ℕ =>
        r.2 * k r.1.1.1.1 + r.1.2) (encPair F encUnary) encUnary := by
      have hk : ComputableInPolyTime (fun r : (((ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) × ℕ) × ℕ =>
          k r.1.1.1.1) (encPair F encUnary) encUnary := k_plain.comp (by fun_prop)
      exact ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' (by fun_prop) hk) (by fun_prop)
    exact ComputableInPolyTime.listGetDWithInput hL hidx 0
  have hfst : ComputableInPolyTime (fun q : ((ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) × ℕ => q.1.1) F
      (encPair encUnary encNat) := by fun_prop
  have hsnd : ComputableInPolyTime (fun q : ((ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) × ℕ => q.1.2.1) F
      (encPair (encList encNat) (encList encNat)) := by fun_prop
  exact hfst.prod (hsnd.prod hu)

/-! ### The programs -/

theorem colAlg_isPPT : IsPPTOn encInp (encList encIntBin) colAlg := by
  have hκ : ComputableInPolyTime (fun c : (ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ => c.1.1) encInp encUnary := by
    fun_prop
  have hs : IsPPTOn encInp encIntBin (fun c : (ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ => samp1 c.1.1) :=
    samp1_isPPT.preprocess hκ
  have hr := IsPPTOn.replicate (count := fun c : (ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ => m c.1.1) hs
    (m_plain.comp hκ)
  exact hr.map_with (f := fun (c : (ℕ × ℕ) × (List ℕ × List ℕ) × List ℕ) (y : List ℤ) =>
    gsynL c.1.1 c.1.2 c.2.1.1 c.2.1.2 c.2.2 y) gsynL_poly

theorem preAlg_isPPT : IsPPTOn encInp (encList (encList encIntBin)) preAlg :=
  colAlg_isPPT.mapM.preprocess colInputs_poly

/-- The public input `(κ, q)`. -/
abbrev encPub : ℕ × ℕ ↪ List Bool := encPair encUnary encNat

theorem genAlg_isPPT : IsPPTOn encPub (encPair (encList encNat) (encPair (encList encNat) (encList encNat)))
    genAlg := by
  have hκ : ComputableInPolyTime (fun pub : ℕ × ℕ => pub.1) encPub encUnary := by fun_prop
  have hQ : ComputableInPolyTime (fun pub : ℕ × ℕ => pub.2) encPub encNat := by fun_prop
  have hA := IsPPTOn.replicate (count := fun pub : ℕ × ℕ => n pub.1 * mb pub.1)
    (isPPTOn_sampleModNat (input := encPub) (width := fun pub => wdA pub.1) (modulus := fun pub => pub.2)
      (wdA_plain.comp hκ) hQ)
    (ComputableInPolyTime.unary_mul' (n_plain.comp hκ) (mb_plain.comp hκ))
  set E := encPair encPub (encList encNat)
  have hκ2 : ComputableInPolyTime (fun p : (ℕ × ℕ) × List ℕ => p.1.1) E encUnary := by fun_prop
  have hR := IsPPTOn.replicate (count := fun p : (ℕ × ℕ) × List ℕ => mb p.1.1 * mb p.1.1)
    (ComputableInPolyTime.sampleBinaryNat (input := E) (width := fun _ => 2) (ComputableInPolyTime.const 2))
    (ComputableInPolyTime.unary_mul' (mb_plain.comp hκ2) (mb_plain.comp hκ2))
  have hout : ComputableInPolyTime (fun r : ((ℕ × ℕ) × List ℕ) × List ℕ =>
      (bL r.1.1.1 r.1.1.2 r.1.2 r.2, r.1.2, r.2))
      (encPair E (encList encNat)) (encPair (encList encNat) (encPair (encList encNat) (encList encNat))) := by
    have hb := bL_poly (encIn := encPair E (encList encNat)) (κ := fun r : ((ℕ × ℕ) × List ℕ) × List ℕ => r.1.1.1)
      (Q := fun r => r.1.1.2) (aL := fun r => r.1.2) (rL := fun r => r.2)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    have h2 : ComputableInPolyTime (fun r : ((ℕ × ℕ) × List ℕ) × List ℕ => r.1.2) (encPair E (encList encNat))
        (encList encNat) := by fun_prop
    have h3 : ComputableInPolyTime (fun r : ((ℕ × ℕ) × List ℕ) × List ℕ => r.2) (encPair E (encList encNat))
        (encList encNat) := by fun_prop
    exact hb.prod (h2.prod h3)
  have h2 := hR.map_with (f := fun (p : (ℕ × ℕ) × List ℕ) (rL : List ℕ) => (bL p.1.1 p.1.2 p.2 rL, p.2, rL)) hout
  have h := hA.bind_with (second := fun (pub : ℕ × ℕ) (aL : List ℕ) =>
    (fun rL => (bL pub.1 pub.2 aL rL, aL, rL)) <$>
      OracleComp.replicate (mb pub.1 * mb pub.1) (ProbComp.sampleBinaryNat 2)) h2
  refine h.congr fun pub => ?_
  simp only [genAlg, map_eq_bind_pure_comp, Function.comp_def]

end

end SigabaNeo.Lattices.Trapdoor.Family
