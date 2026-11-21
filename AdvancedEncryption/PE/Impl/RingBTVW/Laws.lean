import PE.Impl.RingBTVW.Scheme
import SigabaNeo.Lib.Lattices.Basic
import CslibFrontier.Languages.Probabilistic.Basic

/-!
# The distributions of the coins

The laws from which the ring variant of BTVW17 §4.2 draws its coins over `R_q = ℤ_q[X]/(X^N + 1)`,
each ring element with independent coefficients (`polyLaw`):

* `Setup` (`setupLaw`): `A₀`, every `B_j` and `p` uniform; the trapdoor `T` with `0/1`
  coefficients;
* `KeyGen`: a key sampler (`KeySampler`, `keyGenLaw` of `PE.Impl.RingBTVW.Scheme`);
* `Enc` (`encCoinsLaw`): the secret `s` uniform, the errors `e`, `e₀`, `e_j`, `e'` from the error law
  `χ` (a discrete Gaussian, for instance `D_{Z,σ}` reduced mod `q`), and the Ring-GSW randomness
  `Rᵢ` with `0/1` coefficients.
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo.Lattices Cslib

variable {N q : ℕ} [NeZero q]

/-- A ring element with independent coefficients from `χ`. -/
noncomputable def polyLaw (χ : PMF (ZMod q)) : PMF (Negacyclic (ZMod q) N) :=
  (sampleFun χ).map Negacyclic.ofCoeffs

/-- The uniform coefficient. -/
noncomputable def uniformCoeff : PMF (ZMod q) := ProbComp.eval (ProbComp.uniform (ZMod q))

/-- A uniform `0/1` coefficient. -/
noncomputable def binaryCoeff : PMF (ZMod q) :=
  (ProbComp.eval (ProbComp.uniform Bool)).map fun b => if b then 1 else 0

instance : Inhabited (Negacyclic (ZMod q) N) := ⟨0⟩

/-- A matrix with independent entries. -/
noncomputable def matLaw {α : Type} [Inhabited α] {r c : Type} [Fintype r] [Fintype c]
    (d : PMF α) : PMF (Matrix r c α) :=
  (sampleFun (ι := r × c) d).map fun g a b => g (a, b)

variable {k : ℕ} (hk : q ≤ 2 ^ k) (Attr : Type) [Fintype Attr]

instance : Fintype (ringSetting N q k hk Attr).Attr := inferInstanceAs (Fintype Attr)

/-- **Setup**: `(mpk, msk)`. -/
noncomputable def setupLaw :
    PMF (MPK (ringSetting N q k hk Attr) × MSK k (Negacyclic (ZMod q) N)) := do
  let A₀ ← sampleFun (polyLaw uniformCoeff)
  let T ← matLaw (polyLaw binaryCoeff)
  let Bj ← sampleFun (matLaw (polyLaw uniformCoeff))
  let p ← polyLaw uniformCoeff
  pure (setup (ringSetting N q k hk Attr) A₀ T Bj p)

/-- The coins of **Enc**, with the error law `χ`. -/
noncomputable def encCoinsLaw (χ : PMF (ZMod q)) : PMF (EncCoins (ringSetting N q k hk Attr)) := do
  let s ← polyLaw uniformCoeff
  let e ← matLaw (polyLaw χ)
  let e₀ ← matLaw (polyLaw χ)
  let ej ← sampleFun (matLaw (polyLaw χ))
  let e' ← polyLaw χ
  let Rm ← sampleFun (matLaw (polyLaw binaryCoeff))
  pure { s := s, e := e, e₀ := e₀, ej := ej, e' := e', Rm := Rm }

/-- **Enc**. -/
noncomputable def encLaw (χ : PMF (ZMod q)) (mpk : MPK (ringSetting N q k hk Attr))
    (x : Attr → Bool) (M : Bool) : PMF (Ciphertext (ringSetting N q k hk Attr)) :=
  (encCoinsLaw hk Attr χ).map (encrypt mpk x M)

end AdvancedEncryption.RingBTVW
