import PE.Impl.RingBTVW.Scheme
import SigabaNeo.Lib.Lattices.Basic
import CslibFrontier.Languages.Probabilistic.Basic
import CslibFrontier.Probability.PMF
import SigabaNeo.Lib.Lattices.Stat
import CslibFrontier.Languages.Probabilistic.Oracle.Interaction

/-!
# The distributions of the coins

The laws from which the ring variant of BTVW17 §4.2 draws its coins over `R_q = ℤ_q[X]/(X^N + 1)`:

* `Setup` (`setupLaw`): `B`, the `B_j` and `p` uniform;
* `KeyGen`: a key sampler (`KeySampler`, `keyGenLaw` of `PE.Impl.RingBTVW.Scheme`);
* `Enc` (`encCoinsLaw`): the secret `s` and the top rows `aᵢ` uniform, and the errors `eᵢ`, `e₀`,
  `e_j`, `e'` with independent coefficients from the error law `χ` (a discrete Gaussian, for
  instance `D_{Z,σ}` reduced mod `q`).

`unif α` is the uniform law on a finite type, and adding a constant does not change it
(`unif_bind_add`).
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo.Lattices Cslib Cslib.Probability

/-- The uniform law on a finite type. -/
noncomputable def unif (α : Type) [Fintype α] [Nonempty α] : PMF α :=
  ProbComp.eval (ProbComp.uniform α)

/-- A uniform element is unchanged by adding a constant. -/
theorem unif_bind_add {α β : Type} [Fintype α] [Nonempty α] [AddGroup α] (g : α → PMF β)
    (m : α) : (unif α).bind (fun a => g (a + m)) = (unif α).bind g := by
  have h : (unif α).map (Equiv.addRight m) = unif α := by
    rw [unif, ProbComp.eval_uniform]
    exact PMF.uniformOfFintype_map_equiv _
  conv_rhs => rw [← h]
  rw [PMF.bind_map]
  rfl

variable {N q : ℕ} [NeZero q]

/-- A ring element with independent coefficients from `χ`. -/
noncomputable def polyLaw (χ : PMF (ZMod q)) : PMF (Negacyclic (ZMod q) N) :=
  (sampleFun χ).map Negacyclic.ofCoeffs

instance : Inhabited (Negacyclic (ZMod q) N) := ⟨0⟩

/-- A matrix with independent entries. -/
noncomputable def matLaw {α : Type} [Inhabited α] {r c : Type} [Fintype r] [Fintype c]
    (d : PMF α) : PMF (Matrix r c α) :=
  (sampleFun (ι := r × c) d).map fun g a b => g (a, b)

variable {k : ℕ} (hk : q ≤ 2 ^ k) (Attr : Type) [Fintype Attr] [DecidableEq Attr]

instance : Fintype (ringSetting N q k hk Attr).Attr := inferInstanceAs (Fintype Attr)

instance : DecidableEq (ringSetting N q k hk Attr).Attr := inferInstanceAs (DecidableEq Attr)

instance : DecidableEq (ringSetting N q k hk Attr).ctBits.Index :=
  inferInstanceAs (DecidableEq (Fin 2 × Col k × Fin k × Fin N))

/-- A row of `R_q^{1×W}`. -/
abbrev Row (N q k : ℕ) := Matrix (Fin 1) (Col k) (Negacyclic (ZMod q) N)

/-- **Setup**: `B`, the `B_j` and `p` uniform. -/
noncomputable def setupLaw : PMF (MPK (ringSetting N q k hk Attr)) := do
  let B ← unif (Row N q k)
  let p ← unif (Negacyclic (ZMod q) N)
  let Bj ← unif ((ringSetting N q k hk Attr).Attr × (ringSetting N q k hk Attr).ctBits.Index →
    Row N q k)
  pure { B := B, Bj := Bj, p := p }

/-- The coins of **Enc**, with the error law `χ`. -/
noncomputable def encCoinsLaw (χ : PMF (ZMod q)) : PMF (EncCoins (ringSetting N q k hk Attr)) := do
  let s ← unif (Negacyclic (ZMod q) N)
  let a ← unif (Attr → Row N q k)
  let eΨ ← sampleFun (matLaw (polyLaw χ))
  let e₀ ← matLaw (polyLaw χ)
  let ej ← sampleFun (matLaw (polyLaw χ))
  let e' ← polyLaw χ
  pure { s := s, a := a, eΨ := eΨ, e₀ := e₀, ej := ej, e' := e' }

/-- **Enc**. -/
noncomputable def encLaw (χ : PMF (ZMod q)) (mpk : MPK (ringSetting N q k hk Attr))
    (x : Attr → Bool) (M : Bool) : PMF (Ciphertext (ringSetting N q k hk Attr)) :=
  (encCoinsLaw hk Attr χ).map (encrypt mpk x M)

end AdvancedEncryption.RingBTVW
