import PE.Impl.RingBTVW.BitLaws
import PE.Impl.RingBTVW.Encodings

/-!
# The law of `Setup`

`Setup` draws `B₀`, `a`, the short `t`, `e`, the `B_j` and `p`, and outputs
`mpk = (B₀, B₁ = [1 | a | G̲ − (t a + e)], B_j, p)` and `msk = (mpk, e, t)`: the master secret key
keeps the public key, which `KeyGen` needs (`setupLaw`). It is realized by fair coins
(`bitLaw_setup`).
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW.Fresh Cslib Cslib.Probability

variable {R : Type} [CommRing R] [Fintype R] [DecidableEq R] {k : ℕ} {S : Setting R k}
  {Wd : Type} [Fintype Wd] [DecidableEq Wd] [Fintype S.Attr] [DecidableEq S.Attr]
  [DecidableEq S.ctBits.Index]

/-- The master secret key: the public key and the trapdoor `(e, t)` of `B₁`. -/
abbrev MSK (S : Setting R k) (Wd : Type) :=
  MPK S Wd (TrapCol k) × Matrix (Fin 1) (Col k) R × R

/-- **The law of `Setup`.** -/
noncomputable def setupLaw (χ : PMF R) : PMF (MPK S Wd (TrapCol k) × MSK S Wd) := do
  let B₀ ← PMF.uniformOfFintype (Matrix (Fin 1) Wd R)
  let a ← PMF.uniformOfFintype (Matrix (Fin 1) (Col k) R)
  let t ← χ
  let e ← rowLaw χ (Col k)
  let Bj ← PMF.uniformOfFintype (S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R)
  let p ← PMF.uniformOfFintype R
  let mpk : MPK S Wd (TrapCol k) := ⟨B₀, trapRow S a e t, Bj, p⟩
  pure (mpk, (mpk, e, t))

omit [DecidableEq R] in
/-- The trapdoor of `msk` satisfies `B₁ T = G̲`. -/
theorem msk_trapdoor (χ : PMF R) (v) (hv : v ∈ (setupLaw (S := S) (Wd := Wd) χ).support) :
    v.1.B₁ * trapMat v.2.2.1 v.2.2.2 = S.Γ₁.G ∧ v.2.1 = v.1 := by
  unfold setupLaw at hv
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hv
  obtain ⟨B₀, -, a, -, t, -, e, -, Bj, -, p, -, rfl⟩ := hv
  exact ⟨trapRow_mul_trapMat S a e t, rfl⟩

section Ring

variable {N K : ℕ} {S : Setting (Negacyclic (ZMod (2 ^ K)) N) k} [Fintype S.Attr]
  [DecidableEq S.Attr] [DecidableEq S.ctBits.Index]

/-- **`Setup` is realized by fair coins.** -/
theorem bitLaw_setup {χc : PMF (ZMod (2 ^ K))} {m : ℕ} (h : BitLaw χc m) :
    ∃ m', BitLaw (setupLaw (S := S) (Wd := Wd) (polyOf (N := N) χc)) m' := by
  unfold setupLaw
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure]
  exact ⟨_, BitLaw.bind (bitLaw_uniform_row Wd) fun B₀ =>
    BitLaw.bind (bitLaw_uniform_row (Col k)) fun a =>
    BitLaw.bind (BitLaw.polyOf h) fun t =>
    BitLaw.bind (bitLaw_rowLaw h (Col k)) fun e =>
    BitLaw.bind (BitLaw.uniform_fun (BitLaw.uniform_fun (BitLaw.uniform_fun
      (BitLaw.uniform_ring N K)))) fun Bj =>
    BitLaw.bind (BitLaw.uniform_ring N K) fun p => BitLaw.pure _⟩

end Ring

end AdvancedEncryption.RingBTVW
