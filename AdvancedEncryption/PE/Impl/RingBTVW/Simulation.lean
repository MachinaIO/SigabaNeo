import PE.Impl.RingBTVW.Scheme
import SigabaNeo.Lib.Lattices.Homomorphic.SLPSim

/-!
# Simulated keys (BTVW17 §4.2, `Setup*` and `KeyGen*`)

With the Ring-GSW ciphertexts of the paper, `Ψᵢ = A Rᵢ + xᵢ G` where the top row of `A` is `B₀`,
and the simulated public keys `B_j = B₀ W_j + ψ_j G̲` of the bits `ψ` of `Ψ`, the key matrix of a
predicate `f` is `B_f̂ = B₀ W_f + f(x) G̲` with an explicit `W_f` (`keyMatrix_sim`). When
`f(x) = 1`, `[B₀ | B_f̂] = [B₀ | B₀ W_f + G̲]` has the gadget trapdoor `W_f`, so keys can be sampled
without any trapdoor of `B₀`: the simulation behind an efficient security reduction.
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo.Lattices Matrix

variable {R : Type*} [CommRing R] {k : ℕ} {S : Setting R k} {m : Type*} [Fintype m]

/-- The short matrix of the simulated key matrix. -/
def simKeyMat (Rm : S.Attr → Matrix m (Col k) R) (x : S.Attr → Bool)
    (W : S.Attr × S.ctBits.Index → Matrix m (Col k) R) (Ψ : S.Attr → Matrix (Fin 2) (Col k) R)
    (Bj : S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R) (f : S.Pred) : Matrix m (Col k) R :=
  ∑ b, slpSim S.Γ₁ Bj W (bitsOf S Ψ) (S.fhat f).1 ((S.fhat f).2 b) * S.Γ₁.ginv (S.rowBits.V b) +
    evalSim S.Γ Ψ (fun i => bitR (R := R) (x i)) Rm (S.circ f)

/-- **The simulated key matrix**: `B_f̂ = B₀ W_f + f(x) G̲`. -/
theorem keyMatrix_sim (hfhat : S.FhatCorrect) (mpk : MPK S) (A : Matrix (Fin 2) m R)
    (Rm : S.Attr → Matrix m (Col k) R) (x : S.Attr → Bool)
    (W : S.Attr × S.ctBits.Index → Matrix m (Col k) R)
    (Ψ : S.Attr → Matrix (Fin 2) (Col k) R)
    (hΨ : ∀ i, Ψ i = A * Rm i + bitR (R := R) (x i) • S.Γ.G)
    (hB : ∀ j, mpk.Bj j = (Matrix.of fun _ c => A 0 c) * W j + bitsOf S Ψ j • S.Γ₁.G)
    (f : S.Pred) :
    keyMatrix mpk f = (Matrix.of fun _ c => A 0 c) * simKeyMat Rm x W Ψ mpk.Bj f +
      (S.circ f).eval (fun i => bitR (R := R) (x i)) • S.Γ₁.G := by
  set B₀ : Matrix (Fin 1) m R := Matrix.of fun _ c => A 0 c
  have hslp : ∀ b, slpPK S.Γ₁ mpk.Bj (S.fhat f).1 ((S.fhat f).2 b) =
      B₀ * slpSim S.Γ₁ mpk.Bj W (bitsOf S Ψ) (S.fhat f).1 ((S.fhat f).2 b) +
        S.rowBits.bits (topRow (evalMat S.Γ Ψ (S.circ f))) b • S.Γ₁.G := by
    intro b
    rw [slp_sim_relation S.Γ₁ B₀ mpk.Bj W (bitsOf S Ψ) hB, hfhat f Ψ b]
  have hsim := sim_relation S.Γ A Ψ (fun i => bitR (R := R) (x i)) Rm hΨ (S.circ f)
  have htop : topRow (evalMat S.Γ Ψ (S.circ f)) =
      B₀ * evalSim S.Γ Ψ (fun i => bitR (R := R) (x i)) Rm (S.circ f) +
        (S.circ f).eval (fun i => bitR (R := R) (x i)) • S.Γ₁.G := by
    rw [hsim]
    ext a c
    fin_cases a
    simp [topRow, B₀, Matrix.mul_apply, topRowGadget_G]
    rfl
  unfold keyMatrix simKeyMat
  simp only [hslp, Matrix.add_mul, Matrix.smul_mul, Finset.sum_add_distrib, S.Γ₁.mul_ginv]
  rw [S.rowBits.recompose, htop, Matrix.mul_add, Matrix.mul_sum]
  simp only [Matrix.mul_assoc]
  abel
