import PE.Impl.DualUse.KeyGen
import PE.Impl.DualUse.Noise
import PE.Impl.RingBTVW.Simulation

/-!
# Keys in the reductions: the trapdoor `W_f`

In the hybrid views the attribute ciphertexts are `Ψᵢ = A Rᵢ + xᵢ G` with `A = [B₀; c₀]` and the
public keys of the encodings are `B_j = B₀ W_j + ψ_j G̲`, for binary `Rᵢ`, `W_j` drawn by the
reductions themselves. For a predicate with `f(x) = 1` the key matrix is then `B_f̂ = B₀ W_f + G̲`
with `W_f = simKeyMat …` computed from `(Rᵢ, W_j, Ψ)` (`keyMatrix_eq_sim`), so `simTrap W_f`
satisfies the public relation of the key equation (`simTrap_public`): with a big box covering it
(`GoodTrap`), keys from the ideal law are exactly keys sampled with `W_f`
(`DualUse.keyLaw_eq_ideal`). The reductions of hybrids 3 and 5 thus answer key queries without any
trapdoor of `B`.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW

variable {R : Type*} [CommRing R] {k : ℕ} {S : Setting R k} {Wd Wt : Type*} [Fintype Wd]
  [Fintype Wt]

omit [Fintype Wt] [Fintype Wd] in
theorem keyMatrix_eq_old (mpk : MPK S Wd Wt) (f : S.Pred) :
    keyMatrix mpk f = RingBTVW.keyMatrix (oldMPK mpk) f := rfl

omit [Fintype Wt] in
/-- **The simulated key matrix**: `B_f̂ = B₀ W_f + f(x) G̲`. -/
theorem keyMatrix_eq_sim (hfhat : S.FhatCorrect) (mpk : MPK S Wd Wt) (c₀ : Matrix (Fin 1) Wd R)
    (Rm : S.Attr → Matrix Wd (Col k) R) (x : S.Attr → Bool)
    (W : S.Attr × S.ctBits.Index → Matrix Wd (Col k) R) (Ψ : S.Attr → Matrix (Fin 2) (Col k) R)
    (hΨ : ∀ i, Ψ i = gswPK mpk.B₀ c₀ * Rm i + bitR (R := R) (x i) • S.Γ.G)
    (hB : ∀ j, mpk.Bj j = mpk.B₀ * W j + bitsOf S Ψ j • S.Γ₁.G) (f : S.Pred) :
    keyMatrix mpk f = mpk.B₀ * simKeyMat Rm x W Ψ mpk.Bj f +
      (S.circ f).eval (fun i => bitR (R := R) (x i)) • S.Γ₁.G := by
  have hrow : (Matrix.of fun _ c => gswPK mpk.B₀ c₀ 0 c : Matrix (Fin 1) Wd R) = mpk.B₀ := by
    ext i c; fin_cases i; simp [gswPK]
  have h := keyMatrix_sim hfhat (oldMPK mpk) (gswPK mpk.B₀ c₀) Rm x W Ψ hΨ
    (fun j => by rw [hrow]; exact hB j) f
  rw [hrow] at h
  exact h

variable [DecidableEq R]

omit [DecidableEq R] in
/-- **`W_f` satisfies the public relation** of the key equation when `B_f̂ = B₀ W_f + G̲`. -/
theorem simTrap_public (mpk : MPK S Wd Wt) (W : Matrix Wd (Col k) R)
    (Bf : Matrix (Fin 1) (Col k) R) (hBf : Bf = mpk.B₀ * W + S.Γ₁.G) (z : Col k → R) :
    shortMap mpk (simTrap (Wt := Wt) W z) + gadgetMap (S := S) z = (Bf *ᵥ z) 0 := by
  have h := shortMap_simTrap (Wt := Wt) mpk W Bf hBf z
  rw [h, gadgetMap_eq, Matrix.sub_mulVec]
  simp

end AdvancedEncryption.DualUse
