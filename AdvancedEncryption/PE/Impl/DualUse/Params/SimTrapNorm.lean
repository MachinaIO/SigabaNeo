import PE.Impl.DualUse.SimKeys
import PE.Impl.RingBTVW.NoiseClosed
import SigabaNeo.Lib.Lattices.SimNorm

/-!
# The norm of the simulated trapdoor

In the reductions, keys are sampled with the trapdoor `W_f = simKeyMat …` of
`[B₀ | B₀ W_f + G̲]` (`DualUse.keyMatrix_eq_sim`). Its two parts evolve like errors of `EvalFX`
(`SigabaNeo.Lattices.rowOf_slpSim`, `rowOf_evalSim`): the BGG+ part along the program of `f̂` from
the binary `W_j`, the Ring-GSW part along the circuit of `f` from the binary `Rᵢ`. So, over
`ℤ_q[X]/(X^N + 1)` with binary decompositions, every row of `W_f` has norm at most the noise
term of decryption with `Bχ = 1` (`rnorm_rowOf_simKeyMat_le`), in closed form
`(|rowBits| WN + 1) G^n` with `WN = |W| N`, `G = gswFactor WN N k` and `n` gates
(`rnorm_rowOf_simKeyMat_le_closed`). The shift of a key by `simTrap W_f` at a binary `z`
(`z = dec y`) is then at most `simTrapBound N k n = WN (|rowBits| WN + 1) G^n` in every
coefficient (`cnorm_simTrap_le`); it does not depend on `|Wd|`.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib

variable {N q k : ℕ} [NeZero q] (hk : q < 2 ^ k) {Attr : Type} [Fintype Attr] {m : Type*}

/-- The bound on the shift of the simulated trapdoor, for predicates of `n` gates. -/
def simTrapBound (N k n : ℕ) : ℕ :=
  Fintype.card (Col k) * N * ((Fintype.card (Fin 1 × Col k × Fin k × Fin N) *
    (Fintype.card (Col k) * N) + 1) * gswFactor (Fintype.card (Col k) * N) N k ^ n)

omit [Fintype Attr] in
/-- **The rows of `W_f`** are within the noise term of decryption with unit errors. -/
theorem rnorm_rowOf_simKeyMat_le (Rm : Attr → Matrix m (Col k) (Negacyclic (ZMod q) N))
    (x : Attr → Bool)
    (W : Attr × (ringSetting N q k hk Attr).ctBits.Index → Matrix m (Col k) (Negacyclic (ZMod q) N))
    (Ψ : Attr → Matrix (Fin 2) (Col k) (Negacyclic (ZMod q) N))
    (Bj : Attr × (ringSetting N q k hk Attr).ctBits.Index → Matrix (Fin 1) (Col k) (Negacyclic (ZMod q) N))
    (f : SLP Attr × Wire Attr) (hR : ∀ i a c, cnorm (Rm i a c) ≤ 1)
    (hW : ∀ j a c, cnorm (W j a c) ≤ 1) (i : m) :
    rnorm (rowOf (simKeyMat (S := ringSetting N q k hk Attr) Rm x W Ψ Bj f) i) ≤
      ∑ b, Fintype.card (Col k) * N * slpBound (Fintype.card (Col k) * N) 1
        ((ringSetting N q k hk Attr).fhat f).1 (((ringSetting N q k hk Attr).fhat f).2 b) +
        errBound (Fintype.card (Col k) * N) 1 (f.1.circuit f.2) := by
  have hΓ₁ : ∀ A c c', cnorm ((ringSetting N q k hk Attr).Γ₁.ginv A c c') ≤ 1 := fun A c c' =>
    cnorm_gadgetOf_binary_ginv_le hk.le (fun _ : Fin 1 => (0 : Fin 2)) _ A c c'
  have hΓ : ∀ A c c', cnorm ((ringSetting N q k hk Attr).Γ.ginv A c c') ≤ 1 := fun A c c' =>
    cnorm_gadgetOf_binary_ginv_le hk.le id _ A c c'
  have hψ : ∀ j, bitsOf (ringSetting N q k hk Attr) Ψ j = 0 ∨ bitsOf (ringSetting N q k hk Attr) Ψ j = 1 := fun j => by
    have hb := coeffBits_isBoolean (N := N) hk.le (Fin 2) (Ψ j.1) j.2
    rcases bitR_bit (R := Negacyclic (ZMod q) N) (coeffBool (Ψ j.1) j.2) with h | h
    · exact Or.inl (hb.trans h)
    · exact Or.inr (hb.trans h)
  unfold simKeyMat
  rw [rowOf_add]
  refine (rnorm_add_le _ _).trans (Nat.add_le_add ?_ ?_)
  · have rs : ∀ M : (ringSetting N q k hk Attr).rowBits.Index → Matrix m (Col k) (Negacyclic (ZMod q) N),
        rowOf (∑ b, M b) i = ∑ b, rowOf (M b) i := by
      intro M; ext a c; simp [rowOf, Matrix.sum_apply]
    rw [rs]
    simp only [rowOf_mul]
    refine (rnorm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    refine (rnorm_mul_le _ _ 1 (hΓ₁ _)).trans ?_
    rw [mul_one]
    exact Nat.mul_le_mul_left _
      (rnorm_rowOf_slpSim_le (ringSetting N q k hk Attr).Γ₁ hΓ₁ Bj W _ hψ 1 hW _ _ i)
  · exact rnorm_rowOf_evalSim_le (ringSetting N q k hk Attr).Γ hΓ _ _ (fun j => bitR_bit _) Rm 1 hR (f.1.circuit f.2) i

omit [Fintype Attr] in
/-- **The rows of `W_f` in closed form**: at most `(|rowBits| WN + 1) G^n`. -/
theorem rnorm_rowOf_simKeyMat_le_closed (Rm : Attr → Matrix m (Col k) (Negacyclic (ZMod q) N))
    (x : Attr → Bool)
    (W : Attr × (ringSetting N q k hk Attr).ctBits.Index → Matrix m (Col k) (Negacyclic (ZMod q) N))
    (Ψ : Attr → Matrix (Fin 2) (Col k) (Negacyclic (ZMod q) N))
    (Bj : Attr × (ringSetting N q k hk Attr).ctBits.Index → Matrix (Fin 1) (Col k) (Negacyclic (ZMod q) N))
    (f : SLP Attr × Wire Attr) (hR : ∀ i a c, cnorm (Rm i a c) ≤ 1)
    (hW : ∀ j a c, cnorm (W j a c) ≤ 1) (i : m) :
    rnorm (rowOf (simKeyMat (S := ringSetting N q k hk Attr) Rm x W Ψ Bj f) i) ≤
      (Fintype.card (Fin 1 × Col k × Fin k × Fin N) * (Fintype.card (Col k) * N) + 1) *
        gswFactor (Fintype.card (Col k) * N) N k ^ f.1.length := by
  set WN := Fintype.card (Col k) * N
  set G := gswFactor WN N k
  refine (rnorm_rowOf_simKeyMat_le hk Rm x W Ψ Bj f hR hW i).trans ?_
  have hs : ∀ b, slpBound WN 1 ((ringSetting N q k hk Attr).fhat f).1
      (((ringSetting N q k hk Attr).fhat f).2 b) ≤ G ^ f.1.length * 1 := fun b =>
    nb_fhatSLP WN 1 hk f.1 f.2 _
  have he : errBound WN 1 (f.1.circuit f.2) ≤ G ^ f.1.length * 1 := by
    rw [errBound_circuit]
    exact (slpBound_le_length WN 1 f.1 f.2).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (le_gswFactor WN N k) _))
  have hsum : ∑ b, WN * slpBound WN 1 ((ringSetting N q k hk Attr).fhat f).1
      (((ringSetting N q k hk Attr).fhat f).2 b) ≤
      Fintype.card (Fin 1 × Col k × Fin k × Fin N) * (WN * (G ^ f.1.length * 1)) := by
    refine (Finset.sum_le_sum fun b _ => Nat.mul_le_mul_left WN (hs b)).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rfl
  calc _ ≤ Fintype.card (Fin 1 × Col k × Fin k × Fin N) * (WN * (G ^ f.1.length * 1)) +
        G ^ f.1.length * 1 := Nat.add_le_add hsum he
    _ = _ := by ring

omit [Fintype Attr] in
/-- **The shift of the simulated trapdoor**: for binary `Rᵢ`, `W_j` and `z` (`z = dec y`),
`simTrap W_f z = (W_f z, 0)` has coefficients at most `simTrapBound N k n`. -/
theorem cnorm_simTrap_le {Wt : Type*} (Rm : Attr → Matrix m (Col k) (Negacyclic (ZMod q) N))
    (x : Attr → Bool)
    (W : Attr × (ringSetting N q k hk Attr).ctBits.Index → Matrix m (Col k) (Negacyclic (ZMod q) N))
    (Ψ : Attr → Matrix (Fin 2) (Col k) (Negacyclic (ZMod q) N))
    (Bj : Attr × (ringSetting N q k hk Attr).ctBits.Index → Matrix (Fin 1) (Col k) (Negacyclic (ZMod q) N))
    (f : SLP Attr × Wire Attr) (hR : ∀ i a c, cnorm (Rm i a c) ≤ 1)
    (hW : ∀ j a c, cnorm (W j a c) ≤ 1) (z : Col k → Negacyclic (ZMod q) N)
    (hz : ∀ c, cnorm (z c) ≤ 1) :
    (∀ i, cnorm ((simTrap (Wt := Wt) (simKeyMat (S := ringSetting N q k hk Attr) Rm x W Ψ Bj f)
        z).1 i) ≤ simTrapBound N k f.1.length) ∧
      ∀ i, cnorm ((simTrap (Wt := Wt) (simKeyMat (S := ringSetting N q k hk Attr) Rm x W Ψ Bj f)
        z).2 i) ≤ simTrapBound N k f.1.length := by
  refine ⟨fun i => ?_, fun i => by simp [simTrap, cnorm_zero]⟩
  have h := cnorm_mulVec_le _ z _ 1 (rnorm_rowOf_simKeyMat_le_closed hk Rm x W Ψ Bj f hR hW) hz i
  rw [mul_one] at h
  show cnorm ((simKeyMat _ _ _ _ _ _ *ᵥ z) i) ≤ _
  simpa only [simTrapBound, mul_assoc] using h

end AdvancedEncryption.DualUse
