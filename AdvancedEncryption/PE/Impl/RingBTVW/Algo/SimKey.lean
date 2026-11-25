import PE.Impl.RingBTVW.Algo.KeyMatrix
import PE.Impl.RingBTVW.SimKeys
import SigabaNeo.Lib.Lattices.Algo.SimWords

/-!
# The simulated trapdoor `W_f` of a predicate, on words

In the reductions the key matrix is `B_f̂ = B₀ W_f + f(x) G̲` with
`W_f = simKeyMat Rm x W Ψ B_j f` (`keyMatrix_eq_sim`):

  `W_f = ∑_b W_b · G̲⁻¹(V_b) + R_f`,

where `W_b` is the short matrix of the output wire `b` of `f̂` in the joint run of `f̂` on
`(B_j, W_j, ψ_j)` (`slpSim`), and `R_f` the short matrix of the Ring-GSW evaluation of `f` along
the circuit of the predicate (`evalSim`), which is the joint run of the predicate's program on
`(Ψᵢ, Rᵢ, xᵢ)` (`evalSim_circuit`).

`simKeyW` computes the word of `W_f` from the words of `B_j`, `W_j`, `Ψᵢ`, `Rᵢ` and the bits `xᵢ`, by
explicit loops: it generates `f̂` (`fhatProg`), computes the bits `ψ_j` of the `Ψᵢ` from their words
(`bitsW`), runs the two simulations on words (`slpSimRunW`, with the top-row and the Ring-GSW
binary gadgets) and sums (`keySumMW`). `simKeyW_eq`: at the orders of `fhatSLP` it is the word of
`simKeyMat … (predOf nA gs)`.
-/

namespace AdvancedEncryption.RingBTVW.Algo

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo Matrix
  AdvancedEncryption.RingBTVW.Fresh

variable {N K k : ℕ}

/-- The `0/1` ring words of the bits `ψ_j` of the attribute ciphertexts, from their words. -/
def psiBitsW (N K k : ℕ) (ψW : Fin nA → List Bool) (j : Fin nA × BI N k) : List Bool :=
  bitsW N K k (ψW j.1) j.2.1 j.2.2.1.1 j.2.2.1.2 j.2.2.2.1 j.2.2.2.2

/-- **`W_f` on words.** -/
def simKeyW (N K k d : ℕ) (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (gs : GateList) (bjW wW : Fin nA × BI N k → List Bool) (ψW rmW : Fin nA → List Bool)
    (xs : Fin nA → Bool) : List Bool :=
  matAddW N K (d * (2 * k))
    (keySumMW N K k d fun c i j =>
      if h : c < 2 * k ∧ i < k ∧ j < N then
        (slpSimRunW N K k 1 d (gadW N K k) (ginvW N K k) bjW wW (psiBitsW N K k ψW)
          (fhatProg K ordT ordO gs).1
          ((fhatProg K ordT ordO gs).2 (0, colE k ⟨c, h.1⟩, ⟨i, h.2.1⟩, ⟨j, h.2.2⟩))).2.1
      else [])
    (slpSimRunW N K k 2 d (gswGadW N K k) (ginvGswW N K k) ψW rmW
      (fun i => constW N K (bitW K (xs i))) (predOf nA gs).1 (predOf nA gs).2).2.1

theorem psiBitsW_enc (hk : 2 ^ K < 2 ^ k) (Ψ : Fin nA → Matrix (Fin 2) (Col k) (RingBTVW.Rg N K)) :
    psiBitsW N K k (fun i => colsW N K k 2 (Ψ i)) =
      fun j => (ringEnc N K).enc (bitsOf (Sdw (N := N) hk) Ψ j) := by
  funext j
  exact bitsW_enc hk.le (Ψ j.1) j.2.1 j.2.2.1 j.2.2.2.1 j.2.2.2.2

/-- **`simKeyW` computes `W_f`** at the orders of `fhatSLP`. -/
theorem simKeyW_eq (hk : 2 ^ K < 2 ^ k) {d : ℕ}
    (Rm : Fin nA → Matrix (Fin d) (Col k) (RingBTVW.Rg N K)) (x : Fin nA → Bool)
    (W : Fin nA × BI N k → Matrix (Fin d) (Col k) (RingBTVW.Rg N K))
    (Ψ : Fin nA → Matrix (Fin 2) (Col k) (RingBTVW.Rg N K))
    (Bj : Fin nA × BI N k → Matrix (Fin 1) (Col k) (RingBTVW.Rg N K)) (gs : GateList) :
    simKeyW N K k d (ordT₀ N k) (ordO₀ N k) gs (fun j => rowW N K k (Bj j))
      (fun j => colsW N K k d (W j)) (fun i => colsW N K k 2 (Ψ i)) (fun i => colsW N K k d (Rm i))
      x =
      colsW N K k d (simKeyMat (S := Sdw (N := N) hk) Rm x W Ψ Bj (predOf nA gs)) := by
  rw [simKeyW, psiBitsW_enc hk]
  have h2 : (slpSimRunW N K k 2 d (gswGadW N K k) (ginvGswW N K k) (fun i => colsW N K k 2 (Ψ i))
      (fun i => colsW N K k d (Rm i)) (fun i => constW N K (bitW K (x i))) (predOf nA gs).1
      (predOf nA gs).2).2.1 =
      colsW N K k d (evalSim (Sdw (N := N) hk).Γ Ψ (fun i => bitR (R := RingBTVW.Rg N K) (x i)) Rm
        ((Sdw (N := N) hk).circ (predOf nA gs))) := by
    have hx : (fun i => constW N K (bitW K (x i))) =
        fun i => (ringEnc N K).enc (bitR (R := RingBTVW.Rg N K) (x i)) := by
      funext i; exact (enc_bitR (x i)).symm
    rw [hx]
    exact (slpSim_words (gswGadgetW hk.le) Ψ Rm _ _ _).trans
      (congrArg _ (evalSim_circuit (gswB N K k hk.le) Ψ _ Rm _ _).symm)
  rw [h2]
  have h1 : keySumMW N K k d (fun c i j =>
      if h : c < 2 * k ∧ i < k ∧ j < N then
        (slpSimRunW N K k 1 d (gadW N K k) (ginvW N K k) (fun j => rowW N K k (Bj j))
          (fun j => colsW N K k d (W j))
          (fun j => (ringEnc N K).enc (bitsOf (Sdw (N := N) hk) Ψ j))
          (fhatProg K (ordT₀ N k) (ordO₀ N k) gs).1
          ((fhatProg K (ordT₀ N k) (ordO₀ N k) gs).2 (0, colE k ⟨c, h.1⟩, ⟨i, h.2.1⟩, ⟨j, h.2.2⟩))).2.1
      else []) =
      colsW N K k d (∑ b, slpSim (Sdw (N := N) hk).Γ₁ Bj W (bitsOf (Sdw (N := N) hk) Ψ)
        ((Sdw (N := N) hk).fhat (predOf nA gs)).1 (((Sdw (N := N) hk).fhat (predOf nA gs)).2 b) *
        (Sdw (N := N) hk).Γ₁.ginv ((Sdw (N := N) hk).rowBits.V b)) := by
    refine keySumMW_enc hk.le
      (fun b => slpSim (topBin N K k hk.le) Bj W (bitsOf (Sdw (N := N) hk) Ψ)
        ((Sdw (N := N) hk).fhat (predOf nA gs)).1 (((Sdw (N := N) hk).fhat (predOf nA gs)).2 b))
      _ ?_
    intro c i j
    rw [dite_eq_left_of_eq_true (eq_true ⟨c.isLt, i.isLt, j.isLt⟩), fhatProg, ← fhatSLP_eq_L hk]
    exact slpSim_words (topGadgetW hk.le) Bj W _ _ _
  refine (congrArg (fun z => matAddW N K (d * (2 * k)) z _) h1).trans ?_
  rw [colsW, colsW, matAddW_enc, colsW]
  rfl

end AdvancedEncryption.RingBTVW.Algo
