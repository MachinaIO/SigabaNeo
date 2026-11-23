import PE.Impl.ExpLUT.SimEval
import PE.Impl.ExpLUT.Noise
import Mathlib.Data.Matrix.Basic

/-!
# The coefficient bound of the simulation matrices (Appendix A, after Corollary 1)

Entrywise norm bounds (`MatBnd`, at the abstract norm `NormSpec` of `PE.Impl.ExpLUT.Noise`) on the
simulation matrices of Lemma 10 and Corollary 1. They have the same shape as the error bounds of
Lemma 9, with the helpers' simulation matrices (unit selectors, `B_χ = 1`) in place of the helpers'
errors, so C's recurrences are reused:

* `matBnd_simMul`: `D E + 2τ D β + Z` (Lemma 10.3, `E_Mul ≤ D E + 2τ D R* + Z*`);
* `matBnd_simAut`: `autBound S β Bχ E = D Bχ + (D E + 2τ D β + Bχ)` (Lemma 10.4, with `Bχ = 1`:
  `E_Aut ≤ D E + 2τ D R* + D + 1`);
* `matBnd_simRounds`, `matBnd_simLut`, `matBnd_simEval`: `step^[T] R*` with C's `stepBound`;
* for the scheme (`matBnd_simKey`): with programming entries of norm at most `R*` (`Z*` for the
  `Z_t`) and `‖1‖ ≤ 1`, `‖R̂_F‖ ≤ (stepBound S R* 1 Z*)^[T] R* ≤ γ^T (R* + Δ)`
  (`matBnd_simKey_closed`, `B_R̂` of eq. (5)).
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix

variable {R : Type*} [CommRing R] {S : Setting R} {Wb J Pos : Type*} [Fintype Wb] [Fintype J]
  (N : NormSpec S)

/-- A matrix with entries of norm at most `B`. -/
def MatBnd {ι κ : Type*} (X : Matrix ι κ R) (B : ℕ) : Prop := ∀ i j, N.nrm (X i j) ≤ B

variable {N}

theorem matBnd_mono {ι κ : Type*} {X : Matrix ι κ R} {B B' : ℕ} (h : MatBnd N X B) (hB : B ≤ B') :
    MatBnd N X B' := fun i j => (h i j).trans hB

theorem matBnd_add {ι κ : Type*} {X Y : Matrix ι κ R} {B B' : ℕ} (h : MatBnd N X B)
    (h' : MatBnd N Y B') : MatBnd N (X + Y) (B + B') := fun i j =>
  (N.nrm_add _ _).trans (Nat.add_le_add (h i j) (h' i j))

theorem matBnd_mul_ginv {ι : Type*} {X : Matrix ι (Col S.τ) R} {B : ℕ} (h : MatBnd N X B)
    (A : Matrix (Fin 2) (Col S.τ) R) : MatBnd N (X * S.ginv A) (S.gfac * B) := fun ℓ j =>
  rowBnd_vecMul_ginv (N := N) (fun c => h ℓ c) A j

theorem matBnd_sum {ι κ ι' : Type*} (T : Finset ι') {X : ι' → Matrix ι κ R} {B : ℕ}
    (h : ∀ t ∈ T, MatBnd N (X t) B) : MatBnd N (∑ t ∈ T, X t) (T.card * B) := fun i j => by
  rw [Matrix.sum_apply]
  exact N.nrm_sum_le _ _ _ fun t ht => h t ht i j

omit [Fintype Wb] [Fintype J] in
theorem matBnd_simS (A : Matrix (Fin 2) (Col S.τ) R) {Rd : Dig S.τ → SimMat Wb J S} {β : ℕ}
    (hd : ∀ t, MatBnd N (Rd t) β) : MatBnd N (simS A Rd) (2 * S.τ * S.gfac * β) := fun ℓ j => by
  rw [simS_apply]
  refine (N.nrm_sum_le _ _ (S.gfac * β) fun ri _ => matBnd_mul_ginv (hd _) A ℓ ri).trans
    (le_of_eq ?_)
  rw [Finset.card_univ, card_col]; ring

omit [Fintype Wb] [Fintype J] in
/-- **Mul** (Lemma 10.3): `D E + 2τ D β + Z` for a payload `μ` whose multiplication does not
increase norms. -/
theorem matBnd_simMul (A C : Matrix (Fin 2) (Col S.τ) R) {μ : R} (hμ : ∀ a, N.nrm (μ * a) ≤ N.nrm a)
    {Rc Z : SimMat Wb J S} {Rd : Dig S.τ → SimMat Wb J S} {E β Zb : ℕ} (hc : MatBnd N Rc E)
    (hZ : MatBnd N Z Zb) (hd : ∀ t, MatBnd N (Rd t) β) :
    MatBnd N (simMul A C μ Rc Z Rd) (S.gfac * E + 2 * S.τ * S.gfac * β + Zb) := by
  have h := matBnd_add (matBnd_add (matBnd_simS A hd) (matBnd_mul_ginv hc C))
    (show MatBnd N (μ • Z) Zb from fun i j => (hμ _).trans (hZ i j))
  exact matBnd_mono h (by omega)

omit [Fintype Wb] [Fintype J] in
theorem matBnd_simPerm (e : ℕ) {Rh : SimMat Wb J S} {E : ℕ} (h : MatBnd N Rh E) :
    MatBnd N (simPerm e Rh) E := fun _ j => (N.nrm_σ _ _ (S.idx_odd e)).trans (h _ j)

omit [Fintype Wb] [Fintype J] in
/-- **Aut_k** (Lemma 10.4): `autBound S β Bχ E = D Bχ + (D E + 2τ D β + Bχ)` for helper matrices
of norm at most `Bχ`, digit matrices `β` and a payload `μ` with `σ_k(μ)` norm-preserving. -/
theorem matBnd_simAut (e : ℕ) (Hk' : Matrix (Fin 2) (Col S.τ) R)
    (Aaut : Dig S.τ → Matrix (Fin 2) (Col S.τ) R) (A : Matrix (Fin 2) (Col S.τ) R) (hk' : Col S.τ → R)
    {μ : R} (hμ : ∀ a, N.nrm (S.E.σ (S.idx e) μ * a) ≤ N.nrm a) {Rhk RC Rc : SimMat Wb J S}
    {Rd : Dig S.τ → SimMat Wb J S} {Bχ β E : ℕ} (hh : MatBnd N Rhk Bχ) (hC : MatBnd N RC Bχ)
    (hd : ∀ t, MatBnd N (Rd t) β) (hc : MatBnd N Rc E) :
    MatBnd N (simAut e Hk' Aaut A hk' μ Rhk RC Rd Rc) (autBound S β Bχ E) :=
  matBnd_add (matBnd_mul_ginv hh _) (matBnd_simMul _ _ hμ (matBnd_simPerm e hc) hC hd)

/-- The bounds of the helpers' simulation matrices. -/
structure SimAutBnd (Q : SimAut Wb J S) (Bχ β : ℕ) : Prop where
  Rhf : ∀ t, MatBnd N (Q.Rhf t) Bχ
  RC : ∀ t, MatBnd N (Q.RC t) Bχ
  Raut : ∀ t d, MatBnd N (Q.Raut t d) β

omit [Fintype Wb] [Fintype J] in
/-- **The rounds**: after `t` rounds, `aut^[t] E`, for the monomial payload `X^u`. -/
theorem matBnd_simRounds (P : AutPub S) (A : Matrix (Fin 2) (Col S.τ) R) (h : AutData S)
    (Q : SimAut Wb J S) (u : ℕ) {Rc : SimMat Wb J S} {E β Bχ : ℕ} (hD : 1 ≤ S.gfac)
    (hc : MatBnd N Rc E) (hQ : SimAutBnd (N := N) Q Bχ β) :
    ∀ t j, MatBnd N (simRounds P A h Q (S.E.X ^ u) Rc t j) ((autBound S β Bχ)^[t] E) := by
  intro t
  induction t with
  | zero => intro j; simpa [simRounds] using hc
  | succ t ih =>
    intro j
    simp only [simRounds]
    split_ifs
    · exact matBnd_mono (ih j) (le_autBound_iterate hD _ _ _ _ _ (Nat.le_succ t))
    · rw [Function.iterate_succ_apply']
      refine matBnd_simAut _ _ _ _ _ (fun a => ?_) (hQ.Rhf t) (hQ.RC t) (hQ.Raut t) (ih _)
      rw [S.idx_add]
      exact NormSpec.nrm_σ_idx_X_pow_mul N _ _ _

/-- **The table**: `W D aut^[b] E`. -/
theorem matBnd_simLut (P : AutPub S) (coef : ℕ → R) (A : Matrix (Fin 2) (Col S.τ) R) (h : AutData S)
    (Q : SimAut Wb J S) (u : ℕ) {Rc : SimMat Wb J S} {E β Bχ : ℕ} (hD : 1 ≤ S.gfac)
    (hc : MatBnd N Rc E) (hQ : SimAutBnd (N := N) Q Bχ β) :
    MatBnd N (simLut P coef A h Q (S.E.X ^ u) Rc) (S.E.W * (S.gfac * (autBound S β Bχ)^[S.b] E)) := by
  have := matBnd_sum (Finset.range S.E.W) fun j _ =>
    matBnd_mul_ginv (matBnd_simRounds P A h Q u hD hc hQ S.b j) (coef j • S.G)
  rwa [Finset.card_range] at this

/-- The bounds of the fresh simulation matrices: `R*` for `c₀` and the digit encodings, `Z*` for
the input gadget ciphertexts, `Bχ` for the helpers. -/
structure SimFreshBnd (Q : SimFresh Wb J Pos S) (Rs Zs Bχ : ℕ) : Prop where
  R0 : MatBnd N Q.R0 Rs
  Zin : ∀ t, MatBnd N (Q.Zin t) Zs
  Rin : ∀ t d, MatBnd N (Q.Rin t d) Rs
  aut : SimAutBnd (N := N) Q.aut Bχ Rs

/-- **The evaluation**: after `i` steps, `step^[i] R*`. -/
theorem matBnd_simEvalAt (F : BP Pos) (pp : EvalPub S Pos) (ct : EvalCTData S Pos) (x : Pos → ℕ)
    {Q : SimFresh Wb J Pos S} {Rs Zs Bχ : ℕ} (hD : 1 ≤ S.gfac) (hQ : SimFreshBnd (N := N) Q Rs Zs Bχ) :
    ∀ i, MatBnd N (simEvalAt F pp ct x Q i) ((stepBound S Rs Bχ Zs)^[i] Rs) := by
  intro i
  induction i with
  | zero => simpa [simEvalAt] using hQ.R0
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    refine matBnd_simLut _ _ _ _ _ _ hD ?_ hQ.aut
    exact matBnd_simMul _ _ (fun a => N.nrm_X_pow_mul _ _) ih (hQ.Zin _) (hQ.Rin _)

theorem matBnd_simEval (F : BP Pos) (pp : EvalPub S Pos) (ct : EvalCTData S Pos) (x : Pos → ℕ)
    {Q : SimFresh Wb J Pos S} {Rs Zs Bχ : ℕ} (hD : 1 ≤ S.gfac) (hQ : SimFreshBnd (N := N) Q Rs Zs Bχ) :
    MatBnd N (simEval F pp ct x Q) ((stepBound S Rs Bχ Zs)^[F.T] Rs) :=
  matBnd_simEvalAt F pp ct x hD hQ F.T

/-! ### The scheme -/

variable [DecidableEq J]

omit [Fintype Wb] [Fintype J] [DecidableEq J] in
theorem matBnd_finExt {ι κ : Type*} {f : Fin S.b → Matrix ι κ R} {B : ℕ} (h : ∀ t, MatBnd N (f t) B)
    (t : ℕ) : MatBnd N (finExt f t) B := by
  unfold finExt
  split_ifs
  · exact h _
  · intro i j; simp [N.nrm_zero]

omit [Fintype Wb] [Fintype J] in
theorem matBnd_jη (h1 : N.nrm 1 ≤ 1) (i : Fin S.E.W) (k : J) : MatBnd N (jη (Wb := Wb) i k) 1 := by
  intro c j
  rcases c with ⟨i', w⟩ | ⟨i', k', c'⟩
  · simp [jη, N.nrm_zero]
  · simp only [jη, Matrix.of_apply]
    split_ifs
    · exact h1
    · simp [N.nrm_zero]

omit [Fintype Wb] [Fintype J] [DecidableEq J] in
theorem matBnd_jβ (i : Fin S.E.W) {Z : Matrix Wb (Col S.τ) R} {B : ℕ} (hZ : MatBnd N Z B) :
    MatBnd N (jβ (J := J) i Z) B := by
  intro c j
  rcases c with ⟨i', w⟩ | ⟨i', k', c'⟩
  · simp only [jβ, Matrix.of_apply]
    split_ifs
    · exact hZ w j
    · simp [N.nrm_zero]
  · simp [jβ, N.nrm_zero]

/-- Bounds on the programming matrices: `Z*` for the `Z_t`, `R*` for the others. -/
structure ProgBnd (P : Prog S Wb J Pos) (Rs Zs : ℕ) : Prop where
  Z : ∀ t, MatBnd N (P.Z t) Zs
  R0 : MatBnd N P.R0 Rs
  Rin : ∀ t d, MatBnd N (P.Rin t d) Rs
  Raut : ∀ t d, MatBnd N (P.Raut t d) Rs

omit [Fintype Wb] [Fintype J] in
theorem simFreshBnd_of (M : HelperMap S J) (h1 : N.nrm 1 ≤ 1) {P : Prog S Wb J Pos} {Rs Zs : ℕ}
    (hP : ProgBnd (N := N) P Rs Zs) : SimFreshBnd (N := N) (simFreshOf M P) Rs Zs 1 where
  R0 := matBnd_jβ _ hP.R0
  Zin t := matBnd_jβ _ (hP.Z t)
  Rin t d := matBnd_jβ _ (hP.Rin t d)
  aut :=
    { Rhf := matBnd_finExt (f := fun t => jη S.row0 (M.fwd t)) fun _ => matBnd_jη h1 _ _
      RC := matBnd_finExt (f := fun t => jη (S.rowT t) (M.inv t)) fun _ => matBnd_jη h1 _ _
      Raut := fun t d => by
        simp only [simFreshOf]
        unfold finExt
        split_ifs
        · exact matBnd_jβ _ (hP.Raut _ d)
        · intro i j; simp [N.nrm_zero] }

/-- **The coefficient bound of `R̂_F`**: `(stepBound S R* 1 Z*)^[T] R*`. -/
theorem matBnd_simKey (M : HelperMap S J) (h1 : N.nrm 1 ≤ 1) (hD : 1 ≤ S.gfac)
    (mpk : MPK S Wb J Pos) (F : BP Pos) (ct : Ciphertext S Wb J Pos) (x : Pos → ℕ)
    {P : Prog S Wb J Pos} {Rs Zs : ℕ} (hP : ProgBnd (N := N) P Rs Zs) :
    MatBnd N (simKey M mpk F ct x P) ((stepBound S Rs 1 Zs)^[F.T] Rs) :=
  matBnd_simEval F _ _ x hD (simFreshBnd_of M h1 hP)

/-- **`B_R̂` of eq. (5)**: `‖R̂_F‖ ≤ γ^T (R* + Δ)` for `D ≥ 2`. -/
theorem matBnd_simKey_closed (M : HelperMap S J) (h1 : N.nrm 1 ≤ 1) (hD : 2 ≤ S.gfac)
    (mpk : MPK S Wb J Pos) (F : BP Pos) (ct : Ciphertext S Wb J Pos) (x : Pos → ℕ)
    {P : Prog S Wb J Pos} {Rs Zs : ℕ} (hP : ProgBnd (N := N) P Rs Zs) :
    MatBnd N (simKey M mpk F ct x P) (gammaB S ^ F.T * (Rs + deltaB S Rs 1 Zs)) :=
  matBnd_mono (matBnd_simKey M h1 (by omega) mpk F ct x hP)
    (stepBound_iterate_le hD S.E.W_pos _ _ _ _ _)

end AdvancedEncryption.ExpLUT
