import PE.Impl.ExpLUT.Eval

/-!
# Noise bounds of the operations and of Lemma 9

Norm-level bounds on the exact errors of `PE.Impl.ExpLUT.Ops`, `LUT`, `Eval`, for an abstract
coefficient norm (`NormSpec`): subadditive, symmetric, `‖ab‖ ≤ n ‖a‖ ‖b‖`, binary gadget digits
(`‖d_i(a)‖ ≤ 1`), multiplication by a monomial `X^p` and the automorphisms `σ_k` (odd `k`) do not
increase it. Over `ℤ_q[X]/(X^n + 1)` the centered `cnorm` (`SigabaNeo.Lattices.cnorm`) is such a
norm. Write `D = 2τn` (`Setting.gfac`): a binary gadget product multiplies bounds by at most `D`
(`rowBnd_vecMul_ginv`).

* `rowBnd_mulErr` (eq. (1)): `D E + 2τ D β + F` for an input error `E`, digit errors `β` and a
  gadget-ciphertext error `F` times a monomial payload.
* `rowBnd_autErr`: `D B_h + 2τ D β + D E + B_h'`.
* `rowBnd_roundsErr`, `rowBnd_lutErr` (Lemma 8): `aut^[t] E` after `t` rounds (`autBound`), and
  `W D aut^[b] E` for the table; closed form `aut^[t] E + 2c ≤ D^t (E + 2c)`,
  `c = 2τβ + 2B_χ`, when `D ≥ 2` (`autBound_iterate_le`).
* `rowBnd_evalErr` (Lemma 9): `e_F ≤ step^[T] B₀` (`stepBound`), and the closed form
  `step^[T] B₀ ≤ γ^T (B₀ + Δ)` with `γ = W D^{b+2}` and
  `Δ = W D^{b+1} (2τ D β + B_C + 4τβ + 4B_χ)` (`stepBound_iterate_le`), as in Lemma 9.
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix

variable {R : Type*} [CommRing R]

/-- A coefficient norm compatible with the setting. -/
structure NormSpec (S : Setting R) where
  /-- The norm. -/
  nrm : R → ℕ
  nrm_zero : nrm 0 = 0
  nrm_add : ∀ a b, nrm (a + b) ≤ nrm a + nrm b
  nrm_neg : ∀ a, nrm (-a) = nrm a
  nrm_mul : ∀ a b, nrm (a * b) ≤ S.E.n * nrm a * nrm b
  /-- Binary gadget digits. -/
  nrm_digit : ∀ a i, nrm (S.D.d a i) ≤ 1
  /-- Monomials are signed permutations of the coefficients. -/
  nrm_X_pow_mul : ∀ p a, nrm (S.E.X ^ p * a) ≤ nrm a
  /-- Automorphisms are signed permutations of the coefficients. -/
  nrm_σ : ∀ k a, Odd k → nrm (S.E.σ k a) ≤ nrm a

variable {S : Setting R} (N : NormSpec S)

/-- `D = 2τn`, the growth factor of a binary gadget product. -/
abbrev Setting.gfac (S : Setting R) : ℕ := 2 * S.τ * S.E.n

/-- A row (or family) with entries of norm at most `B`. -/
def RowBnd {ι : Type*} (v : ι → R) (B : ℕ) : Prop := ∀ i, N.nrm (v i) ≤ B

namespace NormSpec

theorem nrm_sub (a b : R) : N.nrm (a - b) ≤ N.nrm a + N.nrm b := by
  rw [sub_eq_add_neg]; exact (N.nrm_add _ _).trans (by rw [N.nrm_neg])

theorem nrm_sum {ι : Type*} (s : Finset ι) (f : ι → R) : N.nrm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, N.nrm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [N.nrm_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (N.nrm_add _ _).trans (Nat.add_le_add_left ih _)

theorem nrm_sum_le {ι : Type*} (s : Finset ι) (f : ι → R) (B : ℕ) (h : ∀ i ∈ s, N.nrm (f i) ≤ B) :
    N.nrm (∑ i ∈ s, f i) ≤ s.card * B :=
  (N.nrm_sum s f).trans ((Finset.sum_le_sum h).trans (by simp))

/-- `σ_{g^j}(X^p) = X^{g^j p}`. -/
theorem σ_idx_X_pow (j p : ℕ) : S.E.σ (S.idx j) (S.E.X ^ p) = S.E.X ^ (S.idx j * p) := by
  rw [map_pow, S.E.σ_X _ (S.idx_odd j), ← pow_mul]

theorem nrm_σ_idx_X_pow_mul (j p : ℕ) (a : R) : N.nrm (S.E.σ (S.idx j) (S.E.X ^ p) * a) ≤ N.nrm a := by
  rw [σ_idx_X_pow]; exact N.nrm_X_pow_mul _ _

end NormSpec

theorem card_col (τ : ℕ) : Fintype.card (Col τ) = 2 * τ := by simp

variable {N}

theorem rowBnd_mono {ι : Type*} {v : ι → R} {B B' : ℕ} (h : RowBnd N v B) (hB : B ≤ B') :
    RowBnd N v B' := fun i => (h i).trans hB

/-- **A binary gadget product** multiplies the bound by `D = 2τn`. -/
theorem rowBnd_vecMul_ginv {v : Col S.τ → R} {B : ℕ} (h : RowBnd N v B) (A : Matrix (Fin 2) (Col S.τ) R) :
    RowBnd N (v ᵥ* S.ginv A) (S.gfac * B) := by
  intro c
  simp only [Matrix.vecMul, dotProduct]
  refine (N.nrm_sum_le _ _ (S.E.n * B) fun c' _ => ?_).trans (le_of_eq ?_)
  · refine (N.nrm_mul _ _).trans ?_
    rw [ginv_apply]
    calc S.E.n * N.nrm (v c') * N.nrm (S.D.d (A c'.1 c) c'.2) ≤ S.E.n * B * 1 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (h c')) (N.nrm_digit _ _)
      _ = S.E.n * B := mul_one _
  · rw [Finset.card_univ, card_col]; ring

theorem rowBnd_smulCT {e : Col S.τ → R} {B : ℕ} (h : RowBnd N e B) (α : R) :
    RowBnd N (smulCT S α e) (S.gfac * B) := rowBnd_vecMul_ginv h _

theorem rowBnd_σ {e : Col S.τ → R} {B : ℕ} (h : RowBnd N e B) {k : ℕ} (hk : Odd k) :
    RowBnd N (autRow S k e) B := fun i => (N.nrm_σ k _ hk).trans (h i)

/-- **Mul** (eq. (1)): the error is at most `D E + 2τ D β + F`. -/
theorem rowBnd_mulErr (A C : Matrix (Fin 2) (Col S.τ) R) (μ : R) {f e : Col S.τ → R}
    {ed : Dig S.τ → Col S.τ → R} {E β F : ℕ} (he : RowBnd N e E) (hed : ∀ t, RowBnd N (ed t) β)
    (hf : ∀ j, N.nrm (μ * f j) ≤ F) :
    RowBnd N (mulErr S A C μ f ed e) (S.gfac * E + 2 * S.τ * S.gfac * β + F) := by
  intro j
  refine (N.nrm_sub _ _).trans (Nat.add_le_add_right ?_ _ |>.trans (Nat.add_le_add_left (hf j) _))
  refine (N.nrm_sum_le _ _ (S.gfac * β + S.E.n * E) fun ri _ => ?_).trans (le_of_eq ?_)
  · refine (N.nrm_add _ _).trans (Nat.add_le_add (rowBnd_vecMul_ginv (hed _) A ri) ?_)
    refine (N.nrm_mul _ _).trans ?_
    calc S.E.n * N.nrm (digits S C (ri.1, j, ri.2)) * N.nrm (e ri) ≤ S.E.n * 1 * E :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (N.nrm_digit _ _)) (he ri)
      _ = S.E.n * E := by ring
  · rw [Finset.card_univ, card_col]; ring

/-- **Aut_k**: the error is at most `D B_h + (D E + 2τ D β + B_h')`, for a payload `μ` whose image
`σ_k(μ)` does not increase norms by multiplication. -/
theorem rowBnd_autErr {k : ℕ} (hk : Odd k) (Hk' : Matrix (Fin 2) (Col S.τ) R)
    (Aaut : Dig S.τ → Matrix (Fin 2) (Col S.τ) R) (A : Matrix (Fin 2) (Col S.τ) R) (hk' : Col S.τ → R)
    {μ : R} (hμ : ∀ a, N.nrm (S.E.σ k μ * a) ≤ N.nrm a) {ek ek' e : Col S.τ → R}
    {ed : Dig S.τ → Col S.τ → R} {Bh Bh' β E : ℕ} (hek : RowBnd N ek Bh) (hek' : RowBnd N ek' Bh')
    (hed : ∀ t, RowBnd N (ed t) β) (he : RowBnd N e E) :
    RowBnd N (autErr S k Hk' Aaut A hk' μ ek ek' ed e)
      (S.gfac * Bh + (S.gfac * E + 2 * S.τ * S.gfac * β + Bh')) := by
  intro j
  refine (N.nrm_add _ _).trans (Nat.add_le_add (rowBnd_vecMul_ginv hek _ j) ?_)
  refine rowBnd_mulErr _ _ _ (rowBnd_σ he hk) hed (fun i => ?_) j
  refine (hμ _).trans ?_
  simp only [Pi.neg_apply, N.nrm_neg]
  exact rowBnd_σ hek' hk i

/-! ### Rounds and tables -/

variable (S) in
/-- The bound after one automorphism, for helpers with errors `B_χ` and digit errors `β`. -/
def autBound (β Bχ E : ℕ) : ℕ := S.gfac * Bχ + (S.gfac * E + 2 * S.τ * S.gfac * β + Bχ)

theorem autBound_mono (β Bχ : ℕ) : Monotone (autBound S β Bχ) := fun a b h => by
  unfold autBound; gcongr

theorem le_autBound (hD : 1 ≤ S.gfac) (β Bχ E : ℕ) : E ≤ autBound S β Bχ E := by
  have := Nat.le_mul_of_pos_left E hD
  unfold autBound; omega

theorem le_autBound_iterate (hD : 1 ≤ S.gfac) (β Bχ E : ℕ) :
    ∀ t t', t ≤ t' → (autBound S β Bχ)^[t] E ≤ (autBound S β Bχ)^[t'] E := by
  intro t t' h
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (le_autBound hD _ _ _)

/-- **The rounds**: after `t ≤ b` rounds, every `c_j` has error at most `aut^[t] E`, for the
monomial input payload `X^u`. -/
theorem rowBnd_roundsErr (P : AutPub S) (A : Matrix (Fin 2) (Col S.τ) R) (h er : AutData S) (u : ℕ)
    {e : Col S.τ → R} {E β Bχ : ℕ} (hD : 1 ≤ S.gfac) (he : RowBnd N e E)
    (hf : ∀ t, RowBnd N (er.hf t) Bχ) (hi : ∀ t, RowBnd N (er.hi t) Bχ)
    (hd : ∀ t d, RowBnd N (er.caut t d) β) :
    ∀ t, ∀ j, RowBnd N (roundsErr P A h (S.E.X ^ u) er e t j) ((autBound S β Bχ)^[t] E) := by
  intro t
  induction t with
  | zero => intro j; simpa [roundsErr] using he
  | succ t ih =>
    intro j
    simp only [roundsErr]
    split_ifs
    · exact rowBnd_mono (ih j) (le_autBound_iterate hD _ _ _ _ _ (Nat.le_succ t))
    · rw [Function.iterate_succ_apply']
      refine rowBnd_autErr (S.idx_odd _) _ _ _ _ (fun a => ?_) (hf t) (hi t) (hd t) (ih _)
      rw [NormSpec.σ_idx_X_pow, map_pow, S.E.σ_X _ (S.idx_odd _), ← pow_mul]
      exact N.nrm_X_pow_mul _ _

/-- **The table** (Lemma 8): the error is at most `W D aut^[b] E`. -/
theorem rowBnd_lutErr (P : AutPub S) (coef : ℕ → R) (A : Matrix (Fin 2) (Col S.τ) R) (h er : AutData S)
    (u : ℕ) {e : Col S.τ → R} {E β Bχ : ℕ} (hD : 1 ≤ S.gfac) (he : RowBnd N e E)
    (hf : ∀ t, RowBnd N (er.hf t) Bχ) (hi : ∀ t, RowBnd N (er.hi t) Bχ)
    (hd : ∀ t d, RowBnd N (er.caut t d) β) :
    RowBnd N (lutErr P coef A h (S.E.X ^ u) er e) (S.E.W * (S.gfac * (autBound S β Bχ)^[S.b] E)) := by
  intro c
  simp only [lutErr, Finset.sum_apply]
  refine (N.nrm_sum_le _ _ _ fun j _ => ?_).trans (by rw [Finset.card_range])
  exact rowBnd_smulCT (rowBnd_roundsErr P A h er u hD he hf hi hd S.b j) _ c

/-- Closed form of the rounds: `aut^[t] E + 2c ≤ D^t (E + 2c)` with `c = 2τβ + 2B_χ`, for `D ≥ 2`. -/
theorem autBound_iterate_le (hD : 2 ≤ S.gfac) (β Bχ E : ℕ) (t : ℕ) :
    (autBound S β Bχ)^[t] E + 2 * (2 * S.τ * β + 2 * Bχ) ≤
      S.gfac ^ t * (E + 2 * (2 * S.τ * β + 2 * Bχ)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    generalize (autBound S β Bχ)^[t] E = Y at ih ⊢
    have h1 : autBound S β Bχ Y + 2 * (2 * S.τ * β + 2 * Bχ) ≤
        S.gfac * (Y + 2 * (2 * S.τ * β + 2 * Bχ)) := by
      unfold autBound
      have h2c : 2 * (2 * S.τ * β + 2 * Bχ) ≤ S.gfac * (2 * S.τ * β + 2 * Bχ) :=
        Nat.mul_le_mul_right _ hD
      have hB : Bχ ≤ S.gfac * Bχ := Nat.le_mul_of_pos_left Bχ (by omega)
      ring_nf at h2c hB ⊢
      omega
    calc autBound S β Bχ Y + 2 * (2 * S.τ * β + 2 * Bχ) ≤
          S.gfac * (Y + 2 * (2 * S.τ * β + 2 * Bχ)) := h1
      _ ≤ S.gfac * (S.gfac ^ t * (E + 2 * (2 * S.τ * β + 2 * Bχ))) := Nat.mul_le_mul_left _ ih
      _ = S.gfac ^ t * S.gfac * (E + 2 * (2 * S.τ * β + 2 * Bχ)) := by ring

/-! ### Branching programs (Lemma 9) -/

variable (S) in
/-- The bound after one step of a branching program: `Mul` by an input ciphertext with error `B_C`,
then a table. -/
def stepBound (β Bχ BC E : ℕ) : ℕ :=
  S.E.W * (S.gfac * (autBound S β Bχ)^[S.b] (S.gfac * E + 2 * S.τ * S.gfac * β + BC))

/-- The bounds on the errors of the ciphertext data. -/
structure ErrBounds {Pos : Type*} (N : NormSpec S) (er : EvalErrs S Pos) (B0 β BC Bχ : ℕ) : Prop where
  e0 : RowBnd N er.e0 B0
  fin : ∀ t, RowBnd N (er.fin t) BC
  ein : ∀ t d, RowBnd N (er.ein t d) β
  hf : ∀ t, RowBnd N (er.aut.hf t) Bχ
  hi : ∀ t, RowBnd N (er.aut.hi t) Bχ
  caut : ∀ t d, RowBnd N (er.aut.caut t d) β

/-- **Lemma 9, the error**: after `i` steps, the error is at most `step^[i] B₀`. -/
theorem rowBnd_evalErrAt {Pos : Type*} (F : BP Pos) (pp : EvalPub S Pos) (ct : EvalCTData S Pos)
    (x : Pos → ℕ) {er : EvalErrs S Pos} {B0 β BC Bχ : ℕ} (hD : 1 ≤ S.gfac)
    (hb : ErrBounds N er B0 β BC Bχ) :
    ∀ i, RowBnd N (evalErrAt F pp ct x er i) ((stepBound S β Bχ BC)^[i] B0) := by
  intro i
  induction i with
  | zero => simpa [evalErrAt] using hb.e0
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    refine rowBnd_lutErr _ _ _ _ _ _ hD ?_ hb.hf hb.hi hb.caut
    exact rowBnd_mulErr _ _ _ ih (hb.ein _) fun j => (N.nrm_X_pow_mul _ _).trans (hb.fin _ j)

theorem rowBnd_evalErr {Pos : Type*} (F : BP Pos) (pp : EvalPub S Pos) (ct : EvalCTData S Pos)
    (x : Pos → ℕ) {er : EvalErrs S Pos} {B0 β BC Bχ : ℕ} (hD : 1 ≤ S.gfac)
    (hb : ErrBounds N er B0 β BC Bχ) :
    RowBnd N (evalErr F pp ct x er) ((stepBound S β Bχ BC)^[F.T] B0) :=
  rowBnd_evalErrAt F pp ct x hD hb F.T

variable (S) in
/-- `γ = W D^{b+2}`. -/
def gammaB : ℕ := S.E.W * S.gfac ^ (S.b + 2)

variable (S) in
/-- `Δ = W D^{b+1} (2τ D β + B_C + 4τβ + 4B_χ)`. -/
def deltaB (β Bχ BC : ℕ) : ℕ :=
  S.E.W * S.gfac ^ (S.b + 1) * (2 * S.τ * S.gfac * β + BC + 2 * (2 * S.τ * β + 2 * Bχ))

theorem stepBound_le (hD : 2 ≤ S.gfac) (β Bχ BC E : ℕ) :
    stepBound S β Bχ BC E ≤ gammaB S * E + deltaB S β Bχ BC := by
  have h := autBound_iterate_le hD β Bχ (S.gfac * E + 2 * S.τ * S.gfac * β + BC) S.b
  unfold stepBound gammaB deltaB
  calc S.E.W * (S.gfac * (autBound S β Bχ)^[S.b] (S.gfac * E + 2 * S.τ * S.gfac * β + BC))
      ≤ S.E.W * (S.gfac * (S.gfac ^ S.b * (S.gfac * E + 2 * S.τ * S.gfac * β + BC +
          2 * (2 * S.τ * β + 2 * Bχ)))) := by gcongr; omega
    _ = S.E.W * S.gfac ^ (S.b + 2) * E + S.E.W * S.gfac ^ (S.b + 1) *
          (2 * S.τ * S.gfac * β + BC + 2 * (2 * S.τ * β + 2 * Bχ)) := by ring

/-- **Lemma 9, closed form**: `step^[T] B₀ ≤ γ^T (B₀ + Δ)`, for `D ≥ 2`. -/
theorem stepBound_iterate_le (hD : 2 ≤ S.gfac) (hW : 1 ≤ S.E.W) (β Bχ BC B0 : ℕ) (T : ℕ) :
    (stepBound S β Bχ BC)^[T] B0 ≤ gammaB S ^ T * (B0 + deltaB S β Bχ BC) := by
  have hγ : 2 ≤ gammaB S := by
    unfold gammaB
    calc 2 ≤ S.gfac := hD
      _ ≤ S.gfac ^ (S.b + 2) := Nat.le_self_pow (by omega) _
      _ ≤ S.E.W * S.gfac ^ (S.b + 2) := Nat.le_mul_of_pos_left _ hW
  suffices h : ∀ T, (stepBound S β Bχ BC)^[T] B0 + deltaB S β Bχ BC ≤
      gammaB S ^ T * (B0 + deltaB S β Bχ BC) by
    exact le_trans (Nat.le_add_right _ _) (h T)
  intro T
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    have h1 := stepBound_le hD β Bχ BC ((stepBound S β Bχ BC)^[T] B0)
    calc stepBound S β Bχ BC ((stepBound S β Bχ BC)^[T] B0) + deltaB S β Bχ BC
        ≤ gammaB S * ((stepBound S β Bχ BC)^[T] B0 + deltaB S β Bχ BC) := by nlinarith
      _ ≤ gammaB S * (gammaB S ^ T * (B0 + deltaB S β Bχ BC)) := Nat.mul_le_mul_left _ ih
      _ = _ := by ring

end AdvancedEncryption.ExpLUT
