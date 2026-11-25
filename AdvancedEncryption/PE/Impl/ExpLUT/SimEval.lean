import PE.Impl.ExpLUT.SimForm
import PE.Impl.ExpLUT.Correctness

/-!
# Corollary 1: the simulation form of `A_F`

Lemma 10 along the evaluation of a branching program (ePrint 2026/2539, Appendix A, Corollary 1),
with the simulation matrices as explicit functions of the inputs' ones:

* the rounds of the tables (`simRounds`, `simForm_rounds`), the tables (`simLut`, `simForm_lut`,
  `simForm_lut_of_spec`) and the evaluation (`simEvalAt`, `simEval`, `simForm_eval`): if the fresh
  data are in simulation form (`SimEvalOK`), then `δ₁ᵀ ⊗ A_F⁽¹⁾ − F(x) δ₁ᵀ ⊗ G⁽¹⁾ = L R̂_F`;
* for the scheme (`Programmed`: the first rows of `a_t`, `A₀`, `A^in_{t,d}`, `A^aut_{t,d}` are
  `σ_i(Ā) Z + μ G⁽¹⁾` for programming matrices on the `Ā` columns, with the digits of the gadget
  ciphertexts `C^in_t` and `C_{g_t}` of the ciphertext), the fresh data are in simulation form
  (`simEvalOK_of_programmed`: helpers by `J_{η_{1,k}}`, `C_{g_t}` by `J_{η_{g_t, g_t^{-1}}}`,
  programmed ones by `J_{β_i} Z`), hence **Corollary 1** (`corollary1`):
  `δ₁ᵀ ⊗ A_F⁽¹⁾ = L R̂_F + F(x*) δ₁ᵀ ⊗ G⁽¹⁾` with `R̂_F = simKey`.
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix

variable {R : Type*} [CommRing R] {S : Setting R} {Wb J Pos : Type*} [Fintype Wb] [Fintype J]
  (M : HelperMap S J) (Ab : Wb → R) (H1 : J → Col S.τ → R)

/-- The row of `g_t = g^{2^t}`. -/
abbrev Setting.rowT (S : Setting R) (t : ℕ) : Fin S.E.W := S.rot (2 ^ t) S.row0

theorem rowT_val {t : ℕ} (ht : t < S.b) : (S.rowT t : ℕ) = 2 ^ t := by
  rw [rot_val]
  simp only [Setting.row0, zero_add]
  exact Nat.mod_eq_of_lt (by rw [S.W_eq]; exact Nat.pow_lt_pow_right (by norm_num) ht)

/-- The simulation matrices of the helper data of the rounds: of `H_{g_t}`, of `C_{g_t}` and of its
digit encodings. -/
structure SimAut (Wb J : Type*) (S : Setting R) where
  /-- Of `H_{g_t}`. -/
  Rhf : ℕ → SimMat Wb J S
  /-- Of `C_{g_t}`. -/
  RC : ℕ → SimMat Wb J S
  /-- Of the digit encodings of `C_{g_t}`. -/
  Raut : ℕ → Dig S.τ → SimMat Wb J S

/-- The helper data of round `t` are in simulation form: `H_{g_t}` at `(1, g_t)`, `C_{g_t}` at
`(g_t, 1)`, its digit encodings at `(g_t, g_t)`. -/
def SimHelperOK (P : AutPub S) (h : AutData S) (Q : SimAut Wb J S) (t : ℕ) : Prop :=
  SimForm M Ab H1 S.row0 (S.rowT t) (P.Hf t) 1 (Q.Rhf t) ∧
    SimForm M Ab H1 (S.rowT t) S.row0 (gcAut S (S.kf t) (P.Hi t) (h.hi t)) 1 (Q.RC t) ∧
    ∀ d, SimForm M Ab H1 (S.rowT t) (S.rowT t) (P.Aaut t d)
      (digits S (gcAut S (S.kf t) (P.Hi t) (h.hi t)) d) (Q.Raut t d)

/-! ### Rounds and tables -/

/-- The simulation matrices after `t` rounds. -/
def simRounds (P : AutPub S) (A : Matrix (Fin 2) (Col S.τ) R) (h : AutData S) (Q : SimAut Wb J S)
    (μ : R) (Rc : SimMat Wb J S) : ℕ → ℕ → SimMat Wb J S
  | 0, _ => Rc
  | t + 1, j =>
    if j < 2 ^ t then simRounds P A h Q μ Rc t j
    else simAut (2 ^ t) (P.Hi t) (P.Aaut t) (roundsPK P A t (j - 2 ^ t)) (h.hi t)
      (S.E.σ (S.idx (j - 2 ^ t)) μ) (Q.Rhf t) (Q.RC t) (Q.Raut t) (simRounds P A h Q μ Rc t (j - 2 ^ t))

/-- **The rounds** (Lemma 10 along Lemma 8's rounds): after `t ≤ b` rounds, `c_j` is in simulation
form at `(1, 1)` with respect to `simRounds t j`. -/
theorem simForm_rounds (P : AutPub S) {A : Matrix (Fin 2) (Col S.τ) R} (h : AutData S)
    (Q : SimAut Wb J S) {μ : R} {Rc : SimMat Wb J S} (hc : SimForm M Ab H1 S.row0 S.row0 A μ Rc)
    (hH : ∀ t < S.b, SimHelperOK M Ab H1 P h Q t) :
    ∀ t ≤ S.b, ∀ j < 2 ^ t, SimForm M Ab H1 S.row0 S.row0 (roundsPK P A t j)
      (S.E.σ (S.idx j) μ) (simRounds P A h Q μ Rc t j) := by
  intro t
  induction t with
  | zero =>
    intro _ j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simpa [roundsPK, simRounds, S.idx_zero] using hc
  | succ t ih =>
    intro ht j hj
    simp only [roundsPK, simRounds]
    split_ifs with hjt
    · exact ih (by omega) j hjt
    · have hj' : j - 2 ^ t < 2 ^ t := by rw [pow_succ] at hj; omega
      obtain ⟨h1, h2, h3⟩ := hH t (by omega)
      have := simForm_aut M Ab H1 (2 ^ t) (ih (by omega) (j - 2 ^ t) hj') h1 h2 h3
      have hμ : S.E.σ (S.idx (2 ^ t)) (S.E.σ (S.idx (j - 2 ^ t)) μ) = S.E.σ (S.idx j) μ := by
        have hW : 2 ^ (t + 1) ≤ S.E.W := by
          rw [S.W_eq]; exact Nat.pow_le_pow_right (by norm_num) ht
        rw [S.idx_add, show 2 ^ t + (j - 2 ^ t) = j by omega, Nat.mod_eq_of_lt (by omega)]
      rwa [hμ] at this

/-- The simulation matrix of a table: `Σ_{j<W} R̂_j G⁻¹(α_j G)`. -/
def simLut (P : AutPub S) (coef : ℕ → R) (A : Matrix (Fin 2) (Col S.τ) R) (h : AutData S)
    (Q : SimAut Wb J S) (μ : R) (Rc : SimMat Wb J S) : SimMat Wb J S :=
  ∑ j ∈ Finset.range S.E.W, simRounds P A h Q μ Rc S.b j * S.ginv (coef j • S.G)

/-- **The table**: `LUT(c)` is in simulation form with respect to `simLut`. -/
theorem simForm_lut (P : AutPub S) (coef : ℕ → R) {A : Matrix (Fin 2) (Col S.τ) R} (h : AutData S)
    (Q : SimAut Wb J S) {μ : R} {Rc : SimMat Wb J S} (hc : SimForm M Ab H1 S.row0 S.row0 A μ Rc)
    (hH : ∀ t < S.b, SimHelperOK M Ab H1 P h Q t) :
    SimForm M Ab H1 S.row0 S.row0 (lutPK P coef A)
      (∑ j ∈ Finset.range S.E.W, coef j * S.E.σ (S.idx j) μ) (simLut P coef A h Q μ Rc) := by
  have hr := simForm_rounds M Ab H1 P h Q hc hH S.b le_rfl
  refine simForm_sum M Ab H1 _ fun j hj => ?_
  exact simForm_smul M Ab H1 _ (hr j (by rw [← S.W_eq]; exact Finset.mem_range.mp hj))

theorem simForm_lut_of_spec (P : AutPub S) {coef : ℕ → R} {out : ℕ → R} (hspec : LUTSpec S coef out)
    {A : Matrix (Fin 2) (Col S.τ) R} (h : AutData S) (Q : SimAut Wb J S) {u : ℕ} (hu : u < S.E.W)
    {Rc : SimMat Wb J S} (hc : SimForm M Ab H1 S.row0 S.row0 A (S.E.X ^ u) Rc)
    (hH : ∀ t < S.b, SimHelperOK M Ab H1 P h Q t) :
    SimForm M Ab H1 S.row0 S.row0 (lutPK P coef A) (out u) (simLut P coef A h Q (S.E.X ^ u) Rc) := by
  have := simForm_lut M Ab H1 P coef h Q hc hH
  rwa [hspec u hu] at this

/-! ### The evaluation -/

/-- The simulation matrices of the fresh data of the evaluation: of `c₀`, of `C^in_t`, of the
digit encodings of `C^in_t`, and of the helper data. -/
structure SimFresh (Wb J Pos : Type*) (S : Setting R) where
  /-- Of `c₀`. -/
  R0 : SimMat Wb J S
  /-- Of `C^in_t`. -/
  Zin : Pos → SimMat Wb J S
  /-- Of the digit encodings of `C^in_t`. -/
  Rin : Pos → Dig S.τ → SimMat Wb J S
  /-- Of the helper data. -/
  aut : SimAut Wb J S

/-- The fresh data of the evaluation are in simulation form, for the attribute `x` of width `w`. -/
structure SimEvalOK (w : ℕ) (pp : EvalPub S Pos) (ct : EvalCTData S Pos) (x : Pos → ℕ)
    (Q : SimFresh Wb J Pos S) : Prop where
  c0 : SimForm M Ab H1 S.row0 S.row0 pp.A0 1 Q.R0
  Cin : ∀ t, SimForm M Ab H1 S.row0 S.row0 (ct.Cin t) (S.E.X ^ (w * x t)) (Q.Zin t)
  cin : ∀ t d, SimForm M Ab H1 S.row0 S.row0 (pp.Ain t d) (digits S (ct.Cin t) d) (Q.Rin t d)
  aut : ∀ t < S.b, SimHelperOK M Ab H1 pp.aut ct.aut Q.aut t

/-- The simulation matrices of the evaluation after `i` steps. -/
def simEvalAt (F : BP Pos) (pp : EvalPub S Pos) (ct : EvalCTData S Pos) (x : Pos → ℕ)
    (Q : SimFresh Wb J Pos S) : ℕ → SimMat Wb J S
  | 0 => Q.R0
  | i + 1 => simLut pp.aut (F.coefs S i) (mulPK S (evalPKAt F pp i) (pp.Ain (F.read i))) ct.aut Q.aut
      (S.E.X ^ (F.state x i + F.w * x (F.read i)))
      (simMul (evalPKAt F pp i) (ct.Cin (F.read i)) (S.E.X ^ F.state x i) (simEvalAt F pp ct x Q i)
        (Q.Zin (F.read i)) (Q.Rin (F.read i)))

/-- **`R̂_F`**: the simulation matrix of `A_F`. -/
def simEval (F : BP Pos) (pp : EvalPub S Pos) (ct : EvalCTData S Pos) (x : Pos → ℕ)
    (Q : SimFresh Wb J Pos S) : SimMat Wb J S :=
  simEvalAt F pp ct x Q F.T

theorem simForm_evalMul (F : BP Pos) (pp : EvalPub S Pos) (ct : EvalCTData S Pos) {x : Pos → ℕ}
    {Q : SimFresh Wb J Pos S} (hok : SimEvalOK M Ab H1 F.w pp ct x Q) (i : ℕ)
    (hi : SimForm M Ab H1 S.row0 S.row0 (evalPKAt F pp i) (S.E.X ^ F.state x i)
      (simEvalAt F pp ct x Q i)) :
    SimForm M Ab H1 S.row0 S.row0 (mulPK S (evalPKAt F pp i) (pp.Ain (F.read i)))
      (S.E.X ^ (F.state x i + F.w * x (F.read i)))
      (simMul (evalPKAt F pp i) (ct.Cin (F.read i)) (S.E.X ^ F.state x i) (simEvalAt F pp ct x Q i)
        (Q.Zin (F.read i)) (Q.Rin (F.read i))) := by
  have := simForm_mul M Ab H1 hi (hok.Cin (F.read i)) (hok.cin (F.read i))
  rwa [← pow_add] at this

theorem simForm_evalAt (h8 : Lemma8 S) (F : BP Pos) (hF : F.WF S.E.W) (pp : EvalPub S Pos)
    (ct : EvalCTData S Pos) {x : Pos → ℕ} (hx : ∀ t, x t < F.nsym) {Q : SimFresh Wb J Pos S}
    (hok : SimEvalOK M Ab H1 F.w pp ct x Q) :
    ∀ i < F.T, SimForm M Ab H1 S.row0 S.row0 (evalPKAt F pp i) (S.E.X ^ F.state x i)
      (simEvalAt F pp ct x Q i) := by
  intro i
  induction i with
  | zero => intro _; simpa [evalPKAt, simEvalAt, BP.state] using hok.c0
  | succ i ih =>
    intro hi
    have hz := F.state_lt hF x hx i (by omega)
    have hm := simForm_evalMul M Ab H1 F pp ct hok i (ih (by omega))
    have hl := simForm_lut_of_spec M Ab H1 pp.aut (h8 (F.table i)).1 ct.aut Q.aut
      (F.add_lt_W hF _ _ hz (hx _)) hm hok.aut
    rw [F.table_add hF _ _ _ hz] at hl
    simp only [evalPKAt, simEvalAt, BP.coefs, hi, ite_true, BP.state]
    exact hl

/-- **Corollary 1, abstractly**: `A_F = EvalPK(F, pp)` is in simulation form at `(1, 1)` with payload
`F(x)` with respect to `R̂_F = simEval`. -/
theorem simForm_eval (h8 : Lemma8 S) (F : BP Pos) (hF : F.WF S.E.W) (pp : EvalPub S Pos)
    (ct : EvalCTData S Pos) {x : Pos → ℕ} (hx : ∀ t, x t < F.nsym) {Q : SimFresh Wb J Pos S}
    (hok : SimEvalOK M Ab H1 F.w pp ct x Q) :
    SimForm M Ab H1 S.row0 S.row0 (evalPK F pp) (F.eval x : R) (simEval F pp ct x Q) := by
  obtain ⟨i, hi⟩ : ∃ i, F.T = i + 1 := ⟨F.T - 1, by have := hF.T_pos; omega⟩
  have hz := F.state_lt hF x hx i (by omega)
  have hm := simForm_evalMul M Ab H1 F pp ct hok i
    (simForm_evalAt M Ab H1 h8 F hF pp ct hx hok i (by omega))
  have hl := simForm_lut_of_spec M Ab H1 pp.aut (h8 (F.table i)).2 ct.aut Q.aut
    (F.add_lt_W hF _ _ hz (hx _)) hm hok.aut
  rw [F.table_add hF _ _ _ hz] at hl
  simp only [simEval, evalPK, BP.eval, hi, evalPKAt, simEvalAt, BP.coefs, BP.state, lt_irrefl,
    ite_false]
  exact hl

/-! ### The scheme: programmed public keys -/

/-- `Ā`: the first row of `B` on its `Ā` columns. -/
def abarOf {Pos : Type*} (mpk : MPK S Wb J Pos) : Wb → R := fun w => mpk.B 0 (.inl w)

/-- The first rows of the `H_k`. -/
def h1Of {Pos : Type*} (mpk : MPK S Wb J Pos) : J → Col S.τ → R := fun k => mpk.H k 0

/-- The programming matrices (on the `Ā` columns): `Z_t`, `R₀`, `R^in_{t,d}`, `R^aut_{t,d}`. -/
structure Prog (S : Setting R) (Wb J Pos : Type*) where
  /-- `Z_t` of `a_t = Ā Z_t + X^{w x_t} G⁽¹⁾`. -/
  Z : Pos → Matrix Wb (Col S.τ) R
  /-- `R₀` of `A₀ = B R₀ + G`. -/
  R0 : Matrix Wb (Col S.τ) R
  /-- `R^in_{t,d}` of `A^in_{t,d} = B R + d G`. -/
  Rin : Pos → Dig S.τ → Matrix Wb (Col S.τ) R
  /-- `R^aut_{t,d}` of `A^aut_{t,d} = σ_{g_t}(B) R + d G`. -/
  Raut : Fin S.b → Dig S.τ → Matrix Wb (Col S.τ) R

/-- **A programmed public key** (hybrid H1), on the first rows: `a_t = Ā Z_t + X^{w x_t} G⁽¹⁾`,
`A₀⁽¹⁾ = Ā R₀ + G⁽¹⁾`, `A^in_{t,d}⁽¹⁾ = Ā R + d G⁽¹⁾` with the digits `d` of `C^in_t`, and
`A^aut_{t,d}⁽¹⁾ = σ_{g_t}(Ā) R + d G⁽¹⁾` with the digits of `C_{g_t}` of the ciphertext `ct`. -/
structure Programmed (w : ℕ) (mpk : MPK S Wb J Pos) (ct : Ciphertext S Wb J Pos) (x : Pos → ℕ)
    (P : Prog S Wb J Pos) : Prop where
  a : ∀ t, mpk.a t = abarOf mpk ᵥ* P.Z t + S.E.X ^ (w * x t) • S.G 0
  A0 : mpk.A0 0 = abarOf mpk ᵥ* P.R0 + S.G 0
  Ain : ∀ t d, mpk.Ain t d 0 =
    abarOf mpk ᵥ* P.Rin t d + digits S (cinMat (mpk.a t) (ct.cinBot t)) d • S.G 0
  Aaut : ∀ t d, mpk.Aaut t d 0 =
    (S.E.σ (S.kf t) ∘ abarOf mpk) ᵥ* P.Raut t d + digits S (autGC M mpk.H ct.h t) d • S.G 0

variable [DecidableEq J]

/-- The simulation matrices of the fresh data of a programmed public key. -/
def simFreshOf (P : Prog S Wb J Pos) : SimFresh Wb J Pos S where
  R0 := jβ S.row0 P.R0
  Zin t := jβ S.row0 (P.Z t)
  Rin t d := jβ S.row0 (P.Rin t d)
  aut :=
    { Rhf := finExt fun t => jη S.row0 (M.fwd t)
      RC := finExt fun t => jη (S.rowT t) (M.inv t)
      Raut := finExt fun t d => jβ (S.rowT t) (P.Raut t d) }

/-- **`R̂_F`** of the scheme: the simulation matrix of `A_F = EvalPK(F, mpk)`. -/
def simKey (mpk : MPK S Wb J Pos) (F : BP Pos) (ct : Ciphertext S Wb J Pos) (x : Pos → ℕ)
    (P : Prog S Wb J Pos) : SimMat Wb J S :=
  simEval F (evalPub M mpk) (evalData M mpk ct) x (simFreshOf M P)

omit [Fintype Wb] [Fintype J] [DecidableEq J] in
theorem σ_row0_comp (a : Wb → R) : (S.E.σ (S.idx (S.row0 : ℕ)) ∘ a) = a :=
  funext fun _ => S.idx_zero _

omit [Fintype Wb] [Fintype J] [DecidableEq J] in
theorem σ_row0_comp' (a : Col S.τ → R) : (S.E.σ (S.idx (S.row0 : ℕ)) ∘ a) = a :=
  funext fun _ => S.idx_zero _

omit [Fintype Wb] [Fintype J] [DecidableEq J] in
theorem mulRow_row0_fwd {t : ℕ} (ht : t < S.b) : M.mulRow S.row0 (M.fwd ⟨t, ht⟩) = S.rowT t := by
  rw [mulRow_eq, M.je_fwd]

omit [Fintype Wb] [Fintype J] [DecidableEq J] in
theorem mulRow_rowT_inv {t : ℕ} (ht : t < S.b) : M.mulRow (S.rowT t) (M.inv ⟨t, ht⟩) = S.row0 := by
  have hW : 2 ^ t < S.E.W := by rw [S.W_eq]; exact Nat.pow_lt_pow_right (by norm_num) ht
  ext
  rw [mulRow_eq, rot_val, rowT_val ht, M.je_inv]
  simp only [Setting.row0]
  rw [show 2 ^ t + (S.E.W - 2 ^ t) = S.E.W by omega, Nat.mod_self]

/-- **The fresh data of a programmed public key are in simulation form.** -/
theorem simEvalOK_of_programmed {w : ℕ} {mpk : MPK S Wb J Pos} {ct : Ciphertext S Wb J Pos}
    {x : Pos → ℕ} {P : Prog S Wb J Pos} (hP : Programmed M w mpk ct x P) :
    SimEvalOK M (abarOf mpk) (h1Of mpk) w (evalPub M mpk) (evalData M mpk ct) x (simFreshOf M P) where
  c0 := simForm_jβ M _ _ (by rw [σ_row0_comp, one_smul]; exact hP.A0)
  Cin t := simForm_jβ M _ _ (by rw [σ_row0_comp]; exact hP.a t)
  cin t d := simForm_jβ M _ _ (by rw [σ_row0_comp]; exact hP.Ain t d)
  aut t ht := by
    have hidx : S.idx (S.rowT t : ℕ) = S.kf t := by rw [rowT_val ht]
    refine ⟨?_, ?_, fun d => ?_⟩
    · simp only [simFreshOf, evalPub, finExt_of_lt _ ht]
      rw [← mulRow_row0_fwd M ht]
      exact simForm_jη M _ _ (by rw [σ_row0_comp']; rfl)
    · simp only [simFreshOf, evalPub, evalData, finExt_of_lt _ ht]
      have := simForm_jη M (abarOf mpk) (h1Of mpk) (i := S.rowT t) (k := M.inv ⟨t, ht⟩)
        (A := gcAut S (S.kf t) (mpk.H (M.inv ⟨t, ht⟩)) (ct.h (M.inv ⟨t, ht⟩))) (by
          funext j
          simp [gcAut, hidx, h1Of])
      rwa [mulRow_rowT_inv M ht] at this
    · simp only [simFreshOf, evalPub, evalData, finExt_of_lt _ ht]
      refine simForm_jβ M _ _ ?_
      rw [hidx]
      exact hP.Aaut ⟨t, ht⟩ d

/-- **Corollary 1**: for a programmed public key and the attribute `x` of the programming,
`δ₁ᵀ ⊗ A_F⁽¹⁾ − F(x) δ₁ᵀ ⊗ G⁽¹⁾ = L R̂_F` with `R̂_F = simKey`. -/
theorem corollary1 (h8 : Lemma8 S) (F : BP Pos) (hF : F.WF S.E.W) {mpk : MPK S Wb J Pos}
    {ct : Ciphertext S Wb J Pos} {x : Pos → ℕ} (hx : ∀ t, x t < F.nsym) {P : Prog S Wb J Pos}
    (hP : Programmed M F.w mpk ct x P) :
    SimForm M (abarOf mpk) (h1Of mpk) S.row0 S.row0 (keyPK M mpk F) (F.eval x : R)
      (simKey M mpk F ct x P) :=
  simForm_eval _ _ _ h8 F hF _ _ hx (simEvalOK_of_programmed M hP)

end AdvancedEncryption.ExpLUT
