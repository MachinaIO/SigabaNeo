import PE.Impl.ExpLUT.LUT

/-!
# Branching programs over encodings (§4.4, Lemma 9, exact form)

A branching program (Definition 2, `BP`) of length `T`, width `w` over the alphabet `[0, nsym)`
with read map `read` and tables `step i z x = f_i(z, x)`; on an attribute `x : Pos → ℕ` it computes
`z₀ = 0`, `z_{i+1} = f_i(z_i, x_{read i})` (`BP.state`) and `F(x) = z_T` (`BP.eval`). Its lookup
tables are `L_i(z + w x) = f_i(z, x)` (`BP.table`), with the coefficients `α_{·,L_i}` for `i < T − 1`
and `v_{·,L_{T−1}}` for the last step (`BP.coefs`).

The evaluation (`evalPK`, `evalCT`, with the error `evalErr`) starts from `c₀ : ⟦s⟧^{A₀}_s` and, at
step `i`, multiplies by the gadget ciphertext `C^in_{read i} : GC_s(X^{w x} s)` (`Mul`) and applies
the table `L_i` (`LUT`). Public data (`EvalPub`): `A₀`, the digit matrices `A^in_{t,·}` and the
helper data `AutPub`; ciphertext data (`EvalCTData`): `c₀`, `C^in_t`, the digit encodings `c^in_{t,·}`
and the helper data `AutData`.

**Lemma 9, exactly** (`encodes_eval`): `c_F := EvalCT(F, pp, ct) : ⟦F(x) s⟧^{A_F}_s` with
`A_F = EvalPK(F, pp)`, which depends on `F` and `pp` only, and the error `evalErr`, an explicit
function of the input errors. The noise bound is `PE.Impl.ExpLUT.Noise`.
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix

/-- A branching program (Definition 2): length `T`, width `w`, alphabet `[0, nsym)`, read map, and
tables `step i z x = f_i(z, x)` (the last one, `i = T − 1`, has values in `{0, 1}`). -/
structure BP (Pos : Type*) where
  /-- The length. -/
  T : ℕ
  /-- The width. -/
  w : ℕ
  /-- The alphabet size `|Σ|`. -/
  nsym : ℕ
  /-- The read map `ι`. -/
  read : ℕ → Pos
  /-- The tables `f_i(z, x)`. -/
  step : ℕ → ℕ → ℕ → ℕ

namespace BP

variable {Pos : Type*} (F : BP Pos)

/-- The states `z₀ = 0`, `z_{i+1} = f_i(z_i, x_{ι(i)})`. -/
def state (F : BP Pos) (x : Pos → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => F.step i (state F x i) (x (F.read i))

/-- The output `F(x) = z_T`. -/
def eval (x : Pos → ℕ) : ℕ := F.state x F.T

/-- The lookup table of step `i`: `L_i(z + w x) = f_i(z, x)`. -/
def table (i : ℕ) (u : ℕ) : ℕ := F.step i (u % F.w) (u / F.w)

/-- Well-formed for the lookup width `W`: `T ≥ 1`, `w ≥ 1`, `w |Σ| ≤ W`, and the transition tables
map `[0, w) × Σ` into `[0, w)`. -/
structure WF (W : ℕ) : Prop where
  T_pos : 0 < F.T
  w_pos : 0 < F.w
  le_W : F.w * F.nsym ≤ W
  step_lt : ∀ i z a, i + 1 < F.T → z < F.w → a < F.nsym → F.step i z a < F.w

theorem state_lt {W : ℕ} (hF : F.WF W) (x : Pos → ℕ) (hx : ∀ t, x t < F.nsym) :
    ∀ i < F.T, F.state x i < F.w := by
  intro i
  induction i with
  | zero => intro _; exact hF.w_pos
  | succ i ih => intro hi; exact hF.step_lt i _ _ hi (ih (by omega)) (hx _)

theorem table_add {W : ℕ} (hF : F.WF W) (i z a : ℕ) (hz : z < F.w) :
    F.table i (z + F.w * a) = F.step i z a := by
  have hw := hF.w_pos
  unfold table
  congr 1
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hz]
  · rw [Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt hz, zero_add]

theorem add_lt_W {W : ℕ} (hF : F.WF W) (z a : ℕ) (hz : z < F.w) (ha : a < F.nsym) :
    z + F.w * a < W :=
  calc z + F.w * a < F.w + F.w * a := by omega
    _ = F.w * (a + 1) := by ring
    _ ≤ F.w * F.nsym := Nat.mul_le_mul_left _ ha
    _ ≤ W := hF.le_W

end BP

variable {R : Type*} [CommRing R] {S : Setting R} {Pos : Type*}

variable (S) in
/-- The coefficients of step `i`: `α_{·,L_i}` for `i < T − 1`, `v_{·,L_{T−1}}` for the last step. -/
def BP.coefs (F : BP Pos) (i : ℕ) : ℕ → R :=
  if i + 1 < F.T then alphaCoef (S := S) (F.table i) else vCoef (S := S) (F.table i)

variable (S Pos) in
/-- The public data of the evaluation: `A₀`, the digit matrices `A^in_{t,·}`, the helper data. -/
structure EvalPub where
  /-- `A₀`. -/
  A0 : Matrix (Fin 2) (Col S.τ) R
  /-- `A^in_{t, (r, j, i)}`. -/
  Ain : Pos → Dig S.τ → Matrix (Fin 2) (Col S.τ) R
  /-- The helper data. -/
  aut : AutPub S

variable (S Pos) in
/-- The ciphertext data of the evaluation: `c₀`, the gadget ciphertexts `C^in_t`, their digit
encodings, the helper data. -/
structure EvalCTData where
  /-- `c₀`. -/
  c0 : Col S.τ → R
  /-- `C^in_t`. -/
  Cin : Pos → Matrix (Fin 2) (Col S.τ) R
  /-- `c^in_{t, (r, j, i)}`. -/
  cin : Pos → Dig S.τ → Col S.τ → R
  /-- The helper data. -/
  aut : AutData S

variable (S Pos) in
/-- The errors of the ciphertext data: of `c₀`, of the gadget ciphertexts `C^in_t`, of their digit
encodings, and of the helper data. -/
structure EvalErrs where
  /-- The error of `c₀`. -/
  e0 : Col S.τ → R
  /-- The errors `s C^in_t − X^{w x_t} s G`. -/
  fin : Pos → Col S.τ → R
  /-- The errors of the digit encodings. -/
  ein : Pos → Dig S.τ → Col S.τ → R
  /-- The errors of the helper data. -/
  aut : AutData S

/-- `EvalPK` after `i` steps. -/
def evalPKAt (F : BP Pos) (pp : EvalPub S Pos) : ℕ → Matrix (Fin 2) (Col S.τ) R
  | 0 => pp.A0
  | i + 1 => lutPK pp.aut (F.coefs S i) (mulPK S (evalPKAt F pp i) (pp.Ain (F.read i)))

/-- `EvalCT` after `i` steps. -/
def evalCTAt (F : BP Pos) (pp : EvalPub S Pos) (ct : EvalCTData S Pos) : ℕ → Col S.τ → R
  | 0 => ct.c0
  | i + 1 => lutCT pp.aut (F.coefs S i) (mulPK S (evalPKAt F pp i) (pp.Ain (F.read i))) ct.aut
      (mulCT S (evalPKAt F pp i) (ct.Cin (F.read i)) (ct.cin (F.read i)) (evalCTAt F pp ct i))

/-- The error after `i` steps, for the attribute `x`. -/
def evalErrAt (F : BP Pos) (pp : EvalPub S Pos) (ct : EvalCTData S Pos) (x : Pos → ℕ)
    (er : EvalErrs S Pos) : ℕ → Col S.τ → R
  | 0 => er.e0
  | i + 1 => lutErr pp.aut (F.coefs S i) (mulPK S (evalPKAt F pp i) (pp.Ain (F.read i))) ct.aut
      (S.E.X ^ (F.state x i + F.w * x (F.read i))) er.aut
      (mulErr S (evalPKAt F pp i) (ct.Cin (F.read i)) (S.E.X ^ F.state x i) (er.fin (F.read i))
        (er.ein (F.read i)) (evalErrAt F pp ct x er i))

/-- **`EvalPK(F, pp)`** = `A_F`. -/
def evalPK (F : BP Pos) (pp : EvalPub S Pos) : Matrix (Fin 2) (Col S.τ) R := evalPKAt F pp F.T

/-- **`EvalCT(F, pp, ct)`** = `c_F`. -/
def evalCT (F : BP Pos) (pp : EvalPub S Pos) (ct : EvalCTData S Pos) : Col S.τ → R :=
  evalCTAt F pp ct F.T

/-- The error `e_F` of `c_F`. -/
def evalErr (F : BP Pos) (pp : EvalPub S Pos) (ct : EvalCTData S Pos) (x : Pos → ℕ)
    (er : EvalErrs S Pos) : Col S.τ → R :=
  evalErrAt F pp ct x er F.T

/-- The ciphertext data are exact for the secret `s = (s̄, 1)` and the attribute `x`, with the
errors `er`: `c₀ : ⟦s⟧^{A₀}_s`, `C^in_t : GC_s(X^{w x_t} s)`, the digit encodings of `C^in_t`, and
the helper data. -/
structure EvalOK (F : BP Pos) (pp : EvalPub S Pos) (ct : EvalCTData S Pos) (sb : R) (x : Pos → ℕ)
    (er : EvalErrs S Pos) : Prop where
  c0 : Encodes S (sec sb) pp.A0 (sec sb) er.e0 ct.c0
  Cin : ∀ t, IsGC S (sec sb) (ct.Cin t) (S.E.X ^ (F.w * x t) • sec sb) (er.fin t)
  cin : ∀ t d, Encodes S (sec sb) (pp.Ain t d) (digits S (ct.Cin t) d • sec sb) (er.ein t d) (ct.cin t d)
  aut : ∀ t < S.b, HelperOK pp.aut ct.aut er.aut sb t

/-- One step of the evaluation, before the table: `Mul` by `C^in_{ι(i)}`. -/
theorem encodes_evalMul (F : BP Pos) (pp : EvalPub S Pos) (ct : EvalCTData S Pos) {sb : R}
    {x : Pos → ℕ} {er : EvalErrs S Pos} (hok : EvalOK F pp ct sb x er) (i : ℕ)
    (hi : Encodes S (sec sb) (evalPKAt F pp i) (S.E.X ^ F.state x i • sec sb) (evalErrAt F pp ct x er i)
      (evalCTAt F pp ct i)) :
    Encodes S (sec sb) (mulPK S (evalPKAt F pp i) (pp.Ain (F.read i)))
      (S.E.X ^ (F.state x i + F.w * x (F.read i)) • sec sb)
      (mulErr S (evalPKAt F pp i) (ct.Cin (F.read i)) (S.E.X ^ F.state x i) (er.fin (F.read i))
        (er.ein (F.read i)) (evalErrAt F pp ct x er i))
      (mulCT S (evalPKAt F pp i) (ct.Cin (F.read i)) (ct.cin (F.read i)) (evalCTAt F pp ct i)) := by
  have := encodes_mul hi (hok.Cin (F.read i)) (hok.cin (F.read i))
  rwa [smul_smul, ← pow_add] at this

/-- **The states**: before step `i < T`, `c_i : ⟦X^{z_i} s⟧^{A_i}_s`, exactly. -/
theorem encodes_evalAt (h8 : Lemma8 S) (F : BP Pos) (hF : F.WF S.E.W) (pp : EvalPub S Pos)
    (ct : EvalCTData S Pos) {sb : R} {x : Pos → ℕ} (hx : ∀ t, x t < F.nsym) {er : EvalErrs S Pos}
    (hok : EvalOK F pp ct sb x er) :
    ∀ i < F.T, Encodes S (sec sb) (evalPKAt F pp i) (S.E.X ^ F.state x i • sec sb)
      (evalErrAt F pp ct x er i) (evalCTAt F pp ct i) := by
  intro i
  induction i with
  | zero => intro _; simpa [evalPKAt, evalCTAt, evalErrAt, BP.state] using hok.c0
  | succ i ih =>
    intro hi
    have hz := F.state_lt hF x hx i (by omega)
    have hm := encodes_evalMul F pp ct hok i (ih (by omega))
    have hspec := (h8 (F.table i)).1
    have hl := encodes_lut_of_spec pp.aut hspec ct.aut er.aut
      (F.add_lt_W hF _ _ hz (hx _)) hm hok.aut
    rw [F.table_add hF _ _ _ hz] at hl
    simp only [evalPKAt, evalCTAt, evalErrAt, BP.coefs, if_pos hi, BP.state]
    exact hl

/-- **Lemma 9, exactly**: `c_F = EvalCT(F, pp, ct) : ⟦F(x) s⟧^{A_F}_s` with `A_F = EvalPK(F, pp)`
and the error `e_F = evalErr F pp ct x er`. -/
theorem encodes_eval (h8 : Lemma8 S) (F : BP Pos) (hF : F.WF S.E.W) (pp : EvalPub S Pos)
    (ct : EvalCTData S Pos) {sb : R} {x : Pos → ℕ} (hx : ∀ t, x t < F.nsym) {er : EvalErrs S Pos}
    (hok : EvalOK F pp ct sb x er) :
    Encodes S (sec sb) (evalPK F pp) ((F.eval x : R) • sec sb) (evalErr F pp ct x er)
      (evalCT F pp ct) := by
  obtain ⟨i, hi⟩ : ∃ i, F.T = i + 1 := ⟨F.T - 1, by have := hF.T_pos; omega⟩
  have hz := F.state_lt hF x hx i (by omega)
  have hm := encodes_evalMul F pp ct hok i (encodes_evalAt h8 F hF pp ct hx hok i (by omega))
  have hspec := (h8 (F.table i)).2
  have hl := encodes_lut_of_spec pp.aut hspec ct.aut er.aut (F.add_lt_W hF _ _ hz (hx _)) hm hok.aut
  rw [F.table_add hF _ _ _ hz] at hl
  simp only [evalPK, evalCT, evalErr, BP.eval, hi, evalPKAt, evalCTAt, evalErrAt, BP.coefs,
    BP.state, lt_irrefl, if_false]
  exact hl

end AdvancedEncryption.ExpLUT
