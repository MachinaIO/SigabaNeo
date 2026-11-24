import PE.Impl.ExpLUT.Hybrid3

/-!
# The reduction to circular Ring-LWE (hybrids H3′ → H4)

**Circular Ring-LWE with automorphism keys** (Assumption 1 of ePrint 2026/2539), stated over C's
`Setting` (`σ_k = S.E.σ (S.idx (je k))`) in the shape the reduction uses (`CircInst`):

* plain samples `(a, s̄ a + e)`: `(aB, vB)` indexed by the columns of `B` (`m_B` samples), `(ad, vd)`
  (one sample), and `(aH k (1,i), vH k (1,i))` (`τ |J|` samples);
* circular samples `(a_k, s̄ a_k − σ_k(s̄) g + e_k)`: `(aH k (0,·), vH k (0,·))` for every `k ∈ J`
  (`vH k c = s̄ aH k c − σ_k(s̄) G⁽¹⁾_c + e`);

with `s̄ ← χs` and errors from `χ` (`circReal`), against uniform values (`circUnif`). This is the
instance of the paper's proof with `m = m_B + 1 + τ |J|` plain samples, reindexed; the bridge to the
word-level laws of `SigabaNeo.Lattices.CircularRingLWE` is a reindexing.

**The reduction** (`red`): from an instance, draw `B̄⁽²⁾`, the gadget columns of `B⁽²⁾`, the second
rows of the `H_k`, `d₂`, the flooding errors and the programming, and set (Appendix A, H4)
`B⁽¹⁾ := aB`, `b := vB + B⁽²⁾`, `d₁ := ad`, `c_m := vd + d₂`, `H_k⁽¹⁾ := aH k`,
`h_k := vH k − G⁽²⁾ + H_k⁽²⁾`; the view is H2's view from `b` (`view2`).

* `reduction_real`: on a real instance, the view has the law of **H3′**;
* `reduction_unif`: on a uniform instance, the view has the law of **H4** (`hyb4`: `b`, the
  helpers and `c_m` uniform).
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix Cslib.Probability
open scoped ENNReal

variable {R : Type} [CommRing R] [Fintype R] [DecidableEq R] {S : Setting R} {Wb J Pos : Type}
  [Fintype Wb] [DecidableEq Wb] [Nonempty Wb] [Fintype J] [DecidableEq J] [Fintype Pos]
  [DecidableEq Pos] (M : HelperMap S J) (w : ℕ) (χs χ χfl : PMF R)

variable (S Wb J) in
/-- A circular Ring-LWE instance in the shape of the reduction. -/
structure CircInst where
  /-- The public parts of the samples of `b`. -/
  aB : BCol Wb S.τ → R
  /-- Their values. -/
  vB : BCol Wb S.τ → R
  /-- The public part of the sample of `c_m`. -/
  ad : R
  /-- Its value. -/
  vd : R
  /-- The public parts of the helper samples (`(0,i)`: circular, `(1,i)`: plain). -/
  aH : J → Col S.τ → R
  /-- Their values. -/
  vH : J → Col S.τ → R

variable (S Wb J) in
/-- **Circular Ring-LWE, real**: `s̄ ← χs`, uniform public parts, errors from `χ`. -/
noncomputable def circReal : PMF (CircInst S Wb J) :=
  (PMF.uniformOfFintype (BCol Wb S.τ → R)).bind fun aB =>
  (PMF.uniformOfFintype (J → Col S.τ → R)).bind fun aH =>
  (PMF.uniformOfFintype R).bind fun ad =>
  χs.bind fun s => (iidLaw χ (BCol Wb S.τ)).bind fun eb => (iidFam χ J (Col S.τ)).bind fun eh =>
  χ.map fun em =>
    ⟨aB, s • aB + eb, ad, s * ad + em, aH,
      fun k c => s * aH k c - S.E.σ (S.idx (M.je k)) s * S.G 0 c + eh k c⟩

variable (S Wb J) in
/-- **Circular Ring-LWE, uniform.** -/
noncomputable def circUnif : PMF (CircInst S Wb J) :=
  (PMF.uniformOfFintype (BCol Wb S.τ → R)).bind fun aB =>
  (PMF.uniformOfFintype (J → Col S.τ → R)).bind fun aH =>
  (PMF.uniformOfFintype R).bind fun ad =>
  (PMF.uniformOfFintype (BCol Wb S.τ → R)).bind fun vB =>
  (PMF.uniformOfFintype (J → Col S.τ → R)).bind fun vH =>
  (PMF.uniformOfFintype R).map fun vd => ⟨aB, vB, ad, vd, aH, vH⟩

/-- The public data computed by the reduction. -/
def redPub (inst : CircInst S Wb J) (B2 : BCol Wb S.τ → R) (H2 : J → Col S.τ → R) (d2 : R) :
    PubData S Wb J :=
  ⟨Matrix.of ![fun v => inst.aB (.inl v), fun v => B2 (.inl v)], fun c => inst.aB (.inr c),
    fun c => B2 (.inr c), fun k => Matrix.of ![inst.aH k, H2 k], ![inst.ad, d2]⟩

/-- The core values computed by the reduction: `b = vB + B⁽²⁾`, `h_k = vH k − G⁽²⁾ + H_k⁽²⁾`,
`c_m = vd + d₂`. -/
def redCore (inst : CircInst S Wb J) (B2 : BCol Wb S.τ → R) (H2 : J → Col S.τ → R) (d2 : R) :
    Core S Wb J :=
  (inst.vB + B2, fun k c => inst.vH k c - S.G 1 c + H2 k c, inst.vd + d2)

/-- **The reduction**: the view of H2 from a circular Ring-LWE instance and the reduction's own
coins. -/
noncomputable def red (x : Pos → ℕ) (inst : CircInst S Wb J) :
    PMF (MPK S Wb J Pos × Ciphertext S Wb J Pos) :=
  (PMF.uniformOfFintype (BCol Wb S.τ → R)).bind fun B2 =>
  (PMF.uniformOfFintype (J → Col S.τ → R)).bind fun H2 =>
  (PMF.uniformOfFintype R).bind fun d2 =>
  (floodLaw S Pos χfl).bind fun fl =>
  (zrLaw S Wb Pos).map fun zr =>
    view2 M w (redPub inst B2 H2 d2) x zr (redCore inst B2 H2 d2) fl

/-- **H4**: H3′ with `b`, the helpers and `c_m` uniform. -/
noncomputable def hyb4 (x : Pos → ℕ) : PMF (MPK S Wb J Pos × Ciphertext S Wb J Pos) :=
  (PMF.uniformOfFintype (Matrix (Fin 2) Wb R)).bind fun Bb =>
  (PMF.uniformOfFintype (Fin S.τ → R)).bind fun Bg1 =>
  (PMF.uniformOfFintype (RestPub S J)).bind fun rp =>
  (PMF.uniformOfFintype (Core S Wb J)).bind fun core =>
  (floodLaw S Pos χfl).bind fun fl =>
  (zrLaw S Wb Pos).map fun zr => view2 M w (pubOf Bb Bg1 rp) x zr core fl

/-! ### Splitting uniform draws -/

theorem uniform_H_bind {β : Type} (g : (J → Matrix (Fin 2) (Col S.τ) R) → PMF β) :
    (PMF.uniformOfFintype (J → Matrix (Fin 2) (Col S.τ) R)).bind g =
      (PMF.uniformOfFintype (J → Col S.τ → R)).bind fun aH =>
        (PMF.uniformOfFintype (J → Col S.τ → R)).bind fun H2 =>
          g fun k => Matrix.of ![aH k, H2 k] := by
  let e : (J → Col S.τ → R) × (J → Col S.τ → R) ≃ (J → Matrix (Fin 2) (Col S.τ) R) :=
    { toFun := fun p k => Matrix.of ![p.1 k, p.2 k]
      invFun := fun H => (fun k => H k 0, fun k => H k 1)
      left_inv := fun _ => rfl
      right_inv := fun H => by funext k; ext i j; fin_cases i <;> rfl }
  rw [← bind_uniform_equiv e g, uniform_prod_bind]
  rfl

theorem uniform_d_bind {β : Type} (g : (Fin 2 → R) → PMF β) :
    (PMF.uniformOfFintype (Fin 2 → R)).bind g =
      (PMF.uniformOfFintype R).bind fun ad => (PMF.uniformOfFintype R).bind fun d2 => g ![ad, d2] := by
  rw [← bind_uniform_equiv (piFinTwoEquiv fun _ => R).symm g, uniform_prod_bind]
  rfl

/-- The reduction's values on a real instance are those of `Enc`. -/
theorem redCore_real (Ab B2b : Wb → R) (Bg1 B2g : Fin S.τ → R) (aH H2 : J → Col S.τ → R)
    (ad d2 s : R) (eb : BCol Wb S.τ → R) (eh : J → Col S.τ → R) (em : R) (fl : FloodV S Pos) :
    redCore (⟨Sum.elim Ab Bg1, s • Sum.elim Ab Bg1 + eb, ad, s * ad + em, aH,
        fun k c => s * aH k c - S.E.σ (S.idx (M.je k)) s * S.G 0 c + eh k c⟩ : CircInst S Wb J)
        (Sum.elim B2b B2g) H2 d2 =
      coreOf M (pubOf (Matrix.of ![Ab, B2b]) Bg1 (B2g, fun k => Matrix.of ![aH k, H2 k], ![ad, d2]))
        (⟨s, eb, eh, fl.1, fl.2.1, fl.2.2.1, fl.2.2.2, em⟩ : EncCoins S Wb J Pos) := by
  simp only [redCore, coreOf, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext c
    rcases c with v | c <;>
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, sec, PubData.B, pubOf] <;> ring
  · funext k c
    simp only [helpersOf, pubOf, Pi.add_apply, Pi.sub_apply, vecMul_sec_apply, vecMul_sec_G,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_mul]
    ring
  · simp [dotProduct, Fin.sum_univ_two, sec, pubOf]; ring

/-- **The reduction on a real instance gives H3′.** -/
theorem reduction_real (x : Pos → ℕ) :
    (circReal S Wb J M χs χ).bind (red M w χfl x) = hyb3 M w χs χ χfl x := by
  unfold circReal red hyb3
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, PMF.pure_bind]
  rw [uniform_rows_bind, uniform_sum_bind]
  refine congrArg (PMF.bind _) (funext fun Ab => ?_)
  simp only [uniform_prod_bind, uniform_H_bind, uniform_d_bind, encCoinsLaw_eq, PMF.bind_bind,
    PMF.bind_map, Function.comp_def, uniform_sum_bind]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6, 2, y7]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6, 2, y7, 2, y8]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6, 2, y7, 2, y8, 2, y9]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6, 2, y7]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1]; rw [PMF.bind_comm]
  conv_lhs => rw [PMF.bind_comm]
  refine congrArg (PMF.bind _) (funext fun B2b => ?_)
  refine congrArg (PMF.bind _) (funext fun Bg1 => ?_)
  refine congrArg (PMF.bind _) (funext fun B2g => ?_)
  refine congrArg (PMF.bind _) (funext fun aH => ?_)
  refine congrArg (PMF.bind _) (funext fun H2 => ?_)
  refine congrArg (PMF.bind _) (funext fun ad => ?_)
  refine congrArg (PMF.bind _) (funext fun d2 => ?_)
  refine congrArg (PMF.bind _) (funext fun s => ?_)
  refine congrArg (PMF.bind _) (funext fun eb => ?_)
  refine congrArg (PMF.bind _) (funext fun eh => ?_)
  refine congrArg (PMF.bind _) (funext fun fl => ?_)
  refine congrArg (PMF.bind _) (funext fun em => ?_)
  refine congrArg (PMF.map · _) (funext fun zr => ?_)
  rw [← redCore_real M Ab B2b Bg1 B2g aH H2 ad d2 s eb eh em fl]
  rfl

/-- **The reduction on a uniform instance gives H4.** -/
theorem reduction_unif (x : Pos → ℕ) :
    (circUnif S Wb J).bind (red M w χfl x) = hyb4 M w χfl x := by
  unfold circUnif red hyb4
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rw [uniform_rows_bind, uniform_sum_bind]
  refine congrArg (PMF.bind _) (funext fun Ab => ?_)
  simp only [uniform_prod_bind, uniform_H_bind, uniform_d_bind, PMF.bind_map, Function.comp_def]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5]; rw [uniform_sum_bind]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6, 2, y7]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1]; rw [PMF.bind_comm]
  conv_lhs => rw [PMF.bind_comm]
  conv_rhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6]
              rw [← uniform_bind_add (Sum.elim y0 y2)]
  conv_rhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6, 2, y7]
              rw [← uniform_bind_add (fun k c => -S.G 1 c + y4 k c)]
  conv_rhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6, 2, y7, 2, y8]
              rw [← uniform_bind_add y6]
  refine congrArg (PMF.bind _) (funext fun B2b => ?_)
  refine congrArg (PMF.bind _) (funext fun Bg1 => ?_)
  refine congrArg (PMF.bind _) (funext fun B2g => ?_)
  refine congrArg (PMF.bind _) (funext fun aH => ?_)
  refine congrArg (PMF.bind _) (funext fun H2 => ?_)
  refine congrArg (PMF.bind _) (funext fun ad => ?_)
  refine congrArg (PMF.bind _) (funext fun d2 => ?_)
  refine congrArg (PMF.bind _) (funext fun vB => ?_)
  refine congrArg (PMF.bind _) (funext fun vH => ?_)
  refine congrArg (PMF.bind _) (funext fun vd => ?_)
  refine congrArg (PMF.bind _) (funext fun fl => ?_)
  refine congrArg (PMF.map · _) (funext fun zr => ?_)
  congr 1
  simp only [redCore, Prod.mk.injEq, true_and, and_true]
  funext k c
  simp only [Pi.add_apply]
  ring

end AdvancedEncryption.ExpLUT
