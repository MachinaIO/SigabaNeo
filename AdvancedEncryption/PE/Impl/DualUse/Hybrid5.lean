import PE.Impl.DualUse.Hybrid4
import PE.Impl.DualUse.Hybrid6
import PE.Impl.DualUse.Trapdoor

/-!
# Hybrid 5: Ring-LWE in normal form

After hybrids 1–4 the view is computed from `(B₀, B₁, p)` and `(c₀, c₁, κ₀) = s (B₀, B₁, p) + errors`
alone (plus coins of the view's own). With `B₁ = [1 | a | z]` (hybrid 3 makes `a`, `z` uniform),
the constant column makes `c₁`'s first entry `s + e`; a normal-form Ring-LWE instance (secret
`σ` from the error law) still yields the view exactly (`reduction5`): the reduction draws `u₀`,
and adds `u₀ ·` (public part) to the instance values `−σ · (public part) + e`, so that the
secret is `s = u₀ − σ` (uniform) and the error of the constant column is `σ`.

* On a real instance the view is that of hybrid 4 (`real5_eq`).
* On a uniform instance it is the view `h5View` of hybrid 6 (`unif5_eq`).
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib.Probability
open scoped ENNReal

variable {R : Type} [CommRing R] [Fintype R] [DecidableEq R] {k : ℕ} {S : Setting R k}
  {Wd : Type} [Fintype Wd] [DecidableEq Wd] [Nonempty Wd]
  [Fintype S.Attr] [DecidableEq S.Attr] [DecidableEq S.ctBits.Index]

/-- The trapdoor part after hybrid 3: `[1 | a | z]`. -/
def trapRowU (a z : Matrix (Fin 1) (Col k) R) : Matrix (Fin 1) (TrapCol k) R :=
  Matrix.of fun _ c => match c with
    | .inl _ => 1
    | .inr (.inl c) => a 0 c
    | .inr (.inr c) => z 0 c

/-- The error row of `B₁ = [1 | a | z]`: `[σ | ea | ez]`. -/
def trapRowU' (σ : R) (ea ez : Matrix (Fin 1) (Col k) R) : Matrix (Fin 1) (TrapCol k) R :=
  Matrix.of fun _ c => match c with
    | .inl _ => σ
    | .inr (.inl c) => ea 0 c
    | .inr (.inr c) => ez 0 c

/-- The public part of a Ring-LWE instance: `(B₀, a, z, p)`. -/
abbrev Pub (Wd : Type) (R : Type) (k : ℕ) :=
  Matrix (Fin 1) Wd R × Matrix (Fin 1) (Col k) R × Matrix (Fin 1) (Col k) R × R

/-- A row with independent entries from `χ`. -/
noncomputable def rowLaw (χ : PMF R) (ι : Type) [Fintype ι] : PMF (Matrix (Fin 1) ι R) :=
  (Cslib.Probability.PMF.pi fun _ : ι => χ).map fun v => Matrix.of fun _ c => v c

/-- **Normal-form Ring-LWE, real**: uniform public parts `P = (B₀, a, z, p)` and the values
`−σ P + e` for a secret `σ` and errors `e` from `χ` (the sign is the reduction's convenience; with
`−P` uniform this is the usual `(P', σ P' + e)`). -/
noncomputable def nfReal (χ : PMF R) : PMF (Pub Wd R k × Pub Wd R k) := do
  let σ ← χ
  let B₀ ← PMF.uniformOfFintype (Matrix (Fin 1) Wd R)
  let a ← PMF.uniformOfFintype (Matrix (Fin 1) (Col k) R)
  let z ← PMF.uniformOfFintype (Matrix (Fin 1) (Col k) R)
  let p ← PMF.uniformOfFintype R
  let e₀ ← rowLaw χ Wd
  let ea ← rowLaw χ (Col k)
  let ez ← rowLaw χ (Col k)
  let e' ← χ
  pure ((B₀, a, z, p),
    (-(scalar σ * B₀) + e₀, -(scalar σ * a) + ea, -(scalar σ * z) + ez, -(σ * p) + e'))

/-- **Normal-form Ring-LWE, uniform.** -/
noncomputable def nfUnif : PMF (Pub Wd R k × Pub Wd R k) := do
  let P ← PMF.uniformOfFintype (Pub Wd R k)
  let V ← PMF.uniformOfFintype (Pub Wd R k)
  pure (P, V)

variable (lawRm : PMF (S.Attr → Matrix Wd (Col k) R))
  (lawE : PMF (S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R))

/-- **The reduction of hybrid 5**: the view from an instance `(P, V)`. -/
noncomputable def reduction5 (x : S.Attr → Bool) (M : Bool) (inst : Pub Wd R k × Pub Wd R k) :
    PMF (MPK S Wd (TrapCol k) × Ciphertext S Wd (TrapCol k)) := do
  let u₀ ← PMF.uniformOfFintype R
  let w ← Cslib.Probability.PMF.pi fun _ : JC S => PMF.uniformOfFintype (Wd → Bool)
  let Rm ← lawRm
  let e ← lawE
  let B₀ := inst.1.1
  let a := inst.1.2.1
  let z := inst.1.2.2.1
  let p := inst.1.2.2.2
  let c₀ := scalar u₀ * B₀ + inst.2.1
  let c₁ : Matrix (Fin 1) (TrapCol k) R := Matrix.of fun _ c => match c with
    | .inl _ => u₀
    | .inr (.inl c) => (scalar u₀ * a + inst.2.2.1) 0 c
    | .inr (.inr c) => (scalar u₀ * z + inst.2.2.2.1) 0 c
  let Ψ : S.Attr → Matrix (Fin 2) (Col k) R :=
    fun i => gswPK B₀ c₀ * Rm i + bitR (R := R) (x i) • S.Γ.G
  let Bj := fun j => B₀ * wMat w j + bitsOf S Ψ j • S.Γ₁.G
  pure (⟨B₀, trapRowU a z, Bj, p⟩,
    ⟨Ψ, c₀, c₁, fun j => c₀ * wMat w j + e j, u₀ * p + inst.2.2.2.2 + (if M then S.half else 0)⟩)

omit [Fintype R] [DecidableEq R] in
/-- The uniform law on a product, component by component. -/
theorem uniform_prod_bind {α β γ : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (g : α × β → PMF γ) :
    (PMF.uniformOfFintype (α × β)).bind g =
      (PMF.uniformOfFintype α).bind fun a => (PMF.uniformOfFintype β).bind fun b => g (a, b) := by
  rw [← Cslib.Probability.PMF.uniformOfFintype_prod]
  simp only [PMF.bind_bind, PMF.bind_map]
  rfl

omit [Fintype R] [DecidableEq R] in
/-- Independent coordinates over a sum: the two blocks independently. -/
theorem pi_sum {α β γ : Type} [Fintype α] [Fintype β] [Finite γ] (μ : PMF γ) :
    Cslib.Probability.PMF.pi (fun _ : α ⊕ β => μ) =
      (Cslib.Probability.PMF.pi fun _ : α => μ).bind fun f =>
        (Cslib.Probability.PMF.pi fun _ : β => μ).map fun g => Sum.elim f g := by
  classical
  ext h
  rw [PMF.bind_apply, tsum_eq_single (fun a => h (.inl a))]
  · rw [PMF.map_apply, tsum_eq_single (fun b => h (.inr b))]
    · have : h = Sum.elim (fun a => h (.inl a)) (fun b => h (.inr b)) := by
        funext x; rcases x <;> rfl
      split_ifs
      simp only [Cslib.Probability.PMF.pi_apply, Fintype.prod_sum_type]
    · intro g hg
      split_ifs with he
      · exact absurd (funext fun b => by rw [he]; rfl) hg
      · rfl
  · intro f hf
    rw [PMF.map_apply]
    refine mul_eq_zero_of_right _ (tsum_eq_zero_iff.mpr fun g => ?_)
    split_ifs with he
    · exact absurd (funext fun a => by rw [he]; rfl) hf
    · rfl

/-- The trapdoor part after hybrid 3. -/
noncomputable def lawB₁u : PMF (Matrix (Fin 1) (TrapCol k) R) := do
  let a ← PMF.uniformOfFintype (Matrix (Fin 1) (Col k) R)
  let z ← PMF.uniformOfFintype (Matrix (Fin 1) (Col k) R)
  pure (trapRowU a z)

/-- The coins of `Enc` other than the encodings' errors, sampled as `s = u₀ − σ` with `σ` the
error of the constant column of `B₁` (the same law as an independent uniform `s`). -/
noncomputable def lawRestNF (χ : PMF R) : PMF (Rest S Wd (TrapCol k)) := do
  let σ ← χ
  let u₀ ← PMF.uniformOfFintype R
  let e₀ ← rowLaw χ Wd
  let ea ← rowLaw χ (Col k)
  let ez ← rowLaw χ (Col k)
  let Rm ← lawRm
  let e' ← χ
  pure (u₀ - σ, e₀, trapRowU' σ ea ez, Rm, e')

omit [DecidableEq R] [Nonempty Wd] [DecidableEq S.Attr] [DecidableEq S.ctBits.Index] in
/-- **The real side of hybrid 5**: on a real instance, the reduction gives the view of hybrid 4. -/
theorem real5_eq (χ : PMF R) (x : S.Attr → Bool) (M : Bool) :
    viewW lawB₁u (PMF.uniformOfFintype R) (lawRestNF lawRm χ) lawE x M floodCj =
      (nfReal χ).bind (reduction5 lawRm lawE x M) := by
  unfold viewW nfReal reduction5 lawB₁u lawRestNF
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind]
  conv_lhs => enter [2, x0]; rw [PMF.bind_comm]
  conv_lhs => enter [2, x0, 2, x1]; rw [PMF.bind_comm]
  conv_lhs => enter [2, x0, 2, x1, 2, x2]; rw [PMF.bind_comm]
  conv_lhs => enter [2, x0, 2, x1, 2, x2, 2, x3]; rw [PMF.bind_comm]
  conv_lhs => enter [2, x0, 2, x1, 2, x2, 2, x3, 2, x4]; rw [PMF.bind_comm]
  conv_lhs => enter [2, x0, 2, x1, 2, x2, 2, x3, 2, x4, 2, x5]; rw [PMF.bind_comm]
  conv_lhs => enter [2, x0, 2, x1, 2, x2, 2, x3, 2, x4, 2, x5, 2, x6]; rw [PMF.bind_comm]
  conv_lhs => enter [2, x0, 2, x1, 2, x2, 2, x3, 2, x4, 2, x5, 2, x6, 2, x7]; rw [PMF.bind_comm]
  conv_lhs => enter [2, x0, 2, x1, 2, x2, 2, x3, 2, x4, 2, x5, 2, x6, 2, x7, 2, x8, 2, x9]; rw [PMF.bind_comm]
  conv_lhs => enter [2, x0, 2, x1, 2, x2]; rw [PMF.bind_comm]
  conv_lhs => enter [2, x0, 2, x1, 2, x2, 2, x3, 2, x4]; rw [PMF.bind_comm]
  conv_lhs => enter [2, x0, 2, x1, 2, x2, 2, x3, 2, x4, 2, x5]; rw [PMF.bind_comm]
  conv_lhs => enter [2, x0, 2, x1, 2, x2, 2, x3, 2, x4, 2, x5, 2, x6]; rw [PMF.bind_comm]
  conv_lhs => enter [2, x0, 2, x1, 2, x2, 2, x3, 2, x4, 2, x5, 2, x6, 2, x7, 2, x8]; rw [PMF.bind_comm]
  conv_lhs => enter [2, x0, 2, x1]; rw [PMF.bind_comm]
  conv_lhs => enter [2, x0, 2, x1, 2, x2, 2, x3, 2, x4, 2, x5, 2, x6, 2, x7]; rw [PMF.bind_comm]
  conv_lhs => enter [2, x0]; rw [PMF.bind_comm]
  rw [PMF.bind_comm]
  refine congrArg (PMF.bind _) (funext fun σ => ?_)
  refine congrArg (PMF.bind _) (funext fun B₀ => ?_)
  refine congrArg (PMF.bind _) (funext fun a => ?_)
  refine congrArg (PMF.bind _) (funext fun z => ?_)
  refine congrArg (PMF.bind _) (funext fun p => ?_)
  refine congrArg (PMF.bind _) (funext fun e₀ => ?_)
  refine congrArg (PMF.bind _) (funext fun ea => ?_)
  refine congrArg (PMF.bind _) (funext fun ez => ?_)
  refine congrArg (PMF.bind _) (funext fun e' => ?_)
  refine congrArg (PMF.bind _) (funext fun u₀ => ?_)
  refine congrArg (PMF.bind _) (funext fun w => ?_)
  refine congrArg (PMF.bind _) (funext fun Rm => ?_)
  refine congrArg (PMF.bind _) (funext fun e => ?_)
  have hs : RingBTVW.scalar (u₀ - σ) * B₀ + e₀ =
      RingBTVW.scalar u₀ * B₀ + (-(RingBTVW.scalar σ * B₀) + e₀) := by
    ext i c
    simp [RingBTVW.scalar, Matrix.mul_apply, sub_mul]
    ring
  have hgsw : gswOf (S := S) B₀ x (coinsOf (u₀ - σ, e₀, trapRowU' σ ea ez, Rm, e') e) =
      fun i => gswPK B₀ (RingBTVW.scalar u₀ * B₀ + (-(RingBTVW.scalar σ * B₀) + e₀)) * Rm i +
        bitR (R := R) (x i) • S.Γ.G := by
    funext i
    simp only [gswOf, coinsOf, hs]
  refine congrArg PMF.pure (Prod.ext ?_ ?_)
  · show (⟨B₀, _, _, _⟩ : MPK S Wd (TrapCol k)) = ⟨B₀, _, _, _⟩
    congr 1
    funext j
    simp only [bjOf, of_hashCols, hgsw]
  · simp only [encrypt]
    congr 1
    all_goals first
      | (ext i c; fin_cases i; rcases c with c | c | c <;>
          simp [coinsOf, trapRowU, trapRowU', RingBTVW.scalar, Matrix.mul_apply] <;> ring)
      | (funext j; simp only [floodCj, coinsOf, hs])
      | (simp only [coinsOf]; ring)

omit [DecidableEq R] [Nonempty Wd] [Fintype S.Attr] [DecidableEq S.Attr]
  [DecidableEq S.ctBits.Index] in
/-- A uniform `2 × Wd` matrix is two independent uniform rows. -/
theorem uniform_two_rows_bind {γ : Type} (g : Matrix (Fin 2) Wd R → PMF γ) :
    (PMF.uniformOfFintype (Matrix (Fin 2) Wd R)).bind g =
      (PMF.uniformOfFintype (Matrix (Fin 1) Wd R)).bind fun B₀ =>
        (PMF.uniformOfFintype (Matrix (Fin 1) Wd R)).bind fun c₀ => g (gswPK B₀ c₀) := by
  let e : Matrix (Fin 1) Wd R × Matrix (Fin 1) Wd R ≃ Matrix (Fin 2) Wd R :=
    { toFun := fun bc => gswPK bc.1 bc.2
      invFun := fun A => (Matrix.of fun _ c => A 0 c, Matrix.of fun _ c => A 1 c)
      left_inv := fun bc => by
        ext i c <;> fin_cases i <;> simp [gswPK]
      right_inv := fun A => by
        ext i c; fin_cases i <;> simp [gswPK] }
  rw [← bind_uniform_equiv e g, uniform_prod_bind]
  rfl

omit [DecidableEq R] [Fintype Wd] [DecidableEq Wd] [Nonempty Wd] [Fintype S.Attr]
  [DecidableEq S.Attr] [DecidableEq S.ctBits.Index] in
/-- A uniform row of `B₁`'s width is a uniform `u₀` and two uniform rows. -/
theorem uniform_trapRow_bind {γ : Type} (g : Matrix (Fin 1) (TrapCol k) R → PMF γ) :
    (PMF.uniformOfFintype (Matrix (Fin 1) (TrapCol k) R)).bind g =
      (PMF.uniformOfFintype R).bind fun u₀ =>
        (PMF.uniformOfFintype (Matrix (Fin 1) (Col k) R)).bind fun ca =>
          (PMF.uniformOfFintype (Matrix (Fin 1) (Col k) R)).bind fun cz =>
            g (trapRowU' u₀ ca cz) := by
  let e : R × Matrix (Fin 1) (Col k) R × Matrix (Fin 1) (Col k) R ≃
      Matrix (Fin 1) (TrapCol k) R :=
    { toFun := fun v => trapRowU' v.1 v.2.1 v.2.2
      invFun := fun c => (c 0 (.inl 0), Matrix.of fun _ x => c 0 (.inr (.inl x)),
        Matrix.of fun _ x => c 0 (.inr (.inr x)))
      left_inv := fun v => by
        obtain ⟨u, a, b⟩ := v
        refine Prod.ext rfl (Prod.ext ?_ ?_) <;> ext i c <;> fin_cases i <;> rfl
      right_inv := fun c => by
        ext i x; fin_cases i
        rcases x with x | x | x
        · fin_cases x; rfl
        · rfl
        · rfl }
  rw [← bind_uniform_equiv e g, uniform_prod_bind]
  simp only [uniform_prod_bind]
  rfl

/-- Binary matrices `Rᵢ` from their columns. -/
def rMat (r : S.Attr × Col k → (Wd → Bool)) (i : S.Attr) : Matrix Wd (Col k) R :=
  Matrix.of fun a c => bitVal (r (i, c) a)

/-- The law of the binary matrices `Rᵢ`. -/
noncomputable def lawRmBin : PMF (S.Attr → Matrix Wd (Col k) R) :=
  (Cslib.Probability.PMF.pi fun _ : S.Attr × Col k => PMF.uniformOfFintype (Wd → Bool)).map rMat

/-- **The uniform side of hybrid 5**: on a uniform instance, the reduction gives `h5View`. -/
theorem unif5_eq (x : S.Attr → Bool) (M : Bool) :
    nfUnif.bind (reduction5 (S := S) (Wd := Wd) lawRmBin lawE x M) =
      h5View (Wd := Wd) lawB₁u lawE x M := by
  unfold nfUnif reduction5 h5View viewOf lawB₁u lawRmBin
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind, uniform_prod_bind, PMF.bind_map]
  rw [uniform_two_rows_bind]
  simp only [Cslib.Probability.PMF.pi_map, PMF.bind_map, pi_sum, PMF.bind_bind,
    uniform_trapRow_bind, Function.comp_def]
  conv_rhs => enter [2, B0, 2, c0]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, c0, 2, w]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, c0, 2, w, 2, a]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, c0, 2, w, 2, a, 2, z]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, c0, 2, w, 2, a, 2, z, 2, u]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, c0, 2, w, 2, a, 2, z, 2, u, 2, ca]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, c0, 2, w, 2, a, 2, z, 2, u, 2, ca, 2, cz]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, c0, 2, w, 2, a, 2, z, 2, u, 2, ca, 2, cz, 2, p]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, c0]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, c0, 2, a]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, c0, 2, a, 2, z]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, c0, 2, a, 2, z, 2, u]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, c0, 2, a, 2, z, 2, u, 2, ca]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, c0, 2, a, 2, z, 2, u, 2, ca, 2, cz]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, c0, 2, a, 2, z, 2, u, 2, ca, 2, cz, 2, p]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, a]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, a, 2, z]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, a, 2, z, 2, u, 2, c0, 2, ca]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, a, 2, z, 2, u, 2, c0]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, a, 2, z, 2, u]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, a, 2, z]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, a, 2, z, 2, p, 2, u]; rw [← bind_uniform_equiv (Equiv.addLeft (RingBTVW.scalar u * B0))]
  conv_rhs => enter [2, B0, 2, a, 2, z, 2, p, 2, u, 2, c0]; rw [← bind_uniform_equiv (Equiv.addLeft (RingBTVW.scalar u * a))]
  conv_rhs => enter [2, B0, 2, a, 2, z, 2, p, 2, u, 2, c0, 2, ca]; rw [← bind_uniform_equiv (Equiv.addLeft (RingBTVW.scalar u * z))]
  conv_rhs => enter [2, B0, 2, a, 2, z, 2, p, 2, u, 2, c0, 2, ca, 2, cz]; rw [← bind_uniform_equiv (Equiv.addLeft (u * p))]
  conv_rhs => enter [2, B0, 2, a, 2, z, 2, p]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, a, 2, z, 2, p, 2, c0]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, a, 2, z, 2, p, 2, c0, 2, ca]; rw [PMF.bind_comm]
  conv_rhs => enter [2, B0, 2, a, 2, z, 2, p, 2, c0, 2, ca, 2, cz]; rw [PMF.bind_comm]
  refine congrArg (PMF.bind _) (funext fun B₀ => ?_)
  refine congrArg (PMF.bind _) (funext fun a => ?_)
  refine congrArg (PMF.bind _) (funext fun z => ?_)
  refine congrArg (PMF.bind _) (funext fun p => ?_)
  refine congrArg (PMF.bind _) (funext fun v0 => ?_)
  refine congrArg (PMF.bind _) (funext fun va => ?_)
  refine congrArg (PMF.bind _) (funext fun vz => ?_)
  refine congrArg (PMF.bind _) (funext fun vp => ?_)
  refine congrArg (PMF.bind _) (funext fun u₀ => ?_)
  refine congrArg (PMF.bind _) (funext fun w => ?_)
  refine congrArg (PMF.bind _) (funext fun hr => ?_)
  refine congrArg (PMF.bind _) (funext fun e => ?_)
  simp only [Equiv.coe_addLeft]
  set c₀ := RingBTVW.scalar u₀ * B₀ + v0
  have hA0 : (Matrix.of fun _ c => gswPK B₀ c₀ 0 c : Matrix (Fin 1) Wd R) = B₀ := by
    ext i c; fin_cases i; simp [gswPK]
  have hA1 : (Matrix.of fun _ c => gswPK B₀ c₀ 1 c : Matrix (Fin 1) Wd R) = c₀ := by
    ext i c; fin_cases i; simp [gswPK]
  have hR : ∀ i, (colMat fun c => binaryHash (gswPK B₀ c₀) ((hr ⊕ᵥ w) (Sum.inl (i, c)))) =
      gswPK B₀ c₀ * rMat hr i := by
    intro i; ext r c
    simp only [colMat, binaryHash, rMat, Matrix.mulVec, dotProduct, Matrix.mul_apply, bitVal,
      Matrix.of_apply, Sum.elim_inl, mul_ite, mul_one, mul_zero]
    exact Finset.sum_congr rfl fun t _ => by by_cases h : hr (i, c) t <;> simp [h]
  have hT : ∀ j, topRow (colMat fun c => binaryHash (gswPK B₀ c₀) ((hr ⊕ᵥ w) (Sum.inr (j, c)))) =
      B₀ * wMat w j := by
    intro j; ext r c; fin_cases r
    simp [topRow, colMat, binaryHash, wMat, Matrix.mulVec, dotProduct, Matrix.mul_apply, gswPK,
      bitVal, mul_ite]
    exact Finset.sum_congr rfl fun t _ => by by_cases h : w (j, c) t <;> simp [h]
  have hB : ∀ j, botRow (colMat fun c => binaryHash (gswPK B₀ c₀) ((hr ⊕ᵥ w) (Sum.inr (j, c)))) =
      c₀ * wMat w j := by
    intro j; ext r c; fin_cases r
    simp [botRow, colMat, binaryHash, wMat, Matrix.mulVec, dotProduct, Matrix.mul_apply, gswPK,
      bitVal, mul_ite]
    exact Finset.sum_congr rfl fun t _ => by by_cases h : w (j, c) t <;> simp [h]
  have hc₁ : (Matrix.of fun _ c => match c with
      | Sum.inl _ => u₀
      | Sum.inr (Sum.inl c) => (RingBTVW.scalar u₀ * a + va) 0 c
      | Sum.inr (Sum.inr c) => (RingBTVW.scalar u₀ * z + vz) 0 c : Matrix (Fin 1) (TrapCol k) R) =
      trapRowU' u₀ (RingBTVW.scalar u₀ * a + va) (RingBTVW.scalar u₀ * z + vz) := by
    ext i c; rcases c with c | c | c <;> rfl
  simp only [hA0, hA1, hR, hT, hB, hc₁]

end AdvancedEncryption.DualUse
