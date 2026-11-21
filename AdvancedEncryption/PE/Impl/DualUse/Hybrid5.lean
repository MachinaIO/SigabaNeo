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

end AdvancedEncryption.DualUse
