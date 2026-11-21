import PE.Impl.DualUse.Registry

/-!
# The final view is a product

In the final view of the hybrids, the public key and the ciphertext are independent: the public
key has uniform `B₀`, `B_j`, `p` and `B₁` from its law, and every component of the ciphertext is
uniform (`finalView_prod`). The simulator of attribute hiding outputs `ctU`.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib.Probability

variable {R : Type} [CommRing R] [Fintype R] [DecidableEq R] {k : ℕ} {S : Setting R k}
  {Wd Wt : Type} [Fintype Wd] [Fintype Wt] [DecidableEq Wd] [DecidableEq Wt] [Nonempty Wd]
  [Fintype S.Attr] [DecidableEq S.Attr] [DecidableEq S.ctBits.Index]

variable (S Wd Wt) in
/-- A public key with uniform `B₀`, `B_j`, `p` and `B₁` from `lawB₁`. -/
noncomputable def mpkU (lawB₁ : PMF (Matrix (Fin 1) Wt R)) : PMF (MPK S Wd Wt) := do
  let B₀ ← PMF.uniformOfFintype (Matrix (Fin 1) Wd R)
  let B₁ ← lawB₁
  let Bj ← PMF.uniformOfFintype (S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R)
  let p ← PMF.uniformOfFintype R
  pure ⟨B₀, B₁, Bj, p⟩

variable (S Wd Wt) in
/-- A uniform ciphertext. -/
noncomputable def ctU : PMF (Ciphertext S Wd Wt) := do
  let Ψ ← PMF.uniformOfFintype (S.Attr → Matrix (Fin 2) (Col k) R)
  let c₀ ← PMF.uniformOfFintype (Matrix (Fin 1) Wd R)
  let c₁ ← PMF.uniformOfFintype (Matrix (Fin 1) Wt R)
  let cj ← PMF.uniformOfFintype (S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R)
  let κ ← PMF.uniformOfFintype R
  pure ⟨Ψ, c₀, c₁, cj, κ⟩

variable (lawB₁ : PMF (Matrix (Fin 1) Wt R))
  (lawE : PMF (S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R))

/-- The columns of the Ring-GSW ciphertexts as matrices. -/
def colEquivΨ : (S.Attr × Col k → (Fin 2 → R)) ≃ (S.Attr → Matrix (Fin 2) (Col k) R) where
  toFun f i := Matrix.of fun a c => f (i, c) a
  invFun Ψ ic a := Ψ ic.1 a ic.2
  left_inv f := by funext ic a; rfl
  right_inv Ψ := by funext i; ext a c; rfl

/-- The columns of the encodings as two rows. -/
def colEquivJ : ((S.Attr × S.ctBits.Index) × Col k → (Fin 2 → R)) ≃
    (S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R) ×
      (S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R) where
  toFun f := (fun j => Matrix.of fun _ c => f (j, c) 0, fun j => Matrix.of fun _ c => f (j, c) 1)
  invFun tb jc a := if a = 0 then tb.1 jc.1 0 jc.2 else tb.2 jc.1 0 jc.2
  left_inv f := by
    funext jc a
    fin_cases a <;> rfl
  right_inv tb := by
    ext j a c <;> fin_cases a <;> rfl

omit [DecidableEq R] [Nonempty Wd] in
/-- **The final view is a product.** -/
theorem finalView_prod (x : S.Attr → Bool) (M : Bool) :
    finalView (Wd := Wd) lawB₁ lawE x M =
      (mpkU S Wd Wt lawB₁).bind fun mpk => (ctU S Wd Wt).map (mpk, ·) := by
  rw [finalView_eq_raw, uniform_two_rows_bind]
  simp only [mpkU, Cslib.Probability.PMF.monad_bind_eq_bind,
    Cslib.Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  refine congrArg (PMF.bind _) (funext fun B₀ => ?_)
  -- the columns: those of `Ψ`, then the two rows of the encodings
  conv_lhs => enter [2, c₀]; rw [uniform_sum_bind]
  conv_lhs => enter [2, c₀]; rw [← bind_uniform_equiv colEquivΨ.symm]
  conv_lhs => enter [2, c₀, 2, Ψ]; rw [← bind_uniform_equiv colEquivJ.symm, uniform_prod_bind]
  simp only [rawOf, Cslib.Probability.PMF.monad_bind_eq_bind,
    Cslib.Probability.PMF.monad_pure_eq_pure, mpkU, ctU, PMF.bind_bind, PMF.pure_bind,
    PMF.bind_map]
  have r0 : ∀ c₀ : Matrix (Fin 1) Wd R, (of fun (_ : Fin 1) c => gswPK B₀ c₀ 0 c) = B₀ := fun c₀ => by
    ext i c; fin_cases i; simp [gswPK]
  have r1 : ∀ c₀ : Matrix (Fin 1) Wd R, (of fun (_ : Fin 1) c => gswPK B₀ c₀ 1 c) = c₀ := fun c₀ => by
    ext i c; fin_cases i; simp [gswPK]
  have cΨ : ∀ (Ψ : S.Attr → Matrix (Fin 2) (Col k) R)
      (g : (S.Attr × S.ctBits.Index) × Col k → (Fin 2 → R)),
      (fun i => colMat fun c => (colEquivΨ.symm Ψ ⊕ᵥ g) (Sum.inl (i, c))) = Ψ := fun Ψ g => by
    funext i; ext a c; rfl
  have cT : ∀ (f : S.Attr × Col k → (Fin 2 → R)) (ab : (S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R) ×
      (S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R)),
      (fun j => topRow (colMat fun c => (f ⊕ᵥ colEquivJ.symm ab) (Sum.inr (j, c)))) = ab.1 :=
    fun f ab => by funext j; ext i c; fin_cases i; simp [topRow, colMat, colEquivJ]
  have cB : ∀ (f : S.Attr × Col k → (Fin 2 → R)) (ab : (S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R) ×
      (S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R)) j,
      botRow (colMat fun c => (f ⊕ᵥ colEquivJ.symm ab) (Sum.inr (j, c))) = ab.2 j :=
    fun f ab j => by ext i c; fin_cases i; simp [botRow, colMat, colEquivJ]
  simp only [r0, r1, cΨ, cT, cB]
  -- the errors of the encodings: a uniform shifted row is uniform
  have shift : ∀ {γ : Type} (g : (S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R) → PMF γ),
      (PMF.uniformOfFintype (S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R)).bind g =
        lawE.bind fun e => (PMF.uniformOfFintype (S.Attr × S.ctBits.Index →
          Matrix (Fin 1) (Col k) R)).bind fun b => g fun j => b j + e j := by
    intro γ g
    have : ∀ e : S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R,
        ((PMF.uniformOfFintype (S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R)).bind
          fun b => g fun j => b j + e j) =
        (PMF.uniformOfFintype (S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R)).bind g :=
      fun e => bind_uniform_equiv (Equiv.addRight e) g
    simp only [this, PMF.bind_const]
  simp only [PMF.map_bind, PMF.pure_map]
  conv_rhs => enter [2, v_B1, 2, v_a, 2, v_p, 2, v_Psi, 2, v_c0, 2, v_c1]; rw [shift]
  conv_lhs => enter [2, v_c0, 2, v_Psi, 2, v_a, 2, v_b]; rw [PMF.bind_comm]
  conv_lhs => enter [2, v_c0, 2, v_Psi, 2, v_a]; rw [PMF.bind_comm]
  conv_lhs => enter [2, v_c0, 2, v_Psi]; rw [PMF.bind_comm]
  conv_lhs => enter [2, v_c0]; rw [PMF.bind_comm]
  conv_lhs => rw [PMF.bind_comm]
  conv_lhs => enter [2, v_B1, 2, v_c0]; rw [PMF.bind_comm]
  conv_lhs => enter [2, v_B1]; rw [PMF.bind_comm]
  conv_lhs => enter [2, v_B1, 2, v_a, 2, v_c0, 2, v_Psi, 2, v_b, 2, v_kappa]; rw [PMF.bind_comm]
  conv_lhs => enter [2, v_B1, 2, v_a, 2, v_c0, 2, v_Psi, 2, v_b]; rw [PMF.bind_comm]
  conv_lhs => enter [2, v_B1, 2, v_a, 2, v_c0, 2, v_Psi]; rw [PMF.bind_comm]
  conv_lhs => enter [2, v_B1, 2, v_a, 2, v_c0]; rw [PMF.bind_comm]
  conv_lhs => enter [2, v_B1, 2, v_a]; rw [PMF.bind_comm]
  conv_lhs => enter [2, v_B1, 2, v_a, 2, v_p]; rw [PMF.bind_comm]
  conv_lhs => enter [2, v_B1, 2, v_a, 2, v_p, 2, v_Psi, 2, v_c0, 2, v_b]; rw [PMF.bind_comm]
  conv_lhs => enter [2, v_B1, 2, v_a, 2, v_p, 2, v_Psi, 2, v_c0]; rw [PMF.bind_comm]
  conv_lhs => enter [2, v_B1, 2, v_a, 2, v_p, 2, v_Psi, 2, v_c0, 2, v_c1, 2, v_b]; rw [PMF.bind_comm]
  conv_lhs => enter [2, v_B1, 2, v_a, 2, v_p, 2, v_Psi, 2, v_c0, 2, v_c1]; rw [PMF.bind_comm]

end AdvancedEncryption.DualUse
