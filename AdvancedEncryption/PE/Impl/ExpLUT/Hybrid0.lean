import PE.Impl.ExpLUT.Hybrid12

/-!
# H0 = H1u: the real experiment with uniform programming values

The real `(mpk, ct)` (`hyb0`: `Setup` with the binary trapdoor law and `Enc` of `0`, C's
`setupLaw` and `encLaw`) has the law of `hyb1u` (`hyb0_eq_hyb1u`): with uniform values in place of
the programming hashes, the programmed matrices `a_t = u + X^{w x_t} G⁽¹⁾`, `A₀ = U + G`,
`A^in_{t,d} = U + d G`, `A^aut_{t,d} = σ_{g_t}(U) + d G` are uniform and independent, whatever the
digits `d` (which depend on the other coins only), as in the real `Setup` (`progLaw_eq`); and
`B⁽¹⁾ = [Ā | g − Ā T]` is the TrapGen row of `B̄ = [Ā; B̄⁽²⁾]` and the binary columns of `T`
(`iidFam_bitLaw`).
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix Cslib.Probability
open scoped ENNReal

variable {R : Type} [CommRing R] [Fintype R] [DecidableEq R] {S : Setting R} {Wb J Pos : Type}
  [Fintype Wb] [DecidableEq Wb] [Nonempty Wb] [Fintype J] [DecidableEq J] [Fintype Pos]
  [DecidableEq Pos] (M : HelperMap S J) (w : ℕ) (half : R) (χs χ χfl : PMF R)

/-- The public key from its parts. -/
def mpkOf (P : PubData S Wb J) (a : Pos → Col S.τ → R) (A0 : Matrix (Fin 2) (Col S.τ) R)
    (Ain : Pos → Dig S.τ → Matrix (Fin 2) (Col S.τ) R)
    (Aaut : Fin S.b → Dig S.τ → Matrix (Fin 2) (Col S.τ) R) : MPK S Wb J Pos :=
  ⟨P.B, P.H, a, A0, Ain, Aaut, P.d⟩

/-- `σ_{g_t}` entrywise on a family of matrices, a bijection (inverse `σ_{g_t^{-1}}`). -/
def σFam : (Fin S.b → Dig S.τ → Matrix (Fin 2) (Col S.τ) R) ≃
    (Fin S.b → Dig S.τ → Matrix (Fin 2) (Col S.τ) R) where
  toFun A t d := Matrix.of fun ρ c => S.E.σ (S.kf t) (A t d ρ c)
  invFun A t d := Matrix.of fun ρ c => S.E.σ (S.ki t) (A t d ρ c)
  left_inv A := by
    funext t d; ext ρ c
    simp only [Matrix.of_apply]
    have hW : 2 ^ (t : ℕ) ≤ S.E.W := by
      rw [S.W_eq]; exact Nat.pow_le_pow_right (by norm_num) t.2.le
    rw [S.idx_add, show S.E.W - 2 ^ (t : ℕ) + 2 ^ (t : ℕ) = S.E.W by omega, Nat.mod_self,
      S.idx_zero]
  right_inv A := by
    funext t d; ext ρ c
    simp only [Matrix.of_apply]
    have hW : 2 ^ (t : ℕ) ≤ S.E.W := by
      rw [S.W_eq]; exact Nat.pow_le_pow_right (by norm_num) t.2.le
    exact σ_idx_inv t hW _

/-- Reshaping the hash values of a block of programming columns into a family of matrices. -/
def reshape {ι κ : Type} : (ι × κ × Col S.τ → Fin 2 → R) ≃ (ι → κ → Matrix (Fin 2) (Col S.τ) R) where
  toFun h t d := Matrix.of fun ρ c => h (t, d, c) ρ
  invFun A i ρ := A i.1 i.2.1 ρ i.2.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- The programmed `a_t` from the hash values of the `Z_t` block. -/
def aOfH (x : Pos → ℕ) (hA : Pos × Col S.τ → Fin 2 → R) : Pos → Col S.τ → R :=
  fun t c => hA (t, c) 0 + S.E.X ^ (w * x t) * S.G 0 c

/-- The view of `Setup`'s public key with given `a`, `A₀`, `A^in`, `A^aut`, and `Enc`'s ciphertext. -/
def mkV (P : PubData S Wb J) (x : Pos → ℕ) (r : EncCoins S Wb J Pos) (a : Pos → Col S.τ → R)
    (A0 : Matrix (Fin 2) (Col S.τ) R) (Ain : Pos → Dig S.τ → Matrix (Fin 2) (Col S.τ) R)
    (Aaut : Fin S.b → Dig S.τ → Matrix (Fin 2) (Col S.τ) R) :
    MPK S Wb J Pos × Ciphertext S Wb J Pos :=
  (mpkOf P a A0 Ain Aaut, encrypt M w half (mpkOf P a A0 Ain Aaut) x 0 r)

/-- The shift of `A^in`: the digits of `C^in_t` times `G`. -/
def dIn (x : Pos → ℕ) (r : EncCoins S Wb J Pos) (a : Pos → Col S.τ → R) :
    Pos → Dig S.τ → Matrix (Fin 2) (Col S.τ) R :=
  fun t d => digits S (cinMat (a t) (cinBotsOf w a x r t)) d • S.G

/-- The shift of `A^aut`: the digits of `C_{g_t}` times `G`. -/
def dAut (H : J → Matrix (Fin 2) (Col S.τ) R) (h : J → Col S.τ → R) :
    Fin S.b → Dig S.τ → Matrix (Fin 2) (Col S.τ) R :=
  fun t d => digits S (autGC M H h t) d • S.G

/-- `A₀` from the hash values of its block. -/
def a0Equiv : (Col S.τ → Fin 2 → R) ≃ Matrix (Fin 2) (Col S.τ) R where
  toFun h := Matrix.of fun ρ c => h c ρ
  invFun A c ρ := A ρ c
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype R] [DecidableEq R] [Fintype Wb] [DecidableEq Wb] [Nonempty Wb] [Fintype J]
  [DecidableEq J] [Fintype Pos] [DecidableEq Pos] in
theorem view1_split (P : PubData S Wb J) (x : Pos → ℕ) (r : EncCoins S Wb J Pos)
    (hA : Pos × Col S.τ → Fin 2 → R) (h0 : Col S.τ → Fin 2 → R)
    (hIn : Pos × Dig S.τ × Col S.τ → Fin 2 → R) (hAut : Fin S.b × Dig S.τ × Col S.τ → Fin 2 → R) :
    view1 M w half P x (Sum.elim hA (Sum.elim h0 (Sum.elim hIn hAut))) r =
      mkV M w half P x r (aOfH w x hA) (a0Equiv h0 + S.G)
        (reshape hIn + dIn w x r (aOfH w x hA))
        (σFam (reshape hAut) + dAut M P.H (helpersOf M P.H r)) := by
  have hm : mpk1 M w P x (Sum.elim hA (Sum.elim h0 (Sum.elim hIn hAut))) r =
      mpkOf P (aOfH w x hA) (a0Equiv h0 + S.G) (reshape hIn + dIn w x r (aOfH w x hA))
        (σFam (reshape hAut) + dAut M P.H (helpersOf M P.H r)) := by
    unfold mpk1 progMPK mpkOf
    congr 1
  unfold view1 mkV
  rw [hm]

omit [DecidableEq R] [Fintype Wb] [DecidableEq Wb] [Nonempty Wb] [Fintype J] [DecidableEq J] in
/-- **Uniform programming values give the real public key**: for fixed other coins, the
programmed matrices from uniform hash values are uniform and independent. -/
theorem progLaw_eq (P : PubData S Wb J) (x : Pos → ℕ) (r : EncCoins S Wb J Pos) :
    (PMF.pi fun _ : PrI S Pos => PMF.uniformOfFintype (Fin 2 → R)).map
        (fun hp => view1 M w half P x hp r) =
      (PMF.uniformOfFintype (Pos → Col S.τ → R)).bind fun a =>
      (PMF.uniformOfFintype (Matrix (Fin 2) (Col S.τ) R)).bind fun A0 =>
      (PMF.uniformOfFintype (Pos → Dig S.τ → Matrix (Fin 2) (Col S.τ) R)).bind fun Ain =>
      (PMF.uniformOfFintype (Fin S.b → Dig S.τ → Matrix (Fin 2) (Col S.τ) R)).map fun Aaut =>
        mkV M w half P x r a A0 Ain Aaut := by
  have hsplit : (PMF.pi fun _ : PrI S Pos => PMF.uniformOfFintype (Fin 2 → R)) =
      (PMF.pi fun _ : Pos × Col S.τ => PMF.uniformOfFintype (Fin 2 → R)).bind fun hA =>
      (PMF.pi fun _ : Col S.τ => PMF.uniformOfFintype (Fin 2 → R)).bind fun h0 =>
      (PMF.pi fun _ : Pos × Dig S.τ × Col S.τ => PMF.uniformOfFintype (Fin 2 → R)).bind fun hIn =>
      (PMF.pi fun _ : Fin S.b × Dig S.τ × Col S.τ => PMF.uniformOfFintype (Fin 2 → R)).map
        fun hAut => Sum.elim hA (Sum.elim h0 (Sum.elim hIn hAut)) := by
    rw [pi_sum']
    congr 1; funext hA
    rw [pi_sum', PMF.map_bind]
    congr 1; funext h0
    rw [pi_sum', PMF.map_bind, PMF.map_bind]
    congr 1; funext hIn
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  have hA_eq : ∀ K : (Pos → Col S.τ → R) → PMF (MPK S Wb J Pos × Ciphertext S Wb J Pos),
      (PMF.uniformOfFintype (Pos × Col S.τ → Fin 2 → R)).bind (fun hA => K (aOfH w x hA)) =
        (PMF.uniformOfFintype (Pos → Col S.τ → R)).bind K := by
    intro K
    have hrow : (PMF.uniformOfFintype (Pos × Col S.τ → Fin 2 → R)).map (fun h i => h i 0) =
        PMF.uniformOfFintype (Pos × Col S.τ → R) := by
      calc (PMF.uniformOfFintype (Pos × Col S.τ → Fin 2 → R)).map (fun h i => h i 0)
          = (PMF.pi fun _ : Pos × Col S.τ => PMF.uniformOfFintype (Fin 2 → R)).map
              (fun h i => h i 0) := by rw [Cslib.Probability.PMF.pi_uniformOfFintype]
        _ = PMF.pi fun _ : Pos × Col S.τ => (PMF.uniformOfFintype (Fin 2 → R)).map (fun u => u 0) :=
            (Cslib.Probability.PMF.pi_map (fun _ => PMF.uniformOfFintype (Fin 2 → R))
              (fun _ u => u 0)).symm
        _ = PMF.pi fun _ : Pos × Col S.τ => PMF.uniformOfFintype R := by simp only [uniform_fin2_row0]
        _ = _ := Cslib.Probability.PMF.pi_uniformOfFintype
    have hshift : aOfH w x = (fun a : Pos → Col S.τ → R => a + fun t c => S.E.X ^ (w * x t) * S.G 0 c) ∘
        (Equiv.curry Pos (Col S.τ) R) ∘ (fun h i => h i 0) := by
      funext hA; rfl
    rw [show (fun hA => K (aOfH w x hA)) = K ∘ aOfH w x from rfl, ← PMF.bind_map, hshift,
      ← PMF.map_comp, ← PMF.map_comp, hrow, uniform_map_equiv, PMF.bind_map]
    exact uniform_bind_add _ K
  rw [hsplit]
  simp only [Cslib.Probability.PMF.pi_uniformOfFintype, PMF.map_bind, PMF.map_comp,
    Function.comp_def, view1_split]
  rw [hA_eq (fun a => (PMF.uniformOfFintype (Col S.τ → Fin 2 → R)).bind fun h0 =>
      (PMF.uniformOfFintype (Pos × Dig S.τ × Col S.τ → Fin 2 → R)).bind fun hIn =>
      (PMF.uniformOfFintype (Fin S.b × Dig S.τ × Col S.τ → Fin 2 → R)).map fun hAut =>
        mkV M w half P x r a (a0Equiv h0 + S.G) (reshape hIn + dIn w x r a)
          (σFam (reshape hAut) + dAut M P.H (helpersOf M P.H r)))]
  refine congrArg (PMF.bind _) (funext fun a => ?_)
  rw [bind_uniform_equiv a0Equiv (fun A0 => (PMF.uniformOfFintype (Pos × Dig S.τ × Col S.τ →
      Fin 2 → R)).bind fun hIn =>
      (PMF.uniformOfFintype (Fin S.b × Dig S.τ × Col S.τ → Fin 2 → R)).map fun hAut =>
        mkV M w half P x r a (A0 + S.G) (reshape hIn + dIn w x r a)
          (σFam (reshape hAut) + dAut M P.H (helpersOf M P.H r))),
    uniform_bind_add S.G (fun A0 => (PMF.uniformOfFintype (Pos × Dig S.τ × Col S.τ →
      Fin 2 → R)).bind fun hIn =>
      (PMF.uniformOfFintype (Fin S.b × Dig S.τ × Col S.τ → Fin 2 → R)).map fun hAut =>
        mkV M w half P x r a A0 (reshape hIn + dIn w x r a)
          (σFam (reshape hAut) + dAut M P.H (helpersOf M P.H r)))]
  refine congrArg (PMF.bind _) (funext fun A0 => ?_)
  rw [bind_uniform_equiv reshape (fun Ain =>
      (PMF.uniformOfFintype (Fin S.b × Dig S.τ × Col S.τ → Fin 2 → R)).map fun hAut =>
        mkV M w half P x r a A0 (Ain + dIn w x r a)
          (σFam (reshape hAut) + dAut M P.H (helpersOf M P.H r))),
    uniform_bind_add (dIn w x r a) (fun Ain =>
      (PMF.uniformOfFintype (Fin S.b × Dig S.τ × Col S.τ → Fin 2 → R)).map fun hAut =>
        mkV M w half P x r a A0 Ain (σFam (reshape hAut) + dAut M P.H (helpersOf M P.H r)))]
  refine congrArg (PMF.bind _) (funext fun Ain => ?_)
  have := bind_uniform_equiv (reshape.trans σFam) (fun Aaut =>
    PMF.pure (mkV M w half P x r a A0 Ain (Aaut + dAut M P.H (helpersOf M P.H r))))
  rw [uniform_bind_add (dAut M P.H (helpersOf M P.H r)) (fun Aaut =>
    PMF.pure (mkV M w half P x r a A0 Ain Aaut))] at this
  simp only [Equiv.trans_apply] at this
  exact this

/-! ### The real experiment -/

/-- **H0**: the real `(mpk, ct)`: `Setup` with the binary trapdoor law, and `Enc` of `0`. -/
noncomputable def hyb0 (x : Pos → ℕ) : PMF (MPK S Wb J Pos × Ciphertext S Wb J Pos) :=
  (setupLaw S Wb J Pos bitLaw).bind fun v =>
    (encLaw S Wb J Pos χs χ χfl M w half v.1 x 0).map fun ct => (v.1, ct)

/-- The common normal form of H0 and H1u. -/
noncomputable def hyb0NF (x : Pos → ℕ) : PMF (MPK S Wb J Pos × Ciphertext S Wb J Pos) :=
  (PMF.uniformOfFintype (Wb → R)).bind fun Ab =>
  (PMF.uniformOfFintype (Wb → R)).bind fun B2b =>
  (PMF.pi fun _ : Fin S.τ => PMF.uniformOfFintype (Wb → Bool)).bind fun xs =>
  (PMF.uniformOfFintype (Fin S.τ → R)).bind fun B2g =>
  (PMF.uniformOfFintype (J → Matrix (Fin 2) (Col S.τ) R)).bind fun H =>
  (PMF.uniformOfFintype (Fin 2 → R)).bind fun d =>
  (encCoinsLaw S Wb J Pos χs χ χfl).bind fun r =>
  (PMF.uniformOfFintype (Pos → Col S.τ → R)).bind fun a =>
  (PMF.uniformOfFintype (Matrix (Fin 2) (Col S.τ) R)).bind fun A0 =>
  (PMF.uniformOfFintype (Pos → Dig S.τ → Matrix (Fin 2) (Col S.τ) R)).bind fun Ain =>
  (PMF.uniformOfFintype (Fin S.b → Dig S.τ → Matrix (Fin 2) (Col S.τ) R)).map fun Aaut =>
    mkV M w half ⟨Matrix.of ![Ab, B2b], fun c => S.D.g c - Ab ⬝ᵥ bv (xs c), B2g, H, d⟩ x r a A0 Ain
      Aaut

/-- The two rows of a uniform `2 × m̄` matrix are independent and uniform. -/
def rowsEquiv (Wb : Type) : (Wb → R) × (Wb → R) ≃ Matrix (Fin 2) Wb R where
  toFun p := Matrix.of ![p.1, p.2]
  invFun B := (B 0, B 1)
  left_inv _ := rfl
  right_inv B := by ext i j; fin_cases i <;> rfl

omit [DecidableEq R] [Nonempty Wb] [Fintype J] [DecidableEq J] [Fintype Pos] [DecidableEq Pos] in
theorem uniform_rows_bind {β : Type} (g : Matrix (Fin 2) Wb R → PMF β) :
    (PMF.uniformOfFintype (Matrix (Fin 2) Wb R)).bind g =
      (PMF.uniformOfFintype (Wb → R)).bind fun Ab =>
        (PMF.uniformOfFintype (Wb → R)).bind fun B2b => g (Matrix.of ![Ab, B2b]) := by
  rw [← bind_uniform_equiv (rowsEquiv Wb) g, uniform_prod_bind]
  rfl

omit [DecidableEq R] in
theorem hyb1u_eq_NF (x : Pos → ℕ) :
    hyb1u (Wb := Wb) M w half χs χ χfl x = hyb0NF M w half χs χ χfl x := by
  unfold hyb1u hyb0NF
  simp only [progLaw_eq]
  rw [uniform_rows_bind]
  refine congrArg (PMF.bind _) (funext fun Ab => congrArg (PMF.bind _) (funext fun B2b => ?_))
  unfold thLaw
  rw [Cslib.Probability.PMF.pi_map, PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun xs => ?_)
  simp only [Function.comp_apply]
  rw [uniform_prod_bind]
  refine congrArg (PMF.bind _) (funext fun B2g => ?_)
  rw [uniform_prod_bind]
  refine congrArg (PMF.bind _) (funext fun H => congrArg (PMF.bind _) (funext fun d => ?_))
  refine congrArg (PMF.bind _) (funext fun r => ?_)
  congr

omit [DecidableEq R] [Nonempty Wb] in
theorem hyb0_eq_NF (x : Pos → ℕ) :
    hyb0 (Wb := Wb) M w half χs χ χfl x = hyb0NF M w half χs χ χfl x := by
  unfold hyb0 hyb0NF setupLaw setupCoinsLaw encLaw
  simp only [PMF.bind_bind, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def,
    PMF.pure_bind, iidFam_bitLaw]
  refine congrArg (PMF.bind _) (funext fun Ab => ?_)
  simp only [uniform_sum_bind, PMF.map]
  rw [PMF.bind_comm]
  -- `d` before `a, A₀, A^in, A^aut`
  conv_lhs => enter [2, B2b, 2, xs, 2, B2g, 2, H, 2, a, 2, A0, 2, Ain]; rw [PMF.bind_comm]
  conv_lhs => enter [2, B2b, 2, xs, 2, B2g, 2, H, 2, a, 2, A0]; rw [PMF.bind_comm]
  conv_lhs => enter [2, B2b, 2, xs, 2, B2g, 2, H, 2, a]; rw [PMF.bind_comm]
  conv_lhs => enter [2, B2b, 2, xs, 2, B2g, 2, H]; rw [PMF.bind_comm]
  -- `Enc`'s coins before `a, A₀, A^in, A^aut`
  conv_lhs => enter [2, B2b, 2, xs, 2, B2g, 2, H, 2, d, 2, a, 2, A0, 2, Ain]; rw [PMF.bind_comm]
  conv_lhs => enter [2, B2b, 2, xs, 2, B2g, 2, H, 2, d, 2, a, 2, A0]; rw [PMF.bind_comm]
  conv_lhs => enter [2, B2b, 2, xs, 2, B2g, 2, H, 2, d, 2, a]; rw [PMF.bind_comm]
  conv_lhs => enter [2, B2b, 2, xs, 2, B2g, 2, H, 2, d]; rw [PMF.bind_comm]
  rfl

omit [DecidableEq R] in
/-- **H0 = H1u**: the real experiment is H1 with uniform values in place of the programming
hashes. -/
theorem hyb0_eq_hyb1u (x : Pos → ℕ) :
    hyb0 (Wb := Wb) M w half χs χ χfl x = hyb1u M w half χs χ χfl x :=
  (hyb0_eq_NF M w half χs χ χfl x).trans (hyb1u_eq_NF M w half χs χ χfl x).symm

/-- **H0 ≈ H1** (programming), within `|PrI| · √(|R|² 2^{−m̄})/2`. -/
theorem hybrid01_close (x : Pos → ℕ) :
    CloseTo (hyb0 (Wb := Wb) M w half χs χ χfl x) (hyb1 M w half χs χ χfl x) (delta1 S Wb Pos) := by
  rw [hyb0_eq_hyb1u]
  exact (hybrid1_close M w half χs χ χfl x).symm

end AdvancedEncryption.ExpLUT
