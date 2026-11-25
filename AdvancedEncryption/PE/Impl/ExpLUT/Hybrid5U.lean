import PE.Impl.ExpLUT.Hybrid5

/-!
# H5 is uniform

With uniform 3-row hash values, every component of H5's view is uniform and independent
(`hyb5_eq_final`): `a_t = u₀ + X^{w x_t} G⁽¹⁾` and the bottom row `u₁ − u₂ + e_t + X^{w x_t} G⁽²⁾` of
`C^in_t`; `A₀ = (u₀; u₁) + G` and `c₀ = u₂ + e₀`; `A^in_{t,d} = (u₀; u₁) + d G` and its encoding
`u₂ + e'`; `A^aut_{t,d} = σ_{g_t}(u₀; u₁) + d G` and its encoding `σ_{g_t}(u₂) + e'`; and `B`, `H_k`,
`d`, `b`, `h_k`, `c_m` are uniform already. So H5 is `(mpk, ct)` with independent uniform components
(`final5`), whatever `x` and the message.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix Cslib.Probability
open scoped ENNReal

variable {R : Type} [CommRing R] [Fintype R] [DecidableEq R] {S : Setting R} {Wb J Pos : Type}
  [Fintype Wb] [DecidableEq Wb] [Nonempty Wb] [Fintype J] [DecidableEq J] [Fintype Pos]
  [DecidableEq Pos] (M : HelperMap S J) (w : ℕ) (χfl : PMF R)

/-- The first two rows and the third row of a family of 3-row hash values. -/
def split3 (I : Type) : (I → Fin 3 → R) ≃ (I → Fin 2 → R) × (I → R) where
  toFun h := (fun i ρ => h i ρ.castSucc, fun i => h i 2)
  invFun p i := ![p.1 i 0, p.1 i 1, p.2 i]
  left_inv h := by funext i ρ; fin_cases ρ <;> rfl
  right_inv p := by
    obtain ⟨p, q⟩ := p
    simp only [Prod.mk.injEq]
    refine ⟨?_, rfl⟩
    funext i ρ; fin_cases ρ <;> rfl

theorem uniform_split3_bind {I β : Type} [Fintype I] [DecidableEq I]
    (K : (I → Fin 2 → R) → (I → R) → PMF β) :
    (PMF.uniformOfFintype (I → Fin 3 → R)).bind (fun h => K (split3 I h).1 (split3 I h).2) =
      (PMF.uniformOfFintype (I → Fin 2 → R)).bind fun p =>
        (PMF.uniformOfFintype (I → R)).bind fun q => K p q := by
  rw [bind_uniform_equiv (split3 I) (fun pq => K pq.1 pq.2), uniform_prod_bind]

/-- `(u₀, u₁ − u₂, u₂)`: a bijection of `R³`. -/
def zEquiv (I : Type) : (I → Fin 3 → R) ≃ (I → R) × (I → R) × (I → R) where
  toFun h := (fun i => h i 0, fun i => h i 1 - h i 2, fun i => h i 2)
  invFun p i := ![p.1 i, p.2.1 i + p.2.2 i, p.2.2 i]
  left_inv h := by funext i ρ; fin_cases ρ <;> simp
  right_inv p := by
    obtain ⟨p, q, r⟩ := p
    simp only [Prod.mk.injEq]
    refine ⟨rfl, ?_, rfl⟩
    funext i; simp

/-- The `Z_t` block: `(u₀, u₁ − u₂)` is uniform. -/
theorem uniform_zBlock_bind {I β : Type} [Fintype I] [DecidableEq I]
    (K : (I → R) → (I → R) → PMF β) :
    (PMF.uniformOfFintype (I → Fin 3 → R)).bind (fun h => K (fun i => h i 0) (fun i => h i 1 - h i 2)) =
      (PMF.uniformOfFintype (I → R)).bind fun p =>
        (PMF.uniformOfFintype (I → R)).bind fun q => K p q := by
  rw [show (fun h : I → Fin 3 → R => K (fun i => h i 0) (fun i => h i 1 - h i 2)) =
    fun h => (fun pqr : (I → R) × (I → R) × (I → R) => K pqr.1 pqr.2.1) (zEquiv I h) from rfl,
    bind_uniform_equiv (zEquiv I) (fun pqr => K pqr.1 pqr.2.1), uniform_prod_bind]
  refine congrArg (PMF.bind _) (funext fun p => ?_)
  rw [uniform_prod_bind]
  refine congrArg (PMF.bind _) (funext fun q => ?_)
  show (PMF.uniformOfFintype (I → R)).bind (fun _ => K p q) = K p q
  exact PMF.bind_const _ _

theorem σ_ki_kf (t : Fin S.b) (a : R) : S.E.σ (S.ki t) (S.E.σ (S.kf t) a) = a := by
  have hW : 2 ^ (t : ℕ) ≤ S.E.W := by
    rw [S.W_eq]; exact Nat.pow_le_pow_right (by norm_num) t.2.le
  rw [S.idx_add, show S.E.W - 2 ^ (t : ℕ) + 2 ^ (t : ℕ) = S.E.W by omega, Nat.mod_self, S.idx_zero]

theorem σ_kf_ki (t : Fin S.b) (a : R) : S.E.σ (S.kf t) (S.E.σ (S.ki t) a) = a := by
  have hW : 2 ^ (t : ℕ) ≤ S.E.W := by
    rw [S.W_eq]; exact Nat.pow_le_pow_right (by norm_num) t.2.le
  exact σ_idx_inv t hW _

/-- `σ_{g_t}` entrywise on a family of rows, a bijection. -/
def σRows (κ : Type) : (Fin S.b → κ → Col S.τ → R) ≃ (Fin S.b → κ → Col S.τ → R) where
  toFun A t d c := S.E.σ (S.kf t) (A t d c)
  invFun A t d c := S.E.σ (S.ki t) (A t d c)
  left_inv A := by
    funext t d c
    have hW : 2 ^ (t : ℕ) ≤ S.E.W := by
      rw [S.W_eq]; exact Nat.pow_le_pow_right (by norm_num) t.2.le
    simp only
    rw [S.idx_add, show S.E.W - 2 ^ (t : ℕ) + 2 ^ (t : ℕ) = S.E.W by omega, Nat.mod_self,
      S.idx_zero]
  right_inv A := by
    funext t d c
    have hW : 2 ^ (t : ℕ) ≤ S.E.W := by
      rw [S.W_eq]; exact Nat.pow_le_pow_right (by norm_num) t.2.le
    exact σ_idx_inv t hW _

/-- Currying the rows of a block. -/
def curry3 (ι κ : Type) : (ι × κ × Col S.τ → R) ≃ (ι → κ → Col S.τ → R) where
  toFun h t d c := h (t, d, c)
  invFun A i := A i.1 i.2.1 i.2.2
  left_inv _ := rfl
  right_inv _ := rfl

variable (S Pos) in
/-- The programmed components of H5: `a`, the bottom rows of the `C^in_t`, `A₀`, `c₀`, `A^in`,
their encodings, `A^aut`, their encodings. -/
abbrev Prog5 := (Pos → Col S.τ → R) × (Pos → Col S.τ → R) × Matrix (Fin 2) (Col S.τ) R ×
  (Col S.τ → R) × (Pos → Dig S.τ → Matrix (Fin 2) (Col S.τ) R) × (Pos → Dig S.τ → Col S.τ → R) ×
  (Fin S.b → Dig S.τ → Matrix (Fin 2) (Col S.τ) R) × (Fin S.b → Dig S.τ → Col S.τ → R)

instance fintypeProg5 : Fintype (Prog5 S Pos) :=
  @instFintypeProd _ _ inferInstance (@instFintypeProd _ _ inferInstance
    (@instFintypeProd _ _ inferInstance (@instFintypeProd _ _ inferInstance
      (@instFintypeProd _ _ inferInstance (@instFintypeProd _ _ inferInstance
        (@instFintypeProd _ _ inferInstance inferInstance))))))

instance nonemptyProg5 : Nonempty (Prog5 S Pos) := ⟨(0, 0, 0, 0, 0, 0, 0, 0)⟩

/-- The hash values block by block, without shifts (the third rows of the `Z_t` block last). -/
def blocks : (PrI S Pos → Fin 3 → R) ≃ Prog5 S Pos × (Pos × Col S.τ → R) where
  toFun h :=
    ((fun t c => h (.inl (t, c)) 0, fun t c => h (.inl (t, c)) 1 - h (.inl (t, c)) 2,
      Matrix.of fun ρ c => h (.inr (.inl c)) ρ.castSucc, fun c => h (.inr (.inl c)) 2,
      fun t d => Matrix.of fun ρ c => h (.inr (.inr (.inl (t, d, c)))) ρ.castSucc,
      fun t d c => h (.inr (.inr (.inl (t, d, c)))) 2,
      fun t d => Matrix.of fun ρ c => S.E.σ (S.kf t) (h (.inr (.inr (.inr (t, d, c)))) ρ.castSucc),
      fun t d c => S.E.σ (S.kf t) (h (.inr (.inr (.inr (t, d, c)))) 2)),
      fun i => h (.inl i) 2)
  invFun p := Sum.elim (fun i => ![p.1.1 i.1 i.2, p.1.2.1 i.1 i.2 + p.2 i, p.2 i])
    (Sum.elim (fun c => ![p.1.2.2.1 0 c, p.1.2.2.1 1 c, p.1.2.2.2.1 c])
      (Sum.elim (fun i => ![p.1.2.2.2.2.1 i.1 i.2.1 0 i.2.2, p.1.2.2.2.2.1 i.1 i.2.1 1 i.2.2,
          p.1.2.2.2.2.2.1 i.1 i.2.1 i.2.2])
        (fun i => ![(σFam (S := S)).symm p.1.2.2.2.2.2.2.1 i.1 i.2.1 0 i.2.2,
          (σFam (S := S)).symm p.1.2.2.2.2.2.2.1 i.1 i.2.1 1 i.2.2,
          (σRows (S := S) (Dig S.τ)).symm p.1.2.2.2.2.2.2.2 i.1 i.2.1 i.2.2])))
  left_inv h := by
    funext i ρ
    rcases i with ⟨t, c⟩ | c | ⟨t, d, c⟩ | ⟨t, d, c⟩ <;> fin_cases ρ <;>
      simp [σFam, σRows, σ_ki_kf]
  right_inv p := by
    obtain ⟨⟨a, cb, A0, c0, Ain, cin, Aaut, caut⟩, j⟩ := p
    simp only [Prod.mk.injEq]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rfl
    · funext t c; simp
    · ext ρ c; fin_cases ρ <;> rfl
    · rfl
    · funext t d; ext ρ c; fin_cases ρ <;> rfl
    · rfl
    · funext t d; ext ρ c; fin_cases ρ <;> simp [σFam, σ_kf_ki]
    · funext t d c; simp [σRows, σ_kf_ki]
    · rfl

/-- The digits of `C^in_t` times `G`, for the rows `a_t` and the bottom rows `cb_t`. -/
def dInC (a cb : Pos → Col S.τ → R) : Pos → Dig S.τ → Matrix (Fin 2) (Col S.τ) R :=
  fun t d => digits S (cinMat (a t) (cb t)) d • S.G

/-- The shifts of H5's programmed components: `X^{w x_t} G⁽¹⁾`, `e_t + X^{w x_t} G⁽²⁾`, `G`, `e₀`,
`d G` (digits of `C^in_t`), `e'`, `d G` (digits of `C_{g_t}`), `e'`. -/
def shear (x : Pos → ℕ) (H : J → Matrix (Fin 2) (Col S.τ) R) (h : J → Col S.τ → R)
    (fl : FloodV S Pos) : Prog5 S Pos ≃ Prog5 S Pos where
  toFun p :=
    let a := p.1 + fun t c => S.E.X ^ (w * x t) * S.G 0 c
    let cb := p.2.1 + fun t c => fl.2.1 t c + S.E.X ^ (w * x t) * S.G 1 c
    (a, cb, p.2.2.1 + S.G, p.2.2.2.1 + fl.2.2.2, p.2.2.2.2.1 + dInC a cb, p.2.2.2.2.2.1 + fl.2.2.1,
      p.2.2.2.2.2.2.1 + dAut M H h, p.2.2.2.2.2.2.2 + fl.1)
  invFun p :=
    (p.1 - fun t c => S.E.X ^ (w * x t) * S.G 0 c,
      p.2.1 - fun t c => fl.2.1 t c + S.E.X ^ (w * x t) * S.G 1 c, p.2.2.1 - S.G,
      p.2.2.2.1 - fl.2.2.2, p.2.2.2.2.1 - dInC p.1 p.2.1, p.2.2.2.2.2.1 - fl.2.2.1,
      p.2.2.2.2.2.2.1 - dAut M H h, p.2.2.2.2.2.2.2 - fl.1)
  left_inv p := by
    obtain ⟨a, cb, A0, c0, Ain, cin, Aaut, caut⟩ := p
    simp
  right_inv p := by
    obtain ⟨a, cb, A0, c0, Ain, cin, Aaut, caut⟩ := p
    simp

/-- `(mpk, ct)` from the uniform components. -/
def mkV5 (P : PubData S Wb J) (b : BCol Wb S.τ → R) (h : J → Col S.τ → R) (cm : R)
    (p : Prog5 S Pos) : MPK S Wb J Pos × Ciphertext S Wb J Pos :=
  (mpkOf P p.1 p.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.2.1,
    ⟨b, h, p.2.2.2.2.2.2.2, p.2.1, p.2.2.2.2.2.1, p.2.2.2.1, cm⟩)

/-- **H5's view from its components.** -/
theorem view5_eq (x : Pos → ℕ) (B3 : Matrix (Fin 3) Wb R) (c : Mid5 S J Pos)
    (h3 : PrI S Pos → Fin 3 → R) :
    view5 M w x B3 c h3 =
      mkV5 (pubOf (Matrix.of ![B3 0, B3 1]) c.1 c.2.1) (Sum.elim (B3 2) c.2.2.1) c.2.2.2.1
        c.2.2.2.2.1 (shear M w x c.2.1.2.1 c.2.2.2.1 c.2.2.2.2.2 (blocks h3).1) := by
  have hcb : cbH w x (hp3 h3) (hb3 h3) c.2.2.2.2.2 =
      (shear M w x c.2.1.2.1 c.2.2.2.1 c.2.2.2.2.2 (blocks h3).1).2.1 := by
    funext t c
    simp only [cbH, shear, blocks, hp3, hb3, Equiv.coe_fn_mk, Pi.add_apply]
    rw [show (Fin.castSucc (1 : Fin 2) : Fin 3) = 1 from rfl]
    ring
  unfold view5 viewH mkV5 mpkOf
  rw [hcb]
  congr 1

/-- **For fixed other coins, H5's view is `mkV5` of independent uniform components.** -/
theorem inner5 (x : Pos → ℕ) (B3 : Matrix (Fin 3) Wb R) (c : Mid5 S J Pos) :
    (PMF.pi fun _ : PrI S Pos => PMF.uniformOfFintype (Fin 3 → R)).bind
        (fun h3 => PMF.pure (view5 M w x B3 c h3)) =
      (PMF.uniformOfFintype (Prog5 S Pos)).map
        (mkV5 (pubOf (Matrix.of ![B3 0, B3 1]) c.1 c.2.1) (Sum.elim (B3 2) c.2.2.1) c.2.2.2.1
          c.2.2.2.2.1) := by
  rw [Cslib.Probability.PMF.pi_uniformOfFintype]
  change PMF.map (fun h3 => view5 M w x B3 c h3) _ = _
  simp only [view5_eq]
  rw [show (fun h3 => mkV5 (pubOf (Matrix.of ![B3 0, B3 1]) c.1 c.2.1) (Sum.elim (B3 2) c.2.2.1)
      c.2.2.2.1 c.2.2.2.2.1 (shear M w x c.2.1.2.1 c.2.2.2.1 c.2.2.2.2.2 (blocks h3).1)) =
      (mkV5 (pubOf (Matrix.of ![B3 0, B3 1]) c.1 c.2.1) (Sum.elim (B3 2) c.2.2.1) c.2.2.2.1
        c.2.2.2.2.1) ∘ (shear M w x c.2.1.2.1 c.2.2.2.1 c.2.2.2.2.2) ∘ (fun h3 => (blocks h3).1)
      from rfl, ← PMF.map_comp, ← PMF.map_comp,
    uniform_map_of_equiv_fst blocks _ fun _ => rfl, uniform_map_equiv]

theorem uniform_prog5_map {β : Type} (F : Prog5 S Pos → β) :
    (PMF.uniformOfFintype (Prog5 S Pos)).map F =
      (PMF.uniformOfFintype (Pos → Col S.τ → R)).bind fun a =>
      (PMF.uniformOfFintype (Pos → Col S.τ → R)).bind fun cb =>
      (PMF.uniformOfFintype (Matrix (Fin 2) (Col S.τ) R)).bind fun A0 =>
      (PMF.uniformOfFintype (Col S.τ → R)).bind fun c0 =>
      (PMF.uniformOfFintype (Pos → Dig S.τ → Matrix (Fin 2) (Col S.τ) R)).bind fun Ain =>
      (PMF.uniformOfFintype (Pos → Dig S.τ → Col S.τ → R)).bind fun cin =>
      (PMF.uniformOfFintype (Fin S.b → Dig S.τ → Matrix (Fin 2) (Col S.τ) R)).bind fun Aaut =>
      (PMF.uniformOfFintype (Fin S.b → Dig S.τ → Col S.τ → R)).map fun caut =>
        F (a, cb, A0, c0, Ain, cin, Aaut, caut) := by
  simp only [PMF.map, uniform_prod_bind]
  rfl

/-- **The uniform public key** (with `B⁽¹⁾` uniform). -/
noncomputable def mpkU : PMF (MPK S Wb J Pos) :=
  (PMF.uniformOfFintype (Matrix (Fin 2) Wb R)).bind fun Bb =>
  (PMF.uniformOfFintype (Fin S.τ → R)).bind fun Bg1 =>
  (PMF.uniformOfFintype (RestPub S J)).bind fun rp =>
  (PMF.uniformOfFintype (Pos → Col S.τ → R)).bind fun a =>
  (PMF.uniformOfFintype (Matrix (Fin 2) (Col S.τ) R)).bind fun A0 =>
  (PMF.uniformOfFintype (Pos → Dig S.τ → Matrix (Fin 2) (Col S.τ) R)).bind fun Ain =>
  (PMF.uniformOfFintype (Fin S.b → Dig S.τ → Matrix (Fin 2) (Col S.τ) R)).map fun Aaut =>
    mpkOf (pubOf Bb Bg1 rp) a A0 Ain Aaut

variable (S Wb J Pos) in
/-- **The uniform ciphertext**: the simulator's law. -/
noncomputable def ctU : PMF (Ciphertext S Wb J Pos) :=
  (PMF.uniformOfFintype (BCol Wb S.τ → R)).bind fun b =>
  (PMF.uniformOfFintype (J → Col S.τ → R)).bind fun h =>
  (PMF.uniformOfFintype R).bind fun cm =>
  (PMF.uniformOfFintype (Pos → Col S.τ → R)).bind fun cb =>
  (PMF.uniformOfFintype (Col S.τ → R)).bind fun c0 =>
  (PMF.uniformOfFintype (Pos → Dig S.τ → Col S.τ → R)).bind fun cin =>
  (PMF.uniformOfFintype (Fin S.b → Dig S.τ → Col S.τ → R)).map fun caut =>
    ⟨b, h, caut, cb, cin, c0, cm⟩

/-- **The final view**: uniform public key, uniform ciphertext. -/
noncomputable def final5 : PMF (MPK S Wb J Pos × Ciphertext S Wb J Pos) :=
  (mpkU (S := S) (Wb := Wb) (J := J) (Pos := Pos)).bind fun mpk =>
    (ctU S Wb J Pos).map fun ct => (mpk, ct)

/-- **H5 is the final view**, for every attribute `x`. -/
theorem hyb5_eq_final (x : Pos → ℕ) : hyb5 (Wb := Wb) M w χfl x = final5 := by
  unfold hyb5 mid5Law
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, inner5, PMF.bind_const]
  unfold final5 mpkU ctU
  simp only [PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def,
    uniform_prog5_map]
  conv_rhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6]; rw [uniform_sum_bind]
  conv_rhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5]; rw [PMF.bind_comm]
  conv_rhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4]; rw [PMF.bind_comm]
  conv_rhs => enter [2, y0, 2, y1, 2, y2, 2, y3]; rw [PMF.bind_comm]
  conv_rhs => enter [2, y0, 2, y1, 2, y2]; rw [PMF.bind_comm]
  conv_rhs => enter [2, y0, 2, y1]; rw [PMF.bind_comm]
  conv_rhs => enter [2, y0]; rw [PMF.bind_comm]
  rw [uniform_rows3_bind]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6, 2, y7, 2, y8]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6, 2, y7, 2, y8, 2, y9, 2, y10]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6, 2, y7]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6, 2, y7, 2, y8, 2, y9]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6, 2, y7, 2, y8]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6, 2, y7]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5, 2, y6]; rw [PMF.bind_comm]
  conv_lhs => enter [2, y0, 2, y1, 2, y2, 2, y3, 2, y4, 2, y5]; rw [PMF.bind_comm]
  rfl

end AdvancedEncryption.ExpLUT
