import PE.Impl.ExpLUT.Basic

/-!
# The primitive operations of §4.2: Add, SMul, Mul, Aut

Each operation is a pair of a public-key algorithm (`…PK`, on public matrices) and a ciphertext
algorithm (`…CT`, on encodings), with its **exact** output equation: the output error (`…Err`) is
an explicit function of the input errors. The public matrices never depend on the encoded values or
on the ciphertext.

* **Add** (`encodes_add`, `PE.Impl.ExpLUT.Basic`): `c₁ + c₂ : ⟦(μ₁ + μ₂) s⟧^{A₁ + A₂}`.
* **SMul_α** (`smulPK`, `smulCT`, `encodes_smul`): `c G⁻¹(αG) : ⟦α μ s⟧^{A G⁻¹(αG)}`.
* **Mul** (asymmetric multiplication, eq. (1)): for a gadget ciphertext `C : GC_{s'}(z)` with
  binary digits `d_{r,j,i}` (`digits`) and the RHS data `c_{r,j,i} : ⟦d_{r,j,i} s'⟧^{A_{r,j,i}}_{s'}`,
  `c'_j = Σ_{r,i} (c_{r,j,i} G⁻¹(A) + d_{r,j,i} c)_{(r,i)}` (`mulCT`; the factor `G⁻¹(2^i 1_r^T)` of
  the paper selects the column `(r, i)`) and `A'_j = Σ_{r,i} (A_{r,j,i} G⁻¹(A))_{(r,i)}` (`mulPK`).
  `encodes_mul`: from `c : ⟦μ s'⟧^A_{s'}`, `Mul(c, RHS(C)) : ⟦μ z⟧^{A'}_{s'}` with the error
  `Σ_{r,i} (e_{r,j,i} G⁻¹(A) + d_{r,j,i} e)_{(r,i)} − μ f_j` (`mulErr`).
* **Aut_k** (eq. (2)): `C_k = σ_k(H_{k'}) − [0; σ_k(h_{k'})]` (`gcAut`) for `k k' ≡ 1`, a gadget
  ciphertext of `s` under `s_k` (`isGC_gcAut`); `r_k = Mul(σ_k(c), RHS_{s_k}(C_k))` and
  `Aut_k(c) = h_k G⁻¹(A'_k) + r_k` (`autCT`, `autPK`, `autErr`). `encodes_aut`: from
  `c : ⟦μ s⟧^A_s`, `Aut_k(c) : ⟦σ_k(μ) s⟧^{H_k G⁻¹(A'_k)}_s`.
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix

variable {R : Type*} [CommRing R] (S : Setting R)

/-! ### SMul -/

/-- `EvalPK` of `SMul_α`: `A G⁻¹(αG)`. -/
def smulPK (α : R) (A : Matrix (Fin 2) (Col S.τ) R) : Matrix (Fin 2) (Col S.τ) R :=
  A * S.ginv (α • S.G)

/-- `EvalCT` of `SMul_α`: `c G⁻¹(αG)`. -/
def smulCT (α : R) (c : Col S.τ → R) : Col S.τ → R := c ᵥ* S.ginv (α • S.G)

variable {S}

/-- **SMul**: `c G⁻¹(αG) : ⟨α x G⟩^{A G⁻¹(αG)}_s` with error `e G⁻¹(αG)`. -/
theorem encodes_smul (α : R) {s : Fin 2 → R} {A : Matrix (Fin 2) (Col S.τ) R} {x : Fin 2 → R}
    {e c : Col S.τ → R} (h : Encodes S s A x e c) :
    Encodes S s (smulPK S α A) (α • x) (smulCT S α e) (smulCT S α c) := by
  unfold smulCT smulPK Encodes
  rw [encodes_mul_right h, G_mul_ginv, Matrix.vecMul_smul, Matrix.smul_vecMul]

/-! ### Mul -/

variable (S)

/-- The digits `d_{r,j,i}` of the entries of `C`: `C_{r,j} = Σ_i g_i d_{r,j,i}`. -/
def digits (C : Matrix (Fin 2) (Col S.τ) R) (t : Dig S.τ) : R := S.D.d (C t.1 t.2.1) t.2.2

/-- `EvalPK` of `Mul`: `A'_j = Σ_{(r,i)} (A_{r,j,i} G⁻¹(A))_{·,(r,i)}`. -/
def mulPK (A : Matrix (Fin 2) (Col S.τ) R) (Ad : Dig S.τ → Matrix (Fin 2) (Col S.τ) R) :
    Matrix (Fin 2) (Col S.τ) R :=
  Matrix.of fun a j => ∑ ri : Col S.τ, (Ad (ri.1, j, ri.2) * S.ginv A) a ri

/-- `EvalCT` of `Mul`: `c'_j = Σ_{(r,i)} (c_{r,j,i} G⁻¹(A) + d_{r,j,i} c)_{(r,i)}`. -/
def mulCT (A : Matrix (Fin 2) (Col S.τ) R) (C : Matrix (Fin 2) (Col S.τ) R)
    (cd : Dig S.τ → Col S.τ → R) (c : Col S.τ → R) : Col S.τ → R :=
  fun j => ∑ ri : Col S.τ, ((cd (ri.1, j, ri.2) ᵥ* S.ginv A) ri + digits S C (ri.1, j, ri.2) * c ri)

/-- The error of `Mul`: `Σ_{(r,i)} (e_{r,j,i} G⁻¹(A) + d_{r,j,i} e)_{(r,i)} − μ f_j`. -/
def mulErr (A : Matrix (Fin 2) (Col S.τ) R) (C : Matrix (Fin 2) (Col S.τ) R) (μ : R)
    (f : Col S.τ → R) (ed : Dig S.τ → Col S.τ → R) (e : Col S.τ → R) : Col S.τ → R :=
  fun j => mulCT S A C ed e j - μ * f j

variable {S}

/-- The digits reassemble `s C`: `Σ_{(r,i)} d_{r,j,i} (x G)_{(r,i)} = (x C)_j`. -/
theorem sum_digits_vecMul_G (C : Matrix (Fin 2) (Col S.τ) R) (x : Fin 2 → R) (j : Col S.τ) :
    ∑ ri : Col S.τ, digits S C (ri.1, j, ri.2) * (x ᵥ* S.G) ri = (x ᵥ* C) j := by
  simp only [vecMul_G_apply, digits, Fintype.sum_prod_type]
  simp only [Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl fun r _ => ?_
  conv_rhs => rw [← S.D.recompose (C r j)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem mulCT_add_left (A C : Matrix (Fin 2) (Col S.τ) R) (cd cd' : Dig S.τ → Col S.τ → R)
    (c c' : Col S.τ → R) :
    mulCT S A C (cd + cd') (c + c') = mulCT S A C cd c + mulCT S A C cd' c' := by
  funext j
  simp only [mulCT, Pi.add_apply, Matrix.add_vecMul, mul_add, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **Mul** (eq. (1)): from `c : ⟨μ s' G⟩^A_{s'}`, a gadget ciphertext `C : GC_{s'}⟨z G + f⟩` and
its RHS data `c_t : ⟨d_t s' G⟩^{A_t}_{s'}`, `Mul(c, RHS(C)) : ⟨μ z G⟩^{A'}_{s'}`, exactly. -/
theorem encodes_mul {s' : Fin 2 → R} {A C : Matrix (Fin 2) (Col S.τ) R} {μ : R} {z : Fin 2 → R}
    {f e c : Col S.τ → R} {Ad : Dig S.τ → Matrix (Fin 2) (Col S.τ) R} {ed cd : Dig S.τ → Col S.τ → R}
    (hc : Encodes S s' A (μ • s') e c) (hC : IsGC S s' C z f)
    (hd : ∀ t, Encodes S s' (Ad t) (digits S C t • s') (ed t) (cd t)) :
    Encodes S s' (mulPK S A Ad) (μ • z) (mulErr S A C μ f ed e) (mulCT S A C cd c) := by
  unfold Encodes at hc hd ⊢
  funext j
  have hsC := congrFun hC j
  simp only [Pi.add_apply] at hsC
  have key : ∀ ri : Col S.τ, (cd (ri.1, j, ri.2) ᵥ* S.ginv A) ri + digits S C (ri.1, j, ri.2) * c ri =
      (s' ᵥ* (Ad (ri.1, j, ri.2) * S.ginv A)) ri -
        μ * (digits S C (ri.1, j, ri.2) * (s' ᵥ* S.G) ri) +
        ((ed (ri.1, j, ri.2) ᵥ* S.ginv A) ri + digits S C (ri.1, j, ri.2) * e ri) := by
    intro ri
    rw [hd, hc, Matrix.add_vecMul, Matrix.sub_vecMul, vecMul_G_ginv, Matrix.vecMul_vecMul]
    simp only [Pi.add_apply, Pi.sub_apply, Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [mulCT, mulErr, key, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_digits_vecMul_G, hsC, Pi.add_apply, Pi.sub_apply, Matrix.smul_vecMul, Pi.smul_apply,
    smul_eq_mul]
  have hA : (s' ᵥ* mulPK S A Ad) j = ∑ ri : Col S.τ, (s' ᵥ* (Ad (ri.1, j, ri.2) * S.ginv A)) ri := by
    simp only [mulPK, Matrix.vecMul, dotProduct, Matrix.of_apply, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hA]
  ring

/-! ### Aut -/

variable (S)

/-- `σ_k` on a matrix, entrywise. -/
abbrev autMat (k : ℕ) (A : Matrix (Fin 2) (Col S.τ) R) : Matrix (Fin 2) (Col S.τ) R :=
  A.map (S.E.σ k)

/-- `σ_k` on a row, entrywise. -/
abbrev autRow (k : ℕ) (c : Col S.τ → R) : Col S.τ → R := S.E.σ k ∘ c

/-- The gadget ciphertext of eq. (2): `C_k = σ_k(H_{k'}) − [0; σ_k(h_{k'})]`, from the public
`H_{k'}` and the helper `h_{k'}`. -/
def gcAut (k : ℕ) (Hk' : Matrix (Fin 2) (Col S.τ) R) (hk' : Col S.τ → R) :
    Matrix (Fin 2) (Col S.τ) R :=
  Matrix.of fun a j => S.E.σ k (Hk' a j) - if a = 1 then S.E.σ k (hk' j) else 0

/-- `A'_k = EvalPK_Mul(σ_k(A), {A^aut_{k,t}})`, the public matrix of `r_k`. -/
def autMid (k : ℕ) (Aaut : Dig S.τ → Matrix (Fin 2) (Col S.τ) R) (A : Matrix (Fin 2) (Col S.τ) R) :
    Matrix (Fin 2) (Col S.τ) R :=
  mulPK S (autMat S k A) Aaut

/-- `EvalPK` of `Aut_k`: `H_k G⁻¹(A'_k)`. -/
def autPK (k : ℕ) (Hk : Matrix (Fin 2) (Col S.τ) R) (Aaut : Dig S.τ → Matrix (Fin 2) (Col S.τ) R)
    (A : Matrix (Fin 2) (Col S.τ) R) : Matrix (Fin 2) (Col S.τ) R :=
  Hk * S.ginv (autMid S k Aaut A)

/-- `EvalCT` of `Aut_k`: `h_k G⁻¹(A'_k) + Mul(σ_k(c), RHS_{s_k}(C_k))`. -/
def autCT (k : ℕ) (Hk' : Matrix (Fin 2) (Col S.τ) R) (Aaut : Dig S.τ → Matrix (Fin 2) (Col S.τ) R)
    (A : Matrix (Fin 2) (Col S.τ) R) (hk hk' : Col S.τ → R) (cd : Dig S.τ → Col S.τ → R)
    (c : Col S.τ → R) : Col S.τ → R :=
  hk ᵥ* S.ginv (autMid S k Aaut A) + mulCT S (autMat S k A) (gcAut S k Hk' hk') cd (autRow S k c)

/-- The error of `Aut_k`: `e_k G⁻¹(A'_k) + mulErr(σ_k(e), −σ_k(e_{k'}))`, for the payload `μ`. -/
def autErr (k : ℕ) (Hk' : Matrix (Fin 2) (Col S.τ) R) (Aaut : Dig S.τ → Matrix (Fin 2) (Col S.τ) R)
    (A : Matrix (Fin 2) (Col S.τ) R) (hk' : Col S.τ → R) (μ : R) (ek ek' : Col S.τ → R)
    (ed : Dig S.τ → Col S.τ → R) (e : Col S.τ → R) : Col S.τ → R :=
  ek ᵥ* S.ginv (autMid S k Aaut A) +
    mulErr S (autMat S k A) (gcAut S k Hk' hk') (S.E.σ k μ) (-autRow S k ek') ed (autRow S k e)

variable {S}

/-- **`C_k` is a gadget ciphertext of `s` under `s_k`** (eq. (2)): if `h_{k'} : ⟨s_{k'} G⟩^{H_{k'}}_s`
and `σ_k σ_{k'} = id`, then `s_k C_k = s G − σ_k(e_{k'})`. -/
theorem isGC_gcAut (k k' : ℕ) (hkk' : ∀ a, S.E.σ k (S.E.σ k' a) = a) (sb : R)
    {Hk' : Matrix (Fin 2) (Col S.τ) R} {ek' hk' : Col S.τ → R}
    (hh : Encodes S (sec sb) Hk' (sec (S.E.σ k' sb)) ek' hk') :
    IsGC S (sec (S.E.σ k sb)) (gcAut S k Hk' hk') (sec sb) (-autRow S k ek') := by
  have hσ := encodes_σ k hh
  rw [σ_comp_sec, σ_comp_sec, hkk'] at hσ
  unfold IsGC
  funext j
  have hj := congrFun hσ j
  simp only [autRow] at hj ⊢
  simp only [Function.comp_apply] at hj
  have hv : (sec (S.E.σ k sb) ᵥ* gcAut S k Hk' hk') j =
      (sec (S.E.σ k sb) ᵥ* Hk'.map (S.E.σ k)) j - S.E.σ k (hk' j) := by
    simp [Matrix.vecMul, dotProduct, gcAut, Fin.sum_univ_two, sec, mul_sub]
  rw [hv, hj]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.comp_apply]
  ring

/-- **Aut_k**: from `c : ⟨μ s G⟩^A_s`, helpers `h_k : ⟨s_k G⟩^{H_k}_s`, `h_{k'} : ⟨s_{k'} G⟩^{H_{k'}}_s`
with `k k' ≡ 1`, and the RHS data of `C_k` under `s_k`, `Aut_k(c) : ⟨σ_k(μ) s G⟩^{H_k G⁻¹(A'_k)}_s`,
exactly. -/
theorem encodes_aut (k k' : ℕ) (hkk' : ∀ a, S.E.σ k (S.E.σ k' a) = a) (sb : R)
    {A Hk Hk' : Matrix (Fin 2) (Col S.τ) R} {μ : R} {e c ek ek' hk hk' : Col S.τ → R}
    {Aaut : Dig S.τ → Matrix (Fin 2) (Col S.τ) R} {ed cd : Dig S.τ → Col S.τ → R}
    (hc : Encodes S (sec sb) A (μ • sec sb) e c)
    (hh : Encodes S (sec sb) Hk (sec (S.E.σ k sb)) ek hk)
    (hh' : Encodes S (sec sb) Hk' (sec (S.E.σ k' sb)) ek' hk')
    (hd : ∀ t, Encodes S (sec (S.E.σ k sb)) (Aaut t)
      (digits S (gcAut S k Hk' hk') t • sec (S.E.σ k sb)) (ed t) (cd t)) :
    Encodes S (sec sb) (autPK S k Hk Aaut A) (S.E.σ k μ • sec sb)
      (autErr S k Hk' Aaut A hk' μ ek ek' ed e) (autCT S k Hk' Aaut A hk hk' cd c) := by
  have hσ := encodes_σ k hc
  rw [σ_comp_sec] at hσ
  have hx : S.E.σ k ∘ (μ • sec sb) = S.E.σ k μ • sec (S.E.σ k sb) := by
    rw [← σ_comp_sec]; funext i; simp
  rw [hx] at hσ
  have hr := encodes_mul hσ (isGC_gcAut k k' hkk' sb hh') hd
  exact encodes_maskSwitch hh hr

end AdvancedEncryption.ExpLUT
