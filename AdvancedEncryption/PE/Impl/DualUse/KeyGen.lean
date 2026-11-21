import PE.Impl.DualUse.Scheme
import SigabaNeo.Lib.Lattices.BoxSampler

/-!
# Key generation by box rejection, real and simulated

A key for `f` solves `B₀ k₀ + B₁ k₁ + B_f̂ k₂ = p`. It is drawn by one try of box rejection
(`SigabaNeo.Lattices.boxSample`) with the decomposition `z = k₂` attached to the columns of `B_f̂`
and `(k₀, k₁)` in a small box:

* **real** (`realTrap`): `B₁ T = G̲` (`T ∈ R^{Wt × W}`) gives the trapdoor `T · G̲⁻¹(B_f̂ − G̲)` of
  `[B₁ | B_f̂] = [B₁ | B₁ T G̲⁻¹(B_f̂ − G̲) + G̲]`;
* **simulated** (`simTrap`, BTVW17 `KeyGen*`): when `B_f̂ = B₀ W + G̲` (`keyMatrix_sim` with
  `f(x) = 1`), `W` is a trapdoor of `[B₀ | B_f̂]`.

Both have the same public map, so the two laws are equal (`keyLaw_real_eq_sim`): the simulation of
keys is exact. Every key output is valid (`valid_of_mem_support`).
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW

variable {R : Type*} [CommRing R] {k : ℕ} {S : Setting R k} {Wd Wt : Type*} [Fintype Wd]
  [Fintype Wt] [DecidableEq R]

/-- The short part of a key: against `B₀` and `B₁`. -/
abbrev KeyShort (Wd Wt : Type*) (R : Type*) := (Wd → R) × (Wt → R)

/-- The public map on the short part: `(k₀, k₁) ↦ B₀ k₀ + B₁ k₁`. -/
def shortMap (mpk : MPK S Wd Wt) : KeyShort Wd Wt R →+ R where
  toFun x := ∑ c, mpk.B₀ 0 c * x.1 c + ∑ c, mpk.B₁ 0 c * x.2 c
  map_zero' := by simp
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring

/-- The gadget part: `z ↦ G̲ z`. -/
def gadgetMap (z : Col k → R) : R := ∑ c, S.Γ₁.G 0 c * z c

/-- The real trapdoor: `z ↦ (0, T · G̲⁻¹(B_f̂ − G̲) · z)`. -/
def realTrap (Tm : Matrix Wt (Col k) R) (Bf : Matrix (Fin 1) (Col k) R) (z : Col k → R) :
    KeyShort Wd Wt R :=
  (0, (Tm * S.Γ₁.ginv (Bf - S.Γ₁.G)) *ᵥ z)

/-- The simulated trapdoor: `z ↦ (W z, 0)`. -/
def simTrap (W : Matrix Wd (Col k) R) (z : Col k → R) : KeyShort Wd Wt R := (W *ᵥ z, 0)

omit [DecidableEq R] in
theorem shortMap_realTrap (mpk : MPK S Wd Wt) (Tm : Matrix Wt (Col k) R)
    (hT : mpk.B₁ * Tm = S.Γ₁.G) (Bf : Matrix (Fin 1) (Col k) R) (z : Col k → R) :
    shortMap mpk (realTrap (Wd := Wd) (Wt := Wt) (S := S) Tm Bf z) = ((Bf - S.Γ₁.G) *ᵥ z) 0 := by
  have h : mpk.B₁ * (Tm * S.Γ₁.ginv (Bf - S.Γ₁.G)) = Bf - S.Γ₁.G := by
    rw [← Matrix.mul_assoc, hT, S.Γ₁.mul_ginv]
  have h2 := congrArg (fun M => (M *ᵥ z) 0) h
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply] at h2
  simp only [shortMap, realTrap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add, Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rw [← h2]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

omit [DecidableEq R] in
theorem shortMap_simTrap (mpk : MPK S Wd Wt) (W : Matrix Wd (Col k) R) (Bf : Matrix (Fin 1) (Col k) R)
    (hBf : Bf = mpk.B₀ * W + S.Γ₁.G) (z : Col k → R) :
    shortMap mpk (simTrap (Wt := Wt) W z) = ((Bf - S.Γ₁.G) *ᵥ z) 0 := by
  rw [hBf, add_sub_cancel_right]
  simp only [shortMap, simTrap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

/-- The key of an output: `(k₀, k₁)` and `k₂ = z`, or the zero key on abort. -/
def keyOfOutput : Option (KeyShort Wd Wt R × (Col k → R)) → SecretKey Wd Wt (R := R) (k := k)
  | some (x, z) => ⟨Matrix.of fun c _ => x.1 c, Matrix.of fun c _ => x.2 c, Matrix.of fun c _ => z c⟩
  | none => ⟨0, 0, 0⟩

variable (Big Small : Finset (KeyShort Wd Wt R)) (hBig : Big.Nonempty) (dec : R → (Col k → R))

/-- The law of a key with the trapdoor `T`, for the public row `B_f̂`. -/
noncomputable def keyLaw (mpk : MPK S Wd Wt) (T : (Col k → R) → KeyShort Wd Wt R) :
    PMF (Option (KeyShort Wd Wt R × (Col k → R))) :=
  boxSample Big hBig Small (shortMap mpk) dec T mpk.p

/-- **Exact simulation of keys** (BTVW17 `KeyGen*`): when `B_f̂ = B₀ W + G̲`, the key law with the
real trapdoor equals the one with `W`, provided the big box covers both. -/
theorem keyLaw_real_eq_sim (hdec : ∀ u, gadgetMap (S := S) (dec u) = u) (mpk : MPK S Wd Wt)
    (Tm : Matrix Wt (Col k) R) (hT : mpk.B₁ * Tm = S.Γ₁.G) (W : Matrix Wd (Col k) R)
    (Bf : Matrix (Fin 1) (Col k) R) (hBf : Bf = mpk.B₀ * W + S.Γ₁.G)
    (hcov : ∀ x ∈ Small, ∀ y, x + realTrap (Wd := Wd) (Wt := Wt) (S := S) Tm Bf (dec y) ∈ Big)
    (hcov' : ∀ x ∈ Small, ∀ y, x + simTrap (Wt := Wt) W (dec y) ∈ Big) :
    keyLaw Big Small hBig dec mpk (realTrap (S := S) Tm Bf) = keyLaw Big Small hBig dec mpk (simTrap W) :=
  boxSample_eq Big hBig Small (shortMap mpk) (gadgetMap (S := S)) dec hdec _ _ mpk.p hcov hcov'
    fun z => by rw [shortMap_realTrap mpk Tm hT, shortMap_simTrap mpk W Bf hBf]

omit [DecidableEq R] in
theorem gadgetMap_eq (z : Col k → R) : gadgetMap (S := S) z = (S.Γ₁.G *ᵥ z) 0 := rfl

/-- **Keys are valid**: every key output with a trapdoor `T` of `B_f̂` (that is,
`B₀ T₀ z + B₁ T₁ z + G̲ z = B_f̂ z`) satisfies `B₀ k₀ + B₁ k₁ + B_f̂ k₂ = p`, unless the try aborts. -/
theorem valid_of_mem_support (hdec : ∀ u, gadgetMap (S := S) (dec u) = u) (mpk : MPK S Wd Wt)
    (T : (Col k → R) → KeyShort Wd Wt R) (Bf : Matrix (Fin 1) (Col k) R)
    (hT : ∀ z, shortMap mpk (T z) + gadgetMap (S := S) z = (Bf *ᵥ z) 0)
    (hcov : ∀ x ∈ Small, ∀ y, x + T (dec y) ∈ Big)
    (o : Option (KeyShort Wd Wt R × (Col k → R))) (ho : o ∈ (keyLaw Big Small hBig dec mpk T).support)
    (x : KeyShort Wd Wt R × (Col k → R)) (hox : o = some x) :
    mpk.B₀ * (keyOfOutput o).k₀ + mpk.B₁ * (keyOfOutput o).k₁ + Bf * (keyOfOutput o).k₂ =
      scalar mpk.p := by
  subst hox
  have hpos := (PMF.mem_support_iff _ _).mp ho
  rw [keyLaw, boxSample_some Big hBig Small (shortMap mpk) (gadgetMap (S := S)) dec hdec T mpk.p
    hcov] at hpos
  split_ifs at hpos with ht
  · obtain ⟨-, -, hu⟩ := ht
    have hu' : shortMap mpk x.1 + (Bf *ᵥ x.2) 0 = mpk.p := by
      rw [← hT]; simpa only [add_assoc] using hu
    ext a b
    fin_cases a; fin_cases b
    simp only [shortMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hu'
    simp [keyOfOutput, Matrix.mul_apply, RingBTVW.scalar, Matrix.mulVec, dotProduct, ← hu']
  · exact absurd rfl hpos

/-- A trapdoor of the public row `B_f̂` covered by the boxes. -/
def GoodTrap (dec : R → (Col k → R)) (mpk : MPK S Wd Wt)
    (Bf : Matrix (Fin 1) (Col k) R) (T : (Col k → R) → KeyShort Wd Wt R) : Prop :=
  (∀ z, shortMap mpk (T z) + gadgetMap (S := S) z = (Bf *ᵥ z) 0) ∧
    ∀ x ∈ Small, ∀ y, x + T (dec y) ∈ Big

open Classical in
/-- **The ideal key law** of the public row `B_f̂`: the law of one try with any covered trapdoor
(and an abort if there is none). It depends on public data only. -/
noncomputable def idealKeyLaw (mpk : MPK S Wd Wt) (Bf : Matrix (Fin 1) (Col k) R) :
    PMF (Option (KeyShort Wd Wt R × (Col k → R))) :=
  if h : ∃ T, GoodTrap Big Small dec mpk Bf T then keyLaw Big Small hBig dec mpk h.choose
  else PMF.pure none

/-- **Every covered trapdoor gives the ideal key law.** -/
theorem keyLaw_eq_ideal (hdec : ∀ u, gadgetMap (S := S) (dec u) = u) (mpk : MPK S Wd Wt)
    (Bf : Matrix (Fin 1) (Col k) R) (T : (Col k → R) → KeyShort Wd Wt R)
    (hT : GoodTrap Big Small dec mpk Bf T) :
    keyLaw Big Small hBig dec mpk T = idealKeyLaw Big Small hBig dec mpk Bf := by
  have h : ∃ T, GoodTrap Big Small dec mpk Bf T := ⟨T, hT⟩
  rw [idealKeyLaw, dite_eq_left_of_eq_true (eq_true h)]
  have hc := h.choose_spec
  exact boxSample_eq Big hBig Small (shortMap mpk) (gadgetMap (S := S)) dec hdec _ _ mpk.p hT.2
    hc.2 fun z => by
      have h1 := hT.1 z
      have h2 := hc.1 z
      exact add_right_cancel (h1.trans h2.symm)

end AdvancedEncryption.DualUse
