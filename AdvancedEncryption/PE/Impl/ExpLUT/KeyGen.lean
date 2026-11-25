import PE.Impl.ExpLUT.Scheme
import PE.Impl.ExpLUT.Noise
import SigabaNeoStd.Lattices.BoxSampler

/-!
# Key generation by box rejection (§5.1 KeyGen, Lemma 6)

A key `k_F` with `M_F k_Fᵀ = (d₁ δ₁)ᵀ` is drawn by one try of box rejection
(`SigabaNeo.Lattices.boxSample`). The columns of `M_F` split into

* the **gadget coordinates** `z ∈ R^{W × τ}` (`ZIdx`): the last `τ` columns of every block
  `β_i = δ_iᵀ ⊗ σ_i(B⁽¹⁾)`, where `σ_i(B⁽¹⁾) = [σ_i(Ā) | g − σ_i(Ā) σ_i(T)]` (Lemma 6);
* the **short part** `x` (`PIdx`): the `Ā` columns of every `β_i`, all the blocks `η_{i,k}` and
  the last `2τ` columns;

and the key is `assemble x z`. The public map on the short part is `x ↦ M_F (x, 0)`
(`pubShort`), the gadget is `I_W ⊗ g` (`gadZ`, decomposed by `gadDec`), and a trapdoor is any
`T : z ↦ x` with `pubShort (T z) + G z = M_F (0, z)` (`GoodTrap`).

* **The real trapdoor** `blockdiag σ_i(T)` (`realTrap`, `realTrap_good`): `z ↦ −(σ_i(T) z_i)_i` on
  the `Ā` columns, for `B⁽¹⁾ = [Ā | g − Ā T]` (`TrapOK`, `trapOK_setup`).
* **Keys are valid** (`valid_of_mem_support`) and short: the shift `T z` of the real trapdoor is at
  most `τ n B_T` for decompositions with binary digits (`rowBnd_realTrap`).
* **The law does not depend on the trapdoor** (`keyLaw_eq_of_good`, from `boxSample_eq`): any two
  good trapdoors covered by the boxes give the same key law, which is the ideal one
  (`idealKeyLaw`, `keyLaw_eq_ideal`). Package D plugs the trapdoor of Lemma 11 in here, with the
  same `pubShort`, `gadZ`, `dec`, `Big` and `Small`.
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix
open scoped ENNReal

variable {R : Type*} [CommRing R] {S : Setting R} {Wb J Pos : Type*} [Fintype Wb] [Fintype J]
 

/-- The short coordinates of a key: the `Ā` columns of the blocks `β_i`, the blocks `η_{i,k}`
and the last `2τ` columns. -/
abbrev PIdx (Wb J : Type*) (τ W : ℕ) := (Fin W × Wb) ⊕ (Fin W × J × Col τ) ⊕ Col τ

/-- The gadget coordinates: the last `τ` columns of the blocks `β_i`. -/
abbrev ZIdx (τ W : ℕ) := Fin W × Fin τ

/-- The key of a short part `x` and gadget coordinates `z`. -/
def assemble (x : PIdx Wb J S.τ S.E.W → R) (z : ZIdx S.τ S.E.W → R) : KCol Wb J S.τ S.E.W → R
  | .inl (i, .inl w) => x (.inl (i, w))
  | .inl (i, .inr c) => z (i, c)
  | .inr q => x (.inr q)

omit [Fintype Wb] [Fintype J] in
theorem assemble_add (x x' : PIdx Wb J S.τ S.E.W → R) (z z' : ZIdx S.τ S.E.W → R) :
    assemble (x + x') (z + z') = assemble x z + assemble x' z' := by
  funext c; rcases c with ⟨i, w | c⟩ | q <;> rfl

omit [Fintype Wb] [Fintype J] in
theorem assemble_split (x : PIdx Wb J S.τ S.E.W → R) (z : ZIdx S.τ S.E.W → R) :
    assemble x z = assemble x 0 + assemble 0 z := by
  rw [← assemble_add, add_zero, zero_add]

/-- The public map on the short part: `x ↦ M_F (x, 0)`. -/
def pubShort (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos) :
    (PIdx Wb J S.τ S.E.W → R) →+ (Fin S.E.W → R) where
  toFun x := keyMat M mpk F *ᵥ assemble x 0
  map_zero' := by
    rw [show assemble (0 : PIdx Wb J S.τ S.E.W → R) (0 : ZIdx S.τ S.E.W → R) = 0 from
      funext fun c => by rcases c with ⟨i, w | c⟩ | q <;> rfl, Matrix.mulVec_zero]
  map_add' x y := by
    rw [show assemble (x + y) 0 = assemble x 0 + assemble y 0 by
      rw [← assemble_add, add_zero], Matrix.mulVec_add]

/-- The public map on the gadget coordinates: `z ↦ M_F (0, z)`. -/
def pubZ (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos) (z : ZIdx S.τ S.E.W → R) :
    Fin S.E.W → R :=
  keyMat M mpk F *ᵥ assemble 0 z

/-- The gadget `I_W ⊗ g` on the gadget coordinates. -/
def gadZ (z : ZIdx S.τ S.E.W → R) : Fin S.E.W → R := fun i => ∑ c, S.D.g c * z (i, c)

/-- The binary decomposition `(I_W ⊗ g)⁻¹`. -/
def gadDec (y : Fin S.E.W → R) : ZIdx S.τ S.E.W → R := fun ic => S.D.d (y ic.1) ic.2

theorem gadZ_gadDec (y : Fin S.E.W → R) : gadZ (gadDec y) = y :=
  funext fun i => S.D.recompose (y i)

/-- `M_F (x, z) = pubShort x + pubZ z`. -/
theorem keyMat_mulVec_assemble (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos)
    (x : PIdx Wb J S.τ S.E.W → R) (z : ZIdx S.τ S.E.W → R) :
    keyMat M mpk F *ᵥ assemble x z = pubShort M mpk F x + pubZ M mpk F z := by
  rw [assemble_split, Matrix.mulVec_add]; rfl

/-- A trapdoor of `M_F` for the gadget coordinates: `pubShort (T z) + G z = M_F (0, z)`. -/
def GoodTrap (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos)
    (T : (ZIdx S.τ S.E.W → R) → PIdx Wb J S.τ S.E.W → R) : Prop :=
  ∀ z, pubShort M mpk F (T z) + gadZ z = pubZ M mpk F z

/-! ### The real trapdoor -/

/-- `B⁽¹⁾ = [Ā | g − Ā T]`: the TrapGen trapdoor `T` of the first row of `B`. -/
def TrapOK (mpk : MPK S Wb J Pos) (T : Matrix Wb (Fin S.τ) R) : Prop :=
  ∀ c, mpk.B 0 (.inr c) = S.D.g c - ∑ w, mpk.B 0 (.inl w) * T w c

omit [Fintype J] in
theorem trapOK_setup (r : SetupCoins S Wb J Pos) : TrapOK (setup r).1 (setup r).2.T := by
  intro c; rfl

/-- **The real trapdoor** `blockdiag σ_i(T)`: `z ↦ −(σ_i(T) z_i)_i` on the `Ā` columns. -/
def realTrap (T : Matrix Wb (Fin S.τ) R) (z : ZIdx S.τ S.E.W → R) : PIdx Wb J S.τ S.E.W → R
  | .inl (i, w) => -∑ c, S.E.σ (S.idx i) (T w c) * z (i, c)
  | .inr _ => 0

/-- **The real trapdoor is a trapdoor** (Lemma 6). -/
theorem realTrap_good (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos)
    (T : Matrix Wb (Fin S.τ) R) (hT : TrapOK mpk T) : GoodTrap M mpk F (realTrap T) := by
  intro z
  funext i'
  simp only [pubShort, pubZ, gadZ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.add_apply,
    Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, assemble, realTrap,
    keyMat, Matrix.of_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, ite_mul,
    zero_mul]
  simp only [ite_self, Finset.sum_const_zero, zero_add, add_zero, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have key : ∀ x, S.E.σ (S.idx i') (mpk.B 0 (Sum.inr x)) =
      S.D.g x - ∑ w, S.E.σ (S.idx i') (mpk.B 0 (Sum.inl w)) * S.E.σ (S.idx i') (T w x) := by
    intro x; rw [hT x, map_sub, map_sum, S.σ_g]; simp only [map_mul]
  refine Eq.trans ?_ (Finset.sum_congr rfl fun x _ => congrArg (· * z (i', x)) (key x)).symm
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum, mul_neg,
    Finset.sum_neg_distrib, mul_assoc]
  conv_rhs => rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin S.τ)))]
  ring

/-! ### Keys -/

/-- The key of an output of box rejection (the zero key on abort). -/
def keyOfOutput : Option ((PIdx Wb J S.τ S.E.W → R) × (ZIdx S.τ S.E.W → R)) →
    KCol Wb J S.τ S.E.W → R
  | some (x, z) => assemble x z
  | none => 0

variable [DecidableEq R]
variable (Big Small : Finset (PIdx Wb J S.τ S.E.W → R)) (hBig : Big.Nonempty)
  (dec : (Fin S.E.W → R) → ZIdx S.τ S.E.W → R)

/-- **The law of a key** with the trapdoor `T`: one try of box rejection for the target `d₁ δ₁`. -/
noncomputable def keyLaw (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos)
    (T : (ZIdx S.τ S.E.W → R) → PIdx Wb J S.τ S.E.W → R) :
    PMF (Option ((PIdx Wb J S.τ S.E.W → R) × (ZIdx S.τ S.E.W → R))) :=
  boxSample Big hBig Small (pubShort M mpk F) dec T (keyTarget mpk)

/-- **KeyGen**: the law of the key of `F` with the real trapdoor of `msk`. -/
noncomputable def keyGenLaw (M : HelperMap S J) (msk : MSK S Wb J Pos) (F : BP Pos) :
    PMF (KCol Wb J S.τ S.E.W → R) :=
  (keyLaw Big Small hBig dec M msk.mpk F (realTrap msk.T)).map keyOfOutput

/-- **Keys are valid**: every accepted output with a good trapdoor covered by the boxes gives a
key with `M_F k_Fᵀ = (d₁ δ₁)ᵀ`. -/
theorem valid_of_mem_support (hdec : ∀ y, gadZ (dec y) = y) (M : HelperMap S J)
    (mpk : MPK S Wb J Pos) (F : BP Pos) (T : (ZIdx S.τ S.E.W → R) → PIdx Wb J S.τ S.E.W → R)
    (hT : GoodTrap M mpk F T) (hcov : ∀ x ∈ Small, ∀ y, x + T (dec y) ∈ Big)
    (x : (PIdx Wb J S.τ S.E.W → R) × (ZIdx S.τ S.E.W → R))
    (hx : some x ∈ (keyLaw Big Small hBig dec M mpk F T).support) :
    x.1 ∈ Small ∧ (∃ y, dec y = x.2) ∧ ValidKey M mpk F (keyOfOutput (some x)) := by
  classical
  have hpos := (PMF.mem_support_iff _ _).mp hx
  rw [keyLaw, boxSample_some Big hBig Small (pubShort M mpk F) gadZ dec hdec T _ hcov] at hpos
  split_ifs at hpos with ht
  · obtain ⟨hs, hz, hu⟩ := ht
    refine ⟨hs, hz, ?_⟩
    simp only at hu
    rw [hT] at hu
    unfold ValidKey keyOfOutput
    rw [keyMat_mulVec_assemble, hu]
  · exact absurd rfl hpos

/-- **The law does not depend on the trapdoor**: two good trapdoors covered by the boxes give the
same key law. -/
theorem keyLaw_eq_of_good (hdec : ∀ y, gadZ (dec y) = y) (M : HelperMap S J) (mpk : MPK S Wb J Pos)
    (F : BP Pos) (T T' : (ZIdx S.τ S.E.W → R) → PIdx Wb J S.τ S.E.W → R)
    (hT : GoodTrap M mpk F T) (hT' : GoodTrap M mpk F T')
    (hcov : ∀ x ∈ Small, ∀ y, x + T (dec y) ∈ Big) (hcov' : ∀ x ∈ Small, ∀ y, x + T' (dec y) ∈ Big) :
    keyLaw Big Small hBig dec M mpk F T = keyLaw Big Small hBig dec M mpk F T' :=
  boxSample_eq Big hBig Small (pubShort M mpk F) gadZ dec hdec T T' _ hcov hcov'
    fun z => add_right_cancel ((hT z).trans (hT' z).symm)

open Classical in
/-- **The ideal key law** of `F`: one try with any good covered trapdoor (an abort if there is
none). It depends on public data only. -/
noncomputable def idealKeyLaw (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos) :
    PMF (Option ((PIdx Wb J S.τ S.E.W → R) × (ZIdx S.τ S.E.W → R))) :=
  if h : ∃ T, GoodTrap M mpk F T ∧ ∀ x ∈ Small, ∀ y, x + T (dec y) ∈ Big then
    keyLaw Big Small hBig dec M mpk F h.choose
  else PMF.pure none

/-- **Every good covered trapdoor gives the ideal key law.** -/
theorem keyLaw_eq_ideal (hdec : ∀ y, gadZ (dec y) = y) (M : HelperMap S J) (mpk : MPK S Wb J Pos)
    (F : BP Pos) (T : (ZIdx S.τ S.E.W → R) → PIdx Wb J S.τ S.E.W → R) (hT : GoodTrap M mpk F T)
    (hcov : ∀ x ∈ Small, ∀ y, x + T (dec y) ∈ Big) :
    keyLaw Big Small hBig dec M mpk F T = idealKeyLaw Big Small hBig dec M mpk F := by
  have h : ∃ T, GoodTrap M mpk F T ∧ ∀ x ∈ Small, ∀ y, x + T (dec y) ∈ Big := ⟨T, hT, hcov⟩
  rw [idealKeyLaw, dif_pos h]
  exact keyLaw_eq_of_good Big Small hBig dec hdec M mpk F _ _ hT h.choose_spec.1 hcov
    h.choose_spec.2

omit [Fintype Wb] [Fintype J] [DecidableEq R] in
/-- **The shift of the real trapdoor is short**: for a binary-entry-bounded `T` (`‖T_{w,c}‖ ≤ B_T`)
and gadget coordinates with digits of norm at most `1`, every entry of `T z` is at most `τ n B_T`. -/
theorem rowBnd_realTrap (N : NormSpec S) (T : Matrix Wb (Fin S.τ) R) (BT : ℕ)
    (hT : ∀ w c, N.nrm (T w c) ≤ BT) (z : ZIdx S.τ S.E.W → R) (hz : ∀ ic, N.nrm (z ic) ≤ 1) :
    RowBnd N (realTrap (J := J) T z) (S.τ * (S.E.n * BT)) := by
  intro p
  rcases p with ⟨i, w⟩ | q
  · simp only [realTrap, N.nrm_neg]
    refine (N.nrm_sum_le _ _ (S.E.n * BT) fun c _ => ?_).trans (by simp)
    refine (N.nrm_mul _ _).trans ?_
    calc S.E.n * N.nrm (S.E.σ (S.idx i) (T w c)) * N.nrm (z (i, c)) ≤ S.E.n * BT * 1 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ ((N.nrm_σ _ _ (S.idx_odd _)).trans (hT w c)))
            (hz _)
      _ = S.E.n * BT := mul_one _
  · simp [realTrap, N.nrm_zero]

end AdvancedEncryption.ExpLUT
