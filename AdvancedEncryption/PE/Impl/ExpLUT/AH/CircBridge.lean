import PE.Impl.ExpLUT.AH.Final
import SigabaNeoStd.Lattices.CircularRingLWEInst

/-!
# D's circular instances as the registry's circular Ring-LWE words (package G3)

The rows of `circParamsD D` (`m = mCirc D` plain rows, then `K` key rows per helper):

* plain rows (`plainE`): first the columns of `B` (`m̄ + K`, `Fin (m̄ + K) ≃ Wb ⊕ Fin K`), then `d`,
  then the plain helper samples `(k, (1, i))` (row `m̄ + K + 1 + (i · 2b + j)` for `k = jhE j`);
* key rows (`keyE`, the registry's `finProdFinEquiv` order): row `m + (i · 2b + j)` is the circular
  sample `(k, (0, i))` of the helper `k = jhE j`, whose automorphism index is `(jList D)[j]`.

`ρ D : Fin rows ≃ Coord D` (`Coord D = BCol ⊕ Unit ⊕ (Jh × Col)`, the coordinates of a
`CircInst`), `toPair` (the instance as a ring-level pair, `coordA`/`coordV` along `ρ`), and

* **`enc D i = encodeRing (toPair D i)`**, `decode D` with **`decode_enc : decode D (enc D i) = i`**;
* **`realLaw_circParamsD`**: `CircularRingLWE.realLaw (circParamsD D) = (circReal … (χcbd D)
  (χcbd D)).map (enc D)` (`χcbd D`: CBD(16) coefficients, P's `χc` at `Dc`, `χcbd_Dc`);
* **`idealLaw_circParamsD`**: `CircularRingLWE.idealLaw (circParamsD D) = (circUnif …).map (enc D)`;
* `realLaw_bind_decode`, `idealLaw_bind_decode`: a continuation of the decoded instance has the
  same law on the registry's words as on D's instances (for the reduction machine of package G2).
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Lattices Cslib Cslib.Probability AdvancedEncryption.PE
open AdvancedEncryption.ExpLUT.Params
open scoped ENNReal

variable (D : Dims)

/-! ### Coordinates of an instance -/

/-- The coordinates of a circular instance: the columns of `B`, `d`, the helper columns. -/
abbrev Coord := BCol (Wb D) (setting D).τ ⊕ Unit ⊕ (Jh D × Col (setting D).τ)

variable {D} in
/-- A family on the coordinates from its parts. -/
def coordOf {X : Type} (b : BCol (Wb D) (setting D).τ → X) (h : Jh D → Col (setting D).τ → X) (d : X) : Coord D → X :=
  Sum.elim b (Sum.elim (fun _ => d) fun kc => h kc.1 kc.2)

/-- The public parts of an instance on the coordinates. -/
def coordA (i : CInst D) : Coord D → Rg D := coordOf i.aB i.aH i.ad

/-- The values of an instance on the coordinates. -/
def coordV (i : CInst D) : Coord D → Rg D := coordOf i.vB i.vH i.vd

/-- The instance from its public parts and values on the coordinates. -/
def ofCoord (a v : Coord D → Rg D) : CInst D :=
  ⟨fun b => a (.inl b), fun b => v (.inl b), a (.inr (.inl ())), v (.inr (.inl ())),
    fun k c => a (.inr (.inr (k, c))), fun k c => v (.inr (.inr (k, c)))⟩

theorem ofCoord_coord (i : CInst D) : ofCoord D (coordA D i) (coordV D i) = i := rfl

/-- **Independent coordinates** are independent parts. -/
theorem pi_coord_bind {X γ : Type} [Finite X] (d : PMF X) (G : (Coord D → X) → PMF γ) :
    (PMF.pi fun _ : Coord D => d).bind G =
      (PMF.pi fun _ : BCol (Wb D) (setting D).τ => d).bind fun b =>
        (PMF.pi fun _ : Jh D => PMF.pi fun _ : Col (setting D).τ => d).bind fun h =>
          d.bind fun x => G (coordOf b h x) := by
  rw [pi_sum_bind]
  refine congrArg _ (funext fun b => ?_)
  rw [pi_sum_bind, pi_unit_bind]
  simp only [pi_prod_bind]
  rw [PMF.bind_comm d]
  rfl

theorem uniform_coord_bind {γ : Type} (G : (Coord D → Rg D) → PMF γ) :
    (PMF.uniformOfFintype (Coord D → Rg D)).bind G =
      (PMF.uniformOfFintype (BCol (Wb D) (setting D).τ → Rg D)).bind fun b =>
        (PMF.uniformOfFintype (Jh D → Col (setting D).τ → Rg D)).bind fun h =>
          (PMF.uniformOfFintype (Rg D)).bind fun x => G (coordOf b h x) := by
  rw [← PMF.pi_uniformOfFintype, pi_coord_bind, PMF.pi_uniformOfFintype,
    PMF.pi_uniformOfFintype, PMF.pi_uniformOfFintype]

/-! ### The rows -/

/-- The columns of `B`: `Fin (m̄ + K) ≃ Wb ⊕ Fin K`. -/
def bcolE : Fin (D.mb + D.K) ≃ BCol (Wb D) (setting D).τ := finSumFinEquiv.symm

/-- The plain rows: the columns of `B`, `d`, the plain helper samples `(k, (1, i))`. -/
def plainE : Fin (circParamsD D).base.m ≃ BCol (Wb D) (setting D).τ ⊕ Unit ⊕ (Jh D × Fin (setting D).τ) :=
  ((finSumFinEquiv.symm : Fin (D.mb + D.K + 1 + D.K * (D.b * 2)) ≃ _).trans
    (Equiv.sumCongr ((finSumFinEquiv.symm).trans (Equiv.sumCongr (bcolE D) finOneEquiv))
      ((finProdFinEquiv.symm).trans ((Equiv.prodComm _ _).trans
        (Equiv.prodCongr (jhE D) (Equiv.refl _)))))).trans (Equiv.sumAssoc _ _ _)

theorem length_jList : (jList D).length = D.b * 2 := List.length_ofFn

/-- The helper of the `j`-th automorphism index. -/
def helperE : Fin (circParamsD D).J.length ≃ Jh D := (finCongr (length_jList D)).trans (jhE D)

theorem get_jList (j : Fin (circParamsD D).J.length) :
    (circParamsD D).J.get j = (setting D).idx (je D (helperE D j)) := by
  exact List.get_ofFn (fun j : Fin (D.b * 2) => (setting D).idx (je D (jhE D j))) j

/-- The key rows, in the registry's order: `(i, k)` for the sample `(k, (0, i))`. -/
def keyE : Fin ((circParamsD D).τ * (circParamsD D).J.length) ≃ Fin (setting D).τ × Jh D :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) (helperE D))

/-- Plain and key rows as coordinates. -/
def rowToCoord : (BCol (Wb D) (setting D).τ ⊕ Unit ⊕ (Jh D × Fin (setting D).τ)) ⊕ (Fin (setting D).τ × Jh D) → Coord D :=
  Sum.elim (Sum.elim Sum.inl (Sum.elim (fun u => .inr (.inl u))
      fun ki => .inr (.inr (ki.1, (1, ki.2)))))
    fun ik => .inr (.inr (ik.2, (0, ik.1)))

/-- Coordinates as plain and key rows. -/
def coordToRow : Coord D → (BCol (Wb D) (setting D).τ ⊕ Unit ⊕ (Jh D × Fin (setting D).τ)) ⊕ (Fin (setting D).τ × Jh D) :=
  Sum.elim (fun b => .inl (.inl b)) (Sum.elim (fun u => .inl (.inr (.inl u)))
    fun kc => if kc.2.1 = 0 then .inr (kc.2.2, kc.1) else .inl (.inr (.inr (kc.1, kc.2.2))))

/-- `ψ`: plain and key rows are the coordinates. -/
def rowCoordE : (BCol (Wb D) (setting D).τ ⊕ Unit ⊕ (Jh D × Fin (setting D).τ)) ⊕ (Fin (setting D).τ × Jh D) ≃ Coord D where
  toFun := rowToCoord D
  invFun := coordToRow D
  left_inv y := by
    rcases y with (b | u | ⟨k, i⟩) | ⟨i, k⟩ <;> rfl
  right_inv x := by
    rcases x with b | u | ⟨k, r, i⟩
    · rfl
    · rfl
    · fin_cases r <;> rfl

/-- **The rows of `circParamsD D` as the coordinates of an instance.** -/
def ρ : Fin (circParamsD D).rows ≃ Coord D :=
  ((finSumFinEquiv.symm : Fin ((circParamsD D).base.m + (circParamsD D).τ * (circParamsD D).J.length)
      ≃ _).trans (Equiv.sumCongr (plainE D) (keyE D))).trans (rowCoordE D)

theorem ρ_castAdd (a : Fin (circParamsD D).base.m) :
    ρ D (Fin.castAdd ((circParamsD D).τ * (circParamsD D).J.length) a) =
      rowToCoord D (.inl (plainE D a)) := by
  show rowCoordE D ((Equiv.sumCongr (plainE D) (keyE D)) (finSumFinEquiv.symm (Fin.castAdd _ a))) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem ρ_natAdd (t : Fin ((circParamsD D).τ * (circParamsD D).J.length)) :
    ρ D (Fin.natAdd (circParamsD D).base.m t) = rowToCoord D (.inr (keyE D t)) := by
  show rowCoordE D ((Equiv.sumCongr (plainE D) (keyE D)) (finSumFinEquiv.symm (Fin.natAdd _ t))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

/-! ### Encoding and decoding -/

/-- The ring of the registry's parameters is `Rg D`. -/
abbrev PairD := (Fin (circParamsD D).rows → Rg D) × (Fin (circParamsD D).rows → Rg D)

/-- **The instance as a ring-level pair** (rows along `ρ`). -/
def toPair (i : CInst D) : PairD D := (coordA D i ∘ ρ D, coordV D i ∘ ρ D)

/-- The instance of a ring-level pair. -/
def ofPair (v : PairD D) : CInst D := ofCoord D (v.1 ∘ (ρ D).symm) (v.2 ∘ (ρ D).symm)

theorem ofPair_toPair (i : CInst D) : ofPair D (toPair D i) = i := by
  simp only [ofPair, toPair, Function.comp_def, Equiv.apply_symm_apply]
  rfl

/-- **The word of an instance**: the registry's encoding of its ring-level pair. -/
def enc (i : CInst D) : List Bool := encodeRing (toPair D i)

open Classical in
/-- **The instance of a word** (words that encode no pair give the zero instance). -/
noncomputable def decode (w : List Bool) : CInst D :=
  if h : ∃ v : PairD D, encodeRing v = w then ofPair D h.choose else ofCoord D 0 0

theorem decode_enc (i : CInst D) : decode D (enc D i) = i := by
  have h : ∃ v : PairD D, encodeRing v = enc D i := ⟨toPair D i, rfl⟩
  unfold decode
  rw [dif_pos h, encodeRing_injective h.choose_spec, ofPair_toPair]

/-! ### The key shifts on the coordinates -/

/-- The shift of the samples on the coordinates: `σ_{g^{je k}}(s̄) G⁽¹⁾_c` on the helper columns,
`0` elsewhere. -/
noncomputable def shC (s : Rg D) : Coord D → Rg D :=
  Sum.elim 0 (Sum.elim 0 fun kc => (setting D).E.σ ((setting D).idx ((helperMap D).je kc.1)) s *
    (setting D).G 0 kc.2)

theorem G_zero_apply (r : Fin 2) (i : Fin (setting D).τ) :
    (setting D).G 0 (r, i) = if r = 0 then algebraMap (ZMod D.q) (Rg D) (2 ^ (i : ℕ)) else 0 := by
  show (if (0 : Fin 2) = r then (binaryDigits D.N D.q D.K D.q_le).g i else 0) = _
  by_cases h : r = 0
  · subst h; rw [if_pos rfl, if_pos rfl]; rfl
  · rw [if_neg (Ne.symm h), if_neg h]

theorem σ_setting (k : ℕ) (hk : Odd k) (s : Rg D) :
    (setting D).E.σ k s = aut D.N k s := autσ_of_odd hk s

/-- **The key shifts of the registry are the shifts of D's samples.** -/
theorem keyShiftRing_eq (s : Rg D) (r : Fin (circParamsD D).rows) :
    CircularRingLWE.keyShiftRing (circParamsD D) s r = shC D s (ρ D r) := by
  refine Fin.addCases (fun a => ?_) (fun t => ?_) r
  · rw [ρ_castAdd]
    have h0 : CircularRingLWE.keyShiftRing (circParamsD D) s
        (Fin.castAdd ((circParamsD D).τ * (circParamsD D).J.length) a) = 0 := by
      unfold CircularRingLWE.keyShiftRing CircularRingLWE.keyShift
      rw [Fin.addCases_left]
      rfl
    rw [h0]
    rcases plainE D a with b | u | ⟨k, i⟩
    · rfl
    · rfl
    · show 0 = _ * (setting D).G 0 (1, i)
      rw [G_zero_apply, if_neg (by decide), mul_zero]
  · rw [ρ_natAdd]
    unfold CircularRingLWE.keyShiftRing CircularRingLWE.keyShift
    rw [Fin.addCases_right]
    show Negacyclic.ofCoeffs ((2 : ZMod D.q) ^ ((finProdFinEquiv.symm t).1 : ℕ) •
        autCoeffs D.N ((circParamsD D).J.get (finProdFinEquiv.symm t).2) s.coeffs) =
      (setting D).E.σ ((setting D).idx (je D (helperE D (finProdFinEquiv.symm t).2))) s *
        (setting D).G 0 (0, (finProdFinEquiv.symm t).1)
    set i0 := (finProdFinEquiv.symm t).1
    set j0 := (finProdFinEquiv.symm t).2
    set k := (setting D).idx (je D (helperE D j0))
    have hG : (setting D).G 0 (0, i0) = algebraMap (ZMod D.q) (Rg D) (2 ^ (i0 : ℕ)) :=
      (G_zero_apply D 0 i0).trans (if_pos rfl)
    have hJ : (circParamsD D).J.get j0 = k := get_jList D j0
    calc Negacyclic.ofCoeffs ((2 : ZMod D.q) ^ (i0 : ℕ) • autCoeffs D.N ((circParamsD D).J.get j0)
          s.coeffs) = Negacyclic.ofCoeffs ((2 : ZMod D.q) ^ (i0 : ℕ) • autCoeffs D.N k s.coeffs) := by
          rw [hJ]
      _ = aut D.N k s * algebraMap (ZMod D.q) (Rg D) (2 ^ (i0 : ℕ)) := by
          apply Negacyclic.ext
          rw [mul_comm, ← Algebra.smul_def, Negacyclic.coeffs_smul]
          rfl
      _ = (setting D).E.σ k s * (setting D).G 0 (0, i0) :=
          congrArg₂ (· * ·) (σ_setting D k ((setting D).idx_odd _) s).symm hG.symm

/-! ### The laws -/

/-- The key shifts as elements of `Rg D`. -/
def ksD (s : Rg D) (r : Fin (circParamsD D).rows) : Rg D :=
  CircularRingLWE.keyShiftRing (circParamsD D) s r

/-- CBD(16) coefficients (P's `χc` at `Dc`). -/
noncomputable def χcbd : PMF (Rg D) := polyOf (N := D.N) (ModuleLWE.coeffLaw D.q (.cbd 16))

theorem χcbd_Dc : χcbd Dc = χc := rfl

/-- The values of a real instance on the coordinates. -/
theorem coordV_real (aB eb : BCol (Wb D) (setting D).τ → Rg D) (aH eh : Jh D → Col (setting D).τ → Rg D)
    (ad em s : Rg D) (x : Coord D) :
    coordOf (s • aB + eb) (fun k c => s * aH k c -
        (setting D).E.σ ((setting D).idx ((helperMap D).je k)) s * (setting D).G 0 c + eh k c)
        (s * ad + em) x =
      coordOf aB aH ad x * s + coordOf eb eh em x - shC D s x := by
  rcases x with b | u | ⟨k, c⟩ <;>
    simp only [coordOf, shC, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] <;> ring

/-- **D's real instances are the registry's real ring-level pairs.** -/
theorem circRing_eq :
    CircularRingLWE.circRing (circParamsD D) =
      (circReal (setting D) (Wb D) (Jh D) (helperMap D) (χcbd D) (χcbd D)).map (toPair D) := by
  have hU : PMF.uniformOfFintype (Fin (circParamsD D).rows → Rg D) =
      (PMF.uniformOfFintype (Coord D → Rg D)).map fun a => a ∘ ρ D :=
    (Cslib.Probability.PMF.uniformOfFintype_map_equiv
      (Equiv.arrowCongr (ρ D).symm (Equiv.refl (Rg D)))).symm
  have hE : (PMF.pi fun _ : Fin (circParamsD D).rows => χcbd D) =
      (PMF.pi fun _ : Coord D => χcbd D).map fun e => e ∘ ρ D :=
    (pi_comp_equiv (χcbd D) (ρ D)).symm
  have e0 : CircularRingLWE.circRing (circParamsD D) =
      (χcbd D).bind fun σ => (PMF.uniformOfFintype (Fin (circParamsD D).rows → Rg D)).bind fun A =>
        (PMF.pi fun _ : Fin (circParamsD D).rows => χcbd D).map fun e =>
          (A, fun r => A r * σ + e r - ksD D σ r) := rfl
  rw [e0, PMF.bind_comm]
  rw [hU, hE, PMF.bind_map, uniform_coord_bind]
  unfold circReal
  simp only [PMF.map_bind, Function.comp_def]
  refine congrArg _ (funext fun aB => congrArg _ (funext fun aH => congrArg _ (funext fun ad =>
    congrArg _ (funext fun s => ?_))))
  rw [PMF.map_comp, ← PMF.bind_pure_comp, pi_coord_bind]
  simp only [iidLaw, iidFam]
  refine congrArg _ (funext fun eb => congrArg _ (funext fun eh => ?_))
  rw [PMF.map_comp, ← PMF.bind_pure_comp]
  refine congrArg _ (funext fun em => ?_)
  simp only [Function.comp_apply, toPair]
  congr 1
  refine Prod.ext rfl (funext fun r => ?_)
  simp only [Function.comp_apply]
  rw [ksD, keyShiftRing_eq]
  exact (coordV_real D aB eb aH eh ad em s (ρ D r)).symm

/-- **The registry's real circular Ring-LWE law at `circParamsD D`** is that of D's encoded real
instances. -/
theorem realLaw_circParamsD :
    CircularRingLWE.realLaw (circParamsD D) =
      (circReal (setting D) (Wb D) (Jh D) (helperMap D) (χcbd D) (χcbd D)).map (enc D) := by
  exact (CircularRingLWE.realLaw_eq_circRing (circParamsD D)).trans
    ((congrArg (PMF.map encodeRing) (circRing_eq D)).trans (PMF.map_comp _ _ _))

/-- **D's uniform instances are uniform ring-level pairs.** -/
theorem circUnif_map_toPair :
    (circUnif (setting D) (Wb D) (Jh D)).map (toPair D) = PMF.uniformOfFintype (PairD D) := by
  rw [← PMF.bind_pure (PMF.uniformOfFintype (PairD D)), uniform_prod_bind]
  rw [← bind_uniform_equiv (Equiv.arrowCongr (ρ D).symm (Equiv.refl (Rg D)))]
  simp only [← bind_uniform_equiv (Equiv.arrowCongr (ρ D).symm (Equiv.refl (Rg D)))]
  simp only [uniform_coord_bind]
  unfold circUnif
  simp only [← PMF.bind_pure_comp, PMF.bind_bind, Function.comp_apply, PMF.pure_bind]
  rfl

/-- **The registry's uniform circular Ring-LWE law at `circParamsD D`** is that of D's encoded
uniform instances. -/
theorem idealLaw_circParamsD :
    CircularRingLWE.idealLaw (circParamsD D) = (circUnif (setting D) (Wb D) (Jh D)).map (enc D) := by
  exact (CircularRingLWE.idealLaw_eq_uniform (circParamsD D)).trans
    ((congrArg (PMF.map encodeRing) (circUnif_map_toPair D).symm).trans (PMF.map_comp _ _ _))

/-- **A continuation of the decoded instance** has the same law on real words as on D's real
instances. -/
theorem realLaw_bind_decode {γ : Type} (F : CInst D → PMF γ) :
    (CircularRingLWE.realLaw (circParamsD D)).bind (fun w => F (decode D w)) =
      (circReal (setting D) (Wb D) (Jh D) (helperMap D) (χcbd D) (χcbd D)).bind F := by
  rw [realLaw_circParamsD, PMF.bind_map]
  exact congrArg _ (funext fun i => by simp only [Function.comp_apply, decode_enc])

/-- **The same on uniform words.** -/
theorem idealLaw_bind_decode {γ : Type} (F : CInst D → PMF γ) :
    (CircularRingLWE.idealLaw (circParamsD D)).bind (fun w => F (decode D w)) =
      (circUnif (setting D) (Wb D) (Jh D)).bind F := by
  rw [idealLaw_circParamsD, PMF.bind_map]
  exact congrArg _ (funext fun i => by simp only [Function.comp_apply, decode_enc])

/-- At the concrete parameters: P's laws. -/
theorem realLaw_circParamsD_Dc :
    CircularRingLWE.realLaw (circParamsD Dc) = (circR Dc χc χc).map (enc Dc) :=
  realLaw_circParamsD Dc

end AdvancedEncryption.ExpLUT.Prog

end
