import PE.Impl.ExpLUT.Prog.RedChalCb
/-!
# The rows of the instance and the enumerations (package G2, `chalP`)

The values of the instance as words in the registry's row order (`vsV`): the columns of `B`
(`m̄ + K`), `d`, the plain helper samples `(k, (1, i))` at `m̄ + K + 1 + i·2b + j`, the key samples
`(k, (0, i))` at `mCirc + i·2b + j` (`k = jhE j`). And the enumerations of `Jh`, `Col`, `Fin n`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedChal

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo Matrix AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open SigabaNeo.Tape.RingVM.Hash

variable {D : Dims}

/-! ### The rows -/

/-- The words of the values of the instance, row by row. -/
noncomputable def vsV (i : CInst D) : List (List Bool) :=
  (List.finRange (circParamsD D).rows).map fun r => encRM D.N D.K (coordV D i (ρ D r))

theorem instVW_eq (σ : RawSec D) : instVW σ = (vsV σ.2.1).flatten := by
  rw [instVW, vecE_enc_eq, enum_fin]; rfl

theorem length_vsV (i : CInst D) : (vsV i).length = (circParamsD D).rows := by simp [vsV]

theorem mem_vsV {i : CInst D} : ∀ x ∈ vsV i, x.length = D.N * D.K := fun _ hx => mem_words hx

theorem rows_eq : (circParamsD D).rows = mCirc D + D.K * (D.b * 2) := by
  show mCirc D + D.K * (jList D).length = _
  rw [length_jList]

theorem vsV_get (i : CInst D) (r : Fin (circParamsD D).rows) :
    (vsV i)[r.val]'(by rw [length_vsV]; exact r.isLt) =
      encRM D.N D.K (coordV D i (ρ D r)) := by
  simp [vsV]

/-! ### The rows with `K`-typed equivalences -/

/-- `plainE` with the types of `D.K`. -/
def plainE' (D : Dims) : Fin (D.mb + D.K + 1 + D.K * (D.b * 2)) ≃
    BCol (Wb D) D.K ⊕ Unit ⊕ (Jh D × Fin D.K) :=
  ((finSumFinEquiv.symm : Fin (D.mb + D.K + 1 + D.K * (D.b * 2)) ≃ _).trans
    (Equiv.sumCongr ((finSumFinEquiv.symm).trans (Equiv.sumCongr (bcolE D) finOneEquiv))
      ((finProdFinEquiv.symm).trans ((Equiv.prodComm _ _).trans
        (Equiv.prodCongr (jhE D) (Equiv.refl _)))))).trans (Equiv.sumAssoc _ _ _)

/-- `keyE` with the types of `D.K`. -/
noncomputable def keyE' (D : Dims) : Fin (D.K * (circParamsD D).J.length) ≃ Fin D.K × Jh D :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) (helperE D))

theorem plainE'_col (v : Wb D) :
    plainE' D (Fin.castAdd (D.K * (D.b * 2)) (Fin.castAdd 1 (Fin.castAdd D.K v))) = .inl (.inl v) := by
  simp [plainE', bcolE]

theorem plainE'_gad (g : Fin D.K) :
    plainE' D (Fin.castAdd (D.K * (D.b * 2)) (Fin.castAdd 1 (Fin.natAdd D.mb g))) = .inl (.inr g) := by
  simp [plainE', bcolE]

theorem plainE'_d :
    plainE' D (Fin.castAdd (D.K * (D.b * 2)) (Fin.natAdd (D.mb + D.K) (0 : Fin 1))) = .inr (.inl ()) := by
  simp [plainE', bcolE]

theorem plainE'_h (i : Fin D.K) (j : Fin (D.b * 2)) :
    plainE' D (Fin.natAdd (D.mb + D.K + 1) (finProdFinEquiv (i, j))) = .inr (.inr (jhE D j, i)) := by
  simp [plainE']

theorem keyE'_eq (i : Fin D.K) (j : Fin (circParamsD D).J.length) :
    keyE' D (finProdFinEquiv (i, j)) = (i, helperE D j) := by
  simp [keyE']

/-! ### The words of the rows -/

theorem vsV_col (i : CInst D) (v : Wb D) (hn : v.val < (vsV i).length) :
    (vsV i)[v.val] = encRM D.N D.K (i.vB (.inl v)) := by
  have h := vsV_get i (Fin.castAdd ((circParamsD D).τ * (circParamsD D).J.length)
    (show Fin (circParamsD D).base.m from
      Fin.castAdd (D.K * (D.b * 2)) (Fin.castAdd 1 (Fin.castAdd D.K v))))
  rw [ρ_castAdd, show plainE D (Fin.castAdd (D.K * (D.b * 2)) (Fin.castAdd 1 (Fin.castAdd D.K v))) =
    plainE' D (Fin.castAdd (D.K * (D.b * 2)) (Fin.castAdd 1 (Fin.castAdd D.K v))) from rfl,
    plainE'_col] at h
  exact h

theorem vsV_gad (i : CInst D) (g : Fin D.K) (hn : D.mb + g.val < (vsV i).length) :
    (vsV i)[D.mb + g.val] = encRM D.N D.K (i.vB (.inr g)) := by
  have h := vsV_get i (Fin.castAdd ((circParamsD D).τ * (circParamsD D).J.length)
    (show Fin (circParamsD D).base.m from
      Fin.castAdd (D.K * (D.b * 2)) (Fin.castAdd 1 (Fin.natAdd D.mb g))))
  rw [ρ_castAdd, show plainE D (Fin.castAdd (D.K * (D.b * 2)) (Fin.castAdd 1 (Fin.natAdd D.mb g))) =
    plainE' D (Fin.castAdd (D.K * (D.b * 2)) (Fin.castAdd 1 (Fin.natAdd D.mb g))) from rfl,
    plainE'_gad] at h
  exact h

theorem vsV_d (i : CInst D) (hn : D.mb + D.K < (vsV i).length) :
    (vsV i)[D.mb + D.K] = encRM D.N D.K i.vd := by
  have h := vsV_get i (Fin.castAdd ((circParamsD D).τ * (circParamsD D).J.length)
    (show Fin (circParamsD D).base.m from
      Fin.castAdd (D.K * (D.b * 2)) (Fin.natAdd (D.mb + D.K) (0 : Fin 1))))
  rw [ρ_castAdd, show plainE D (Fin.castAdd (D.K * (D.b * 2)) (Fin.natAdd (D.mb + D.K) (0 : Fin 1))) =
    plainE' D (Fin.castAdd (D.K * (D.b * 2)) (Fin.natAdd (D.mb + D.K) (0 : Fin 1))) from rfl,
    plainE'_d] at h
  exact h

theorem vsV_ph (i : CInst D) (r : Fin D.K) (j : Fin (D.b * 2))
    (hn : D.mb + D.K + 1 + (j.val + D.b * 2 * r.val) < (vsV i).length) :
    (vsV i)[D.mb + D.K + 1 + (j.val + D.b * 2 * r.val)] =
      encRM D.N D.K (i.vH (jhE D j) (1, r)) := by
  have h := vsV_get i (Fin.castAdd ((circParamsD D).τ * (circParamsD D).J.length)
    (show Fin (circParamsD D).base.m from
      Fin.natAdd (D.mb + D.K + 1) (finProdFinEquiv (r, j))))
  rw [ρ_castAdd, show plainE D (Fin.natAdd (D.mb + D.K + 1) (finProdFinEquiv (r, j))) =
    plainE' D (Fin.natAdd (D.mb + D.K + 1) (finProdFinEquiv (r, j))) from rfl, plainE'_h] at h
  exact h

theorem vsV_key (i : CInst D) (r : Fin D.K) (j : Fin (circParamsD D).J.length)
    (hn : mCirc D + (j.val + (circParamsD D).J.length * r.val) < (vsV i).length) :
    (vsV i)[mCirc D + (j.val + (circParamsD D).J.length * r.val)] =
      encRM D.N D.K (i.vH (helperE D j) (0, r)) := by
  have h := vsV_get i (Fin.natAdd (circParamsD D).base.m
    (show Fin ((circParamsD D).τ * (circParamsD D).J.length) from finProdFinEquiv (r, j)))
  rw [ρ_natAdd, show keyE D (finProdFinEquiv (r, j)) = keyE' D (finProdFinEquiv (r, j)) from rfl,
    keyE'_eq] at h
  exact h

end AdvancedEncryption.ExpLUT.Prog.RedChal
