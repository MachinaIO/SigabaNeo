import PE.Impl.ExpLUT.Prog.RedPubPMath
/-!
# The words of the instance in the raw secret (package G2, `pubP`)

The instance enters the raw secret as its ring-level pair (`instEnc`, `toPair`), rows in the
registry's order `ρ` (`AH/CircBridge`): the columns of `B` (`BCol`, in `Enum` order), `d`, the
plain helper samples `(k, (1, i))` (`i` outer, `k ∈ Jh` inner), then the circular samples
`(k, (0, i))` (`i` outer, `k` inner). **`rows_map`**: the values of any family on the coordinates
along the rows, in this order; **`instA_words`**, **`instV_words`**: the two halves of the
instance word.

The public key needs the transpose of the helper blocks (`H_k`, `k` outer); `pubP` reorders them
(`RedPubPLAN.md`).
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
open AdvancedEncryption.PE

/-! ### Lists over `Fin` along the standard equivalences -/

theorem map_finRange_sum {β : Type} {m n : ℕ} (g : Fin m ⊕ Fin n → β) :
    (List.finRange (m + n)).map (fun x => g (finSumFinEquiv.symm x)) =
      (List.finRange m).map (fun x => g (.inl x)) ++ (List.finRange n).map (fun x => g (.inr x)) := by
  rw [← List.ofFn_eq_map, List.ofFn_add, List.ofFn_eq_map, List.ofFn_eq_map]
  congr 1
  · refine List.map_congr_left fun a _ => ?_
    exact congrArg g (finSumFinEquiv_symm_apply_castAdd a)
  · refine List.map_congr_left fun a _ => ?_
    exact congrArg g (finSumFinEquiv_symm_apply_natAdd a)

theorem finProd_symm_mk {m n : ℕ} (i : Fin m) (j : Fin n) (h : (i : ℕ) * n + j < m * n) :
    finProdFinEquiv.symm (⟨i * n + j, h⟩ : Fin (m * n)) = (i, j) := by
  rw [Equiv.symm_apply_eq]
  ext
  simp [finProdFinEquiv]
  ring

theorem map_finRange_prod {β : Type} {m n : ℕ} (g : Fin m × Fin n → β) :
    (List.finRange (m * n)).map (fun x => g (finProdFinEquiv.symm x)) =
      ((List.finRange m).map fun i => (List.finRange n).map fun j => g (i, j)).flatten := by
  rw [← List.ofFn_eq_map, List.ofFn_mul]
  simp only [finProd_symm_mk, List.ofFn_eq_map]

theorem map_finRange_congr {β : Type} {L L' : ℕ} (h : L = L') (f : Fin L' → β) :
    (List.finRange L).map (fun x => f (finCongr h x)) = (List.finRange L').map f := by
  subst h; simp

/-! ### The rows of an instance -/

variable (D : Dims)

/-- The values of a family on the plain helper samples, `i` outer, `k` inner. -/
def plainHL {β : Type} (F : Jh D → Col D.K → β) : List β :=
  ((List.finRange D.K).map fun i => (Enum.list (α := Jh D)).map fun k => F k (1, i)).flatten

/-- The values of a family on the circular samples, `i` outer, `k` inner. -/
def keyHL {β : Type} (F : Jh D → Col D.K → β) : List β :=
  ((List.finRange D.K).map fun i => (Enum.list (α := Jh D)).map fun k => F k (0, i)).flatten

variable {D}

theorem map_jh {β : Type} (g : Jh D → β) :
    (List.finRange (D.b * 2)).map (fun x => g (jhE D x)) = (Enum.list (α := Jh D)).map g := by
  rw [show (Enum.list (α := Jh D)) = (List.finRange D.b).product (List.finRange 2) from rfl,
    map_product]
  exact map_finRange_prod (m := D.b) (n := 2) g

theorem map_bcol {β : Type} (g : BCol (Wb D) D.K → β) :
    (List.finRange (D.mb + D.K)).map (fun x => g (bcolE D x)) =
      (Enum.list (α := BCol (Wb D) D.K)).map g := by
  rw [show (Enum.list (α := BCol (Wb D) D.K)) =
      (List.finRange D.mb).map Sum.inl ++ (List.finRange D.K).map Sum.inr from rfl,
    List.map_append, List.map_map, List.map_map]
  exact map_finRange_sum (m := D.mb) (n := D.K) g

/-- **The values of a family on the coordinates along the rows of the registry.** -/
theorem rows_map {β : Type} (F : Coord D → β) :
    (List.finRange (circParamsD D).rows).map (fun r => F (ρ D r)) =
      (Enum.list (α := BCol (Wb D) D.K)).map (fun b => F (.inl b)) ++
        ([F (.inr (.inl ()))] ++ (plainHL D (fun k c => F (.inr (.inr (k, c)))) ++
          keyHL D (fun k c => F (.inr (.inr (k, c)))))) := by
  show (List.finRange ((circParamsD D).base.m + (circParamsD D).τ * (circParamsD D).J.length)).map
    (fun r => F (rowCoordE D ((Equiv.sumCongr (plainE D) (keyE D)) (finSumFinEquiv.symm r)))) = _
  refine (map_finRange_sum (g := fun y => F (rowCoordE D (Equiv.sumCongr (plainE D) (keyE D) y)))).trans ?_
  rw [← List.append_assoc, ← List.append_assoc]
  congr 1
  · -- the plain rows
    refine (map_finRange_sum (m := D.mb + D.K + 1) (n := D.K * (D.b * 2))
      (g := fun y => F (rowToCoord D (.inl (Equiv.sumAssoc _ _ _
        (Equiv.sumCongr ((finSumFinEquiv.symm).trans (Equiv.sumCongr (bcolE D) finOneEquiv))
          ((finProdFinEquiv.symm).trans ((Equiv.prodComm _ _).trans
            (Equiv.prodCongr (jhE D) (Equiv.refl _)))) y)))))).trans ?_
    congr 1
    · refine (map_finRange_sum (m := D.mb + D.K) (n := 1)
        (g := fun y => F (rowToCoord D (.inl (Equiv.sumAssoc _ _ _
          (.inl (Sum.map (bcolE D) finOneEquiv y))))))).trans ?_
      congr 1
      exact map_bcol (fun b => F (.inl b))
    · refine (map_finRange_prod (m := D.K) (n := D.b * 2)
        (g := fun p => F (.inr (.inr (jhE D p.2, (1, p.1)))))).trans ?_
      unfold plainHL
      congr 1
      refine List.map_congr_left fun i _ => ?_
      exact map_jh (fun k => F (.inr (.inr (k, (1, i)))))
  · -- the circular rows
    refine (map_finRange_prod (m := (circParamsD D).τ) (n := (circParamsD D).J.length)
      (g := fun p => F (.inr (.inr (helperE D p.2, (0, p.1)))))).trans ?_
    unfold keyHL
    congr 1
    refine List.map_congr_left fun i _ => ?_
    refine (map_finRange_congr (length_jList D)
      (fun j => F (.inr (.inr (jhE D j, ((0 : Fin 2), i)))))).trans ?_
    exact map_jh (fun k => F (.inr (.inr (k, (0, i)))))

/-- The words of a list of ring elements. -/
noncomputable def ringWords (l : List (Rg D)) : List Bool := (l.map (encRM D.N D.K)).flatten

theorem vecE_rows (v : Fin (circParamsD D).rows → Rg D) :
    (vecE D (Fin (circParamsD D).rows)).enc v = ringWords ((List.finRange _).map v) := by
  rw [pvecE_enc, ringWords, List.map_map]
  rfl

/-- **The public half of the instance word**: `aB`, `ad`, the plain helper samples, the circular
ones. -/
theorem instA_words (i : CInst D) :
    (vecE D (Fin (circParamsD D).rows)).enc (toPair D i).1 =
      pwordsOf i.aB ++ (encRM D.N D.K i.ad ++
        (ringWords (plainHL D i.aH) ++ ringWords (keyHL D i.aH))) := by
  rw [vecE_rows]
  show ringWords ((List.finRange _).map fun r => coordA D i (ρ D r)) = _
  rw [rows_map]
  simp only [ringWords, List.map_append, List.flatten_append, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.append_nil]
  congr 1
  exact congrArg List.flatten List.map_map

/-- **The value half of the instance word.** -/
theorem instV_words (i : CInst D) :
    (vecE D (Fin (circParamsD D).rows)).enc (toPair D i).2 =
      pwordsOf i.vB ++ (encRM D.N D.K i.vd ++
        (ringWords (plainHL D i.vH) ++ ringWords (keyHL D i.vH))) := by
  rw [vecE_rows]
  show ringWords ((List.finRange _).map fun r => coordV D i (ρ D r)) = _
  rw [rows_map]
  simp only [ringWords, List.map_append, List.flatten_append, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.append_nil]
  congr 1
  exact congrArg List.flatten List.map_map

end AdvancedEncryption.ExpLUT.Prog
