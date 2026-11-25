import PE.Impl.ExpLUT.Prog.RedChalBlocks
/-!
# The words of the helpers (package G2, `chalP`)

The words written by `hC` (on indices: helper `j < 2b`, round `i < K`) are the canonical words of
`h_k(c) = v_{H,k}(c) − G⁽²⁾(c) + H⁽²⁾_k(c)` along `Enum Jh` and `Enum Col` (**`hout_eq`**), and the
stream `H⁽²⁾` is read in the same order (**`h2W_eq`**).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedChal

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo Matrix AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open SigabaNeo.Tape.RingVM.Hash

variable {D : Dims}

/-! ### Enumerations -/

theorem range_map_eq {β : Type} (n : ℕ) (f : ℕ → β) :
    (List.range n).map f = (List.finRange n).map fun j => f j.val := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp

theorem enum_jh : (Enum.list (α := Jh D)) = (List.finRange (D.b * 2)).map (jhE D) := by
  have hl : (Enum.list (α := Jh D)).length = D.b * 2 := by
    rw [length_enum_prod, enum_fin, enum_fin]; simp
  show (List.finRange D.b).product (List.finRange 2) = _
  refine List.ext_getElem (hl.trans (by simp)) fun n h1 h2 => ?_
  have hn : n < D.b * 2 := by simpa using h2
  have key := getD_map_product_F (List.finRange D.b) (List.finRange 2) id (⟨0, by omega⟩, 0)
    (i := n / 2) (e := n % 2) (by simp; omega) (by simp; omega)
  simp only [List.map_id, List.length_finRange] at key
  rw [show n / 2 * 2 + n % 2 = n by omega, List.getD_eq_getElem _ _ h1] at key
  rw [key, List.getElem_map, List.getElem_finRange]
  simp only [jhE, finProdFinEquiv_symm_apply, id, List.getElem_finRange, Prod.mk.injEq]
  constructor <;> rfl

theorem enum_col_map {β : Type} (G : Col D.K → β) :
    (Enum.list (α := Col D.K)).map G = (List.finRange D.K).map (fun i => G (0, i)) ++
      (List.finRange D.K).map (fun i => G (1, i)) := by
  rw [enum_prod, map_product]
  show ((List.finRange 2).map _).flatten = _
  simp [List.finRange_succ]
  rfl

/-! ### `H⁽²⁾` -/

theorem h2W_eq (σ : RawSec D) :
    h2W σ = ((List.range (D.b * 2)).map (hblk D.K (F0 σ) (F1 σ))).flatten := by
  rw [h2W, fun_enc_eq, enum_jh, List.map_map, range_map_eq]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  rw [Function.comp_apply, vecE_enc_eq, enum_col_map, List.flatten_append, hblk,
    range_map_eq, range_map_eq]
  congr 2
  · refine List.map_congr_left fun i _ => ?_
    simp [F0, j.isLt, i.isLt]
  · refine List.map_congr_left fun i _ => ?_
    simp [F1, j.isLt, i.isLt]

/-! ### The words of the helpers -/

theorem G1_zero (i : Fin D.K) : (setting D).G 1 (0, i) = 0 := by
  rw [G_apply]; simp

theorem G1_one (i : Fin D.K) : (setting D).G 1 (1, i) = 2 ^ (i : ℕ) := by
  rw [G_apply, ite_eq_left_iff.mpr (fun h => absurd rfl h)]
  show algebraMap (ZMod D.q) (Rg D) (2 ^ (i : ℕ)) = _
  rw [map_pow, map_ofNat]

theorem helperE_eq (j : Fin (D.b * 2)) :
    helperE D ⟨j.val, by rw [show (circParamsD D).J.length = D.b * 2 from length_jList D]; exact j.isLt⟩ =
      jhE D j := rfl

theorem getD_vs (i : CInst D) (n : ℕ) (hn : D.mb + D.K + 1 + n < (vsV i).length) :
    ((vsV i).drop (D.mb + D.K + 1)).getD n [] = (vsV i)[D.mb + D.K + 1 + n] := by
  rw [dgetD_drop', List.getD_eq_getElem _ _ hn]

theorem jlen : (circParamsD D).J.length = D.b * 2 := length_jList D

/-- **The words of the helpers.** -/
theorem hout_eq (σ : RawSec D) :
    ((List.range (D.b * 2)).map (hout ((vsV σ.2.1).drop (D.mb + D.K + 1)) D.K (D.b * 2)
      (D.K * (D.b * 2)) 0 (F0 σ) (F1 σ))).flatten =
    ((Enum.list (α := Jh D)).map fun k => (Enum.list (α := Col D.K)).map fun c =>
      encRM D.N D.K (σ.2.1.vH k c - (setting D).G 1 c + σ.2.2.2.1 k c)).flatten := by
  have hKp := D.K_pos
  rw [enum_jh, List.map_map, range_map_eq]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  refine Eq.trans ?_ (enum_col_map (fun c : Col D.K => encRM D.N D.K
    (σ.2.1.vH (jhE D j) c - (setting D).G 1 c + σ.2.2.2.1 (jhE D j) c))).symm
  rw [hout, outs0, outs1, range_map_eq, range_map_eq]
  have hlen : (vsV σ.2.1).length = mCirc D + D.K * (D.b * 2) := by rw [length_vsV, rows_eq]
  have hbnd : ∀ i : Fin D.K, j.val + D.b * 2 * i.val < D.K * (D.b * 2) := fun i => by
    have := Nat.mul_le_mul_left (D.b * 2) (show i.val + 1 ≤ D.K from i.isLt)
    have := j.isLt
    rw [Nat.mul_add, mul_one] at *
    rw [Nat.mul_comm D.K]; omega
  congr 1
  · refine List.map_congr_left fun i _ => ?_
    congr 1
    have hj' : j.val < (circParamsD D).J.length := by rw [jlen]; exact j.isLt
    have key := vsV_key σ.2.1 i ⟨j.val, hj'⟩ (by
      rw [hlen]; have := hbnd i; simp only [Fin.val_mk, jlen]; omega)
    rw [helperE_eq] at key
    have hidx : D.mb + D.K + 1 + (D.K * (D.b * 2) + j.val + i.val * (D.b * 2)) =
        mCirc D + (j.val + (circParamsD D).J.length * i.val) := by
      rw [jlen, mCirc]; ring
    rw [getD_vs σ.2.1 _ (by rw [hlen, mCirc]; have := hbnd i; nlinarith), ]
    simp only [hidx, key, decRM_encRM hKp, F0, j.isLt, i.isLt, and_self, dite_true, Fin.eta]
    erw [G1_zero]
    simp
  · refine List.map_congr_left fun i _ => ?_
    congr 1
    have key := vsV_ph σ.2.1 i j (by rw [hlen, mCirc]; have := hbnd i; omega)
    have hidx : D.mb + D.K + 1 + (0 + j.val + i.val * (D.b * 2)) =
        D.mb + D.K + 1 + (j.val + D.b * 2 * i.val) := by ring
    rw [getD_vs σ.2.1 _ (by rw [hlen, mCirc]; have := hbnd i; nlinarith)]
    simp only [hidx, key, decRM_encRM hKp, F1, j.isLt, i.isLt, and_self, dite_true, Fin.eta]
    erw [G1_one]
    have gen : ∀ A B C : Rg D, A + B - C = A - C + B := fun A B C => by abel
    exact gen _ _ _

end AdvancedEncryption.ExpLUT.Prog.RedChal
