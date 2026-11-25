import PE.Impl.ExpLUT.Prog.UnifCanon
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.GadRow
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.MatMul

/-!
# The gadget columns of `B⁽¹⁾` on words

`B⁽¹⁾ = [Ā | g − Ā T]` (`trapRow`). On the canonical words of `Ā` (`1 × m̄`) and `T` (`m̄ × K`),
the program words compute the gadget columns: **`gadRowW_matMulMW`**,

  `gadRowW N K one (matMulMW N K 1 m̄ K Ā T) = enc (c ↦ g_c − Σ_w Ā_w T_{w,c})`,

the canonical words of the entries (`rEnc`), from the identities of `mulRMW`, `addRMW`, `subRMW`,
`rotBW` (`2^c` as `c` doublings of `1`) and `canonW_eq`.
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  Matrix Cslib

/-- A function on `Fin m`, encoded: the concatenation of the values' words. -/
theorem fun_enc_concatN {β : Type} {n : ℕ} (e : FixedEnc β n) : ∀ (m : ℕ) (f : Fin m → β),
    (FixedEnc.fun (α := Fin m) e).enc f = concatN m (fun i => if h : i < m then e.enc (f ⟨i, h⟩) else [])
  | 0, f => rfl
  | m + 1, f => by
    have ih := fun_enc_concatN e m (fun i => f i.castSucc)
    show ((List.finRange (m + 1)).map f).flatMap e.enc = _
    have hl : List.finRange (m + 1) = (List.finRange m).map Fin.castSucc ++ [Fin.last m] := by
      simp [List.finRange_succ_last]
    rw [hl, List.map_append, List.flatMap_append, concatN, List.map_map]
    rw [show ((List.finRange m).map (f ∘ Fin.castSucc)).flatMap e.enc =
      (FixedEnc.fun (α := Fin m) e).enc (fun i => f i.castSucc) from rfl, ih]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      lt_add_iff_pos_right, Nat.lt_irrefl, dif_pos (Nat.lt_succ_self m)]
    congr 1
    apply concatN_congr
    intro i hi
    rw [dif_pos hi, dif_pos (by omega)]
    rfl

variable {D : Dims}

theorem rget_vec (A : Fin D.mb → Rg D) {t : ℕ} (ht : t < D.mb) :
    rget D.N D.K t ((vecE D (Fin D.mb)).enc A) = encRM D.N D.K (A ⟨t, ht⟩) := by
  have h := FixedEnc.fun_block (α := Fin D.mb) (rEnc D) A t (by rw [len_fin]; exact ht)
  rw [Enum.getElem_fin] at h
  exact h

theorem rget_mat (T : Fin D.mb → Fin D.K → Rg D) {t c : ℕ} (ht : t < D.mb) (hc : c < D.K) :
    rget D.N D.K (t * D.K + c) ((matE D (Fin D.mb) (Fin D.K)).enc T) =
      encRM D.N D.K (T ⟨t, ht⟩ ⟨c, hc⟩) := by
  have h := fun2_block (rEnc D) D.mb D.K T ⟨t, ht⟩ ⟨c, hc⟩
  unfold rget block
  rw [show (t * D.K + c) * (D.N * D.K) = D.N * D.K * (D.K * t + c) by ring]
  exact h

theorem length_vecE_fin (m : ℕ) (A : Fin m → Rg D) :
    ((vecE D (Fin m)).enc A).length = m * (D.N * D.K) := by
  rw [FixedEnc.length, len_fin]

theorem length_matE_fin (m l : ℕ) (T : Fin m → Fin l → Rg D) :
    ((matE D (Fin m) (Fin l)).enc T).length = m * (l * (D.N * D.K)) := by
  rw [FixedEnc.length, len_fin, len_fin]

/-- The gadget entry `2^c`. -/
theorem decRM_gIt (c : ℕ) :
    decRM D.N D.K (gIt D.N D.K (true :: List.replicate (D.N * D.K - 1) false) c) =
      algebraMap (ZMod D.q) (Rg D) (2 ^ c) := by
  have hNK : 1 ≤ D.N * D.K := Nat.one_le_iff_ne_zero.mpr (by have := D.K_pos; positivity)
  have hone : (true :: List.replicate (D.N * D.K - 1) false).length = D.N * D.K := by
    simp; omega
  induction c with
  | zero =>
    rw [gIt, Function.iterate_zero_apply, decRM_one D.K_pos D.N_pos, pow_zero, map_one]
  | succ c ih =>
    rw [gIt, Function.iterate_succ_apply']
    show decRM D.N D.K (rotBW D.N D.K (D.K - 1) (gIt D.N D.K _ c)) = _
    rw [decRM_rotBW (length_gIt hone c) (show 1 ≤ D.K from D.K_pos), ih, pow_one,
      pow_succ, map_mul, Algebra.smul_def, mul_comm]

/-- **The gadget columns on words.** -/
theorem gadRowW_matMulMW (Abar : Fin D.mb → Rg D) (T : Fin D.mb → Fin D.K → Rg D) :
    gadRowW D.N D.K (true :: List.replicate (D.N * D.K - 1) false)
        (matMulMW D.N D.K 1 D.mb D.K ((vecE D (Fin D.mb)).enc Abar)
          ((matE D (Fin D.mb) (Fin D.K)).enc T)) =
      (vecE D (Fin D.K)).enc (fun c => (setting D).D.g c - ∑ w, Abar w * T w c) := by
  refine Eq.trans ?_ (fun_enc_concatN (rEnc D) D.K _).symm
  rw [gadRowW]
  apply concatN_congr
  intro c hc
  rw [dif_pos hc]
  have hlen : ∀ p < 1 * D.K, (sumLoopM D.N D.K (fun t => mulRMW D.N D.K
      (rget D.N D.K (p / D.K * D.mb + t) ((vecE D (Fin D.mb)).enc Abar))
      (rget D.N D.K (t * D.K + p % D.K) ((matE D (Fin D.mb) (Fin D.K)).enc T))) D.mb).length =
        D.N * D.K := fun p _ => length_sumLoopM _ _ _ _
  have hP : (matMulMW D.N D.K 1 D.mb D.K ((vecE D (Fin D.mb)).enc Abar)
      ((matE D (Fin D.mb) (Fin D.K)).enc T)).length = D.K * (D.N * D.K) := by
    rw [matMulMW, length_concatN hlen, one_mul]
  rw [takeD_drop_eq_block hP hc, matMulMW, block_concatN hlen, if_pos (by omega)]
  have hdiv : c / D.K = 0 := Nat.div_eq_of_lt hc
  have hmod : c % D.K = c := Nat.mod_eq_of_lt hc
  simp only [hdiv, hmod, zero_mul, zero_add]
  have hone : (true :: List.replicate (D.N * D.K - 1) false).length = D.N * D.K := by
    have : 1 ≤ D.N * D.K := Nat.one_le_iff_ne_zero.mpr (by have := D.K_pos; positivity)
    simp; omega
  rw [canonW_eq D.K_pos (length_subRMW _ _ (length_gIt hone c) _), rEnc_enc]
  congr 1
  rw [decRM_subRMW (length_gIt hone c) (length_sumLoopM _ _ _ _), decRM_gIt,
    decRM_sumLoopM (fun t _ => length_mulRMW _ _ _ _) D.mb le_rfl]
  have hg : (setting D).D.g ⟨c, hc⟩ = algebraMap (ZMod D.q) (Rg D) (2 ^ c) := rfl
  refine congrArg₂ (· - ·) hg.symm ?_
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [rget_vec Abar t.isLt, rget_mat T t.isLt hc, decRM_mulRMW (length_encRM _ _ _)
    (length_encRM _ _ _), decRM_encRM D.K_pos, decRM_encRM D.K_pos]

end AdvancedEncryption.ExpLUT.Prog
