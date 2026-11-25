import PE.Impl.ExpLUT.Prog.SetupP
import PE.Impl.RingBTVW.Prog.SetupTime3

/-!
# Explicit samplers of ring laws

* `χbin D`: the binary law, `0` or `1 ∈ R` with probability `1/2` each (the trapdoor `T` of
  TrapGen); `binSampler D : RingSampler D (χbin D)` is `entB` (one fair bit, then `N K − 1` zeros),
  whose word is the canonical word of the sample (`encRM_bit`).
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.XProg Cslib Cslib.Probability SigabaNeo.Lattices.Algo.NegaG
open AdvancedEncryption.RingBTVW.Prog

variable (D : Dims)

/-- **The binary law**: `0` or `1`, each with probability `1/2`. -/
noncomputable def χbin : PMF (Rg D) :=
  (BitString.uniformList 1).map fun u => if u.headD false then 1 else 0

theorem coefG_one_ring (i : ℕ) :
    coefG (1 : Rg D) i = if i = 0 then 1 else 0 := by
  rw [show (1 : Rg D) = algebraMap (ZMod D.q) (Rg D) 1 from (map_one _).symm]
  by_cases hi : i < D.N
  · rw [coefG_of_lt _ hi]
    simp only [Algebra.algebraMap_eq_smul_one, Negacyclic.coeffs_smul, one_smul]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp [Negacyclic.coeffs_one]
    · simp [Negacyclic.coeffs_one, hi0.ne']
  · rw [coefG, dif_neg hi, if_neg (by have := D.N_pos; omega)]

/-- **The canonical word of a bit.** -/
theorem encRM_bit (b : Bool) :
    encRM D.N D.K (if b then 1 else 0) = b :: List.replicate (D.N * D.K - 1) false := by
  have hK := D.K_pos
  obtain ⟨n, hn⟩ : ∃ n, D.N = n + 1 := ⟨D.N - 1, by have := D.N_pos; omega⟩
  obtain ⟨K', hK'⟩ : ∃ K', D.K = K' + 1 := ⟨D.K - 1, by omega⟩
  have hv : encM D.K (if b then 1 else 0) = b :: List.replicate K' false := by
    cases b
    · simp only [Bool.false_eq_true, if_false, encM, ZMod.val_zero]
      have := toBits_val (zeroW D.K)
      rw [length_zeroW, val_zeroW] at this
      rw [this, hK', zeroW, List.replicate_succ]
    · simp only [if_true, encM]
      have h1 : (1 : ZMod D.q).val = 1 := ZMod.val_one_eq_one_mod D.q ▸ Nat.mod_eq_of_lt D.one_lt_q
      rw [h1, hK']
      simp only [toBits, Nat.one_mod, decide_true]
      congr 1
      have : ∀ m, toBits m 0 = List.replicate m false := fun m => by
        induction m with
        | zero => rfl
        | succ m ih => simp [toBits, ih, List.replicate_succ]
      exact this K'
  unfold encRM
  rw [show (fun i => encM D.K (coefG (if b then (1 : Rg D) else 0) i)) =
      fun t => if t = 0 then encM D.K (if b then 1 else 0) else zeroW D.K from funext fun t => by
    by_cases ht : t = 0
    · subst ht; cases b <;> simp [coefG_one_ring, coefG_zero]
    · rw [if_neg ht]
      have e : coefG (if b then (1 : Rg D) else 0) t = 0 := by
        cases b <;> simp [coefG_one_ring, ht, coefG_zero]
      rw [e, encM, ZMod.val_zero]
      have := toBits_val (zeroW D.K)
      rwa [length_zeroW, val_zeroW] at this]
  rw [hn, concatN_head_zero, hv]
  simp only [List.cons_append, List.replicate_append_replicate]
  congr 2
  rw [hK']; ring_nf; omega

theorem χbin_enc : (χbin D).map (rEnc D).enc = μB D.N D.K := by
  rw [χbin, PMF.map_comp, μB, cat]
  simp only [PMF.pure_map]
  rw [← PMF.bind_pure_comp]
  refine pmf_bind_congr_support _ fun u hu => ?_
  have hl := BitString.length_of_mem_support_uniformList hu
  obtain ⟨b, rfl⟩ : ∃ b, u = [b] := by
    match u, hl with
    | [b], _ => exact ⟨b, rfl⟩
  exact congrArg PMF.pure (encRM_bit D b)

/-- **The binary sampler.** -/
noncomputable def binSampler : RingSampler D (χbin D) where
  P := entB D.N D.K
  law := (χbin_enc D) ▸ law_entB
  wf := ⟨wf_coinAp _ _, wf_zerosF _⟩
  pres6 := ⟨by simp [coinAp, XProg.Preserves, Prog.Preserves, Prim.writes], preserves_zerosF _
    (by decide)⟩
  B := bEntB D.N D.K
  atb := atbb_entB D.N D.K

end AdvancedEncryption.ExpLUT.Prog
