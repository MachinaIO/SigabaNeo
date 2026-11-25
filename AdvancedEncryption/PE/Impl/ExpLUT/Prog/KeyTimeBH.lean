import PE.Impl.ExpLUT.Prog.KeyTimeGatherAut

/-! Actual public-key prefix loading and B/H coefficient generation. -/
set_option exponentiation.threshold 1000

namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib

open Classical in
noncomputable def bhIndices (D : Dims) : List ℕ := Enum.list.map (Enum.index ∘ bhSelection D)

theorem bhIndices_length (D : Dims) : (bhIndices D).length = (Enum.list (α := BHRow D)).length := by
  simp [bhIndices]

theorem bhIndices_bound (D : Dims) (I : ℕ)
    (hi : (Enum.list (α := BHSource D)).length ≤ I) : ∀ j ∈ bhIndices D, j ≤ I := by
  intro j hj
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hj
  exact (Enum.index_lt (bhSelection D x)).le.trans hi

noncomputable def bhResult (D : Dims) (M i : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  gatherAutResult M D.N D.K (rowExponent D i) (bhIndices D) (prefixResult (bhPrefixLength D) b)

noncomputable def bhTime (D : Dims) (M I i : ℕ) :=
  prefixTime M (bhPrefixLength D) +
    (gatherTime M D.N D.K I (bhIndices D).length +
      autGatheredTime M D.N D.K (bhIndices D).length (rowExponent D i))

theorem compile_mpkBHC (D : Dims) (M I i : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b)) (hb : b rB1 = 1)
    (hz : b rZ ≤ D.N * D.K) (hx : b rZ ≤ b rQx) (hy : D.N * D.K ≤ b rQy)
    (hsrc : (Enum.list (α := BHSource D)).length ≤ I)
    (hi : I * (D.N * D.K) ≤ M) (hn : (bhIndices D).length ≤ M)
    (hk : rowExponent D i ≤ M) (hs : 2 * ((bhIndices D).length * (D.N * D.K)) ≤ M) :
    Cert (MVM.compile (mpkBHC D i)) (layout M D.N D.K b)
      (layout M D.N D.K (bhResult D M i b)) (bhTime D M I i) := by
  have hpref : bhPrefixLength D ≤ M := (Nat.mul_le_mul_right (D.N * D.K) hsrc).trans hi
  let c := prefixResult (bhPrefixLength D) b
  have hc := prefixResult_inputs M D.N D.K _ b h hpref
  have p0 := compile_prefixC M D.N D.K _ b h hb hpref
  have p1 := compile_gatherAutC M D.N D.K I (rowExponent D i) (bhIndices D) c hc
    (by simpa [c, prefixResult] using hb) (by simpa [c, prefixResult] using hz)
    (by simpa [c, prefixResult] using hx) (by simpa [c, prefixResult] using hy)
    hi (bhIndices_bound D I hsrc) hn hk hs
  exact p0.seq p1

theorem bhResult_inputs (D : Dims) (M i : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b)) (hp : bhPrefixLength D ≤ M)
    (hn : (bhIndices D).length ≤ M) (hk : rowExponent D i ≤ M)
    (hs : 2 * ((bhIndices D).length * (D.N * D.K)) ≤ M) :
    RingInputs M D.N D.K (layout M D.N D.K (bhResult D M i b)) :=
  gatherAutResult_inputs M D.N D.K _ _ _ (prefixResult_inputs M D.N D.K _ b h hp) hn hk hs

theorem bhResult_length (D : Dims) (M i : ℕ) (b : Fin 64 → ℕ) :
    bhResult D M i b 4 = 2 * ((bhIndices D).length * (D.N * D.K)) :=
  gatherAutResult_length _ _ _ _ _ _

theorem bhResult_other (D : Dims) (M i : ℕ) (b : Fin 64 → ℕ) (r : Fin 64)
    (hr : r ∉ [0, 1, 2, 3, 4, rQa, rQc, rQk]) : bhResult D M i b r = b r := by
  have hn (s : Fin 64) (hs : s ∈ [0, 1, 2, 3, 4, rQa, rQc, rQk]) : r ≠ s :=
    fun he ↦ hr (he.symm ▸ hs)
  unfold bhResult
  rw [gatherAutResult_other]
  · simp [prefixResult, Function.update_of_ne (hn 0 (by simp)),
      Function.update_of_ne (hn 2 (by simp)), Function.update_of_ne (hn 3 (by simp))]
  · intro hm; apply hr
    simp only [List.mem_cons] at hm ⊢
    tauto

theorem bh_bounds_Dc (i : ℕ) :
    bhPrefixLength Dc ≤ 2 ^ 120 ∧ (bhIndices Dc).length ≤ 2 ^ 66 ∧
    rowExponent Dc i ≤ 2 ^ 25 ∧ 2 * ((bhIndices Dc).length * (Dc.N * Dc.K)) ≤ 2 ^ 120 := by
  have hsrc := publicSizeInputs_Dc.source
  have hrow : (bhIndices Dc).length ≤ 2 ^ 66 := by rw [bhIndices_length]; exact publicSizeInputs_Dc.rows
  have hn : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
  have hk : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
  refine ⟨?_, hrow, ?_, ?_⟩
  · exact (Nat.mul_le_mul_right (Dc.N * Dc.K) hsrc).trans (by rw [hn, hk]; norm_num)
  · exact (rowExponent_lt Dc i).le.trans (by rw [hn]; norm_num)
  · exact (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right (Dc.N * Dc.K) hrow)).trans
      (by rw [hn, hk]; norm_num)

set_option exponentiation.threshold 1000 in
theorem bhTime_Dc (i : ℕ) : bhTime Dc (2 ^ 120) (2 ^ 66) i ≤ 2 ^ 415 := by
  have hb := bh_bounds_Dc i
  have hp := prefixTime_concrete _ hb.1
  have hg : gatherTime (2 ^ 120) Dc.N Dc.K (2 ^ 66) (bhIndices Dc).length +
      autGatheredTime (2 ^ 120) Dc.N Dc.K (bhIndices Dc).length (rowExponent Dc i) ≤ 2 ^ 414 := by
    have hn : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
    have hk : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
    rw [hn, hk]
    exact gatherAutTime_concrete _ _ hb.2.1 hb.2.2.1
  exact (Nat.add_le_add hp hg).trans (by norm_num)

theorem compile_mpkBHC_Dc (i : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b)) (hb : b rB1 = 1)
    (hz : b rZ ≤ Dc.N * Dc.K) (hx : b rZ ≤ b rQx) (hy : Dc.N * Dc.K ≤ b rQy) :
    Cert (MVM.compile (mpkBHC Dc i)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (bhResult Dc (2 ^ 120) i b)) (2 ^ 415) := by
  have hs := bh_bounds_Dc i
  exact (compile_mpkBHC Dc (2 ^ 120) (2 ^ 66) i b h hb hz hx hy publicSizeInputs_Dc.source
    (by norm_num [Dc, Dims.N, Params.en, Params.Kc])
    (hs.2.1.trans (by norm_num)) (hs.2.2.1.trans (by norm_num)) hs.2.2.2).mono
      le_rfl le_rfl (bhTime_Dc i)

open Classical in
noncomputable def positiveResult (D : Dims) (M : ℕ) (i : Fin (setting D).E.W)
    (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  appendAFResult D.N D.K (decide (i = (setting D).row0))
    (Function.update (bhResult D M i.val b) 0 (b 8))

theorem compile_positiveCoeffC_Dc (i : Fin (setting Dc).E.W) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b)) (hb : b rB1 = 1)
    (hz : b rZ ≤ Dc.N * Dc.K) (hx : b rZ ≤ b rQx) (hy : Dc.N * Dc.K ≤ b rQy) :
    Cert (MVM.compile (positiveCoeffC Dc i)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (positiveResult Dc (2 ^ 120) i b)) (2 ^ 416) := by
  classical
  let c := bhResult Dc (2 ^ 120) i.val b
  let d := Function.update c 0 (b 8)
  have hn : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
  have hk : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
  have bounds := bh_bounds_Dc i.val
  have hc := bhResult_inputs Dc (2 ^ 120) i.val b h bounds.1
    (bounds.2.1.trans (by norm_num)) (bounds.2.2.1.trans (by norm_num)) bounds.2.2.2
  have hd := hc.update_layout 0 _ (by simpa using h.top (tR 8))
  have hs : d 4 + (2 * Dc.K) * (Dc.N * Dc.K) ≤ 2 ^ 120 := by
    have he : d 4 = 2 * ((bhIndices Dc).length * (Dc.N * Dc.K)) := by
      simpa only [d, Function.update_of_ne (by decide : (4 : Fin 64) ≠ 0)] using bhResult_length Dc (2 ^ 120) i.val b
    rw [he]
    calc
      _ ≤ 2 * (2 ^ 66 * (Dc.N * Dc.K)) + (2 * Dc.K) * (Dc.N * Dc.K) := by
        gcongr; exact bounds.2.1
      _ ≤ 2 ^ 120 := by rw [hn, hk]; norm_num
  have p0 := compile_mpkBHC_Dc i.val b h hb hz hx hy
  have p1 := layout_copy_update (2 ^ 120) Dc.N Dc.K c hc.top 0 8
  have h8 : c 8 = b 8 := bhResult_other Dc (2 ^ 120) i.val b 8 (by decide)
  rw [h8] at p1
  have hbit : d rB1 = 1 := by
    simp only [d, Function.update_of_ne (by decide : rB1 ≠ 0)]
    exact (bhResult_other Dc (2 ^ 120) i.val b rB1 (by decide)).trans hb
  have p2 := compile_appendAFC (2 ^ 120) Dc.N Dc.K (decide (i = (setting Dc).row0)) d hd hbit hs
  have ht : appendAFTime (2 ^ 120) Dc.N Dc.K ≤ 2 ^ 246 := by
    rw [hn, hk]; exact appendAFTime_concrete
  have hp2 := p2.mono le_rfl le_rfl ht
  have htime : 2 ^ 415 + ((2 * 2 ^ 120 + 5) + 2 ^ 246) ≤ (2 ^ 416 : ℕ) := by
    norm_num [Nat.pow_succ]
  exact (p0.seq (p1.seq hp2)).mono le_rfl le_rfl htime

theorem positiveResult_length (D : Dims) (M : ℕ) (i : Fin (setting D).E.W)
    (b : Fin 64 → ℕ) : positiveResult D M i b 4 =
      2 * ((bhIndices D).length * (D.N * D.K)) + (2 * D.K) * (D.N * D.K) := by
  classical
  unfold positiveResult
  rw [appendAFResult_length]
  simp only [Function.update_of_ne (by decide : (4 : Fin 64) ≠ 0), bhResult_length]

theorem positiveResult_inputs (D : Dims) (M : ℕ) (i : Fin (setting D).E.W) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b)) (hp : bhPrefixLength D ≤ M)
    (hn : (bhIndices D).length ≤ M) (hk : rowExponent D i.val ≤ M)
    (hs : 2 * ((bhIndices D).length * (D.N * D.K)) + (2 * D.K) * (D.N * D.K) ≤ M) :
    RingInputs M D.N D.K (layout M D.N D.K (positiveResult D M i b)) := by
  classical
  have hc := bhResult_inputs D M i.val b h hp hn hk (by omega)
  apply appendAFResult_inputs
  · exact hc.update_layout 0 _ (by simpa using h.top (tR 8))
  · simpa only [Function.update_of_ne (by decide : (4 : Fin 64) ≠ 0), bhResult_length] using hs

theorem positiveResult_other (D : Dims) (M : ℕ) (i : Fin (setting D).E.W)
    (b : Fin 64 → ℕ) (r : Fin 64) (hr : r ∉ [0, 1, 2, 3, 4, 6, rQa, rQc, rQk]) :
    positiveResult D M i b r = b r := by
  classical
  have hn (s : Fin 64) (hs : s ∈ [0, 1, 2, 3, 4, 6, rQa, rQc, rQk]) : r ≠ s :=
    fun he ↦ hr (he.symm ▸ hs)
  unfold positiveResult
  rw [appendAFResult_other _ _ _ _ r (hn 0 (by simp)) (hn 2 (by simp))
    (hn 3 (by simp)) (hn 4 (by simp)) (hn 6 (by simp)), Function.update_of_ne (hn 0 (by simp))]
  apply bhResult_other
  intro hm; apply hr
  simp only [List.mem_cons, List.mem_singleton] at hm ⊢
  tauto

end AdvancedEncryption.ExpLUT.Prog.KeyTime
