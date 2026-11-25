import PE.Impl.ExpLUT.Prog.RedKeyTMain
import PE.Impl.ExpLUT.Prog.KeyTimeCorrection
/-!
# KeyGen: a tight certificate for the real-trapdoor correction `correctionC`

F3 (`KeyTime.compile_correctionC_Dc`, `≤ 2^484`) charges every coordinate's `autDotC` with the
queue length cap `2^66` and every ring instruction with the counter cap `M`. Here (generic in
`D`, `M`, index cap `I`):

* `tAutDotC`: the queue automorphism and the inner product with RedKeyT's tight kernels
  (`rktAutQC`, `rktIpC`), the actual length `R = K` and exponent bound `k = 2 N`;
* `tCorrectionInlC`, `tCorrectionCoordC`, `tCorrectionStep`, `tCorrectionAppendC`;
* **`tCorrectionC`**: `layout b → layout (update (correctionBase M b) 18 (|PIdx| · N K))`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 1000
set_option maxRecDepth 100000

namespace AdvancedEncryption.ExpLUT.Prog.KeyTight

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Prog.KeyTime
open AdvancedEncryption.ExpLUT.Prog.RedKeyT (autQT ipT rktAutQC rktIpC)

/-! ### `autDotC` -/

def tAutDotT (M N K R k : ℕ) : ℕ := 2 * (2 * M + 5) + autQT M N K k R + ipT M N K R

theorem tAutDotC (M N K R k : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : QueueArithmeticCaps N K b)
    (hz0 : b rZ ≤ N * K) (hr : b rQc ≤ R) (hk : b rQk ≤ k) (hs : b rQa + R * (N * K) ≤ M) :
    Cert (MVM.compile autDotC) (layout M N K b)
      (layout M N K (autDotResult N K R b)) (tAutDotT M N K R k) := by
  let c := Function.update b 56 (b rQc)
  let d := autDotResult N K R b
  have hic : RingInputs M N K (layout M N K c) :=
    h.update_layout 56 _ (by simpa using h.top (tR rQc))
  have hid : RingInputs M N K (layout M N K d) := hic.update_layout rQa _ hs
  have p0 := layout_copy_update M N K b h.top 56 rQc
  have p1 := rktAutQC M N K k R c hic (by simpa [c] using hc.zeroX)
    (by simpa [c] using hc.y) (by simpa [c] using hk) (by simpa [c] using hr)
    (by simpa [c] using hs)
  have p2 := layout_copy M N K d hid.top rQc 56 (by simp [d, autDotResult])
  have hcd : QueueArithmeticCaps N K d := by
    constructor
    · simpa [d, autDotResult] using hc.x
    · simpa [d, autDotResult] using hc.y
    · simpa [d, autDotResult] using hc.acc
    · simpa [d, autDotResult] using hc.zeroX
    · simpa [d, autDotResult] using hc.zeroY
  have p3 := rktIpC M N K R d hid hcd (by simpa [d, autDotResult] using hz0)
    (by simpa [d, autDotResult] using hr)
  rw [autDotC]
  exact (p0.seq (p1.seq (p2.seq p3))).mono le_rfl le_rfl (by unfold tAutDotT; omega)

/-! ### One trapdoor coordinate -/

def tInlT (D : Dims) (M I e : ℕ) : ℕ :=
  3 * (2 * (2 * M + 5)) + 2 * gatherTime M D.N D.K I D.K + gatherTime M D.N D.K I 1 +
    ((32 * D.K + 4) * (2 * M + 5) + ((32 * e + 4) * (2 * M + 5) +
      tAutDotT M D.N D.K D.K (2 * D.N)))

theorem tCorrectionInlC (D : Dims) (M I : ℕ)
    (i : Fin (setting D).E.W) (row : Wb D) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ D.N * D.K)
    (hx : D.N * D.K ≤ b rQx) (hy : D.N * D.K ≤ b rQy)
    (hi : I * (D.N * D.K) ≤ M) (hk : 2 * (D.K * (D.N * D.K)) ≤ M)
    (he : rowExponent D i.val ≤ M)
    (hT : (Enum.list (α := Wb D × Fin D.K)).length ≤ I)
    (hZ : (Enum.list (α := ZIdx (setting D).τ (setting D).E.W)).length ≤ I)
    (hP : (Enum.list (α := PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W)).length ≤ I) :
    Cert (MVM.compile (correctionInlC D i row)) (layout M D.N D.K b)
      (layout M D.N D.K (correctionInlResult D M i row b))
      (tInlT D M I (rowExponent D i.val)) := by
  let c := correctionLoadResult D M i row b
  let d := Function.update c rQc D.K
  let e := correctionReady D M i row b
  have hc := correctionLoadResult_inputs D M i row b h (by omega)
  have hd := hc.update_layout rQc D.K h.width
  have he' := hd.update_layout rQk (rowExponent D i.val) he
  have hcB : c rB1 = 1 := (correctionLoadResult_other D M i row b rB1 (by decide)).trans hb
  have keep (r : Fin 64) (hr : r ∉ [0, 1, 2, 3, 4, rQa, rQb, rIa, rQc, rQk]) :
      e r = b r := by
    have hrc : r ≠ rQc := fun heq ↦ hr (by simp [heq])
    have hrk : r ≠ rQk := fun heq ↦ hr (by simp [heq])
    simp only [e, correctionReady, Function.update_of_ne hrc, Function.update_of_ne hrk]
    apply correctionLoadResult_other
    intro hm; apply hr
    simp only [List.mem_cons] at hm ⊢
    tauto
  have lengths := correctionLoadResult_lengths D M i row b
  have caps : QueueArithmeticCaps D.N D.K e := by
    constructor
    · rw [keep rQx (by decide)]; exact hx
    · rw [keep rQy (by decide)]; exact hy
    · simp only [e, correctionReady, Function.update_of_ne (show rIa ≠ rQk by decide),
        Function.update_of_ne (show rIa ≠ rQc by decide)]
      exact lengths.2.2.ge
    · rw [keep rZ (by decide), keep rQx (by decide)]; exact hz.trans hx
    · rw [keep rZ (by decide), keep rQy (by decide)]; exact hz.trans hy
  have p0 := compile_correctionLoadC D M I i row b h hb hz hi (by omega) hT hZ hP
  have p1 := layout_nat_update M D.N D.K c hc rQc rB1 (by decide) D.K hcB h.width
  have p2 := layout_nat_update M D.N D.K d hd rQk rB1 (by decide) (rowExponent D i.val)
    (by simpa [d] using hcB) he
  have p3 := tAutDotC M D.N D.K D.K (2 * D.N) e he' caps
    (by rw [keep rZ (by decide)]; exact hz)
    (by simp [e, correctionReady])
    (by simp [e, correctionReady]; exact (rowExponent_lt D i.val).le)
    (by
      simp only [e, correctionReady, Function.update_of_ne (show rQa ≠ rQk by decide),
        Function.update_of_ne (show rQa ≠ rQc by decide), lengths.1]
      omega)
  rw [correctionInlC]
  exact (p0.seq (p1.seq (p2.seq p3))).mono le_rfl le_rfl (by unfold tInlT; omega)

/-- The uniform per-coordinate time. -/
def tCoordT (D : Dims) (M I : ℕ) : ℕ :=
  tInlT D M I (2 * D.N) + (2 * (2 * M + 5) + gatherTime M D.N D.K I 1)

theorem tInlT_le (D : Dims) (M I e : ℕ) (he : e ≤ 2 * D.N) :
    tInlT D M I e ≤ tCoordT D M I := by
  have : (32 * e + 4) * (2 * M + 5) ≤ (32 * (2 * D.N) + 4) * (2 * M + 5) :=
    Nat.mul_le_mul_right _ (by omega)
  unfold tCoordT tInlT
  omega

theorem tCorrectionCoordC (D : Dims) (M I : ℕ)
    (q : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ D.N * D.K)
    (hx : D.N * D.K ≤ b rQx) (hy : D.N * D.K ≤ b rQy)
    (hi : I * (D.N * D.K) ≤ M) (hk : 2 * (D.K * (D.N * D.K)) ≤ M) (hN : 2 * D.N ≤ M)
    (hT : (Enum.list (α := Wb D × Fin D.K)).length ≤ I)
    (hZ : (Enum.list (α := ZIdx (setting D).τ (setting D).E.W)).length ≤ I)
    (hP : (Enum.list (α := PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W)).length ≤ I) :
    Cert (MVM.compile (correctionCoordC D q)) (layout M D.N D.K b)
      (layout M D.N D.K (correctionCoordResult D M q b)) (tCoordT D M I) := by
  classical
  let : DecidableEq (PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W) := Classical.decEq _
  rcases q with ⟨i, row⟩ | q
  · have hl := (rowExponent_lt D i.val).le
    exact (tCorrectionInlC D M I i row b h hb hz hx hy hi hk (hl.trans hN) hT hZ hP).mono
      le_rfl le_rfl (tInlT_le D M I _ hl)
  · let js := [Enum.index (.inr q : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W)]
    have hp := compile_loadFamilyC M D.N D.K I js 9 rIa b h hb hz hi
      (by intro j hj; simp only [js, List.mem_singleton] at hj; subst j
          exact (Enum.index_lt _).le.trans hP)
      (by simpa [js] using h.ring)
    have ht : 2 * (2 * M + 5) + gatherTime M D.N D.K I js.length ≤ tCoordT D M I := by
      simp only [js, List.length_singleton, tCoordT]; omega
    simpa only [correctionCoordC, correctionCoordResult, js, index_classical] using
      hp.mono le_rfl le_rfl ht

/-! ### The traversal -/

theorem tCorrectionCoordResult_le (D : Dims) (M : ℕ) (q : PIdxD D) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b))
    (hk : 2 * (D.K * (D.N * D.K)) ≤ M) (he : 2 * D.N ≤ M)
    (hs : ∀ r ∈ correctionScratch, b r = M) :
    correctionCoordResult D M q b ≤ b := by
  have hi := correctionCoordResult_inputs D M q b h hk he
  intro r
  by_cases hr : r ∈ correctionScratch
  · rw [hs r hr]; simpa using hi.top (tR r)
  · exact (correctionCoordResult_other D M q b r hr).le

def tStepT (D : Dims) (M I : ℕ) : ℕ := tCoordT D M I + appendAllowance M

theorem tCorrectionStep (D : Dims) (M I : ℕ) (q : PIdxD D) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ D.N * D.K)
    (hx : D.N * D.K ≤ b rQx) (hy : D.N * D.K ≤ b rQy)
    (hw : ∀ r ∈ correctionScratch, b r = M)
    (hs : b 18 + D.N * D.K ≤ M)
    (hi : I * (D.N * D.K) ≤ M) (hk : 2 * (D.K * (D.N * D.K)) ≤ M) (hN : 2 * D.N ≤ M)
    (hT : (Enum.list (α := Wb D × Fin D.K)).length ≤ I)
    (hZ : (Enum.list (α := ZIdx (setting D).τ (setting D).E.W)).length ≤ I)
    (hP : (Enum.list (α := PIdxD D)).length ≤ I) :
    Cert (MVM.compile (.seq (correctionCoordC D q) (.app 18 rIa)))
      (layout M D.N D.K b)
      (layout M D.N D.K (Function.update b 18 (b 18 + D.N * D.K))) (tStepT D M I) := by
  let c := correctionCoordResult D M q b
  have hi' := correctionCoordResult_inputs D M q b h hk hN
  have ho : c 18 = b 18 := correctionCoordResult_other D M q b 18 (by decide)
  have ha : c rIa = D.N * D.K := correctionCoordResult_acc D M q b
  have p0 := tCorrectionCoordC D M I q b h hb hz hx hy hi hk hN hT hZ hP
  have p1 := layout_append_uniform M D.N D.K c hi'.top 18 rIa (by rw [ho, ha]; exact hs)
  have hl := tCorrectionCoordResult_le D M q b h hk hN hw
  apply (p0.seq p1).mono le_rfl _ le_rfl
  apply layout_mono
  intro r
  by_cases hr : r = 18
  · subst r; simp only [Function.update_self, ho, ha]; exact le_rfl
  · simp only [Function.update_of_ne hr]; exact hl r

theorem tCorrectionAppendC (D : Dims) (M I : ℕ) (qs : List (PIdxD D)) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ D.N * D.K)
    (hx : D.N * D.K ≤ b rQx) (hy : D.N * D.K ≤ b rQy)
    (hw : ∀ r ∈ correctionScratch, b r = M)
    (hs : b 18 + qs.length * (D.N * D.K) ≤ M)
    (hi : I * (D.N * D.K) ≤ M) (hk : 2 * (D.K * (D.N * D.K)) ≤ M) (hN : 2 * D.N ≤ M)
    (hT : (Enum.list (α := Wb D × Fin D.K)).length ≤ I)
    (hZ : (Enum.list (α := ZIdx (setting D).τ (setting D).E.W)).length ≤ I)
    (hP : (Enum.list (α := PIdxD D)).length ≤ I) :
    Cert (MVM.compile (correctionAppendC D qs)) (layout M D.N D.K b)
      (layout M D.N D.K (Function.update b 18 (b 18 + qs.length * (D.N * D.K))))
      (qs.length * tStepT D M I + (2 * M + 5)) := by
  induction qs generalizing b with
  | nil =>
    simpa [correctionAppendC] using (compile_nop (layout M D.N D.K b)
      M h.top).mono le_rfl le_rfl (show 2 * (M + 1) + 3 ≤ 2 * M + 5 by omega)
  | cons q qs ih =>
    have hs0 : b 18 + D.N * D.K ≤ M := by
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hs; omega
    have p0 := tCorrectionStep D M I q b h hb hz hx hy hw hs0 hi hk hN hT hZ hP
    let c := Function.update b 18 (b 18 + D.N * D.K)
    have hc := h.update_layout 18 _ hs0
    have p1 := ih c hc (by simpa [c] using hb) (by simpa [c] using hz)
      (by simpa [c] using hx) (by simpa [c] using hy)
      (by intro r hr
          have hn : r ≠ 18 := by intro he; subst r; norm_num [correctionScratch] at hr
          simpa [c, Function.update_of_ne hn] using hw r hr)
      (by simpa [c, List.length_cons, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using hs)
    have he : Function.update c 18 (c 18 + qs.length * (D.N * D.K)) =
        Function.update b 18 (b 18 + (q :: qs).length * (D.N * D.K)) := by
      simp [c, List.length_cons, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    rw [he] at p1
    exact (p0.seq p1).seq_assoc.mono le_rfl le_rfl
      (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega)

/-- **The complete real-trapdoor correction** (tight). -/
theorem tCorrectionC (D : Dims) (M I : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ D.N * D.K)
    (hx : D.N * D.K ≤ b rQx) (hy : D.N * D.K ≤ b rQy)
    (hs : (Enum.list (α := PIdxD D)).length * (D.N * D.K) ≤ M)
    (hi : I * (D.N * D.K) ≤ M) (hk : 2 * (D.K * (D.N * D.K)) ≤ M) (hN : 2 * D.N ≤ M)
    (hT : (Enum.list (α := Wb D × Fin D.K)).length ≤ I)
    (hZ : (Enum.list (α := ZIdx (setting D).τ (setting D).E.W)).length ≤ I)
    (hP : (Enum.list (α := PIdxD D)).length ≤ I) :
    Cert (MVM.compile (correctionC D)) (layout M D.N D.K b)
      (layout M D.N D.K (Function.update (correctionBase M b) 18
        ((Enum.list (α := PIdxD D)).length * (D.N * D.K))))
      ((2 * M + 5) + ((Enum.list (α := PIdxD D)).length * tStepT D M I + (2 * M + 5))) := by
  let c := correctionBase M b
  have hc := correctionBase_inputs M D.N D.K b h
  have p0 := layout_clear_update M D.N D.K c hc.top 18
  have p1 := tCorrectionAppendC D M I Enum.list (Function.update c 18 0)
    (hc.update_layout 18 0 (by omega))
    (by simpa [c, correctionBase, correctionScratch] using hb)
    (by simpa [c, correctionBase, correctionScratch] using hz)
    (by simpa [c, correctionBase, correctionScratch] using hx)
    (by simpa [c, correctionBase, correctionScratch] using hy)
    (by intro r hr
        have hn : r ≠ 18 := by intro he; subst r; norm_num [correctionScratch] at hr
        simp [Function.update_of_ne hn, c, correctionBase, hr])
    (by simpa using hs) hi hk hN hT hZ hP
  simp only [Function.update_self, zero_add, cap_reset] at p1
  rw [correctionC]
  exact (p0.seq p1).mono (layout_mono _ _ _ (le_correctionBase _ _ _ b h)) le_rfl le_rfl

end AdvancedEncryption.ExpLUT.Prog.KeyTight
