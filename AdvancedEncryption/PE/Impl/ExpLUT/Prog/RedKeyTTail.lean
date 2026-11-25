import PE.Impl.ExpLUT.Prog.RedKeyTNum

/-!
# Module 9: the back-end certificate `RkTailCert` (cap `2^150`)

**`rkTailCert_of : RkTailIn a → RkTailCert a rkLt rkTt`** with `rkLt = 2^102 + 2^120 ≤ 2^125` and
`rkTt = 2^436 ≤ 2^449`.

The chain: `a ≤ layout Mx N K inX` (all registers `≤ 2^150`, register `14 ≤ 2^102`); coins;
candidate decoder; then the standard envelope `stdX 2^102 Mx` through `keyDigitsC`, `uC`, the two
counters and `mvSubC`; the assembly puts the key word (`≤ 2^106`) in `19`
(`stdX 2^102 2^120`), which the acceptance step keeps; packing and the VM epilogue leave
`14 ++ 19` on tape `0`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 1000
set_option maxRecDepth 100000

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyT

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Prog.KeyTime

/-! ### Envelope facts (generic, so that `simp` never meets the concrete `Dc` terms) -/

theorem candOut_keep (D : Dims) (B M : ℕ) (a : Fin 105 → ℕ) (r : Fin 64)
    (hr : r = 14 ∨ r = 19) : candOut D B M a r = a (tR r) := by
  rcases hr with rfl | rfl <;>
    simp [candOut, decodeQueueBase, candidateInitResult, templateBounds, candidateInitOps,
      natResult, initBitsResult, bitsResult, Function.update_apply, tR]

theorem candOut_consts (D : Dims) (B M : ℕ) (a : Fin 105 → ℕ) :
    candOut D B M a rB1 = 1 ∧ candOut D B M a rZ = D.N * D.K := by
  have h := candidateInitResult_constants D B M a
  refine ⟨?_, ?_⟩
  · simp only [candOut, decodeQueueBase, Function.update_apply]; simpa using h.1
  · simp only [candOut, decodeQueueBase, Function.update_apply]; simpa using h.2

theorem digits_keep (D : Dims) (M : ℕ) (b : Fin 64 → ℕ) (r : Fin 64) (hr : r = 14 ∨ r = 19) :
    digitsTailResult D M (Function.update (publicBase M b) 15 ((Enum.list
      (α := Fin (setting D).E.W)).length * (D.N * D.K))) r = b r := by
  rcases hr with rfl | rfl <;>
    simp [digitsTailResult, digitsReady, decompositionBase, decompositionScratch, targetResult,
      targetHeadResult, publicBase, publicScratch, Function.update_apply]

theorem digits_consts (D : Dims) (M : ℕ) (b : Fin 64 → ℕ) :
    digitsTailResult D M (Function.update (publicBase M b) 15 ((Enum.list
      (α := Fin (setting D).E.W)).length * (D.N * D.K))) rB1 = b rB1 ∧
    digitsTailResult D M (Function.update (publicBase M b) 15 ((Enum.list
      (α := Fin (setting D).E.W)).length * (D.N * D.K))) rZ = b rZ := by
  have h := digitsTailResult_fields D M (Function.update (publicBase M b) 15 ((Enum.list
      (α := Fin (setting D).E.W)).length * (D.N * D.K)))
  refine ⟨h.2.1.trans ?_, h.2.2.1.trans ?_⟩ <;> simp [publicBase, publicScratch]

theorem accOut_keep (D : Dims) (M B : ℕ) (b : Fin 64 → ℕ) :
    accOut D M B b rB1 = b rB1 ∧ accOut D M B b rZ = b rZ ∧ accOut D M B b 14 = b 14 ∧
    accOut D M B b 19 = max (b 19) (codecSize (keyEnc D)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [accOut, bxBase, bxScratch, acceptInitResult, radiusResult, Function.update_apply]

/-! ### The assembly at the cap -/

def asmX (NK L : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (gatherBase Mx (Function.update b 0 (b 18 + b 17)))
    4 (L * NK)) 19 (L * NK)

/-- The assembly words, generic in the dimensions and the index list. -/
theorem rktAssembleWords (N K : ℕ) (js : List ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs Mx N K (layout Mx N K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ N * K) (hs : b 18 + b 17 ≤ Mx)
    (hj : ∀ j ∈ js, j ≤ 2 ^ 66) (hl : js.length ≤ 2 ^ 66) (hNK : N * K = 2 ^ 40)
    (hg : gatherTime Mx N K (2 ^ 66) js.length ≤ 2 ^ 372) :
    Cert (MVM.compile (.seq (.cp 0 18) (.seq (.app 0 17)
      (saveQueueC (gatherC N K js) 19)))) (layout Mx N K b)
      (layout Mx N K (asmX (N * K) js.length b)) (2 ^ 373) := by
  let c := Function.update b 0 (b 18)
  have hc := h.update_layout 0 (b 18) (by simpa using h.top (tR 18))
  have p0 := layout_copy_update Mx N K b h.top 0 18
  have p1 := layout_append_uniform Mx N K c hc.top 0 17 (by simpa [c] using hs)
  have he : Function.update c 0 (c 0 + c 17) = Function.update b 0 (b 18 + b 17) := by simp [c]
  rw [he] at p1
  have ha : RingInputs Mx N K (layout Mx N K (Function.update b 0 (b 18 + b 17))) :=
    h.update_layout 0 _ hs
  have hlen : js.length * (N * K) ≤ Mx :=
    (Nat.mul_le_mul_right _ hl).trans (by rw [hNK]; norm_num)
  have p2 := compile_gatherC Mx N K (2 ^ 66) js _ ha (by simpa using hb) (by simpa using hz)
    (by rw [hNK]; norm_num) hj hlen
  have hgi := (gatherBase_inputs _ _ _ _ ha).update_layout 4 _ hlen
  have p3 := layout_copy_update Mx N K _ hgi.top 19 4
  simp only [Function.update_self] at p3
  have all := p0.seq (p1.seq ((p2.mono le_rfl le_rfl hg).seq p3))
  have hnum : 2 * Mx + 5 + (appendAllowance Mx + (2 ^ 372 + (2 * Mx + 5))) ≤ (2 : ℕ) ^ 373 := by
    norm_num [appendAllowance]
  exact all.mono le_rfl le_rfl hnum

theorem rktAssembleC (b : Fin 64 → ℕ) (h : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K) (hs : b 18 + b 17 ≤ Mx) :
    Cert (MVM.compile (assembleC Dc)) (layout Mx Dc.N Dc.K b)
      (layout Mx Dc.N Dc.K (asmX (Dc.N * Dc.K) (assemblyIndices Dc).length b)) (2 ^ 373) := by
  rw [assembleC_eq]
  exact rktAssembleWords Dc.N Dc.K (assemblyIndices Dc) b h hb hz hs assemblyIndices_bounds.1
    assemblyIndices_bounds.2 rkNK (gT_le _ assemblyIndices_bounds.2)

/-! ### The input envelope -/

/-- The register bounds of the input: `14 ≤ 2^102`, the rest at the cap. -/
def inX (r : Fin 64) : ℕ := if r = 14 then 2 ^ 102 else Mx

theorem inX_inputs : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K inX) := by
  apply layout_inputs
  · intro r; unfold inX; split_ifs <;> norm_num
  · rw [rkNK]; norm_num
  · rw [rkN]; norm_num
  · rw [rkK]; norm_num

theorem le_inX {a : Fin 105 → ℕ} (h : RkTailIn a) : a ≤ layout Mx Dc.N Dc.K inX := by
  apply le_layout Mx Dc.N Dc.K inX a h.top h.templateK h.templateN h.zeros h.ones
  intro r
  unfold inX
  split_ifs with hr
  · subst hr; exact h.mpk
  · exact h.top _

end AdvancedEncryption.ExpLUT.Prog.RedKeyT
