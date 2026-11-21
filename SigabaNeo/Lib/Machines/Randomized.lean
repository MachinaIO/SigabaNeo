import SigabaNeo.Lib.Machines.Guarded
import SigabaNeo.Lib.Machines.FromPTM
import CslibFrontier.Computability.Probabilistic.Time
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.PairSampler
import CslibFrontier.Languages.Probabilistic.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Guarded randomized algorithms

A randomized algorithm that draws `m` fair coins `w` and outputs `G (a, w)`, guarded by the length
of its input: on inputs at most `L` long its output law is `G (a, ·)` over uniform `w`, on longer
inputs it outputs `d` (`Machine.exists_randomized`). One constant clock bounds every run:

1. a guarded deterministic phase writes `some a` (or `none` on long inputs), padded by `m` cells;
2. cslib's `pairSampler` replaces the padding by `m` fresh coins;
3. a guarded deterministic phase computes `G` (or `d`).
-/

namespace SigabaNeo

open Turing Turing.MultiTapeTM Cslib Cslib.Probability

/-- A framed word padded by `m` cells. -/
def padEnc {γ : Type} (enc : γ ↪ List Bool) (m : ℕ) : γ ↪ List Bool :=
  ⟨fun b => frame (enc b) ++ List.replicate m true, fun _ _ h =>
    enc.injective (frame_append_inj h).1⟩

theorem length_padEnc {γ : Type} (enc : γ ↪ List Bool) (m : ℕ) (b : γ) :
    (padEnc enc m b).length = 2 * (enc b).length + 1 + m := by
  show (frame (enc b) ++ List.replicate m true).length = _
  simp [length_frame]

/-- `pairSampler` replaces the padding by `m` fresh coins. -/
theorem computesInTimeOn_pairSampler {γ : Type} (enc : γ ↪ List Bool) (m : ℕ) :
    ComputesInTimeOn (padEnc enc m) (encPair enc encBits)
      (fun b => (padEnc enc m b).length + 1)
      (fun b => (fun w => (b, w)) <$> BitString.sampleList m) := by
  refine ⟨0, MultiTapePTM.PairSampler.Phase, inferInstance, MultiTapePTM.pairSampler, fun b => ⟨?_, ?_⟩⟩
  · have h := MultiTapePTM.eval_pairSampler (enc b) (List.replicate m true)
    simp only [List.length_replicate] at h
    change _ = (MultiTapePTM.pairSampler.runClosed
      ((frame (enc b) ++ List.replicate m true).length + 1)
      (frame (enc b) ++ List.replicate m true)).eval
    rw [h, ProbComp.eval_map, BitString.eval_sampleList, PMF.map_comp]
    rfl
  · exact MultiTapePTM.pairSampler_halted (enc b) (List.replicate m true)

theorem PMF.map_congr_support {α β : Type*} (p : PMF α) {f g : α → β}
    (h : ∀ a ∈ p.support, f a = g a) : p.map f = p.map g := by
  ext b
  simp only [PMF.map_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [(PMF.apply_eq_zero_iff p a).mpr ha]; simp

/-- **The machine of a guarded randomized algorithm**: on inputs at most `L` long, the law of
`G (a, w)` over `m` fair coins `w`; on longer inputs, `d`. -/
theorem Machine.exists_randomized {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {G : α × List Bool → β} (hG : ComputableTidilyInPolyTime G (encPair encIn encBits) encOut)
    (L m : ℕ) (d : β) :
    ∃ M : Machine, ∀ a, M.run (encIn a) =
      if (encIn a).length ≤ L then (BitString.uniformList m).map (fun w => encOut (G (a, w)))
      else PMF.pure (encOut d) := by
  set encO := encOption encIn
  set middle := padEnc encO m
  -- Phase 1: `some a`, padded.
  have hsome : ComputableTidilyInPolyTime (some : α → Option α) encIn middle := by
    have h1 : ComputableTidilyInPolyTime (fun a => (some a, List.replicate m true)) encIn
        (encPair encO encBits) := by fun_prop
    obtain ⟨t, s, ht, hs, h⟩ := h1
    exact ⟨t, s, ht, hs, h.of_enc_eq fun _ => rfl⟩
  obtain ⟨T₁, s₁, hprep⟩ := computable_guarded hsome L none
  -- Phase 3: `G`, or `d`.
  set H : Option α × List Bool → β := fun p => p.1.elim d (fun a => G (a, p.2))
  have hH : ComputableTidilyInPolyTime H (encPair encO encBits) encOut := by
    have hbody : ComputableTidilyInPolyTime (fun q : (Option α × List Bool) × α => G (q.2, q.1.2))
        (encPair (encPair encO encBits) encIn) encOut :=
      hG.comp ((ComputableTidilyInPolyTime.snd _ _).prod
        ((ComputableTidilyInPolyTime.snd _ _).comp (ComputableTidilyInPolyTime.fst _ _)))
    exact ComputableTidilyInPolyTime.optionElimWithInput (encA := encPair encO encBits)
      (encB := encIn) (encC := encOut) (value := fun p : Option α × List Bool => p.1)
      (fallback := fun _ => d) (body := fun p a => G (a, p.2))
      (ComputableTidilyInPolyTime.fst _ _) (ComputableTidilyInPolyTime.const d) hbody
  set L' := 2 * (L + 2) + 1 + m
  obtain ⟨T₃, s₃, hHg⟩ := computable_guarded hH L' d
  -- The pipeline.
  have hmap := (computesInTimeOn_pairSampler encO m).map hHg
    (tf' := fun _ => T₃) (fun _ _ _ => le_rfl)
  have hall := hmap.preprocess hprep
  set T := 2 * T₁ + (2 * (2 * (L + 1) + 1 + m + 1) + T₃ + 4) + 4
  have hlenO : ∀ a, (encO (guarded encIn L some none a)).length ≤ L + 1 := by
    intro a
    unfold guarded
    split_ifs with h
    · simp [encO, encOption, h]
    · simp [encO, encOption]
  obtain ⟨k, S, hS, machine, hm⟩ := hall.mono (t₂ := fun _ => T) (fun a => by
    have := hlenO a
    rw [length_padEnc]
    omega)
  refine ⟨Machine.ofPTM machine T, fun a => ?_⟩
  rw [Machine.run_ofPTM, ← (hm a).1]
  simp only [ProbComp.eval_map, BitString.eval_sampleList, PMF.map_comp]
  by_cases ha : (encIn a).length ≤ L
  · rw [ite_eq_left_iff.mpr (fun h => absurd ha h)]
    have hp : guarded encIn L some none a = some a := by simp [guarded, ha]
    rw [hp]
    apply PMF.map_congr_support
    intro w hw
    have hwl := BitString.length_of_mem_support_uniformList hw
    have hle : (encPair encO encBits (some a, w)).length ≤ L' := by
      simp [encO, encOption, hwl, L']; omega
    simp only [Function.comp_apply, guarded, hle, ite_true]
    rfl
  · rw [ite_eq_right_iff.mpr (fun h => absurd h ha)]
    have hp : guarded encIn L some none a = none := by simp [guarded, ha]
    rw [hp]
    have : (encOut ∘ guarded (encPair encO encBits) L' H d ∘ fun w => (none, w)) =
        Function.const _ (encOut d) := by
      funext w
      simp only [Function.comp_apply, guarded, Function.const_apply]
      split_ifs <;> rfl
    rw [this, PMF.map_const]

end SigabaNeo
