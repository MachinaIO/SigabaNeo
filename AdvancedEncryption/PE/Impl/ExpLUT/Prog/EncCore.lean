import PE.Impl.ExpLUT.Prog.EncBPhase
import SigabaNeo.Lib.Machines.Prog.CoinFreeX

/-! # Concrete tape layout and sequential encryption core

Only output tape zero is shared. The four phases have disjoint input, template,
and scratch regions, so consuming a phase's streams leaves later inputs intact.
-/
namespace AdvancedEncryption.ExpLUT.Prog.EncW

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.Prog Matrix

/-- Local tape zero is the common output; all other local tapes occupy a private interval. -/
def phaseSlot (off n : ℕ) (hn : off + n < 321) (i : Fin (n + 1)) : Fin 321 :=
  if i = 0 then 0 else ⟨off + i.val, by omega⟩

@[simp] theorem phaseSlot_zero (off n : ℕ) (hn : off + n < 321) :
    phaseSlot off n hn 0 = 0 := by simp [phaseSlot]

theorem phaseSlot_inj (off n : ℕ) (hn : off + n < 321) :
    Function.Injective (phaseSlot off n hn) := by
  intro i j hij
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · simp_all
  · have hjv : 0 < j.val := by exact Fin.pos_of_ne_zero hj
    simp [phaseSlot, hi, hj] at hij
  · have hiv : 0 < i.val := by exact Fin.pos_of_ne_zero hi
    simp [phaseSlot, hi, hj] at hij
  · simp only [phaseSlot, ite_eq_right hi, ite_eq_right hj] at hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    change off + i.val = off + j.val at hv
    omega

def bSlot : Fin 66 → Fin 321 := phaseSlot 0 65 (by decide)
def helperSlot : Fin 69 → Fin 321 := phaseSlot 65 68 (by decide)
def autSlot : Fin 85 → Fin 321 := phaseSlot 133 84 (by decide)
def tailSlot : Fin 104 → Fin 321 := phaseSlot 217 103 (by decide)

theorem bSlot_inj : Function.Injective bSlot := phaseSlot_inj _ _ _
theorem helperSlot_inj : Function.Injective helperSlot := phaseSlot_inj _ _ _
theorem autSlot_inj : Function.Injective autSlot := phaseSlot_inj _ _ _
theorem tailSlot_inj : Function.Injective tailSlot := phaseSlot_inj _ _ _

/-- An earlier phase cannot write a nonzero tape of a later phase. -/
theorem phaseSlot_separate {off n off' n' : ℕ} (hn : off + n < 321)
    (hn' : off' + n' < 321) (hsep : off + n ≤ off')
    (i : Fin (n + 1)) (j : Fin (n' + 1)) (hj : j ≠ 0) :
    phaseSlot off n hn i ≠ phaseSlot off' n' hn' j := by
  have hjv := Fin.pos_of_ne_zero hj
  intro he
  have hv := congrArg Fin.val he
  by_cases hi : i = 0
  · simp [phaseSlot, hi, hj] at hv
    omega
  · simp [phaseSlot, hi, hj] at hv
    omega

/-- Running a phase changes a later phase's view only at the shared output tape. -/
theorem phase_view_after {n m : ℕ} (u : Fin (n + 1) → Fin 321)
    (v : Fin (m + 1) → Fin 321) (hu : Function.Injective u)
    (hu0 : u 0 = 0) (hv0 : v 0 = 0)
    (hsep : ∀ i j, j ≠ 0 → u i ≠ v j) (p : SigabaNeo.Tape.Prog (n + 1)) (S : Store 321) :
    (Prog.map u p).run S ∘ v = Function.update (S ∘ v) 0 (p.run (S ∘ u) 0) := by
  rw [run_map hu]
  funext j
  by_cases hj : j = 0
  · subst j
    simp only [Function.comp_apply, hv0, Function.update_self]
    rw [← hu0, hu.extend_apply]
  · simp only [Function.comp_apply, Function.update_of_ne hj]
    exact extend_apply_of_not_mem _ _ (fun i ↦ hsep i j hj)

variable (D : Dims)

/-- All four verified encryption phases in ciphertext order on a single store. -/
def encCoreP : SigabaNeo.Tape.Prog 321 :=
  .seq (Prog.map bSlot mrowP)
    (.seq (Prog.map helperSlot (helperPairsP D 0 D.b))
      (.seq (Prog.map autSlot (autBlocksP D 0 D.b)) (Prog.map tailSlot tailP)))

theorem wf_encCoreP : (encCoreP D).WF :=
  ⟨wf_mrowP.map bSlot_inj, (wf_helperPairsP D 0 D.b).map helperSlot_inj,
    (wf_autBlocksP D 0 D.b).map autSlot_inj, wf_tailP.map tailSlot_inj⟩

theorem coinFree_encCoreP : (encCoreP D).CoinFree := by
  have hb : mrowP.CoinFree := rfl
  have ht : tailP.CoinFree := rfl
  simp only [encCoreP, Prog.CoinFree, Prog.coinFreeB, Bool.and_eq_true]
  exact ⟨coinFree_mapP bSlot hb, coinFree_mapP helperSlot (coinFree_helperPairsP D 0 D.b),
    coinFree_mapP autSlot (coinFree_autBlocksP D 0 D.b), coinFree_mapP tailSlot ht⟩

/-- The tape embeddings do not add instructions to the description. -/
theorem size_encCoreP : (encCoreP D).size = mrowP.size +
    (36 + D.b * (hBlkP.size + 144 + 60 * 2 ^ D.b)) +
    (36 + D.b * (autBlkP.size + 144 + 60 * 2 ^ D.b)) + tailP.size := by
  simp only [encCoreP, Prog.size, size_map]
  rw [size_helperPairsP D 0 D.b (by omega), size_autBlocksP D 0 D.b (by omega)]
  omega

/-- Exact execution of the combined core in terms of the four local machines.
The only state passed between phases is the ciphertext output register. -/
theorem run_encCoreP_output (S : Store 321) :
    (encCoreP D).run S 0 =
      let b := mrowP.run (S ∘ bSlot) 0
      let h := (helperPairsP D 0 D.b).run (Function.update (S ∘ helperSlot) 0 b) 0
      let a := (autBlocksP D 0 D.b).run (Function.update (S ∘ autSlot) 0 h) 0
      tailP.run (Function.update (S ∘ tailSlot) 0 a) 0 := by
  let B := (Prog.map bSlot mrowP).run S
  let H := (Prog.map helperSlot (helperPairsP D 0 D.b)).run B
  let A := (Prog.map autSlot (autBlocksP D 0 D.b)).run H
  have bh := phase_view_after bSlot helperSlot bSlot_inj rfl rfl
    (phaseSlot_separate _ _ (by decide)) mrowP S
  have ba := phase_view_after bSlot autSlot bSlot_inj rfl rfl
    (phaseSlot_separate _ _ (by decide)) mrowP S
  have bt := phase_view_after bSlot tailSlot bSlot_inj rfl rfl
    (phaseSlot_separate _ _ (by decide)) mrowP S
  have ha := phase_view_after helperSlot autSlot helperSlot_inj rfl rfl
    (phaseSlot_separate _ _ (by decide)) (helperPairsP D 0 D.b) B
  have ht := phase_view_after helperSlot tailSlot helperSlot_inj rfl rfl
    (phaseSlot_separate _ _ (by decide)) (helperPairsP D 0 D.b) B
  have hat :=  phase_view_after autSlot tailSlot autSlot_inj rfl rfl
    (phaseSlot_separate _ _ (by decide)) (autBlocksP D 0 D.b) H
  change B ∘ helperSlot = _ at bh
  change B ∘ autSlot = _ at ba
  change B ∘ tailSlot = _ at bt
  change H ∘ autSlot = _ at ha
  change H ∘ tailSlot = _ at ht
  change A ∘ tailSlot = _ at hat
  rw [bh, ba, Function.update_idem] at ha
  rw [bh, bt, Function.update_idem] at ht
  rw [ha, ht, Function.update_idem] at hat
  simp only [encCoreP, Prog.run_seq]
  change (Prog.map tailSlot tailP).run A 0 = _
  rw [run_map tailSlot_inj]
  change Function.extend tailSlot (tailP.run (A ∘ tailSlot)) A (tailSlot 0) = _
  rw [tailSlot_inj.extend_apply, hat]

end AdvancedEncryption.ExpLUT.Prog.EncW
