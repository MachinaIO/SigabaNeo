import PE.Impl.ExpLUT.Prog.RedKeyXDrive

/-!
# `KGsim` on the VM (module 6c): slab-major to row-major (generic VM)

Module 6 computes `R̂_F` slab by slab (`RedKeySimSlab`): `n` slabs of `W` rows of `2K` words,
slab-major. Module 5 reads the rows of `R̂_F` row-major (`rowsWord`, the block row `i` outer).
`transC` transposes: `W` passes over the queue; in pass `i` every slab gives its head row (the
row `i`) to the output (register `rxRh`, appended) and moves its remaining `W − i − 1` rows to
the back of the queue (**`exec_transC`**).

Registers: the queue `rtQ = 0`, the rest template `rtR = 1` (length `(W − 1) · 2K` words), a
temporary `rtX = 2`, the counters `rtP = 3`, `rtS = 4`, the templates `rtN = 5` (unary `n`) and
`rtW = 6` (unary `W`); rows are `rT2KNK` wide.
-/

set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)

@[simp, vmreg] abbrev rtQ : Fin 64 := 0
@[simp, vmreg] abbrev rtR : Fin 64 := 1
@[simp, vmreg] abbrev rtX : Fin 64 := 2
@[simp, vmreg] abbrev rtP : Fin 64 := 3
@[simp, vmreg] abbrev rtS : Fin 64 := 4
@[simp, vmreg] abbrev rtN : Fin 64 := 5
@[simp, vmreg] abbrev rtW : Fin 64 := 6

variable {N K : ℕ}

/-- One slab in a pass: its head row to the output, its rest to the back of the queue. -/
def tSlabBody : Code :=
  .seq (.cp rtX rT2KNK) <| .seq (.mv rtX rtQ rT2KNK) <| .seq (.app rxRh rtX) <|
  .seq (.cp rtX rtR) <| .seq (.mv rtX rtQ rtR) (.app rtQ rtX)

/-- One pass. -/
def tPassBody : Code := .seq (.cp rtS rtN) <| .seq (.rep rtS tSlabBody) (.drop rtR rT2KNK)

/-- **The transposition.** -/
def transC : Code := .seq (.cp rtP rtW) (.rep rtP tPassBody)

theorem tSlabBody_writes_rtS : tSlabBody.writes rtS = false := by decide
theorem tPassBody_writes_rtP : tPassBody.writes rtP = false := by decide
theorem wf_transC : transC.WFc := by repeat constructor

theorem transC_writes : ∀ r : Fin 64, transC.writes r = true →
    r ∈ [rtP, rtS, rtX, rtQ, rxRh, rtR] := by decide

/-- The rows `i' ≥ i` of the slab `k`. -/
def tRest (rows : ℕ → ℕ → List (Rq N K)) (W k i : ℕ) : List (Rq N K) :=
  ((List.range W).drop i).flatMap (rows k)

theorem tRest_cons (rows : ℕ → ℕ → List (Rq N K)) {W i : ℕ} (k : ℕ) (hi : i < W) :
    tRest rows W k i = rows k i ++ tRest rows W k (i + 1) := by
  unfold tRest; rw [drop_range_cons hi, List.flatMap_cons]

theorem length_tRest (rows : ℕ → ℕ → List (Rq N K)) {L : ℕ}
    (hL : ∀ k i, (rows k i).length = L) (W k i : ℕ) :
    (tRest rows W k i).length = (W - i) * L := by
  unfold tRest
  rw [List.length_flatMap, List.map_congr_left (fun i _ => hL k i)]
  simp [List.sum_replicate, List.map_const']

theorem shiftIn_len {n : ℕ} (d s : List Bool) (h : d.length = n) :
    ValVM.shiftIn n d s = takeD n s := by
  unfold ValVM.shiftIn; rw [← h, List.drop_left]

/-- **The slabs of one pass.** -/
theorem exec_tSlabLoop (w : St) (rows : ℕ → ℕ → List (Rq N K))
    (hL : ∀ k i, (rows k i).length = 2 * K) (n W i : ℕ) (hi : i < W) (pre : List Bool)
    (hQ : w rtQ = encL N K ((List.range n).flatMap fun k => tRest rows W k i))
    (hO : w rxRh = pre) (hR : (w rtR).length = (W - (i + 1)) * (2 * K) * (N * K))
    (hS : (w rtS).length = n) (hT : w rT2KNK = encL N K (List.replicate (2 * K) 0)) :
    exec N K (.rep rtS tSlabBody) w rtQ =
      encL N K ((List.range n).flatMap fun k => tRest rows W k (i + 1)) ∧
    exec N K (.rep rtS tSlabBody) w rxRh =
      pre ++ encL N K ((List.range n).flatMap fun k => rows k i) := by
  have key := exec_rep_inv2 (N := N) (K := K) rtS tSlabBody tSlabBody_writes_rtS
    (fun m w' => w' rtQ = encL N K (((List.range n).drop m).flatMap (fun k => tRest rows W k i) ++
        (List.range m).flatMap fun k => tRest rows W k (i + 1)) ∧
      w' rxRh = pre ++ encL N K ((List.range m).flatMap fun k => rows k i)) w
    ⟨by rw [hQ]; simp, by rw [hO]; simp⟩ ?_
  · rw [hS] at key
    rw [key.1, key.2, List.drop_of_length_le (by simp)]
    exact ⟨by simp, rfl⟩
  · intro m w' hm hP _ hfr
    rw [hS] at hm
    obtain ⟨p1, p2⟩ := hP
    have hT' : w' rT2KNK = encL N K (List.replicate (2 * K) 0) := by
      rw [hfr _ (by decide) (by decide), hT]
    have hR' : (w' rtR).length = (W - (i + 1)) * (2 * K) * (N * K) := by
      rw [hfr _ (by decide) (by decide), hR]
    rw [flatMap_range_drop _ hm, tRest_cons rows m hi, List.append_assoc, List.append_assoc] at p1
    have hlr : (rows m i).length = 2 * K := hL m i
    have hlt : (tRest rows W m (i + 1)).length = (W - (i + 1)) * (2 * K) :=
      length_tRest rows hL W m (i + 1)
    unfold tSlabBody
    vm_simp
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, hT', p1, p2, length_encL,
      List.length_replicate]
    have hR1 : (w' rtR).length = (W - (i + 1)) * (2 * K) * (N * K) := hR'
    simp only [rtR] at hR1
    rw [hR1]
    refine ⟨?_, ?_⟩
    · rw [drop_encL _ _ hlr, drop_encL _ _ hlt, shiftIn_len _ _ hR1, takeD_encL _ _ hlt,
        List.range_succ, List.flatMap_append, List.flatMap_singleton]
      simp only [encL_append, List.append_assoc]
    · rw [shiftIn_encL' _ _ (List.length_replicate), takeD_encL _ _ hlr, List.range_succ,
        List.flatMap_append, List.flatMap_singleton]
      simp only [encL_append, List.append_assoc]

/-- **The transposition**: `n` slabs of `W` rows (`2K` words each), slab-major in `rtQ`, are
appended row-major (row `i` of every slab, `i < W`) to `rxRh`. -/
theorem exec_transC (w : St) (rows : ℕ → ℕ → List (Rq N K))
    (hL : ∀ k i, (rows k i).length = 2 * K) (n W : ℕ) (pre : List Bool)
    (hQ : w rtQ = encL N K ((List.range n).flatMap fun k => (List.range W).flatMap (rows k)))
    (hO : w rxRh = pre) (hR : (w rtR).length = (W - 1) * (2 * K) * (N * K))
    (hN : (w rtN).length = n) (hW : (w rtW).length = W)
    (hT : w rT2KNK = encL N K (List.replicate (2 * K) 0)) :
    exec N K transC w rxRh =
      pre ++ encL N K ((List.range W).flatMap fun i => (List.range n).flatMap fun k => rows k i) := by
  unfold transC
  rw [exec_seq]
  set w0 := exec N K (.cp rtP rtW) w with hw0
  have e0 : ∀ r : Fin 64, r ≠ rtP → w0 r = w r := fun r h => by
    rw [hw0, exec_cp, Function.update_of_ne h]
  have key := exec_rep_inv2 (N := N) (K := K) rtP tPassBody tPassBody_writes_rtP
    (fun i w' => w' rtQ = encL N K ((List.range n).flatMap fun k => tRest rows W k i) ∧
      w' rxRh = pre ++ encL N K ((List.range i).flatMap fun i =>
        (List.range n).flatMap fun k => rows k i) ∧
      (w' rtR).length = (W - (i + 1)) * (2 * K) * (N * K)) w0
    ⟨by rw [e0 _ (by decide), hQ]; rfl, by rw [e0 _ (by decide), hO]; simp,
      by rw [e0 _ (by decide), hR]⟩ ?_
  · have hc : (w0 rtP).length = W := by rw [hw0, exec_cp, Function.update_self, hW]
    rw [hc] at key
    exact key.2.1
  · intro i w' hi hP _ hfr
    have hc : (w0 rtP).length = W := by rw [hw0, exec_cp, Function.update_self, hW]
    rw [hc] at hi
    obtain ⟨p1, p2, p3⟩ := hP
    set W1 := Function.update w' rtP (w' rtP).tail with hW1
    have u : ∀ r : Fin 64, r ≠ rtP → W1 r = w' r := fun r h => Function.update_of_ne h _ _
    have fr : ∀ r : Fin 64, tPassBody.writes r = false → r ≠ rtP → W1 r = w r := fun r h h' => by
      rw [u r h', hfr r h h', e0 r h']
    unfold tPassBody
    simp only [exec_seq]
    set W2 := exec N K (.cp rtS rtN) W1 with hW2
    have e2 : ∀ r : Fin 64, r ≠ rtS → W2 r = W1 r := fun r h => by
      rw [hW2, exec_cp, Function.update_of_ne h]
    have sl := exec_tSlabLoop W2 rows hL n W i hi _
      (by rw [e2 _ (by decide), u _ (by decide), p1]) (by rw [e2 _ (by decide), u _ (by decide), p2])
      (by rw [e2 _ (by decide), u _ (by decide), p3])
      (by rw [hW2, exec_cp, Function.update_self, fr _ (by decide) (by decide), hN])
      (by rw [e2 _ (by decide), fr _ (by decide) (by decide), hT])
    set W3 := exec N K (.rep rtS tSlabBody) W2 with hW3
    have f3 : ∀ r : Fin 64, (Code.rep rtS tSlabBody).writes r = false → W3 r = W2 r :=
      fun r h => exec_writes _ _ _ h
    refine ⟨?_, ?_, ?_⟩
    · rw [exec_drop, if_neg (by decide), Function.update_of_ne (by decide), sl.1]
    · rw [exec_drop, if_neg (by decide), Function.update_of_ne (by decide), sl.2, List.range_succ,
        List.flatMap_append, List.flatMap_singleton, encL_append, List.append_assoc]
    · rw [exec_drop, if_neg (by decide), Function.update_self, List.length_drop,
        f3 _ (by decide), e2 _ (by decide), u _ (by decide), p3, f3 _ (by decide),
        e2 _ (by decide), fr _ (by decide) (by decide), hT, length_encL, List.length_replicate,
        show W - (i + 1 + 1) = W - (i + 1) - 1 by omega, Nat.sub_one_mul]
      generalize (W - (i + 1)) * (2 * K) = Y
      rw [Nat.sub_mul]

end AdvancedEncryption.ExpLUT.Prog
