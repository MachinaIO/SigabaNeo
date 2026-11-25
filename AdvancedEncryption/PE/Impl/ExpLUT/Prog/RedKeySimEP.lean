import PE.Impl.ExpLUT.Prog.RedKeySimEL
import PE.Impl.ExpLUT.Prog.RedKeySimT
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMUtil

/-!
# `KGsim` on the VM (module 6b, part 8): from the slab-major outputs to `rxRh` (generic VM)

After the slab loop (`RedKeySimEL.exec_seLoopKC`) the stream `rAinS` holds the output slabs,
slab-major: first the `nA` slabs `A` (the `Ā` slabs at `D`), then the `nB` slabs `B` (the `η` slabs),
each of `W` rows of `2K` words. `sePostC` splits off the `A` slabs (a counter of `nA · W` rows from
the unary `nA` in `seMb = 13`), transposes them into `rxRh` (`transC`, `n = nA`), then transposes the `B`
slabs (`n = nB = b · 2 · 2K`, the unary built from `rTb` and `rT2K`) behind them:
**`exec_sePostC`**: `rxRh = encL (transOut A W nA ++ transOut B W nB)`.

**`exec_sePostMC`**: `sePostMC mb = natC seMb rBit1 mb ; sePostC` (the count `0^{mb}` built fresh,
so its static length bound is `mb`, not the bound of `rCs`).

Registers: the `A` rows in `8`, the `B` rows in `9`, counters `10`, `11`, the pop temporary `12`;
`transC`'s registers `0 … 6`, `rxRh = 24`.
-/

set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)

variable {N K : ℕ}

/-- The `A` rows. -/
@[simp, vmreg] abbrev sePA : Fin 64 := 8
/-- The `B` rows. -/
@[simp, vmreg] abbrev sePB : Fin 64 := 9
/-- A counter. -/
@[simp, vmreg] abbrev sePC : Fin 64 := 10
/-- A counter. -/
@[simp, vmreg] abbrev sePD : Fin 64 := 11
/-- The pop temporary. -/
@[simp, vmreg] abbrev sePX : Fin 64 := 12
/-- The split count `0^{nA}` (`= 0^{m̄}` at `D`), a fresh unary word built by `sePostMC` (not
`rCs`: its static length bound after the slab loop is the full coefficient word). -/
@[simp, vmreg] abbrev seMb : Fin 64 := 13

/-- `rtR := (|rTW| − 1)` rows of `2K` words. -/
def seRtC : Code :=
  .seq (.clr rtR) <| .seq (.cp sePC rTW) <| .seq (.tl sePC) (.rep sePC (.app rtR rT2KNK))

theorem exec_seRtC (w : St) (W : ℕ) (hW : (w rTW).length = W) (hT : MulTmpl N K w) :
    (exec N K seRtC w rtR).length = (W - 1) * (2 * K) * (N * K) ∧
    (∀ r : Fin 64, r ≠ rtR → r ≠ sePC → exec N K seRtC w r = w r) := by
  unfold seRtC
  simp only [exec_seq]
  generalize hW1 : exec N K (.tl sePC) (exec N K (.cp sePC rTW) (exec N K (.clr rtR) w)) = W1
  have f1 : ∀ r : Fin 64, r ≠ rtR → r ≠ sePC → W1 r = w r := fun r h1 h2 => by
    rw [← hW1]; vm_simp; simp [Function.update_apply, h1, h2]
  have key := exec_rep_inv2 (N := N) (K := K) sePC (.app rtR rT2KNK) (by decide)
    (fun m w' => (w' rtR).length = m * (2 * K) * (N * K)) W1
    (by rw [← hW1]; vm_simp; simp [Function.update_apply]) ?_
  · have hc : (W1 sePC).length = W - 1 := by
      rw [← hW1]; vm_simp; simp [Function.update_apply, hW]
    rw [hc] at key
    refine ⟨key, fun r h1 h2 => ?_⟩
    rw [exec_writes _ _ _ (by simp [Code.writes, Ne.symm h1, Ne.symm h2]), f1 r h1 h2]
  · intro m w' _ hP _ hfr
    have h2 : w' rT2KNK = encL N K (List.replicate (2 * K) 0) := by
      rw [hfr _ (by decide) (by decide), f1 _ (by decide) (by decide), hT.t2KNK]
    vm_simp
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, List.length_append, hP, h2,
      length_encL, List.length_replicate]
    ring

/-- `rtN := b · 2 · 2K` (unary, from `rTb` and `rT2K`). -/
def seNBC : Code :=
  .seq (.clr rtN) <| .seq (.cp sePC rTb) (.rep sePC (.seq (.app rtN rT2K) (.app rtN rT2K)))

theorem exec_seNBC (w : St) (b : ℕ) (hb : (w rTb).length = b) (hT : MulTmpl N K w) :
    (exec N K seNBC w rtN).length = b * (2 * (2 * K)) ∧
    (∀ r : Fin 64, r ≠ rtN → r ≠ sePC → exec N K seNBC w r = w r) := by
  unfold seNBC
  simp only [exec_seq]
  generalize hW1 : exec N K (.cp sePC rTb) (exec N K (.clr rtN) w) = W1
  have f1 : ∀ r : Fin 64, r ≠ rtN → r ≠ sePC → W1 r = w r := fun r h1 h2 => by
    rw [← hW1]; vm_simp; simp [Function.update_apply, h1, h2]
  have key := exec_rep_inv2 (N := N) (K := K) sePC (.seq (.app rtN rT2K) (.app rtN rT2K))
    (by decide) (fun m w' => (w' rtN).length = m * (2 * (2 * K))) W1
    (by rw [← hW1]; vm_simp; simp [Function.update_apply]) ?_
  · have hc : (W1 sePC).length = b := by
      rw [← hW1]; vm_simp; simp [Function.update_apply, hb]
    rw [hc] at key
    refine ⟨key, fun r h1 h2 => ?_⟩
    rw [exec_writes _ _ _ (by simp [Code.writes, Ne.symm h1, Ne.symm h2]), f1 r h1 h2]
  · intro m w' _ hP _ hfr
    have h2 : w' rT2K = List.replicate (2 * K) false := by
      rw [hfr _ (by decide) (by decide), f1 _ (by decide) (by decide), hT.t2K]
    vm_simp
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, List.length_append, hP, h2,
      List.length_replicate]
    ring

/-- The split: the first `|seMb| · |rTW|` rows of `rAinS` into `sePA`, the rest into `sePB`,
`rtQ := sePA`. -/
def seSplitC : Code :=
  .seq (.clr sePA) <| .seq (.clr sePC) <| .seq (.cp sePD seMb) <| .seq (.rep sePD (.app sePC rTW)) <|
  .seq (sePopsC sePC sePA rAinS rT2KNK sePX) <| .seq (.cp sePB rAinS) (.cp rAinS sePA)

/-- **The post-processing**: split, `transC` on the `A` slabs, `transC` on the `B` slabs. -/
def sePostC : Code :=
  .seq seSplitC <| .seq (.clr rxRh) <| .seq (.cp rtN seMb) <| .seq (.cp rtW rTW) <| .seq seRtC <|
  .seq transC <| .seq (.cp rtQ sePB) <| .seq seNBC <| .seq seRtC transC

theorem flatten_rows (rows : ℕ → ℕ → List (Rq N K)) (n W : ℕ) :
    (((List.range n).flatMap fun k => (List.range W).map (rows k))).flatten =
      (List.range n).flatMap fun k => (List.range W).flatMap (rows k) := by
  induction (List.range n) with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, List.flatten_append, ih]
    simp [List.flatMap]

theorem exec_seSplitC (w : St) (W nA : ℕ) (rB : List (Rq N K))
    (rows : ℕ → ℕ → List (Rq N K)) (hL : ∀ k i, (rows k i).length = 2 * K)
    (hS : w rAinS = encL N K (((List.range nA).flatMap fun k => (List.range W).flatMap (rows k)) ++
      rB)) (hW : w rTW = List.replicate W false) (hC : (w seMb).length = nA) (hT : MulTmpl N K w) :
    exec N K seSplitC w rAinS = encL N K ((List.range nA).flatMap fun k =>
      (List.range W).flatMap (rows k)) ∧
    exec N K seSplitC w sePB = encL N K rB ∧
    (∀ r : Fin 64, r.val ∉ [0, 8, 9, 10, 11, 12] → exec N K seSplitC w r = w r) := by
  unfold seSplitC
  simp only [exec_seq]
  generalize hW1 : exec N K (.cp sePD seMb) (exec N K (.clr sePC) (exec N K (.clr sePA) w)) = W1
  have f1 : ∀ r : Fin 64, r ≠ sePA → r ≠ sePC → r ≠ sePD → W1 r = w r := fun r h1 h2 h3 => by
    rw [← hW1]; vm_simp; simp [Function.update_apply, h1, h2, h3]
  -- the counter `nA · W`
  have key := exec_rep_inv2 (N := N) (K := K) sePD (.app sePC rTW) (by decide)
    (fun m w' => w' sePC = List.replicate (m * W) false) W1
    (by rw [← hW1]; vm_simp; simp [Function.update_apply]) ?_
  · have hc : (W1 sePD).length = nA := by rw [← hW1]; vm_simp; simp [Function.update_apply, hC]
    rw [hc] at key
    generalize hW2 : exec N K (.rep sePD (.app sePC rTW)) W1 = W2
    rw [hW2] at key
    have f2 : ∀ r : Fin 64, r ≠ sePC → r ≠ sePD → W2 r = W1 r := fun r h1 h2 => by
      rw [← hW2, exec_writes _ _ _ (by simp [Code.writes, Ne.symm h1, Ne.symm h2])]
    obtain ⟨p1, p2⟩ := exec_sePopsC (N := N) (K := K) sePC sePA rAinS rT2KNK sePX (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) W2 ((List.range nA).flatMap fun k => (List.range W).map (rows k)) rB
      (2 * K) (fun x hx => by
        obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp hx
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hk
        exact hL k i)
      (by rw [key]; simp [List.length_flatMap, Nat.mul_comm])
      (by rw [f2 _ (by decide) (by decide), f1 _ (by decide) (by decide) (by decide), hT.t2KNK]
          simp)
      (by rw [f2 _ (by decide) (by decide), f1 _ (by decide) (by decide) (by decide), hS,
            flatten_rows])
    generalize hW3 : exec N K (sePopsC sePC sePA rAinS rT2KNK sePX) W2 = W3
    rw [hW3] at p1 p2
    have f3 : ∀ r : Fin 64, r.val ∉ [0, 8, 9, 10, 11, 12] → W3 r = w r := fun r hr => by
      rw [← hW3, exec_writes _ _ _ (by
          simp only [sePopsC, sePopC, Code.writes, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
          revert r; decide), f2 r (by revert r; decide) (by revert r; decide),
        f1 r (by revert r; decide) (by revert r; decide) (by revert r; decide)]
    have hA : W2 sePA = [] := by
      rw [f2 _ (by decide) (by decide), ← hW1]; vm_simp; simp [Function.update_apply]
    rw [hA, List.nil_append, flatten_rows] at p1
    refine ⟨?_, ?_, fun r hr => ?_⟩
    · rw [exec_cp, Function.update_self, exec_cp, Function.update_of_ne (by decide), p1]
    · rw [exec_cp, Function.update_of_ne (by decide), exec_cp, Function.update_self, p2]
    · have h0 : r ≠ rAinS := by intro e; subst e; simp at hr
      have h9 : r ≠ sePB := by intro e; subst e; simp at hr
      rw [exec_cp, Function.update_of_ne h0, exec_cp, Function.update_of_ne h9, f3 r hr]
  · intro m w' _ hP _ hfr
    have h2 : w' rTW = List.replicate W false := by
      rw [hfr _ (by decide) (by decide), f1 _ (by decide) (by decide) (by decide), hW]
    vm_simp
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, hP, h2, ← List.replicate_add]
    congr 1
    ring

theorem transC_frame : ∀ r : Fin 64, r.val ∉ [0, 1, 2, 3, 4, 24] → transC.writes r = false := by
  decide

/-- **The post-processing**: `rxRh` = the row-major transpositions of the `A` slabs, then of the
`B` slabs. -/
theorem exec_sePostC (w : St) (W nA b : ℕ) (rowsA rowsB : ℕ → ℕ → List (Rq N K))
    (hA : ∀ k i, (rowsA k i).length = 2 * K) (hB : ∀ k i, (rowsB k i).length = 2 * K)
    (hS : w rAinS = encL N K (((List.range nA).flatMap fun k => (List.range W).flatMap (rowsA k)) ++
      ((List.range (b * (2 * (2 * K)))).flatMap fun k => (List.range W).flatMap (rowsB k))))
    (hW : w rTW = List.replicate W false) (hC : (w seMb).length = nA) (hb : (w rTb).length = b)
    (hT : MulTmpl N K w) :
    exec N K sePostC w rxRh = encL N K
      (((List.range W).flatMap fun i => (List.range nA).flatMap fun k => rowsA k i) ++
        ((List.range W).flatMap fun i => (List.range (b * (2 * (2 * K)))).flatMap fun k => rowsB k i)) := by
  unfold sePostC
  simp only [exec_seq]
  obtain ⟨s1, s2, s3⟩ := exec_seSplitC w W nA _ rowsA hA hS hW hC hT
  generalize hW1 : exec N K seSplitC w = W1
  rw [hW1] at s1 s2 s3
  have T1 : MulTmpl N K W1 := hT.of_writes fun q hq => s3 q (by revert q; decide)
  generalize hW2 : exec N K (.cp rtW rTW) (exec N K (.cp rtN seMb) (exec N K (.clr rxRh) W1)) = W2
  have f2 : ∀ r : Fin 64, r ≠ rtW → r ≠ rtN → r ≠ rxRh → W2 r = W1 r := fun r h1 h2 h3 => by
    rw [← hW2]; vm_simp; simp [Function.update_apply, h1, h2, h3]
  have T2 : MulTmpl N K W2 := T1.of_writes fun q hq =>
    f2 q (by revert q; decide) (by revert q; decide) (by revert q; decide)
  obtain ⟨r3, f3⟩ := exec_seRtC W2 W (by rw [f2 _ (by decide) (by decide) (by decide),
    s3 _ (by decide), hW, List.length_replicate]) T2
  generalize hW3 : exec N K seRtC W2 = W3
  rw [hW3] at r3 f3
  have g3 : ∀ r : Fin 64, r.val ∉ [0, 1, 5, 6, 8, 9, 10, 11, 12, 24] → W3 r = w r := fun r hr => by
    rw [f3 r (by revert r; decide) (by revert r; decide),
      f2 r (by revert r; decide) (by revert r; decide) (by revert r; decide), s3 r (by revert r; decide)]
  have T3 : MulTmpl N K W3 := hT.of_writes fun q hq => g3 q (by revert q; decide)
  have t4 := exec_transC W3 rowsA hA nA W [] (by rw [f3 _ (by decide) (by decide),
      f2 _ (by decide) (by decide) (by decide), s1])
    (by rw [f3 _ (by decide) (by decide), ← hW2]; vm_simp; simp [Function.update_apply]) r3
    (by rw [f3 _ (by decide) (by decide), ← hW2]; vm_simp; simp [Function.update_apply, s3 seMb (by decide), hC])
    (by rw [f3 _ (by decide) (by decide), ← hW2]; vm_simp; simp [Function.update_apply, s3, hW])
    T3.t2KNK
  generalize hW4 : exec N K transC W3 = W4
  rw [hW4] at t4
  have f4 : ∀ r : Fin 64, r.val ∉ [0, 1, 2, 3, 4, 24] → W4 r = W3 r := fun r hr => by
    rw [← hW4, exec_writes _ _ _ (transC_frame r hr)]
  generalize hW5 : exec N K (.cp rtQ sePB) W4 = W5
  have f5 : ∀ r : Fin 64, r ≠ rtQ → W5 r = W4 r := fun r h => by
    rw [← hW5, exec_cp, Function.update_of_ne h]
  have T5 : MulTmpl N K W5 := hT.of_writes fun q hq => by
    rw [f5 q (by revert q; decide), f4 q (by revert q; decide), g3 q (by revert q; decide)]
  obtain ⟨n6, f6⟩ := exec_seNBC W5 b (by rw [f5 _ (by decide), f4 _ (by decide), g3 _ (by decide),
    hb]) T5
  generalize hW6 : exec N K seNBC W5 = W6
  rw [hW6] at n6 f6
  have T6 : MulTmpl N K W6 := T5.of_writes fun q hq => f6 q (by revert q; decide) (by revert q; decide)
  obtain ⟨r7, f7⟩ := exec_seRtC W6 W (by rw [f6 _ (by decide) (by decide), f5 _ (by decide),
    f4 _ (by decide), g3 _ (by decide), hW, List.length_replicate]) T6
  generalize hW7 : exec N K seRtC W6 = W7
  rw [hW7] at r7 f7
  have T7 : MulTmpl N K W7 := T6.of_writes fun q hq => f7 q (by revert q; decide) (by revert q; decide)
  have e9 : W4 sePB = encL N K ((List.range (b * (2 * (2 * K)))).flatMap fun k =>
      (List.range W).flatMap (rowsB k)) := by
    rw [f4 _ (by decide), f3 _ (by decide) (by decide), f2 _ (by decide) (by decide) (by decide), s2]
  have t8 := exec_transC W7 rowsB hB (b * (2 * (2 * K))) W _
    (by rw [f7 _ (by decide) (by decide), f6 _ (by decide) (by decide), ← hW5, exec_cp,
      Function.update_self, e9])
    (by rw [f7 _ (by decide) (by decide), f6 _ (by decide) (by decide), f5 _ (by decide)])
    r7 (by rw [f7 _ (by decide) (by decide)]; exact n6)
    (by rw [f7 _ (by decide) (by decide), f6 _ (by decide) (by decide), f5 _ (by decide),
      f4 _ (by decide), f3 _ (by decide) (by decide), ← hW2]; vm_simp
        simp [Function.update_apply, s3, hW])
    T7.t2KNK
  rw [t8, t4, encL_append]
  simp

/-- **The post-processing with a fresh count**: `seMb := 0^{mb}` (from `rBit1 = [false]`), then
`sePostC`. -/
def sePostMC (mb : ℕ) : Code := .seq (natC seMb rBit1 mb) sePostC

theorem exec_sePostMC (w : St) (W nA b : ℕ) (rowsA rowsB : ℕ → ℕ → List (Rq N K))
    (hA : ∀ k i, (rowsA k i).length = 2 * K) (hB : ∀ k i, (rowsB k i).length = 2 * K)
    (hS : w rAinS = encL N K (((List.range nA).flatMap fun k => (List.range W).flatMap (rowsA k)) ++
      ((List.range (b * (2 * (2 * K)))).flatMap fun k => (List.range W).flatMap (rowsB k))))
    (hW : w rTW = List.replicate W false) (h1 : w rBit1 = [false]) (hb : (w rTb).length = b)
    (hT : MulTmpl N K w) :
    exec N K (sePostMC nA) w rxRh = encL N K
      (((List.range W).flatMap fun i => (List.range nA).flatMap fun k => rowsA k i) ++
        ((List.range W).flatMap fun i => (List.range (b * (2 * (2 * K)))).flatMap fun k => rowsB k i)) := by
  rw [sePostMC, exec_seq, exec_natC seMb rBit1 (by decide) nA w h1]
  exact exec_sePostC _ W nA b rowsA rowsB hA hB
    (by rw [Function.update_of_ne (by decide)]; exact hS)
    (by rw [Function.update_of_ne (by decide)]; exact hW)
    (by rw [Function.update_self, List.length_replicate])
    (by rw [Function.update_of_ne (by decide)]; exact hb)
    (hT.of_writes fun q hq => Function.update_of_ne (fun e => by subst e; simp at hq) _ _)

theorem sePostMC_writes (mb : ℕ) (r : Fin 64) (hr : r ≠ seMb) :
    (sePostMC mb).writes r = sePostC.writes r := by
  simp [sePostMC, Code.writes, natC_writes _ _ mb r hr]

theorem wf_sePostMC (mb : ℕ) (h : sePostC.WFc) : (sePostMC mb).WFc := ⟨natC_wfc _ _ _, h⟩

end AdvancedEncryption.ExpLUT.Prog
