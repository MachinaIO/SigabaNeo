import PE.Impl.ExpLUT.Prog.KeyBoxTest

/-! Streaming small-box checks with a persistent rejection latch. -/
namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)

/-- Constants preserved throughout the family test. -/
structure BoxTestReady (N K B r : ℕ) (w : St) : Prop where
  radius : w rRR = encRM N K (allC N (r : ZMod (2 ^ K - 1)))
  low : w rTBk = List.replicate B false
  high : w rTKB = List.replicate (K - B) false
  bit : w rB1 = [false]
  zero : w rZ = encRM N K 0

/-- Consume one word and reset the per-element accumulator. -/
def boxLoadC : Code := .seq (.cp rTx rZ) (.seq (.mvR rTx rQa) (.cp rFa rZ))

/-- Test the head; a failed test permanently sets the rejection latch to `[false]`. -/
def boxBodyC : Code := .seq boxLoadC
  (.seq ballTestC (.ifb rTx .nop (.cp rDq rB1)))

/-- Empty rejection latch means all tested coordinates were accepted. -/
def boxQueueC : Code := .seq (.clr rDq) (.rep rQc boxBodyC)

theorem boxBodyC_counter : boxBodyC.writes rQc = false := by decide

theorem wf_boxQueueC : boxQueueC.WFc := by
  refine ⟨trivial, boxBodyC_counter, ?_⟩
  simp [boxBodyC, boxLoadC, Code.WFc, wf_ballTestC]

theorem exec_boxBodyC {N K : ℕ} [NeZero (2 ^ K - 1)]
    (hK : 0 < K) (B r : ℕ) (hBK : B ≤ K) (hr : 2 * r < 2 ^ B)
    (hq : 2 ^ (B + 1) ≤ 2 ^ K - 1) (hcount : 2 * (K - B) < 2 ^ K - 1)
    (w : St) (hw : BoxTestReady N K B r w) (x : Rq N K) (xs : List (Rq N K))
    (hQ : w rQa = encL N K (x :: xs)) :
    exec N K boxBodyC w rQa = encL N K xs ∧
    exec N K boxBodyC w rDq = if cnorm x ≤ r then w rDq else [false] := by
  let u := exec N K boxLoadC w
  have uf : ∀ i : Fin 64, boxLoadC.writes i = false → u i = w i :=
    fun i hi ↦ exec_writes _ _ _ hi
  have ux : u rTx = encRM N K x := by
    dsimp [u, boxLoadC]; vm_simp
    simp [hQ, hw.zero, encL_cons]
  have uq : u rQa = encL N K xs := by
    dsimp [u, boxLoadC]; vm_simp
    simp [hQ, encL_cons]
  have uF : u rFa = encRM N K 0 := by
    dsimp [u, boxLoadC]; vm_simp; simp [hw.zero]
  have ht := exec_ballTestC hK B r hBK hr hq hcount u x ux
    (by rw [uf _ (by decide), hw.radius]) uF
    (by rw [uf _ (by decide), hw.low])
    (by rw [uf _ (by decide), hw.high])
    (by rw [uf _ (by decide), hw.bit])
    (by rw [uf _ (by decide), hw.zero])
  have vq : exec N K ballTestC u rQa = encL N K xs := by
    rw [exec_writes _ _ _ (by decide), uq]
  have vd : exec N K ballTestC u rDq = w rDq := by
    rw [exec_writes _ _ _ (by decide), uf _ (by decide)]
  have vb : exec N K ballTestC u rB1 = [false] := by
    rw [exec_writes _ _ _ (by decide), uf _ (by decide), hw.bit]
  change exec N K (.seq ballTestC (.ifb rTx .nop (.cp rDq rB1))) u rQa = _ ∧
    exec N K (.seq ballTestC (.ifb rTx .nop (.cp rDq rB1))) u rDq = _
  simp only [exec_seq, exec_ifb, ht, hd_cons, decide_eq_true_eq]
  by_cases hx : cnorm x ≤ r <;> simp [hx, exec_nop, exec_cp, vq, vd, vb]

/-- The family loop exhausts its input and leaves the latch blank exactly when every
coordinate is within the small ball. -/
theorem exec_boxQueueC {N K : ℕ} [NeZero (2 ^ K - 1)]
    (hK : 0 < K) (B r : ℕ) (hBK : B ≤ K) (hr : 2 * r < 2 ^ B)
    (hq : 2 ^ (B + 1) ≤ 2 ^ K - 1) (hcount : 2 * (K - B) < 2 ^ K - 1)
    (w : St) (hw : BoxTestReady N K B r w) (xs : List (Rq N K))
    (hQ : w rQa = encL N K xs) (hn : w rQc = List.replicate xs.length false) :
    exec N K boxQueueC w rQa = [] ∧
      (exec N K boxQueueC w rDq = [] ↔ ∀ x ∈ xs, cnorm x ≤ r) := by
  rw [boxQueueC, exec_seq]
  let W := exec N K (.clr rDq) w
  have fr : ∀ i : Fin 64, i ≠ rDq → W i = w i := by
    intro i hi; exact Function.update_of_ne hi _ _
  have hc : (W rQc).length = xs.length := by rw [fr _ (by decide), hn]; simp
  have key := exec_rep_inv2 (N := N) (K := K) rQc boxBodyC boxBodyC_counter
    (fun m v ↦ v rQa = encL N K (xs.drop m) ∧
      (v rDq = [] ↔ ∀ x ∈ xs.take m, cnorm x ≤ r)) W
    ⟨by rw [fr _ (by decide), hQ]; simp, by simp [W]⟩ ?_
  · rw [hc] at key
    simpa [W] using key
  · intro m v hm hp _ hfr
    rw [hc] at hm
    let U := Function.update v rQc (v rQc).tail
    have fU : ∀ i : Fin 64, i ≠ rQc → U i = v i :=
      fun i hi ↦ Function.update_of_ne hi _ _
    have keep : ∀ i : Fin 64, boxBodyC.writes i = false → i ≠ rQc → i ≠ rDq → U i = w i := by
      intro i hi hic hid
      rw [fU i hic, hfr i hi hic, fr i hid]
    have ready : BoxTestReady N K B r U :=
      ⟨(keep _ (by decide) (by decide) (by decide)).trans hw.radius,
       (keep _ (by decide) (by decide) (by decide)).trans hw.low,
       (keep _ (by decide) (by decide) (by decide)).trans hw.high,
       (keep _ (by decide) (by decide) (by decide)).trans hw.bit,
       (keep _ (by decide) (by decide) (by decide)).trans hw.zero⟩
    have huq : U rQa = encL N K (xs[m] :: xs.drop (m + 1)) := by
      rw [fU _ (by decide), hp.1, drop_cons_getElem xs hm]
    obtain ⟨hq', hd'⟩ := exec_boxBodyC hK B r hBK hr hq hcount U ready xs[m]
      (xs.drop (m + 1)) huq
    refine ⟨hq', ?_⟩
    change exec N K boxBodyC U rDq = [] ↔ _
    rw [hd', fU _ (by decide), take_succ_getElem xs hm]
    by_cases hx : cnorm xs[m] ≤ r <;>
      simp only [hx, ↓reduceIte, hp.2, List.forall_mem_append, List.forall_mem_singleton,
        and_true, and_false, List.cons_ne_nil]

/-- The executable streaming test recognizes exactly the configured family box. -/
theorem exec_boxQueueC_family (D : Dims) (B r : ℕ) (hB : 2 ^ B ≤ D.q)
    (hBK : B ≤ D.K) (hr : 2 * r < 2 ^ B) (hq : 2 ^ (B + 1) ≤ D.q)
    (hcount : 2 * (D.K - B) < D.q) (w : St) (hw : BoxTestReady D.N D.K B r w)
    (p : PIdxD D → Rg D)
    (hQ : w rQa = encL D.N D.K ((Enum.list (α := PIdxD D)).map p))
    (hn : w rQc = List.replicate (Enum.list (α := PIdxD D)).length false) :
    exec D.N D.K boxQueueC w rQa = [] ∧
      (exec D.N D.K boxQueueC w rDq = [] ↔ p ∈ (kbOf D B hB r).Small) := by
  have h := exec_boxQueueC D.K_pos B r hBK hr hq hcount w hw
    ((Enum.list (α := PIdxD D)).map p) hQ (by simpa using hn)
  refine ⟨h.1, h.2.trans ?_⟩
  rw [kbOf_Small, mem_famBall]
  simp only [List.forall_mem_map]
  exact ⟨fun h t ↦ h t (Enum.complete t), fun h t _ ↦ h t⟩

/-- Convert the persistent rejection latch to an explicit Boolean branch input. -/
def boxFamilyC : Code := .seq boxQueueC (.seq (.clr rQb) (.eqb rTx rDq rQb))

theorem wf_boxFamilyC : boxFamilyC.WFc := ⟨wf_boxQueueC, trivial, trivial⟩

/-- Boolean output of the complete streaming family test. -/
theorem exec_boxFamilyC (D : Dims) (B r : ℕ) (hB : 2 ^ B ≤ D.q)
    (hBK : B ≤ D.K) (hr : 2 * r < 2 ^ B) (hq : 2 ^ (B + 1) ≤ D.q)
    (hcount : 2 * (D.K - B) < D.q) (w : St) (hw : BoxTestReady D.N D.K B r w)
    (p : PIdxD D → Rg D)
    (hQ : w rQa = encL D.N D.K ((Enum.list (α := PIdxD D)).map p))
    (hn : w rQc = List.replicate (Enum.list (α := PIdxD D)).length false) :
    exec D.N D.K boxFamilyC w rTx = [decide (p ∈ (kbOf D B hB r).Small)] := by
  have ht := (exec_boxQueueC_family D B r hB hBK hr hq hcount w hw p hQ hn).2
  simp only [boxFamilyC, exec_seq, exec_clr]
  simp only [exec, rTx, rDq, rQb, Fin.reduceEq, or_self, ↓reduceIte,
    Function.update_self, Function.update_of_ne (by decide : (28 : Fin 64) ≠ 51)]
  simp only [ht]

end AdvancedEncryption.ExpLUT.Prog
