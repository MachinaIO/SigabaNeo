import PE.Impl.ExpLUT.Prog.KeyTryVM
import PE.Impl.ExpLUT.Prog.KeyEval
import PE.Impl.ExpLUT.Prog.KeyTryMath

/-! Target-minus-public-map subtraction followed by executable gadget decomposition. -/
namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)

/-- Subtract the public-map row in rIa from the target row in rQx, then emit its digits. -/
def decomposeC : Code := .seq (.op .sub rY rQx rIa) digQC

theorem wf_decomposeC : decomposeC.WFc := by
  simp [decomposeC, digQC, digQBody, Code.WFc, Code.writes]

/-- The actual subtraction and digit program, with an explicit digit count. -/
theorem exec_decomposeC {N K : ℕ} (hK : 0 < K) (w : St) (u v : Rq N K)
    (n : ℕ) (hu : w rQx = encRM N K u) (hv : w rIa = encRM N K v)
    (hn : w rCK = List.replicate n false) (h1 : w rB1 = [false]) :
    exec N K decomposeC w rZq = encL N K ((List.range n).map (binaryDigit (u - v))) := by
  rw [decomposeC, exec_seq]
  apply exec_digQC hK _ (u - v) n
  · vm_simp; simp [hu, hv, canonW_sub hK]
  · rw [exec_writes _ _ _ (by decide), hn]
  · rw [exec_writes _ _ _ (by decide), h1]

/-- The queue order is the order of the finite gadget coordinates. -/
theorem range_digits_eq_ofFn {N K : ℕ} (a : Rq N K) :
    (List.range K).map (binaryDigit a) = List.ofFn (fun c : Fin K ↦ binaryDigit a c.val) := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'; simp

/-- The executable row decomposition is the scheme's `gadDec`, with no abstract core premise. -/
theorem exec_decomposeC_gadDec (D : Dims) (w : St)
    (u v : Fin (setting D).E.W → Rg D) (i : Fin (setting D).E.W)
    (hu : w rQx = encRM D.N D.K (u i)) (hv : w rIa = encRM D.N D.K (v i))
    (hn : w rCK = List.replicate D.K false) (h1 : w rB1 = [false]) :
    exec D.N D.K decomposeC w rZq = encL D.N D.K
      (List.ofFn (fun c : Fin D.K ↦ gadDec (S := setting D) (u - v) (i, c))) := by
  rw [exec_decomposeC D.K_pos w (u i) (v i) D.K hu hv hn h1, range_digits_eq_ofFn]
  rfl

/-- Specialization to the target and public map used by one try of KeyGen. -/
theorem exec_decomposeC_key (D : Dims) (w : St) (mpk : MPKt D)
    (F : BP Pos) (p : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D)
    (i : Fin (setting D).E.W)
    (hu : w rQx = encRM D.N D.K (keyTarget mpk i))
    (hv : w rIa = encRM D.N D.K (pubShort (helperMap D) mpk F p i))
    (hn : w rCK = List.replicate D.K false) (h1 : w rB1 = [false]) :
    exec D.N D.K decomposeC w rZq = encL D.N D.K
      (List.ofFn (fun c : Fin D.K ↦ gadDec (S := setting D)
        (keyTarget mpk - pubShort (helperMap D) mpk F p) (i, c))) :=
  exec_decomposeC_gadDec D w _ _ i hu hv hn h1

/-- Load one pair of stream heads and restore the digit counter from the K-bit template. -/
def decRowLoadC : Code := .seq (.cp rQx rZ) <| .seq (.mvR rQx rQa) <|
  .seq (.cp rIa rZ) <| .seq (.mvR rIa rQb) (.cp rCK rQk)

/-- Append the gadget digits of one target/public-map row pair. -/
def decRowBodyC : Code := .seq decRowLoadC (.seq decomposeC (.app rDq rZq))

/-- Decompose every row, preserving row-major then digit-major order. -/
def decRowsC : Code := .seq (.clr rDq) (.rep rQc decRowBodyC)

theorem decRowBodyC_counter : decRowBodyC.writes rQc = false := by decide

theorem wf_decRowsC : decRowsC.WFc := by
  refine ⟨trivial, decRowBodyC_counter, ?_⟩
  simp [decRowBodyC, decRowLoadC, Code.WFc, wf_decomposeC]

theorem exec_decRowBodyC {N K : ℕ} (hK : 0 < K) (w : St)
    (u v : Rq N K) (us vs out : List (Rq N K))
    (hu : w rQa = encL N K (u :: us)) (hv : w rQb = encL N K (v :: vs))
    (ho : w rDq = encL N K out) (hKc : w rQk = List.replicate K false)
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM N K 0) :
    exec N K decRowBodyC w rQa = encL N K us ∧
    exec N K decRowBodyC w rQb = encL N K vs ∧
    exec N K decRowBodyC w rDq =
      encL N K (out ++ (List.range K).map (binaryDigit (u - v))) := by
  let t := exec N K decRowLoadC w
  have tf : ∀ i : Fin 64, decRowLoadC.writes i = false → t i = w i :=
    fun i hi ↦ exec_writes _ _ _ hi
  have tu : t rQx = encRM N K u := by
    dsimp [t, decRowLoadC]; vm_simp; simp [hu, hZ, encL_cons]
  have tv : t rIa = encRM N K v := by
    dsimp [t, decRowLoadC]; vm_simp; simp [hv, hZ, encL_cons]
  have tqA : t rQa = encL N K us := by
    dsimp [t, decRowLoadC]; vm_simp; simp [hu, encL_cons]
  have tqB : t rQb = encL N K vs := by
    dsimp [t, decRowLoadC]; vm_simp; simp [hv, encL_cons]
  have tc : t rCK = List.replicate K false := by
    dsimp [t, decRowLoadC]; vm_simp; simp [hKc]
  have hd := exec_decomposeC hK t u v K tu tv tc (by rw [tf _ (by decide), h1])
  have qa : exec N K decomposeC t rQa = encL N K us := by
    rw [exec_writes _ _ _ (by decide), tqA]
  have qb : exec N K decomposeC t rQb = encL N K vs := by
    rw [exec_writes _ _ _ (by decide), tqB]
  have qo : exec N K decomposeC t rDq = encL N K out := by
    rw [exec_writes _ _ _ (by decide), tf _ (by decide), ho]
  change exec N K (.seq decomposeC (.app rDq rZq)) t rQa = _ ∧
    exec N K (.seq decomposeC (.app rDq rZq)) t rQb = _ ∧
    exec N K (.seq decomposeC (.app rDq rZq)) t rDq = _
  simp [exec_seq, exec_app, qa, qb, qo, hd, encL_append]

/-- Full streaming decomposition: both input streams are exhausted and all digits are emitted. -/
theorem exec_decRowsC {N K : ℕ} (hK : 0 < K) (w : St)
    (rows : List (Rq N K × Rq N K))
    (hu : w rQa = encL N K (rows.map Prod.fst))
    (hv : w rQb = encL N K (rows.map Prod.snd))
    (hn : w rQc = List.replicate rows.length false)
    (hKc : w rQk = List.replicate K false) (h1 : w rB1 = [false])
    (hZ : w rZ = encRM N K 0) :
    exec N K decRowsC w rQa = [] ∧ exec N K decRowsC w rQb = [] ∧
    exec N K decRowsC w rDq = encL N K
      (rows.flatMap (fun uv ↦ (List.range K).map (binaryDigit (uv.1 - uv.2)))) := by
  let digits : Rq N K × Rq N K → List (Rq N K) :=
    fun uv ↦ (List.range K).map (binaryDigit (uv.1 - uv.2))
  rw [decRowsC, exec_seq]
  let W := exec N K (.clr rDq) w
  have fr : ∀ i : Fin 64, i ≠ rDq → W i = w i :=
    fun i hi ↦ Function.update_of_ne hi _ _
  have hc : (W rQc).length = rows.length := by rw [fr _ (by decide), hn]; simp
  have key := exec_rep_inv2 (N := N) (K := K) rQc decRowBodyC decRowBodyC_counter
    (fun m t ↦ t rQa = encL N K ((rows.drop m).map Prod.fst) ∧
      t rQb = encL N K ((rows.drop m).map Prod.snd) ∧
      t rDq = encL N K ((rows.take m).flatMap digits)) W
    ⟨by rw [fr _ (by decide), hu]; simp,
     by rw [fr _ (by decide), hv]; simp, by simp [W]⟩ ?_
  · rw [hc] at key
    simpa [W, digits] using key
  · intro m v hm hp _ hfr
    rw [hc] at hm
    let U := Function.update v rQc (v rQc).tail
    have fU : ∀ i : Fin 64, i ≠ rQc → U i = v i :=
      fun i hi ↦ Function.update_of_ne hi _ _
    have keep : ∀ i : Fin 64, decRowBodyC.writes i = false → i ≠ rQc → i ≠ rDq → U i = w i := by
      intro i hi hic hid
      rw [fU i hic, hfr i hi hic, fr i hid]
    have uA : U rQa = encL N K (rows[m].1 :: (rows.drop (m + 1)).map Prod.fst) := by
      rw [fU _ (by decide), hp.1, drop_cons_getElem rows hm, List.map_cons]
    have uB : U rQb = encL N K (rows[m].2 :: (rows.drop (m + 1)).map Prod.snd) := by
      rw [fU _ (by decide), hp.2.1, drop_cons_getElem rows hm, List.map_cons]
    obtain ⟨a, b, o⟩ := exec_decRowBodyC hK U rows[m].1 rows[m].2
      ((rows.drop (m + 1)).map Prod.fst) ((rows.drop (m + 1)).map Prod.snd)
      ((rows.take m).flatMap digits) uA uB (by rw [fU _ (by decide), hp.2.2])
      ((keep _ (by decide) (by decide) (by decide)).trans hKc)
      ((keep _ (by decide) (by decide) (by decide)).trans h1)
      ((keep _ (by decide) (by decide) (by decide)).trans hZ)
    refine ⟨a, b, ?_⟩
    rw [take_succ_getElem rows hm, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact o

/-- The full row stream uses exactly the row-major order of the scheme's gadget coordinates. -/
theorem rows_digits_gadDec (D : Dims) (u v : Fin (setting D).E.W → Rg D) :
    ((List.ofFn (fun i ↦ (u i, v i))).flatMap
      (fun uv ↦ (List.range D.K).map (binaryDigit (uv.1 - uv.2)))) =
    (List.ofFn (fun i : Fin (setting D).E.W ↦ List.ofFn
      (fun c : Fin D.K ↦ gadDec (S := setting D) (u - v) (i, c)))).flatten := by
  rw [List.flatMap_def, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  exact range_digits_eq_ofFn (N := D.N) (K := D.K) (u i - v i)

end AdvancedEncryption.ExpLUT.Prog
