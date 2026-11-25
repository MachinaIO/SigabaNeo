import PE.Impl.ExpLUT.Prog.EncRun
import PE.Impl.ExpLUT.Prog.EncReadyTail

/-! # Complete deterministic encryption from encoded inputs -/
namespace AdvancedEncryption.ExpLUT.Prog.EncW
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.Prog Matrix
open PE.BranchingProgram
variable (D : Dims) (mpk : MPKt D) (x : Attribute w8) (μ : Bool)
  (r : EncCoins (setting D) (Wb D) (Jh D) Pos)

theorem run_ready_tail (hN : 2 ≤ D.N) (hw : wSt * 128 ≤ 2 * D.N) (o : List Bool)
    (ho : (tailWord D (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r)).length ≤ o.length) :
    tailP.run (Function.update (readyCore D mpk x μ r ∘ tailSlot) 0 o) 0 =
      shiftAppend o (tailWord D (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r)) := by
  let ct := encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r
  have hbot : ((FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc ct.cinBot).length =
      16 * ((D.K + D.K) * (D.N * D.K)) := by
    simpa only [len_fin, w8_len, length_col] using
      (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).length ct.cinBot
  have hdig : ((FixedEnc.fun (α := Pos)
      (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc ct.cin).length =
      16 * ((D.K + D.K + (D.K + D.K)) * (D.K * ((D.K + D.K) * (D.N * D.K)))) := by
    rw [(FixedEnc.fun (α := Pos)
      (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).length ct.cin]
    simp only [Dig, Col, Enum.length_prod, len_fin, w8_len]
    ring
  have hcap := ho
  change (tailWord D ct).length ≤ o.length at hcap
  simp only [tailWord, List.length_append] at hcap
  rw [hbot, hdig] at hcap
  exact run_tailP_word D _ (tailOK_output (ready_tailOK D mpk x μ r) o) mpk x μ r
    ((ready_tailData D mpk x μ r).output o) hN hw
    (by simp only [Function.update_self]; omega)
    (by simp only [Function.update_self]; omega)
    (by simpa only [Function.update_self] using ho)

@[simp] theorem length_shiftAppend (out word : List Bool) :
    (shiftAppend out word).length = out.length := by
  simp [shiftAppend, List.length_drop, List.length_append]

theorem shiftAppend_comp_any (out a b : List Bool) :
    shiftAppend (shiftAppend out a) b = shiftAppend out (a ++ b) := by
  simpa only [shiftAppend, List.length_append] using (drop_append_drop out a b)

theorem ctEnc_four_parts (ct : CTt D) : (ctEnc D).enc ct =
    ((bWord D ct ++ hWord D ct) ++ aWord D ct) ++ tailWord D ct := by
  rw [ctEnc_prefix_tail]
  rfl

theorem update_bView (S : Store 321) :
    Function.update (S ∘ bSlot) 0 (S 0) = S ∘ bSlot :=
  Function.update_eq_self 0 (S ∘ bSlot)

/-- The concrete core returns the scheme ciphertext from its actual initialized store. -/
theorem run_encCoreP_ciphertext (hb : 0 < D.b) (hN : 2 ≤ D.N)
    (hw : wSt * 128 ≤ 2 * D.N) :
    (encCoreP D).run (readyCore D mpk x μ r) 0 =
      (ctEnc D).enc (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r) := by
  let ct := encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r
  let S := readyCore D mpk x μ r
  let o := S 0
  have ho : o.length = ((ctEnc D).enc ct).length := by
    rw [show o = readyCore D mpk x μ r 0 from rfl, ready_output, List.length_replicate,
      (ctEnc D).length ct]
    rfl
  have hparts := ho
  rw [ctEnc_four_parts D ct] at hparts
  simp only [List.length_append] at hparts
  have hH : (hWord D ct).length ≤ o.length := by omega
  have hA : (aWord D ct).length ≤ o.length := by omega
  have hT : (tailWord D ct).length ≤ o.length := by omega
  have hbRun : mrowP.run (S ∘ bSlot) 0 = shiftAppend o (bWord D ct) := by
    have hh := run_ready_b D mpk x μ r o
    have he : Function.update (S ∘ bSlot) 0 o = S ∘ bSlot := update_bView S
    change mrowP.run (Function.update (S ∘ bSlot) 0 o) 0 = _ at hh
    rw [he] at hh
    exact hh
  rw [run_encCoreP_output D S, hbRun]
  dsimp only
  rw [run_ready_helper D mpk x μ r hb _ (by simpa only [length_shiftAppend] using hH)]
  rw [run_ready_aut D mpk x μ r hb _ (by simpa only [length_shiftAppend] using hA)]
  rw [run_ready_tail D mpk x μ r hN hw _ (by simpa only [length_shiftAppend] using hT)]
  simp only [shiftAppend_comp_any, ← List.append_assoc]
  rw [← ctEnc_four_parts D ct]
  change (o ++ (ctEnc D).enc ct).drop ((ctEnc D).enc ct).length = _
  rw [← ho, List.drop_left]

/-- Actual encoded public/coin input words produce the exact serialized ciphertext. -/
theorem run_initializedCoreP_ciphertext (hb : 0 < D.b) (hN : 2 ≤ D.N)
    (hw : wSt * 128 ≤ 2 * D.N) :
    (initializedCoreP D).run (encStart (encCoinWord D r)
      ((mpkEnc D).enc mpk ++ (encAttribute w8 x ++ [μ]))) 0 =
      (ctEnc D).enc (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r) := by
  rw [initializedCoreP, Prog.run_seq, run_encInitP_start, run_map coreTape_inj]
  change Function.extend coreTape _ _ (coreTape 0) = _
  rw [coreTape_inj.extend_apply]
  exact run_encCoreP_ciphertext D mpk x μ r hb hN hw

end AdvancedEncryption.ExpLUT.Prog.EncW
