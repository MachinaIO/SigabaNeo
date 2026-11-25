import PE.Impl.ExpLUT.Prog.RedKeyPktPub

/-!
# The packet stream, part 12: the loops of the public words (generic `N K`)

* **`pbBitC`** (`t < b`): pop `H_{(t,0)}`, `H_{(t,1)}` from `pbQH`, `h_{(t,0)}`, `h_{(t,1)}` from `pbQh`,
  `A^aut_t` from `pbQA`; `G_t` (`pbGC`, `σ = σ_g^{2^t}`); `ptPB ++= G_t ++ Aa_t ++ Hf_t`; `P := P ++ P`
  (**`exec_pbBitC`**);
* **`pbStepC`** (`i < 16`): `ptPS ++= Ain_i ++ a_i ++ cb_i ++ pz_i ++ pu_i` (**`exec_pbStepC`**);
* **`pbPubC`**: the cursors, both loops and `A₀` (**`exec_pbPubC`**).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyPkt

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo.NegaG
open SigabaNeo.Lattices.Algo (encRM)
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

/-! ### The bit loop -/

/-- One bit `t`. -/
def pbBitBody : Code :=
  .seq (pbPopC pbH0 pbQH ptTM) <| .seq (pbPopC pbH1 pbQH ptTM) <|
  .seq (pbPopC pbh1 pbQh pbTV) <| .seq (pbPopC pbh1 pbQh pbTV) <|
  .seq (pbPopC pbAa pbQA ptTAa) <| .seq pbGC <|
  .seq (.app ptPB pbG) <| .seq (.app ptPB pbAa) <| .seq (.app ptPB pbH0) (.app pbP pbP)

/-- **The bit loop.** -/
def pbBitC : Code :=
  .seq (.clr ptPB) <| .seq (.cp pbP rB1) <| .seq (.cp pbCT ptTB) (.rep pbCT pbBitBody)

/-- The registers the bit body reads and never writes. -/
def pbBitR (r : Fin 64) : Bool :=
  r == ptTM || r == pbTV || r == ptTAa || r == pbTC || r == pbTN || r == pbKg

theorem pbBitBody_writes : ∀ r : Fin 64, pbBitR r = true ∨ r = pbCT → pbBitBody.writes r = false := by
  decide

theorem exec_pbBitBody {N K : ℕ} (hN : 0 < N) (hK : 0 < K) (w : St) (Hf h0 Aa : List Bool)
    (r0 r1 r2 : List (Rq N K)) (restH resth restA : List Bool)
    (hQH : w pbQH = Hf ++ (encL N K (r0 ++ r1) ++ restH))
    (hQh : w pbQh = h0 ++ (encL N K r2 ++ resth)) (hQA : w pbQA = Aa ++ restA)
    (lHf : Hf.length = (w ptTM).length) (lH : (encL N K (r0 ++ r1)).length = (w ptTM).length)
    (lh0 : h0.length = (w pbTV).length) (lh : (encL N K r2).length = (w pbTV).length)
    (lAa : Aa.length = (w ptTAa).length)
    (l0 : r0.length = (w pbTC).length) (l1 : r1.length = (w pbTC).length)
    (l2 : r2.length = (w pbTC).length)
    (hTN : (w pbTN).length = N * K) (hg : 0 < (w pbKg).length) :
    let w' := exec N K pbBitBody w
    w' ptPB = w ptPB ++ (encL N K (pbGL (pbSig (w pbKg).length (w pbP).length) r0 r1 r2) ++
        (Aa ++ Hf)) ∧
      w' pbQH = restH ∧ w' pbQh = resth ∧ w' pbQA = restA ∧ w' pbP = w pbP ++ w pbP := by
  intro w'
  have e1 := exec_pbPopC (N := N) (K := K) pbH0 pbQH ptTM (by decide) (by decide) (by decide) w _ _
    hQH lHf
  set w1 := exec N K (pbPopC pbH0 pbQH ptTM) w with hw1
  have e2 := exec_pbPopC (N := N) (K := K) pbH1 pbQH ptTM (by decide) (by decide) (by decide) w1
    (encL N K (r0 ++ r1)) restH
    (by rw [e1]; simp [Function.update_apply]) (by rw [e1]; simpa [Function.update_apply] using lH)
  set w2 := exec N K (pbPopC pbH1 pbQH ptTM) w1 with hw2
  have e3 := exec_pbPopC (N := N) (K := K) pbh1 pbQh pbTV (by decide) (by decide) (by decide) w2
    h0 (encL N K r2 ++ resth)
    (by rw [e2, e1]; simpa [Function.update_apply] using hQh)
    (by rw [e2, e1]; simpa [Function.update_apply] using lh0)
  set w3 := exec N K (pbPopC pbh1 pbQh pbTV) w2 with hw3
  have e4 := exec_pbPopC (N := N) (K := K) pbh1 pbQh pbTV (by decide) (by decide) (by decide) w3
    (encL N K r2) resth
    (by rw [e3]; simp [Function.update_apply])
    (by rw [e3, e2, e1]; simpa [Function.update_apply] using lh)
  set w4 := exec N K (pbPopC pbh1 pbQh pbTV) w3 with hw4
  have e5 := exec_pbPopC (N := N) (K := K) pbAa pbQA ptTAa (by decide) (by decide) (by decide) w4
    Aa restA
    (by rw [e4, e3, e2, e1]; simpa [Function.update_apply] using hQA)
    (by rw [e4, e3, e2, e1]; simpa [Function.update_apply] using lAa)
  set w5 := exec N K (pbPopC pbAa pbQA ptTAa) w4 with hw5
  have v5 : ∀ r, r ≠ pbH0 → r ≠ pbQH → r ≠ pbH1 → r ≠ pbh1 → r ≠ pbQh → r ≠ pbAa → r ≠ pbQA →
      w5 r = w r := by
    intro r a1 a2 a3 a4 a5 a6 a7
    rw [e5, e4, e3, e2, e1]; simp [Function.update_apply, a1, a2, a3, a4, a5, a6, a7]
  have g6 := exec_pbGC (N := N) (K := K) hN hK w5 r0 r1 r2
    (by rw [e5, e4, e3, e2, e1]; simp [Function.update_apply])
    (by rw [e5, e4]; simp [Function.update_apply])
    (by rw [v5 pbTC (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact l0)
    (by rw [v5 pbTC (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact l1)
    (by rw [v5 pbTC (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact l2)
    (by rw [v5 pbTN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hTN)
    (by rw [v5 pbKg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hg)
  rw [v5 pbKg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    v5 pbP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] at g6
  set w6 := exec N K pbGC w5 with hw6
  have f6 : ∀ r, pbGC.writes r = false → w6 r = w5 r := fun r h => exec_writes _ _ _ h
  have hw' : w' = exec N K (.app pbP pbP) (exec N K (.app ptPB pbH0) (exec N K (.app ptPB pbAa)
      (exec N K (.app ptPB pbG) w6))) := rfl
  rw [hw']
  simp only [exec_app, Function.update_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [show (ptPB : Fin 64) ≠ pbP by decide, if_true, if_false]
    rw [g6, f6 ptPB (by decide), f6 pbAa (by decide), f6 pbH0 (by decide),
      v5 ptPB (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      e5, e4, e3, e2, e1]
    simp [Function.update_apply, List.append_assoc]
  · simp only [show (pbQH : Fin 64) ≠ pbP by decide, show (pbQH : Fin 64) ≠ ptPB by decide,
      if_false]
    rw [f6 pbQH (by decide), e5, e4, e3, e2]; simp [Function.update_apply]
  · simp only [show (pbQh : Fin 64) ≠ pbP by decide, show (pbQh : Fin 64) ≠ ptPB by decide,
      if_false]
    rw [f6 pbQh (by decide), e5, e4]; simp [Function.update_apply]
  · simp only [show (pbQA : Fin 64) ≠ pbP by decide, show (pbQA : Fin 64) ≠ ptPB by decide,
      if_false]
    rw [f6 pbQA (by decide), e5]; simp [Function.update_apply]
  · simp only [show (pbP : Fin 64) ≠ ptPB by decide, if_true, if_false]
    rw [f6 pbP (by decide),
      v5 pbP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]

theorem range'_flatMap_succ {α : Type*} (f : ℕ → List α) (t b : ℕ) (ht : t < b) (u : List α) :
    (List.range' t (b - t)).flatMap f ++ u = f t ++ ((List.range' (t + 1) (b - (t + 1))).flatMap f ++ u) := by
  obtain ⟨k, hk⟩ : ∃ k, b - t = k + 1 := ⟨b - t - 1, by omega⟩
  rw [hk, range'_flatMap_cons, List.append_assoc, show b - (t + 1) = k by omega]

/-- **The bit loop.** -/
theorem exec_pbBitC {N K : ℕ} (hN : 0 < N) (hK : 0 < K) (b : ℕ) (w : St)
    (Hf h0 Aa : ℕ → List Bool) (r0 r1 r2 : ℕ → List (Rq N K)) (tH th tA : List Bool)
    (hQH : w pbQH = (List.range b).flatMap (fun t => Hf t ++ encL N K (r0 t ++ r1 t)) ++ tH)
    (hQh : w pbQh = (List.range b).flatMap (fun t => h0 t ++ encL N K (r2 t)) ++ th)
    (hQA : w pbQA = (List.range b).flatMap Aa ++ tA)
    (lHf : ∀ t, (Hf t).length = (w ptTM).length)
    (lH : ∀ t, (encL N K (r0 t ++ r1 t)).length = (w ptTM).length)
    (lh0 : ∀ t, (h0 t).length = (w pbTV).length) (lh : ∀ t, (encL N K (r2 t)).length = (w pbTV).length)
    (lAa : ∀ t, (Aa t).length = (w ptTAa).length)
    (l0 : ∀ t, (r0 t).length = (w pbTC).length) (l1 : ∀ t, (r1 t).length = (w pbTC).length)
    (l2 : ∀ t, (r2 t).length = (w pbTC).length)
    (hTB : (w ptTB).length = b) (hB1 : w rB1 = [false])
    (hTN : (w pbTN).length = N * K) (hg : 0 < (w pbKg).length) :
    exec N K pbBitC w ptPB = (List.range b).flatMap (fun t =>
      encL N K (pbGL (pbSig (w pbKg).length (2 ^ t)) (r0 t) (r1 t) (r2 t)) ++ (Aa t ++ Hf t)) := by
  set w1 := exec N K (.cp pbCT ptTB) (exec N K (.cp pbP rB1) (exec N K (.clr ptPB) w)) with hw1
  have fr1 : ∀ r, r ≠ pbCT → r ≠ pbP → r ≠ ptPB → w1 r = w r := by
    intro r a b c; simp [hw1, Function.update_apply, a, b, c]
  have hc : (w1 pbCT).length = b := by simp [hw1, hTB]
  have key := exec_rep_inv2 (N := N) (K := K) pbCT pbBitBody (pbBitBody_writes _ (Or.inr rfl))
    (fun t v => v ptPB = (List.range t).flatMap (fun t =>
        encL N K (pbGL (pbSig (w pbKg).length (2 ^ t)) (r0 t) (r1 t) (r2 t)) ++ (Aa t ++ Hf t)) ∧
      v pbQH = (List.range' t (b - t)).flatMap (fun t => Hf t ++ encL N K (r0 t ++ r1 t)) ++ tH ∧
      v pbQh = (List.range' t (b - t)).flatMap (fun t => h0 t ++ encL N K (r2 t)) ++ th ∧
      v pbQA = (List.range' t (b - t)).flatMap Aa ++ tA ∧
      v pbP = List.replicate (2 ^ t) false) w1
    ⟨by simp [hw1], by rw [fr1 _ (by decide) (by decide) (by decide), hQH, List.range_eq_range', Nat.sub_zero],
     by rw [fr1 _ (by decide) (by decide) (by decide), hQh, List.range_eq_range', Nat.sub_zero],
     by rw [fr1 _ (by decide) (by decide) (by decide), hQA, List.range_eq_range', Nat.sub_zero],
     by simp [hw1, Function.update_apply, hB1]⟩
    (by
      intro t v ht hP _ hfr
      rw [hc] at ht
      obtain ⟨h1, h2, h3, h4, h5⟩ := hP
      set vv := Function.update v pbCT (v pbCT).tail with hvv
      have fr : ∀ r, pbBitR r = true → vv r = w r := fun r hr => by
        have hrc : r ≠ pbCT := by rintro rfl; revert hr; decide
        rw [hvv, Function.update_of_ne hrc, hfr r (pbBitBody_writes r (Or.inl hr)) hrc,
          fr1 r hrc (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)]
      have vP : vv pbP = List.replicate (2 ^ t) false := by
        rw [hvv, Function.update_of_ne (by decide), h5]
      obtain ⟨o1, o2, o3, o4, o5⟩ := exec_pbBitBody (N := N) (K := K) hN hK vv (Hf t) (h0 t) (Aa t)
        (r0 t) (r1 t) (r2 t) _ _ _
        (by rw [hvv, Function.update_of_ne (by decide), h2, range'_flatMap_succ _ t b ht,
          List.append_assoc])
        (by rw [hvv, Function.update_of_ne (by decide), h3, range'_flatMap_succ _ t b ht,
          List.append_assoc])
        (by rw [hvv, Function.update_of_ne (by decide), h4, range'_flatMap_succ _ t b ht])
        (by rw [fr ptTM rfl]; exact lHf t) (by rw [fr ptTM rfl]; exact lH t)
        (by rw [fr pbTV rfl]; exact lh0 t) (by rw [fr pbTV rfl]; exact lh t)
        (by rw [fr ptTAa rfl]; exact lAa t) (by rw [fr pbTC rfl]; exact l0 t)
        (by rw [fr pbTC rfl]; exact l1 t) (by rw [fr pbTC rfl]; exact l2 t)
        (by rw [fr pbTN rfl]; exact hTN) (by rw [fr pbKg rfl]; exact hg)
      refine ⟨?_, o2, o3, o4, ?_⟩
      · rw [o1, fr pbKg rfl, vP, List.length_replicate, hvv, Function.update_of_ne (by decide), h1,
          List.range_succ, List.flatMap_append]
        simp [List.append_assoc]
      · rw [o5, vP, ← List.replicate_add, pow_succ, mul_two])
  rw [hc] at key
  exact key.1

/-! ### The step loop -/

/-- One step `i`. -/
def pbStepBody : Code :=
  .seq (pbPopC pbH0 pbQAin ptTAa) <| .seq (.app ptPS pbH0) <|
  .seq (pbPopC pbH0 pbQa pbTV) <| .seq (.app ptPS pbH0) <|
  .seq (pbPopC pbH0 pbQcb pbTV) <| .seq (.app ptPS pbH0) <|
  .seq (pbPopC pbH0 swQZ pbTN) <| .seq (.app ptPS pbH0) <|
  .seq (pbPopC pbH0 swQU pbTN) (.app ptPS pbH0)

/-- **The step loop.** -/
def pbStepC : Code := .seq (.clr ptPS) <| .seq (.cp pbCT ptT16) (.rep pbCT pbStepBody)

theorem pbStepBody_writes : ∀ r : Fin 64, r = ptTAa ∨ r = pbTV ∨ r = pbTN ∨ r = pbCT →
    pbStepBody.writes r = false := by
  decide

theorem exec_pbStepBody {N K : ℕ} (w : St) (Ain a cb z u : List Bool)
    (rAin ra rcb rz ru : List Bool)
    (hAin : w pbQAin = Ain ++ rAin) (ha : w pbQa = a ++ ra) (hcb : w pbQcb = cb ++ rcb)
    (hz : w swQZ = z ++ rz) (hu : w swQU = u ++ ru)
    (lAin : Ain.length = (w ptTAa).length) (la : a.length = (w pbTV).length)
    (lcb : cb.length = (w pbTV).length) (lz : z.length = (w pbTN).length)
    (lu : u.length = (w pbTN).length) :
    let w' := exec N K pbStepBody w
    w' ptPS = w ptPS ++ ((Ain ++ (a ++ (cb ++ z))) ++ u) ∧ w' pbQAin = rAin ∧ w' pbQa = ra ∧
      w' pbQcb = rcb ∧ w' swQZ = rz ∧ w' swQU = ru := by
  intro w'
  have e1 := exec_pbPopC (N := N) (K := K) pbH0 pbQAin ptTAa (by decide) (by decide) (by decide)
    w _ _ hAin lAin
  set w1 := exec N K (.app ptPS pbH0) (exec N K (pbPopC pbH0 pbQAin ptTAa) w) with hw1
  have k1 : ∀ r, r ≠ ptPS → r ≠ pbH0 → r ≠ pbQAin → w1 r = w r := by
    intro r x y z; rw [hw1, exec_app, e1]; simp [Function.update_apply, x, y, z]
  have o1 : w1 ptPS = w ptPS ++ Ain := by rw [hw1, exec_app, e1]; simp [Function.update_apply]
  have e2 := exec_pbPopC (N := N) (K := K) pbH0 pbQa pbTV (by decide) (by decide) (by decide)
    w1 _ _ (by rw [k1 _ (by decide) (by decide) (by decide)]; exact ha)
    (by rw [k1 _ (by decide) (by decide) (by decide)]; exact la)
  set w2 := exec N K (.app ptPS pbH0) (exec N K (pbPopC pbH0 pbQa pbTV) w1) with hw2
  have k2 : ∀ r, r ≠ ptPS → r ≠ pbH0 → r ≠ pbQa → w2 r = w1 r := by
    intro r x y z; rw [hw2, exec_app, e2]; simp [Function.update_apply, x, y, z]
  have o2 : w2 ptPS = w1 ptPS ++ a := by rw [hw2, exec_app, e2]; simp [Function.update_apply]
  have e3 := exec_pbPopC (N := N) (K := K) pbH0 pbQcb pbTV (by decide) (by decide) (by decide)
    w2 _ _ (by rw [k2 _ (by decide) (by decide) (by decide),
      k1 _ (by decide) (by decide) (by decide)]; exact hcb)
    (by rw [k2 _ (by decide) (by decide) (by decide), k1 _ (by decide) (by decide) (by decide)];
        exact lcb)
  set w3 := exec N K (.app ptPS pbH0) (exec N K (pbPopC pbH0 pbQcb pbTV) w2) with hw3
  have k3 : ∀ r, r ≠ ptPS → r ≠ pbH0 → r ≠ pbQcb → w3 r = w2 r := by
    intro r x y z; rw [hw3, exec_app, e3]; simp [Function.update_apply, x, y, z]
  have o3 : w3 ptPS = w2 ptPS ++ cb := by rw [hw3, exec_app, e3]; simp [Function.update_apply]
  have e4 := exec_pbPopC (N := N) (K := K) pbH0 swQZ pbTN (by decide) (by decide) (by decide)
    w3 _ _ (by rw [k3 _ (by decide) (by decide) (by decide), k2 _ (by decide) (by decide) (by decide),
      k1 _ (by decide) (by decide) (by decide)]; exact hz)
    (by rw [k3 _ (by decide) (by decide) (by decide), k2 _ (by decide) (by decide) (by decide),
      k1 _ (by decide) (by decide) (by decide)]; exact lz)
  set w4 := exec N K (.app ptPS pbH0) (exec N K (pbPopC pbH0 swQZ pbTN) w3) with hw4
  have k4 : ∀ r, r ≠ ptPS → r ≠ pbH0 → r ≠ swQZ → w4 r = w3 r := by
    intro r x y z; rw [hw4, exec_app, e4]; simp [Function.update_apply, x, y, z]
  have o4 : w4 ptPS = w3 ptPS ++ z := by rw [hw4, exec_app, e4]; simp [Function.update_apply]
  have e5 := exec_pbPopC (N := N) (K := K) pbH0 swQU pbTN (by decide) (by decide) (by decide)
    w4 _ _ (by rw [k4 _ (by decide) (by decide) (by decide), k3 _ (by decide) (by decide) (by decide),
      k2 _ (by decide) (by decide) (by decide), k1 _ (by decide) (by decide) (by decide)]; exact hu)
    (by rw [k4 _ (by decide) (by decide) (by decide), k3 _ (by decide) (by decide) (by decide),
      k2 _ (by decide) (by decide) (by decide), k1 _ (by decide) (by decide) (by decide)]; exact lu)
  have hw' : w' = exec N K (.app ptPS pbH0) (exec N K (pbPopC pbH0 swQU pbTN) w4) := rfl
  have k5 : ∀ r, r ≠ ptPS → r ≠ pbH0 → r ≠ swQU → w' r = w4 r := by
    intro r x y z; rw [hw', exec_app, e5]; simp [Function.update_apply, x, y, z]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hw', exec_app, e5]
    simp only [Function.update_apply, if_true, show (ptPS : Fin 64) ≠ pbH0 by decide,
      show (ptPS : Fin 64) ≠ swQU by decide, if_false]
    rw [o4, o3, o2, o1]; simp [List.append_assoc]
  · rw [k5 _ (by decide) (by decide) (by decide), k4 _ (by decide) (by decide) (by decide),
      k3 _ (by decide) (by decide) (by decide), k2 _ (by decide) (by decide) (by decide), hw1,
      exec_app, e1]
    simp [Function.update_apply]
  · rw [k5 _ (by decide) (by decide) (by decide), k4 _ (by decide) (by decide) (by decide),
      k3 _ (by decide) (by decide) (by decide), hw2, exec_app, e2]
    simp [Function.update_apply]
  · rw [k5 _ (by decide) (by decide) (by decide), k4 _ (by decide) (by decide) (by decide), hw3,
      exec_app, e3]
    simp [Function.update_apply]
  · rw [k5 _ (by decide) (by decide) (by decide), hw4, exec_app, e4]
    simp [Function.update_apply]
  · rw [hw', exec_app, e5]; simp [Function.update_apply]

/-- **The step loop.** -/
theorem exec_pbStepC {N K : ℕ} (w : St) (Ain a cb z u : ℕ → List Bool)
    (tAin ta tcb : List Bool)
    (hAin : w pbQAin = (List.range 16).flatMap Ain ++ tAin)
    (ha : w pbQa = (List.range 16).flatMap a ++ ta)
    (hcb : w pbQcb = (List.range 16).flatMap cb ++ tcb)
    (hz : w swQZ = (List.range 16).flatMap z) (hu : w swQU = (List.range 16).flatMap u)
    (lAin : ∀ i, (Ain i).length = (w ptTAa).length) (la : ∀ i, (a i).length = (w pbTV).length)
    (lcb : ∀ i, (cb i).length = (w pbTV).length) (lz : ∀ i, (z i).length = (w pbTN).length)
    (lu : ∀ i, (u i).length = (w pbTN).length) (h16 : (w ptT16).length = 16) :
    exec N K pbStepC w ptPS =
      (List.range 16).flatMap fun i => (Ain i ++ (a i ++ (cb i ++ z i))) ++ u i := by
  set w1 := exec N K (.cp pbCT ptT16) (exec N K (.clr ptPS) w) with hw1
  have fr1 : ∀ r, r ≠ pbCT → r ≠ ptPS → w1 r = w r := by
    intro r x y; simp [hw1, Function.update_apply, x, y]
  have hc : (w1 pbCT).length = 16 := by simp [hw1, h16]
  have key := exec_rep_inv2 (N := N) (K := K) pbCT pbStepBody (pbStepBody_writes _ (by simp))
    (fun i v => v ptPS = (List.range i).flatMap (fun i => (Ain i ++ (a i ++ (cb i ++ z i))) ++ u i) ∧
      v pbQAin = (List.range' i (16 - i)).flatMap Ain ++ tAin ∧
      v pbQa = (List.range' i (16 - i)).flatMap a ++ ta ∧
      v pbQcb = (List.range' i (16 - i)).flatMap cb ++ tcb ∧
      v swQZ = (List.range' i (16 - i)).flatMap z ++ [] ∧
      v swQU = (List.range' i (16 - i)).flatMap u ++ []) w1
    ⟨by simp [hw1], by rw [fr1 _ (by decide) (by decide), hAin, List.range_eq_range', Nat.sub_zero],
     by rw [fr1 _ (by decide) (by decide), ha, List.range_eq_range', Nat.sub_zero],
     by rw [fr1 _ (by decide) (by decide), hcb, List.range_eq_range', Nat.sub_zero],
     by rw [fr1 _ (by decide) (by decide), hz, List.range_eq_range', Nat.sub_zero, List.append_nil],
     by rw [fr1 _ (by decide) (by decide), hu, List.range_eq_range', Nat.sub_zero, List.append_nil]⟩
    (by
      intro i v hi hP _ hfr
      rw [hc] at hi
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP
      set vv := Function.update v pbCT (v pbCT).tail with hvv
      have fr : ∀ r, r = ptTAa ∨ r = pbTV ∨ r = pbTN → vv r = w r := fun r hr => by
        have hrc : r ≠ pbCT := by rcases hr with rfl | rfl | rfl <;> decide
        rw [hvv, Function.update_of_ne hrc,
          hfr r (pbStepBody_writes r (by rcases hr with rfl | rfl | rfl <;> simp)) hrc,
          fr1 r hrc (by rcases hr with rfl | rfl | rfl <;> decide)]
      have hv : ∀ r, r ≠ pbCT → vv r = v r := fun r h => Function.update_of_ne h _ _
      obtain ⟨o1, o2, o3, o4, o5, o6⟩ := exec_pbStepBody (N := N) (K := K) vv (Ain i) (a i) (cb i)
        (z i) (u i) _ _ _ _ _
        (by rw [hv _ (by decide), h2, range'_flatMap_succ _ i 16 hi])
        (by rw [hv _ (by decide), h3, range'_flatMap_succ _ i 16 hi])
        (by rw [hv _ (by decide), h4, range'_flatMap_succ _ i 16 hi])
        (by rw [hv _ (by decide), h5, range'_flatMap_succ _ i 16 hi])
        (by rw [hv _ (by decide), h6, range'_flatMap_succ _ i 16 hi])
        (by rw [fr _ (Or.inl rfl)]; exact lAin i) (by rw [fr _ (Or.inr (Or.inl rfl))]; exact la i)
        (by rw [fr _ (Or.inr (Or.inl rfl))]; exact lcb i)
        (by rw [fr _ (Or.inr (Or.inr rfl))]; exact lz i)
        (by rw [fr _ (Or.inr (Or.inr rfl))]; exact lu i)
      refine ⟨?_, o2, o3, o4, o5, o6⟩
      rw [o1, hv _ (by decide), h1, List.range_succ, List.flatMap_append]
      simp [List.append_assoc])
  rw [hc] at key
  exact key.1

/-! ### The public phase -/

/-- The cursors of the bit loop (the public-key word in `2`, the ciphertext word in `1`). -/
def pbCurBC : Code :=
  .seq (.cp pbQH 2) <| .seq (.drop pbQH pbOH) <| .seq (.cp pbQh 1) <| .seq (.drop pbQh pbOh) <|
  .seq (.cp pbQA 2) (.drop pbQA pbOAa)

/-- The cursors of the step loop. -/
def pbCurSC : Code :=
  .seq (.cp pbQAin 2) <| .seq (.drop pbQAin pbOAin) <| .seq (.cp pbQa 2) <|
  .seq (.drop pbQa pbOa) <| .seq (.cp pbQcb 1) (.drop pbQcb pbOcb)

/-- `A₀`. -/
def pbA0C : Code := .seq (.cp pbH0 2) <| .seq (.drop pbH0 pbOA0) (pbPopC ptA0 pbH0 ptTM)

/-- **The public phase.** -/
def pbPubC : Code := .seq pbCurBC <| .seq pbBitC <| .seq pbCurSC <| .seq pbStepC pbA0C

/-- The registers the public phase reads (and never writes). -/
def pbInR (r : Fin 64) : Bool :=
  r == 1 || r == 2 || r == pbOH || r == pbOh || r == pbOAa || r == pbOAin || r == pbOa ||
    r == pbOcb || r == pbOA0 || r == ptTM || r == ptTAa || r == pbTV || r == pbTC || r == pbTN ||
    r == pbKg || r == ptTB || r == ptT16 || r == rB1

theorem pbPubC_keeps : ∀ r : Fin 64, pbInR r = true → pbPubC.writes r = false := by decide

theorem pbBitC_keeps : ∀ r : Fin 64, pbInR r = true ∨ r = swQZ ∨ r = swQU →
    pbBitC.writes r = false := by decide

theorem pbLate_keepsPB : (pbCurSC.writes ptPB || pbStepC.writes ptPB || pbA0C.writes ptPB ||
    pbA0C.writes ptPS) = false := by decide

theorem pbCurSC_keeps : ∀ r : Fin 64, pbInR r = true ∨ r = swQZ ∨ r = swQU →
    pbCurSC.writes r = false := by decide

theorem pbStepC_keeps : ∀ r : Fin 64, pbInR r = true → pbStepC.writes r = false := by decide

/-- **The public phase.** -/
theorem exec_pbPubC {N K : ℕ} (hN : 0 < N) (hK : 0 < K) (b : ℕ) (w : St)
    (Hf h0 Aa Ain a cb z u : ℕ → List Bool) (r0 r1 r2 : ℕ → List (Rq N K))
    (A0 tH th tA tAin ta tcb tA0 : List Bool)
    (hQH : (w 2).drop (w pbOH).length =
      (List.range b).flatMap (fun t => Hf t ++ encL N K (r0 t ++ r1 t)) ++ tH)
    (hQh : (w 1).drop (w pbOh).length =
      (List.range b).flatMap (fun t => h0 t ++ encL N K (r2 t)) ++ th)
    (hQA : (w 2).drop (w pbOAa).length = (List.range b).flatMap Aa ++ tA)
    (hAin : (w 2).drop (w pbOAin).length = (List.range 16).flatMap Ain ++ tAin)
    (ha : (w 2).drop (w pbOa).length = (List.range 16).flatMap a ++ ta)
    (hcb : (w 1).drop (w pbOcb).length = (List.range 16).flatMap cb ++ tcb)
    (hA0 : (w 2).drop (w pbOA0).length = A0 ++ tA0)
    (hz : w swQZ = (List.range 16).flatMap z) (hu : w swQU = (List.range 16).flatMap u)
    (lHf : ∀ t, (Hf t).length = (w ptTM).length)
    (lH : ∀ t, (encL N K (r0 t ++ r1 t)).length = (w ptTM).length)
    (lh0 : ∀ t, (h0 t).length = (w pbTV).length) (lh : ∀ t, (encL N K (r2 t)).length = (w pbTV).length)
    (lAa : ∀ t, (Aa t).length = (w ptTAa).length)
    (l0 : ∀ t, (r0 t).length = (w pbTC).length) (l1 : ∀ t, (r1 t).length = (w pbTC).length)
    (l2 : ∀ t, (r2 t).length = (w pbTC).length)
    (lAin : ∀ i, (Ain i).length = (w ptTAa).length) (la : ∀ i, (a i).length = (w pbTV).length)
    (lcb : ∀ i, (cb i).length = (w pbTV).length) (lz : ∀ i, (z i).length = (w pbTN).length)
    (lu : ∀ i, (u i).length = (w pbTN).length) (lA0 : A0.length = (w ptTM).length)
    (hTB : (w ptTB).length = b) (hB1 : w rB1 = [false]) (h16 : (w ptT16).length = 16)
    (hTN : (w pbTN).length = N * K) (hg : 0 < (w pbKg).length) :
    let w' := exec N K pbPubC w
    w' ptPB = (List.range b).flatMap (fun t =>
        encL N K (pbGL (pbSig (w pbKg).length (2 ^ t)) (r0 t) (r1 t) (r2 t)) ++ (Aa t ++ Hf t)) ∧
      w' ptPS = (List.range 16).flatMap (fun i => (Ain i ++ (a i ++ (cb i ++ z i))) ++ u i) ∧
      w' ptA0 = A0 := by
  intro w'
  -- the cursors
  set w1 := exec N K pbCurBC w with hw1
  have k1 : ∀ r, r ≠ pbQH → r ≠ pbQh → r ≠ pbQA → w1 r = w r := by
    intro r x y z; simp [hw1, pbCurBC, exec_seq, Function.update_apply, x, y, z]
  have c1 : w1 pbQH = (w 2).drop (w pbOH).length ∧ w1 pbQh = (w 1).drop (w pbOh).length ∧
      w1 pbQA = (w 2).drop (w pbOAa).length := by
    simp [hw1, pbCurBC, exec_seq, Function.update_apply]
  have kin : ∀ r, pbInR r = true ∨ r = swQZ ∨ r = swQU → w1 r = w r := fun r hr =>
    k1 r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)
      (by rintro rfl; revert hr; decide)
  -- the bit loop
  have B := exec_pbBitC (N := N) (K := K) hN hK b w1 Hf h0 Aa r0 r1 r2 tH th tA
    (by rw [c1.1, hQH]) (by rw [c1.2.1, hQh]) (by rw [c1.2.2, hQA])
    (by rw [kin ptTM (by simp [pbInR])]; exact lHf) (by rw [kin ptTM (by simp [pbInR])]; exact lH)
    (by rw [kin pbTV (by simp [pbInR])]; exact lh0) (by rw [kin pbTV (by simp [pbInR])]; exact lh)
    (by rw [kin ptTAa (by simp [pbInR])]; exact lAa) (by rw [kin pbTC (by simp [pbInR])]; exact l0)
    (by rw [kin pbTC (by simp [pbInR])]; exact l1) (by rw [kin pbTC (by simp [pbInR])]; exact l2)
    (by rw [kin ptTB (by simp [pbInR])]; exact hTB) (by rw [kin rB1 (by simp [pbInR])]; exact hB1)
    (by rw [kin pbTN (by simp [pbInR])]; exact hTN) (by rw [kin pbKg (by simp [pbInR])]; exact hg)
  rw [kin pbKg (by simp [pbInR])] at B
  set w2 := exec N K pbBitC w1 with hw2
  have k2 : ∀ r, pbInR r = true ∨ r = swQZ ∨ r = swQU → w2 r = w r := fun r hr => by
    rw [hw2, exec_writes _ _ _ (pbBitC_keeps r hr), kin r hr]
  -- the step cursors
  set w3 := exec N K pbCurSC w2 with hw3
  have c3 : w3 pbQAin = (w 2).drop (w pbOAin).length ∧ w3 pbQa = (w 2).drop (w pbOa).length ∧
      w3 pbQcb = (w 1).drop (w pbOcb).length := by
    simp only [hw3, pbCurSC, exec_seq, exec_cp, exec_drop, Function.update_apply]
    simp [k2 2 (by simp [pbInR]), k2 1 (by simp [pbInR]), k2 pbOAin (by simp [pbInR]),
      k2 pbOa (by simp [pbInR]), k2 pbOcb (by simp [pbInR])]
  have k3 : ∀ r, pbInR r = true ∨ r = swQZ ∨ r = swQU → w3 r = w r := fun r hr => by
    rw [hw3, exec_writes _ _ _ (pbCurSC_keeps r hr), k2 r hr]
  -- the step loop
  have S := exec_pbStepC (N := N) (K := K) w3 Ain a cb z u tAin ta tcb
    (by rw [c3.1, hAin]) (by rw [c3.2.1, ha]) (by rw [c3.2.2, hcb])
    (by rw [k3 swQZ (by simp), hz]) (by rw [k3 swQU (by simp), hu])
    (by rw [k3 ptTAa (by simp [pbInR])]; exact lAin) (by rw [k3 pbTV (by simp [pbInR])]; exact la)
    (by rw [k3 pbTV (by simp [pbInR])]; exact lcb) (by rw [k3 pbTN (by simp [pbInR])]; exact lz)
    (by rw [k3 pbTN (by simp [pbInR])]; exact lu) (by rw [k3 ptT16 (by simp [pbInR])]; exact h16)
  set w4 := exec N K pbStepC w3 with hw4
  have k4 : ∀ r, pbInR r = true → w4 r = w r := fun r hr => by
    rw [hw4, exec_writes _ _ _ (pbStepC_keeps r hr), k3 r (Or.inl hr)]
  -- A₀
  have hw' : w' = exec N K pbA0C w4 := rfl
  have hk := pbLate_keepsPB
  simp only [Bool.or_eq_false_iff] at hk
  obtain ⟨⟨⟨hk1, hk2⟩, hk3⟩, hk4⟩ := hk
  refine ⟨?_, ?_, ?_⟩
  · rw [hw', exec_writes _ _ _ hk3, hw4, exec_writes _ _ _ hk2, hw3, exec_writes _ _ _ hk1, B]
  · rw [hw', exec_writes _ _ _ hk4, S]
  · rw [hw']
    have e := exec_pbPopC (N := N) (K := K) ptA0 pbH0 ptTM (by decide) (by decide) (by decide)
      (exec N K (.drop pbH0 pbOA0) (exec N K (.cp pbH0 2) w4)) A0 tA0
      (by simp [Function.update_apply, k4 2 (by simp [pbInR]), k4 pbOA0 (by simp [pbInR]), hA0])
      (by simp [Function.update_apply, k4 ptTM (by simp [pbInR]), lA0])
    show exec N K (pbPopC ptA0 pbH0 ptTM) (exec N K (.drop pbH0 pbOA0) (exec N K (.cp pbH0 2) w4))
      ptA0 = A0
    rw [e]; simp

end AdvancedEncryption.ExpLUT.Prog.RedKeyPkt
