import PE.Impl.ExpLUT.Prog.EncInputCodec

/-! # All four encryption-tail phases composed on the actual tape store -/

namespace AdvancedEncryption.ExpLUT.Prog.EncW

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.Prog Matrix
open PE.BranchingProgram

variable (D : Dims)

/-- Data and semantic templates at the entrance to the encryption tail. -/
structure TailInput (S : Store 104) (mpk : MPKt D) (x : Attribute w8) (μ : Bool)
    (r : EncCoins (setting D) (Wb D) (Jh D) Pos) : Prop where
  secret : S 1 = wd D r.s
  one : S 16 = wd D 1
  message : S 15 = [μ]
  zero : S 37 = List.replicate (D.N * D.K) false
  rotation : ∀ i < 8, τT S i = 2 * D.N - wSt * 2 ^ (7 - i)
  entries : (S 34).length = D.K + D.K + (D.K + D.K)
  positions : (S 35).length = 16
  xBot : S 2 = encAttribute w8 x
  xDig : S 3 = encAttribute w8 x
  aBot : S 4 = (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc mpk.a
  aDig : S 5 = (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc mpk.a
  aCopy : S 6 = (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc mpk.a
  eBot : S 7 = (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc r.ein
  eDig : S 8 = (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc r.ein
  matrices : S 9 = (FixedEnc.fun (α := Pos)
    (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc mpk.Ain
  errors : S 10 = (FixedEnc.fun (α := Pos)
    (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc r.edin
  initialMatrix : S 11 = (matE D (Fin 2) (Col D.K)).enc mpk.A0
  initialError : S 12 = (vecE D (Col D.K)).enc r.e0
  messageVector : S 13 = (vecE D (Fin 2)).enc mpk.d
  messageError : S 14 = wd D r.em

/-- Four ciphertext fields shifted into the existing fixed-size output register. -/
noncomputable def tailOutput (ct : CTt D) (out : List Bool) : List Bool :=
  let b := (out ++ (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc ct.cinBot).drop
    (16 * ((D.K + D.K) * (D.N * D.K)))
  let c := (b ++ (FixedEnc.fun (α := Pos)
    (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc ct.cin).drop
      (16 * ((D.K + D.K + (D.K + D.K)) * (D.K * ((D.K + D.K) * (D.N * D.K)))))
  let z := (c ++ (vecE D (Col D.K)).enc ct.c0).drop ((D.K + D.K) * (D.N * D.K))
  (z ++ wd D ct.cm).drop (D.N * D.K)

/-- Consuming bottom-row streams leaves all rotation templates unchanged. -/
theorem τT_cbG (S : Store 104) (v : List Bool × List Bool × List Bool × List Bool) :
    τT (cbG S v) = τT S := by
  have hf : ∀ j : Fin 74, 6 ≤ j.val → j.val < 14 → (cbG S v) (tCb1 j) = S (tCb1 j) := by
    intro j hj hj'
    obtain ⟨x, a, e, o⟩ := v
    fin_cases j <;> simp [cbG, tCb1] at hj hj' ⊢
  funext i
  simp only [τT, τOf, Function.comp]
  rw [hf _ (by simp) (by simp; omega)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The entire actual encryption tail writes the four scheme fields in ciphertext order. -/
theorem run_tailP_ciphertext (S : Store 104) (h : TailOK D.K D.N S)
    (mpk : MPKt D) (x : Attribute w8) (μ : Bool)
    (r : EncCoins (setting D) (Wb D) (Jh D) Pos) (d : TailInput D S mpk x μ r)
    (hN : 2 ≤ D.N) (hw : wSt * 128 ≤ 2 * D.N)
    (hbot : 16 * ((D.K + D.K) * (D.N * D.K)) ≤ (S 0).length)
    (hdig : 16 * ((D.K + D.K + (D.K + D.K)) *
      (D.K * ((D.K + D.K) * (D.N * D.K)))) ≤ (S 0).length) :
    (tailP.run S) 0 = tailOutput D
      (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r) (S 0) := by
  let ct := encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r
  let ob := (S 0 ++ (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc ct.cinBot).drop
    (16 * ((D.K + D.K) * (D.N * D.K)))
  let B := cbG S ([], [], [], ob)
  have hbrun : cinbotP.run S = B := run_cinbotP_ciphertext D S h hN hw mpk x μ r
    d.secret d.one d.rotation d.positions d.xBot d.aBot d.eBot hbot
  have hB : TailOK D.K D.N B := by
    apply h.of_agree
    · intro i hi; fin_cases i <;> simp [B, cbG, h.hs] at hi ⊢
    · intro i hi; fin_cases i <;> simp [B, cbG] at hi ⊢
  have hblen : (B 0).length = (S 0).length := by
    have hl : ((FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc ct.cinBot).length =
        16 * ((D.K + D.K) * (D.N * D.K)) := by
      simpa only [len_fin, w8_len, length_col] using
        (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).length ct.cinBot
    simp only [B, cbG, Function.update_self, ob, List.length_drop, List.length_append, hl]
    omega
  let oc := (B 0 ++ (FixedEnc.fun (α := Pos)
    (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc ct.cin).drop
      (16 * ((D.K + D.K + (D.K + D.K)) * (D.K * ((D.K + D.K) * (D.N * D.K)))))
  let C := ciG B ([], [], [], [], [], [], oc)
  have hcrun : cinP.run B = C := run_cinP_ciphertext D B hB hN hw mpk x μ r
    (by simpa [B, cbG] using d.secret) (by simpa [B, cbG] using d.one)
    (by simpa only [B, τT_cbG] using d.rotation)
    (by simpa [B, cbG] using d.entries) (by simpa [B, cbG] using d.positions)
    (by simpa [B, cbG] using d.xDig) (by simpa [B, cbG] using d.aDig)
    (by simpa [B, cbG] using d.eDig) (by simpa [B, cbG] using d.aCopy)
    (by simpa [B, cbG] using d.matrices) (by simpa [B, cbG] using d.errors)
    (by rw [hblen]; exact hdig)
  have hC : TailOK D.K D.N C := tailOK_ciG hB _
  have hlast := run_lastRows_ciphertext D C hC mpk x μ r
    (by simpa [C, ciG, B, cbG] using d.secret)
    (by simpa [C, ciG, B, cbG] using d.one)
    (by simpa [C, ciG, B, cbG] using d.message)
    (by simpa [C, ciG, B, cbG] using d.zero)
    (by simpa [C, ciG, B, cbG] using d.initialMatrix)
    (by simpa [C, ciG, B, cbG] using d.initialError)
    (by simpa [C, ciG, B, cbG] using d.messageVector)
    (by simpa [C, ciG, B, cbG] using d.messageError)
  simp only [tailP, Prog.run_seq]
  rw [hbrun, hcrun]
  change ((Prog.seq c0P cmP).run C) 0 = _
  rw [hlast]
  rfl

/-- The last four fields in their final ciphertext serialization order. -/
noncomputable def tailWord (ct : CTt D) : List Bool :=
  (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc ct.cinBot ++
    (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc ct.cin ++
      (vecE D (Col D.K)).enc ct.c0 ++ wd D ct.cm

/-- Append a block while retaining the original register length when capacity suffices. -/
def shiftAppend (out word : List Bool) : List Bool := (out ++ word).drop word.length

theorem shiftAppend_comp (out a b : List Bool) (ha : a.length ≤ out.length) :
    shiftAppend (shiftAppend out a) b = shiftAppend out (a ++ b) := by
  unfold shiftAppend
  rw [List.drop_append_of_le_length ha, List.append_assoc]
  conv_rhs => rw [List.length_append, ← List.drop_drop, List.drop_append_of_le_length ha]

/-- Four shifts are one append/drop operation, with no truncation of the new fields. -/
theorem tailOutput_eq (ct : CTt D) (out : List Bool) (h : (tailWord D ct).length ≤ out.length) :
    tailOutput D ct out = (out ++ tailWord D ct).drop (tailWord D ct).length := by
  let a := (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc ct.cinBot
  let b := (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc ct.cin
  let c := (vecE D (Col D.K)).enc ct.c0
  let d := wd D ct.cm
  have ha : a.length = 16 * ((D.K + D.K) * (D.N * D.K)) := by
    simpa only [len_fin, w8_len, length_col] using
      (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).length ct.cinBot
  have hb : b.length = 16 * ((D.K + D.K + (D.K + D.K)) *
      (D.K * ((D.K + D.K) * (D.N * D.K)))) := by
    have hl := (FixedEnc.fun (α := Pos)
      (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).length ct.cin
    change b.length = _ at hl
    rw [hl]
    simp only [Dig, Col, Enum.length_prod, len_fin, w8_len]
    ring
  have hc : c.length = (D.K + D.K) * (D.N * D.K) := by
    simpa only [length_col] using (vecE D (Col D.K)).length ct.c0
  have hd : d.length = D.N * D.K := length_wd D ct.cm
  have hr : tailOutput D ct out = shiftAppend (shiftAppend (shiftAppend (shiftAppend out a) b) c) d := by
    simp only [shiftAppend, ha, hb, hc, hd]
    rfl
  have ht : tailWord D ct = ((a ++ b) ++ c) ++ d := rfl
  rw [ht, List.length_append, List.length_append, List.length_append] at h
  rw [hr, shiftAppend_comp out a b (by omega),
    shiftAppend_comp out (a ++ b) c (by simp only [List.length_append]; omega),
    shiftAppend_comp out ((a ++ b) ++ c) d (by simp only [List.length_append]; omega)]
  rfl

/-- The composed executable tail produces the concatenation of the scheme's four final fields. -/
theorem run_tailP_word (S : Store 104) (h : TailOK D.K D.N S)
    (mpk : MPKt D) (x : Attribute w8) (μ : Bool)
    (r : EncCoins (setting D) (Wb D) (Jh D) Pos) (d : TailInput D S mpk x μ r)
    (hN : 2 ≤ D.N) (hw : wSt * 128 ≤ 2 * D.N)
    (hbot : 16 * ((D.K + D.K) * (D.N * D.K)) ≤ (S 0).length)
    (hdig : 16 * ((D.K + D.K + (D.K + D.K)) *
      (D.K * ((D.K + D.K) * (D.N * D.K)))) ≤ (S 0).length)
    (hout : (tailWord D (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r)).length ≤
      (S 0).length) :
    (tailP.run S) 0 = (S 0 ++ tailWord D
      (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r)).drop
        (tailWord D (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r)).length := by
  rw [run_tailP_ciphertext D S h mpk x μ r d hN hw hbot hdig, tailOutput_eq D _ _ hout]

/-- Ciphertext fields already written before entering the tail. -/
noncomputable def prefixWord (ct : CTt D) : List Bool :=
  (vecE D (BCol (Wb D) D.K)).enc ct.b ++
    (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc ct.h ++
      (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc ct.caut

/-- The full ciphertext codec splits at the entrance to the tail. -/
theorem ctEnc_prefix_tail (ct : CTt D) :
    (ctEnc D).enc ct = prefixWord D ct ++ tailWord D ct := by
  simp [ctEnc, prefixWord, tailWord, FixedEnc.comap, FixedEnc.prod, List.append_assoc]

/-- When preceding phases have filled the prefix, the actual tail completes the ciphertext codec. -/
theorem run_tailP_serialized (S : Store 104) (h : TailOK D.K D.N S)
    (mpk : MPKt D) (x : Attribute w8) (μ : Bool)
    (r : EncCoins (setting D) (Wb D) (Jh D) Pos) (d : TailInput D S mpk x μ r)
    (hN : 2 ≤ D.N) (hw : wSt * 128 ≤ 2 * D.N)
    (hbot : 16 * ((D.K + D.K) * (D.N * D.K)) ≤ (S 0).length)
    (hdig : 16 * ((D.K + D.K + (D.K + D.K)) *
      (D.K * ((D.K + D.K) * (D.N * D.K)))) ≤ (S 0).length)
    (hprefix : S 0 = List.replicate
      (tailWord D (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r)).length false ++
      prefixWord D (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r)) :
    (tailP.run S) 0 = (ctEnc D).enc
      (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r) := by
  rw [run_tailP_word D S h mpk x μ r d hN hw hbot hdig
    (by rw [hprefix]; simp), hprefix, List.append_assoc]
  simp only [List.drop_append, List.length_replicate, List.drop_replicate,
    Nat.sub_self, Nat.zero_sub, List.replicate_zero, List.nil_append, List.drop_zero]
  exact (ctEnc_prefix_tail D _).symm

end AdvancedEncryption.ExpLUT.Prog.EncW
