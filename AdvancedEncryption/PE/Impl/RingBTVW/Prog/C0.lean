import PE.Impl.RingBTVW.Prog.UBound

/-!
# The row `c₀ = s B₀ + e₀` as a component block

`c0P oB oS d N K : XProg 82` reads, from a word on tape `0`, the row `B₀` (`1 × d`, at the offset
`oB`) and the secret `s` followed by the error row `e₀` (at the offset `oS`), and leaves the word
of `scalar s * B₀ + e₀` alone on tape `0`:

1. templates of the sizes (`natP`);
2. two splits (`splitP`, framed): `B₀`, then `s` and `e₀`;
3. `scalar s * B₀` (`matMulP`, framed, `m = n = 1`, `l = d`) and the sum with `e₀` (`addRWP`,
   framed, `matAddW`);
4. copy the result to tape `0` and clear the scratch tapes.

* `law_c0P_words`: the law on words;
* **`law_c0IP`**: on the packed secret `(ab, σ)` of the ideal side the output is the word of
  `scalar r.s * B₀ + r.e₀` (`r = σ.2.2.2.2.1`, `B₀ = σ.2.1`): the field `c₀` of `sdI`;
* `time_c0P`: a uniform time bound (`UB`).
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.XProg Matrix AdvancedEncryption.RingBTVW.Fresh Cslib Cslib.Probability

/-! ### The program -/

/-- The tapes of the split of `B₀`. -/
def eS1 : Fin 10 ↪ Fin 82 := ⟨![16, 17, 18, 0, 2, 3, 4, 19, 20, 21], by decide⟩
/-- The tapes of the split of `s` and `e₀`. -/
def eS2 : Fin 10 ↪ Fin 82 := ⟨![22, 23, 24, 0, 5, 6, 7, 19, 20, 21], by decide⟩
/-- The tapes of the product. -/
def eM : Fin 59 ↪ Fin 82 := ⟨![25, 23, 17, 8, 9, 6, 11, 12, 13, 14, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74], by decide⟩
/-- The tapes of the sum. -/
def eA : Fin 28 ↪ Fin 82 := ⟨![75, 25, 24, 8, 15, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48], by decide⟩

theorem eS1_apply (j : Fin 10) : eS1 j = ![16, 17, 18, 0, 2, 3, 4, 19, 20, 21] j := rfl
theorem eS2_apply (j : Fin 10) : eS2 j = ![22, 23, 24, 0, 5, 6, 7, 19, 20, 21] j := rfl
theorem eM_apply (j : Fin 59) : eM j = ![25, 23, 17, 8, 9, 6, 11, 12, 13, 14, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74] j := rfl
theorem eA_apply (j : Fin 28) : eA j = ![75, 25, 24, 8, 15, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48] j := rfl

/-- The scratch tapes written by `c0P`. -/
def c0Tapes : List (Fin 82) :=
  [2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 22, 23, 24, 25, 75]

/-- **The row `c₀ = s B₀ + e₀`** from a word holding `B₀` at `oB` and `s, e₀` at `oS`. -/
def c0P (oB oS d N K : ℕ) : XProg 82 :=
  seq (natP 2 10 oB) <| seq (natP 3 10 (d * (N * K))) <| seq (natP 5 10 oS) <|
  seq (natP 6 10 (N * K)) <| seq (natP 7 10 (d * (N * K))) <| seq (natP 8 10 K) <|
  seq (natP 9 10 N) <| seq (natP 11 10 1) <| seq (natP 12 10 1) <| seq (natP 13 10 d) <|
  seq (natP 14 10 (1 * d * (N * K))) <| seq (natP 15 10 (1 * d * N)) <|
  seq (frame eS1 (prog Prog.splitP)) <| seq (frame eS2 (prog Prog.splitP)) <|
  seq (frame eM (prog Prog.matMulP)) <| seq (frame eA (prog Prog.addRWP)) <|
  seq (prog (.prim (.copy 0 75))) <| clearL c0Tapes

theorem wf_c0P (oB oS d N K : ℕ) : (c0P oB oS d N K).WF := by
  refine ⟨wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _,
    wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _,
    wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _,
    Prog.wf_splitP, Prog.wf_splitP, Prog.wf_matMulP, Prog.wf_addRWP, trivial, wf_clearL _⟩

theorem takeD_drop_mid {P X Y : List Bool} {a b : ℕ} (hP : P.length = a) (hX : X.length = b) :
    takeD b ((P ++ (X ++ Y)).drop a) = X := by
  rw [List.drop_left' hP, takeD_eq_take (by simp; omega), List.take_left' hX]

set_option maxHeartbeats 4000000 in
/-- **The law of `c0P` on words.** -/
theorem law_c0P_words {oB oS d N K : ℕ} (W P B0w Y P' sw e0w Z : List Bool)
    (hW1 : W = P ++ (B0w ++ Y)) (hP : P.length = oB) (hB : B0w.length = d * (N * K))
    (hW2 : W = P' ++ (sw ++ (e0w ++ Z))) (hP' : P'.length = oS) (hs : sw.length = N * K)
    (he : e0w.length = d * (N * K)) (hm : (matMulW N K 1 1 d sw B0w).length = 1 * d * N * K) :
    (c0P oB oS d N K).law (ioS (R := 80) W [] []) =
      PMF.pure (ioS (R := 80) (matAddW N K (1 * d) (matMulW N K 1 1 d sw B0w) e0w) [] []) := by
  have h1 : takeD (d * (N * K)) (W.drop oB) = B0w := by rw [hW1]; exact takeD_drop_mid hP hB
  have h2 : takeD (N * K) (W.drop oS) = sw := by rw [hW2]; exact takeD_drop_mid hP' hs
  have h3 : takeD (d * (N * K)) (W.drop (oS + N * K)) = e0w := by
    rw [hW2, show P' ++ (sw ++ (e0w ++ Z)) = (P' ++ sw) ++ (e0w ++ Z) by simp]
    exact takeD_drop_mid (by simp [hP', hs]) he
  unfold c0P
  rw [law_seq, law_natP (by decide) _ _ (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, law_frame_run eS1 _ Prog.noGrow_splitP, PMF.pure_bind,
    Prog.run_splitP _ (by simp [eS1_apply, ioS]) (by simp [eS1_apply, ioS]) (by simp [eS1_apply, ioS])]
  simp only [embedF_upd, embedF_comp]
  simp only [eS1_apply, Matrix.cons_val]
  rw [law_seq, law_frame_run eS2 _ Prog.noGrow_splitP, PMF.pure_bind,
    Prog.run_splitP _ (by simp [eS2_apply, ioS]) (by simp [eS2_apply, ioS]) (by simp [eS2_apply, ioS])]
  simp only [embedF_upd, embedF_comp]
  simp only [eS2_apply, Matrix.cons_val]
  rw [law_seq, law_frame_run eM _ Prog.noGrow_matMulP, PMF.pure_bind,
    Prog.run_matMulP (K := K) (N := N) (m := 1) (n := 1) (l := d) _
      (by intro i hi; fin_cases i <;> first | (simp at hi; done) | simp [eM_apply, ioS])
      (by simp [eM_apply]) (by simp [eM_apply]) (by simp [eM_apply]) (by simp [eM_apply])
      (by simp [eM_apply]) (by simp [eM_apply]) (by simp [eM_apply])
      (by simp [eM_apply, h2, hs]) (by simp [eM_apply, h1, hB])]
  simp only [embedF_upd, embedF_comp]
  simp only [eM_apply, Matrix.cons_val]
  rw [law_seq, law_frame_run eA _ Prog.noGrow_addRWP, PMF.pure_bind,
    Prog.run_addRWP_mat (K := K) (N := N) (L := 1 * d) _
      (by intro i hi; fin_cases i <;> first | (simp at hi; done) | simp [eA_apply, ioS])
      (by simp [eA_apply]) (by simp [eA_apply]) (by simp only [eA_apply, Matrix.cons_val, Function.update_apply]; simp [ioS, h1, h2]; simpa using hm)
      (by simp [eA_apply, h3, he]; ring)]
  simp only [embedF_upd, embedF_comp]
  simp only [eA_apply, Matrix.cons_val]
  rw [law_seq, law_prim, PMF.pure_bind, law_clearL]
  congr 1
  funext t
  simp only [h1, h2, h3, Prim.apply, Function.update_self]
  by_cases ht : t ∈ c0Tapes
  · rw [if_pos ht]
    simp only [c0Tapes, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ioS]
  · rw [if_neg ht]
    simp only [c0Tapes, List.mem_cons, List.not_mem_nil, or_false, not_or] at ht
    obtain ⟨t2, t3, t5, t6, t7, t8, t9, t11, t12, t13, t14, t15, t16, t17, t18, t22, t23, t24, t25,
      t75⟩ := ht
    simp only [Function.update_apply, t2, t3, t5, t6, t7, t8, t9, t11, t12, t13, t14, t15, t16, t17,
      t18, t22, t23, t24, t25, t75, if_false]
    by_cases t0 : t = 0
    · subst t0; simp [ioS]; rw [h1, h2, h3]
    · simp only [t0, if_false]
      by_cases t1 : t.val = 1
      · simp [ioS, t1]
      · have : t.val ≠ 0 := fun h => t0 (Fin.ext h)
        simp [ioS, t1, this]

/-! ### Time -/

/-- The sizes of the templates of `c0P`. -/
def sizeC0 (oB oS d N K : ℕ) : ℕ :=
  oB + d * (N * K) + oS + N * K + d * (N * K) + K + N + 1 + 1 + d + 1 * d * (N * K) + 1 * d * N

/-- **The time of `c0P`** from tapes below `M`. -/
def timeC0 (oB oS d N K M : ℕ) : ℕ :=
  (2 * oB + 1) * (4 * M + 12) + (2 * (d * (N * K)) + 1) * (4 * M + 12) +
    (2 * oS + 1) * (4 * M + 12) + (2 * (N * K) + 1) * (4 * M + 12) +
    (2 * (d * (N * K)) + 1) * (4 * M + 12) + (2 * K + 1) * (4 * M + 12) +
    (2 * N + 1) * (4 * M + 12) + (2 * 1 + 1) * (4 * M + 12) + (2 * 1 + 1) * (4 * M + 12) +
    (2 * d + 1) * (4 * M + 12) + (2 * (1 * d * (N * K)) + 1) * (4 * M + 12) +
    (2 * (1 * d * N) + 1) * (4 * M + 12) +
    Prog.timeBound Prog.splitP M + Prog.timeBound Prog.splitP M + Prog.timeBound Prog.matMulP M +
    Prog.timeBound Prog.addRWP M + (2 * (M + 1) + 3) +
    (c0Tapes.length * (2 * (M + 1 + 1) + 3) + (2 * (M + 1 + 1) + 3))

theorem ub_c0P (oB oS d N K M : ℕ) (hM : sizeC0 oB oS d N K ≤ M) :
    UB (c0P oB oS d N K) M (timeC0 oB oS d N K M) (M + 1) := by
  unfold sizeC0 at hM
  have u := (ub_natP (t := (2 : Fin 82)) (c := 10) (by decide) (n := oB) (M := M) (by omega)).seq <|
    (ub_natP (t := (3 : Fin 82)) (c := 10) (by decide) (n := d * (N * K)) (M := M) (by omega)).seq <|
    (ub_natP (t := (5 : Fin 82)) (c := 10) (by decide) (n := oS) (M := M) (by omega)).seq <|
    (ub_natP (t := (6 : Fin 82)) (c := 10) (by decide) (n := N * K) (M := M) (by omega)).seq <|
    (ub_natP (t := (7 : Fin 82)) (c := 10) (by decide) (n := d * (N * K)) (M := M) (by omega)).seq <|
    (ub_natP (t := (8 : Fin 82)) (c := 10) (by decide) (n := K) (M := M) (by omega)).seq <|
    (ub_natP (t := (9 : Fin 82)) (c := 10) (by decide) (n := N) (M := M) (by omega)).seq <|
    (ub_natP (t := (11 : Fin 82)) (c := 10) (by decide) (n := 1) (M := M) (by omega)).seq <|
    (ub_natP (t := (12 : Fin 82)) (c := 10) (by decide) (n := 1) (M := M) (by omega)).seq <|
    (ub_natP (t := (13 : Fin 82)) (c := 10) (by decide) (n := d) (M := M) (by omega)).seq <|
    (ub_natP (t := (14 : Fin 82)) (c := 10) (by decide) (n := 1 * d * (N * K)) (M := M)
      (by omega)).seq <|
    (ub_natP (t := (15 : Fin 82)) (c := 10) (by decide) (n := 1 * d * N) (M := M) (by omega)).seq <|
    (ub_frame eS1 _ Prog.noGrow_splitP M).seq <| (ub_frame eS2 _ Prog.noGrow_splitP M).seq <|
    (ub_frame eM _ Prog.noGrow_matMulP M).seq <| (ub_frame eA _ Prog.noGrow_addRWP M).seq <|
    (ub_prim (.copy 0 75) M).seq <| ub_clearL (M + 1) c0Tapes
  refine u.mono (le_of_eq ?_) le_rfl
  simp only [timeC0, Nat.add_assoc]

/-- **The time of the `c₀` block** on inputs of at most `a`, `b` bits. -/
theorem time_c0P (oB oS d N K a b : ℕ) :
    timeBoundT (c0P oB oS d N K) (io2 (R := 80) a b 0) ≤
      timeC0 oB oS d N K (max a b + sizeC0 oB oS d N K) :=
  (ub_c0P oB oS d N K _ (by omega) _ fun i => by
    simp only [io2]; split_ifs <;> omega).1

/-! ### The ideal side -/

section Ideal

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The offset of `B₀` in the packed secret of the ideal side. -/
def oB0I : ℕ := fencLen (inst3Enc (N := N) (K := K) (k := k)) + nA

/-- The offset of the secret `s` of the coins in the packed secret of the ideal side. -/
def oSI : ℕ := oB0I (N := N) (K := K) (k := k) + fencLen (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)) +
  fencLen (wEnc hk c) + N * K

/-- **The component block of `c₀` on the ideal side.** -/
def c0IP : XProg 82 := c0P (oB0I (N := N) (K := K) (k := k)) (oSI hk c) c.d N K

theorem matW_one_one (M : Matrix (Fin 1) (Fin 1) (Rg N K)) :
    matW N K 1 1 M = (ringEnc N K).enc (M 0 0) := by
  simp [matW, concatN]

theorem length_matEnc_row (d : ℕ) (B : Matrix (Fin 1) (Fin d) (Rg N K)) :
    ((matEnc (N := N) (K := K) (Fin 1) (Fin d)).enc B).length = d * (N * K) := by
  rw [(matEnc (N := N) (K := K) (Fin 1) (Fin d)).length]; simp [Enum.list]

/-- **The law of the `c₀` block of the ideal side**: the word of `scalar r.s * B₀ + r.e₀`. -/
theorem law_c0IP (ab : Inst3T N K k) (σ : SecI hk c) :
    (c0IP hk c).law (ioS (R := 80)
      (((inst3Enc (N := N) (K := K) (k := k)).prod (secIEnc hk c)).enc (ab, σ)) [] []) =
      PMF.pure (ioS (R := 80) ((matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc
        (scalar σ.2.2.2.2.1.s * σ.2.1 + σ.2.2.2.2.1.e₀)) [] []) := by
  set r := σ.2.2.2.2.1
  set B₀ := σ.2.1
  have hsw : (ringEnc N K).enc r.s = matW N K 1 1 (scalar r.s) := by rw [matW_one_one]; rfl
  have hm : (matMulW N K 1 1 c.d ((ringEnc N K).enc r.s)
      ((matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc B₀)).length = 1 * c.d * N * K := by
    rw [hsw, matEnc_fin_eq_matW, matMulW_enc, length_matW]; ring
  rw [c0IP, law_c0P_words _ ((inst3Enc (N := N) (K := K) (k := k)).enc ab ++ attrEnc.enc σ.1)
    ((matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc B₀) _
    ((inst3Enc (N := N) (K := K) (k := k)).enc ab ++ (attrEnc.enc σ.1 ++
      ((matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc B₀ ++ ((wEnc hk c).enc σ.2.2.1 ++
        (ringEnc N K).enc σ.2.2.2.1))))
    ((ringEnc N K).enc r.s) ((matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc r.e₀) _
    (by simp only [FixedEnc.prod, secIEnc, List.append_assoc]; rfl)
    (by simp [length_enc, (attrEnc).length, oB0I])
    (length_matEnc_row _ _)
    (by simp only [FixedEnc.prod, secIEnc, coinsEnc, FixedEnc.comap, coinsTuple, List.append_assoc]; rfl)
    (by simp [length_enc, (attrEnc).length, (ringEnc N K).length, oSI, oB0I, Nat.add_assoc])
    ((ringEnc N K).length _) (length_matEnc_row _ _) hm]
  congr 2
  rw [hsw, matEnc_fin_eq_matW, matEnc_fin_eq_matW, matMulW_enc, matAddW_enc, matEnc_fin_eq_matW]

theorem wf_c0IP : (c0IP hk c).WF := wf_c0P _ _ _ _ _

end Ideal

end AdvancedEncryption.RingBTVW.Prog
