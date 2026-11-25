import PE.Impl.RingBTVW.Prog.Lift
import SigabaNeo.Lib.Lattices.ProgAlgo.Spec
import SigabaNeo.Lib.Machines.Prog.Split

/-!
# The trapdoor row `B₁ = toB₁ (a, b)` as a component block

The public-key components of hybrid 3 and of the ideal side output `B₁ = [1 | a | G̲ − b]`
(`toB₁`) for the instance `(a, b)`. Here `b1P : XProg 82` computes its word from the instance word
`a ++ b` on tape `0` (tape `1` blank, the other tapes blank), leaving it alone on tape `0`:

1. templates of the sizes (`natP`): `K`, `N`, `N K`, `k`, the row length `L = 2k · N K` (twice),
   `2k · N` and `N K + 2L`;
2. split the instance word into `a`, `b` (`splitP`, framed);
3. the gadget row `G̲` (`gadP`, framed) and `G̲ − b` (`subRWP`, framed);
4. the word of `1` (`oneW`, `N K − 1` zeros and a leading `1`);
5. join `1`, `a`, `G̲ − b` (`joinP`, framed) onto tape `0`, and clear the scratch tapes.

* `law_b1P_words`: on words, the output is `oneW N K ++ aw ++ matSubW N K (1 · 2k) (gadW N K k) bw`;
* **`law_b1P`**: on the instance word of `(a, b)` the output is
  `(matEnc (Fin 1) (TrapCol k)).enc (toB₁ (Sdw hk) (a, b))`;
* `wf_b1P`.

Generic helpers: `law_frame_run` (the law of a framed deterministic program), `embedF_upd`,
`embedF_comp`, `clearL` and `law_clearL`.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.XProg Matrix AdvancedEncryption.RingBTVW.Fresh Cslib Cslib.Probability

/-! ### Helpers -/

section Helpers

variable {k n : ℕ}

theorem embedF_upd (e : Fin n ↪ Fin k) (s : Store k) (g : Store n) (o : Fin n) (v : List Bool) :
    embedF e s (Function.update g o v) = Function.update (embedF e s g) (e o) v := by
  funext t
  rcases embedF_cases e s (Function.update g o v) t with ⟨hn, h⟩ | ⟨j, rfl, h⟩
  · rw [h, Function.update_of_ne]
    · rcases embedF_cases e s g t with ⟨-, h'⟩ | ⟨j, rfl, -⟩
      · exact h'.symm
      · rw [partialInv_self] at hn; exact absurd hn (Option.some_ne_none _)
    · rintro rfl; rw [partialInv_self] at hn; exact Option.some_ne_none _ hn
  · rw [h]
    by_cases hj : j = o
    · subst hj; simp
    · rw [Function.update_of_ne hj, Function.update_of_ne (e.injective.ne hj), embedF_apply_self]

theorem embedF_comp (e : Fin n ↪ Fin k) (s : Store k) : embedF e s (fun j => s (e j)) = s := by
  funext t
  rcases embedF_cases e s (fun j => s (e j)) t with ⟨-, h⟩ | ⟨j, rfl, h⟩ <;> exact h

/-- **The law of a framed deterministic program.** -/
theorem law_frame_run (e : Fin n ↪ Fin k) (p : Prog n) (hp : p.NoGrow) (s : Store k) :
    (frame e (prog p)).law s = PMF.pure (embedF e s (p.run fun j => s (e j))) := by
  rw [law_frame, law_prog_run p hp, PMF.pure_map]

/-- Clear the tapes of a list. -/
def clearL [NeZero k] : List (Fin k) → XProg k
  | [] => prog (.prim (.copy 0 0))
  | t :: l => seq (prog (.prim (.clear t))) (clearL l)

theorem law_clearL [NeZero k] : ∀ (l : List (Fin k)) (s : Store k),
    (clearL l).law s = PMF.pure (fun t => if t ∈ l then [] else s t)
  | [], s => by
    rw [clearL, law_prim]; congr 1; funext t; simp [Prim.apply]
  | t :: l, s => by
    rw [clearL, law_seq, law_prim, PMF.pure_bind, law_clearL l]
    congr 1
    funext u
    simp only [Prim.apply, List.mem_cons, Function.update_apply]
    by_cases h1 : u = t <;> by_cases h2 : u ∈ l <;> simp [h1, h2]

theorem wf_clearL [NeZero k] : ∀ l : List (Fin k), (clearL l).WF
  | [] => trivial
  | _ :: l => ⟨trivial, wf_clearL l⟩

end Helpers

/-! ### The word of `1` -/

theorem concatN_zero_tail (K : ℕ) (g : ℕ → List Bool) (hg : ∀ t, 0 < t → g t = zeroW K) :
    ∀ n, concatN (n + 1) g = g 0 ++ List.replicate (n * K) false
  | 0 => by simp [concatN]
  | n + 1 => by
    rw [concatN, concatN_zero_tail K g hg n, hg (n + 1) (by omega), zeroW, List.append_assoc,
      List.replicate_append_replicate, Nat.succ_mul]

theorem oneW_eq {N K : ℕ} (hN : 0 < N) (hK : 0 < K) :
    oneW N K = true :: List.replicate (N * K - 1) false := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  rw [oneW, constW, concatN_zero_tail (K' + 1) _ (fun t ht => by simp [Nat.pos_iff_ne_zero.mp ht])]
  simp only [if_true, bitW, zeroW, List.cons_append, List.replicate_append_replicate]
  congr 2
  rw [Nat.add_mul, Nat.mul_add, Nat.one_mul]; omega

/-! ### The program -/

/-- The tapes of the split. -/
def eS : Fin 10 ↪ Fin 82 := ⟨![11, 12, 13, 0, 6, 14, 9, 15, 16, 17], by decide⟩

/-- The tapes of the gadget row. -/
def eG : Fin 21 ↪ Fin 82 :=
  ⟨![18, 2, 3, 4, 5, 6, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33], by decide⟩

/-- The tapes of the subtraction. -/
def eD : Fin 28 ↪ Fin 82 :=
  ⟨![34, 18, 12, 2, 7, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53,
    54, 55, 56, 57], by decide⟩

/-- The tapes of the join. -/
def eJ : Fin 11 ↪ Fin 82 := ⟨![0, 58, 11, 34, 4, 6, 14, 8, 67, 68, 69], by decide⟩

theorem eS_apply (j : Fin 10) : eS j = ![11, 12, 13, 0, 6, 14, 9, 15, 16, 17] j := rfl
theorem eG_apply (j : Fin 21) : eG j =
    ![18, 2, 3, 4, 5, 6, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33] j := rfl
theorem eD_apply (j : Fin 28) : eD j =
    ![34, 18, 12, 2, 7, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53,
    54, 55, 56, 57] j := rfl
theorem eJ_apply (j : Fin 11) : eJ j = ![0, 58, 11, 34, 4, 6, 14, 8, 67, 68, 69] j := rfl

/-- The row length `2k · N K`. -/
abbrev rowL (N K k : ℕ) : ℕ := 1 * (2 * k) * (N * K)

/-- The scratch tapes written by `b1P`. -/
def b1Tapes : List (Fin 82) := [2, 3, 4, 5, 6, 7, 8, 11, 12, 13, 14, 18, 34, 58]

/-- **The trapdoor row from the instance word.** -/
def b1P (N K k : ℕ) : XProg 82 :=
  seq (natP 2 10 K) <| seq (natP 3 10 N) <| seq (natP 4 10 (N * K)) <| seq (natP 5 10 k) <|
  seq (natP 6 10 (rowL N K k)) <| seq (natP 14 10 (rowL N K k)) <|
  seq (natP 7 10 (1 * (2 * k) * N)) <| seq (natP 8 10 (N * K + rowL N K k + rowL N K k)) <|
  seq (frame eS (prog Prog.splitP)) <| seq (frame eG (prog Prog.gadP)) <|
  seq (frame eD (prog Prog.subRWP)) <| seq (natP 58 10 (N * K - 1)) <|
  seq (prog (.prim (.cons 58 true))) <| seq (frame eJ (prog Prog.joinP)) <| clearL b1Tapes

theorem wf_b1P (N K k : ℕ) : (b1P N K k).WF := by
  refine ⟨wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _,
    wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _,
    Prog.wf_splitP, Prog.wf_gadP, Prog.wf_subRWP, wf_natP (by decide) _, trivial, Prog.wf_joinP,
    wf_clearL _⟩

set_option maxHeartbeats 2000000 in
theorem law_b1P_words {N K k : ℕ} (hN : 0 < N) (hK : 0 < K) (hkK : 2 ^ K ≤ 2 ^ k) (aw bw : List Bool)
    (ha : aw.length = rowL N K k) (hb : bw.length = rowL N K k) :
    (b1P N K k).law (ioS (R := 80) (aw ++ bw) [] []) =
      PMF.pure (ioS (R := 80) (oneW N K ++ aw ++
        takeD (rowL N K k) (matSubW N K (1 * (2 * k)) (gadW N K k) bw)) [] []) := by
  have h1 : takeD (rowL N K k) (aw ++ bw) = aw := by
    rw [takeD_eq_take (by simp; omega), List.take_left' ha]
  have h2 : takeD (rowL N K k) ((aw ++ bw).drop (rowL N K k)) = bw := by
    rw [List.drop_left' ha, takeD_of_length' hb]
  have h0 : ∀ w, takeD 0 w = [] := fun _ => rfl
  have hg : (gadW N K k).length = 1 * (2 * k) * N * K := by
    rw [gadW_enc hkK, rowW, length_matW]; ring
  unfold b1P
  rw [law_seq, law_natP (by decide) _ _ (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, law_frame_run eS _ Prog.noGrow_splitP, PMF.pure_bind,
    Prog.run_splitP _ (by simp [eS_apply, ioS]) (by simp [eS_apply, ioS]) (by simp [eS_apply, ioS])]
  simp only [embedF_upd, embedF_comp]
  simp only [eS_apply, eG_apply, eD_apply, eJ_apply, Matrix.cons_val]
  rw [law_seq, law_frame_run eG _ Prog.noGrow_gadP, PMF.pure_bind,
    Prog.run_gadP (K := K) (N := N) (k := k) _ (by intro i hi; fin_cases i <;> simp_all [eG_apply, ioS])
      (by simp [eG_apply]) (by simp [eG_apply]) (by simp [eG_apply]) (by simp [eG_apply]) (by simp [eG_apply])]
  simp only [embedF_upd, embedF_comp]
  simp only [eS_apply, eG_apply, eD_apply, eJ_apply, Matrix.cons_val]
  rw [law_seq, law_frame_run eD _ Prog.noGrow_subRWP, PMF.pure_bind,
    Prog.run_subRWP_mat (K := K) (N := N) (L := 1 * (2 * k)) _
      (by intro i hi; fin_cases i <;> simp_all [eD_apply, ioS])
      (by simp [eD_apply]) (by simp [eD_apply]) (by simp [eD_apply, hg]) (by simp [eD_apply, h2, hb]; ring)]
  simp only [embedF_upd, embedF_comp]
  simp only [eS_apply, eG_apply, eD_apply, eJ_apply, Matrix.cons_val]
  rw [law_seq, law_natP (by decide) _ _ (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, law_prim, PMF.pure_bind]
  rw [law_seq, law_frame_run eJ _ Prog.noGrow_joinP, PMF.pure_bind,
    Prog.run_joinP _ (by simp [eJ_apply, ioS, Prim.apply]) (by simp [eJ_apply, ioS, Prim.apply]) (by simp [eJ_apply, ioS, Prim.apply])
      (by simp [eJ_apply, Prim.apply])]
  simp only [embedF_upd, embedF_comp]
  simp only [eS_apply, eG_apply, eD_apply, eJ_apply, Matrix.cons_val]
  rw [law_clearL]
  congr 1
  funext t
  have hone : takeD (N * K) (true :: List.replicate (N * K - 1) false) = oneW N K := by
    rw [oneW_eq hN hK, takeD_of_length']
    simp only [List.length_cons, List.length_replicate]
    have : 0 < N * K := Nat.mul_pos hN hK
    omega
  simp only [h1, h2, Prim.apply, Function.update_self]
  by_cases ht : t ∈ b1Tapes
  · rw [if_pos ht]
    simp only [b1Tapes, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [ioS]
  · rw [if_neg ht]
    simp only [b1Tapes, List.mem_cons, List.not_mem_nil, or_false, not_or] at ht
    obtain ⟨t2, t3, t4, t5, t6, t7, t8, t11, t12, t13, t14, t18, t34, t58⟩ := ht
    simp only [Function.update_apply, t2, t3, t4, t5, t6, t7, t8, t11, t12, t13, t14, t18, t34, t58,
      if_false]
    by_cases t0 : t = 0
    · subst t0
      simp [ioS, hone]
      rw [h1, h2]
    · simp only [t0, if_false]
      by_cases t1 : t.val = 1
      · simp [ioS, t1]
      · have : t.val ≠ 0 := fun h => t0 (Fin.ext h)
        simp [ioS, t1, this]

/-! ### On the encodings -/

section Enc

variable {N K k : ℕ}

/-- **The codec's word of a row on the trapdoor columns**: the entry `1`, then the two blocks
`RingBTVW.Fresh.Col k`. -/
theorem matEnc_trap (M : Matrix (Fin 1) (TrapCol k) (Rg N K)) :
    (matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc M =
      (ringEnc N K).enc (M 0 (.inl 0)) ++
        ((matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Fresh.Col k)).enc (Matrix.of fun _ c => M 0 (.inr (.inl c))) ++
          (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Fresh.Col k)).enc (Matrix.of fun _ c => M 0 (.inr (.inr c)))) := by
  show (([0] : List (Fin 1)).map (fun i => (M i : TrapCol k → Rg N K))).flatMap
      (fun r => ((Enum.list (α := TrapCol k)).map r).flatMap (ringEnc N K).enc) =
    _ ++ ((([0] : List (Fin 1)).map (fun i => ((Matrix.of fun _ c => M 0 (.inr (.inl c)) :
        Matrix (Fin 1) (RingBTVW.Fresh.Col k) (Rg N K)) i : RingBTVW.Fresh.Col k → Rg N K))).flatMap
      (fun r => ((Enum.list (α := RingBTVW.Fresh.Col k)).map r).flatMap (ringEnc N K).enc) ++
      (([0] : List (Fin 1)).map (fun i => ((Matrix.of fun _ c => M 0 (.inr (.inr c)) :
        Matrix (Fin 1) (RingBTVW.Fresh.Col k) (Rg N K)) i : RingBTVW.Fresh.Col k → Rg N K))).flatMap
      (fun r => ((Enum.list (α := RingBTVW.Fresh.Col k)).map r).flatMap (ringEnc N K).enc))
  simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  show ((Enum.list (α := Fin 1)).map Sum.inl ++ ((Enum.list (α := RingBTVW.Fresh.Col k)).map Sum.inl ++
      (Enum.list (α := RingBTVW.Fresh.Col k)).map Sum.inr).map Sum.inr |>.map (M 0)).flatMap (ringEnc N K).enc = _
  simp only [List.map_append, List.map_map, List.flatMap_append]
  congr 1
  · have : (Enum.list (α := Fin 1)) = [0] := by simp [Enum.list]; rfl
    rw [this]; simp

variable (hk : 2 ^ K < 2 ^ k)

theorem length_rowW (B : Matrix (Fin 1) (RingBTVW.Fresh.Col k) (Rg N K)) : (rowW N K k B).length = rowL N K k := by
  rw [rowW, length_matW]

/-- **The trapdoor row component**: on the instance word of `(a, b)` the output is the word of
`toB₁ (a, b) = [1 | a | G̲ − b]`. -/
theorem law_b1P (hN : 0 < N) (hK : 0 < K) (ab : Inst3T N K k) :
    (b1P N K k).law (ioS (R := 80) ((inst3Enc (N := N) (K := K) (k := k)).enc ab) [] []) =
      PMF.pure (ioS (R := 80)
        ((matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc (toB₁ (Sdw (N := N) hk) ab)) [] []) := by
  have hw : (inst3Enc (N := N) (K := K) (k := k)).enc ab = rowW N K k ab.1 ++ rowW N K k ab.2 := by
    show (matEnc (Fin 1) (RingBTVW.Fresh.Col k)).enc ab.1 ++ (matEnc (Fin 1) (RingBTVW.Fresh.Col k)).enc ab.2 = _
    rw [Algo.matEnc_row, Algo.matEnc_row]
  rw [hw, law_b1P_words hN hK hk.le _ _ (length_rowW _) (length_rowW _)]
  congr 2
  have hsub : matSubW N K (1 * (2 * k)) (gadW N K k) (rowW N K k ab.2) =
      rowW N K k ((Sdw (N := N) hk).Γ₁.G - ab.2) := by
    rw [gadW_enc hk.le, rowW, rowW, matSubW_enc, rowW, Matrix.submatrix_sub]
    rfl
  rw [hsub, takeD_of_length' (length_rowW _), matEnc_trap, Algo.matEnc_row, Algo.matEnc_row]
  simp only [toB₁, trapRowU, Matrix.of_apply, enc_one, List.append_assoc]
  congr 3 <;> ext i c <;> simp [Subsingleton.elim i 0]

end Enc

end AdvancedEncryption.RingBTVW.Prog
