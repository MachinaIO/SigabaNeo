import PE.Impl.ExpLUT.Prog.EncAutMath

/-! # Digit-encryption rows and their streaming loop -/

namespace AdvancedEncryption.ExpLUT.Prog.EncW

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.Prog Matrix

variable (D : Dims)

/-- Encoding rows accept noncanonical secret words, as produced by automorphism routines. -/
theorem row_mat_word (M : Matrix (Fin 2) (Col D.K) (Rg D)) (rest : List Bool)
    {s u y : List Bool} (hs : s.length = D.N * D.K)
    (hu : u.length = D.N * D.K) (hy : y.length = D.N * D.K)
    (e : Col D.K → Rg D) (rest' : List Bool) :
    rowW D.N D.K (D.K + D.K) s ((matE D (Fin 2) (Col D.K)).enc M ++ rest)
      (((matE D (Fin 2) (Col D.K)).enc M ++ rest).drop ((D.K + D.K) * (D.N * D.K)))
      (zStream D.N D.K u y) ((vecE D (Col D.K)).enc e ++ rest') =
      (vecE D (Col D.K)).enc (sec (decRM D.N D.K s) ᵥ* M -
        (decRM D.N D.K u • sec (decRM D.N D.K y)) ᵥ* GD D + e) := by
  rw [← length_col D]
  refine rowW_fam D _ hs _ _ _ _ fun c hc => ?_
  rw [blk_matE_row0 D M rest hc, blk_matE_row1 D M rest hc,
    decRM_blk_zStream D hu hy hc, blk_vecE_append D e rest' hc,
    decRM_wd, decRM_wd, decRM_wd]
  simp only [Pi.add_apply, Pi.sub_apply, vecMul_sec]

/-- The scheme row encrypted for a digit index; indices in a loop are proved below `K`. -/
noncomputable def digitRow (s : List Bool) (a : Rg D)
    (A : ℕ → Fin 2 → Col D.K → Rg D) (E : ℕ → Col D.K → Rg D)
    (i : ℕ) : Col D.K → Rg D :=
  sec (decRM D.N D.K s) ᵥ* A i -
    ((setting D).D.d a ⟨i % D.K, Nat.mod_lt _ D.K_pos⟩ •
      sec (decRM D.N D.K s)) ᵥ* GD D + E i

/-- The actual digit extraction and row arithmetic agree with the scheme. -/
theorem deRow_scheme {s : List Bool} (hs : s.length = D.N * D.K) (a : Rg D)
    (A : ℕ → Fin 2 → Col D.K → Rg D) (E : ℕ → Col D.K → Rg D)
    (i : ℕ) (hi : i < D.K) (rest rest' : List Bool) :
    deRow D.N D.K (D.K + D.K) s
      (digitRW D.N D.K 0 ((rotBW D.N D.K 1)^[i] (wd D a)))
      ((matE D (Fin 2) (Col D.K)).enc (A i) ++ rest)
      ((vecE D (Col D.K)).enc (E i) ++ rest') =
      (vecE D (Col D.K)).enc (digitRow D s a A E i) := by
  unfold deRow
  rw [row_mat_word D (A i) rest hs (length_digitRW _ _ _ _) hs (E i) rest',
    decRM_digit_rot D a ⟨i, hi⟩]
  simp only [digitRow, Nat.mod_eq_of_lt hi]
  rfl

/-- Consecutive fixed-length words, with a start index for stream consumption. -/
def wordStream {α : Type} {n : ℕ} (e : FixedEnc α n) (f : ℕ → α) (j k : ℕ) : List Bool :=
  ((List.range' j k).map f).flatMap e.enc

@[simp] theorem wordStream_zero {α : Type} {n : ℕ} (e : FixedEnc α n)
    (f : ℕ → α) (j : ℕ) : wordStream e f j 0 = [] := rfl

theorem wordStream_succ {α : Type} {n : ℕ} (e : FixedEnc α n)
    (f : ℕ → α) (j k : ℕ) :
    wordStream e f j (k + 1) = e.enc (f j) ++ wordStream e f (j + 1) k := by
  simp [wordStream, List.range'_succ]

theorem length_wordStream {α : Type} {n : ℕ} (e : FixedEnc α n)
    (f : ℕ → α) (j k : ℕ) : (wordStream e f j k).length = k * n := by
  induction k generalizing j with
  | zero => simp
  | succ k ih => rw [wordStream_succ, List.length_append, e.length, ih]; ring

/-- All digits in a contiguous interval are encrypted and both input queues are consumed. -/
theorem deIn_stream {s : List Bool} (hs : s.length = D.N * D.K) (a : Rg D)
    (A : ℕ → Fin 2 → Col D.K → Rg D) (E : ℕ → Col D.K → Rg D)
    (j n : ℕ) (hjn : j + n ≤ D.K) (out rest rest' : List Bool)
    (hout : n * ((D.K + D.K) * (D.N * D.K)) ≤ out.length) :
    (deIn D.N D.K (D.K + D.K) s)^[n]
      ((rotBW D.N D.K 1)^[j] (wd D a), out,
        wordStream (matE D (Fin 2) (Col D.K)) A j n ++ rest,
        wordStream (vecE D (Col D.K)) E j n ++ rest') =
      ((rotBW D.N D.K 1)^[j + n] (wd D a),
        (out ++ wordStream (vecE D (Col D.K)) (digitRow D s a A E) j n).drop
          (n * ((D.K + D.K) * (D.N * D.K))), rest, rest') := by
  induction n generalizing j out with
  | zero => simp
  | succ n ih =>
    have hj : j < D.K := by omega
    have hn : (D.K + D.K) * (D.N * D.K) ≤ out.length := by
      rw [Nat.succ_mul] at hout; omega
    have hmat : ((matE D (Fin 2) (Col D.K)).enc (A j)).length =
        (D.K + D.K + (D.K + D.K)) * (D.N * D.K) := by
      rw [FixedEnc.length]
      simp only [len_fin, length_col]
      ring
    have hvec : ((vecE D (Col D.K)).enc (E j)).length =
        (D.K + D.K) * (D.N * D.K) := by rw [length_vecE', length_col]
    have hlen : ((out ++ (vecE D (Col D.K)).enc (digitRow D s a A E j)).drop
        ((D.K + D.K) * (D.N * D.K))).length = out.length := by
      rw [List.length_drop, List.length_append, length_vecE', length_col]; omega
    rw [Function.iterate_succ_apply]
    simp only [wordStream_succ, List.append_assoc, deIn]
    rw [deRow_scheme D hs a A E j hj,
      ← hmat, List.drop_left, ← hvec, List.drop_left, hvec,
      ← Function.iterate_succ_apply' (rotBW D.N D.K 1) j]
    rw [ih (j + 1) (by omega) _ (by rw [hlen]; rw [Nat.succ_mul] at hout; omega)]
    rw [show j + 1 + n = j + (n + 1) by omega]
    rw [List.drop_append_of_le_length hn, List.append_assoc]
    conv_rhs =>
      rw [Nat.succ_mul, Nat.add_comm (n * ((D.K + D.K) * (D.N * D.K)))
        ((D.K + D.K) * (D.N * D.K)), ← List.drop_drop,
        List.drop_append_of_le_length hn]

/-- One complete entry of the digit-encryption phase, including all `K` digits. -/
theorem deOut_scheme {s : List Bool} (hs : s.length = D.N * D.K) (a : Rg D)
    (A : ℕ → Fin 2 → Col D.K → Rg D) (E : ℕ → Col D.K → Rg D)
    (out restC restA restE : List Bool)
    (hout : D.K * ((D.K + D.K) * (D.N * D.K)) ≤ out.length) :
    deOut D.N D.K (D.K + D.K) s
      (wd D a ++ restC, out,
        wordStream (matE D (Fin 2) (Col D.K)) A 0 D.K ++ restA,
        wordStream (vecE D (Col D.K)) E 0 D.K ++ restE) =
      (restC, (out ++ wordStream (vecE D (Col D.K)) (digitRow D s a A E) 0 D.K).drop
        (D.K * ((D.K + D.K) * (D.N * D.K))), restA, restE) := by
  dsimp only [deOut]
  rw [show wd D a = encRM D.N D.K a from rfl,
    MVM.takeD_encRM_append, MVM.drop_encRM_append]
  have h := deIn_stream D hs a A E 0 D.K (by omega) out restA restE hout
  simp only [Function.iterate_zero_apply, Nat.zero_add] at h
  rw [show encRM D.N D.K a = wd D a from rfl, h]

/-- A consecutive stream of whole entry blocks. -/
def blockStream (f : ℕ → List Bool) (j n : ℕ) : List Bool :=
  (List.range' j n).flatMap f

@[simp] theorem blockStream_zero (f : ℕ → List Bool) (j : ℕ) :
    blockStream f j 0 = [] := rfl

theorem blockStream_succ (f : ℕ → List Bool) (j n : ℕ) :
    blockStream f j (n + 1) = f j ++ blockStream f (j + 1) n := by
  simp [blockStream, List.range'_succ]

/-- The complete digit phase encrypts every entry and consumes the three source streams. -/
theorem deOut_stream {s : List Bool} (hs : s.length = D.N * D.K) (f : ℕ → Rg D)
    (A : ℕ → ℕ → Fin 2 → Col D.K → Rg D) (E : ℕ → ℕ → Col D.K → Rg D)
    (j n : ℕ) (out restC restA restE : List Bool)
    (hout : n * (D.K * ((D.K + D.K) * (D.N * D.K))) ≤ out.length) :
    (deOut D.N D.K (D.K + D.K) s)^[n]
      (blockStream (fun t ↦ wd D (f t)) j n ++ restC, out,
        blockStream (fun t ↦ wordStream (matE D (Fin 2) (Col D.K)) (A t) 0 D.K) j n ++ restA,
        blockStream (fun t ↦ wordStream (vecE D (Col D.K)) (E t) 0 D.K) j n ++ restE) =
      (restC, (out ++ blockStream (fun t ↦ wordStream (vecE D (Col D.K))
        (digitRow D s (f t) (A t) (E t)) 0 D.K) j n).drop
          (n * (D.K * ((D.K + D.K) * (D.N * D.K)))), restA, restE) := by
  induction n generalizing j out with
  | zero => simp
  | succ n ih =>
    have hn : D.K * ((D.K + D.K) * (D.N * D.K)) ≤ out.length := by
      rw [Nat.succ_mul] at hout; omega
    have hrow : (wordStream (vecE D (Col D.K))
        (digitRow D s (f j) (A j) (E j)) 0 D.K).length =
        D.K * ((D.K + D.K) * (D.N * D.K)) := by
      rw [length_wordStream, length_col]
    have hlen : ((out ++ wordStream (vecE D (Col D.K))
        (digitRow D s (f j) (A j) (E j)) 0 D.K).drop
        (D.K * ((D.K + D.K) * (D.N * D.K)))).length = out.length := by
      rw [List.length_drop, List.length_append, hrow]; omega
    rw [Function.iterate_succ_apply]
    simp only [blockStream_succ, List.append_assoc]
    rw [deOut_scheme D hs (f j) (A j) (E j) out _ _ _ hn,
      ih (j + 1) _ (by rw [hlen]; rw [Nat.succ_mul] at hout; omega)]
    rw [List.drop_append_of_le_length hn, List.append_assoc]
    conv_rhs =>
      rw [Nat.succ_mul, Nat.add_comm (n * (D.K * ((D.K + D.K) * (D.N * D.K))))
        (D.K * ((D.K + D.K) * (D.N * D.K))), ← List.drop_drop,
        List.drop_append_of_le_length hn]

/-- Fixed templates, secret length, and blank scratch for the digit-encryption machine. -/
structure DigitOK (S : Store 74) : Prop where
  scratch : ∀ i : Fin 74, 15 ≤ i.val → S i = []
  hK : (S 5).length = D.K
  hN : (S 6).length = D.N
  hNK : (S 7).length = D.N * D.K
  hL : (S 8).length = D.K + D.K
  hK1 : (S 9).length = D.K - 1
  h10 : (S 10).length = (D.K + D.K) * (D.N * D.K)
  h11 : (S 11).length = (D.K + D.K) * (D.N * D.K)
  h12 : (S 12).length = (D.K + D.K + (D.K + D.K)) * (D.N * D.K)
  h13 : (S 13).length = 1
  secret : (S 1).length = D.N * D.K

/-- The actual digit-encryption program, for any number of canonical entries. -/
theorem run_deP_scheme (S : Store 74) (h : DigitOK D S) (f : ℕ → Rg D)
    (A : ℕ → ℕ → Fin 2 → Col D.K → Rg D) (E : ℕ → ℕ → Col D.K → Rg D)
    (j n : ℕ) (restC restA restE : List Bool) (hcount : (S 14).length = n)
    (hC : S 2 = blockStream (fun t ↦ wd D (f t)) j n ++ restC)
    (hA : S 3 = blockStream (fun t ↦
      wordStream (matE D (Fin 2) (Col D.K)) (A t) 0 D.K) j n ++ restA)
    (hE : S 4 = blockStream (fun t ↦
      wordStream (vecE D (Col D.K)) (E t) 0 D.K) j n ++ restE)
    (hout : n * (D.K * ((D.K + D.K) * (D.N * D.K))) ≤ (S 0).length) :
    deP.run S = Function.update (Function.update (Function.update (Function.update S 2 restC) 0
      ((S 0 ++ blockStream (fun t ↦ wordStream (vecE D (Col D.K))
        (digitRow D (S 1) (f t) (A t) (E t)) 0 D.K) j n).drop
          (n * (D.K * ((D.K + D.K) * (D.N * D.K)))))) 3 restA) 4 restE := by
  rw [run_deP D.K_pos S h.scratch h.hK h.hN h.hNK h.hL h.hK1 h.h10 h.h11 h.h12
    h.h13 h.secret, hcount, hC, hA, hE,
    deOut_stream D h.secret f A E j n (S 0) restC restA restE hout]
  rfl

end AdvancedEncryption.ExpLUT.Prog.EncW
