import PE.Impl.DualUse.Prog.Pub5

/-!
# The challenge component of hybrid 5

`chal5P hk c` maps the packed secret of hybrid 5 and the message `μ` to
`(ctEnc hk c).enc (shiftCT hk c μ (view5 hk c i σ).2)`: the public-key body (`pub5Body`), then
`c₁ = [u₀ | u₀ a + v_a | u₀ z + v_z]`, the encodings `c_j = c₀ W_j + e_j`, `κ = u₀ p + v_p`, the join
and the flip of the bit of `half` under `μ`.

**`law_chal5P`**, `wf_chal5P`, `time_chal5P`, `len_chal5P`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.XProg Matrix AdvancedEncryption.RingBTVW
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord

variable {N K k : ℕ}

theorem mm_scalarC (s : Rg N K) (B : Matrix (Fin 1) (RingBTVW.Col k) (Rg N K)) :
    matMulW N K 1 1 (2 * k) ((ringEnc N K).enc s)
        ((DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc B) =
      (DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc (RingBTVW.scalar s * B) := by
  rw [show (ringEnc N K).enc s = (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin 1)).enc
    (RingBTVW.scalar s) by rw [matEnc_one_one]; rfl, matEnc_mul' (len_fin 1) (len_fin 1) len_col]

/-- The trapdoor row of an encryption, `[u | u_a | u_z]`. -/
def trapRowE (u : Rg N K) (ua uz : Matrix (Fin 1) (RingBTVW.Col k) (Rg N K)) :
    Matrix (Fin 1) (TrapCol k) (Rg N K) := Matrix.of fun _ c => match c with
  | .inl _ => u
  | .inr (.inl c) => ua 0 c
  | .inr (.inr c) => uz 0 c

theorem c15_word (u : Rg N K) (ua uz : Matrix (Fin 1) (RingBTVW.Col k) (Rg N K)) :
    takeD (N * K) ((ringEnc N K).enc u) ++
        takeD (rowL N K k) ((DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc ua) ++
        takeD (rowL N K k) ((DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc uz) =
      (DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc (trapRowE u ua uz) := by
  rw [Algo.matEnc_row, Algo.matEnc_row, takeD_of_length' ((ringEnc N K).length u),
    takeD_of_length' (length_rowW _), takeD_of_length' (length_rowW _), matEnc_trap, Algo.matEnc_row,
    Algo.matEnc_row]
  simp only [trapRowE, Matrix.of_apply, List.append_assoc]
  congr 3 <;> ext i c <;> simp [Subsingleton.elim i 0]

variable (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The tail of the challenge component of hybrid 5 after `pub5Body` (output on tape `10`). -/
def chal5TailBody : XProg 82 :=
  seq (frame ⟨vGet 12 0, by decide⟩ (getB (o5va c) (fC N K k))) <|
  seq (frame ⟨vMm 13 7 10, by decide⟩ (mmB (1) (1) (2 * k) N K)) <|
  seq (frame ⟨vAdd 14 13 12, by decide⟩ (addB (1 * (2 * k)) N K)) <|
  seq (frame ⟨vGet 12 0, by decide⟩ (getB (o5vz c) (fC N K k))) <|
  seq (frame ⟨vMm 13 7 11, by decide⟩ (mmB (1) (1) (2 * k) N K)) <|
  seq (frame ⟨vAdd 16 13 12, by decide⟩ (addB (1 * (2 * k)) N K)) <|
  seq (frame ⟨vJoin 17 7 14 16, by decide⟩ (joinB (N * K) (rowL N K k) (rowL N K k))) <|
  seq (frame ⟨vGet 12 0, by decide⟩ (getB (o5e hk c) (fencLen (eEnc (N := N) hk)))) <|
  seq (frame ⟨vHash 13 6 3 12, by decide⟩ (hashB (P1 N k * (2 * k)) (c.d) N K)) <|
  seq (frame ⟨vMm 10 7 18, by decide⟩ (mmB (1) (1) (1) N K)) <|
  seq (frame ⟨vGet 11 0, by decide⟩ (getB (o5vp c) (fR N K))) <|
  seq (frame ⟨vAdd 14 10 11, by decide⟩ (addB (1) N K)) <|
  seq (frame ⟨vJoin 16 8 3 17, by decide⟩ (joinB (fPsi N K k) (fD N K c.d) (fT N K k))) <|
  seq (frame ⟨vJoin 17 16 13 14, by decide⟩ (joinB (fPsi N K k + fD N K c.d + fT N K k) (fJ (N := N) hk) (fR N K))) <|
  frame ⟨vFl 10 17 1, by decide⟩ (flipB (offK hk c + (K - 1)) (fencLen (ctEnc hk c)))

theorem wf_chal5TailBody : (chal5TailBody hk c).WF := by
  unfold chal5TailBody
  exact ⟨wf_getB _ _, wf_mmB _ _ _ _ _, wf_addB _ _ _, wf_getB _ _, wf_mmB _ _ _ _ _, wf_addB _ _ _, wf_joinB _ _ _, wf_getB _ _, wf_hashB _ _ _ _, wf_mmB _ _ _ _ _, wf_getB _ _, wf_addB _ _ _, wf_joinB _ _ _, wf_joinB _ _ _, wf_flipB _ _⟩

/-- The sizes of the templates of `chal5TailBody`. -/
def sizechal5Tail : ℕ :=
  ((o5va c) + (fC N K k)) +
    sizeMmB (1) (1) (2 * k) N K +
    sizeAddB (1 * (2 * k)) N K +
    ((o5vz c) + (fC N K k)) +
    sizeMmB (1) (1) (2 * k) N K +
    sizeAddB (1 * (2 * k)) N K +
    ((N * K) + (rowL N K k) + (rowL N K k)) +
    ((o5e hk c) + (fencLen (eEnc (N := N) hk))) +
    sizeHashB (P1 N k * (2 * k)) (c.d) N K +
    sizeMmB (1) (1) (1) N K +
    ((o5vp c) + (fR N K)) +
    sizeAddB (1) N K +
    ((fPsi N K k) + (fD N K c.d) + (fT N K k)) +
    ((fPsi N K k + fD N K c.d + fT N K k) + (fJ (N := N) hk) + (fR N K)) +
    ((offK hk c + (K - 1)) + (fencLen (ctEnc hk c)))

/-- The time of `chal5TailBody` from tapes below `M`. -/
def timechal5Tail (M : ℕ) : ℕ :=
  timeGetB (o5va c) (fC N K k) M + (timeMmB (1) (1) (2 * k) N K M + (timeAddB (1 * (2 * k)) N K M + (timeGetB (o5vz c) (fC N K k) M + (timeMmB (1) (1) (2 * k) N K M + (timeAddB (1 * (2 * k)) N K M + (timeJoinB (N * K) (rowL N K k) (rowL N K k) M + (timeGetB (o5e hk c) (fencLen (eEnc (N := N) hk)) M + (timeHashB (P1 N k * (2 * k)) (c.d) N K M + (timeMmB (1) (1) (1) N K M + (timeGetB (o5vp c) (fR N K) M + (timeAddB (1) N K M + (timeJoinB (fPsi N K k) (fD N K c.d) (fT N K k) M + (timeJoinB (fPsi N K k + fD N K c.d + fT N K k) (fJ (N := N) hk) (fR N K) M + (timeFlipB (offK hk c + (K - 1)) (fencLen (ctEnc hk c)) M))))))))))))))

theorem ub_chal5TailBody (M : ℕ) (hM : sizechal5Tail hk c ≤ M) :
    UBZ 20 (chal5TailBody hk c) M (timechal5Tail hk c M) M := by
  unfold sizechal5Tail at hM
  exact (UBZ.frame _ (by decide) (ub_getB (o5va c) (fC N K k) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_mmB (1) (1) (2 * k) N K M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_addB (1 * (2 * k)) N K M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_getB (o5vz c) (fC N K k) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_mmB (1) (1) (2 * k) N K M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_addB (1 * (2 * k)) N K M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_joinB (N * K) (rowL N K k) (rowL N K k) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_getB (o5e hk c) (fencLen (eEnc (N := N) hk)) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_hashB (P1 N k * (2 * k)) (c.d) N K M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_mmB (1) (1) (1) N K M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_getB (o5vp c) (fR N K) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_addB (1) N K M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_joinB (fPsi N K k) (fD N K c.d) (fT N K k) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_joinB (fPsi N K k + fD N K c.d + fT N K k) (fJ (N := N) hk) (fR N K) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_flipB (offK hk c + (K - 1)) (fencLen (ctEnc hk c)) M (by omega)) le_rfl)

theorem sz_chal5TailBody (M : ℕ) (hM : sizechal5Tail hk c ≤ M) (hB : M < 2 ^ 240) :
    SZ (chal5TailBody hk c) (2 ^ 22) := by
  unfold sizechal5Tail at hM
  exact ((SZ.frame _ (sz_getB (o5va c) (fC N K k) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_mmB (1) (1) (2 * k) N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_addB (1 * (2 * k)) N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getB (o5vz c) (fC N K k) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_mmB (1) (1) (2 * k) N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_addB (1 * (2 * k)) N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_joinB (N * K) (rowL N K k) (rowL N K k) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getB (o5e hk c) (fencLen (eEnc (N := N) hk)) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_hashB (P1 N k * (2 * k)) (c.d) N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_mmB (1) (1) (1) N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getB (o5vp c) (fR N K) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_addB (1) N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_joinB (fPsi N K k) (fD N K c.d) (fT N K k) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_joinB (fPsi N K k + fD N K c.d + fT N K k) (fJ (N := N) hk) (fR N K) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_flipB (offK hk c + (K - 1)) (fencLen (ctEnc hk c)) M (by omega) hB))).mono (by norm_num)


set_option maxHeartbeats 8000000 in
/-- **The law of the tail of hybrid 5.** -/
theorem law_chal5Tail (hN : 0 < N) (hK : 1 ≤ K) (S : Store 82) (hS : Blank20 S)
    (i : Pub (Fin c.d) (Rg N K) k × Pub (Fin c.d) (Rg N K) k) (σ : Sec5 hk c) (μ : Bool)
    (h0 : S 0 = W5 hk c i σ) (h1 : S 1 = encMsg μ)
    (h3 : S 3 = (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc (c05 hk c i σ))
    (h6 : S 6 = (wEnc hk c).enc σ.2.2.1) (h7 : S 7 = (ringEnc N K).enc σ.2.1)
    (h8 : S 8 = (FixedEnc.fun (DualUse.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).enc
      (psi5 hk c i σ))
    (h10 : S 10 = (DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc i.1.2.1)
    (h11 : S 11 = (DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc i.1.2.2.1)
    (h18 : S 18 = (ringEnc N K).enc i.1.2.2.2) :
    ∃ S', (chal5TailBody hk c).law S = PMF.pure S' ∧
      S' 10 = (ctEnc hk c).enc (shiftCT hk c μ (view5 hk c i σ).2) := by
  have hct : (view5 hk c i σ).2 = ⟨psi5 hk c i σ, c05 hk c i σ,
      trapRowE σ.2.1 (RingBTVW.scalar σ.2.1 * i.1.2.1 + i.2.2.1) (RingBTVW.scalar σ.2.1 * i.1.2.2.1 + i.2.2.2.1),
      fun j => c05 hk c i σ * wMat σ.2.2.1 j + σ.2.2.2.2 j, σ.2.1 * i.1.2.2.2 + i.2.2.2.2⟩ := by
    simp only [view5, add_zero]
    rfl
  unfold chal5TailBody
  rw [law_seq, plc_getB' _ _ _ _ _ _ hS h0 (f5_va hk c i σ), PMF.pure_bind]
  rw [law_seq, plc_mmB' _ _ _ _ _ _ _ _ (by bl20) (by simp [h7]) (by simp [h10]) (len_ring _)
    (by rw [len_rowC]; ring) (mm_scalarC σ.2.1 i.1.2.1), PMF.pure_bind]
  rw [law_seq, plc_addB' _ _ _ _ _ _ (by bl20) (by simp) (by simp) (len_rowC _) (len_rowC _)
    (matAddW_matEnc' (len_fin 1) len_col (RingBTVW.scalar σ.2.1 * i.1.2.1) i.2.2.1), PMF.pure_bind]
  rw [law_seq, plc_getB' _ _ _ _ _ _ (by bl20) (by simp [h0]) (f5_vz hk c i σ), PMF.pure_bind]
  rw [law_seq, plc_mmB' _ _ _ _ _ _ _ _ (by bl20) (by simp [h7]) (by simp [h11]) (len_ring _)
    (by rw [len_rowC]; ring) (mm_scalarC σ.2.1 i.1.2.2.1), PMF.pure_bind]
  rw [law_seq, plc_addB' _ _ _ _ _ _ (by bl20) (by simp) (by simp) (len_rowC _) (len_rowC _)
    (matAddW_matEnc' (len_fin 1) len_col (RingBTVW.scalar σ.2.1 * i.1.2.2.1) i.2.2.2.1), PMF.pure_bind]
  rw [law_seq, plc_joinB' _ _ _ _ _ _ _ _ _ (by bl20) (by simp [h7]) (by simp) (by simp)
    (c15_word σ.2.1 (RingBTVW.scalar σ.2.1 * i.1.2.1 + i.2.2.1)
      (RingBTVW.scalar σ.2.1 * i.1.2.2.1 + i.2.2.2.1)), PMF.pure_bind]
  rw [law_seq, plc_getB' _ _ _ _ _ _ (by bl20) (by simp [h0]) (f5_e hk c i σ), PMF.pure_bind]
  rw [law_seq, plc_hashB' _ _ _ _ _ _ _ _ (by bl20) (by simp [h6]) (by simp [h3]) (by simp; rfl)
    (hash_rows c hk σ.2.2.1 (c05 hk c i σ) σ.2.2.2.2), PMF.pure_bind]
  rw [law_seq, plc_mmB' _ _ _ _ _ _ _ _ (by bl20) (by simp [h7]) (by simp [h18]) (len_ring _)
    (len_ring _) (ring_mul_word σ.2.1 i.1.2.2.2), PMF.pure_bind]
  rw [law_seq, plc_getB' _ _ _ _ _ _ (by bl20) (by simp [h0]) (f5_vp hk c i σ), PMF.pure_bind]
  rw [law_seq, plc_addB' _ _ _ _ _ _ (by bl20) (by simp) (by simp) (len_ring1 _) (len_ring1 _)
    (ring_add_word (σ.2.1 * i.1.2.2.2) i.2.2.2.2), PMF.pure_bind]
  rw [law_seq, plc_joinB' _ _ _ _ _ _ _ _ _ (by bl20) (by simp [h8]) (by simp [h3]) (by simp)
    (join3_exact (length_enc _ (psi5 hk c i σ)) (length_enc _ (c05 hk c i σ))
      (length_enc _ (trapRowE σ.2.1 (RingBTVW.scalar σ.2.1 * i.1.2.1 + i.2.2.1)
        (RingBTVW.scalar σ.2.1 * i.1.2.2.1 + i.2.2.2.1)))), PMF.pure_bind]
  rw [law_seq, plc_joinB' _ _ _ _ _ _ _ _ _ (by bl20) (by simp) (by simp) (by simp)
    (join3_exact (X := (FixedEnc.fun (DualUse.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).enc
        (psi5 hk c i σ) ++ (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc (c05 hk c i σ) ++
        (DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc
          (trapRowE σ.2.1 (RingBTVW.scalar σ.2.1 * i.1.2.1 + i.2.2.1)
            (RingBTVW.scalar σ.2.1 * i.1.2.2.1 + i.2.2.2.1)))
      (by simp only [List.length_append, length_enc] <;> rfl)
      (length_enc (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
        (DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)))
        (fun j => c05 hk c i σ * wMat σ.2.2.1 j + σ.2.2.2.2 j))
      (length_enc _ (σ.2.1 * i.1.2.2.2 + i.2.2.2.2))), PMF.pure_bind]
  rw [plc_flipB' _ _ _ _ _ _ _ (by bl20) (W := (ctEnc hk c).enc (view5 hk c i σ).2)
    (F := encMsg μ) (by rw [hct]; simp [ctEnc_enc] <;> rfl) (by simp [h1]) (length_enc _ _)
    (offK_lt hk c hN hK) (by rw [← ctEnc_shift hk c hN hK])]
  exact ⟨_, rfl, by simp only [Function.update_self]; rfl⟩

/-- **The challenge component of hybrid 5.** -/
def chal5P : XProg 82 := seq (seq (pub5Body hk c) (chal5TailBody hk c)) (finP 10)

theorem wf_chal5P : (chal5P hk c).WF := ⟨⟨wf_pub5Body hk c, wf_chal5TailBody hk c⟩, wf_finP _⟩

/-- **The law of the challenge component of hybrid 5.** -/
theorem law_chal5P (hN : 0 < N) (hK : 1 ≤ K) (i : Pub (Fin c.d) (Rg N K) k × Pub (Fin c.d) (Rg N K) k)
    (σ : Sec5 hk c) (μ : Bool) :
    (chal5P hk c).law (ioS (R := 80) (W5 hk c i σ) (encMsg μ) []) =
      PMF.pure (ioS (R := 80) ((ctEnc hk c).enc (shiftCT hk c μ (view5 hk c i σ).2)) [] []) := by
  obtain ⟨S, hS, hb, h0, h1, h3, -, -, h6, h7, h8, h10, h11, h18, -, -⟩ :=
    law_pub5Body hk c hN (by omega) (encMsg μ) i σ
  obtain ⟨S', hS', h10'⟩ := law_chal5Tail hk c hN hK S hb i σ μ h0 h1 h3 h6 h7 h8 h10 h11 h18
  rw [chal5P, law_seq, law_seq, hS, PMF.pure_bind, hS', PMF.pure_bind, law_finP 10 S' h10']

/-! ### Time and length -/

/-- The sizes of the templates of `chal5P`. -/
def sizeChal5 : ℕ := sizepub5 hk c + sizechal5Tail hk c

/-- The time of the body of `chal5P` from tapes below `M`. -/
def timeChal5 (M : ℕ) : ℕ := timepub5 hk c M + timechal5Tail hk c M

theorem ub_chal5Body (M : ℕ) (hM : sizeChal5 hk c ≤ M) :
    UBZ 20 (seq (pub5Body hk c) (chal5TailBody hk c)) M (timeChal5 hk c M) M :=
  (ub_pub5Body hk c M (by unfold sizeChal5 at hM; omega)).seq
    (ub_chal5TailBody hk c M (by unfold sizeChal5 at hM; omega))

theorem sz_chal5Body (M : ℕ) (hM : sizeChal5 hk c ≤ M) (hB : M < 2 ^ 240) :
    SZ (seq (pub5Body hk c) (chal5TailBody hk c)) (2 ^ 24) :=
  ((sz_pub5Body hk c M (by unfold sizeChal5 at hM; omega) hB).seq
    (sz_chal5TailBody hk c M (by unfold sizeChal5 at hM; omega) hB)).mono (by norm_num)

theorem time_chal5P (a b : ℕ) :
    timeBoundT (chal5P hk c) (io2 (R := 80) a b 0) ≤
      timeChal5 hk c (max a b + sizeChal5 hk c) + timeFin (max a b + sizeChal5 hk c) :=
  time_comp (ub_chal5Body hk c _ (by omega)) 10 _ (io2_le_zv (by omega))

theorem len_chal5P (a b : ℕ) :
    lenBoundT (chal5P hk c) (io2 (R := 80) a b 0) ≤ io2 (R := 80) (max a b + sizeChal5 hk c) 0 0 :=
  len_comp (ub_chal5Body hk c _ (by omega)) 10 _ (io2_le_zv (by omega))

end AdvancedEncryption.DualUse.Prog
