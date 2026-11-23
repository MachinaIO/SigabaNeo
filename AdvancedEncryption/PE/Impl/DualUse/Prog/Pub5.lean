import PE.Impl.DualUse.Prog.Chal3

/-!
# The public-key and simulation-data components of hybrid 5

`pub5P hk c` maps the packed secret of hybrid 5 to `(pkEnc hk c).enc (view5 hk c i σ).1`:
`B₀` from the instance, `c₀ = u₀ B₀ + v₀`, the `Ψᵢ` and `B_j` (`psiCore`, `bjCore`), the trapdoor
row `[1 | a | z]` (`trapU_word`) and `p`. `sd5P` adds the tail `sdTail` of `PE.Impl.DualUse.Prog.Sd3`.

**`law_pub5P`**, **`law_sd5P`**, WF, time and length bounds.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.XProg Matrix AdvancedEncryption.RingBTVW
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The body of the public-key component of hybrid 5 (output on tape `15`). -/
def pub5Body : XProg 82 :=
  seq (frame ⟨vGet 2 0, by decide⟩ (getB (0) (fD N K c.d))) <|
  seq (frame ⟨vGet 7 0, by decide⟩ (getB (o5u c) (fR N K))) <|
  seq (frame ⟨vGet 14 0, by decide⟩ (getB (o5v c) (fD N K c.d))) <|
  seq (frame ⟨vMm 15 7 2, by decide⟩ (mmB (1) (1) (c.d) N K)) <|
  seq (frame ⟨vAdd 3 15 14, by decide⟩ (addB (1 * c.d) N K)) <|
  seq (frame ⟨vGet 4 0, by decide⟩ (getB (o5R hk c) (fencLen (rmTEnc c)))) <|
  seq (frame ⟨vGet 5 0, by decide⟩ (getB (o5x c) (fencLen attrEnc))) <|
  seq (frame ⟨vGet 6 0, by decide⟩ (getB (o5w c) (fencLen (wEnc hk c)))) <|
  seq (psiCore N K k c.d) <|
  seq (bjCore N K k c.d) <|
  seq (frame ⟨vGet 10 0, by decide⟩ (getB (o5a c) (fC N K k))) <|
  seq (frame ⟨vGet 11 0, by decide⟩ (getB (o5z c) (fC N K k))) <|
  seq (frame ⟨vOne 16, by decide⟩ (oneB N K)) <|
  seq (frame ⟨vJoin 17 16 10 11, by decide⟩ (joinB (N * K) (rowL N K k) (rowL N K k))) <|
  seq (frame ⟨vGet 18 0, by decide⟩ (getB (o5p c) (fR N K))) <|
  seq (frame ⟨vJoin 14 2 17 9, by decide⟩ (joinB (fD N K c.d) (fT N K k) (fJ (N := N) hk))) <|
  frame ⟨vJoin 15 14 18 19, by decide⟩ (joinB (fD N K c.d + fT N K k + fJ (N := N) hk) (fR N K) (0))

theorem wf_pub5Body : (pub5Body hk c).WF := by
  unfold pub5Body
  exact ⟨wf_getB _ _, wf_getB _ _, wf_getB _ _, wf_mmB _ _ _ _ _, wf_addB _ _ _, wf_getB _ _, wf_getB _ _, wf_getB _ _, wf_psiCore _ _ _ _, wf_bjCore _ _ _ _, wf_getB _ _, wf_getB _ _, wf_oneB _ _, wf_joinB _ _ _, wf_getB _ _, wf_joinB _ _ _, wf_joinB _ _ _⟩

/-- The sizes of the templates of `pub5Body`. -/
def sizepub5 : ℕ :=
  ((0) + (fD N K c.d)) +
    ((o5u c) + (fR N K)) +
    ((o5v c) + (fD N K c.d)) +
    sizeMmB (1) (1) (c.d) N K +
    sizeAddB (1 * c.d) N K +
    ((o5R hk c) + (fencLen (rmTEnc c))) +
    ((o5x c) + (fencLen attrEnc)) +
    ((o5w c) + (fencLen (wEnc hk c))) +
    sizePsiCore N K k c.d +
    sizeBjCore N K k c.d +
    ((o5a c) + (fC N K k)) +
    ((o5z c) + (fC N K k)) +
    (N * K + 1) +
    ((N * K) + (rowL N K k) + (rowL N K k)) +
    ((o5p c) + (fR N K)) +
    ((fD N K c.d) + (fT N K k) + (fJ (N := N) hk)) +
    ((fD N K c.d + fT N K k + fJ (N := N) hk) + (fR N K) + (0))

/-- The time of `pub5Body` from tapes below `M`. -/
def timepub5 (M : ℕ) : ℕ :=
  timeGetB (0) (fD N K c.d) M + (timeGetB (o5u c) (fR N K) M + (timeGetB (o5v c) (fD N K c.d) M + (timeMmB (1) (1) (c.d) N K M + (timeAddB (1 * c.d) N K M + (timeGetB (o5R hk c) (fencLen (rmTEnc c)) M + (timeGetB (o5x c) (fencLen attrEnc) M + (timeGetB (o5w c) (fencLen (wEnc hk c)) M + (timePsiCore N K k c.d M + (timeBjCore N K k c.d M + (timeGetB (o5a c) (fC N K k) M + (timeGetB (o5z c) (fC N K k) M + (timeOneB N K M + (timeJoinB (N * K) (rowL N K k) (rowL N K k) M + (timeGetB (o5p c) (fR N K) M + (timeJoinB (fD N K c.d) (fT N K k) (fJ (N := N) hk) M + (timeJoinB (fD N K c.d + fT N K k + fJ (N := N) hk) (fR N K) (0) M))))))))))))))))

theorem ub_pub5Body (M : ℕ) (hM : sizepub5 hk c ≤ M) :
    UBZ 20 (pub5Body hk c) M (timepub5 hk c M) M := by
  unfold sizepub5 at hM
  exact (UBZ.frame _ (by decide) (ub_getB (0) (fD N K c.d) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_getB (o5u c) (fR N K) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_getB (o5v c) (fD N K c.d) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_mmB (1) (1) (c.d) N K M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_addB (1 * c.d) N K M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_getB (o5R hk c) (fencLen (rmTEnc c)) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_getB (o5x c) (fencLen attrEnc) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_getB (o5w c) (fencLen (wEnc hk c)) M (by omega)) le_rfl).seq <|
    (ub_psiCore N K k c.d M (by omega)).seq <|
    (ub_bjCore N K k c.d M (by omega)).seq <|
    (UBZ.frame _ (by decide) (ub_getB (o5a c) (fC N K k) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_getB (o5z c) (fC N K k) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_oneB' N K M (by omega) (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_joinB (N * K) (rowL N K k) (rowL N K k) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_getB (o5p c) (fR N K) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_joinB (fD N K c.d) (fT N K k) (fJ (N := N) hk) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_joinB (fD N K c.d + fT N K k + fJ (N := N) hk) (fR N K) (0) M (by omega)) le_rfl)

theorem sz_pub5Body (M : ℕ) (hM : sizepub5 hk c ≤ M) (hB : M < 2 ^ 240) :
    SZ (pub5Body hk c) (2 ^ 23) := by
  unfold sizepub5 at hM
  exact ((SZ.frame _ (sz_getB (0) (fD N K c.d) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getB (o5u c) (fR N K) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getB (o5v c) (fD N K c.d) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_mmB (1) (1) (c.d) N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_addB (1 * c.d) N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getB (o5R hk c) (fencLen (rmTEnc c)) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getB (o5x c) (fencLen attrEnc) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getB (o5w c) (fencLen (wEnc hk c)) M (by omega) hB)).seq <|
    (sz_psiCore N K k c.d M (by omega) hB).seq <|
    (sz_bjCore N K k c.d M (by omega) hB).seq <|
    (SZ.frame _ (sz_getB (o5a c) (fC N K k) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getB (o5z c) (fC N K k) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_oneB' N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_joinB (N * K) (rowL N K k) (rowL N K k) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getB (o5p c) (fR N K) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_joinB (fD N K c.d) (fT N K k) (fJ (N := N) hk) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_joinB (fD N K c.d + fT N K k + fJ (N := N) hk) (fR N K) (0) M (by omega) hB))).mono (by norm_num)


/-- **The public-key component of hybrid 5.** -/
def pub5P : XProg 82 := seq (pub5Body hk c) (finP 15)

theorem wf_pub5P : (pub5P hk c).WF := ⟨wf_pub5Body hk c, wf_finP _⟩

/-- The row `c₀ = u₀ B₀ + v₀` of hybrid 5. -/
noncomputable def c05 (i : Pub (Fin c.d) (Rg N K) k × Pub (Fin c.d) (Rg N K) k) (σ : Sec5 hk c) :
    Matrix (Fin 1) (Fin c.d) (Rg N K) := RingBTVW.scalar σ.2.1 * i.1.1 + i.2.1

/-- The Ring-GSW ciphertexts of hybrid 5. -/
noncomputable def psi5 (i : Pub (Fin c.d) (Rg N K) k × Pub (Fin c.d) (Rg N K) k) (σ : Sec5 hk c) :
    Fin 10 → Matrix (Fin 2) (RingBTVW.Col k) (Rg N K) :=
  psiOf hk c i.1.1 (c05 hk c i σ) σ.2.2.2.1 σ.1

theorem pk5_word (i : Pub (Fin c.d) (Rg N K) k × Pub (Fin c.d) (Rg N K) k) (σ : Sec5 hk c) :
    (pkEnc hk c).enc (view5 hk c i σ).1 =
      (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc i.1.1 ++
        (DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc (trapRowU i.1.2.1 i.1.2.2.1) ++
        bjW hk c i.1.1 σ.2.2.1 (psi5 hk c i σ) ++ (ringEnc N K).enc i.1.2.2.2 := by
  rw [pkEnc_enc, bjW]
  simp only [List.append_assoc]
  rfl

set_option maxHeartbeats 8000000 in
/-- **The law of the body of hybrid 5** (tape `1` arbitrary), with the values left on the tapes. -/
theorem law_pub5Body (hN : 0 < N) (hK : 0 < K) (m : List Bool)
    (i : Pub (Fin c.d) (Rg N K) k × Pub (Fin c.d) (Rg N K) k) (σ : Sec5 hk c) :
    ∃ S, (pub5Body hk c).law (ioS (R := 80) (W5 hk c i σ) m []) = PMF.pure S ∧ Blank20 S ∧
      S 0 = W5 hk c i σ ∧ S 1 = m ∧
      S 3 = (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc (c05 hk c i σ) ∧
      S 4 = (rmTEnc c).enc σ.2.2.2.1 ∧ S 5 = encAttr σ.1 ∧ S 6 = (wEnc hk c).enc σ.2.2.1 ∧
      S 7 = (ringEnc N K).enc σ.2.1 ∧
      S 8 = (FixedEnc.fun (DualUse.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).enc
        (psi5 hk c i σ) ∧
      S 10 = (DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc i.1.2.1 ∧
      S 11 = (DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc i.1.2.2.1 ∧
      S 18 = (ringEnc N K).enc i.1.2.2.2 ∧ S 19 = [] ∧
      S 15 = (pkEnc hk c).enc (view5 hk c i σ).1 := by
  have hS0 := blank20_ioS (W5 hk c i σ) m
  have h0 : ioS (R := 80) (W5 hk c i σ) m [] 0 = W5 hk c i σ := rfl
  unfold pub5Body
  rw [law_seq, plc_getB' _ _ _ _ _ _ hS0 h0 (f5_B hk c i σ), PMF.pure_bind]
  rw [law_seq, plc_getB' _ _ _ _ _ _ (by bl20) (by simp [ioS]) (f5_u hk c i σ), PMF.pure_bind]
  rw [law_seq, plc_getB' _ _ _ _ _ _ (by bl20) (by simp [ioS]) (f5_v hk c i σ), PMF.pure_bind]
  rw [law_seq, plc_mmB' _ _ _ _ _ _ _ _ (by bl20) (by simp) (by simp) (len_ring σ.2.1)
    (by rw [len_row]; ring) (mm_scalar c.d σ.2.1 i.1.1), PMF.pure_bind]
  rw [law_seq, plc_addB' _ _ _ _ _ _ (by bl20) (by simp) (by simp) (len_row _ _) (len_row _ _)
    (matAddW_matEnc' (len_fin 1) (len_fin c.d) (RingBTVW.scalar σ.2.1 * i.1.1) i.2.1), PMF.pure_bind]
  rw [law_seq, plc_getB' _ _ _ _ _ _ (by bl20) (by simp [ioS]) (f5_R hk c i σ), PMF.pure_bind]
  rw [law_seq, plc_getB' _ _ _ _ _ _ (by bl20) (by simp [ioS]) (f5_x hk c i σ), PMF.pure_bind]
  rw [law_seq, plc_getB' _ _ _ _ _ _ (by bl20) (by simp [ioS]) (f5_w hk c i σ), PMF.pure_bind]
  rw [law_seq, law_psiCore hk c _ (by bl20) i.1.1 (c05 hk c i σ) σ.2.2.2.1 σ.1 (by simp)
    (by simp [c05]) (by simp) (by simp) (by simp [ioS]) (by simp [ioS]) (by simp [ioS])
    (by simp [ioS]) (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, law_bjCore hk c _ (by bl20) i.1.1 σ.2.2.1 (psi5 hk c i σ)
    (by simp) (by simp) (by simp [psi5]) (by simp [ioS]) (by simp [ioS]) (by simp [ioS])
    (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, plc_getB' _ _ _ _ _ _ (by bl20) (by simp [ioS]) (f5_a hk c i σ), PMF.pure_bind]
  rw [law_seq, plc_getB' _ _ _ _ _ _ (by bl20) (by simp [ioS]) (f5_z hk c i σ), PMF.pure_bind]
  rw [law_seq, plc_oneB _ _ hN hK _ (by bl20), PMF.pure_bind]
  rw [law_seq, plc_joinB' _ _ _ _ _ _ _ _ _ (by bl20) (by simp) (by simp) (by simp)
    (trapU_word i.1.2.1 i.1.2.2.1), PMF.pure_bind]
  rw [law_seq, plc_getB' _ _ _ _ _ _ (by bl20) (by simp [ioS]) (f5_p hk c i σ), PMF.pure_bind]
  rw [law_seq, plc_joinB' _ _ _ _ _ _ _ _ _ (by bl20) (by simp) (by simp) (by simp [bjW])
    (join3_exact (length_enc _ i.1.1) (length_enc _ (trapRowU i.1.2.1 i.1.2.2.1))
      (length_bjW hk c i.1.1 σ.2.2.1 (psi5 hk c i σ))), PMF.pure_bind]
  rw [plc_joinB' _ _ _ _ _ _ _ _ _ (by bl20) (by simp) (by simp) (by simp [ioS])
    (join2_exact (X := (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc i.1.1 ++
      (DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc (trapRowU i.1.2.1 i.1.2.2.1) ++
      bjW hk c i.1.1 σ.2.2.1 (psi5 hk c i σ))
      (by simp only [List.length_append, length_enc, length_bjW, fD, fT] <;> omega)
      (length_enc _ i.1.2.2.2))]
  exact ⟨_, rfl, by bl20, by simp [ioS], by simp [ioS], by simp [c05], by simp, by simp, by simp,
    by simp, by simp [psi5], by simp, by simp, by simp, by simp [ioS], by simp [pk5_word]⟩

/-- **The law of the public-key component of hybrid 5.** -/
theorem law_pub5P (hN : 0 < N) (hK : 0 < K) (i : Pub (Fin c.d) (Rg N K) k × Pub (Fin c.d) (Rg N K) k)
    (σ : Sec5 hk c) :
    (pub5P hk c).law (ioS (R := 80) (W5 hk c i σ) [] []) =
      PMF.pure (ioS (R := 80) ((pkEnc hk c).enc (view5 hk c i σ).1) [] []) := by
  obtain ⟨S, hS, -, -, -, -, -, -, -, -, -, -, -, -, -, h15⟩ := law_pub5Body hk c hN hK [] i σ
  rw [pub5P, law_seq, hS, PMF.pure_bind, law_finP 15 S h15]

/-- **The simulation-data component of hybrid 5.** -/
def sd5P : XProg 82 := seq (seq (pub5Body hk c) (sdTailBody hk c)) (finP 13)

theorem wf_sd5P : (sd5P hk c).WF := ⟨⟨wf_pub5Body hk c, wf_sdTailBody hk c⟩, wf_finP _⟩

/-- **The law of the simulation-data component of hybrid 5.** -/
theorem law_sd5P (hN : 0 < N) (hK : 0 < K) (i : Pub (Fin c.d) (Rg N K) k × Pub (Fin c.d) (Rg N K) k)
    (σ : Sec5 hk c) :
    (sd5P hk c).law (ioS (R := 80) (W5 hk c i σ) [] []) =
      PMF.pure (ioS (R := 80) ((sdEnc hk c).enc (sd5 hk c i σ)) [] []) := by
  obtain ⟨S, hS, hb, -, -, h3, h4, h5, h6, -, h8, -, -, -, h19, h15⟩ := law_pub5Body hk c hN hK [] i σ
  obtain ⟨S', hS', h13⟩ := law_sdTail hk c hN hK S hb _ _ _ _ _ (view5 hk c i σ).1 h3 h4 h5 h6 h8 h15 h19
  rw [sd5P, law_seq, law_seq, hS, PMF.pure_bind, hS', PMF.pure_bind,
    law_finP 13 S' (v := (sdEnc hk c).enc (sd5 hk c i σ)) (h13.trans rfl)]

/-! ### Time and length -/

theorem time_pub5P (a b : ℕ) :
    timeBoundT (pub5P hk c) (io2 (R := 80) a b 0) ≤
      timepub5 hk c (max a b + sizepub5 hk c) + timeFin (max a b + sizepub5 hk c) :=
  time_comp (ub_pub5Body hk c _ (by omega)) 15 _ (io2_le_zv (by omega))

theorem len_pub5P (a b : ℕ) :
    lenBoundT (pub5P hk c) (io2 (R := 80) a b 0) ≤ io2 (R := 80) (max a b + sizepub5 hk c) 0 0 :=
  len_comp (ub_pub5Body hk c _ (by omega)) 15 _ (io2_le_zv (by omega))

/-- The sizes of the templates of `sd5P`. -/
def sizeSd5 : ℕ := sizepub5 hk c + sizesdTail hk c

/-- The time of the body of `sd5P` from tapes below `M`. -/
def timeSd5 (M : ℕ) : ℕ := timepub5 hk c M + timesdTail hk c M

theorem ub_sd5Body (M : ℕ) (hM : sizeSd5 hk c ≤ M) :
    UBZ 20 (seq (pub5Body hk c) (sdTailBody hk c)) M (timeSd5 hk c M) M :=
  (ub_pub5Body hk c M (by unfold sizeSd5 at hM; omega)).seq
    (ub_sdTailBody hk c M (by unfold sizeSd5 at hM; omega))

theorem sz_sd5Body (M : ℕ) (hM : sizeSd5 hk c ≤ M) (hB : M < 2 ^ 240) :
    SZ (seq (pub5Body hk c) (sdTailBody hk c)) (2 ^ 24) :=
  ((sz_pub5Body hk c M (by unfold sizeSd5 at hM; omega) hB).seq
    (sz_sdTailBody hk c M (by unfold sizeSd5 at hM; omega) hB)).mono (by norm_num)

theorem time_sd5P (a b : ℕ) :
    timeBoundT (sd5P hk c) (io2 (R := 80) a b 0) ≤
      timeSd5 hk c (max a b + sizeSd5 hk c) + timeFin (max a b + sizeSd5 hk c) :=
  time_comp (ub_sd5Body hk c _ (by omega)) 13 _ (io2_le_zv (by omega))

theorem len_sd5P (a b : ℕ) :
    lenBoundT (sd5P hk c) (io2 (R := 80) a b 0) ≤ io2 (R := 80) (max a b + sizeSd5 hk c) 0 0 :=
  len_comp (ub_sd5Body hk c _ (by omega)) 13 _ (io2_le_zv (by omega))

end AdvancedEncryption.DualUse.Prog
