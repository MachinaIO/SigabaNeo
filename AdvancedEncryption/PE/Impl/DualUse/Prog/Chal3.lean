import PE.Impl.DualUse.Prog.Flip

/-!
# The challenge component of hybrid 3

`chal3P hk c` maps the packed secret of hybrid 3 (tape `0`) and the message `μ` (tape `1`) to
`(ctEnc hk c).enc (shiftCT hk c μ (view3 hk c ab σ).2)`: the public-key body (`pub3Body`, which
leaves `c₀`, `w`, `s`, the `Ψᵢ`, `B₁`, `p` on its tapes), then `chal3Tail`:
`c₁ = s B₁ + e₁`, the encodings `c_j = c₀ W_j + e_j` (`hashB`), `κ = s p + e'`, the join, and the
flip of the bit of `half` under `μ` (`flipB`, `ctEnc_shift`).

**`law_chal3P`**, `wf_chal3P`, `time_chal3P`, `len_chal3P`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.XProg Matrix AdvancedEncryption.RingBTVW
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord

variable {N K k : ℕ}

theorem mm_scalarT (s : Rg N K) (B : Matrix (Fin 1) (TrapCol k) (Rg N K)) :
    matMulW N K 1 1 (1 + (2 * k + 2 * k)) ((ringEnc N K).enc s)
        ((DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc B) =
      (DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc (RingBTVW.scalar s * B) := by
  rw [show (ringEnc N K).enc s = (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin 1)).enc
    (RingBTVW.scalar s) by rw [matEnc_one_one]; rfl, matEnc_mul' (len_fin 1) (len_fin 1) len_trap]

theorem len_rowT (B : Matrix (Fin 1) (TrapCol k) (Rg N K)) :
    ((DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc B).length =
      1 * (1 + (2 * k + 2 * k)) * N * K := by
  rw [length_matEnc, len_fin, len_trap]; ring

theorem len_ring1 (s : Rg N K) : ((ringEnc N K).enc s).length = 1 * N * K := by
  rw [(ringEnc N K).length]; ring

variable (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

theorem ctEnc_enc (ct : CT hk c) : (ctEnc hk c).enc ct =
    (FixedEnc.fun (DualUse.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).enc ct.Ψ ++
      ((DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc ct.c₀ ++
        ((DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc ct.c₁ ++
          ((FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
            (DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k))).enc ct.cj ++
            (ringEnc N K).enc ct.κ))) := rfl

theorem offK_lt (hN : 0 < N) (hK : 1 ≤ K) : offK hk c + (K - 1) < fencLen (ctEnc hk c) := by
  rw [offK]
  simp only [fencLen]
  have : K - 1 < N * K := by
    have := Nat.mul_le_mul_right K (show 1 ≤ N from hN); omega
  omega

/-- The tail of the challenge component of hybrid 3 after `pub3Body` (output on tape `10`). -/
def chal3TailBody : XProg 82 :=
  seq (frame ⟨vGet 10 0, by decide⟩ (getB (o3e1 hk c) (fT N K k))) <|
  seq (frame ⟨vMm 11 7 17, by decide⟩ (mmB (1) (1) (1 + (2 * k + 2 * k)) N K)) <|
  seq (frame ⟨vAdd 12 11 10, by decide⟩ (addB (1 * (1 + (2 * k + 2 * k))) N K)) <|
  seq (frame ⟨vGet 13 0, by decide⟩ (getB (o3e hk c) (fencLen (eEnc (N := N) hk)))) <|
  seq (frame ⟨vHash 16 6 3 13, by decide⟩ (hashB (P1 N k * (2 * k)) (c.d) N K)) <|
  seq (frame ⟨vMm 10 7 18, by decide⟩ (mmB (1) (1) (1) N K)) <|
  seq (frame ⟨vGet 11 0, by decide⟩ (getB (o3e' hk c) (fR N K))) <|
  seq (frame ⟨vAdd 14 10 11, by decide⟩ (addB (1) N K)) <|
  seq (frame ⟨vJoin 17 8 3 12, by decide⟩ (joinB (fPsi N K k) (fD N K c.d) (fT N K k))) <|
  seq (frame ⟨vJoin 18 17 16 14, by decide⟩ (joinB (fPsi N K k + fD N K c.d + fT N K k) (fJ (N := N) hk) (fR N K))) <|
  frame ⟨vFl 10 18 1, by decide⟩ (flipB (offK hk c + (K - 1)) (fencLen (ctEnc hk c)))

theorem wf_chal3TailBody : (chal3TailBody hk c).WF := by
  unfold chal3TailBody
  exact ⟨wf_getB _ _, wf_mmB _ _ _ _ _, wf_addB _ _ _, wf_getB _ _, wf_hashB _ _ _ _, wf_mmB _ _ _ _ _, wf_getB _ _, wf_addB _ _ _, wf_joinB _ _ _, wf_joinB _ _ _, wf_flipB _ _⟩

/-- The sizes of the templates of `chal3TailBody`. -/
def sizechal3Tail : ℕ :=
  ((o3e1 hk c) + (fT N K k)) +
    sizeMmB (1) (1) (1 + (2 * k + 2 * k)) N K +
    sizeAddB (1 * (1 + (2 * k + 2 * k))) N K +
    ((o3e hk c) + (fencLen (eEnc (N := N) hk))) +
    sizeHashB (P1 N k * (2 * k)) (c.d) N K +
    sizeMmB (1) (1) (1) N K +
    ((o3e' hk c) + (fR N K)) +
    sizeAddB (1) N K +
    ((fPsi N K k) + (fD N K c.d) + (fT N K k)) +
    ((fPsi N K k + fD N K c.d + fT N K k) + (fJ (N := N) hk) + (fR N K)) +
    ((offK hk c + (K - 1)) + (fencLen (ctEnc hk c)))

/-- The time of `chal3TailBody` from tapes below `M`. -/
def timechal3Tail (M : ℕ) : ℕ :=
  timeGetB (o3e1 hk c) (fT N K k) M + (timeMmB (1) (1) (1 + (2 * k + 2 * k)) N K M + (timeAddB (1 * (1 + (2 * k + 2 * k))) N K M + (timeGetB (o3e hk c) (fencLen (eEnc (N := N) hk)) M + (timeHashB (P1 N k * (2 * k)) (c.d) N K M + (timeMmB (1) (1) (1) N K M + (timeGetB (o3e' hk c) (fR N K) M + (timeAddB (1) N K M + (timeJoinB (fPsi N K k) (fD N K c.d) (fT N K k) M + (timeJoinB (fPsi N K k + fD N K c.d + fT N K k) (fJ (N := N) hk) (fR N K) M + (timeFlipB (offK hk c + (K - 1)) (fencLen (ctEnc hk c)) M))))))))))

theorem ub_chal3TailBody (M : ℕ) (hM : sizechal3Tail hk c ≤ M) :
    UBZ 20 (chal3TailBody hk c) M (timechal3Tail hk c M) M := by
  unfold sizechal3Tail at hM
  exact (UBZ.frame _ (by decide) (ub_getB (o3e1 hk c) (fT N K k) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_mmB (1) (1) (1 + (2 * k + 2 * k)) N K M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_addB (1 * (1 + (2 * k + 2 * k))) N K M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_getB (o3e hk c) (fencLen (eEnc (N := N) hk)) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_hashB (P1 N k * (2 * k)) (c.d) N K M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_mmB (1) (1) (1) N K M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_getB (o3e' hk c) (fR N K) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_addB (1) N K M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_joinB (fPsi N K k) (fD N K c.d) (fT N K k) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_joinB (fPsi N K k + fD N K c.d + fT N K k) (fJ (N := N) hk) (fR N K) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_flipB (offK hk c + (K - 1)) (fencLen (ctEnc hk c)) M (by omega)) le_rfl)

theorem sz_chal3TailBody (M : ℕ) (hM : sizechal3Tail hk c ≤ M) (hB : M < 2 ^ 240) :
    SZ (chal3TailBody hk c) (2 ^ 22) := by
  unfold sizechal3Tail at hM
  exact ((SZ.frame _ (sz_getB (o3e1 hk c) (fT N K k) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_mmB (1) (1) (1 + (2 * k + 2 * k)) N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_addB (1 * (1 + (2 * k + 2 * k))) N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getB (o3e hk c) (fencLen (eEnc (N := N) hk)) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_hashB (P1 N k * (2 * k)) (c.d) N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_mmB (1) (1) (1) N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getB (o3e' hk c) (fR N K) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_addB (1) N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_joinB (fPsi N K k) (fD N K c.d) (fT N K k) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_joinB (fPsi N K k + fD N K c.d + fT N K k) (fJ (N := N) hk) (fR N K) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_flipB (offK hk c + (K - 1)) (fencLen (ctEnc hk c)) M (by omega) hB))).mono (by norm_num)


/-- The ciphertext computed by the tail. -/
noncomputable def ctOf (Ψ : Fin 10 → Matrix (Fin 2) (RingBTVW.Col k) (Rg N K))
    (c₀ : Matrix (Fin 1) (Fin c.d) (Rg N K)) (B₁ e₁ : Matrix (Fin 1) (TrapCol k) (Rg N K)) (s p e' : Rg N K)
    (w : DualUse.JC (Sdw (N := N) hk) → (Fin c.d → Bool))
    (e : (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index → Matrix (Fin 1) (RingBTVW.Col k) (Rg N K)) :
    CT hk c :=
  ⟨Ψ, c₀, RingBTVW.scalar s * B₁ + e₁, fun j => c₀ * wMat w j + e j, s * p + e'⟩

set_option maxHeartbeats 8000000 in
/-- **The law of the tail.** -/
theorem law_chal3Tail (hN : 0 < N) (hK : 1 ≤ K) (S : Store 82) (hS : Blank20 S) (W : List Bool)
    (μ : Bool) (Ψ : Fin 10 → Matrix (Fin 2) (RingBTVW.Col k) (Rg N K))
    (c₀ : Matrix (Fin 1) (Fin c.d) (Rg N K)) (B₁ e₁ : Matrix (Fin 1) (TrapCol k) (Rg N K))
    (s p e' : Rg N K) (w : DualUse.JC (Sdw (N := N) hk) → (Fin c.d → Bool))
    (e : (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index → Matrix (Fin 1) (RingBTVW.Col k) (Rg N K))
    (h0 : S 0 = W) (h1 : S 1 = encMsg μ)
    (h3 : S 3 = (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc c₀)
    (h6 : S 6 = (wEnc hk c).enc w) (h7 : S 7 = (ringEnc N K).enc s)
    (h8 : S 8 = (FixedEnc.fun (DualUse.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).enc Ψ)
    (h17 : S 17 = (DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc B₁)
    (h18 : S 18 = (ringEnc N K).enc p)
    (he1 : takeD (fT N K k) (W.drop (o3e1 hk c)) =
      (DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc e₁)
    (he : takeD (fencLen (eEnc (N := N) hk)) (W.drop (o3e hk c)) = (eEnc (N := N) hk).enc e)
    (he' : takeD (fR N K) (W.drop (o3e' hk c)) = (ringEnc N K).enc e') :
    ∃ S', (chal3TailBody hk c).law S = PMF.pure S' ∧
      S' 10 = (ctEnc hk c).enc (shiftCT hk c μ (ctOf hk c Ψ c₀ B₁ e₁ s p e' w e)) := by
  unfold chal3TailBody
  rw [law_seq, plc_getB' _ _ _ _ _ _ hS h0 he1, PMF.pure_bind]
  rw [law_seq, plc_mmB' _ _ _ _ _ _ _ _ (by bl20) (by simp [h7]) (by simp [h17]) (len_ring s)
    (by rw [len_rowT]; ring) (mm_scalarT s B₁), PMF.pure_bind]
  rw [law_seq, plc_addB' _ _ _ _ _ _ (by bl20) (by simp) (by simp) (len_rowT _) (len_rowT _)
    (matAddW_matEnc' (len_fin 1) len_trap (RingBTVW.scalar s * B₁) e₁), PMF.pure_bind]
  rw [law_seq, plc_getB' _ _ _ _ _ _ (by bl20) (by simp [h0]) he, PMF.pure_bind]
  rw [law_seq, plc_hashB' _ _ _ _ _ _ _ _ (by bl20) (by simp [h6]) (by simp [h3]) (by simp; rfl)
    (hash_rows c hk w c₀ e), PMF.pure_bind]
  rw [law_seq, plc_mmB' _ _ _ _ _ _ _ _ (by bl20) (by simp [h7]) (by simp [h18]) (len_ring s)
    (len_ring p) (ring_mul_word s p), PMF.pure_bind]
  rw [law_seq, plc_getB' _ _ _ _ _ _ (by bl20) (by simp [h0]) he', PMF.pure_bind]
  rw [law_seq, plc_addB' _ _ _ _ _ _ (by bl20) (by simp) (by simp) (len_ring1 _) (len_ring1 _)
    (ring_add_word (s * p) e'), PMF.pure_bind]
  rw [law_seq, plc_joinB' _ _ _ _ _ _ _ _ _ (by bl20) (by simp [h8]) (by simp [h3]) (by simp)
    (join3_exact (length_enc _ Ψ) (length_enc _ c₀) (length_enc _ (RingBTVW.scalar s * B₁ + e₁))),
    PMF.pure_bind]
  rw [law_seq, plc_joinB' _ _ _ _ _ _ _ _ _ (by bl20) (by simp) (by simp) (by simp)
    (join3_exact (X := (FixedEnc.fun (DualUse.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).enc Ψ ++
        (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc c₀ ++
        (DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc (RingBTVW.scalar s * B₁ + e₁))
      (by simp only [List.length_append, length_enc] <;> rfl)
      (length_enc (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
        (DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k))) (fun j => c₀ * wMat w j + e j))
      (length_enc _ (s * p + e'))),
    PMF.pure_bind]
  rw [plc_flipB' _ _ _ _ _ _ _ (by bl20) (W := (ctEnc hk c).enc (ctOf hk c Ψ c₀ B₁ e₁ s p e' w e))
    (F := encMsg μ) (by simp [ctEnc_enc, ctOf] <;> rfl) (by simp [h1]) (length_enc _ _)
    (offK_lt hk c hN hK) (by rw [← ctEnc_shift hk c hN hK])]
  exact ⟨_, rfl, by simp only [Function.update_self]; rfl⟩

/-! ### The component -/

/-- **The challenge component of hybrid 3.** -/
def chal3P : XProg 82 := seq (seq (pub3Body hk c) (chal3TailBody hk c)) (finP 10)

theorem wf_chal3P : (chal3P hk c).WF := ⟨⟨wf_pub3Body hk c, wf_chal3TailBody hk c⟩, wf_finP _⟩

theorem ct3_eq (ab : Inst3T N K k) (σ : Sec3 hk c) :
    ctOf hk c (psi3 hk c σ) (c03 hk c σ) (toB₁ (Sdw (N := N) hk) ab) σ.2.2.2.2.1.2.2.1
      σ.2.2.2.2.1.1 σ.2.2.2.1 σ.2.2.2.2.1.2.2.2.2 σ.2.2.1 σ.2.2.2.2.2 = (view3 hk c ab σ).2 := by
  simp only [ctOf, view3, encrypt, Bool.false_eq_true, ite_false, add_zero]
  rfl

/-- **The law of the challenge component of hybrid 3.** -/
theorem law_chal3P (hN : 0 < N) (hK : 1 ≤ K) (ab : Inst3T N K k) (σ : Sec3 hk c) (μ : Bool) :
    (chal3P hk c).law (ioS (R := 80) (W3 hk c ab σ) (encMsg μ) []) =
      PMF.pure (ioS (R := 80) ((ctEnc hk c).enc (shiftCT hk c μ (view3 hk c ab σ).2)) [] []) := by
  obtain ⟨S, hS, hb, h1, h0, h3, -, -, h6, h8, -, h7, h17, h18, -⟩ := law_pub3Body hk c hN (by omega)
    (W3 hk c ab σ) (encMsg μ) ab σ.2.1 σ.2.2.2.2.1.2.1 σ.2.2.2.2.1.1 σ.2.2.2.1 σ.2.2.2.2.1.2.2.2.1
    σ.1 σ.2.2.1 (f3_a hk c ab σ) (f3_b hk c ab σ) (f3_x hk c ab σ) (f3_B hk c ab σ)
    (f3_w hk c ab σ) (f3_p hk c ab σ) (f3_s hk c ab σ) (f3_e0 hk c ab σ) (f3_R hk c ab σ)
  obtain ⟨S', hS', h10⟩ := law_chal3Tail hk c hN hK S hb (W3 hk c ab σ) μ (psi3 hk c σ) (c03 hk c σ)
    (toB₁ (Sdw (N := N) hk) ab) σ.2.2.2.2.1.2.2.1 σ.2.2.2.2.1.1 σ.2.2.2.1 σ.2.2.2.2.1.2.2.2.2 σ.2.2.1
    σ.2.2.2.2.2 h0 h1 h3 h6 h7 h8 h17 h18 (f3_e1 hk c ab σ) (f3_e hk c ab σ) (f3_e' hk c ab σ)
  rw [chal3P, law_seq, law_seq, hS, PMF.pure_bind, hS', PMF.pure_bind,
    law_finP 10 S' (v := (ctEnc hk c).enc (shiftCT hk c μ (view3 hk c ab σ).2))
      (h10.trans (by rw [ct3_eq]))]

/-! ### Time and length -/

/-- The sizes of the templates of `chal3P`. -/
def sizeChal3 : ℕ := sizepub3 hk c + sizechal3Tail hk c

/-- The time of the body of `chal3P` from tapes below `M`. -/
def timeChal3 (M : ℕ) : ℕ := timepub3 hk c M + timechal3Tail hk c M

theorem ub_chal3Body (M : ℕ) (hM : sizeChal3 hk c ≤ M) :
    UBZ 20 (seq (pub3Body hk c) (chal3TailBody hk c)) M (timeChal3 hk c M) M :=
  (ub_pub3Body hk c M (by unfold sizeChal3 at hM; omega)).seq
    (ub_chal3TailBody hk c M (by unfold sizeChal3 at hM; omega))

theorem sz_chal3Body (M : ℕ) (hM : sizeChal3 hk c ≤ M) (hB : M < 2 ^ 240) :
    SZ (seq (pub3Body hk c) (chal3TailBody hk c)) (2 ^ 24) :=
  ((sz_pub3Body hk c M (by unfold sizeChal3 at hM; omega) hB).seq
    (sz_chal3TailBody hk c M (by unfold sizeChal3 at hM; omega) hB)).mono (by norm_num)

/-- **The time of the challenge component of hybrid 3.** -/
theorem time_chal3P (a b : ℕ) :
    timeBoundT (chal3P hk c) (io2 (R := 80) a b 0) ≤
      timeChal3 hk c (max a b + sizeChal3 hk c) + timeFin (max a b + sizeChal3 hk c) :=
  time_comp (ub_chal3Body hk c _ (by omega)) 10 _ (io2_le_zv (by omega))

/-- **The length bound of the challenge component of hybrid 3.** -/
theorem len_chal3P (a b : ℕ) :
    lenBoundT (chal3P hk c) (io2 (R := 80) a b 0) ≤ io2 (R := 80) (max a b + sizeChal3 hk c) 0 0 :=
  len_comp (ub_chal3Body hk c _ (by omega)) 10 _ (io2_le_zv (by omega))

end AdvancedEncryption.DualUse.Prog
