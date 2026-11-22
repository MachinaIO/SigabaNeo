import PE.Impl.DualUse.Prog.Finish

/-!
# The public-key component of hybrid 3

`pub3P hk c : XProg 82` maps the packed secret `W3 = (inst3Enc ⊗ sec3Enc).enc (ab, σ)` (tape `0`,
tape `1` blank) to `(pkEnc hk c).enc (view3 hk c ab σ).1` alone on tape `0`:

1. the fields `B₀`, `s`, `e₀` and `c₀ = s B₀ + e₀` (`mmB`, `addB`); the `Rᵢ`, the date `x`, the
   columns `w`;
2. the `Ψᵢ` (`psiCore`) and the `B_j` (`bjCore`);
3. `B₁ = toB₁ (a, b) = [1 | a | G̲ − b]` (`gadB`, `subB`, `oneB`, `joinB`);
4. the join `B₀, B₁, (B_j), p`, then `finP`.

**`law_pub3P`**, `wf_pub3P`, `time_pub3P`, `len_pub3P`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.XProg Matrix AdvancedEncryption.RingBTVW
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow

variable {N K k : ℕ}

/-! ### Words -/

theorem mm_scalar (d : ℕ) (s : Rg N K) (B : Matrix (Fin 1) (Fin d) (Rg N K)) :
    matMulW N K 1 1 d ((ringEnc N K).enc s) ((DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin d)).enc B) =
      (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin d)).enc (RingBTVW.scalar s * B) := by
  rw [show (ringEnc N K).enc s = (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin 1)).enc
    (RingBTVW.scalar s) by rw [matEnc_one_one]; rfl, matEnc_mul' (len_fin 1) (len_fin 1) (len_fin d)]

theorem len_row (d : ℕ) (B : Matrix (Fin 1) (Fin d) (Rg N K)) :
    ((DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin d)).enc B).length = 1 * d * N * K := by
  rw [length_matEnc, len_fin, len_fin]; ring

theorem len_rowC (B : Matrix (Fin 1) (RingBTVW.Col k) (Rg N K)) :
    ((DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc B).length = 1 * (2 * k) * N * K := by
  rw [length_matEnc, len_fin, len_col]; ring

theorem len_ring (s : Rg N K) : ((ringEnc N K).enc s).length = 1 * 1 * (N * K) := by
  rw [(ringEnc N K).length]; ring

theorem length_gadW (hk : 2 ^ K < 2 ^ k) : (gadW N K k).length = 1 * (2 * k) * N * K := by
  rw [gadW_split hk, List.length_append, length_gHalf, List.length_replicate]; ring

theorem join3_exact {X Y Z : List Bool} {a b c : ℕ} (ha : X.length = a) (hb : Y.length = b)
    (hc : Z.length = c) : takeD a X ++ takeD b Y ++ takeD c Z = X ++ Y ++ Z := by
  rw [takeD_of_length' ha, takeD_of_length' hb, takeD_of_length' hc]

theorem join2_exact {X Y : List Bool} {a b : ℕ} (ha : X.length = a) (hb : Y.length = b) :
    takeD a X ++ takeD b Y ++ takeD 0 [] = X ++ Y := by
  rw [takeD_of_length' ha, takeD_of_length' hb]; exact List.append_nil _

variable (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The word of the `B_j` of `(B₀, w, Ψ)`. -/
noncomputable def bjW (B₀ : Matrix (Fin 1) (Fin c.d) (Rg N K)) (w : DualUse.JC (Sdw (N := N) hk) → (Fin c.d → Bool))
    (Ψ : Fin 10 → Matrix (Fin 2) (RingBTVW.Col k) (Rg N K)) : List Bool :=
  (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
      (DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k))).enc
    fun j => B₀ * wMat w j + RingBTVW.bitsOf (Sdw (N := N) hk) Ψ j • (Sdw (N := N) hk).Γ₁.G

/-- The length of the word of the `B_j`. -/
abbrev fJ (hk : 2 ^ K < 2 ^ k) : ℕ :=
  fencLen (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
    (DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)))

/-- The length of `B₁`. -/
abbrev fT (N K k : ℕ) : ℕ := fencLen (DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k))

/-! ### The program -/

/-- The body of the public-key component of hybrid 3 (output on tape `15`). -/
def pub3Body : XProg 82 :=
  seq (frame ⟨vGet 2 0, by decide⟩ (getB (o3B (N := N) (K := K) (k := k)) (fD N K c.d))) <|
  seq (frame ⟨vGet 7 0, by decide⟩ (getB (o3s hk c) (fR N K))) <|
  seq (frame ⟨vGet 14 0, by decide⟩ (getB (o3e0 hk c) (fD N K c.d))) <|
  seq (frame ⟨vMm 15 7 2, by decide⟩ (mmB (1) (1) (c.d) N K)) <|
  seq (frame ⟨vAdd 3 15 14, by decide⟩ (addB (1 * c.d) N K)) <|
  seq (frame ⟨vGet 4 0, by decide⟩ (getB (o3R hk c) (fencLen (rmTEnc c)))) <|
  seq (frame ⟨vGet 5 0, by decide⟩ (getB (o3x (N := N) (K := K) (k := k)) (fencLen dateEnc))) <|
  seq (frame ⟨vGet 6 0, by decide⟩ (getB (o3w c) (fencLen (wEnc hk c)))) <|
  seq (psiCore N K k c.d) <|
  seq (bjCore N K k c.d) <|
  seq (frame ⟨vGet 10 0, by decide⟩ (getB (0) (fC N K k))) <|
  seq (frame ⟨vGet 11 0, by decide⟩ (getB (fC N K k + 0) (fC N K k))) <|
  seq (frame ⟨vGad 12, by decide⟩ (gadB N K k)) <|
  seq (frame ⟨vAdd 13 12 11, by decide⟩ (subB (1 * (2 * k)) N K)) <|
  seq (frame ⟨vOne 16, by decide⟩ (oneB N K)) <|
  seq (frame ⟨vJoin 17 16 10 13, by decide⟩ (joinB (N * K) (rowL N K k) (rowL N K k))) <|
  seq (frame ⟨vGet 18 0, by decide⟩ (getB (o3p hk c) (fR N K))) <|
  seq (frame ⟨vJoin 14 2 17 9, by decide⟩ (joinB (fD N K c.d) (fT N K k) (fJ (N := N) hk))) <|
  frame ⟨vJoin 15 14 18 19, by decide⟩ (joinB (fD N K c.d + fT N K k + fJ (N := N) hk) (fR N K) (0))

theorem wf_pub3Body : (pub3Body hk c).WF := by
  unfold pub3Body
  exact ⟨wf_getB _ _, wf_getB _ _, wf_getB _ _, wf_mmB _ _ _ _ _, wf_addB _ _ _, wf_getB _ _, wf_getB _ _, wf_getB _ _, wf_psiCore _ _ _ _, wf_bjCore _ _ _ _, wf_getB _ _, wf_getB _ _, wf_gadB _ _ _, wf_subB _ _ _, wf_oneB _ _, wf_joinB _ _ _, wf_getB _ _, wf_joinB _ _ _, wf_joinB _ _ _⟩

/-- The sizes of the templates of `pub3Body`. -/
def sizepub3 : ℕ :=
  ((o3B (N := N) (K := K) (k := k)) + (fD N K c.d)) +
    ((o3s hk c) + (fR N K)) +
    ((o3e0 hk c) + (fD N K c.d)) +
    sizeMmB (1) (1) (c.d) N K +
    sizeAddB (1 * c.d) N K +
    ((o3R hk c) + (fencLen (rmTEnc c))) +
    ((o3x (N := N) (K := K) (k := k)) + (fencLen dateEnc)) +
    ((o3w c) + (fencLen (wEnc hk c))) +
    sizePsiCore N K k c.d +
    sizeBjCore N K k c.d +
    ((0) + (fC N K k)) +
    ((fC N K k + 0) + (fC N K k)) +
    sizeGadB N K k +
    sizeAddB (1 * (2 * k)) N K +
    (N * K + 1) +
    ((N * K) + (rowL N K k) + (rowL N K k)) +
    ((o3p hk c) + (fR N K)) +
    ((fD N K c.d) + (fT N K k) + (fJ (N := N) hk)) +
    ((fD N K c.d + fT N K k + fJ (N := N) hk) + (fR N K) + (0))

/-- The time of `pub3Body` from tapes below `M`. -/
def timepub3 (M : ℕ) : ℕ :=
  timeGetB (o3B (N := N) (K := K) (k := k)) (fD N K c.d) M + (timeGetB (o3s hk c) (fR N K) M + (timeGetB (o3e0 hk c) (fD N K c.d) M + (timeMmB (1) (1) (c.d) N K M + (timeAddB (1 * c.d) N K M + (timeGetB (o3R hk c) (fencLen (rmTEnc c)) M + (timeGetB (o3x (N := N) (K := K) (k := k)) (fencLen dateEnc) M + (timeGetB (o3w c) (fencLen (wEnc hk c)) M + (timePsiCore N K k c.d M + (timeBjCore N K k c.d M + (timeGetB (0) (fC N K k) M + (timeGetB (fC N K k + 0) (fC N K k) M + (timeGadB N K k M + (timeSubB (1 * (2 * k)) N K M + (timeOneB N K M + (timeJoinB (N * K) (rowL N K k) (rowL N K k) M + (timeGetB (o3p hk c) (fR N K) M + (timeJoinB (fD N K c.d) (fT N K k) (fJ (N := N) hk) M + (timeJoinB (fD N K c.d + fT N K k + fJ (N := N) hk) (fR N K) (0) M))))))))))))))))))

theorem ub_pub3Body (M : ℕ) (hM : sizepub3 hk c ≤ M) :
    UB (pub3Body hk c) M (timepub3 hk c M) M := by
  unfold sizepub3 at hM
  exact (ub_frameX _ (ub_getB (o3B (N := N) (K := K) (k := k)) (fD N K c.d) M (by omega)) le_rfl).seq <|
    (ub_frameX _ (ub_getB (o3s hk c) (fR N K) M (by omega)) le_rfl).seq <|
    (ub_frameX _ (ub_getB (o3e0 hk c) (fD N K c.d) M (by omega)) le_rfl).seq <|
    (ub_frameX _ (ub_mmB (1) (1) (c.d) N K M (by omega)) le_rfl).seq <|
    (ub_frameX _ (ub_addB (1 * c.d) N K M (by omega)) le_rfl).seq <|
    (ub_frameX _ (ub_getB (o3R hk c) (fencLen (rmTEnc c)) M (by omega)) le_rfl).seq <|
    (ub_frameX _ (ub_getB (o3x (N := N) (K := K) (k := k)) (fencLen dateEnc) M (by omega)) le_rfl).seq <|
    (ub_frameX _ (ub_getB (o3w c) (fencLen (wEnc hk c)) M (by omega)) le_rfl).seq <|
    (ub_psiCore N K k c.d M (by omega)).seq <|
    (ub_bjCore N K k c.d M (by omega)).seq <|
    (ub_frameX _ (ub_getB (0) (fC N K k) M (by omega)) le_rfl).seq <|
    (ub_frameX _ (ub_getB (fC N K k + 0) (fC N K k) M (by omega)) le_rfl).seq <|
    (ub_frameX _ (ub_gadB N K k M (by omega)) le_rfl).seq <|
    (ub_frameX _ (ub_subB (1 * (2 * k)) N K M (by omega)) le_rfl).seq <|
    (ub_frameX _ (ub_oneB' N K M (by omega) (by omega)) le_rfl).seq <|
    (ub_frameX _ (ub_joinB (N * K) (rowL N K k) (rowL N K k) M (by omega)) le_rfl).seq <|
    (ub_frameX _ (ub_getB (o3p hk c) (fR N K) M (by omega)) le_rfl).seq <|
    (ub_frameX _ (ub_joinB (fD N K c.d) (fT N K k) (fJ (N := N) hk) M (by omega)) le_rfl).seq <|
    (ub_frameX _ (ub_joinB (fD N K c.d + fT N K k + fJ (N := N) hk) (fR N K) (0) M (by omega)) le_rfl)


/-- **The public-key component of hybrid 3.** -/
def pub3P : XProg 82 := seq (pub3Body hk c) (finP 15)

theorem wf_pub3P : (pub3P hk c).WF := ⟨wf_pub3Body hk c, wf_finP _⟩

/-! ### The law -/

/-- The row `c₀ = s B₀ + e₀` of hybrid 3. -/
noncomputable def c03 (σ : Sec3 hk c) : Matrix (Fin 1) (Fin c.d) (Rg N K) :=
  RingBTVW.scalar σ.2.2.2.2.1.1 * σ.2.1 + σ.2.2.2.2.1.2.1

/-- The Ring-GSW ciphertexts of hybrid 3. -/
noncomputable def psi3 (σ : Sec3 hk c) : Fin 10 → Matrix (Fin 2) (RingBTVW.Col k) (Rg N K) :=
  psiOf hk c σ.2.1 (c03 hk c σ) σ.2.2.2.2.1.2.2.2.1 σ.1

theorem length_bjW (B₀ : Matrix (Fin 1) (Fin c.d) (Rg N K)) (w : DualUse.JC (Sdw (N := N) hk) → (Fin c.d → Bool))
    (Ψ : Fin 10 → Matrix (Fin 2) (RingBTVW.Col k) (Rg N K)) : (bjW hk c B₀ w Ψ).length = fJ (N := N) hk :=
  length_enc _ _

theorem pkEnc_enc (m : PK hk c) : (pkEnc hk c).enc m =
    (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc m.B₀ ++
      ((DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc m.B₁ ++
        ((FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
          (DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k))).enc m.Bj ++
          (ringEnc N K).enc m.p)) := rfl

theorem pk3_word (ab : Inst3T N K k) (σ : Sec3 hk c) :
    (pkEnc hk c).enc (view3 hk c ab σ).1 =
      (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc σ.2.1 ++
        (DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc (toB₁ (Sdw (N := N) hk) ab) ++
        bjW hk c σ.2.1 σ.2.2.1 (psi3 hk c σ) ++
        (ringEnc N K).enc σ.2.2.2.1 := by
  have hBj : (view3 hk c ab σ).1.Bj = fun j => σ.2.1 * wMat σ.2.2.1 j +
      RingBTVW.bitsOf (Sdw (N := N) hk) (psi3 hk c σ) j •
        (Sdw (N := N) hk).Γ₁.G := funext fun j => by
    show bjOf σ.2.1 (bitsOf σ.1) _ (hashCols σ.2.1 σ.2.2.1) j = _
    unfold bjOf
    rw [of_hashCols]
    rfl
  rw [pkEnc_enc, hBj, bjW]
  simp only [List.append_assoc]
  rfl

set_option maxHeartbeats 8000000 in
/-- **The law of the public-key component of hybrid 3.** -/
theorem law_pub3P (hN : 0 < N) (hK : 0 < K) (ab : Inst3T N K k) (σ : Sec3 hk c) :
    (pub3P hk c).law (ioS (R := 80) (W3 hk c ab σ) [] []) =
      PMF.pure (ioS (R := 80) ((pkEnc hk c).enc (view3 hk c ab σ).1) [] []) := by
  have hS0 : Blank20 (ioS (R := 80) (W3 hk c ab σ) [] []) := fun t ht => by
    simp only [ioS]; split_ifs <;> first | rfl | omega
  have h0 : ioS (R := 80) (W3 hk c ab σ) [] [] 0 = W3 hk c ab σ := rfl
  unfold pub3P pub3Body
  rw [law_seq, law_seq, plc_getB' _ _ _ _ _ _ hS0 h0 (f3_B hk c ab σ), PMF.pure_bind]
  rw [law_seq, plc_getB' _ _ _ _ _ _ (by bl20) (by simp [ioS]) (f3_s hk c ab σ), PMF.pure_bind]
  rw [law_seq, plc_getB' _ _ _ _ _ _ (by bl20) (by simp [ioS]) (f3_e0 hk c ab σ), PMF.pure_bind]
  rw [law_seq, plc_mmB' _ _ _ _ _ _ _ _ (by bl20) (by simp) (by simp) (len_ring σ.2.2.2.2.1.1) (by rw [len_row]; ring)
    (mm_scalar c.d σ.2.2.2.2.1.1 σ.2.1), PMF.pure_bind]
  rw [law_seq, plc_addB' _ _ _ _ _ _ (by bl20) (by simp) (by simp) (len_row _ _) (len_row _ _)
    (matAddW_matEnc' (len_fin 1) (len_fin c.d) (RingBTVW.scalar σ.2.2.2.2.1.1 * σ.2.1)
      σ.2.2.2.2.1.2.1), PMF.pure_bind]
  rw [law_seq, plc_getB' _ _ _ _ _ _ (by bl20) (by simp [ioS]) (f3_R hk c ab σ), PMF.pure_bind]
  rw [law_seq, plc_getB' _ _ _ _ _ _ (by bl20) (by simp [ioS]) (f3_x hk c ab σ), PMF.pure_bind]
  rw [law_seq, plc_getB' _ _ _ _ _ _ (by bl20) (by simp [ioS]) (f3_w hk c ab σ), PMF.pure_bind]
  rw [law_seq, law_psiCore hk c _ (by bl20) σ.2.1 (c03 hk c σ) σ.2.2.2.2.1.2.2.2.1 σ.1 (by simp) (by simp [c03]) (by simp) (by simp)
    (by simp [ioS]) (by simp [ioS]) (by simp [ioS]) (by simp [ioS]) (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, law_bjCore hk c _ (by bl20) σ.2.1 σ.2.2.1 (psi3 hk c σ) (by simp) (by simp) (by simp [psi3])
    (by simp [ioS]) (by simp [ioS]) (by simp [ioS]) (by simp [ioS]), PMF.pure_bind]
  rw [law_seq, plc_getB' _ _ _ _ _ _ (by bl20) (by simp [ioS]) (f3_a hk c ab σ), PMF.pure_bind]
  rw [law_seq, plc_getB' _ _ _ _ _ _ (by bl20) (by simp [ioS]) (f3_b hk c ab σ), PMF.pure_bind]
  rw [law_seq, plc_gadB _ _ _ (by bl20), PMF.pure_bind]
  rw [law_seq, plc_subB' _ _ _ _ _ _ (by bl20) (by simp) (by simp) (length_gadW hk) (len_rowC ab.2) rfl,
    PMF.pure_bind]
  rw [law_seq, plc_oneB _ _ hN hK _ (by bl20), PMF.pure_bind]
  rw [law_seq, plc_joinB' _ _ _ _ _ _ _ _ _ (by bl20) (by simp) (by simp) (by simp) (b1_word hk ab),
    PMF.pure_bind]
  rw [law_seq, plc_getB' _ _ _ _ _ _ (by bl20) (by simp [ioS]) (f3_p hk c ab σ), PMF.pure_bind]
  rw [law_seq, plc_joinB' _ _ _ _ _ _ _ _ _ (by bl20) (by simp) (by simp) (by simp [bjW, psi3])
    (join3_exact (length_enc _ σ.2.1) (length_enc _ (toB₁ (Sdw (N := N) hk) ab))
      (length_bjW hk c σ.2.1 σ.2.2.1 (psi3 hk c σ))), PMF.pure_bind]
  rw [plc_joinB' _ _ _ _ _ _ _ _ _ (by bl20) (by simp) (by simp) (by simp [ioS])
    (join2_exact (X := (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc σ.2.1 ++
      (DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc (toB₁ (Sdw (N := N) hk) ab) ++
      bjW hk c σ.2.1 σ.2.2.1 (psi3 hk c σ))
      (by simp only [List.length_append, length_enc, length_bjW, fD, fT] <;> omega)
      (length_enc _ σ.2.2.2.1)), PMF.pure_bind]
  rw [law_finP 15 _ (v := (pkEnc hk c).enc (view3 hk c ab σ).1) (by simp [pk3_word])]

/-! ### Time and length -/

/-- **The time of the public-key component of hybrid 3** on inputs of at most `a`, `b` bits. -/
theorem time_pub3P (a b : ℕ) :
    timeBoundT (pub3P hk c) (io2 (R := 80) a b 0) ≤
      timepub3 hk c (max a b + sizepub3 hk c) + timeFin (max a b + sizepub3 hk c) :=
  time_comp (ub_pub3Body hk c _ (by omega)) 15 _ fun i => (io2_le a b i).trans (by omega)

/-- **The length bound of the public-key component of hybrid 3**: the output below
`max a b + sizepub3`, every other tape blank. -/
theorem len_pub3P (a b : ℕ) :
    lenBoundT (pub3P hk c) (io2 (R := 80) a b 0) ≤ io2 (R := 80) (max a b + sizepub3 hk c) 0 0 :=
  len_comp (ub_pub3Body hk c _ (by omega)) 15 _ fun i => (io2_le a b i).trans (by omega)

end AdvancedEncryption.DualUse.Prog
