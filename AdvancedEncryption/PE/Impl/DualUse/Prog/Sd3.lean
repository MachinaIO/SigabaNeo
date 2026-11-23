import PE.Impl.DualUse.Prog.Pub3

/-!
# The simulation-data components of hybrid 3 and of the ideal side

`sd3P hk c` (and `sdIP hk c`, the same program) maps the packed secret to `(sdEnc hk c).enc (sd3 …)`
(resp. `sdI`): the public-key body of hybrid 3 (`pub3Body`), then `sdTail`: the `Rᵢ` row-major
(`trB`), the `W_j` (`trB`, `oneB`, `selB`) and the join `mpk, c₀, (Rᵢ), (W_j), (Ψᵢ), x`.

**`law_sd3P`**, **`law_sdIP`**, `wf_sd3P`, `time_sd3P`, `len_sd3P`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.XProg Matrix AdvancedEncryption.RingBTVW
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord

variable {N K k : ℕ}

/-- The number of the encodings' positions `Attr × Index`. -/
abbrev P1 (N k : ℕ) : ℕ := nA * (2 * (2 * k * (k * N)))

/-- The length of the word of the `Ψᵢ`. -/
abbrev fPsi (N K k : ℕ) : ℕ :=
  fencLen (FixedEnc.fun (α := Fin nA) (DualUse.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k)))

variable (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The length of the word of the `W_j`. -/
abbrev fWm : ℕ :=
  fencLen (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
    (DualUse.matEnc (N := N) (K := K) (Fin c.d) (RingBTVW.Col k)))

/-- The tail of the simulation-data components after a public-key body (output on tape `13`). -/
def sdTailBody : XProg 82 :=
  seq (frame ⟨vTr 16 4, by decide⟩ (trB (nA) (2 * k) (c.d) (N * K) (0))) <|
  seq (frame ⟨vTr 17 6, by decide⟩ (trB (P1 N k) (2 * k) (c.d) (1) (0))) <|
  seq (frame ⟨vOne 18, by decide⟩ (oneB N K)) <|
  seq (frame ⟨vSel 10 17 18 19, by decide⟩ (selB (P1 N k * (c.d * (2 * k))) (N * K))) <|
  seq (frame ⟨vJoin 11 16 10 8, by decide⟩ (joinB (fencLen (rmEnc c)) (fWm (N := N) hk c) (fPsi N K k))) <|
  seq (frame ⟨vJoin 12 3 11 5, by decide⟩ (joinB (fD N K c.d) (fencLen (rmEnc c) + fWm (N := N) hk c + fPsi N K k) (fencLen attrEnc))) <|
  frame ⟨vJoin 13 15 12 19, by decide⟩ (joinB (fencLen (pkEnc hk c)) (fD N K c.d + (fencLen (rmEnc c) + fWm (N := N) hk c + fPsi N K k) + fencLen attrEnc) (0))

theorem wf_sdTailBody : (sdTailBody hk c).WF := by
  unfold sdTailBody
  exact ⟨wf_trB _ _ _ _ _, wf_trB _ _ _ _ _, wf_oneB _ _, wf_selB _ _, wf_joinB _ _ _, wf_joinB _ _ _, wf_joinB _ _ _⟩

/-- The sizes of the templates of `sdTailBody`. -/
def sizesdTail : ℕ :=
  sizeTrB (nA) (2 * k) (c.d) (N * K) (0) +
    sizeTrB (P1 N k) (2 * k) (c.d) (1) (0) +
    (N * K + 1) +
    sizeSelB (P1 N k * (c.d * (2 * k))) (N * K) +
    ((fencLen (rmEnc c)) + (fWm (N := N) hk c) + (fPsi N K k)) +
    ((fD N K c.d) + (fencLen (rmEnc c) + fWm (N := N) hk c + fPsi N K k) + (fencLen attrEnc)) +
    ((fencLen (pkEnc hk c)) + (fD N K c.d + (fencLen (rmEnc c) + fWm (N := N) hk c + fPsi N K k) + fencLen attrEnc) + (0))

/-- The time of `sdTailBody` from tapes below `M`. -/
def timesdTail (M : ℕ) : ℕ :=
  timeTrB (nA) (2 * k) (c.d) (N * K) (0) M + (timeTrB (P1 N k) (2 * k) (c.d) (1) (0) M + (timeOneB N K M + (timeSelB (P1 N k * (c.d * (2 * k))) (N * K) M + (timeJoinB (fencLen (rmEnc c)) (fWm (N := N) hk c) (fPsi N K k) M + (timeJoinB (fD N K c.d) (fencLen (rmEnc c) + fWm (N := N) hk c + fPsi N K k) (fencLen attrEnc) M + (timeJoinB (fencLen (pkEnc hk c)) (fD N K c.d + (fencLen (rmEnc c) + fWm (N := N) hk c + fPsi N K k) + fencLen attrEnc) (0) M))))))

theorem ub_sdTailBody (M : ℕ) (hM : sizesdTail hk c ≤ M) :
    UBZ 20 (sdTailBody hk c) M (timesdTail hk c M) M := by
  unfold sizesdTail at hM
  exact (UBZ.frame _ (by decide) (ub_trB (nA) (2 * k) (c.d) (N * K) (0) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_trB (P1 N k) (2 * k) (c.d) (1) (0) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_oneB' N K M (by omega) (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_selB (P1 N k * (c.d * (2 * k))) (N * K) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_joinB (fencLen (rmEnc c)) (fWm (N := N) hk c) (fPsi N K k) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_joinB (fD N K c.d) (fencLen (rmEnc c) + fWm (N := N) hk c + fPsi N K k) (fencLen attrEnc) M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_joinB (fencLen (pkEnc hk c)) (fD N K c.d + (fencLen (rmEnc c) + fWm (N := N) hk c + fPsi N K k) + fencLen attrEnc) (0) M (by omega)) le_rfl)

theorem sz_sdTailBody (M : ℕ) (hM : sizesdTail hk c ≤ M) (hB : M < 2 ^ 240) :
    SZ (sdTailBody hk c) (2 ^ 21) := by
  unfold sizesdTail at hM
  exact ((SZ.frame _ (sz_trB (nA) (2 * k) (c.d) (N * K) (0) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_trB (P1 N k) (2 * k) (c.d) (1) (0) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_oneB' N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_selB (P1 N k * (c.d * (2 * k))) (N * K) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_joinB (fencLen (rmEnc c)) (fWm (N := N) hk c) (fPsi N K k) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_joinB (fD N K c.d) (fencLen (rmEnc c) + fWm (N := N) hk c + fPsi N K k) (fencLen attrEnc) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_joinB (fencLen (pkEnc hk c)) (fD N K c.d + (fencLen (rmEnc c) + fWm (N := N) hk c + fPsi N K k) + fencLen attrEnc) (0) M (by omega) hB))).mono (by norm_num)


set_option maxHeartbeats 4000000 in
/-- **The law of the tail.** -/
theorem law_sdTail (hN : 0 < N) (hK : 0 < K) (S : Store 82) (hS : Blank20 S)
    (c₀ : Matrix (Fin 1) (Fin c.d) (Rg N K)) (Rm : Fin nA → Matrix (Fin c.d) (RingBTVW.Col k) (Rg N K))
    (x : PUniv.Attr) (w : DualUse.JC (Sdw (N := N) hk) → (Fin c.d → Bool))
    (Ψ : Fin nA → Matrix (Fin 2) (RingBTVW.Col k) (Rg N K)) (pk : PK hk c)
    (h3 : S 3 = (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc c₀)
    (h4 : S 4 = (rmTEnc c).enc Rm) (h5 : S 5 = encAttr x) (h6 : S 6 = (wEnc hk c).enc w)
    (h8 : S 8 = (FixedEnc.fun (DualUse.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).enc Ψ)
    (h15 : S 15 = (pkEnc hk c).enc pk) (h19 : S 19 = []) :
    ∃ S', (sdTailBody hk c).law S = PMF.pure S' ∧ S' 13 = (sdEnc hk c).enc ⟨pk, c₀, Rm, wMat w, Ψ, x⟩ := by
  unfold sdTailBody
  rw [law_seq, plc_trB' _ _ _ _ _ _ _ _ S hS h4 (trW_rm c Rm), PMF.pure_bind]
  rw [law_seq, plc_trB' _ _ _ _ _ _ _ _ _ (by bl20) (by simp [h6])
    (rfl : trW (P1 N k) (2 * k) c.d 1 0 ((wEnc hk c).enc w) = _), PMF.pure_bind]
  rw [law_seq, plc_oneB _ _ hN hK _ (by bl20), PMF.pure_bind]
  rw [law_seq, plc_selB' _ _ _ _ _ _ _ _ (by bl20) (by simp) (by simp) (by simp [h19])
    (wMat_word c hk w), PMF.pure_bind]
  rw [law_seq, plc_joinB' _ _ _ _ _ _ _ _ _ (by bl20) (by simp) (by simp) (by simp [h8])
    (join3_exact (length_enc _ Rm) (length_enc _ (wMat w)) (length_enc _ Ψ)), PMF.pure_bind]
  rw [law_seq, plc_joinB' _ _ _ _ _ _ _ _ _ (by bl20) (by simp [h3]) (by simp) (by simp [h5])
    (join3_exact (Y := ((rmEnc c).enc Rm ++ (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
        (DualUse.matEnc (N := N) (K := K) (Fin c.d) (RingBTVW.Col k))).enc (wMat w) ++
        (FixedEnc.fun (DualUse.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).enc Ψ))
      (Z := encAttr x) (c := fencLen attrEnc) (length_enc _ c₀)
      (by simp only [List.length_append, length_enc]) (length_enc attrEnc x)),
    PMF.pure_bind]
  rw [plc_joinB' _ _ _ _ _ _ _ _ _ (by bl20) (by simp [h15]) (by simp) (by simp [h19])
    (join2_exact (Y := (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc c₀ ++ ((rmEnc c).enc Rm ++ (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
        (DualUse.matEnc (N := N) (K := K) (Fin c.d) (RingBTVW.Col k))).enc (wMat w) ++
        (FixedEnc.fun (DualUse.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).enc Ψ) ++ encAttr x)
      (length_enc _ pk)
      (by simp only [List.length_append, length_enc]; rfl))]
  refine ⟨_, rfl, ?_⟩
  simp only [Function.update_self, sdEnc_enc, List.append_assoc]
  rfl

/-! ### The components -/

/-- **The simulation-data component of hybrid 3.** -/
def sd3P : XProg 82 := seq (seq (pub3Body hk c) (sdTailBody hk c)) (finP 13)

/-- **The simulation-data component of the ideal side** (the same program). -/
def sdIP : XProg 82 := sd3P hk c

theorem wf_sd3P : (sd3P hk c).WF := ⟨⟨wf_pub3Body hk c, wf_sdTailBody hk c⟩, wf_finP _⟩

theorem wf_sdIP : (sdIP hk c).WF := wf_sd3P hk c

/-- **The law of the simulation-data component of hybrid 3.** -/
theorem law_sd3P (hN : 0 < N) (hK : 0 < K) (ab : Inst3T N K k) (σ : Sec3 hk c) :
    (sd3P hk c).law (ioS (R := 80) (W3 hk c ab σ) [] []) =
      PMF.pure (ioS (R := 80) ((sdEnc hk c).enc (sd3 hk c ab σ)) [] []) := by
  obtain ⟨S, hS, hb, -, -, h3, h4, h5, h6, h8, h19, -, -, -, h15⟩ := law_pub3Body hk c hN hK (W3 hk c ab σ) [] ab
    σ.2.1 σ.2.2.2.2.1.2.1 σ.2.2.2.2.1.1 σ.2.2.2.1 σ.2.2.2.2.1.2.2.2.1 σ.1 σ.2.2.1
    (f3_a hk c ab σ) (f3_b hk c ab σ) (f3_x hk c ab σ) (f3_B hk c ab σ) (f3_w hk c ab σ)
    (f3_p hk c ab σ) (f3_s hk c ab σ) (f3_e0 hk c ab σ) (f3_R hk c ab σ)
  obtain ⟨S', hS', h13⟩ := law_sdTail hk c hN hK S hb _ _ _ _ _ (view3 hk c ab σ).1 h3 h4 h5 h6 h8
    (h15.trans (pk3_word hk c ab σ).symm) h19
  rw [sd3P, law_seq, law_seq, hS, PMF.pure_bind, hS', PMF.pure_bind,
    law_finP 13 S' (v := (sdEnc hk c).enc (sd3 hk c ab σ)) (h13.trans rfl)]

/-- **The law of the simulation-data component of the ideal side.** -/
theorem law_sdIP (hN : 0 < N) (hK : 0 < K) (ab : Inst3T N K k) (σ : SecI hk c) :
    (sdIP hk c).law (ioS (R := 80) (WI hk c ab σ) [] []) =
      PMF.pure (ioS (R := 80) ((sdEnc hk c).enc (sdI hk c ab σ)) [] []) := by
  obtain ⟨S, hS, hb, -, -, h3, h4, h5, h6, h8, h19, -, -, -, h15⟩ := law_pub3Body hk c hN hK (WI hk c ab σ) [] ab
    σ.2.1 σ.2.2.2.2.1.e₀ σ.2.2.2.2.1.s σ.2.2.2.1 σ.2.2.2.2.1.Rm σ.1 σ.2.2.1
    (fI_a hk c ab σ) (fI_b hk c ab σ) (fI_x hk c ab σ) (fI_B hk c ab σ) (fI_w hk c ab σ)
    (fI_p hk c ab σ) (fI_s hk c ab σ) (fI_e0 hk c ab σ) (fI_R hk c ab σ)
  obtain ⟨S', hS', h13⟩ := law_sdTail hk c hN hK S hb _ _ _ _ _ (viewI hk c ab σ).1 h3 h4 h5 h6 h8
    (h15.trans (pkI_word hk c ab σ).symm) h19
  rw [sdIP, sd3P, law_seq, law_seq, hS, PMF.pure_bind, hS', PMF.pure_bind,
    law_finP 13 S' (v := (sdEnc hk c).enc (sdI hk c ab σ)) (h13.trans rfl)]

/-! ### Time and length -/

/-- The sizes of the templates of `sd3P`. -/
def sizeSd3 : ℕ := sizepub3 hk c + sizesdTail hk c

/-- The time of the body of `sd3P` from tapes below `M`. -/
def timeSd3 (M : ℕ) : ℕ := timepub3 hk c M + timesdTail hk c M

theorem ub_sd3Body (M : ℕ) (hM : sizeSd3 hk c ≤ M) :
    UBZ 20 (seq (pub3Body hk c) (sdTailBody hk c)) M (timeSd3 hk c M) M :=
  (ub_pub3Body hk c M (by unfold sizeSd3 at hM; omega)).seq
    (ub_sdTailBody hk c M (by unfold sizeSd3 at hM; omega))

theorem sz_sd3Body (M : ℕ) (hM : sizeSd3 hk c ≤ M) (hB : M < 2 ^ 240) :
    SZ (seq (pub3Body hk c) (sdTailBody hk c)) (2 ^ 24) :=
  ((sz_pub3Body hk c M (by unfold sizeSd3 at hM; omega) hB).seq
    (sz_sdTailBody hk c M (by unfold sizeSd3 at hM; omega) hB)).mono (by norm_num)

/-- **The time of the simulation-data component** (hybrid 3 and the ideal side). -/
theorem time_sd3P (a b : ℕ) :
    timeBoundT (sd3P hk c) (io2 (R := 80) a b 0) ≤
      timeSd3 hk c (max a b + sizeSd3 hk c) + timeFin (max a b + sizeSd3 hk c) :=
  time_comp (ub_sd3Body hk c _ (by omega)) 13 _ (io2_le_zv (by omega))

/-- **The length bound of the simulation-data component.** -/
theorem len_sd3P (a b : ℕ) :
    lenBoundT (sd3P hk c) (io2 (R := 80) a b 0) ≤ io2 (R := 80) (max a b + sizeSd3 hk c) 0 0 :=
  len_comp (ub_sd3Body hk c _ (by omega)) 13 _ (io2_le_zv (by omega))

end AdvancedEncryption.DualUse.Prog
