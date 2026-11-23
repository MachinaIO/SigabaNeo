import PE.Impl.DualUse.Prog.Place

/-!
# The common cores of the reductions' components

Values on the tapes `2 … 19` of an `XProg 82` (tape `19` stays blank), scratch from `20`:

* **`psiCore`**: from `B₀` (tape `2`), `c₀` (tape `3`), the `Rᵢ` column-major (tape `4`) and the
  date `x` (tape `5`), the word of the Ring-GSW ciphertexts `Ψᵢ = [B₀; c₀] Rᵢ + xᵢ G` on tape `8`
  (temporaries `10 … 13`, blank before and after): `law_psiCore`;
* **`bjCore`**: from `B₀` (tape `2`), the binary columns `w` (tape `6`) and the word of the `Ψᵢ`
  (tape `8`), the word of the public keys of the encodings `B_j = B₀ W_j + ψ_j G̲` on tape `9`
  (temporaries `10 … 12`): `law_bjCore`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.XProg Matrix AdvancedEncryption.RingBTVW
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow

/-- Discharge `Blank20` of an updated store. -/
macro "bl20" : tactic => `(tactic| ((repeat (refine Blank20.upd ?_ (by decide) _)); assumption))

/-- Clear a tape. -/
abbrev clr82 (t : Fin 82) : XProg 82 := prog (.prim (.clear t))

theorem law_clr82 (t : Fin 82) (s : Store 82) : (clr82 t).law s = PMF.pure (Function.update s t []) :=
  law_prim _ s

variable {N K k : ℕ}

/-! ### The Ring-GSW ciphertexts -/

/-- **The Ring-GSW ciphertexts** `Ψᵢ = [B₀; c₀] Rᵢ + xᵢ G` (tape `8`). -/
def psiCore (N K k d : ℕ) : XProg 82 :=
  seq (frame ⟨vJoin 10 2 3 19, by decide⟩ (joinB (d * (N * K)) (d * (N * K)) 0)) <|
  seq (frame ⟨vTr 11 10, by decide⟩ (trB 1 2 d (N * K) 0)) <|
  seq (frame ⟨vMm 12 4 11, by decide⟩ (mmB (nA * (2 * k)) d 2 N K)) <|
  seq (frame ⟨vTr 13 12, by decide⟩ (trB nA (2 * k) 2 (N * K) 0)) <|
  seq (frame ⟨vGad 10, by decide⟩ (gadB N K k)) <|
  seq (prog (.prim (.copy 12 10))) <|
  seq (frame ⟨vJoin 11 10 19 12, by decide⟩ (joinB (2 * k * (N * K)) (k * (N * K)) (k * (N * K)))) <|
  seq (frame ⟨vSel 12 5 11 19, by decide⟩ (selB nA (2 * (2 * k) * (N * K)))) <|
  seq (frame ⟨vAdd 8 13 12, by decide⟩ (addB (nA * (2 * (2 * k))) N K)) <|
  seq (clr82 10) <| seq (clr82 11) <| seq (clr82 12) <| clr82 13

theorem wf_psiCore (N K k d : ℕ) : (psiCore N K k d).WF :=
  ⟨wf_joinB _ _ _, wf_trB _ _ _ _ _, wf_mmB _ _ _ _ _, wf_trB _ _ _ _ _, wf_gadB _ _ _,
    trivial, wf_joinB _ _ _, wf_selB _ _, wf_addB _ _ _, trivial, trivial, trivial, trivial⟩

variable (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The Ring-GSW ciphertexts of `(B₀, c₀, R, x)`. -/
noncomputable def psiOf (B₀ c₀ : Matrix (Fin 1) (Fin c.d) (Rg N K)) (Rm : Fin nA → Matrix (Fin c.d) (RingBTVW.Col k) (Rg N K))
    (x : Date) : Fin nA → Matrix (Fin 2) (RingBTVW.Col k) (Rg N K) :=
  fun i => gswPK B₀ c₀ * Rm i + bitR (R := Rg N K) (bitsOf x i) • (Sdw (N := N) hk).Γ.G

set_option maxHeartbeats 4000000 in
/-- **The law of `psiCore`.** -/
theorem law_psiCore (s : Store 82) (hS : Blank20 s) (B₀ c₀ : Matrix (Fin 1) (Fin c.d) (Rg N K))
    (Rm : Fin nA → Matrix (Fin c.d) (RingBTVW.Col k) (Rg N K)) (x : Date)
    (h2 : s 2 = (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc B₀)
    (h3 : s 3 = (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc c₀)
    (h4 : s 4 = (rmTEnc c).enc Rm) (h5 : s 5 = encDate x)
    (h10 : s 10 = []) (h11 : s 11 = []) (h12 : s 12 = []) (h13 : s 13 = []) (h19 : s 19 = []) :
    (psiCore N K k c.d).law s = PMF.pure (Function.update s 8
      ((FixedEnc.fun (DualUse.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).enc
        (psiOf hk c B₀ c₀ Rm x))) := by
  have hlA : ((DualUse.matEnc (N := N) (K := K) (Fin c.d) (Fin 2)).enc (gswPK B₀ c₀)ᵀ).length =
      c.d * 2 * (N * K) := by rw [length_matEnc, len_fin, len_fin]; ring
  have hlR : ((rmTEnc c).enc Rm).length = nA * (2 * k) * c.d * (N * K) := by
    rw [rmTEnc_stk, length_matEnc, Enum.length_prod, len_fin, len_col, len_fin]; ring
  have hMM : matMulW N K (nA * (2 * k)) c.d 2 ((rmTEnc c).enc Rm)
      ((DualUse.matEnc (N := N) (K := K) (Fin c.d) (Fin 2)).enc (gswPK B₀ c₀)ᵀ) =
      (DualUse.matEnc (N := N) (K := K) (Fin nA × RingBTVW.Col k) (Fin 2)).enc
        (stkR c Rm * (gswPK B₀ c₀)ᵀ) := by
    rw [← trW_matEnc' (len_fin 2) (len_fin c.d)]; exact psiMM c (gswPK B₀ c₀) Rm
  have hlF : ∀ F : Fin nA → Matrix (Fin 2) (RingBTVW.Col k) (Rg N K),
      ((FixedEnc.fun (DualUse.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).enc F).length =
        nA * (2 * (2 * k)) * N * K := fun F => by
    rw [(FixedEnc.fun (DualUse.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).length, len_fin,
      len_fin, len_col]; ring
  unfold psiCore
  rw [law_seq, plc_joinB' _ _ _ _ _ _ _ _ s hS h2 h3 h19 (psiA c B₀ c₀), PMF.pure_bind]
  rw [law_seq, plc_trB' _ _ _ _ _ _ _ _ _ (by bl20) (by simp)
    (trW_matEnc' (len_fin 2) (len_fin c.d) (gswPK B₀ c₀)), PMF.pure_bind]
  rw [law_seq, plc_mmB' _ _ _ _ _ _ _ _ (by bl20) (by simp [h4])
    (by simp) hlR hlA hMM, PMF.pure_bind]
  rw [law_seq, plc_trB' _ _ _ _ _ _ _ _ _ (by bl20) (by simp) (psiPre c (gswPK B₀ c₀) Rm), PMF.pure_bind]
  rw [law_seq, plc_gadB _ _ _ (by bl20), PMF.pure_bind]
  rw [law_seq, law_prim, PMF.pure_bind]
  simp only [Prim.apply, Function.update_self]
  rw [law_seq, plc_joinB' _ _ _ _ _ _ _ _ _ (by bl20) (by simp)
    (by simp [h19]) (by simp) (gswG_word hk), PMF.pure_bind]
  rw [law_seq, plc_selB' _ _ _ _ _ _ _ _ (by bl20) (by simp [h5])
    (by simp) (by simp [h19]) (psiSel hk x), PMF.pure_bind]
  rw [law_seq, plc_addB' _ _ _ _ _ _ (by bl20) (by simp) (by simp)
    (hlF _) (hlF _)
    (psiAdd (fun i => gswPK B₀ c₀ * Rm i) (fun i => bitR (R := Rg N K) (bitsOf x i) • (Sdw (N := N) hk).Γ.G)),
    PMF.pure_bind]
  rw [law_seq, law_clr82, PMF.pure_bind, law_seq, law_clr82, PMF.pure_bind, law_seq, law_clr82,
    PMF.pure_bind, law_clr82]
  congr 1
  funext t
  simp only [Function.update_apply]
  split_ifs <;> subst_vars <;> first | rfl | assumption | simp_all [psiOf]

/-! ### The public keys of the encodings -/

/-- **The public keys of the encodings** `B_j = B₀ W_j + ψ_j G̲` (tape `9`). -/
def bjCore (N K k d : ℕ) : XProg 82 :=
  seq (frame ⟨vTr 10 8, by decide⟩ (trB (nA * (2 * (2 * k))) N K 1 ((k - K) * N))) <|
  seq (frame ⟨vGad 11, by decide⟩ (gadB N K k)) <|
  seq (frame ⟨vSel 12 10 11 19, by decide⟩ (selB (nA * (2 * (2 * k * (k * N)))) (2 * k * (N * K)))) <|
  seq (frame ⟨vHash 9 6 2 12, by decide⟩ (hashB (nA * (2 * (2 * k * (k * N))) * (2 * k)) d N K)) <|
  seq (clr82 10) <| seq (clr82 11) <| clr82 12

theorem wf_bjCore (N K k d : ℕ) : (bjCore N K k d).WF :=
  ⟨wf_trB _ _ _ _ _, wf_gadB _ _ _, wf_selB _ _, wf_hashB _ _ _ _, trivial, trivial, trivial⟩

set_option maxHeartbeats 4000000 in
/-- **The law of `bjCore`.** -/
theorem law_bjCore (s : Store 82) (hS : Blank20 s) (B₀ : Matrix (Fin 1) (Fin c.d) (Rg N K))
    (w : DualUse.JC (Sdw (N := N) hk) → (Fin c.d → Bool))
    (Ψ : Fin nA → Matrix (Fin 2) (RingBTVW.Col k) (Rg N K))
    (h2 : s 2 = (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc B₀)
    (h6 : s 6 = (wEnc hk c).enc w)
    (h8 : s 8 = (FixedEnc.fun (DualUse.matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).enc Ψ)
    (h10 : s 10 = []) (h11 : s 11 = []) (h12 : s 12 = []) (h19 : s 19 = []) :
    (bjCore N K k c.d).law s = PMF.pure (Function.update s 9
      ((FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
          (DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k))).enc
        fun j => B₀ * wMat w j + RingBTVW.bitsOf (Sdw (N := N) hk) Ψ j • (Sdw (N := N) hk).Γ₁.G)) := by
  unfold bjCore
  rw [law_seq, plc_trB' _ _ _ _ _ _ _ _ s hS h8 (psiBits hk Ψ), PMF.pure_bind]
  rw [law_seq, plc_gadB _ _ _ (by bl20), PMF.pure_bind]
  rw [law_seq, plc_selB' _ _ _ _ _ _ _ _ (by bl20) (by simp) (by simp) (by simp [h19])
    (psiRows hk Ψ), PMF.pure_bind]
  rw [law_seq, plc_hashB' _ _ _ _ _ _ _ _ (by bl20) (by simp [h6]) (by simp [h2]) (by simp)
    (hash_rows c hk w B₀ (fun j => RingBTVW.bitsOf (Sdw (N := N) hk) Ψ j • (Sdw (N := N) hk).Γ₁.G)),
    PMF.pure_bind]
  rw [law_seq, law_clr82, PMF.pure_bind, law_seq, law_clr82, PMF.pure_bind, law_clr82]
  congr 1
  funext t
  simp only [Function.update_apply]
  split_ifs <;> subst_vars <;> first | rfl | assumption | simp_all

/-! ### Time -/

/-- A primitive on the component's tapes, keeping the scratch tapes `≥ 20` blank. -/
theorem ubz_prim82 (p : Prim 82) (M : ℕ) (h : ∀ ℓ : Fin 82 → ℕ, ℓ ≤ zv 20 M → p.lenT ℓ ≤ zv 20 M) :
    UBZ 20 (prog (.prim p)) M (2 * (M + 1) + 3) M := fun ℓ hℓ =>
  ⟨((VB.prim p (a := zv 20 M) (zv_le 20 M)) ℓ hℓ).1, h ℓ hℓ⟩

theorem ubz_copy (i j : Fin 82) (hi : i.val < 20) (M : ℕ) :
    UBZ 20 (prog (.prim (.copy i j))) M (2 * (M + 1) + 3) M :=
  ubz_prim82 _ M fun ℓ hℓ t => by
    simp only [Prim.lenT, Function.update_apply]
    split_ifs with h
    · subst h; refine (hℓ j).trans ((zv_le 20 M j).trans ?_); simp [zv, hi]
    · exact hℓ t

theorem ubz_clear (j : Fin 82) (M : ℕ) : UBZ 20 (clr82 j) M (2 * (M + 1) + 3) M :=
  ubz_prim82 _ M fun ℓ hℓ t => by
    simp only [Prim.lenT, Function.update_apply]
    split_ifs
    · exact Nat.zero_le _
    · exact hℓ t

/-- The sizes of the templates of `psiCore`. -/
def sizePsiCore (N K k d : ℕ) : ℕ :=
  (d * (N * K) + d * (N * K) + 0) + sizeTrB 1 2 d (N * K) 0 + sizeMmB (nA * (2 * k)) d 2 N K +
    sizeTrB nA (2 * k) 2 (N * K) 0 + sizeGadB N K k + (2 * k * (N * K) + k * (N * K) + k * (N * K)) +
    sizeSelB nA (2 * (2 * k) * (N * K)) + sizeAddB (nA * (2 * (2 * k))) N K

/-- **The time of `psiCore`** from tapes below `M`. -/
def timePsiCore (N K k d M : ℕ) : ℕ :=
  timeJoinB (d * (N * K)) (d * (N * K)) 0 M + (timeTrB 1 2 d (N * K) 0 M +
    (timeMmB (nA * (2 * k)) d 2 N K M + (timeTrB nA (2 * k) 2 (N * K) 0 M + (timeGadB N K k M +
    ((2 * (M + 1) + 3) + (timeJoinB (2 * k * (N * K)) (k * (N * K)) (k * (N * K)) M +
    (timeSelB nA (2 * (2 * k) * (N * K)) M + (timeAddB (nA * (2 * (2 * k))) N K M +
    ((2 * (M + 1) + 3) + ((2 * (M + 1) + 3) + ((2 * (M + 1) + 3) + (2 * (M + 1) + 3))))))))))))

theorem ub_psiCore (N K k d M : ℕ) (hM : sizePsiCore N K k d ≤ M) :
    UBZ 20 (psiCore N K k d) M (timePsiCore N K k d M) M := by
  unfold sizePsiCore at hM
  exact (UBZ.frame _ (by decide) (ub_joinB _ _ _ M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_trB _ _ _ _ _ M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_mmB _ _ _ _ _ M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_trB _ _ _ _ _ M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_gadB _ _ _ M (by omega)) le_rfl).seq <|
    (ubz_copy _ _ (by decide) M).seq <|
    (UBZ.frame _ (by decide) (ub_joinB _ _ _ M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_selB _ _ M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_addB _ _ _ M (by omega)) le_rfl).seq <|
    (ubz_clear _ M).seq <| (ubz_clear _ M).seq <| (ubz_clear _ M).seq <| ubz_clear _ M

theorem sz_psiCore (N K k d M : ℕ) (hM : sizePsiCore N K k d ≤ M) (hB : M < 2 ^ 240) :
    SZ (psiCore N K k d) (2 ^ 21) := by
  unfold sizePsiCore at hM
  exact ((SZ.frame _ (sz_joinB _ _ _ M (by omega) hB)).seq <|
    (SZ.frame _ (sz_trB _ _ _ _ _ M (by omega) hB)).seq <|
    (SZ.frame _ (sz_mmB _ _ _ _ _ M (by omega) hB)).seq <|
    (SZ.frame _ (sz_trB _ _ _ _ _ M (by omega) hB)).seq <|
    (SZ.frame _ (sz_gadB _ _ _ M (by omega) hB)).seq <|
    (sz_prim _).seq <|
    (SZ.frame _ (sz_joinB _ _ _ M (by omega) hB)).seq <|
    (SZ.frame _ (sz_selB _ _ M (by omega) hB)).seq <|
    (SZ.frame _ (sz_addB _ _ _ M (by omega) hB)).seq <|
    (sz_prim _).seq <| (sz_prim _).seq <| (sz_prim _).seq <| sz_prim _).mono (by norm_num)

/-- The sizes of the templates of `bjCore`. -/
def sizeBjCore (N K k d : ℕ) : ℕ :=
  sizeTrB (nA * (2 * (2 * k))) N K 1 ((k - K) * N) + sizeGadB N K k +
    sizeSelB (nA * (2 * (2 * k * (k * N)))) (2 * k * (N * K)) +
    sizeHashB (nA * (2 * (2 * k * (k * N))) * (2 * k)) d N K

/-- **The time of `bjCore`** from tapes below `M`. -/
def timeBjCore (N K k d M : ℕ) : ℕ :=
  timeTrB (nA * (2 * (2 * k))) N K 1 ((k - K) * N) M + (timeGadB N K k M +
    (timeSelB (nA * (2 * (2 * k * (k * N)))) (2 * k * (N * K)) M +
    (timeHashB (nA * (2 * (2 * k * (k * N))) * (2 * k)) d N K M +
    ((2 * (M + 1) + 3) + ((2 * (M + 1) + 3) + (2 * (M + 1) + 3))))))

theorem ub_bjCore (N K k d M : ℕ) (hM : sizeBjCore N K k d ≤ M) :
    UBZ 20 (bjCore N K k d) M (timeBjCore N K k d M) M := by
  unfold sizeBjCore at hM
  exact (UBZ.frame _ (by decide) (ub_trB _ _ _ _ _ M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_gadB _ _ _ M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_selB _ _ M (by omega)) le_rfl).seq <|
    (UBZ.frame _ (by decide) (ub_hashB _ _ _ _ M (by omega)) le_rfl).seq <|
    (ubz_clear _ M).seq <| (ubz_clear _ M).seq <| ubz_clear _ M

theorem sz_bjCore (N K k d M : ℕ) (hM : sizeBjCore N K k d ≤ M) (hB : M < 2 ^ 240) :
    SZ (bjCore N K k d) (2 ^ 20) := by
  unfold sizeBjCore at hM
  exact ((SZ.frame _ (sz_trB _ _ _ _ _ M (by omega) hB)).seq <|
    (SZ.frame _ (sz_gadB _ _ _ M (by omega) hB)).seq <|
    (SZ.frame _ (sz_selB _ _ M (by omega) hB)).seq <|
    (SZ.frame _ (sz_hashB _ _ _ _ M (by omega) hB)).seq <|
    (sz_prim _).seq <| (sz_prim _).seq <| sz_prim _).mono (by norm_num)

end AdvancedEncryption.DualUse.Prog
