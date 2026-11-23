import PE.Impl.DualUse.Prog.SizeCost
import PE.Impl.DualUse.Prog.SetupL
import PE.Impl.DualUse.Prog.SetupEncCost
import PE.Impl.DualUse.Prog.CompCost
import PE.Impl.DualUse.ReductionCompsBound

/-!
# The state counts of `Setup` and `Enc` at `confP`

`size_setupP_conf`, `size_encP_conf`: explicit bounds of `XProg.size` of the programs of `Setup`
and `Enc` with the sampler `chiSamplerP`, from the state counts of their blocks (`SZ`).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.DualUse.Params
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow

section Generic

variable {k : ℕ}

theorem sz_appendTapeP' (r a S c : Fin k) : SZ (appendTapeP r a S c) 1000 := by
  unfold SZ appendTapeP XProg.forN; simp [Prog.size, Prim.pad]

theorem sz_frameApP (r a S c : Fin k) : SZ (frameApP r a S c) 1000 := by
  unfold SZ frameApP XProg.forN; simp [Prog.size, Prim.pad]

theorem sz_dropP (S c t : Fin k) : SZ (dropP S c t) 1000 := by
  unfold SZ dropP XProg.forN; simp [Prog.size, Prim.pad]

theorem sz_unframeP (W D c t : Fin k) : SZ (unframeP W D c t) 1000 := by
  unfold SZ unframeP XProg.forN; simp [Prog.size, Prim.pad]

theorem sz_progP {p : Prog k} {a : ℕ} (h : p.size ≤ a) : SZ (prog p) a := by
  unfold SZ; rw [size_prog]; exact h

end Generic

/-! ### `Setup` -/

theorem sz_appC (r a : Fin 96) : SZ (appC r a) 1060 :=
  (sz_prim _).seq (sz_appendTapeP' _ _ _ _)

theorem sz_c0P {oB oS d N K M : ℕ} (hB : M < 2 ^ 240) (h1 : oB ≤ M) (h2 : d * (N * K) ≤ M)
    (h3 : oS ≤ M) (h4 : N * K ≤ M) (h5 : K ≤ M) (h6 : N ≤ M) (h7 : 1 ≤ M) (h8 : d ≤ M)
    (h9 : d * N ≤ M) :
    SZ (c0P oB oS d N K) (12 * 46836 + 2 * 2 ^ 12 + 2 ^ 16 + 2 ^ 12 + 60 + 36 * 21) := by
  unfold c0P
  have hn := fun (t c : Fin 82) (n : ℕ) (hn : n ≤ M) => sz_natP (t := t) (c := c) hn hB
  have e1 : 1 * d * (N * K) ≤ M := by rw [Nat.one_mul]; exact h2
  have e2 : 1 * d * N ≤ M := by rw [Nat.one_mul]; exact h9
  exact ((hn _ _ _ h1).seq <| (hn _ _ _ h2).seq <| (hn _ _ _ h3).seq <| (hn _ _ _ h4).seq <|
    (hn _ _ _ h2).seq <| (hn _ _ _ h5).seq <| (hn _ _ _ h6).seq <| (hn _ _ _ h7).seq <|
    (hn _ _ _ h7).seq <| (hn _ _ _ h8).seq <| (hn _ _ _ e1).seq <| (hn _ _ _ e2).seq <|
    (SZ.frame _ (sz_progP size_splitP)).seq <| (SZ.frame _ (sz_progP size_splitP)).seq <|
    (SZ.frame _ (sz_progP size_matMulP)).seq <| (SZ.frame _ (sz_progP size_addRWP)).seq <|
    (sz_prim _).seq (sz_clearL c0Tapes)).mono (by simp [c0Tapes])

theorem sz_b1P {N K k M : ℕ} (hB : M < 2 ^ 240) (h1 : K ≤ M) (h2 : N ≤ M) (h3 : N * K ≤ M)
    (h4 : k ≤ M) (h5 : rowL N K k ≤ M) (h6 : 1 * (2 * k) * N ≤ M)
    (h7 : N * K + rowL N K k + rowL N K k ≤ M) :
    SZ (b1P N K k) (10 * 46836 + 2 ^ 12 + 2 ^ 14 + 2 ^ 12 + 2 ^ 12 + 60 + 36 * 15) := by
  unfold b1P
  have hn := fun (t c : Fin 82) (n : ℕ) (hn : n ≤ M) => sz_natP (t := t) (c := c) hn hB
  have e1 : N * K - 1 ≤ M := by omega
  exact ((hn _ _ _ h1).seq <| (hn _ _ _ h2).seq <| (hn _ _ _ h3).seq <| (hn _ _ _ h4).seq <|
    (hn _ _ _ h5).seq <| (hn _ _ _ h5).seq <| (hn _ _ _ h6).seq <| (hn _ _ _ h7).seq <|
    (SZ.frame _ (sz_progP size_splitP)).seq <| (SZ.frame _ (sz_progP size_gadP)).seq <|
    (SZ.frame _ (sz_progP size_subRWP)).seq <| (hn _ _ _ e1).seq <|
    (sz_prim _).seq <| (SZ.frame _ (sz_progP size_joinP)).seq (sz_clearL b1Tapes)).mono
    (by simp [b1Tapes])

theorem setup_counts : nRowD Np Kp confP.d ≤ 2 ^ 181 ∧ nRowC Np Kp kp ≤ 2 ^ 181 ∧
    Np ≤ 2 ^ 181 ∧ (Enum.list (α := RingBTVW.Col kp)).length * Np ≤ 2 ^ 181 ∧
    nBj (N := Np) (K := Kp) hkp ≤ 2 ^ 181 ∧ Np * Kp ≤ 2 ^ 181 ∧
    2 * kp * (Np * Kp) ≤ 2 ^ 181 ∧ 2 * kp * (Np * Kp) + 2 * kp * (Np * Kp) + Np * Kp ≤ 2 ^ 181 ∧
    2 * kp * Np ≤ 2 ^ 181 := by
  simp only [nRowD, nRowC, nBj]
  comp_unfold
  norm_num

theorem size_setupDet_conf : (setupDet (N := Np) (K := Kp) (k := kp)).size ≤ 2 ^ 21 := by
  obtain ⟨-, -, -, -, -, h6, h7, h8, h9⟩ := setup_counts
  have hB : (2 : ℕ) ^ 181 < 2 ^ 240 := by norm_num
  have hK : Kp ≤ 2 ^ 181 := by rw [Kp_def]; norm_num
  have hN : Np ≤ 2 ^ 181 := by rw [Np_def]; norm_num
  have hk : kp ≤ 2 ^ 181 := by rw [kp, Kp_def]; norm_num
  have c0 := sz_c0P (oB := 0) (oS := 2 * kp * (Np * Kp)) (d := 2 * kp) (N := Np) (K := Kp) hB
    (Nat.zero_le _) h7 h7 h6 hK hN (by norm_num)
    (by rw [kp, Kp_def]; norm_num) h9
  have b1 := sz_b1P (N := Np) (K := Kp) (k := kp) hB hK hN h6 hk
    (by simp only [rowL, Nat.one_mul]; exact h7) (by rw [Nat.one_mul]; exact h9)
    (by simp only [rowL, Nat.one_mul]; omega)
  unfold setupDet
  exact ((sz_prim _).seq <| (sz_appC _ _).seq <| (sz_appC _ _).seq <| (SZ.frame _ c0).seq <|
    (sz_prim _).seq <| (sz_prim _).seq <| (sz_appC _ _).seq <| (SZ.frame _ b1).seq <|
    (sz_prim _).seq <| (sz_prim _).seq <| (sz_appC _ _).seq <| (sz_appC _ _).seq <|
    (sz_appC _ _).seq <| (sz_frameApP _ _ _ _).seq <| (sz_appC _ _).seq <| (sz_appC _ _).seq
    (sz_frameApP _ _ _ _)).mono (by norm_num)

/-- **The states of `Setup`'s program at `confP`.** -/
theorem size_setupP_conf : (setupP hkp confP chiSamplerP).size ≤ 2 ^ 24 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -, -⟩ := setup_counts
  have hB : (2 : ℕ) ^ 181 < 2 ^ 240 := by norm_num
  have hD := size_setupDet_conf
  unfold setupP
  exact ((SZ.frame _ (sz_coinsF h1 hB)).seq <| (SZ.frame _ (sz_coinsF h2 hB)).seq <|
    (SZ.frame _ (sz_repF h3 hB sz_chiP)).seq <| (SZ.frame _ (sz_repF h4 hB sz_chiP)).seq <|
    (SZ.frame _ (sz_coinsF h5 hB)).seq <| (SZ.frame _ (sz_coinsF h6 hB)).seq hD).mono
    (by norm_num)

/-! ### `Enc` -/

theorem sz_natL {M : ℕ} (hB : M < 2 ^ 240) :
    ∀ l : List (Fin 124 × ℕ), (∀ p ∈ l, p.2 ≤ M) → SZ (natL l) (46836 * l.length + 60)
  | [], _ => (sz_prim _).mono (by simp)
  | p :: l, h => ((sz_natP (h p (by simp)) hB).seq
      (sz_natL hB l fun q hq => h q (by simp [hq]))).mono (by simp; ring_nf; omega)

theorem tmpl_conf : ∀ p ∈ tmplList hkp confP, p.2 ≤ 2 ^ 200 := by
  intro p hp
  simp only [tmplList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
  all_goals ((try simp only [ctLen, nTrap, nJenc]) <;> (try comp_unfold) <;>
    (try simp only [confP_d, kp, Kp_def, Np_def]) <;> norm_num)

theorem size_encCoreP : encCoreP.size ≤ 2 ^ 20 := by decide +kernel

theorem enc_counts : Np * Kp ≤ 2 ^ 181 ∧
    (Enum.list (α := Fin confP.d)).length * Np ≤ 2 ^ 181 ∧ Np ≤ 2 ^ 181 ∧
    (Enum.list (α := RingBTVW.Col kp)).length * Np ≤ 2 ^ 181 ∧ nR hkp confP ≤ 2 ^ 181 ∧
    nE (N := Np) hkp ≤ 2 ^ 181 ∧ Kp + confP.w ≤ 2 ^ 181 := by
  obtain ⟨-, -, h3, h4, h5, h6, h7, h8, h9, -, -, -, -⟩ := counts_le
  exact ⟨h3, h4, h5, h6, h7, h8, h9⟩

theorem parse_counts : 2 * DualUse.pw.length + 1 ≤ 2 ^ 181 ∧
    (Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin confP.d)).length * (Np * Kp)) ≤ 2 ^ 181 ∧
    (Enum.list (α := Fin 1)).length * ((Enum.list (α := TrapCol kp)).length * (Np * Kp)) ≤ 2 ^ 181 ∧
    (Enum.list (α := (Sdw (N := Np) hkp).Attr × (Sdw (N := Np) hkp).ctBits.Index)).length *
      ((Enum.list (α := Fin 1)).length * ((Enum.list (α := RingBTVW.Col kp)).length * (Np * Kp)))
        ≤ 2 ^ 181 := by
  simp only [DualUse.pw, length_paramsWord_date]
  comp_unfold
  norm_num

theorem size_encParseP_conf : (encParseP hkp confP).size ≤ 2 ^ 19 := by
  obtain ⟨h0, h1, h2, h3⟩ := parse_counts
  have hB : (2 : ℕ) ^ 181 < 2 ^ 240 := by norm_num
  have hNK : Np * Kp ≤ 2 ^ 181 := enc_counts.1
  have hn := fun (t c : Fin 124) (n : ℕ) (hn : n ≤ 2 ^ 181) => sz_natP (t := t) (c := c) hn hB
  have uf := fun (D : Fin 124) (n : ℕ) (h : n ≤ 2 ^ 181) =>
    (hn 121 123 n h).seq ((sz_unframeP 120 D 123 121).seq (sz_prim (k := 124) (.clear 121)))
  unfold encParseP
  exact (((hn 121 123 _ h0).seq ((sz_dropP 120 123 121).seq (sz_prim (k := 124) (.clear 121)))).seq <|
    (uf 1 _ h1).seq <| (uf 2 _ h2).seq <| (uf 3 _ h3).seq <| (uf 4 _ hNK).seq <| (sz_prim _).seq <|
    (uf 5 10 (by norm_num)).seq <| (sz_prim _).seq (uf 6 1 (by norm_num))).mono (by norm_num)

/-- **The states of `Enc`'s program at `confP`.** -/
theorem size_encP_conf : (encP hkp confP chiSamplerP).size ≤ 2 ^ 24 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := enc_counts
  have hB : (2 : ℕ) ^ 181 < 2 ^ 240 := by norm_num
  have hB' : (2 : ℕ) ^ 200 < 2 ^ 240 := by norm_num
  have hP : SZ _ _ := size_encParseP_conf
  have hT := sz_natL hB' _ tmpl_conf
  have hl : (tmplList hkp confP).length = 27 := rfl
  rw [hl] at hT
  unfold encP encTail
  exact (hP.seq <| (SZ.frame _ (sz_coinsF h1 hB)).seq <| (SZ.frame _ (sz_repF h2 hB sz_chiP)).seq <|
    (SZ.frame _ (sz_repF h3 hB sz_chiP)).seq <| (SZ.frame _ (sz_repF h4 hB sz_chiP)).seq <|
    (SZ.frame _ (sz_repF h4 hB sz_chiP)).seq <| (SZ.frame _ (sz_repF h5 hB (sz_entB h1 hB))).seq <|
    (SZ.frame _ (sz_repF h6 hB (sz_entF h7 hB))).seq <| (SZ.frame _ (sz_repF h3 hB sz_chiP)).seq <|
    hT.seq ((SZ.frame _ (sz_progP size_encCoreP)).seq (sz_frameApP _ _ _ _))).mono (by norm_num)

end AdvancedEncryption.DualUse.Prog
