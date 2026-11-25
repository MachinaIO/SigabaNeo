import PE.Impl.ExpLUT.Prog.EncTightCert
/-!
# The encryption core on its actual counters (tight encryption clock, part 4)

The 22 helper and automorphism rounds install their exponent templates (literal words of at
most `W = 2^22` bits), run the certified block and release the templates, restoring the block's
input bounds (`tb_round`); the four phases sit in disjoint slots of the core, sharing only the
output register, so each phase sees the loader's bounds of its own tapes (`core_tight`).
-/

namespace AdvancedEncryption.ExpLUT.Prog.EncTight

set_option maxRecDepth 100000

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Tape.Sym SigabaNeo.Tape.Prog.SpecT
open AdvancedEncryption.ExpLUT.Prog AdvancedEncryption.ExpLUT.Prog.EncW

theorem putW_time_le (w : List Bool) (hw : w.length ≤ 2 ^ 22) :
    (w.length + 1) * (2 * (top ρE + (w.length + 1)) + 5) ≤ 2 ^ 123 := by
  rw [top_ρE]
  calc (w.length + 1) * (2 * (2 ^ 99 + (w.length + 1)) + 5)
      ≤ (2 ^ 22 + 1) * (2 * (2 ^ 99 + (2 ^ 22 + 1)) + 5) := by gcongr
    _ ≤ 2 ^ 123 := by norm_num

/-- **One round**: two exponent templates of at most `W` bits around a certified block. -/
theorem tb_round {n : ℕ} (blk : SigabaNeo.Tape.Prog n) (σ : Asg) (T : ℕ)
    (hblk : TB blk ρE σ σ T) (a b : Fin n) (hab : a ≠ b) (wa wb : List Bool)
    (hwa : wa.length ≤ 2 ^ 22) (hwb : wb.length ≤ 2 ^ 22)
    (ha : bnd ρE σ a = 2 ^ 22) (hb : bnd ρE σ b = 2 ^ 22) :
    TB (.seq (putW a wa) (.seq (putW b wb) (.seq blk (.seq (clr a) (clr b))))) ρE σ σ
      (T + 2 ^ 125) := by
  have h1 := TB.putW a wa ρE σ (by rw [top_ρE]; omega)
  have h2 := TB.putW b wb ρE (aSet σ a.val (pC wa.length)) (by rw [top_ρE]; omega)
  have h2' : TB (putW b wb) ρE (aSet σ a.val (pC wa.length)) σ
      ((wb.length + 1) * (2 * (top ρE + (wb.length + 1)) + 5)) := by
    refine h2.mono (fun _ => le_rfl) (fun j => ?_) le_rfl
    rw [bnd_aSet_apply, bnd_aSet_apply]
    split_ifs with h h'
    · subst h; simpa [hb] using hwb
    · subst h'; simpa [ha] using hwa
    · exact le_rfl
  have hc : ∀ i : Fin n, TB (clr i) ρE σ σ (2 * top ρE + 3) := fun i =>
    (TB.clr i ρE σ).mono (fun _ => le_rfl)
      (fun j => by rw [bnd_aSet_apply]; split_ifs <;> simp) le_rfl
  refine (h1.seq (h2'.seq (hblk.seq ((hc a).seq (hc b))))).mono (fun _ => le_rfl)
    (fun _ => le_rfl) ?_
  have t1 := putW_time_le wa hwa
  have t2 := putW_time_le wb hwb
  rw [top_ρE] at t1 t2 ⊢
  omega

theorem bnd_σHE_5 : bnd ρE σHE (5 : Fin 69) = 2 ^ 22 := by decide +kernel
theorem bnd_σHE_6 : bnd ρE σHE (6 : Fin 69) = 2 ^ 22 := by decide +kernel
theorem bnd_σAE_7 : bnd ρE σAE (7 : Fin 85) = 2 ^ 22 := by decide +kernel
theorem bnd_σAE_8 : bnd ρE σAE (8 : Fin 85) = 2 ^ 22 := by decide +kernel

theorem templ_le {t : ℕ} (ht : t ≤ 22) :
    (List.replicate (2 ^ t) false).length ≤ 2 ^ 22 ∧
      (List.replicate (2 ^ Dc.b - 2 ^ t) false).length ≤ 2 ^ 22 := by
  simp only [List.length_replicate, Dc_b]
  exact ⟨Nat.pow_le_pow_right (by norm_num) ht, Nat.sub_le _ _⟩

theorem tb_helperRound {t : ℕ} (ht : t ≤ 22) :
    TB (helperRoundP Dc t) ρE σHE σHE (2 ^ 203 + 2 ^ 125) :=
  tb_round hBlkP σHE _ tb_hBlkE 5 6 (by decide) _ _ (templ_le ht).1 (templ_le ht).2
    bnd_σHE_5 bnd_σHE_6

theorem tb_autRound {t : ℕ} (ht : t ≤ 22) :
    TB (autRoundP Dc t) ρE σAE σAE (2 ^ 236 + 2 ^ 125) :=
  tb_round autBlkP σAE _ tb_autBlkE 7 8 (by decide) _ _ (templ_le ht).1 (templ_le ht).2
    bnd_σAE_7 bnd_σAE_8

theorem tb_helperPairs (j n : ℕ) (hn : j + n ≤ 22) :
    TB (helperPairsP Dc j n) ρE σHE σHE (n * (2 ^ 203 + 2 ^ 125) + (2 * 2 ^ 99 + 3)) := by
  induction n generalizing j with
  | zero => simpa [helperPairsP, top_ρE] using TB.cpSelf (0 : Fin 69) ρE σHE
  | succ n ih =>
    exact ((tb_helperRound (by omega)).seq (ih (j + 1) (by omega))).mono (fun _ => le_rfl)
      (fun _ => le_rfl) (by rw [Nat.succ_mul]; omega)

theorem tb_autBlocks (j n : ℕ) (hn : j + n ≤ 22) :
    TB (autBlocksP Dc j n) ρE σAE σAE (n * (2 ^ 236 + 2 ^ 125) + (2 * 2 ^ 99 + 3)) := by
  induction n generalizing j with
  | zero => simpa [autBlocksP, top_ρE] using TB.cpSelf (0 : Fin 85) ρE σAE
  | succ n ih =>
    exact ((tb_autRound (by omega)).seq (ih (j + 1) (by omega))).mono (fun _ => le_rfl)
      (fun _ => le_rfl) (by rw [Nat.succ_mul]; omega)

/-- The clock of the core. -/
def coreT : ℕ := 2 ^ 228 + (22 * (2 ^ 203 + 2 ^ 125) + (2 * 2 ^ 99 + 3)) +
  (22 * (2 ^ 236 + 2 ^ 125) + (2 * 2 ^ 99 + 3)) + 2 ^ 240

theorem bnd_σHE_0 : bnd ρE σHE (0 : Fin 69) = 2 ^ 99 := by decide +kernel
theorem bnd_σAE_0 : bnd ρE σAE (0 : Fin 85) = 2 ^ 99 := by decide +kernel
theorem bnd_σTE_0 : bnd ρE σTE (0 : Fin 104) = 2 ^ 99 := by decide +kernel

/-- Slots of distinct phases differ on the nonzero tapes of the later phase. -/
theorem core_sep {off n off' n' : ℕ} (hn : off + n < 321) (hn' : off' + n' < 321)
    (hsep : off + n ≤ off') (i : Fin (n + 1)) (j : Fin (n' + 1)) (hj : j ≠ 0) :
    coreTape (phaseSlot off n hn i) ≠ coreTape (phaseSlot off' n' hn' j) :=
  fun h => phaseSlot_separate hn hn' hsep i j hj (coreTape_inj h)

/-- **The core**, from the loader's per-tape bounds of the four phases' tapes. -/
theorem core_tight (ℓ : Fin 326 → ℕ) (hM : ∀ t, ℓ t ≤ 2 ^ 99)
    (hb : ∀ j, ℓ (coreTape (bSlot j)) ≤ bnd ρE σME j)
    (hh : ∀ j, ℓ (coreTape (helperSlot j)) ≤ bnd ρE σHE j)
    (ha : ∀ j, ℓ (coreTape (autSlot j)) ≤ bnd ρE σAE j)
    (ht : ∀ j, ℓ (coreTape (tailSlot j)) ≤ bnd ρE σTE j) :
    timeBoundT (map coreTape (encCoreP Dc)) ℓ ≤ coreT ∧
      ∀ t, lenBoundT (map coreTape (encCoreP Dc)) ℓ t ≤ 2 ^ 99 := by
  have e : map coreTape (encCoreP Dc) =
      .seq (map (coreTape ∘ bSlot) mrowP)
        (.seq (map (coreTape ∘ helperSlot) (helperPairsP Dc 0 Dc.b))
          (.seq (map (coreTape ∘ autSlot) (autBlocksP Dc 0 Dc.b))
            (map (coreTape ∘ tailSlot) tailP))) := by
    simp only [encCoreP, map_seq_enc, map_map_enc]
  rw [e]
  have hM' : ∀ t, ℓ t ≤ top ρE := hM
  obtain ⟨a1, b1, c1⟩ := tb_mrowE 326 _ (coreTape_inj.comp bSlot_inj) ℓ hb hM'
  set ℓ₁ := lenBoundT (map (coreTape ∘ bSlot) mrowP) ℓ with hℓ₁
  -- the later phases' nonzero tapes are untouched by the earlier ones
  have o1 : ∀ {off n} (hn : off + n < 321) (j : Fin (n + 1)), j ≠ 0 → 65 ≤ off →
      ℓ₁ (coreTape (phaseSlot off n hn j)) = ℓ (coreTape (phaseSlot off n hn j)) := by
    intro off n hn j hj hoff
    exact lenBoundT_map_off (coreTape ∘ bSlot) mrowP
      (fun i => core_sep (off := 0) (n := 65) (by decide) hn (by omega) i j hj) ℓ
  have hD : Dc.b = 22 := Dc_b
  obtain ⟨a2, b2, c2⟩ := tb_helperPairs 0 Dc.b (by omega) 326 _
    (coreTape_inj.comp helperSlot_inj) ℓ₁ (fun j => by
      by_cases hj : j = 0
      · subst hj; rw [bnd_σHE_0]; exact b1 _
      · show ℓ₁ (coreTape (phaseSlot 65 68 _ j)) ≤ _
        rw [o1 _ j hj le_rfl]; exact hh j) b1
  set ℓ₂ := lenBoundT (map (coreTape ∘ helperSlot) (helperPairsP Dc 0 Dc.b)) ℓ₁ with hℓ₂
  have o2 : ∀ {off n} (hn : off + n < 321) (j : Fin (n + 1)), j ≠ 0 → 133 ≤ off →
      ℓ₂ (coreTape (phaseSlot off n hn j)) = ℓ (coreTape (phaseSlot off n hn j)) := by
    intro off n hn j hj hoff
    show lenBoundT (map (coreTape ∘ helperSlot) (helperPairsP Dc 0 Dc.b)) ℓ₁
      (coreTape (phaseSlot off n hn j)) = _
    rw [lenBoundT_map_off (coreTape ∘ helperSlot) (helperPairsP Dc 0 Dc.b)
      (fun i => core_sep (off := 65) (n := 68) (by decide) hn (by omega) i j hj) ℓ₁]
    exact o1 hn j hj (by omega)
  obtain ⟨a3, b3, c3⟩ := tb_autBlocks 0 Dc.b (by omega) 326 _
    (coreTape_inj.comp autSlot_inj) ℓ₂ (fun j => by
      by_cases hj : j = 0
      · subst hj; rw [bnd_σAE_0]; exact b2 _
      · show ℓ₂ (coreTape (phaseSlot 133 84 _ j)) ≤ _
        rw [o2 _ j hj le_rfl]; exact ha j) b2
  set ℓ₃ := lenBoundT (map (coreTape ∘ autSlot) (autBlocksP Dc 0 Dc.b)) ℓ₂ with hℓ₃
  obtain ⟨a4, b4, c4⟩ := tb_tailE 326 _ (coreTape_inj.comp tailSlot_inj) ℓ₃ (fun j => by
      by_cases hj : j = 0
      · subst hj; rw [bnd_σTE_0]; exact b3 _
      · show lenBoundT (map (coreTape ∘ autSlot) (autBlocksP Dc 0 Dc.b)) ℓ₂
          (coreTape (phaseSlot 217 103 (by decide) j)) ≤ _
        rw [lenBoundT_map_off (t := coreTape (phaseSlot 217 103 (by decide) j))
          (coreTape ∘ autSlot) (autBlocksP Dc 0 Dc.b)
          (fun i => core_sep (off := 133) (n := 84) (off' := 217) (n' := 103) (by decide) (by decide)
            (by omega) i j hj) ℓ₂,
          o2 _ j hj (by omega)]
        exact ht j) b3
  refine ⟨?_, fun t => ?_⟩
  swap
  · rw [lenBoundT_seq_enc, lenBoundT_seq_enc, lenBoundT_seq_enc, ← hℓ₁, ← hℓ₂, ← hℓ₃]
    exact b4 t
  rw [timeBoundT_seq, ← hℓ₁, timeBoundT_seq, ← hℓ₂, timeBoundT_seq, ← hℓ₃]
  have k2 := c2.trans (le_of_eq (by rw [hD]) :
    Dc.b * (2 ^ 203 + 2 ^ 125) + (2 * 2 ^ 99 + 3) ≤ 22 * (2 ^ 203 + 2 ^ 125) + (2 * 2 ^ 99 + 3))
  have k3 := c3.trans (le_of_eq (by rw [hD]) :
    Dc.b * (2 ^ 236 + 2 ^ 125) + (2 * 2 ^ 99 + 3) ≤ 22 * (2 ^ 236 + 2 ^ 125) + (2 * 2 ^ 99 + 3))
  unfold coreT
  omega

end AdvancedEncryption.ExpLUT.Prog.EncTight
