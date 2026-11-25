import PE.Impl.RingBTVW.Prog.KeyTightPre
import PE.Impl.RingBTVW.Prog.KeyTightPost
import PE.Impl.RingBTVW.Prog.BlockCost
import PE.Impl.RingBTVW.Prog.WfB2S

/-!
# The key-row block of `KeyGen`, per tape

`ph_bfX` (`PE.Impl.RingBTVW.Prog.BlockCost`) bounds `bfX` with the row loop of the crafted data and
the gadget and addition of the read-back charged uniformly, and leaves every tape below one bound.
**`ph_bfX_v`** charges them per tape (`ph_preCoreB_v`, `ph_postCoreB_v`) and keeps track of the
blank tapes: only tapes `0` and `2` are nonblank afterwards (the `W_f` block clears all its tapes
but `0`, `2`, `wfB2S_clear`; the read-back clears its scratch).
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

/-! ### The `W_f` block clears its scratch -/

theorem lenBoundT_clrsP_le {k : ℕ} [NeZero k] : ∀ (l : List (Fin k)) (β : Fin k → ℕ),
    Prog.lenBoundT (clrsP l) β ≤ β
  | [], β => fun t => by
    simp only [clrsP, Prog.nop, Prog.lenBoundT, Prim.lenT, Function.update_apply]
    split_ifs with h <;> simp [h]
  | t :: l, β => fun i => by
    refine (lenBoundT_clrsP_le l _ i).trans ?_
    simp only [Prog.lenBoundT, Prim.lenT, Function.update_apply]
    split_ifs <;> simp

theorem lenBoundT_clrsP_mem {k : ℕ} [NeZero k] : ∀ (l : List (Fin k)) (β : Fin k → ℕ) (t : Fin k),
    t ∈ l → Prog.lenBoundT (clrsP l) β t = 0
  | [], _, _, h => absurd h (by simp)
  | s :: l, β, t, h => by
    show Prog.lenBoundT (clrsP l) (Prog.lenBoundT (Prog.clr s) β) t = 0
    by_cases hl : t ∈ l
    · exact lenBoundT_clrsP_mem l _ t hl
    · have hs : t = s := by simpa [hl] using h
      subst hs
      refine Nat.eq_zero_of_le_zero ((lenBoundT_clrsP_le l _ t).trans ?_)
      simp [Prog.lenBoundT, Prim.lenT]

theorem swp_symm_finClr : ∀ t : Fin 256, t.val ≠ 0 → t.val ≠ 2 → WB2.swp.symm t ∈ WB2.finClr := by
  decide +kernel

/-- **The stream block clears every tape but `0` and `2`.** -/
theorem wfB2S_clear {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (Ic W : ℕ) (ℓ : Fin 256 → ℕ)
    (t : Fin 256) (h0 : t.val ≠ 0) (h2 : t.val ≠ 2) : lenBoundT (wfB2S hk c Ic W) ℓ t = 0 := by
  have ht : t = WB2.eW (WB2.swp.symm t) := by simp [WB2.eW]
  rw [ht]
  show embedF WB2.eW ℓ _ (WB2.eW _) = 0
  rw [embedF_apply_self]
  exact lenBoundT_clrsP_mem _ _ _ (swp_symm_finClr t h0 h2)

/-! ### The block -/

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

/-- The bound after the block: tapes `0` and `2` below `M`, the others blank. -/
def v02 (M : ℕ) : Fin 256 → ℕ := fun t => if t.val = 0 ∨ t.val = 2 then M else 0

theorem eLo55_val_le (j : Fin 55) : ((eLo 55 eLo55 j).val = 0 ∨ (eLo 55 eLo55 j).val = 2) ↔ j.val ≤ 1 := by
  revert j; decide

/-- **The time of `bfX`, per tape.** -/
theorem ph_bfX_v {wfB : XProg 256} {Lw LF Tw Gw a Mβ X : ℕ}
    (hwT : timeBoundT wfB (wfIn Lw LF) ≤ Tw) (hwL : ∀ i, lenBoundT wfB (wfIn Lw LF) i ≤ Gw)
    (hwZ : ∀ ℓ t, t.val ≠ 0 → t.val ≠ 2 → lenBoundT wfB ℓ t = 0)
    (hX : a + 1 + 3 + lenPK hk c + (lenT N K k + 1) + nJ (N := N) hk * RingBTVW.rowL N K k +
      c.d * (N * K) + nA * (c.d * RingBTVW.rowL N K k) +
      nJ (N := N) hk * (lenZ c + RingBTVW.rowL N K k) + nA * (2 * RingBTVW.rowL N K k) + nA +
      lenZ c + RingBTVW.rowL N K k + (lenZ c - (lenT N K k + 1)) + nA ≤ X)
    (hoB : offBk c ≤ X) (hRM : nA * (c.d * RingBTVW.rowL N K k) ≤ X)
    (hPS : nA * (2 * RingBTVW.rowL N K k) ≤ X) (hnT : nJ (N := N) hk ≤ X)
    (hLw : a + 1 + 1 + lenPK hk c + c.d * (N * K) + nA * (c.d * RingBTVW.rowL N K k) +
      nJ (N := N) hk * (lenZ c + RingBTVW.rowL N K k) + nA * (2 * RingBTVW.rowL N K k) + nA ≤ Lw)
    (hG : ∀ x ∈ postTmpl N K k, x.2 ≤ postMd (lenPK hk c) (lenT N K k) Gw)
    {β : Fin 256 → ℕ} (h0 : β 0 ≤ a) (h1 : β 1 ≤ LF) (hβ : ∀ i, β i ≤ Mβ) :
    Ph (bfX hk c wfB) β (256 * (2 * (Mβ + 1) + 3) + (2 * (Mβ + 1) + 3) + (mvBitT a LF +
      (preTV X (nJ (N := N) hk) (lenZ c + RingBTVW.rowL N K k) + (Tw +
        postTV (lenPK hk c) (lenT N K k) (offWk hk c) (lenZ c) N K k Gw))))
      (v02 (postMd (lenPK hk c) (lenT N K k) Gw)) := by
  have p1 := ph_clr01 h0 h1 hβ
  have pm := ph_mvBit a LF
  have p2 : Ph (preB hk c) (io2 (R := 254) (a + 1) LF 0)
      (preTV X (nJ (N := N) hk) (lenZ c + RingBTVW.rowL N K k)) (io2 (R := 254)
      (a + 1 + 1 + lenPK hk c + c.d * (N * K) + nA * (c.d * RingBTVW.rowL N K k) +
        nJ (N := N) hk * (lenZ c + RingBTVW.rowL N K k) + nA * (2 * RingBTVW.rowL N K k) + nA) LF 0) := by
    have h := ph_frame (eLo 18 eLo18) (β := io2 (R := 254) (a + 1) LF 0)
      (T := preTV X (nJ (N := N) hk) (lenZ c + RingBTVW.rowL N K k))
      (p := preCoreB (lenPK hk c) (lenT N K k + 1) (offBk c) (nJ (N := N) hk * RingBTVW.rowL N K k)
        (lenZ c) (RingBTVW.rowL N K k) (nJ (N := N) hk) (c.d * (N * K))
        (nA * (c.d * RingBTVW.rowL N K k)) (nA * (2 * RingBTVW.rowL N K k)) (lenZ c - (lenT N K k + 1)))
      (by
        rw [io2_eLo_nat, ← vec18_eq]
        exact (ph_preCoreB_v _ _ _ _ _ _ _ _ _ _ _ (a + 1) X (by omega) hoB hRM hPS hnT).mono le_rfl
          le_rfl (le_of_eq (vec18_eq _)))
    rw [embedF_eLo_nat] at h
    exact h
  have p3 : Ph wfB (io2 (R := 254) (a + 1 + 1 + lenPK hk c + c.d * (N * K) +
      nA * (c.d * RingBTVW.rowL N K k) + nJ (N := N) hk * (lenZ c + RingBTVW.rowL N K k) +
      nA * (2 * RingBTVW.rowL N K k) + nA) LF 0) Tw (v02 Gw) := fun ℓ hℓ => by
    obtain ⟨t1, t2⟩ := ph_wf (wfB := wfB) hwT hwL hLw ℓ hℓ
    refine ⟨t1, fun t => ?_⟩
    simp only [v02]
    split_ifs with h
    · exact t2 t
    · push Not at h
      rw [hwZ ℓ t h.1 h.2]
  have p4 : Ph (postB hk c) (v02 Gw)
      (postTV (lenPK hk c) (lenT N K k) (offWk hk c) (lenZ c) N K k Gw)
      (v02 (postMd (lenPK hk c) (lenT N K k) Gw)) := by
    have h := ph_frame (eLo 55 eLo55) (β := v02 Gw)
      ((ph_postCoreB_v (lenPK hk c) (lenT N K k) (offWk hk c) (lenZ c) N K k Gw hG).mono
        (fun j => by simp only [v02]; split_ifs <;> omega) le_rfl le_rfl)
    refine h.mono le_rfl le_rfl (fun t => ?_)
    rcases embedF_cases (eLo 55 eLo55) (v02 Gw)
      (fun j => if j.val ≤ 1 then postMd (lenPK hk c) (lenT N K k) Gw else 0) t with
      ⟨hn, e⟩ | ⟨j, rfl, e⟩
    · rw [e]
      simp only [v02]
      split_ifs with h'
      · exfalso
        have hj : ∃ j, eLo 55 eLo55 j = t := by
          rcases h' with h' | h'
          · exact ⟨0, Fin.ext (by rw [eLo_val]; simp [h'])⟩
          · exact ⟨1, Fin.ext (by rw [eLo_val]; simp [h'])⟩
        obtain ⟨j, rfl⟩ := hj
        rw [partialInv_self] at hn
        exact absurd hn (by simp)
      · exact Nat.zero_le _
    · rw [e]
      have := eLo55_val_le j
      by_cases hj : j.val ≤ 1 <;> simp_all [v02]
  exact p1.seq (pm.seq (p2.seq (p3.seq p4)))

end AdvancedEncryption.RingBTVW.Prog
