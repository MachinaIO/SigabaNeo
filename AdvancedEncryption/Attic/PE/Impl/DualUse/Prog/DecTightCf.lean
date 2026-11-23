import PE.Impl.DualUse.Prog.DecTightPre
import PE.Impl.DualUse.Prog.DecTightFin
import PE.Impl.DualUse.Prog.DecTightWf
import PE.Impl.DualUse.Prog.BlockCost

/-!
# The `c_f̂` block of `Dec`, per tape

`ph_cfX` (`BlockCost`) leaves every tape below the uniform bound `postCG … Gw` (`≈ 2^502` at
`confP`). Here the three phases are per tape: the crafted data (`ph_preC'`), the `W_f` block with
its per-tape output (`WB2.wOut`), the read-back (`ph_postC'`): afterwards only tape `0`
(`sk ++ ct`) and tape `2` (`c_f̂`) are non-blank (**`ph_cfX'`**).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

/-- The bounds after the block: tape `0`, tape `2`. -/
def cfOut (F0 F2 : ℕ) : Fin 256 → ℕ := fun t => if t.val = 0 then F0 else if t.val = 2 then F2 else 0

/-- **The glue**: clearing, then the three phases. -/
theorem ph_cfX' {wfB : XProg 256} {a LF Mβ a' Tp Tw Tq F0 F2 : ℕ}
    (hpre : Ph (preC hk c) (io2 (R := 254) a LF 0) Tp (io2 (R := 254) a' LF 0))
    (hw : Ph wfB (io2 (R := 254) a' LF 0) Tw WB2.wOut)
    (hpost : Ph (postC hk c) WB2.wOut Tq (cfOut F0 F2))
    {β : Fin 256 → ℕ} (h0 : β 0 ≤ a) (h1 : β 1 ≤ LF) (hβ : ∀ i, β i ≤ Mβ) :
    Ph (cfX hk c wfB) β (256 * (2 * (Mβ + 1) + 3) + (2 * (Mβ + 1) + 3) + (Tp + (Tw + Tq)))
      (cfOut F0 F2) :=
  (ph_clr01 h0 h1 hβ).seq (hpre.seq (hw.seq hpost))

/-- **The crafted data, per tape.** -/
theorem ph_preC' (a LF X Y T : ℕ)
    (hX : 2 * (a + 6 + lenPK hk c + lenKA hk c + N * K + 2 * lPsi (N := N) (K := K) hk +
      c.d * (N * K) + 10 * ((c.d - 2) * DualUse.rowL N K k + 2 * DualUse.rowL N K k) +
      (lenZ c - (lenKA hk c + N * K)) + lenZ c + DualUse.rowL N K k +
      (c.d - 2) * DualUse.rowL N K k + 2 * DualUse.rowL N K k + lPsi (N := N) (K := K) hk + 10 +
      c.d * (N * K) + (lenZ c - (lenKA hk c + N * K)) + nJ (N := N) hk + 10) +
      lenCj (N := N) hk + nJ (N := N) hk * (lenZ c + DualUse.rowL N K k) +
      lPsi (N := N) (K := K) hk + 10 ≤ X)
    (hoK : lenPK hk c + lenKA hk c + lenCj (N := N) hk ≤ Y)
    (hoP : lenPK hk c + fixLen (keyEnc (N := N) (K := K) c) ≤ Y)
    (hoJ : lenPK hk c + lenKA hk c ≤ Y) (hL : lenPK hk c ≤ Y) (hA : lenKA hk c ≤ Y)
    (hNK : N * K ≤ Y) (hLΨ : lPsi (N := N) (K := K) hk ≤ Y) (hLcj : lenCj (N := N) hk ≤ Y)
    (hTX : T ≤ X) (tZ : lenZ c ≤ T) (tR : DualUse.rowL N K k ≤ T) (tnJ : nJ (N := N) hk ≤ T)
    (tC0 : c.d * (N * K) ≤ T) (tZ2 : (c.d - 2) * DualUse.rowL N K k ≤ T)
    (tR2 : 2 * DualUse.rowL N K k ≤ T) (tPAD : lenZ c - (lenKA hk c + N * K) ≤ T)
    (tLΨ : lPsi (N := N) (K := K) hk ≤ T) (t10 : 10 ≤ T) :
    Ph (preC hk c) (io2 (R := 254) a LF 0)
      (preTCv X Y T ((c.d - 2) * DualUse.rowL N K k + 2 * DualUse.rowL N K k) (nJ (N := N) hk)
        (lenZ c + DualUse.rowL N K k))
      (io2 (R := 254) (a + 1 + lenPK hk c + c.d * (N * K) +
        10 * ((c.d - 2) * DualUse.rowL N K k + 2 * DualUse.rowL N K k) +
        nJ (N := N) hk * (lenZ c + DualUse.rowL N K k) + lPsi (N := N) (K := K) hk + 10) LF 0) := by
  have h := ph_frame (eLo 21 eLo21) (β := io2 (R := 254) a LF 0)
    (T := preTCv X Y T ((c.d - 2) * DualUse.rowL N K k + 2 * DualUse.rowL N K k) (nJ (N := N) hk)
        (lenZ c + DualUse.rowL N K k))
    (p := preCoreC (lenPK hk c) (lenKA hk c) (lenPK hk c + lenKA hk c + lenCj (N := N) hk) (N * K)
      (lenPK hk c + fixLen (keyEnc (N := N) (K := K) c)) (lPsi (N := N) (K := K) hk)
      (lenPK hk c + lenKA hk c) (lenCj (N := N) hk) (lenZ c) (DualUse.rowL N K k) (nJ (N := N) hk)
      (c.d * (N * K)) ((c.d - 2) * DualUse.rowL N K k) (2 * DualUse.rowL N K k)
      (lenZ c - (lenKA hk c + N * K)))
    (by
      rw [io2_eLo_nat, ← vec21_eq]
      exact (ph_preCoreC' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a X Y T hX hoK hoP hoJ hL hA hNK hLΨ hLcj
        hTX tZ tR tnJ tC0 tZ2 tR2 tPAD tLΨ t10).mono le_rfl le_rfl (le_of_eq (vec21_eq _)))
  rw [embedF_eLo_nat] at h
  exact h

theorem wOut_eLo (j : Fin 64) :
    WB2.wOut (eLo 64 eLo64 j) ≤ pcU 0 WB2.Lb WB2.wOut2 j := by
  fin_cases j <;> simp [WB2.wOut, pcU, eLo] <;> decide

theorem cfOut_of (F0 F2 : ℕ) :
    embedF (eLo 64 eLo64) WB2.wOut (pcF F0 F2) ≤ cfOut F0 F2 := fun t => by
  rcases embedF_cases (eLo 64 eLo64) WB2.wOut (pcF F0 F2) t with ⟨hn, h⟩ | ⟨j, hj, h⟩ <;> rw [h]
  · have h0 : t.val ≠ 0 := fun e => by
      have : eLo 64 eLo64 0 = t := Fin.ext (by rw [eLo_val]; simp [e])
      rw [← this, partialInv_self] at hn; exact Option.some_ne_none _ hn
    have h2 : t.val ≠ 2 := fun e => by
      have : eLo 64 eLo64 1 = t := Fin.ext (by rw [eLo_val]; simp [e])
      rw [← this, partialInv_self] at hn; exact Option.some_ne_none _ hn
    simp [WB2.wOut, cfOut, h0, h2, Fin.ext_iff]
  · subst hj
    clear h; fin_cases j <;> simp [pcF, cfOut, eLo]


/-- **The read-back, per tape**, from the per-tape output of the `W_f` block. -/
theorem ph_postC' (T : ℕ)
    (hTD : T ≤ WB2.Lb) (hWD : WB2.wOut2 ≤ WB2.Lb)
    (hW : WB2.wOut2 ≤ lenZ c + (1 * (2 * k) * N) * K) (hRZ : DualUse.rowL N K k ≤ lenZ c)
    (t1 : K ≤ T) (t2 : N ≤ T) (t3 : N * K ≤ T) (t4 : k ≤ T) (t5 : 2 * k * (N * K) ≤ T)
    (t6 : 1 * (2 * k) * N ≤ T) (t7 : lenZ c ≤ T) (t8 : nJ (N := N) hk ≤ T)
    (t9 : k * (N * K) ≤ T) :
    Ph (postC hk c) WB2.wOut
      (postCT' (lenPK hk c) (lenKA hk c) (N * K) (offWk hk c)
        (nJ (N := N) hk * (lenZ c + DualUse.rowL N K k)) (lenZ c) N K k (lenZ c)
        (DualUse.rowL N K k) (nJ (N := N) hk) WB2.Lb T)
      (cfOut (lenPK hk c + lenKA hk c + nJ (N := N) hk * DualUse.rowL N K k + N * K)
        ((1 * (2 * k) * N) * K)) :=
  (ph_frame (eLo 64 eLo64) ((ph_postCoreC' _ _ _ _ _ _ N K k _ _ _ WB2.Lb T WB2.wOut2 hTD hWD hW hRZ
    t1 t2 t3 t4 t5 t6 t7 t8 t9).mono wOut_eLo le_rfl le_rfl)).mono le_rfl le_rfl (cfOut_of _ _)

end AdvancedEncryption.DualUse.Prog
