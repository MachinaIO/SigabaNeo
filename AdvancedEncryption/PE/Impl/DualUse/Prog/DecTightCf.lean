import PE.Impl.DualUse.Prog.DecTightPre
import PE.Impl.DualUse.Prog.DecTightPost
import PE.Impl.DualUse.Prog.DecTightFin
import PE.Impl.DualUse.Prog.DecTightWf
import PE.Impl.DualUse.Prog.BlockCost

/-!
# The `c_f̂` block of `Dec`, per tape

`ph_cfX` (`BlockCost`) leaves every tape below the uniform bound `postCG … Gw` (`≈ 2^502` at
`confP`). Here the phases are per tape: the bit `f(0)` moved behind the data word (`ph_mvBit`),
the crafted data (`ph_preC'`), the stream block with its per-tape output (`WB2.wOutS`), the
read-back (`ph_postC'`): afterwards only tape `0`
(`sk ++ ct`) and tape `2` (`c_f̂`) are non-blank (**`ph_cfX'`**).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

/-- The bounds after the block: tape `0`, tape `2`. -/
def cfOut (F0 F2 : ℕ) : Fin 256 → ℕ := fun t => if t.val = 0 then F0 else if t.val = 2 then F2 else 0

/-- **The glue**: clearing, the bit, then the three phases. -/
theorem ph_cfX' {wfB : XProg 256} {a LF Mβ a' Tp Tw Tq F0 F2 : ℕ}
    (hpre : Ph (preC hk c) (io2 (R := 254) (a + 1) LF 0) Tp (io2 (R := 254) a' LF 0))
    (hw : Ph wfB (io2 (R := 254) a' LF 0) Tw WB2.wOutS)
    (hpost : Ph (postC hk c) WB2.wOutS Tq (cfOut F0 F2))
    {β : Fin 256 → ℕ} (h0 : β 0 ≤ a) (h1 : β 1 ≤ LF) (hβ : ∀ i, β i ≤ Mβ) :
    Ph (cfX hk c wfB) β (256 * (2 * (Mβ + 1) + 3) + (2 * (Mβ + 1) + 3) +
      (mvBitT a LF + (Tp + (Tw + Tq)))) (cfOut F0 F2) :=
  (ph_clr01 h0 h1 hβ).seq ((ph_mvBit a LF).seq (hpre.seq (hw.seq hpost)))

/-- **The crafted data, per tape.** -/
theorem ph_preC' (a LF X Y T : ℕ)
    (hX : 2 * (a + 6 + lenPK hk c + lenKA hk c + (N * K + 1) + 2 * lPsi (N := N) (K := K) hk +
      c.d * (N * K) + nA * ((c.d - 2) * DualUse.rowL N K k + 2 * DualUse.rowL N K k) +
      (lenZ c - (lenKA hk c + N * K + 1)) + lenZ c + DualUse.rowL N K k +
      (c.d - 2) * DualUse.rowL N K k + 2 * DualUse.rowL N K k + lPsi (N := N) (K := K) hk + nA +
      c.d * (N * K) + (lenZ c - (lenKA hk c + N * K + 1)) + nJ (N := N) hk + nA) +
      lenCj (N := N) hk + nJ (N := N) hk * (lenZ c + DualUse.rowL N K k) +
      lPsi (N := N) (K := K) hk + nA ≤ X)
    (hoK : lenPK hk c + lenKA hk c + lenCj (N := N) hk ≤ Y)
    (hoP : lenPK hk c + fixLen (keyEnc (N := N) (K := K) c) ≤ Y)
    (hoJ : lenPK hk c + lenKA hk c ≤ Y) (hL : lenPK hk c ≤ Y) (hA : lenKA hk c ≤ Y)
    (hNK : N * K + 1 ≤ Y) (hLΨ : lPsi (N := N) (K := K) hk ≤ Y) (hLcj : lenCj (N := N) hk ≤ Y)
    (hTX : T ≤ X) (tZ : lenZ c ≤ T) (tR : DualUse.rowL N K k ≤ T) (tnJ : nJ (N := N) hk ≤ T)
    (tC0 : c.d * (N * K) ≤ T) (tZ2 : (c.d - 2) * DualUse.rowL N K k ≤ T)
    (tR2 : 2 * DualUse.rowL N K k ≤ T) (tPAD : lenZ c - (lenKA hk c + N * K + 1) ≤ T)
    (tLΨ : lPsi (N := N) (K := K) hk ≤ T) (t10 : nA ≤ T) :
    Ph (preC hk c) (io2 (R := 254) a LF 0)
      (preTCv X Y T ((c.d - 2) * DualUse.rowL N K k + 2 * DualUse.rowL N K k) (nJ (N := N) hk)
        (lenZ c + DualUse.rowL N K k))
      (io2 (R := 254) (a + 1 + lenPK hk c + c.d * (N * K) +
        nA * ((c.d - 2) * DualUse.rowL N K k + 2 * DualUse.rowL N K k) +
        nJ (N := N) hk * (lenZ c + DualUse.rowL N K k) + lPsi (N := N) (K := K) hk + nA) LF 0) := by
  have h := ph_frame (eLo 21 eLo21) (β := io2 (R := 254) a LF 0)
    (T := preTCv X Y T ((c.d - 2) * DualUse.rowL N K k + 2 * DualUse.rowL N K k) (nJ (N := N) hk)
        (lenZ c + DualUse.rowL N K k))
    (p := preCoreC (lenPK hk c) (lenKA hk c) (lenPK hk c + lenKA hk c + lenCj (N := N) hk) (N * K + 1)
      (lenPK hk c + fixLen (keyEnc (N := N) (K := K) c)) (lPsi (N := N) (K := K) hk)
      (lenPK hk c + lenKA hk c) (lenCj (N := N) hk) (lenZ c) (DualUse.rowL N K k) (nJ (N := N) hk)
      (c.d * (N * K)) ((c.d - 2) * DualUse.rowL N K k) (2 * DualUse.rowL N K k)
      (lenZ c - (lenKA hk c + N * K + 1)))
    (by
      rw [io2_eLo_nat, ← vec21_eq]
      exact (ph_preCoreC' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a X Y T hX hoK hoP hoJ hL hA hNK hLΨ hLcj
        hTX tZ tR tnJ tC0 tZ2 tR2 tPAD tLΨ t10).mono le_rfl le_rfl (le_of_eq (vec21_eq _)))
  rw [embedF_eLo_nat] at h
  exact h

theorem wOut_eLo (j : Fin 65) :
    WB2.wOutS (eLo 65 eLo65 j) ≤ pcU 0 WB2.Lbn WB2.wOut2S j := by
  fin_cases j <;> simp [WB2.wOutS, pcU, eLo]

theorem cfOut_of (F0 F2 : ℕ) :
    embedF (eLo 65 eLo65) WB2.wOutS (pcF F0 F2) ≤ cfOut F0 F2 := fun t => by
  rcases embedF_cases (eLo 65 eLo65) WB2.wOutS (pcF F0 F2) t with ⟨hn, h⟩ | ⟨j, hj, h⟩ <;> rw [h]
  · have h0 : t.val ≠ 0 := fun e => by
      have : eLo 65 eLo65 0 = t := Fin.ext (by rw [eLo_val]; simp [e])
      rw [← this, partialInv_self] at hn; exact Option.some_ne_none _ hn
    have h2 : t.val ≠ 2 := fun e => by
      have : eLo 65 eLo65 1 = t := Fin.ext (by rw [eLo_val]; simp [e])
      rw [← this, partialInv_self] at hn; exact Option.some_ne_none _ hn
    simp [WB2.wOutS, cfOut, h0, h2, Fin.ext_iff]
  · subst hj
    clear h; fin_cases j <;> simp [pcF, cfOut, eLo]


/-- **The read-back, per tape**, from the per-tape output of the `W_f` block. -/
theorem ph_postC' (T : ℕ)
    (hTD : T ≤ WB2.Lbn) (hWD : WB2.wOut2S ≤ WB2.Lbn)
    (hW : WB2.wOut2S ≤ lenZ c + (1 * (2 * k) * N) * K) (hRZ : DualUse.rowL N K k ≤ lenZ c)
    (t1 : K ≤ T) (t2 : N ≤ T) (t3 : N * K ≤ T) (t4 : k ≤ T) (t5 : 2 * k * (N * K) ≤ T)
    (t6 : 1 * (2 * k) * N ≤ T) (t7 : lenZ c ≤ T) (t8 : nJ (N := N) hk ≤ T)
    (t9 : k * (N * K) ≤ T) :
    Ph (postC hk c) WB2.wOutS
      (postCT' (lenPK hk c) (lenKA hk c) (N * K) (offWk hk c)
        (nJ (N := N) hk * (lenZ c + DualUse.rowL N K k)) (lenZ c) N K k (lenZ c)
        (DualUse.rowL N K k) (nJ (N := N) hk) WB2.Lbn T)
      (cfOut (lenPK hk c + lenKA hk c + nJ (N := N) hk * DualUse.rowL N K k + N * K)
        ((1 * (2 * k) * N) * K)) :=
  (ph_frame (eLo 65 eLo65) ((ph_postCoreC' _ _ _ _ _ _ N K k _ _ _ WB2.Lbn T WB2.wOut2S hTD hWD hW hRZ
    t1 t2 t3 t4 t5 t6 t7 t8 t9).mono wOut_eLo le_rfl le_rfl)).mono le_rfl le_rfl (cfOut_of _ _)

end AdvancedEncryption.DualUse.Prog
