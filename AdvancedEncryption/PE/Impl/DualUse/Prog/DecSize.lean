import PE.Impl.DualUse.Prog.SizeCost
import PE.Impl.DualUse.Prog.DecTightConf

/-!
# The states of `Dec` and its description length at `confA`

Crude bounds on `XProg.size` (the states of the compiled machine) of the `c_f̂` block and of the
program of `Dec` (each read `getAt` is unrolled, so the bounds are linear in the largest offset or
length `X` read and in the bits `m` of the templates):

* `size_preCoreC`, `size_postCoreC` (65 tapes, the gadget row under `ifBit`), **`size_cfX_le`**;
* **`size_decGenF`**: the program of `Dec` for any front end;
* at `confA`: **`cfC_size_conf`** (`≤ 2^270`), **`size_decGenP_conf`**, and
  **`descLen_decMachineP_conf`**: the description length of the `Dec` machine of `implC`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg
open SigabaNeo.Tape.Prog (tailsP)
open AdvancedEncryption.PE.Gates.BPWord SigabaNeo.Lattices.Algo

set_option maxHeartbeats 2000000 in
theorem size_postCoreC (L A NK oW LW Zr N K k Z R nJ X m : ℕ) (h1 : L ≤ X) (h2 : A ≤ X)
    (h3 : oW + A + NK ≤ X) (h4 : NK ≤ X) (h5 : LW ≤ X) (h6 : Zr ≤ X) (h7 : nJ * R ≤ X)
    (h8 : k * (N * K) ≤ X) (h0 : 1 ≤ X) (ht : ∀ x ∈ postTmplC N K k Z R nJ, x.2 < 2 ^ m) :
    (postCoreC L A NK oW LW Zr N K k Z R nJ).size ≤ 2200 * X + 10 * (195 * m + 36) + 60000 := by
  have g1 := size_getAt 0 L X (by omega) h1 (0 : Fin 65) 2 4 5 6
  have g2 := size_getAt oW A X (by omega) h2 (0 : Fin 65) 3 4 5 6
  have g3 := size_getAt (oW + A) NK X (by omega) h4 (0 : Fin 65) 54 4 5 6
  have g3' := size_getAt (oW + A + NK) 1 X h3 (by omega) (0 : Fin 65) 64 4 5 6
  have g4 := size_getAt oW LW X (by omega) h5 (0 : Fin 65) 55 4 5 6
  have p1 := size_prefP (n := 65) L 2 0 4 5
  have p2 := size_prefP (n := 65) A 3 0 4 5
  have p3 := size_prefP (n := 65) (nJ * R) 56 0 4 5
  have p4 := size_prefP (n := 65) NK 54 0 4 5
  have p5 := size_prefP (n := 65) (k * (N * K)) 7 60 4 5
  have gt := size_tmplP_le (53 : Fin 65) m _ ht
  have hl : (postTmplC N K k Z R nJ).length = 10 := rfl
  rw [hl] at gt
  have c1 : (skipLoopP (56 : Fin 65) 55 62 63 59 57 58).size ≤ 1000 := by decide
  have c2 : (XProg.zerosP (60 : Fin 65) 63 61).size ≤ 1000 := by decide
  have c7 := size_clearL_le ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64] : List (Fin 65))
  have sg := size_gadP'
  have sa := size_addRWP'
  simp only [postCoreC, gadAddC, size_seq, size_prog, size_ifBit, Prog.size, Prim.pad, size_tailsP,
    Prog.size_map, List.length_cons, List.length_nil] at *
  omega

set_option maxHeartbeats 2000000 in
theorem size_preCoreC (L A oK NK oP LΨ oJ Lcj Z R nJ C0 Z2 R2 PAD X m : ℕ)
    (h1 : L ≤ X) (h2 : A ≤ X) (h3 : oK ≤ X) (h4 : NK ≤ X) (h5 : oP ≤ X) (h6 : LΨ ≤ X)
    (h7 : oJ ≤ X) (h8 : Lcj ≤ X) (ht : ∀ x ∈ preTmplC Z R nJ C0 Z2 R2 PAD LΨ, x.2 < 2 ^ m) :
    (preCoreC L A oK NK oP LΨ oJ Lcj Z R nJ C0 Z2 R2 PAD).size ≤
      1200 * X + 9 * (195 * m + 36) + 20000 := by
  have g1 := size_getAt 0 L X (by omega) h1 (0 : Fin 21) 1 4 5 6
  have g2 := size_getAt L A X h1 h2 (0 : Fin 21) 3 4 5 6
  have g3 := size_getAt oK NK X h3 h4 (0 : Fin 21) 3 4 5 6
  have g4 := size_getAt oP LΨ X h5 h6 (0 : Fin 21) 2 4 5 6
  have g5 := size_getAt oP LΨ X h5 h6 (0 : Fin 21) 18 4 5 6
  have g6 := size_getAt oJ Lcj X h7 h8 (0 : Fin 21) 2 4 5 6
  have gt := size_tmplP_le (17 : Fin 21) m _ ht
  have hl : (preTmplC Z R nJ C0 Z2 R2 PAD LΨ).length = 9 := rfl
  rw [hl] at gt
  have c1 : (XProg.zerosP (1 : Fin 21) 16 10).size ≤ 1000 := by decide
  have c2 : (XProg.zerosP (3 : Fin 21) 16 14).size ≤ 1000 := by decide
  have c3 : (XProg.zerosP (19 : Fin 21) 16 11).size ≤ 1000 := by decide
  have c4 : (wLoopP (1 : Fin 21) 2 19 15 16 13 11 12).size ≤ 1000 := by decide
  have c5 : (wLoopP (1 : Fin 21) 2 3 15 16 9 7 8).size ≤ 1000 := by decide
  have c6 : (XProg.moveP (1 : Fin 21) 18 16 20).size ≤ 1000 := by decide
  have c8 : (XProg.zerosP (1 : Fin 21) 16 13).size ≤ 1000 := by decide
  have c7 := size_clearL_le ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] :
    List (Fin 21))
  simp only [preCoreC, size_seq, size_prog, Prog.size, Prim.pad, List.length_cons,
    List.length_nil] at *
  omega

section Gen

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- **The states of the `c_f̂` block.** -/
theorem size_cfX_le (wfB : XProg 256) {X m : ℕ} (h1 : lenPK hk c ≤ X) (h2 : lenKA hk c ≤ X)
    (h3 : lenPK hk c + lenKA hk c + lenCj (N := N) hk ≤ X) (h4 : N * K + 1 ≤ X)
    (h5 : lenPK hk c + fixLen (keyEnc (N := N) (K := K) c) ≤ X) (h6 : lPsi (N := N) (K := K) hk ≤ X)
    (h7 : lenPK hk c + lenKA hk c ≤ X) (h8 : lenCj (N := N) hk ≤ X)
    (h9 : offWk hk c + lenKA hk c + N * K ≤ X)
    (h10 : nJ (N := N) hk * (lenZ c + DualUse.rowL N K k) ≤ X) (h11 : lenZ c ≤ X)
    (h12 : nJ (N := N) hk * DualUse.rowL N K k ≤ X) (h13 : k * (N * K) ≤ X)
    (hpre : ∀ x ∈ preTmplC (lenZ c) (DualUse.rowL N K k) (nJ (N := N) hk) (c.d * (N * K))
      ((c.d - 2) * DualUse.rowL N K k) (2 * DualUse.rowL N K k) (lenZ c - (lenKA hk c + N * K + 1))
      (lPsi (N := N) (K := K) hk), x.2 < 2 ^ m)
    (hpost : ∀ x ∈ postTmplC N K k (lenZ c) (DualUse.rowL N K k) (nJ (N := N) hk), x.2 < 2 ^ m) :
    (cfX hk c wfB).size ≤ 36 * 257 + 300 + (1200 * X + 9 * (195 * m + 36) + 20000) + wfB.size +
      (2200 * X + 10 * (195 * m + 36) + 60000) := by
  have a := size_preCoreC (lenPK hk c) (lenKA hk c) (lenPK hk c + lenKA hk c + lenCj (N := N) hk)
    (N * K + 1) (lenPK hk c + fixLen (keyEnc (N := N) (K := K) c)) (lPsi (N := N) (K := K) hk)
    (lenPK hk c + lenKA hk c) (lenCj (N := N) hk) (lenZ c) (DualUse.rowL N K k) (nJ (N := N) hk)
    (c.d * (N * K)) ((c.d - 2) * DualUse.rowL N K k) (2 * DualUse.rowL N K k)
    (lenZ c - (lenKA hk c + N * K + 1)) X m h1 h2 h3 h4 h5 h6 h7 h8 hpre
  have b := size_postCoreC (lenPK hk c) (lenKA hk c) (N * K) (offWk hk c)
    (nJ (N := N) hk * (lenZ c + DualUse.rowL N K k)) (lenZ c) N K k (lenZ c) (DualUse.rowL N K k)
    (nJ (N := N) hk) X m h1 h2 h9 (by omega) h10 h11 h12 h13 (by omega) hpost
  have c0 := size_clearL_le clr01
  have c1 := length_clr01_le
  have c2 : (XProg.prog mvBit).size ≤ 300 := by decide
  simp only [cfX, preC, postC, size_seq, size_frame] at *
  omega

set_option maxHeartbeats 2000000 in
/-- **The states of `Dec`'s program**, for any front end. -/
theorem size_decGenF {R : ℕ} (e : Fin (R + 2) ↪ Fin 256) (fr : XProg (R + 2)) (cfX : XProg 256)
    (B m : ℕ) (hB : ∀ x ∈ decOffs hk c, x ≤ B) (ht : ∀ x ∈ decTmpl c, x.2 < 2 ^ m) :
    (decGenF hk c e fr cfX).size ≤ 36 * nDec hk c + fr.size + cfX.size + 4000 * B +
      200 * K + 10 * (195 * m + 36) + 2 ^ 20 := by
  have hb := fun x (hx : x ∈ decOffs hk c) => hB x hx
  simp only [decOffs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := hb
  have h1 := size_leP (nDec hk c)
  have h2 := size_parse4P
  have g1 := size_getAt _ _ B b1 b2 (0 : Fin 256) 30 102 103 104
  have g2 := size_getAt _ _ B b3 b2 (0 : Fin 256) 31 102 103 104
  have g3 := size_getAt _ _ B b4 b5 (0 : Fin 256) 32 102 103 104
  have g4 := size_getAt _ _ B b6 b5 (0 : Fin 256) 33 102 103 104
  have g5 := size_getAt _ _ B b7 b8 (0 : Fin 256) 34 102 103 104
  have g6 := size_getAt _ _ B b9 b10 (0 : Fin 256) 35 102 103 104
  have w1 := size_putWX (4 : Fin 256) (Algo.decRadW K)
  have w2 : (Algo.decRadW K).length = K := SigabaNeo.Lattices.Algo.length_toBits _ _
  have gt := size_tmplP_le (120 : Fin 256) m _ ht
  have hl : (decTmpl c).length = 10 := rfl
  rw [hl] at gt
  have pK := size_prefP (n := 256) K 28 39 41 42
  have sdf : ProgKeyR.decFP.size ≤ 2 ^ 17 := by decide +kernel
  have sbl : SigabaNeo.Tape.Prog.ballP.size ≤ 2 ^ 14 := by decide +kernel
  have c2 := size_clearL_le clrAll
  have c3 := size_clearL_le ([0] : List (Fin 256))
  simp only [List.length_singleton] at c3
  have u1 := size_putWX (0 : Fin 256) [true, false, false]
  have u2 := size_putWX (0 : Fin 256) [true, true, false]
  simp only [List.length_cons, List.length_nil] at u1 u2
  have hA := length_clrAll_le
  rw [← getP_eq] at g1 g2 g3 g4 g5 g6
  simp only [decGenF, branchD, decFinB, dumDec, longB, size_seq, size_prog, size_frame,
    size_ifBit, size_ifBlank, Prog.size, Prim.pad, Prog.size_map, size_tailsP,
    List.length_singleton]
  omega

end Gen

/-! ### At `confA` -/

section Conf

open AdvancedEncryption.DualUse.Params AdvancedEncryption.DualUse.Sub

set_option maxRecDepth 100000
set_option exponentiation.threshold 2000

theorem preTmplC_conf : ∀ x ∈ preTmplC (lenZ confP) (DualUse.rowL Np Kp kp) (nJ (N := Np) (K := Kp) hkp)
    (confP.d * (Np * Kp)) ((confP.d - 2) * DualUse.rowL Np Kp kp) (2 * DualUse.rowL Np Kp kp)
    (lenZ confP - (lenKA hkp confP + Np * Kp + 1)) (lPsi (N := Np) (K := Kp) hkp), x.2 < 2 ^ 158 := by
  have h1 := lenZ_le
  have h2 := rowL_le
  have h3 := nJ_le
  have h4 : confP.d * (Np * Kp) ≤ 2 ^ 128 := by rw [dNK_conf]; norm_num
  have h5 : (confP.d - 2) * DualUse.rowL Np Kp kp ≤ 2 ^ 157 := by rw [confP_d, rowL_conf]; norm_num
  have h6 := lPsi_le
  have hn : nA = 128 := rfl
  intro x hx
  simp only [preTmplC, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

theorem postTmplC_lt : ∀ x ∈ postTmplC Np Kp kp (lenZ confP) (DualUse.rowL Np Kp kp)
    (nJ (N := Np) (K := Kp) hkp), x.2 < 2 ^ 158 := fun x hx =>
  lt_of_le_of_lt (postTmplC_conf x hx) (by norm_num)

/-- **The states of the `c_f̂` block of `implC`.** -/
theorem cfC_size_conf : cfC.size ≤ 2 ^ 270 := by
  have hPK := lenPK_le; have hKA := lenKA_le; have hCj := lenCj_le; have hNK := NK_le
  have hkE := fixLen_keyEnc_le; have hPs := lPsi_le; have hW := offWk_le; have hLW := LW_le
  have hZ := lenZ_le; have hk := kNK_le
  have hb := size_cfX_le hkp confP wfC (X := 2 ^ 258) (m := 158) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hLW (by omega)
    (by simp only [lenCj] at hCj; omega) (by omega) preTmplC_conf postTmplC_lt
  have hw := size_wfC
  rw [show cfC = cfX hkp confP wfC from rfl]
  generalize (cfX hkp confP wfC).size = S at hb ⊢
  generalize wfC.size = w at hb hw
  omega

/-- The arithmetic of the description length with the exact `Nat.size` of the state count. -/
theorem descLen_arith_size {k S B b : ℕ} (h : S ≤ B) (hb : S < 2 ^ b) :
    6 * S * 3 ^ k * 3 ^ 0 * Machine.entryBits k S 0 ≤ 6 * B * 3 ^ k * (4 + 4 * k + b) := by
  have hs : Nat.size S ≤ b := Nat.size_le.mpr hb
  unfold Machine.entryBits
  simp only [pow_zero, mul_one, Nat.mul_zero, Nat.add_zero, Nat.size_zero]
  gcongr

theorem dsz_arith {S n F b B K : ℕ}
    (hS : S ≤ 36 * n + F + b + 4000 * B + 200 * K + 10 * (195 * 67 + 36) + 2 ^ 20)
    (hb : b ≤ 2 ^ 270) (hn : n ≤ 2 ^ 195) (hF : F ≤ 36 * 2 ^ 49 + 2 ^ 56) (hB : B ≤ 2 ^ 194)
    (hK : K ≤ 2 ^ 27) : S + (n + 3) + 2 ≤ 2 ^ 270 + 2 ^ 208 := by
  omega

theorem decTmpl_lt67 : ∀ x ∈ decTmpl confP, x.2 < 2 ^ 67 := fun x hx =>
  lt_of_le_of_lt (decTmpl_conf (G := 2 ^ 66) le_rfl x hx) (by norm_num)

theorem size_frontBP_conf : (frontBP confP.L).size ≤ 36 * 2 ^ 49 + 2 ^ 56 := by
  have h1 := (frontSpec_frontBP confP.L).size
  have h2 := confP_L_le
  generalize (frontBP confP.L).size = F at h1 ⊢
  generalize confP.L = L at h1 h2
  omega

theorem decGenP_eqF : decGenP hkp confP cfC = decGenF hkp confP eF (frontBP confP.L) cfC := rfl

/-- **The states of the program of `Dec` in `implC`.** -/
theorem size_decGenP_conf : (decGenP hkp confP cfC).size + (nDec hkp confP + 3) + 2 ≤
    2 ^ 270 + 2 ^ 208 := by
  have hS := size_decGenF hkp confP eF (frontBP confP.L) cfC (2 ^ 194) 67 decOffs_conf decTmpl_lt67
  have hF := (frontSpec_frontBP confP.L).size
  have hL := confP_L_le
  have hK : Kp ≤ 2 ^ 27 := by rw [Kp_def]
  have hc := cfC_size_conf
  have hn := nDec_le
  rw [decGenP_eqF]
  omega

set_option exponentiation.threshold 2000 in
theorem dl_num_dec : 6 * (2 ^ 270 + 2 ^ 208) * 3 ^ 256 * (4 + 4 * 256 + 271) ≤ 2 ^ 689 := by
  norm_num

/-- **The description length of the `Dec` machine of `implC`**: at most `2^689` (the state count
`≤ 2^270 + 2^208`, linear in the SimData length through the unrolled reads of the `c_f̂` block;
`256` tapes; `Nat.size` of the state count `≤ 271` in the entry width). -/
theorem descLen_decMachineP_conf : (decMachineP hkp confP cfC).descLen ≤ 2 ^ 689 := by
  rw [descLen_decMachineP]
  have h := size_decGenP_conf
  exact (descLen_arith_size h (lt_of_le_of_lt h (by norm_num))).trans dl_num_dec

/-- **The description length of the `Dec` machine of `implC`** (`msC.dec`). -/
theorem descLen_dec_msC : msC.dec.descLen ≤ 2 ^ 689 := descLen_decMachineP_conf

end Conf

end AdvancedEncryption.DualUse.Prog
