import PE.Impl.DualUse.Prog.BlockCost
import PE.Impl.DualUse.Prog.KeyGenCost
import PE.Impl.DualUse.Prog.DecGenCost

/-!
# The number of states of the blocks

Crude bounds on `XProg.size` (the states of the compiled machine) of the crafted-data blocks, in
terms of the largest offset or length `X` they read (each read is unrolled) and the number `m` of
bits of their templates.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg
open SigabaNeo.Tape.Prog (tailsP)
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord SigabaNeo.Lattices.Algo

theorem size_tailsP {k : ℕ} (i : Fin k) : ∀ n, (tailsP i n).size = 36 * (n + 1)
  | 0 => by simp [tailsP, Prog.size, Prim.pad]
  | n + 1 => by
    rw [tailsP, Prog.size, size_tailsP i n]
    simp [Prog.size, Prim.pad]; ring

theorem size_getAt {k : ℕ} (o L X : ℕ) (ho : o ≤ X) (hL : L ≤ X) (src dst tmp a b : Fin k) :
    (getAt o L src dst tmp a b).size ≤ 200 * X + 400 := by
  have := size_prefP (n := k) L tmp dst a b
  simp only [getAt, size_seq, size_prog, Prog.size, size_tailsP, Prim.pad] at *
  omega

theorem size_preCoreB (L LT oB nTR Z R nT C0 RM0 PS0 PAD X m : ℕ)
    (h1 : L ≤ X) (h2 : LT ≤ X) (h3 : oB ≤ X) (h4 : nTR ≤ X)
    (ht : ∀ x ∈ preTmpl Z R nT C0 RM0 PS0 PAD, x.2 < 2 ^ m) :
    (preCoreB L LT oB nTR Z R nT C0 RM0 PS0 PAD).size ≤ 600 * X + 8 * (195 * m + 36) + 10000 := by
  have g1 := size_getAt 0 L X (by omega) h1 (0 : Fin 18) 1 4 5 6
  have g2 := size_getAt L LT X h1 h2 (0 : Fin 18) 3 4 5 6
  have g3 := size_getAt oB nTR X h3 h4 (0 : Fin 18) 2 4 5 6
  have g4 := size_tmplP_le (17 : Fin 18) m _ ht
  have hl : (preTmpl Z R nT C0 RM0 PS0 PAD).length = 8 := rfl
  rw [hl] at g4
  have c1 : (XProg.zerosP (1 : Fin 18) 16 10).size ≤ 1000 := by decide
  have c2 : (XProg.zerosP (1 : Fin 18) 16 11).size ≤ 1000 := by decide
  have c3 : (XProg.zerosP (3 : Fin 18) 16 14).size ≤ 1000 := by decide
  have c4 : (wLoopP (1 : Fin 18) 2 3 15 16 9 7 8).size ≤ 1000 := by decide
  have c5 : (XProg.zerosP (1 : Fin 18) 16 12).size ≤ 1000 := by decide
  have c6 : (XProg.zerosP (1 : Fin 18) 16 13).size ≤ 1000 := by decide
  have c7 := size_clearL_le ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] : List (Fin 18))
  simp only [preCoreB, size_seq, size_prog, Prog.size, Prim.pad, List.length_cons,
    List.length_nil] at *
  omega

theorem size_gadP' : Prog.gadP.size ≤ 20000 := by decide +kernel
theorem size_addRWP' : Prog.addRWP.size ≤ 5000 := by decide +kernel

set_option maxHeartbeats 2000000 in
theorem size_postCoreB (L LT oW Zr N K k X m : ℕ) (h1 : L ≤ X) (h2 : LT ≤ X) (h3 : oW ≤ X)
    (h4 : Zr ≤ X) (ht : ∀ x ∈ postTmpl N K k, x.2 < 2 ^ m) :
    (postCoreB L LT oW Zr N K k).size ≤ 1000 * X + 6 * (195 * m + 36) + 40000 := by
  have g1 := size_getAt 0 L X (by omega) h1 (0 : Fin 54) 2 4 5 6
  have g2 := size_getAt oW LT X h3 h2 (0 : Fin 54) 3 4 5 6
  have p1 := size_prefP (n := 54) L 2 0 4 5
  have p2 := size_prefP (n := 54) LT 3 0 4 5
  have g4 := size_tmplP_le (53 : Fin 54) m _ ht
  have hl : (postTmpl N K k).length = 6 := rfl
  rw [hl] at g4
  have c7 := size_clearL_le ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53] : List (Fin 54))
  have sg := size_gadP'
  have sa := size_addRWP'
  simp only [postCoreB, size_seq, size_prog, Prog.size, Prim.pad, size_tailsP, Prog.size_map,
    List.length_cons, List.length_nil] at *
  omega

set_option maxHeartbeats 2000000 in
theorem size_postCoreC (L A NK oW LW Zr N K k Z R nJ X m : ℕ) (h1 : L ≤ X) (h2 : A ≤ X)
    (h3 : oW + A ≤ X) (h4 : NK ≤ X) (h5 : LW ≤ X) (h6 : Zr ≤ X) (h7 : nJ * R ≤ X)
    (h8 : k * (N * K) ≤ X) (ht : ∀ x ∈ postTmplC N K k Z R nJ, x.2 < 2 ^ m) :
    (postCoreC L A NK oW LW Zr N K k Z R nJ).size ≤ 2000 * X + 10 * (195 * m + 36) + 60000 := by
  have g1 := size_getAt 0 L X (by omega) h1 (0 : Fin 64) 2 4 5 6
  have g2 := size_getAt oW A X (by omega) h2 (0 : Fin 64) 3 4 5 6
  have g3 := size_getAt (oW + A) NK X h3 h4 (0 : Fin 64) 54 4 5 6
  have g4 := size_getAt oW LW X (by omega) h5 (0 : Fin 64) 55 4 5 6
  have p1 := size_prefP (n := 64) L 2 0 4 5
  have p2 := size_prefP (n := 64) A 3 0 4 5
  have p3 := size_prefP (n := 64) (nJ * R) 56 0 4 5
  have p4 := size_prefP (n := 64) NK 54 0 4 5
  have p5 := size_prefP (n := 64) (k * (N * K)) 7 60 4 5
  have gt := size_tmplP_le (53 : Fin 64) m _ ht
  have hl : (postTmplC N K k Z R nJ).length = 10 := rfl
  rw [hl] at gt
  have c1 : (skipLoopP (56 : Fin 64) 55 62 63 59 57 58).size ≤ 1000 := by decide
  have c2 : (XProg.zerosP (60 : Fin 64) 63 61).size ≤ 1000 := by decide
  have c7 := size_clearL_le ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63] : List (Fin 64))
  have sg := size_gadP'
  have sa := size_addRWP'
  simp only [postCoreC, size_seq, size_prog, Prog.size, Prim.pad, size_tailsP, Prog.size_map,
    List.length_cons, List.length_nil] at *
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

/-! ### The programs of `KeyGen` and `Dec` -/

theorem size_leP (n : ℕ) : (SigabaNeo.Tape.Prog.leP n).size ≤ 36 * n + 400 := by
  simp only [SigabaNeo.Tape.Prog.leP, Prog.size, Prim.pad, size_tailsP]; omega

theorem size_unfrP : SigabaNeo.Tape.Prog.unfrP.size ≤ 1000 := by decide +kernel
theorem size_frP : SigabaNeo.Tape.Prog.frP.size ≤ 1000 := by decide +kernel
set_option maxRecDepth 100000 in
theorem size_keyTryR : ProgKeyR.keyTryRCoinsP.size ≤ 2 ^ 20 := by decide +kernel

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

theorem size_parseP : parseP.size ≤ 4000 := by
  have := size_unfrP
  simp only [parseP, Prog.size, Prim.pad, Prog.size_map] at *; omega

theorem size_parse4P : parse4P.size ≤ 5000 := by
  have := size_unfrP
  simp only [parse4P, Prog.size, Prim.pad, Prog.size_map] at *; omega

set_option maxHeartbeats 2000000 in
/-- **The states of `KeyGen`'s program.** -/
theorem size_keyGenP (bfX : XProg 256) (W : ℕ) (cf : KeyCfg) (m : ℕ)
    (ht : ∀ x ∈ keyTmplR hk c cf, x.2 < 2 ^ m) :
    (keyGenP hk c bfX W cf).size ≤ 36 * nKG hk c + (frontP c.L W).size + bfX.size +
      400 * (lenPK hk c + 2 * k * (N * K)) + 60 * (cf.sW.length + (powW K (cf.B - 1)).length +
        ((keyEnc (N := N) (K := K) c).enc (dummyKey c)).length) + 23 * (195 * m + 36) + 2 ^ 21 := by
  have h1 := size_leP (nKG hk c)
  have h2 := size_parseP
  have h3 := size_frP
  have h4 := size_keyTryR
  have p1 := size_prefP (n := 256) (lenPK hk c) 0 1 100 101
  have p2 := size_prefP (n := 256) (2 * k * (N * K)) 102 90 103 104
  have p3 := size_prefP (n := 256) (lenPK hk c) 0 2 100 101
  have w1 := size_putWX (4 : Fin 256) cf.sW
  have w2 := size_putWX (5 : Fin 256) (powW K (cf.B - 1))
  have w3 := size_putWX (2 : Fin 256) ((keyEnc (N := N) (K := K) c).enc (dummyKey c))
  have gt := size_tmplP_le (120 : Fin 256) m _ ht
  have hl : (keyTmplR hk c cf).length = 23 := rfl
  rw [hl] at gt
  have c1 := size_clearL_le keyClrR
  have c2 := size_clearL_le clrAll
  have c3 := size_clearL_le ([0] : List (Fin 256))
  have hA := length_clrAll_le
  have hc : keyClrR.length = 31 := rfl
  rw [hc] at c1
  simp only [keyGenP, keyGenF, branchK, winR, dumR, dumB, longB, etP, size_seq, size_prog, size_frame,
    size_ifBit, size_ifBlank, Prog.size, Prim.pad, Prog.size_map, size_tailsP,
    List.length_singleton] at *
  omega

set_option maxHeartbeats 2000000 in
/-- **The states of `Dec`'s program.** -/
theorem size_decGenP (cfX : XProg 256) (W : ℕ) (B m : ℕ) (hB : ∀ x ∈ decOffs hk c, x ≤ B)
    (ht : ∀ x ∈ decTmpl c, x.2 < 2 ^ m) :
    (decGenP hk c cfX W).size ≤ 36 * nDec hk c + (frontP c.L W).size + cfX.size + 4000 * B +
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
  simp only [decGenP, decGenF, branchD, decFinB, dumDec, longB, size_seq, size_prog, size_frame,
    size_ifBit, size_ifBlank, Prog.size, Prim.pad, Prog.size_map, size_tailsP,
    List.length_singleton]
  omega

end AdvancedEncryption.DualUse.Prog
