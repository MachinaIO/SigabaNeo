import PE.Impl.DualUse.Prog.BlockCost
import PE.Impl.DualUse.Prog.KeyGenCost
import PE.Impl.DualUse.Prog.DecGenCost

/-!
# The number of states of the blocks

Crude bounds on `XProg.size` (the states of the compiled machine) of the crafted-data blocks of
`KeyGen`, in terms of the largest offset or length `X` they read (each read is unrolled) and the
number `m` of bits of their templates, and of `KeyGen`'s program for any front end
(`size_keyGenF`). The generic helpers (`size_tailsP`, `size_getAt`, `size_leP`, `size_parse4P`, …)
are shared with `Dec` (`DecSize`).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg
open SigabaNeo.Tape.Prog (tailsP)
open AdvancedEncryption.PE.Gates.BPWord SigabaNeo.Lattices.Algo

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
theorem size_postCoreB (L LT oW Zr N K k X m : ℕ) (h1 : L ≤ X) (h2 : LT ≤ X) (h3 : oW + LT ≤ X)
    (h4 : Zr ≤ X) (h5 : 1 ≤ X) (ht : ∀ x ∈ postTmpl N K k, x.2 < 2 ^ m) :
    (postCoreB L LT oW Zr N K k).size ≤ 1200 * X + 6 * (195 * m + 36) + 40000 := by
  have g1 := size_getAt 0 L X (by omega) h1 (0 : Fin 55) 2 4 5 6
  have g2 := size_getAt oW LT X (by omega) h2 (0 : Fin 55) 3 4 5 6
  have g3 := size_getAt (oW + LT) 1 X h3 (by omega) (0 : Fin 55) 54 4 5 6
  have p1 := size_prefP (n := 55) L 2 0 4 5
  have p2 := size_prefP (n := 55) LT 3 0 4 5
  have g4 := size_tmplP_le (53 : Fin 55) m _ ht
  have hl : (postTmpl N K k).length = 6 := rfl
  rw [hl] at g4
  have c7 := size_clearL_le ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List (Fin 55))
  have sg := size_gadP'
  have sa := size_addRWP'
  simp only [postCoreB, gadAddP, size_seq, size_prog, Prog.size, Prim.pad, size_tailsP, Prog.size_map,
    List.length_cons, List.length_nil] at *
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
/-- **The states of `KeyGen`'s program**, for any front end `fr` framed by `e`. -/
theorem size_keyGenF {R : ℕ} (e : Fin (R + 2) ↪ Fin 256) (fr : XProg (R + 2)) (bfX : XProg 256)
    (W : ℕ) (cf : KeyCfg) (m : ℕ) (ht : ∀ x ∈ keyTmplR hk c cf, x.2 < 2 ^ m) :
    (keyGenF hk c e fr bfX W cf).size ≤ 36 * nKG hk c + fr.size + bfX.size +
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
  simp only [keyGenF, branchK, winR, dumR, dumB, longB, etP, size_seq, size_prog, size_frame,
    size_ifBit, size_ifBlank, Prog.size, Prim.pad, Prog.size_map, size_tailsP,
    List.length_singleton] at *
  omega

end AdvancedEncryption.DualUse.Prog
