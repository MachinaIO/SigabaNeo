import PE.Impl.DualUse.Prog.Pub5

/-!
# State counts for templates below `2^260`

The state counts of the blocks (`Blocks.lean`: `sz_natP`, `sz_getB`, …) and of the bodies of the
public-key and simulation-data components (`sz_pub3Body`, `sz_sd3Body`, …) assume templates below
`2^240` (a counter of `n < 2^240` has at most `46836` states). At `confA` the offsets of the
simulation data reach `2^257`; here the same counts for templates below `2^260` (at most
`195 · 260 + 36 = 50736` states per counter), with the same proofs (`…W`).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.XProg Matrix AdvancedEncryption.RingBTVW
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord

section Blocks

variable {k : ℕ}

theorem sz_natPW {t c : Fin k} {n M : ℕ} (hn : n ≤ M) (hB : M < 2 ^ 260) :
    SZ (natP t c n) 50736 :=
  (size_natP_le t c n 260 (by omega)).trans (by norm_num)

theorem sz_trBW (m r s B Z M : ℕ) (hM : sizeTrB m r s B Z ≤ M) (hB : M < 2 ^ 260) :
    SZ (trB m r s B Z) (6 * 50736 + 2 ^ 12 + 36 * 20) := by
  unfold sizeTrB at hM
  exact ((sz_natPW (by omega) hB).seq <| (sz_natPW (by omega) hB).seq <| (sz_natPW (by omega) hB).seq <|
    (sz_natPW (by omega) hB).seq <| (sz_natPW (by omega) hB).seq <| (sz_natPW (by omega) hB).seq <|
    (sz_leaf size_trP).seq (sz_clearL _)).mono (by simp [scrFrom]; rfl)

theorem sz_selBW (n B M : ℕ) (hM : sizeSelB n B ≤ M) (hB : M < 2 ^ 260) :
    SZ (selB n B) (3 * 50736 + 2 ^ 12 + 36 * 11) := by
  unfold sizeSelB at hM
  exact ((sz_natPW (by omega) hB).seq <| (sz_natPW (by omega) hB).seq <| (sz_natPW (by omega) hB).seq <|
    (sz_leaf size_bitSelP).seq (sz_clearL _)).mono (by simp [scrFrom]; rfl)

theorem sz_hashBW (P d N K M : ℕ) (hM : sizeHashB P d N K ≤ M) (hB : M < 2 ^ 260) :
    SZ (hashB P d N K) (6 * 50736 + 2 ^ 14 + 36 * 43) := by
  unfold sizeHashB at hM
  exact ((sz_natPW (by omega) hB).seq <| (sz_natPW (by omega) hB).seq <| (sz_natPW (by omega) hB).seq <|
    (sz_natPW (by omega) hB).seq <| (sz_natPW (by omega) hB).seq <| (sz_natPW (by omega) hB).seq <|
    (sz_leaf size_hashP).seq (sz_clearL _)).mono (by simp [scrFrom]; rfl)

theorem sz_mmBW (m n l N K M : ℕ) (hM : sizeMmB m n l N K ≤ M) (hB : M < 2 ^ 260) :
    SZ (mmB m n l N K) (7 * 50736 + 2 ^ 16 + 36 * 58) := by
  unfold sizeMmB at hM
  exact ((sz_natPW (by omega) hB).seq <| (sz_natPW (by omega) hB).seq <| (sz_natPW (by omega) hB).seq <|
    (sz_natPW (by omega) hB).seq <| (sz_natPW (by omega) hB).seq <| (sz_natPW (by omega) hB).seq <|
    (sz_natPW (by omega) hB).seq <| (sz_leaf size_matMulP).seq (sz_clearL _)).mono
    (by simp [scrFrom]; rfl)

theorem sz_addBW (L N K M : ℕ) (hM : sizeAddB L N K ≤ M) (hB : M < 2 ^ 260) :
    SZ (addB L N K) (2 * 50736 + 2 ^ 12 + 36 * 27) := by
  unfold sizeAddB at hM
  exact ((sz_natPW (by omega) hB).seq <| (sz_natPW (by omega) hB).seq <|
    (sz_leaf size_addRWP).seq (sz_clearL _)).mono (by simp [scrFrom]; rfl)

theorem sz_subBW (L N K M : ℕ) (hM : sizeAddB L N K ≤ M) (hB : M < 2 ^ 260) :
    SZ (subB L N K) (2 * 50736 + 2 ^ 12 + 36 * 27) := by
  unfold sizeAddB at hM
  exact ((sz_natPW (by omega) hB).seq <| (sz_natPW (by omega) hB).seq <|
    (sz_leaf size_subRWP).seq (sz_clearL _)).mono (by simp [scrFrom]; rfl)

theorem sz_getBW (o L M : ℕ) (hM : o + L ≤ M) (hB : M < 2 ^ 260) :
    SZ (getB o L) (2 * 50736 + 2 ^ 12 + 36 * 10) := by
  exact ((sz_natPW (by omega) hB).seq <| (sz_natPW (by omega) hB).seq <|
    (sz_leaf size_splitP).seq (sz_clearL _)).mono (by simp [scrFrom]; rfl)

theorem sz_joinBW (a b c M : ℕ) (hM : a + b + c ≤ M) (hB : M < 2 ^ 260) :
    SZ (joinB a b c) (4 * 50736 + 2 ^ 12 + 36 * 9) := by
  exact ((sz_natPW (by omega) hB).seq <| (sz_natPW (by omega) hB).seq <| (sz_natPW (by omega) hB).seq <|
    (sz_natPW (by omega) hB).seq <| (sz_leaf size_joinP).seq (sz_clearL _)).mono
    (by simp [scrFrom]; rfl)

theorem sz_gadBW (N K k M : ℕ) (hM : sizeGadB N K k ≤ M) (hB : M < 2 ^ 260) :
    SZ (gadB N K k) (5 * 50736 + 2 ^ 14 + 36 * 22) := by
  unfold sizeGadB at hM
  exact ((sz_natPW (by omega) hB).seq <| (sz_natPW (by omega) hB).seq <| (sz_natPW (by omega) hB).seq <|
    (sz_natPW (by omega) hB).seq <| (sz_natPW (by omega) hB).seq <|
    (sz_leaf size_gadP).seq (sz_clearL _)).mono (by simp [scrFrom]; rfl)

theorem sz_oneBW (N K M : ℕ) (hM : N * K ≤ M) (hB : M < 2 ^ 260) : SZ (oneB N K) (50736 + 120) :=
  ((sz_natPW (by omega) hB).seq ((sz_prim _).seq (sz_prim _))).mono (by norm_num)

end Blocks

theorem sz_psiCoreW (N K k d M : ℕ) (hM : sizePsiCore N K k d ≤ M) (hB : M < 2 ^ 260) :
    SZ (psiCore N K k d) (2 ^ 21) := by
  unfold sizePsiCore at hM
  exact ((SZ.frame _ (sz_joinBW _ _ _ M (by omega) hB)).seq <|
    (SZ.frame _ (sz_trBW _ _ _ _ _ M (by omega) hB)).seq <|
    (SZ.frame _ (sz_mmBW _ _ _ _ _ M (by omega) hB)).seq <|
    (SZ.frame _ (sz_trBW _ _ _ _ _ M (by omega) hB)).seq <|
    (SZ.frame _ (sz_gadBW _ _ _ M (by omega) hB)).seq <|
    (sz_prim _).seq <|
    (SZ.frame _ (sz_joinBW _ _ _ M (by omega) hB)).seq <|
    (SZ.frame _ (sz_selBW _ _ M (by omega) hB)).seq <|
    (SZ.frame _ (sz_addBW _ _ _ M (by omega) hB)).seq <|
    (sz_prim _).seq <| (sz_prim _).seq <| (sz_prim _).seq <| sz_prim _).mono (by norm_num)

theorem sz_bjCoreW (N K k d M : ℕ) (hM : sizeBjCore N K k d ≤ M) (hB : M < 2 ^ 260) :
    SZ (bjCore N K k d) (2 ^ 21) := by
  unfold sizeBjCore at hM
  exact ((SZ.frame _ (sz_trBW _ _ _ _ _ M (by omega) hB)).seq <|
    (SZ.frame _ (sz_gadBW _ _ _ M (by omega) hB)).seq <|
    (SZ.frame _ (sz_selBW _ _ M (by omega) hB)).seq <|
    (SZ.frame _ (sz_hashBW _ _ _ _ M (by omega) hB)).seq <|
    (sz_prim _).seq <| (sz_prim _).seq <| sz_prim _).mono (by norm_num)

section Comps

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

theorem sz_pub3BodyW (M : ℕ) (hM : sizepub3 hk c ≤ M) (hB : M < 2 ^ 260) :
    SZ (pub3Body hk c) (2 ^ 24) := by
  unfold sizepub3 at hM
  exact ((SZ.frame _ (sz_getBW (o3B (N := N) (K := K) (k := k)) (fD N K c.d) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getBW (o3s hk c) (fR N K) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getBW (o3e0 hk c) (fD N K c.d) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_mmBW (1) (1) (c.d) N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_addBW (1 * c.d) N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getBW (o3R hk c) (fencLen (rmTEnc c)) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getBW (o3x (N := N) (K := K) (k := k)) (fencLen attrEnc) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getBW (o3w c) (fencLen (wEnc hk c)) M (by omega) hB)).seq <|
    (sz_psiCoreW N K k c.d M (by omega) hB).seq <|
    (sz_bjCoreW N K k c.d M (by omega) hB).seq <|
    (SZ.frame _ (sz_getBW (0) (fC N K k) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getBW (fC N K k + 0) (fC N K k) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_gadBW N K k M (by omega) hB)).seq <|
    (SZ.frame _ (sz_subBW (1 * (2 * k)) N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_oneBW N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_joinBW (N * K) (rowL N K k) (rowL N K k) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getBW (o3p hk c) (fR N K) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_joinBW (fD N K c.d) (fT N K k) (fJ (N := N) hk) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_joinBW (fD N K c.d + fT N K k + fJ (N := N) hk) (fR N K) (0) M (by omega) hB))).mono (by norm_num)

theorem sz_sdTailBodyW (M : ℕ) (hM : sizesdTail hk c ≤ M) (hB : M < 2 ^ 260) :
    SZ (sdTailBody hk c) (2 ^ 22) := by
  unfold sizesdTail at hM
  exact ((SZ.frame _ (sz_trBW (nA) (2 * k) (c.d) (N * K) (0) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_trBW (P1 N k) (2 * k) (c.d) (1) (0) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_oneBW N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_selBW (P1 N k * (c.d * (2 * k))) (N * K) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_joinBW (fencLen (rmEnc c)) (fWm (N := N) hk c) (fPsi N K k) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_joinBW (fD N K c.d) (fencLen (rmEnc c) + fWm (N := N) hk c + fPsi N K k) (fencLen attrEnc) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_joinBW (fencLen (pkEnc hk c)) (fD N K c.d + (fencLen (rmEnc c) + fWm (N := N) hk c + fPsi N K k) + fencLen attrEnc) (0) M (by omega) hB))).mono (by norm_num)

theorem sz_sd3BodyW (M : ℕ) (hM : sizeSd3 hk c ≤ M) (hB : M < 2 ^ 260) :
    SZ (seq (pub3Body hk c) (sdTailBody hk c)) (2 ^ 24 + 2 ^ 22) :=
  ((sz_pub3BodyW hk c M (by unfold sizeSd3 at hM; omega) hB).seq
    (sz_sdTailBodyW hk c M (by unfold sizeSd3 at hM; omega) hB)).mono (by norm_num)

theorem sz_pub5BodyW (M : ℕ) (hM : sizepub5 hk c ≤ M) (hB : M < 2 ^ 260) :
    SZ (pub5Body hk c) (2 ^ 24) := by
  unfold sizepub5 at hM
  exact ((SZ.frame _ (sz_getBW (0) (fD N K c.d) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getBW (o5u c) (fR N K) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getBW (o5v c) (fD N K c.d) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_mmBW (1) (1) (c.d) N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_addBW (1 * c.d) N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getBW (o5R hk c) (fencLen (rmTEnc c)) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getBW (o5x c) (fencLen attrEnc) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getBW (o5w c) (fencLen (wEnc hk c)) M (by omega) hB)).seq <|
    (sz_psiCoreW N K k c.d M (by omega) hB).seq <|
    (sz_bjCoreW N K k c.d M (by omega) hB).seq <|
    (SZ.frame _ (sz_getBW (o5a c) (fC N K k) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getBW (o5z c) (fC N K k) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_oneBW N K M (by omega) hB)).seq <|
    (SZ.frame _ (sz_joinBW (N * K) (rowL N K k) (rowL N K k) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_getBW (o5p c) (fR N K) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_joinBW (fD N K c.d) (fT N K k) (fJ (N := N) hk) M (by omega) hB)).seq <|
    (SZ.frame _ (sz_joinBW (fD N K c.d + fT N K k + fJ (N := N) hk) (fR N K) (0) M (by omega) hB))).mono (by norm_num)

theorem sz_sd5BodyW (M : ℕ) (hM : sizeSd5 hk c ≤ M) (hB : M < 2 ^ 260) :
    SZ (seq (pub5Body hk c) (sdTailBody hk c)) (2 ^ 24 + 2 ^ 22) :=
  ((sz_pub5BodyW hk c M (by unfold sizeSd5 at hM; omega) hB).seq
    (sz_sdTailBodyW hk c M (by unfold sizeSd5 at hM; omega) hB)).mono (by norm_num)

end Comps

end AdvancedEncryption.DualUse.Prog
