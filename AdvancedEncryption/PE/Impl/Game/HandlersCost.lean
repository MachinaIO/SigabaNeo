import PE.Impl.Game.HandlersMain

/-!
# The clock of the handlers

An explicit bound on `handlerTime` (`handlerTime_le`), affine in the query bound `T`:

  `handlerTime ≤ N · (2 (M + N) + 5) + compTime + 20`

with `N = 10 nA + 11 nM + 40` (the glue primitives of one handler), `M = T + stateBound + Ssig +
Lp + Lk + La + Lc + nA + nM + 2` (a bound on every glue tape between the steps), and `compTime`
the per-tape time bounds of the components at their input bounds:

* `setupP` at `(stateBound, nA)`, `pubP` at `(Ssig, 0)`, `keyP` at `(sigBound, T)`,
  `authP` at `(T, nA)`, `chalP` at `(sigBound, nM)`, where `sigBound = stateBound - (nM + nA + 3)`.

The components' output bounds `Ssig`, `Lp`, `Lk`, `La`, `Lc` are hypotheses on their per-tape
length bounds (`CompBounds`): every other tape of a component ends with the bound `0` (a component
clears its scratch tapes).
-/

namespace AdvancedEncryption.PE.Generic

open SigabaNeo SigabaNeo.Tape Cslib

variable {U : Universe} {Sig : Type} {R : ℕ}

/-- The bound on the secret word after parsing a selected state. -/
def sigBound (cd : Codes U Sig) (W : ℕ) : ℕ := stateBound cd W - (cd.nM + cd.nA + 3)

variable {cd : Codes U Sig} {sp : Spec U Sig} {setupW : List Bool → U.Attr → PMF Sig}
  {IW : List Bool → Prop} {Ok : Sig → Prop}

/-- The per-tape length bounds of the components' outputs. -/
structure CompBounds (cs : Comps R cd sp setupW IW Ok) (T W : ℕ) where
  /-- The secret word. -/
  Ssig : ℕ
  /-- The public key. -/
  Lp : ℕ
  /-- The answer to a key query. -/
  Lk : ℕ
  /-- The authorization word. -/
  La : ℕ
  /-- The challenge. -/
  Lc : ℕ
  len_setup : XProg.lenBoundT cs.setupP (io2 (stateBound cd W) cd.nA 0) ≤ io2 Ssig 0 0
  len_pub : XProg.lenBoundT cs.pubP (io2 Ssig 0 0) ≤ io2 Lp 0 0
  len_key : XProg.lenBoundT cs.keyP (io2 (sigBound cd W) T 0) ≤ io2 Lk 0 0
  len_auth : XProg.lenBoundT cs.authP (io2 T cd.nA 0) ≤ io2 La 0 0
  len_chal : XProg.lenBoundT cs.chalP (io2 (sigBound cd W) cd.nM 0) ≤ io2 Lc 0 0

variable (cd) in
/-- The glue primitives of one handler. -/
def glueN : ℕ := 10 * cd.nA + 11 * cd.nM + 40

/-- A bound on every glue tape between the steps of a handler. -/
def glueM {cs : Comps R cd sp setupW IW Ok} {T W : ℕ} (cb : CompBounds cs T W) : ℕ :=
  T + stateBound cd W + cb.Ssig + cb.Lp + cb.Lk + cb.La + cb.Lc + cd.nA + cd.nM + 2

/-- The time of the components at their input bounds. -/
def compTime {cs : Comps R cd sp setupW IW Ok} {T W : ℕ} (cb : CompBounds cs T W) : ℕ :=
  XProg.timeBoundT cs.setupP (io2 (stateBound cd W) cd.nA 0) +
    XProg.timeBoundT cs.pubP (io2 cb.Ssig 0 0) +
    XProg.timeBoundT cs.keyP (io2 (sigBound cd W) T 0) +
    XProg.timeBoundT cs.authP (io2 T cd.nA 0) +
    XProg.timeBoundT cs.chalP (io2 (sigBound cd W) cd.nM 0)

/-! ### Glue pieces -/

/-- A glue piece within the bound `M` on every tape costs at most `pcount · c`. -/
theorem glue_time_le (P : Prog 8) (hP : P.LoopFree) (u : Fin 8 → ℕ) {M N : ℕ}
    (hM : ∀ t, u t ≤ M) (hN : P.pcount ≤ N) :
    P.timeBoundT u ≤ P.pcount * (2 * (M + N) + 5) :=
  (Prog.timeBoundT_le_pcount P hP u hM).trans (Nat.mul_le_mul_left _ (by omega))

theorem TT.glueB (P : Prog 8) (hP : P.LoopFree) (u : Fin 8 → ℕ) {M N : ℕ}
    (hM : ∀ t, u t ≤ M) (hN : P.pcount ≤ N) :
    TT (glue (R := R) P) u (P.pcount * (2 * (M + N) + 5)) :=
  (TT.glue' P u).mono (glue_time_le P hP u hM hN)

theorem TT.seq_glueB {q : XProg (R + 8)} {u : Fin 8 → ℕ} {t : ℕ} (P : Prog 8) (hP : P.LoopFree)
    {M N : ℕ} (hM : ∀ t, u t ≤ M) (hN : P.pcount ≤ N) (h : TT q (P.lenBoundT u) t) :
    TT (.seq (glue P) q) u (P.pcount * (2 * (M + N) + 5) + t) :=
  (TT.seq_glue P h).mono (Nat.add_le_add_right (glue_time_le P hP u hM hN) _)

theorem TT.seq_ifBit_glueB {r : XProg (R + 8)} {u : Fin 8 → ℕ} {t : ℕ} (i : Fin (R + 8))
    (P₁ P₂ : Prog 8) (h1 : P₁.LoopFree) (h2 : P₂.LoopFree) {M N : ℕ} (hM : ∀ t, u t ≤ M)
    (hN1 : P₁.pcount ≤ N) (hN2 : P₂.pcount ≤ N) (h : TT r (P₁.lenBoundT u ⊔ P₂.lenBoundT u) t) :
    TT (.seq (.ifBit i (glue P₁) (glue P₂)) r) u
      (P₁.pcount * (2 * (M + N) + 5) + P₂.pcount * (2 * (M + N) + 5) + 1 + t) := by
  refine (TT.seq_ifBit_glue i P₁ P₂ h).mono ?_
  have := glue_time_le P₁ h1 u hM hN1
  have := glue_time_le P₂ h2 u hM hN2
  omega

/-! ### The selection -/

theorem time_selH (cs : Comps R cd sp setupW IW Ok) {T W : ℕ} (cb : CompBounds cs T W) :
    XProg.timeBoundT (selH cd cs.setupP cs.pubP) (startBound cd T W) ≤
      glueN cd * (2 * (glueM cb + glueN cd) + 5) + compTime cb + 20 := by
  show TT (selH cd cs.setupP cs.pubP) (bvec T 0 (stateBound cd W)) _
  simp only [selH, testLen, selCore]
  refine TT.mono (TT.ifBit _
    (TT.seq_glueB (M := glueM cb) (N := glueN cd) _ ?l1 ?m1 ?n1 (TT.ifBlank _ (TT.glueB (M := glueM cb) (N := glueN cd) _ ?l2 _ ?m2 ?n2) (TT.seq_glueB (M := glueM cb) (N := glueN cd) _ ?l3 ?m3 ?n3 (TT.ifBlank _
      (TT.seq_glueB (M := glueM cb) (N := glueN cd) _ ?l4 ?m4 ?n4 (TT.seq_comp 2 4 _ cs.setupP ?a1 ?b1 cb.len_setup
        (TT.seq_glueB (M := glueM cb) (N := glueN cd) _ ?l5 ?m5 ?n5 (TT.seq_comp 1 4 _ cs.pubP ?a2 ?b2 cb.len_pub
          (TT.glueB (M := glueM cb) (N := glueN cd) _ ?l6 _ ?m6 ?n6)))))
      (TT.seq_glueB (M := glueM cb) (N := glueN cd) _ ?l7 ?m7 ?n7 (TT.glueB (M := glueM cb) (N := glueN cd) _ ?l8 _ ?m8 ?n8))))))
    (TT.ifBlank _ (TT.seq_glueB (M := glueM cb) (N := glueN cd) _ ?l9 ?m9 ?n9 (TT.ifBlank _ (TT.glueB (M := glueM cb) (N := glueN cd) _ ?l10 _ ?m10 ?n10)
      (TT.seq_glueB (M := glueM cb) (N := glueN cd) _ ?l11 ?m11 ?n11 (TT.ifBlank _
      (TT.seq_glueB (M := glueM cb) (N := glueN cd) _ ?l12 ?m12 ?n12 (TT.seq_comp 2 4 _ cs.setupP ?a3 ?b3 cb.len_setup
        (TT.seq_glueB (M := glueM cb) (N := glueN cd) _ ?l13 ?m13 ?n13 (TT.seq_comp 1 4 _ cs.pubP ?a4 ?b4 cb.len_pub
          (TT.glueB (M := glueM cb) (N := glueN cd) _ ?l14 _ ?m14 ?n14)))))
      (TT.seq_glueB (M := glueM cb) (N := glueN cd) _ ?l15 ?m15 ?n15 (TT.glueB (M := glueM cb) (N := glueN cd) _ ?l16 _ ?m16 ?n16)))))) (TT.glueB (M := glueM cb) (N := glueN cd) _ ?l17 _ ?m17 ?n17))) ?fin
  case fin =>
    generalize 2 * (glueM cb + glueN cd) + 5 = c
    simp only [lenPrep, takeQ, buildSel, Prog.pcount, Prog.pcount_dropN, Prog.pcount_moveFront,
      Prog.pcount_prependN, Prog.pcount_consN]
    unfold compTime glueN
    ring_nf
    omega
  all_goals (try (intro t; fin_cases t)) <;>
    simp [lenPrep, takeQ, buildSel, Prog.lenBoundT, Prim.lenT, Prog.lenBoundT_dropN,
      Prog.lenBoundT_moveFront, bvec,
      Prog.LoopFree, Prog.loopFree_moveFront, Prog.loopFree_prependN, Prog.loopFree_dropN,
      Prog.loopFree_consN, Prog.pcount, glueM, glueN] <;> omega

/-! ### Key queries -/

theorem time_keyH (cs : Comps R cd sp setupW IW Ok) {T W : ℕ} (cb : CompBounds cs T W) :
    XProg.timeBoundT (keyH cd cs.keyP cs.authP) (startBound cd T W) ≤
      glueN cd * (2 * (glueM cb + glueN cd) + 5) + compTime cb + 20 := by
  show TT (keyH cd cs.keyP cs.authP) (bvec T 0 (stateBound cd W)) _
  simp only [keyH, keySel, skipG]
  refine TT.mono (TT.ifBit _ (TT.glueB (M := glueM cb) (N := glueN cd) _ ?l1 _ ?m1 ?n1)
    (TT.ifBlank _ (TT.glueB (M := glueM cb) (N := glueN cd) _ ?l2 _ ?m2 ?n2)
      (TT.seq_glueB (M := glueM cb) (N := glueN cd) _ ?l3 ?m3 ?n3
        (TT.seq_glueB (M := glueM cb) (N := glueN cd) _ ?l4 ?m4 ?n4
          (TT.seq_comp 1 6 _ cs.keyP ?a1 ?b1 cb.len_key
            (TT.seq_glueB (M := glueM cb) (N := glueN cd) _ ?l5 ?m5 ?n5
              (TT.seq_comp 6 7 _ cs.authP ?a2 ?b2 cb.len_auth
                (TT.seq_ifBit_glueB (M := glueM cb) (N := glueN cd) _ _ _ ?l6 ?l7 ?m6 ?n6 ?n7
                  (TT.glueB (M := glueM cb) (N := glueN cd) _ ?l8 _ ?m8 ?n8))))))))) ?fin
  case fin =>
    generalize 2 * (glueM cb + glueN cd) + 5 = c
    simp only [parseSel, setBad, rebuildK, Prog.pcount, Prog.pcount_moveFront,
      Prog.pcount_prependN]
    unfold compTime glueN
    ring_nf
    omega
  all_goals (try (intro t; fin_cases t)) <;>
    simp [parseSel, setBad, rebuildK, Prog.lenBoundT, Prim.lenT, Prog.lenBoundT_moveFront, bvec,
      sigBound, Prog.LoopFree, Prog.loopFree_moveFront, Prog.loopFree_prependN, Prog.pcount, glueM,
      glueN] <;> omega

/-! ### The challenge -/

theorem time_chalH (cs : Comps R cd sp setupW IW Ok) {T W : ℕ} (cb : CompBounds cs T W) :
    XProg.timeBoundT (chalH cd cs.chalP) (startBound cd T W) ≤
      glueN cd * (2 * (glueM cb + glueN cd) + 5) + compTime cb + 20 := by
  show TT (chalH cd cs.chalP) (bvec T 0 (stateBound cd W)) _
  simp only [chalH, chalSel, testLen, chalFresh, skipG]
  refine TT.mono (TT.ifBit _ (TT.glueB (M := glueM cb) (N := glueN cd) _ ?l1 _ ?m1 ?n1)
    (TT.ifBlank _ (TT.glueB (M := glueM cb) (N := glueN cd) _ ?l2 _ ?m2 ?n2)
      (TT.seq_glueB (M := glueM cb) (N := glueN cd) _ ?l3 ?m3 ?n3
        (TT.ifBit _ (TT.glueB (M := glueM cb) (N := glueN cd) _ ?l4 _ ?m4 ?n4)
          (TT.seq_glueB (M := glueM cb) (N := glueN cd) _ ?l5 ?m5 ?n5
            (TT.ifBlank _ (TT.glueB (M := glueM cb) (N := glueN cd) _ ?l6 _ ?m6 ?n6)
              (TT.seq_glueB (M := glueM cb) (N := glueN cd) _ ?l7 ?m7 ?n7
                (TT.ifBlank _
                  (TT.seq_glueB (M := glueM cb) (N := glueN cd) _ ?l8 ?m8 ?n8
                    (TT.seq_glueB (M := glueM cb) (N := glueN cd) _ ?l9 ?m9 ?n9
                      (TT.seq_comp 1 6 _ cs.chalP ?a1 ?b1 cb.len_chal
                        (TT.glueB (M := glueM cb) (N := glueN cd) _ ?l10 _ ?m10 ?n10))))
                  (TT.seq_glueB (M := glueM cb) (N := glueN cd) _ ?l11 ?m11 ?n11
                    (TT.glueB (M := glueM cb) (N := glueN cd) _ ?l12 _ ?m12 ?n12)))))))))) ?fin
  case fin =>
    generalize 2 * (glueM cb + glueN cd) + 5 = c
    simp only [lenPrep, restoreC, parseC, takeQ, rebuildC, Prog.pcount, Prog.pcount_dropN,
      Prog.pcount_moveFront, Prog.pcount_prependN]
    unfold compTime glueN
    ring_nf
    omega
  all_goals (try (intro t; fin_cases t)) <;>
    simp [lenPrep, restoreC, parseC, takeQ, rebuildC, Prog.lenBoundT, Prim.lenT,
      Prog.lenBoundT_dropN, Prog.lenBoundT_moveFront, bvec, sigBound,
      Prog.LoopFree, Prog.loopFree_moveFront, Prog.loopFree_prependN, Prog.loopFree_dropN,
      Prog.pcount, glueM, glueN] <;> omega

/-! ### The clock -/

/-- **The clock of the handlers**, explicitly: affine in the query bound `T` (through `glueM`
and the components' per-tape time bounds `compTime`). -/
theorem handlerTime_le (cs : Comps R cd sp setupW IW Ok) {T W : ℕ} (cb : CompBounds cs T W) :
    handlerTime cd cs T W ≤ glueN cd * (2 * (glueM cb + glueN cd) + 5) + compTime cb + 20 :=
  max_le (time_selH cs cb) (max_le (time_keyH cs cb) (time_chalH cs cb))

end AdvancedEncryption.PE.Generic