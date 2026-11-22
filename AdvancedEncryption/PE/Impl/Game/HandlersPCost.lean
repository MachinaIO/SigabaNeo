import PE.Impl.Game.HandlersP

/-!
# The time of the per-query handlers

`time_handlerProgP`: started with a query of at most `T` bits (and a state word of at most
`stateBound W` bits), every handler program of `handlerProgP` takes at most

  `handlerQ0 cb + handlerQ1 cd K₀ kL * T`

steps, where `handlerQ1 = 2 N` (`N = glueNP` the number of glue primitives) and `handlerQ0` depends
on the codes, `K₀`, `kL`, `W` and the components' bounds at their input bounds with the query cut
at `K₀` (`CompBoundsP`, `compTimeP`), not on `T`.

`handlesP`: the handlers `handlersP` satisfy `SigabaNeo.HandlesP` for every oracle machine `A`, with
`q₀ = handlerQ0 cb` and `q₁ = handlerQ1 cd K₀ kL`.
-/

namespace AdvancedEncryption.PE.Generic

open SigabaNeo SigabaNeo.Tape Cslib

variable {U : Universe} {Sig : Type} {R : ℕ}

variable {cd : Codes U Sig} {sp : Spec U Sig} {setupW : List Bool → U.Attr → PMF Sig}
  {IW : List Bool → Prop} {Ok : Sig → Prop}

/-- The per-tape length bounds of the components' outputs, the key queries cut at `K₀`. -/
structure CompBoundsP (cs : Comps R cd sp setupW IW Ok) (K₀ W : ℕ) where
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
  len_key : XProg.lenBoundT cs.keyP (io2 (sigBound cd W) K₀ 0) ≤ io2 Lk 0 0
  len_auth : XProg.lenBoundT cs.authP (io2 K₀ cd.nA 0) ≤ io2 La 0 0
  len_chal : XProg.lenBoundT cs.chalP (io2 (sigBound cd W) cd.nM 0) ≤ io2 Lc 0 0

variable (cd) in
/-- The glue primitives of one handler, with the cut `K₀` and the answer `kL` to long queries. -/
def glueNP (K₀ : ℕ) (kL : List Bool) : ℕ := glueN cd + 6 * K₀ + kL.length + 20

/-- A bound on every glue tape between the steps of a handler, for queries of at most `T` bits. -/
def glueMP {cs : Comps R cd sp setupW IW Ok} {K₀ W : ℕ} (cb : CompBoundsP cs K₀ W) (T : ℕ) : ℕ :=
  T + stateBound cd W + cb.Ssig + cb.Lp + cb.Lk + cb.La + cb.Lc + cd.nA + cd.nM + K₀ + 2

/-- The time of the components at their input bounds, the key queries cut at `K₀`. -/
def compTimeP {cs : Comps R cd sp setupW IW Ok} {K₀ W : ℕ} (cb : CompBoundsP cs K₀ W) : ℕ :=
  XProg.timeBoundT cs.setupP (io2 (stateBound cd W) cd.nA 0) +
    XProg.timeBoundT cs.pubP (io2 cb.Ssig 0 0) +
    XProg.timeBoundT cs.keyP (io2 (sigBound cd W) K₀ 0) +
    XProg.timeBoundT cs.authP (io2 K₀ cd.nA 0) +
    XProg.timeBoundT cs.chalP (io2 (sigBound cd W) cd.nM 0)

/-! ### The selection and the challenge -/

theorem time_selHP (cs : Comps R cd sp setupW IW Ok) {K₀ : ℕ} {kL : List Bool} {W : ℕ} (cb : CompBoundsP cs K₀ W) (T : ℕ) :
    XProg.timeBoundT (selH cd cs.setupP cs.pubP) (startBound cd T W) ≤
      glueNP cd K₀ kL * (2 * (glueMP cb T + glueNP cd K₀ kL) + 5) + compTimeP cb + 20 := by
  show TT (selH cd cs.setupP cs.pubP) (bvec T 0 (stateBound cd W)) _
  simp only [selH, testLen, selCore]
  refine TT.mono (TT.ifBit _
    (TT.seq_glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l1 ?m1 ?n1 (TT.ifBlank _ (TT.glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l2 _ ?m2 ?n2) (TT.seq_glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l3 ?m3 ?n3 (TT.ifBlank _
      (TT.seq_glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l4 ?m4 ?n4 (TT.seq_comp 2 4 _ cs.setupP ?a1 ?b1 cb.len_setup
        (TT.seq_glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l5 ?m5 ?n5 (TT.seq_comp 1 4 _ cs.pubP ?a2 ?b2 cb.len_pub
          (TT.glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l6 _ ?m6 ?n6)))))
      (TT.seq_glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l7 ?m7 ?n7 (TT.glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l8 _ ?m8 ?n8))))))
    (TT.ifBlank _ (TT.seq_glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l9 ?m9 ?n9 (TT.ifBlank _ (TT.glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l10 _ ?m10 ?n10)
      (TT.seq_glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l11 ?m11 ?n11 (TT.ifBlank _
      (TT.seq_glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l12 ?m12 ?n12 (TT.seq_comp 2 4 _ cs.setupP ?a3 ?b3 cb.len_setup
        (TT.seq_glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l13 ?m13 ?n13 (TT.seq_comp 1 4 _ cs.pubP ?a4 ?b4 cb.len_pub
          (TT.glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l14 _ ?m14 ?n14)))))
      (TT.seq_glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l15 ?m15 ?n15 (TT.glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l16 _ ?m16 ?n16)))))) (TT.glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l17 _ ?m17 ?n17))) ?fin
  case fin =>
    generalize 2 * (glueMP cb T + glueNP cd K₀ kL) + 5 = c
    simp only [lenPrep, takeQ, buildSel, Prog.pcount, Prog.pcount_dropN, Prog.pcount_moveFront,
      Prog.pcount_prependN, Prog.pcount_consN]
    unfold compTimeP glueNP glueN
    ring_nf
    omega
  all_goals (try (intro t; fin_cases t)) <;>
    simp [lenPrep, takeQ, buildSel, Prog.lenBoundT, Prim.lenT, Prog.lenBoundT_dropN,
      Prog.lenBoundT_moveFront, bvec,
      Prog.LoopFree, Prog.loopFree_moveFront, Prog.loopFree_prependN, Prog.loopFree_dropN,
      Prog.loopFree_consN, Prog.pcount, glueMP, glueNP, glueN] <;> omega

theorem time_chalHP (cs : Comps R cd sp setupW IW Ok) {K₀ : ℕ} {kL : List Bool} {W : ℕ} (cb : CompBoundsP cs K₀ W) (T : ℕ) :
    XProg.timeBoundT (chalH cd cs.chalP) (startBound cd T W) ≤
      glueNP cd K₀ kL * (2 * (glueMP cb T + glueNP cd K₀ kL) + 5) + compTimeP cb + 20 := by
  show TT (chalH cd cs.chalP) (bvec T 0 (stateBound cd W)) _
  simp only [chalH, chalSel, testLen, chalFresh, skipG]
  refine TT.mono (TT.ifBit _ (TT.glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l1 _ ?m1 ?n1)
    (TT.ifBlank _ (TT.glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l2 _ ?m2 ?n2)
      (TT.seq_glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l3 ?m3 ?n3
        (TT.ifBit _ (TT.glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l4 _ ?m4 ?n4)
          (TT.seq_glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l5 ?m5 ?n5
            (TT.ifBlank _ (TT.glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l6 _ ?m6 ?n6)
              (TT.seq_glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l7 ?m7 ?n7
                (TT.ifBlank _
                  (TT.seq_glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l8 ?m8 ?n8
                    (TT.seq_glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l9 ?m9 ?n9
                      (TT.seq_comp 1 6 _ cs.chalP ?a1 ?b1 cb.len_chal
                        (TT.glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l10 _ ?m10 ?n10))))
                  (TT.seq_glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l11 ?m11 ?n11
                    (TT.glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l12 _ ?m12 ?n12)))))))))) ?fin
  case fin =>
    generalize 2 * (glueMP cb T + glueNP cd K₀ kL) + 5 = c
    simp only [lenPrep, restoreC, parseC, takeQ, rebuildC, Prog.pcount, Prog.pcount_dropN,
      Prog.pcount_moveFront, Prog.pcount_prependN]
    unfold compTimeP glueNP glueN
    ring_nf
    omega
  all_goals (try (intro t; fin_cases t)) <;>
    simp [lenPrep, restoreC, parseC, takeQ, rebuildC, Prog.lenBoundT, Prim.lenT,
      Prog.lenBoundT_dropN, Prog.lenBoundT_moveFront, bvec, sigBound,
      Prog.LoopFree, Prog.loopFree_moveFront, Prog.loopFree_prependN, Prog.loopFree_dropN,
      Prog.pcount, glueMP, glueNP, glueN] <;> omega

/-! ### Key queries -/

theorem time_keyHP (cs : Comps R cd sp setupW IW Ok) {K₀ : ℕ} {kL : List Bool} {W : ℕ}
    (cb : CompBoundsP cs K₀ W) (T : ℕ) :
    XProg.timeBoundT (keyHP cd K₀ kL cs.keyP cs.authP) (startBound cd T W) ≤
      glueNP cd K₀ kL * (2 * (glueMP cb T + glueNP cd K₀ kL) + 5) + compTimeP cb + 20 := by
  show TT (keyHP cd K₀ kL cs.keyP cs.authP) (bvec T 0 (stateBound cd W)) _
  simp only [keyHP, keySelP, keyShortP, skipG]
  refine TT.mono (TT.ifBit _ (TT.glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l1 _ ?m1 ?n1)
    (TT.ifBlank _ (TT.glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l2 _ ?m2 ?n2)
      (TT.seq_glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l3 ?m3 ?n3
        (TT.ifBlank _
          (TT.seq_glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l4 ?m4 ?n4
            (TT.seq_glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l5 ?m5 ?n5
              (TT.seq_comp 6 7 _ cs.authP ?a1 ?b1 cb.len_auth
                (TT.seq_ifBit_glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ _ _ ?l6 ?l7 ?m6
                  ?n6 ?n7
                  (TT.seq_glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l8 ?m8 ?n8
                    (TT.seq_comp 1 6 _ cs.keyP ?a2 ?b2 cb.len_key
                      (TT.glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l9 _ ?m9 ?n9)))))))
          (TT.glueB (M := glueMP cb T) (N := glueNP cd K₀ kL) _ ?l10 _ ?m10 ?n10))))) ?fin
  case fin =>
    generalize 2 * (glueMP cb T + glueNP cd K₀ kL) + 5 = c
    simp only [cutQ, longK, keyArgP, parseSel, setBad, rebuildK, Prog.pcount, Prog.pcount_moveFront,
      Prog.pcount_prependN, pcount_writeA]
    unfold compTimeP glueNP glueN
    ring_nf
    omega
  all_goals (try (intro t; fin_cases t)) <;>
    simp [cutQ, longK, keyArgP, parseSel, setBad, rebuildK, Prog.lenBoundT, Prim.lenT,
      Prog.lenBoundT_moveFront, bvec, sigBound, Prog.LoopFree, Prog.loopFree_moveFront,
      Prog.loopFree_prependN, loopFree_writeA, pcount_writeA, Prog.pcount, glueMP, glueNP,
      glueN] <;> omega

/-! ### The per-query clock -/

variable (cd) in
/-- The time per query bit of the handlers. -/
def handlerQ1 (K₀ : ℕ) (kL : List Bool) : ℕ := 2 * glueNP cd K₀ kL

/-- The time of the handlers for an empty query. -/
def handlerQ0 {cs : Comps R cd sp setupW IW Ok} {K₀ W : ℕ} (cb : CompBoundsP cs K₀ W)
    (kL : List Bool) : ℕ :=
  glueNP cd K₀ kL * (2 * (glueMP cb 0 + glueNP cd K₀ kL) + 5) + compTimeP cb + 20

theorem bound_eq {cs : Comps R cd sp setupW IW Ok} {K₀ W : ℕ} (cb : CompBoundsP cs K₀ W)
    (kL : List Bool) (T : ℕ) :
    glueNP cd K₀ kL * (2 * (glueMP cb T + glueNP cd K₀ kL) + 5) + compTimeP cb + 20 =
      handlerQ0 cb kL + handlerQ1 cd K₀ kL * T := by
  simp only [handlerQ0, handlerQ1, glueMP]
  ring

/-- **The per-query clock of the handlers**: affine in the query bound `T`, with coefficients
independent of `T`. -/
theorem time_handlerProgP (cs : Comps R cd sp setupW IW Ok) (K₀ : ℕ) (kL : List Bool) {W : ℕ}
    (cb : CompBoundsP cs K₀ W) (o : Fin 3) (T : ℕ) :
    XProg.timeBoundT (handlerProgP cd cs K₀ kL o) (startBound cd T W) ≤
      handlerQ0 cb kL + handlerQ1 cd K₀ kL * T := by
  rw [← bound_eq]
  rcases fin3_cases o with rfl | rfl | rfl
  · rw [handlerProgP_sel]; exact time_selHP cs cb T
  · rw [handlerProgP_key]; exact time_keyHP cs cb T
  · rw [handlerProgP_chal]; exact time_chalHP cs cb T

/-! ### The handlers serve the oracle, per query -/

/-- **The per-query handlers serve the oracle.** For every oracle machine `A`, the handlers
`handlersP` satisfy `HandlesP` for the oracle `oracleW sp setupW`, the encoding `encState`, the
served states `InvS IW W Ok`, the per-query clock `handlerQ0 cb kL + handlerQ1 cd K₀ kL * |b|` and
answers of at most `L` bits, when key queries longer than `K₀` are answered by `kL` and never
authorized (`LongKeys`). -/
theorem handlesP (cs : Comps R cd sp setupW IW Ok) (K₀ : ℕ) (kL : List Bool)
    (hlong : LongKeys sp Ok K₀ kL) {W : ℕ} (cb : CompBoundsP cs K₀ W) (A : Machine 3) (L : ℕ)
    (hpubL : ∀ σ, Ok σ → (sp.pub σ).length ≤ L)
    (hkeyL : ∀ σ C, Ok σ → C.length ≤ K₀ → ∀ sk ∈ (sp.key σ C).support, sk.length ≤ L)
    (hkL : kL.length ≤ L)
    (hchalL : ∀ σ μ, Ok σ → ∀ ct ∈ (sp.chal σ μ).support, ct.length ≤ L) :
    HandlesP A (handlersP cd cs K₀ kL W) (oracleW sp setupW) cd.encState (InvS IW W Ok)
      (handlerQ0 cb kL) (handlerQ1 cd K₀ kL) L where
  runs o b st hb h := by
    have hfits : Fits (Inline.layout (m := R + 5) b [] (cd.encState st))
        (startBound (R := R) cd b.length W) := by
      rw [layout_eq]
      refine fits_ext8 fun j => ?_
      simp only [vec, bvec]
      split_ifs
      · exact le_rfl
      · simp
      · exact length_encState_le h
      · simp
    have hr := Routine.runs_ofXProg (handlerProgP cd cs K₀ kL o) (wf_handlerProgP cs K₀ kL o)
      (startBound cd b.length W) _ hfits
    rw [layout_eq, law_handlerProgP cs K₀ kL hlong o b st h] at hr
    simp only [layout_eq]
    have hr' : (handlersP cd cs K₀ kL W o).RunsIn
        (XProg.timeBoundT (handlerProgP cd cs K₀ kL o) (startBound cd b.length W))
        (ext8 (vec b [] (cd.encState st)) [])
        ((oracleW sp setupW (o, b) st).map fun r => ext8 (vec b r.1 (cd.encState r.2)) []) := hr
    exact hr'.mono (time_handlerProgP cs K₀ kL cb o b.length)
  inv o b st hb h := by
    refine inv_oracleW (T := A.time) cs hpubL (fun σ C hσ _ sk hsk => ?_) hchalL o b st hb h
    by_cases hC : C.length ≤ K₀
    · exact hkeyL σ C hσ hC sk hsk
    · rw [hlong.key σ C hσ (by omega), PMF.mem_support_pure_iff] at hsk
      rw [hsk]; exact hkL

end AdvancedEncryption.PE.Generic
