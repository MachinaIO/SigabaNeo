import PE.Impl.ExpLUT.Prog.RedPubPAutT
open SigabaNeo.Tape.RingVM.Buf SigabaNeo.Tape.RingVM.Hash
/-!
# The public-key component of the reduction (package G2, `pubP`)

* `exec_outDC`: `d = [ad; d₂]`;
* **`exec_pubC`**: from the raw secret, `pubC D` leaves the word of the public key
  `(mpkEnc D).enc (pubK D σ)` in `rOut` (`pubWord_eq`);
* **`law_pubP`**: `law (pubP D) (io2 ((rawEnc D).enc σ) [] []) =
  pure (io2 ((mpkEnc D).enc (redView D (rawF D σ)).1) [] [])`;
* **`wf_pubP`**.

At dimensions with `2 ≤ N`, `w 2^7 ≤ 2N` (the monomials `X^{w 2^j}` by `rhoJ`) and `b ≤ 32`
(the templates `κ_t`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedPubP

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open SigabaNeo.Tape.RingVM.Hash

variable {D : Dims}

/-- **`d`.** -/
theorem exec_outDC (σ : RawSec D) (w : St) (hT : TmplOK D w) (b₀ acc : List Bool)
    (hO : w rOut = pbuf b₀ acc) (hAd : w rAd = encRM D.N D.K σ.2.1.ad)
    (hD2 : w rD2 = encRM D.N D.K σ.2.2.2.2.1) :
    exec D.N D.K outDC w rOut = pbuf b₀ (acc ++ wd σ) := by
  simp only [outDC, exec_ofList_cons, exec_ofList_nil]
  rw [exec_mv_blk (d := rOut) (s := rAd) (c := xCNK) (by decide) (b₀ := b₀) (acc := acc)
    (w := w) (v := encRM D.N D.K σ.2.1.ad) (L := []) hO
    (by rw [length_encRM, hT.len xCNK]; rfl) (by rw [hAd, List.append_nil])]
  rw [exec_mv_blk (d := rOut) (s := rD2) (c := xCNK) (by decide) (b₀ := b₀)
    (acc := acc ++ encRM D.N D.K σ.2.1.ad) (v := encRM D.N D.K σ.2.2.2.2.1) (L := [])
    (by simp [Function.update_apply]) (by simp [Function.update_apply, length_encRM, hT.len xCNK])
    (by simp [Function.update_apply, hD2])]
  simp [Function.update_apply, wd, List.append_assoc]

/-- The initial registers. -/
noncomputable def w0P (D : Dims) (σ : RawSec D) : St :=
  SigabaNeo.Tape.RingVM.Handler.initW1 ra rb r1 (tm D) ((rawEnc D).enc σ) []

theorem w0P_tm (σ : RawSec D) (r : Fin 200) (h0 : r ≠ ra) (h1 : r ≠ rb) (h2 : r ≠ r1) :
    w0P D σ r = List.replicate (tm D r) false := by
  simp [w0P, SigabaNeo.Tape.RingVM.Handler.initW1, SigabaNeo.Tape.RingVM.Handler.initW, Function.update_of_ne h2, h0, h1]

theorem length_pubWord (σ : RawSec D) :
    (wB σ ++ (wH σ ++ (wa σ ++ ((wA0row σ 0 ++ wA0row σ 1) ++ (wAin σ ++ (wAaut σ ++ wd σ)))))).length =
      pencLen (mpkEnc D) := by
  rw [← pubWord_eq]; exact FixedEnc.length _ _

/-- **The code of the public key**: `rOut` holds the word of the public key. -/
theorem exec_pubC (hN : 2 ≤ D.N) (hW : wSt * 2 ^ 7 ≤ 2 * D.N) (hb32 : D.b ≤ 32) (σ : RawSec D) :
    exec D.N D.K (pubC D) (w0P D σ) rOut = (mpkEnc D).enc (pubK D σ) := by
  set w := w0P D σ
  have hT : TmplOK D w := tmplOK_initW1 _ _
  have hI : ∀ r : Fin 200, r ≠ ra → r ≠ rb → r ≠ r1 → w r = List.replicate (tm D r) false :=
    fun r h0 h1 h2 => w0P_tm σ r h0 h1 h2
  set b₀ := w rOut
  have hb₀ : b₀ = List.replicate (pencLen (mpkEnc D)) false := hI rOut (by decide) (by decide)
    (by decide)
  -- parse
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ :=
    exec_parseC σ w hT (by simp [w, w0P, SigabaNeo.Tape.RingVM.Handler.initW1, SigabaNeo.Tape.RingVM.Handler.initW])
      (fun r hr => hI r (fun h => by subst h; revert hr; decide)
        (fun h => by subst h; revert hr; decide) (fun h => by subst h; revert hr; decide))
  set w1 := exec D.N D.K parseC w
  have hT1 : TmplOK D w1 := tmplOK_frame parseW (by decide) hT c17
  have f1 : ∀ r, r ∉ parseW → r ≠ ra → r ≠ rb → r ≠ r1 → w1 r = List.replicate (tm D r) false :=
    fun r h h0 h1 h2 => by rw [c17 r h, hI r h0 h1 h2]
  -- `B`
  obtain ⟨d1, d2⟩ := exec_outBC σ w1 hT1 b₀ [] (by rw [c17 _ (by decide), pbuf_nil]) c2 c9
  set w2 := exec D.N D.K outBC w1
  have hT2 : TmplOK D w2 := tmplOK_frame [rOut, tmp] (by decide) hT1 fun j hj => d2 j
    (fun h => hj (by simp [h])) (fun h => hj (by simp [h]))
  -- `H`
  obtain ⟨e1, e2⟩ := exec_outHC σ w2 hT2 b₀ _ d1 (by rw [d2 _ (by decide) (by decide), c4])
    (by rw [d2 _ (by decide) (by decide), c5]) (by rw [d2 _ (by decide) (by decide), c10])
  set w3 := exec D.N D.K outHC w2
  have hT3 : TmplOK D w3 := tmplOK_frame _ (by decide) hT2 e2
  have g3 : ∀ r, r ∉ [rOut, tmp, cnt, rSk, rSp, rH2s, cntJ] → w3 r = w1 r := fun r hr => by
    rw [e2 r hr, d2 r (fun h => hr (by simp [h])) (fun h => hr (by simp [h]))]
  -- `Ā`, `B̄⁽²⁾`, `−v̄_B`
  obtain ⟨p1, p2, p3, p4, p5⟩ := exec_prepC σ w3 hT3 (by rw [g3 _ (by decide), c2])
    (by rw [g3 _ (by decide), c9]) (by rw [g3 _ (by decide), c6])
    (by rw [g3 _ (by decide), f1 _ (by decide) (by decide) (by decide) (by decide)]; simp)
    (by rw [g3 _ (by decide), f1 _ (by decide) (by decide) (by decide) (by decide)]; simp)
    (by rw [g3 _ (by decide), f1 _ (by decide) (by decide) (by decide) (by decide)]; rfl)
    (by rw [g3 _ (by decide), f1 _ (by decide) (by decide) (by decide) (by decide)]; simp)
  set w4 := exec D.N D.K prepC w3
  have hT4 : TmplOK D w4 := tmplOK_frame _ (by decide) hT3 p5
  have g4 : ∀ r, r ∉ [tmp, rAbar, rB2bar, cnt, xv, xS, rNV] →
      r ∉ [rOut, tmp, cnt, rSk, rSp, rH2s, cntJ] → w4 r = w1 r := fun r h1 h2 => by
    rw [p5 r h1, g3 r h2]
  -- `a`
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := exec_aPhC (D := D) hN hW σ w4 hT4
    (by rw [g4 _ (by decide) (by decide), c1])
    (by rw [g4 _ (by decide) (by decide), f1 _ (by decide) (by decide) (by decide) (by decide)]; simp)
    p1 p3 (by rw [g4 _ (by decide) (by decide), c13]) (by rw [g4 _ (by decide) (by decide), c12])
    (by rw [g4 _ (by decide) (by decide), f1 _ (by decide) (by decide) (by decide) (by decide)]; simp)
    (by rw [g4 _ (by decide) (by decide), f1 _ (by decide) (by decide) (by decide) (by decide)]; simp)
    p4 (by rw [g4 _ (by decide) (by decide), f1 _ (by decide) (by decide) (by decide) (by decide)]; simp)
    (by rw [g4 _ (by decide) (by decide), f1 _ (by decide) (by decide) (by decide) (by decide)]; simp)
    b₀ _ (by rw [p5 _ (by decide)]; exact e1)
  set w5 := exec D.N D.K aPhC w4
  -- `A₀`
  obtain ⟨z1, z2, z3, z4, z5, z6⟩ := exec_a0C σ w5 a7 (by rw [a8 _ (by decide), p1])
    (by rw [a8 _ (by decide), p2])
    (by rw [a8 _ (by decide), g4 _ (by decide) (by decide), c14]) a4 a5 a6 b₀ _ a1
  set w6 := exec D.N D.K a0C w5
  -- `A^in`
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := exec_ainC σ w6 z5
    (by rw [z6 _ (by decide), a8 _ (by decide), p1]) (by rw [z6 _ (by decide), a8 _ (by decide), p2])
    (by rw [z6 _ (by decide), a2]) (by rw [z6 _ (by decide), a3])
    (by rw [z6 _ (by decide), a8 _ (by decide), g4 _ (by decide) (by decide),
      f1 _ (by decide) (by decide) (by decide) (by decide)]; simp)
    (by rw [z6 _ (by decide), a8 _ (by decide), g4 _ (by decide) (by decide), c15]) b₀ _ z1 z2 z3 z4
  set w7 := exec D.N D.K ainC w6
  -- `A^aut`
  have h7 : ∀ r, r ∉ ainW → r ∉ rowPushW → r ∉ aPhW → w7 r = w5 r := fun r h1 h2 h3 => by
    rw [i7 r h1, z6 r h2]
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := exec_autC hb32 σ w7 i6
    (by rw [h7 _ (by decide) (by decide) (by decide), a8 _ (by decide), g4 _ (by decide) (by decide), c5])
    (by rw [h7 _ (by decide) (by decide) (by decide), a8 _ (by decide), g4 _ (by decide) (by decide), c4])
    (by rw [h7 _ (by decide) (by decide) (by decide), a8 _ (by decide), g4 _ (by decide) (by decide), c8])
    (by rw [h7 _ (by decide) (by decide) (by decide), a8 _ (by decide), g4 _ (by decide) (by decide), c7])
    (by rw [h7 _ (by decide) (by decide) (by decide), a8 _ (by decide), p1])
    (by rw [h7 _ (by decide) (by decide) (by decide), a8 _ (by decide), p2]) i2
    (by rw [h7 _ (by decide) (by decide) (by decide), a8 _ (by decide), g4 _ (by decide) (by decide), c16])
    b₀ _ i1 i3 i4 i5
  set w8 := exec D.N D.K (autC D) w7
  -- `d`
  have hd := exec_outDC σ w8 u6 b₀ _ u1
    (by rw [u7 _ (by decide), h7 _ (by decide) (by decide) (by decide), a8 _ (by decide),
      g4 _ (by decide) (by decide), c3])
    (by rw [u7 _ (by decide), h7 _ (by decide) (by decide) (by decide), a8 _ (by decide),
      g4 _ (by decide) (by decide), c11])
  have ex : exec D.N D.K (pubC D) w = exec D.N D.K outDC w8 := rfl
  rw [ex, hd, pubWord_eq]
  simp only [List.nil_append, List.append_assoc]
  exact pbuf_full (by
    rw [hb₀, List.length_replicate, ← length_pubWord σ]; simp only [List.length_append]; omega)

/-- **The law of the public-key component.** -/
theorem law_pubP (hN : 2 ≤ D.N) (hW : wSt * 2 ^ 7 ≤ 2 * D.N) (hb32 : D.b ≤ 32) (σ : RawSec D) :
    XProg.law (pubP D) (io2 (R := 245) ((rawEnc D).enc σ) [] []) =
      PMF.pure (io2 (R := 245) ((mpkEnc D).enc (redView D (rawF D σ)).1) [] []) := by
  rw [pubP, SigabaNeo.Tape.RingVM.Handler.law_ringIO1 D.N_pos D.K_pos (by decide) rOut r1 (by decide) (by decide)]
  have := exec_pubC hN hW hb32 σ
  rw [w0P] at this
  rw [this]
  rfl

/-- **The public-key component is well formed.** -/
theorem wf_pubP : (pubP D).WF :=
  SigabaNeo.Tape.RingVM.Handler.wf_ringIO1 D.N D.K ra rb rOut r1 (tm D) (pubC D) (loopOkB_pubC D)

end AdvancedEncryption.ExpLUT.Prog.RedPubP
