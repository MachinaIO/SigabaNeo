import PE.Impl.RingBTVW.Prog.WfB2S
import PE.Impl.RingBTVW.Prog.WfB2Time

/-!
# The time of the `W_f` block on register streams

Per-tape bounds of the phases of `wfBodyS` (`XProg.Ph`), as `WfB2Time` for `wfBody`: the count of
the instructions (`countP (3 W)`), the clear of its phase word, the cap `capN Ic` (`ph_capN`), and
then the phases of `WfB2` (`prepTRest`, `prepGRest`, the two runs, the key sum, the cleanup).
-/

namespace AdvancedEncryption.RingBTVW.Prog

set_option maxRecDepth 100000

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

namespace WB2

open SigabaNeo.Tape.ValVM SigabaNeo.Tape.Prog SigabaNeo.Tape.Prog.KST

/-! ### The count and the cap -/

/-- The bounds after `countP (3 W)` on its frame. -/
def cntOutS (W : ℕ) (β : Fin 256 → ℕ) : Fin 5 → ℕ :=
  ![β (mw GS), β (mw GCNT) + β (mw GS), max (β (mw 1)) (3 * W - 1), 0, β (mw GS)]

/-- The steps of `countP (3 W)`. -/
def cntTS (W : ℕ) (β : Fin 256 → ℕ) : ℕ :=
  Prog.countT (3 * W) (β (mw GS))
    (β (mw GS) + β (mw GCNT) + β (mw 1) + β (mw 3) + β (mw 4) + 3 * W)

theorem ph_cntS (W : ℕ) (β : Fin 256 → ℕ) :
    Ph (.frame (ValVM.mkE cntE cntE_inj) (.prog (Prog.countP (3 * W)))) β (cntTS W β)
      (embedF (ValVM.mkE cntE cntE_inj) β (cntOutS W β)) := by
  refine ph_frame _ ?_
  have h := ph_countP (3 * W) (β (mw GS)) (β (mw GCNT)) (β (mw 1)) (β (mw 3)) (β (mw 4))
  refine h.mono (fun j => ?_) le_rfl le_rfl
  fin_cases j <;> rfl

/-- The bounds after `capN Ic` on its frame. -/
def capOutS (Ic : ℕ) (β : Fin 256 → ℕ) : Fin 5 → ℕ :=
  ![β (mw 1) + Ic, 0, max (max (β (mw 5)) Ic) 1, 0, Ic]

/-- The steps of `capN Ic`. -/
def capTS (Ic : ℕ) (β : Fin 256 → ℕ) : ℕ :=
  (2 * Ic + 1) * (4 * max (supB ![β (mw GCNT), β (mw 1), β (mw 5), β (mw 3), β (mw 4)]) Ic + 12) +
    Prog.capLT Ic (β (mw GCNT) + β (mw 1) + max (β (mw 5)) Ic + β (mw 4) + Ic + 1)

theorem ph_capS (Ic : ℕ) (β : Fin 256 → ℕ) :
    Ph (.frame (ValVM.mkE capE capE_inj) (XProg.capN Ic)) β (capTS Ic β)
      (embedF (ValVM.mkE capE capE_inj) β (capOutS Ic β)) := by
  refine ph_frame _ ?_
  have h := XProg.ph_capN Ic (β (mw GCNT)) (β (mw 1)) (β (mw 5)) (β (mw 3)) (β (mw 4))
  refine h.mono (fun j => ?_) le_rfl le_rfl
  fin_cases j <;> rfl

/-- The bounds after the count, the clear of `1` and the cap. -/
def ccVS (W Ic : ℕ) (β : Fin 256 → ℕ) : Fin 256 → ℕ :=
  let vc := embedF (ValVM.mkE cntE cntE_inj) β (cntOutS W β)
  let vc' := Prog.lenBoundT (clr (mw 1)) vc
  embedF (ValVM.mkE capE capE_inj) vc' (capOutS Ic vc')

/-- The steps of the count, the clear of `1` and the cap. -/
def ccTS (W Ic : ℕ) (β : Fin 256 → ℕ) : ℕ :=
  let vc := embedF (ValVM.mkE cntE cntE_inj) β (cntOutS W β)
  let vc' := Prog.lenBoundT (clr (mw 1)) vc
  cntTS W β + (Prog.timeBoundT (clr (mw 1)) vc + capTS Ic vc')

/-- **The count, the clear, the cap and the rest.** -/
theorem ph_cntS_seq (W Ic : ℕ) {R : XProg 256} {β : Fin 256 → ℕ} {T : ℕ} {β' : Fin 256 → ℕ}
    (h : Ph (.seq (.prog (clr (mw 12))) R) (ccVS W Ic β) T β') :
    Ph (cntS Ic W R) β (ccTS W Ic β + T) β' := by
  have := (ph_cntS W β).seq <| (ph_prog (clr (mw 1)) _).seq <| (ph_capS Ic _).seq h
  refine this.mono le_rfl (le_of_eq ?_) le_rfl
  simp only [ccTS]; ring

/-! ### The preparations -/

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (W Ic : ℕ)

/-- The bounds after `prepTS`, step by step. -/
def vTS (β0 : Fin 256 → ℕ) (M31 : ℕ) : Fin 256 → ℕ :=
  let v1 := Prog.lenBoundT (cp (mw GSC) (mw GS)) β0
  let v2 := ccVS W Ic v1
  let v3 := Prog.lenBoundT (clr (mw 12)) v2
  let v4 := Prog.lenBoundT (cp (mw GS) (mw GSC)) v3
  let v5 := tmplB tX0 (tmpl31 N K k c.d) v4
  let v6 := tmOut c M31 v5
  let v7 := Prog.lenBoundT (copiesP 0) v6
  let v8 := tmplB tX0 (stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c)) v7
  let v9 := Prog.lenBoundT (clr tX0) v8
  let v10 := Function.update v9 (mw OB) (v9 (mw OB) + 1)
  Function.update v10 (mw ZB) (v10 (mw ZB) + 1)

/-- The steps of `prepTS`. -/
def tTS (β0 : Fin 256 → ℕ) (M31 : ℕ) : ℕ :=
  let v1 := Prog.lenBoundT (cp (mw GSC) (mw GS)) β0
  let v2 := ccVS W Ic v1
  let v3 := Prog.lenBoundT (clr (mw 12)) v2
  let v4 := Prog.lenBoundT (cp (mw GS) (mw GSC)) v3
  let v5 := tmplB tX0 (tmpl31 N K k c.d) v4
  let v6 := tmOut c M31 v5
  let v7 := Prog.lenBoundT (copiesP 0) v6
  let v8 := tmplB tX0 (stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c)) v7
  let v9 := Prog.lenBoundT (clr tX0) v8
  let v10 := Function.update v9 (mw OB) (v9 (mw OB) + 1)
  Prog.timeBoundT (cp (mw GSC) (mw GS)) β0 + (ccTS W Ic v1 + (Prog.timeBoundT (clr (mw 12)) v2 +
    (Prog.timeBoundT (cp (mw GS) (mw GSC)) v3 + (tmplTT tX0 (tmpl31 N K k c.d) v4 +
    ((2 * M31 + 3) * simTmplSweeps N K k + (Prog.timeBoundT (copiesP 0) v6 +
    (tmplTT tX0 (stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c)) v7 +
    (Prog.timeBoundT (clr tX0) v8 + ((1 + 1) * (2 * (supB v9 + 1 + 1) + 3) +
      (1 + 1) * (2 * (supB v10 + 1 + 1) + 3))))))))))

/-- **The phase of `prepTS`.** -/
theorem ph_prepTS (β0 : Fin 256 → ℕ) (M31 : ℕ)
    (hin : (fun j => tmplB tX0 (tmpl31 N K k c.d) (Prog.lenBoundT (cp (mw GS) (mw GSC))
      (Prog.lenBoundT (clr (mw 12)) (ccVS W Ic (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0)))) (tm31 j)) ≤
      Sym.bnd (tmVars M31 N K k (lenA N K k c.d)) σTmF)
    (htop : ∀ j, tmplB tX0 (tmpl31 N K k c.d) (Prog.lenBoundT (cp (mw GS) (mw GSC))
      (Prog.lenBoundT (clr (mw 12)) (ccVS W Ic (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0)))) (tm31 j) ≤ M31) :
    Ph (prepTS hk c Ic W) β0 (tTS hk c W Ic β0 M31) (vTS hk c W Ic β0 M31) := by
  have k31 : ∀ x ∈ tmpl31 N K k c.d, x.1 ≠ tX0 := ne_of_keys (keys_tmpl31 N K k c.d) (by decide)
  have kT : ∀ x ∈ stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c),
      x.1 ≠ tX0 := ne_of_keys (keys_T N K k c.d W _ _ _) (by decide)
  exact (ph_prog _ β0).seq <| ph_cntS_seq W Ic <| (ph_prog _ _).seq <| (ph_prog _ _).seq <|
    (ph_tmplP tX0 _ _ k31).seq <| (ph_tm c M31 _ hin htop).seq <| (ph_prog _ _).seq <|
    (ph_tmplP tX0 _ _ kT).seq <| (ph_prog _ _).seq <| (ph_putW _ _ _).seq (ph_putW _ _ _)

/-- The bounds after `prepGS`, step by step. -/
def vGS (β0 : Fin 256 → ℕ) (M31 : ℕ) : Fin 256 → ℕ :=
  let v1 := Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0
  let v2 := ccVS W Ic v1
  let v3 := Prog.lenBoundT (clr (mw 12)) v2
  let v4 := Prog.lenBoundT (cp (mw GS) (mw GSC)) v3
  let v5 := tmplB tX0 (tmpl31 N K k c.d) v4
  let v6 := tmOut c M31 v5
  let v7 := Prog.lenBoundT (copiesP 1) v6
  let v8 := tmplB tX0 (stepG N K k c.d ++ wordsG N K k c.d W (offPsi hk c) (offR hk c)
    (offPsi hk c + nA * lenPsi N K k)) v7
  Prog.lenBoundT (clr (ms 92)) (Prog.lenBoundT (clr tX0) v8)

/-- The steps of `prepGS`. -/
def tGS (β0 : Fin 256 → ℕ) (M31 : ℕ) : ℕ :=
  let v1 := Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0
  let v2 := ccVS W Ic v1
  let v3 := Prog.lenBoundT (clr (mw 12)) v2
  let v4 := Prog.lenBoundT (cp (mw GS) (mw GSC)) v3
  let v5 := tmplB tX0 (tmpl31 N K k c.d) v4
  let v6 := tmOut c M31 v5
  let v7 := Prog.lenBoundT (copiesP 1) v6
  let v8 := tmplB tX0 (stepG N K k c.d ++ wordsG N K k c.d W (offPsi hk c) (offR hk c)
    (offPsi hk c + nA * lenPsi N K k)) v7
  Prog.timeBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0 + (ccTS W Ic v1 +
    (Prog.timeBoundT (clr (mw 12)) v2 + (Prog.timeBoundT (cp (mw GS) (mw GSC)) v3 +
    (tmplTT tX0 (tmpl31 N K k c.d) v4 + ((2 * M31 + 3) * simTmplSweeps N K k +
    (Prog.timeBoundT (copiesP 1) v6 + (tmplTT tX0 (stepG N K k c.d ++ wordsG N K k c.d W
      (offPsi hk c) (offR hk c) (offPsi hk c + nA * lenPsi N K k)) v7 +
    (Prog.timeBoundT (clr tX0) v8 + Prog.timeBoundT (clr (ms 92)) (Prog.lenBoundT (clr tX0) v8)))))))))

/-- **The phase of `prepGS`.** -/
theorem ph_prepGS (β0 : Fin 256 → ℕ) (M31 : ℕ)
    (hin : (fun j => tmplB tX0 (tmpl31 N K k c.d) (Prog.lenBoundT (cp (mw GS) (mw GSC))
      (Prog.lenBoundT (clr (mw 12)) (ccVS W Ic (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0))))
        (tm31 j)) ≤ Sym.bnd (tmVars M31 N K k (lenA N K k c.d)) σTmF)
    (htop : ∀ j, tmplB tX0 (tmpl31 N K k c.d) (Prog.lenBoundT (cp (mw GS) (mw GSC))
      (Prog.lenBoundT (clr (mw 12)) (ccVS W Ic (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0))))
        (tm31 j) ≤ M31) :
    Ph (prepGS hk c Ic W) β0 (tGS hk c W Ic β0 M31) (vGS hk c W Ic β0 M31) := by
  have k31 : ∀ x ∈ tmpl31 N K k c.d, x.1 ≠ tX0 := ne_of_keys (keys_tmpl31 N K k c.d) (by decide)
  have kG : ∀ x ∈ stepG N K k c.d ++ wordsG N K k c.d W (offPsi hk c) (offR hk c)
      (offPsi hk c + nA * lenPsi N K k), x.1 ≠ tX0 :=
    ne_of_keys (keys_G N K k c.d W _ _ _) (by decide)
  exact (ph_prog _ β0).seq <| ph_cntS_seq W Ic <| (ph_prog _ _).seq <| (ph_prog _ _).seq <|
    (ph_tmplP tX0 _ _ k31).seq <| (ph_tm c M31 _ hin htop).seq <| (ph_prog _ _).seq <|
    (ph_tmplP tX0 _ _ kG).seq ((ph_prog _ _).seq (ph_prog _ _))

/-! ### The body and the block -/

theorem ph_wfBodyS {β0 β1 β1' β2 β3 β3' β4 β5 β6 β7 : Fin 256 → ℕ} {T1 T2 T3 T4 T5 T6 T7 : ℕ}
    (h1 : Ph (prepTS hk c Ic W) β0 T1 β1) (g1 : β1 ≤ β1') (h2 : Ph runTR β1' T2 β2)
    (h3 : Ph (prepGS hk c Ic W) β2 T3 β3) (g3 : β3 ≤ β3') (h4 : Ph runGR β3' T4 β4)
    (h5 : Ph (keyPrep N K k c.d) β4 T5 β5)
    (h6 : Ph (.frame (ValVM.mkE oK2 oK2_inj) (.prog SigabaNeo.Tape.Prog.simKeyP)) β5 T6 β6)
    (h7 : Ph (.prog (clrsP finClr)) β6 T7 β7) :
    Ph (wfBodyS hk c Ic W) β0 (T1 + (T2 + (T3 + (T4 + (T5 + (T6 + T7)))))) β7 := by
  have h2' : Ph runTR β1 T2 β2 := fun ℓ hℓ => h2 ℓ (hℓ.trans g1)
  have h4' : Ph runGR β3 T4 β4 := fun ℓ hℓ => h4 ℓ (hℓ.trans g3)
  unfold wfBodyS
  exact ph_wfBody_aux h1 h2' h3 h4' h5 h6 h7

/-- **The phase of the block**, from the phase of its body on the input in the machine's
coordinates. -/
theorem ph_wfB2S {β : Fin 256 → ℕ} {T : ℕ} {β' : Fin 256 → ℕ}
    (h : Ph (wfBodyS hk c Ic W) (fun j => β (eW j)) T β') :
    Ph (wfB2S hk c Ic W) β T (embedF eW β β') := by
  rw [wfB2S]; exact ph_frame eW h

/-! ### The bounds with explicit parameters -/

/-- The bounds after `prepTS` with explicit parameters. -/
def vTSn (N K k d W Ic : ℕ) (lw : List (Fin 256 × ℕ)) (β0 : Fin 256 → ℕ) (M31 : ℕ) :
    Fin 256 → ℕ :=
  let v1 := Prog.lenBoundT (cp (mw GSC) (mw GS)) β0
  let v2 := ccVS W Ic v1
  let v3 := Prog.lenBoundT (clr (mw 12)) v2
  let v4 := Prog.lenBoundT (cp (mw GS) (mw GSC)) v3
  let v5 := tmplB tX0 (tmpl31 N K k d) v4
  let v6 := tmOutN N K k d M31 v5
  let v7 := Prog.lenBoundT (copiesP 0) v6
  let v8 := tmplB tX0 (stepT N K k d ++ lw) v7
  let v9 := Prog.lenBoundT (clr tX0) v8
  let v10 := Function.update v9 (mw OB) (v9 (mw OB) + 1)
  Function.update v10 (mw ZB) (v10 (mw ZB) + 1)

/-- The bounds after `prepGS` with explicit parameters. -/
def vGSn (N K k d W Ic : ℕ) (lw : List (Fin 256 × ℕ)) (β0 : Fin 256 → ℕ) (M31 : ℕ) :
    Fin 256 → ℕ :=
  let v1 := Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0
  let v2 := ccVS W Ic v1
  let v3 := Prog.lenBoundT (clr (mw 12)) v2
  let v4 := Prog.lenBoundT (cp (mw GS) (mw GSC)) v3
  let v5 := tmplB tX0 (tmpl31 N K k d) v4
  let v6 := tmOutN N K k d M31 v5
  let v7 := Prog.lenBoundT (copiesP 1) v6
  let v8 := tmplB tX0 (stepG N K k d ++ lw) v7
  Prog.lenBoundT (clr (ms 92)) (Prog.lenBoundT (clr tX0) v8)

theorem vTS_le (β0 : Fin 256 → ℕ) (M31 : ℕ) (lw : List (Fin 256 × ℕ))
    (hl : TLe (wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c)) lw) :
    vTS hk c W Ic β0 M31 ≤ vTSn N K k c.d W Ic lw β0 M31 := by
  simp only [vTS, vTSn]
  have hm := tmplB_mono tX0 _ _ (TLe_append (TLe_refl (stepT N K k c.d)) hl) (le_refl
    (Prog.lenBoundT (copiesP 0) (tmOut c M31 (tmplB tX0 (tmpl31 N K k c.d)
      (Prog.lenBoundT (cp (mw GS) (mw GSC)) (Prog.lenBoundT (clr (mw 12))
        (ccVS W Ic (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0))))))))
  intro t
  have h9 := Prog.lenBoundT_mono (clr tX0) hm
  by_cases e1 : t = mw ZB
  · subst e1
    rw [Function.update_self, Function.update_self, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]
    exact Nat.add_le_add_right (h9 _) 1
  · rw [Function.update_of_ne e1, Function.update_of_ne e1]
    by_cases e2 : t = mw OB
    · subst e2
      rw [Function.update_self, Function.update_self]
      exact Nat.add_le_add_right (h9 _) 1
    · rw [Function.update_of_ne e2, Function.update_of_ne e2]
      exact h9 t

theorem vGS_le (β0 : Fin 256 → ℕ) (M31 : ℕ) (lw : List (Fin 256 × ℕ))
    (hl : TLe (wordsG N K k c.d W (offPsi hk c) (offR hk c) (offPsi hk c + nA * lenPsi N K k)) lw) :
    vGS hk c W Ic β0 M31 ≤ vGSn N K k c.d W Ic lw β0 M31 := by
  simp only [vGS, vGSn]
  exact Prog.lenBoundT_mono _ (Prog.lenBoundT_mono _
    (tmplB_mono tX0 _ _ (TLe_append (TLe_refl _) hl) le_rfl))

/-! ### The steps of the preparations -/

set_option maxHeartbeats 2000000 in
/-- **The steps of `prepTS`**, below a uniform bound of its intermediate tapes. -/
theorem tTS_le (β0 : Fin 256 → ℕ) (M31 M : ℕ) (h0 : ∀ t, β0 t ≤ M)
    (h2 : ∀ t, ccVS W Ic (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0) t ≤ M)
    (h6 : ∀ t, tmOut c M31 (tmplB tX0 (tmpl31 N K k c.d) (Prog.lenBoundT (cp (mw GS) (mw GSC))
      (Prog.lenBoundT (clr (mw 12)) (ccVS W Ic (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0))))) t ≤ M)
    (h31 : ∀ x ∈ tmpl31 N K k c.d, x.2 ≤ M)
    (hl : ∀ x ∈ stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c), x.2 ≤ M) :
    tTS hk c W Ic β0 M31 ≤ ccTS W Ic (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0) +
      (2 * M31 + 3) * simTmplSweeps N K k + 90 * uT (M + 6) := by
  set v1 := Prog.lenBoundT (cp (mw GSC) (mw GS)) β0
  set v2 := ccVS W Ic v1
  set v3 := Prog.lenBoundT (clr (mw 12)) v2
  set v4 := Prog.lenBoundT (cp (mw GS) (mw GSC)) v3
  set v5 := tmplB tX0 (tmpl31 N K k c.d) v4
  set v6 := tmOut c M31 v5
  set v7 := Prog.lenBoundT (copiesP 0) v6
  set v8 := tmplB tX0 (stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c)) v7
  set v9 := Prog.lenBoundT (clr tX0) v8
  set v10 := Function.update v9 (mw OB) (v9 (mw OB) + 1)
  have h3 : ∀ t, v3 t ≤ M := Sym.lenBoundT_le_const (clr (mw 12)) rfl h2
  have h4 : ∀ t, v4 t ≤ M := Sym.lenBoundT_le_const (cp (mw GS) (mw GSC)) rfl h3
  have h7 : ∀ t, v7 t ≤ M := Sym.lenBoundT_le_const (copiesP 0) rfl h6
  have h8 : ∀ t, v8 t ≤ M := tmplB_le tX0 M _ v7 h7 hl
  have h9 : ∀ t, v9 t ≤ M := Sym.lenBoundT_le_const (clr tX0) rfl h8
  have h10 : ∀ t, v10 t ≤ M + 1 := fun t => by
    simp only [v10, Function.update_apply]; split_ifs
    · have := h9 (mw OB); omega
    · have := h9 t; omega
  show Prog.timeBoundT (cp (mw GSC) (mw GS)) β0 + (ccTS W Ic v1 + (Prog.timeBoundT (clr (mw 12)) v2 +
    (Prog.timeBoundT (cp (mw GS) (mw GSC)) v3 + (tmplTT tX0 (tmpl31 N K k c.d) v4 +
    ((2 * M31 + 3) * simTmplSweeps N K k + (Prog.timeBoundT (copiesP 0) v6 +
    (tmplTT tX0 (stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c)) v7 +
    (Prog.timeBoundT (clr tX0) v8 + ((1 + 1) * (2 * (supB v9 + 1 + 1) + 3) +
      (1 + 1) * (2 * (supB v10 + 1 + 1) + 3)))))))))) ≤ _
  have a : Prog.timeBoundT (cp (mw GSC) (mw GS)) β0 ≤ 2 * M + 7 := tb_prim _ β0 M h0
  have b : Prog.timeBoundT (clr (mw 12)) v2 ≤ 2 * M + 7 := tb_prim _ v2 M h2
  have c' : Prog.timeBoundT (cp (mw GS) (mw GSC)) v3 ≤ 2 * M + 7 := tb_prim _ v3 M h3
  have d := tmplTT_le tX0 M _ v4 h4 h31
  have e := timeBoundT_le_pcount (copiesP 0) ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
    v6 h6
  have f := tmplTT_le tX0 M _ v7 h7 hl
  have g : Prog.timeBoundT (clr tX0) v8 ≤ 2 * M + 7 := tb_prim _ v8 M h8
  have s9 := supB_le_of h9
  have s10 := supB_le_of h10
  have l31 : (tmpl31 N K k c.d).length = 8 := rfl
  have lT : (stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c)).length = 60 := rfl
  have pc : pcount (copiesP 0) = 6 := rfl
  rw [l31] at d
  rw [lT] at f
  rw [pc] at e
  have u1 : uT M ≤ uT (M + 6) := by simp only [uT]; nlinarith
  have u2 : 2 * M + 7 ≤ uT (M + 6) := (le_uT M).trans u1
  have u3 : 6 * (2 * (M + 6) + 5) ≤ 6 * uT (M + 6) := by simp only [uT]; nlinarith
  have u4 : (1 + 1) * (2 * (supB v9 + 1 + 1) + 3) ≤ uT (M + 6) := by simp only [uT]; nlinarith
  have u5 : (1 + 1) * (2 * (supB v10 + 1 + 1) + 3) ≤ uT (M + 6) := by simp only [uT]; nlinarith
  have hd : (8 + 1) * uT M ≤ 9 * uT (M + 6) := by nlinarith
  have hf : (60 + 1) * uT M ≤ 61 * uT (M + 6) := by nlinarith
  have hd' : (8 + 1) * ((2 * M + 1) * (4 * M + 12)) ≤ 9 * uT (M + 6) := hd
  have hf' : (60 + 1) * ((2 * M + 1) * (4 * M + 12)) ≤ 61 * uT (M + 6) := hf
  generalize (2 * M + 1) * (4 * M + 12) = P at d f hd' hf'
  generalize uT (M + 6) = U at *
  omega

set_option maxHeartbeats 2000000 in
/-- **The steps of `prepGS`**, below a uniform bound of its intermediate tapes. -/
theorem tGS_le (β0 : Fin 256 → ℕ) (M31 M : ℕ) (h0 : ∀ t, β0 t ≤ M)
    (h2 : ∀ t, ccVS W Ic (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0) t ≤ M)
    (h6 : ∀ t, tmOut c M31 (tmplB tX0 (tmpl31 N K k c.d) (Prog.lenBoundT (cp (mw GS) (mw GSC))
      (Prog.lenBoundT (clr (mw 12)) (ccVS W Ic (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC))
        β0))))) t ≤ M)
    (h31 : ∀ x ∈ tmpl31 N K k c.d, x.2 ≤ M)
    (hl : ∀ x ∈ stepG N K k c.d ++ wordsG N K k c.d W (offPsi hk c) (offR hk c)
      (offPsi hk c + nA * lenPsi N K k), x.2 ≤ M) :
    tGS hk c W Ic β0 M31 ≤ ccTS W Ic (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0) +
      (2 * M31 + 3) * simTmplSweeps N K k + 120 * uT (M + 40) := by
  set v1 := Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0
  set v2 := ccVS W Ic v1
  set v3 := Prog.lenBoundT (clr (mw 12)) v2
  set v4 := Prog.lenBoundT (cp (mw GS) (mw GSC)) v3
  set v5 := tmplB tX0 (tmpl31 N K k c.d) v4
  set v6 := tmOut c M31 v5
  set v7 := Prog.lenBoundT (copiesP 1) v6
  set v8 := tmplB tX0 (stepG N K k c.d ++ wordsG N K k c.d W (offPsi hk c) (offR hk c)
    (offPsi hk c + nA * lenPsi N K k)) v7
  have h3 : ∀ t, v3 t ≤ M := Sym.lenBoundT_le_const (clr (mw 12)) rfl h2
  have h4 : ∀ t, v4 t ≤ M := Sym.lenBoundT_le_const (cp (mw GS) (mw GSC)) rfl h3
  have h7 : ∀ t, v7 t ≤ M := Sym.lenBoundT_le_const (copiesP 1) rfl h6
  have h8 : ∀ t, v8 t ≤ M := tmplB_le tX0 M _ v7 h7 hl
  have h9 : ∀ t, Prog.lenBoundT (clr tX0) v8 t ≤ M := Sym.lenBoundT_le_const (clr tX0) rfl h8
  show Prog.timeBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0 + (ccTS W Ic v1 +
    (Prog.timeBoundT (clr (mw 12)) v2 + (Prog.timeBoundT (cp (mw GS) (mw GSC)) v3 +
    (tmplTT tX0 (tmpl31 N K k c.d) v4 + ((2 * M31 + 3) * simTmplSweeps N K k +
    (Prog.timeBoundT (copiesP 1) v6 + (tmplTT tX0 (stepG N K k c.d ++ wordsG N K k c.d W
      (offPsi hk c) (offR hk c) (offPsi hk c + nA * lenPsi N K k)) v7 +
    (Prog.timeBoundT (clr tX0) v8 + Prog.timeBoundT (clr (ms 92)) (Prog.lenBoundT (clr tX0) v8))))))))) ≤ _
  have a := timeBoundT_le_pcount (clrsP lowW ⨾ cp (mw GS) (mw GSC)) ⟨loopFree_clrsP _, trivial⟩ β0 h0
  have pa : pcount (clrsP lowW ⨾ cp (mw GS) (mw GSC)) = 34 := by
    simp only [pcount, pcount_clrsP]; rfl
  rw [pa] at a
  have b : Prog.timeBoundT (clr (mw 12)) v2 ≤ 2 * M + 7 := tb_prim _ v2 M h2
  have c' : Prog.timeBoundT (cp (mw GS) (mw GSC)) v3 ≤ 2 * M + 7 := tb_prim _ v3 M h3
  have d := tmplTT_le tX0 M _ v4 h4 h31
  have e := timeBoundT_le_pcount (copiesP 1) ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
    v6 h6
  have f := tmplTT_le tX0 M _ v7 h7 hl
  have g : Prog.timeBoundT (clr tX0) v8 ≤ 2 * M + 7 := tb_prim _ v8 M h8
  have g' : Prog.timeBoundT (clr (ms 92)) (Prog.lenBoundT (clr tX0) v8) ≤ 2 * M + 7 :=
    tb_prim _ _ M h9
  have l31 : (tmpl31 N K k c.d).length = 8 := rfl
  have lG : (stepG N K k c.d ++ wordsG N K k c.d W (offPsi hk c) (offR hk c)
    (offPsi hk c + nA * lenPsi N K k)).length = 46 := rfl
  have pc : pcount (copiesP 1) = 6 := rfl
  rw [l31] at d
  rw [lG] at f
  rw [pc] at e
  have u1 : uT M ≤ uT (M + 40) := by simp only [uT]; nlinarith
  have u2 : 2 * M + 7 ≤ uT (M + 40) := (le_uT M).trans u1
  have u3 : 6 * (2 * (M + 6) + 5) ≤ 6 * uT (M + 40) := by simp only [uT]; nlinarith
  have u0 : 34 * (2 * (M + 34) + 5) ≤ 34 * uT (M + 40) := by simp only [uT]; nlinarith
  have hd' : (8 + 1) * ((2 * M + 1) * (4 * M + 12)) ≤ 9 * uT (M + 40) := by
    have : (2 * M + 1) * (4 * M + 12) = uT M := rfl
    rw [this]; nlinarith
  have hf' : (46 + 1) * ((2 * M + 1) * (4 * M + 12)) ≤ 47 * uT (M + 40) := by
    have : (2 * M + 1) * (4 * M + 12) = uT M := rfl
    rw [this]; nlinarith
  generalize (2 * M + 1) * (4 * M + 12) = P at d f hd' hf'
  generalize uT (M + 40) = U at *
  omega

end WB2

end AdvancedEncryption.RingBTVW.Prog
