import PE.Impl.DualUse.Prog.WfB2
import SigabaNeo.Lib.Lattices.ProgAlgo.ValCost
import SigabaNeo.Lib.Machines.Prog.PhaseB
import SigabaNeo.Lib.Lattices.ProgAlgo.SimStepGT

/-!
# The time of the block-structured `W_f` block

Per-tape bounds of the phases of `wfBody` (`XProg.Ph`): the preparations by their primitives and
templates (`ph_tmplP`, `ph_putW`), the runs of the machine by `inv_compileA` with static word
bounds, the key sum by `boundsT_simKeyP`.
-/

namespace AdvancedEncryption.DualUse.Prog

set_option maxRecDepth 100000

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

/-! ### Templates and literals -/

section Tmpl

variable {n : ℕ}

/-- The bounds after the templates `l` (counter `c`). -/
def tmplB (c : Fin n) : List (Fin n × ℕ) → (Fin n → ℕ) → (Fin n → ℕ)
  | [], β => β
  | x :: l, β => tmplB c l (natB x.1 c x.2 β)

/-- The steps of the templates `l`. -/
def tmplTT (c : Fin n) : List (Fin n × ℕ) → (Fin n → ℕ) → ℕ
  | [], β => 2 * (supB β + 1) + 3
  | x :: l, β => (2 * x.2 + 1) * (4 * max (supB β) x.2 + 12) + tmplTT c l (natB x.1 c x.2 β)

theorem ph_tmplP (c : Fin n) : ∀ (l : List (Fin n × ℕ)) (β : Fin n → ℕ), (∀ x ∈ l, x.1 ≠ c) →
    Ph (tmplP c l) β (tmplTT c l β) (tmplB c l β)
  | [], β, _ => by
    refine (ph_prim (.copy c c) β).mono le_rfl le_rfl (fun t => ?_)
    simp only [Prim.lenT, tmplB, Function.update_apply]
    split_ifs with h <;> simp [h]
  | x :: l, β, hl => (ph_natP (Ne.symm (hl x (by simp))) x.2 β).seq
      (ph_tmplP c l _ (fun y hy => hl y (by simp [hy])))

/-- The literal `w` appended to `t`. -/
theorem ph_putW (t : Fin n) : ∀ (w : List Bool) (β : Fin n → ℕ),
    Ph (putW t w) β ((w.length + 1) * (2 * (supB β + w.length + 1) + 3))
      (Function.update β t (β t + w.length))
  | [], β => by
    refine (ph_prim (.copy t t) β).mono le_rfl (by simp) (fun i => ?_)
    simp only [Prim.lenT, Function.update_apply]
    split_ifs with h <;> simp [h]
  | b :: w, β => by
    refine ((ph_prim (.snoc t b) β).seq (ph_putW t w _)).mono le_rfl ?_ (fun i => ?_)
    · simp only [Prim.lenT, List.length_cons]
      have : supB (Function.update β t (β t + 1)) ≤ supB β + 1 :=
        supB_le_of fun i => by
          by_cases h : i = t
          · subst h; simp only [Function.update_self]; exact Nat.add_le_add_right (le_supB β _) 1
          · rw [Function.update_of_ne h]; exact (le_supB β i).trans (Nat.le_succ _)
      nlinarith
    · simp only [Prim.lenT, List.length_cons]
      by_cases h : i = t
      · subst h; simp only [Function.update_self]; omega
      · simp only [Function.update_of_ne h]; exact le_rfl

end Tmpl

/-! ### The preparation of the run of `f̂` -/

namespace WB2

open SigabaNeo.Tape.ValVM SigabaNeo.Tape.Prog SigabaNeo.Tape.Prog.KST

/-- The certificate of `simTmplP` on all its tapes. -/
def σTmF : Sym.Asg := σTm ++ List.replicate 19 []
def σTmF' : Sym.Asg := σTm' ++ [[], [], [], q 1 [0, 1], q 1 [1], [], q 1 [0, 1], [], [], [], [], [], [],
  [], q 1 [0, 1], [], [], [], []]

theorem check_simTmplF : Sym.check 8 simTmplP σTmF σTmF' wTm = true := by decide +kernel

theorem length_σTmF' : σTmF'.length = 31 := rfl

/-- `countP` as a phase. -/
theorem ph_countP (m S O Y Z Q : ℕ) :
    Ph (.prog (Prog.countP m)) ![S, O, Y, Z, Q] (Prog.countT m S (S + O + Y + Z + Q + m))
      ![S, O + S, max Y (m - 1), 0, S] := fun ℓ hℓ => by
  obtain ⟨h1, h2⟩ := Prog.bounds_countP m S O Y Z Q ℓ hℓ
  exact ⟨h2, h1⟩

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (W : ℕ)

/-- The bounds of the frame of `countP` from `β`. -/
def cntIn (β : Fin 256 → ℕ) : Fin 5 → ℕ := ![β (mw GS), β (mw GCNT), β (mw 1), β (mw 3), β (mw 4)]

/-- The bounds after `countP`. -/
def cntOut (W : ℕ) (β : Fin 256 → ℕ) : Fin 5 → ℕ :=
  ![β (mw GS), β (mw GCNT) + β (mw GS), max (β (mw 1)) (2 * W - 1), 0, β (mw GS)]

/-- The steps of `countP`. -/
def cntT (W : ℕ) (β : Fin 256 → ℕ) : ℕ :=
  Prog.countT (2 * W) (β (mw GS)) (β (mw GS) + β (mw GCNT) + β (mw 1) + β (mw 3) + β (mw 4) + 2 * W)

theorem ph_cnt (β : Fin 256 → ℕ) :
    Ph (.frame (ValVM.mkE cntE cntE_inj) (.prog (Prog.countP (2 * W)))) β (cntT W β)
      (embedF (ValVM.mkE cntE cntE_inj) β (cntOut W β)) := by
  refine ph_frame _ ?_
  have h := ph_countP (2 * W) (β (mw GS)) (β (mw GCNT)) (β (mw 1)) (β (mw 3)) (β (mw 4))
  refine h.mono (fun j => ?_) le_rfl le_rfl
  fin_cases j <;> rfl

/-- The bounds after `simTmplP` (on the words `0 … 30`, with the top `M31`). -/
def tmOut (M31 : ℕ) (β : Fin 256 → ℕ) : Fin 256 → ℕ :=
  embedF (ValVM.mkE tm31 tm31_inj) β fun j =>
    Sym.pEval (tmVars M31 N K k (lenA N K k c.d)) (Sym.aGet σTmF' j.val)

theorem ph_tm (M31 : ℕ) (β : Fin 256 → ℕ)
    (hin : (fun j => β (tm31 j)) ≤ Sym.bnd (tmVars M31 N K k (lenA N K k c.d)) σTmF)
    (htop : ∀ j, β (tm31 j) ≤ M31) :
    Ph (.frame (ValVM.mkE tm31 tm31_inj) (.prog simTmplP)) β ((2 * M31 + 3) * simTmplSweeps N K k)
      (tmOut c M31 β) := by
  have h := ph_frame_check check_simTmplF (tmVars M31 N K k (lenA N K k c.d))
    (ValVM.mkE tm31 tm31_inj) β (tmOut c M31 β) hin htop length_σTmF'
    (fun j => by simp only [tmOut]; rw [embedF_apply_self])
    (fun t ht => by
      simp only [tmOut]
      rcases embedF_cases (ValVM.mkE tm31 tm31_inj) β _ t with ⟨_, h⟩ | ⟨j, hj, -⟩
      · rw [h]
      · exact absurd hj (ht j))
  have hw : Sym.pEval (tmVars M31 N K k (lenA N K k c.d)) wTm = simTmplSweeps N K k := by
    simp only [wTm, simTmplSweeps, Sym.pEval, Sym.mEval, tmVars, List.headD, List.tail]; ring
  rwa [show Sym.top (tmVars M31 N K k (lenA N K k c.d)) = M31 from rfl, hw] at h

/-- The bounds after `prepT`, step by step. -/
def vT (β0 : Fin 256 → ℕ) (M31 : ℕ) : Fin 256 → ℕ :=
  let v1 := Prog.lenBoundT (cp (mw GSC) (mw GS)) β0
  let v2 := embedF (ValVM.mkE cntE cntE_inj) v1 (cntOut W v1)
  let v3 := Prog.lenBoundT (clr (mw 12)) v2
  let v4 := Prog.lenBoundT (cp (mw GS) (mw GSC)) v3
  let v5 := tmplB tX0 (tmpl31 N K k c.d) v4
  let v6 := tmOut c M31 v5
  let v7 := Prog.lenBoundT (copiesP 0) v6
  let v8 := tmplB tX0 (stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c)) v7
  let v9 := Prog.lenBoundT (clr tX0) v8
  let v10 := Function.update v9 (mw OB) (v9 (mw OB) + 1)
  Function.update v10 (mw ZB) (v10 (mw ZB) + 1)

/-- The steps of `prepT`. -/
def tT (β0 : Fin 256 → ℕ) (M31 : ℕ) : ℕ :=
  let v1 := Prog.lenBoundT (cp (mw GSC) (mw GS)) β0
  let v2 := embedF (ValVM.mkE cntE cntE_inj) v1 (cntOut W v1)
  let v3 := Prog.lenBoundT (clr (mw 12)) v2
  let v4 := Prog.lenBoundT (cp (mw GS) (mw GSC)) v3
  let v5 := tmplB tX0 (tmpl31 N K k c.d) v4
  let v6 := tmOut c M31 v5
  let v7 := Prog.lenBoundT (copiesP 0) v6
  let v8 := tmplB tX0 (stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c)) v7
  let v9 := Prog.lenBoundT (clr tX0) v8
  let v10 := Function.update v9 (mw OB) (v9 (mw OB) + 1)
  Prog.timeBoundT (cp (mw GSC) (mw GS)) β0 + (cntT W v1 + (Prog.timeBoundT (clr (mw 12)) v2 +
    (Prog.timeBoundT (cp (mw GS) (mw GSC)) v3 + (tmplTT tX0 (tmpl31 N K k c.d) v4 +
    ((2 * M31 + 3) * simTmplSweeps N K k + (Prog.timeBoundT (copiesP 0) v6 +
    (tmplTT tX0 (stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c)) v7 +
    (Prog.timeBoundT (clr tX0) v8 + ((1 + 1) * (2 * (supB v9 + 1 + 1) + 3) +
      (1 + 1) * (2 * (supB v10 + 1 + 1) + 3))))))))))

/-- **The phase of `prepT`.** -/
theorem ph_prepT (β0 : Fin 256 → ℕ) (M31 : ℕ)
    (hin : (fun j => tmplB tX0 (tmpl31 N K k c.d) (Prog.lenBoundT (cp (mw GS) (mw GSC))
      (Prog.lenBoundT (clr (mw 12)) (embedF (ValVM.mkE cntE cntE_inj)
        (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0)
        (cntOut W (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0))))) (tm31 j)) ≤
      Sym.bnd (tmVars M31 N K k (lenA N K k c.d)) σTmF)
    (htop : ∀ j, tmplB tX0 (tmpl31 N K k c.d) (Prog.lenBoundT (cp (mw GS) (mw GSC))
      (Prog.lenBoundT (clr (mw 12)) (embedF (ValVM.mkE cntE cntE_inj)
        (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0)
        (cntOut W (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0))))) (tm31 j) ≤ M31) :
    Ph (prepT hk c W) β0 (tT hk c W β0 M31) (vT hk c W β0 M31) := by
  have k31 : ∀ x ∈ tmpl31 N K k c.d, x.1 ≠ tX0 := ne_of_keys (keys_tmpl31 N K k c.d) (by decide)
  have kT : ∀ x ∈ stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c),
      x.1 ≠ tX0 := ne_of_keys (keys_T N K k c.d W _ _ _) (by decide)
  exact (ph_prog _ β0).seq <| (ph_cnt W _).seq <| (ph_prog _ _).seq <| (ph_prog _ _).seq <|
    (ph_tmplP tX0 _ _ k31).seq <| (ph_tm c M31 _ hin htop).seq <| (ph_prog _ _).seq <|
    (ph_tmplP tX0 _ _ kT).seq <| (ph_prog _ _).seq <| (ph_putW _ _ _).seq (ph_putW _ _ _)

end WB2

/-! ### The runs of the machine -/

namespace WB2

open SigabaNeo.Tape.ValVM SigabaNeo.Tape.Prog SigabaNeo.Tape.Prog.StepT

/-- The bounds of the step's tapes for the run of `f̂` (`σSt2` at `N K k d`). -/
def bsT (N K k d : ℕ) : Fin 132 → ℕ := Sym.bnd [0, N, K, k, d] σSt2

/-- The bounds of the step's tapes for the predicate's run. -/
def bsG (N K k d : ℕ) : Fin 132 → ℕ := Sym.bnd [0, N, K, k, d] σStG2

/-- **The phase of the run of `f̂`**, from the abstract interpreter. -/
theorem ph_runT (N K k d Ms fuel : ℕ) (L L' : List ℕ) (T : ℕ) (hL : L.length = 120)
    (hV1 : VT N K k d ≤ bsT N K k d 1) (hV2 : VT N K k d ≤ bsT N K k d 2)
    (hbs : ∀ t, bsT N K k d t ≤ Ms) (hVM : VT N K k d ≤ Ms)
    (habs : absC (bsT N K k d) (VT N K k d) (Sym.pEval [0, N, K, k, d] cStep2) Ms fuel fhatFullC L =
      some (L', T)) :
    Ph runT (encB (bsT N K k d) (VT N K k d) (gB L)) T (encB (bsT N K k d) (VT N K k d) (gB L')) := by
  have hx := xsound_simStepP [0, N, K, k, d] trivial
  exact absC_sound (nocert _) _ _ _ _ hV1 hV2 (fun ℓ hℓ => (hx ℓ hℓ).2)
    (fun ℓ hℓ => (hx ℓ hℓ).1.trans fun t => Sym.aLe_spec _ aLe_out_top t.val)
    hbs hVM fuel fhatFullC L L' T hL habs

/-- **The phase of the predicate's run.** -/
theorem ph_runG (N K k d Ms fuel : ℕ) (L L' : List ℕ) (T : ℕ) (hL : L.length = 120)
    (hV1 : VG N K k d ≤ bsG N K k d 1) (hV2 : VG N K k d ≤ bsG N K k d 2)
    (hbs : ∀ t, bsG N K k d t ≤ Ms) (hVM : VG N K k d ≤ Ms)
    (habs : absC (bsG N K k d) (VG N K k d) (Sym.pEval [0, N, K, k, d] cStepG2) Ms fuel gswFullC L =
      some (L', T)) :
    Ph runG (encB (bsG N K k d) (VG N K k d) (gB L)) T (encB (bsG N K k d) (VG N K k d) (gB L')) := by
  have hx := xsound_simStepG [0, N, K, k, d] trivial
  exact absC_sound (nocert _) _ _ _ _ hV1 hV2 (fun ℓ hℓ => (hx ℓ hℓ).2)
    (fun ℓ hℓ => (hx ℓ hℓ).1.trans fun t => Sym.aLe_spec _ aLe_out_gsw t.val)
    hbs hVM fuel gswFullC L L' T hL habs

end WB2

/-! ### The preparation of the predicate's run, the key sum, the cleanup -/

namespace WB2

open SigabaNeo.Tape.ValVM SigabaNeo.Tape.Prog SigabaNeo.Tape.Prog.KST

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (W : ℕ)

/-- The bounds after `prepG`, step by step. -/
def vG (β0 : Fin 256 → ℕ) (M31 : ℕ) : Fin 256 → ℕ :=
  let v1 := Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0
  let v2 := embedF (ValVM.mkE cntE cntE_inj) v1 (cntOut W v1)
  let v3 := Prog.lenBoundT (clr (mw 12)) v2
  let v4 := Prog.lenBoundT (cp (mw GS) (mw GSC)) v3
  let v5 := tmplB tX0 (tmpl31 N K k c.d) v4
  let v6 := tmOut c M31 v5
  let v7 := Prog.lenBoundT (copiesP 1) v6
  let v8 := tmplB tX0 (stepG N K k c.d ++ wordsG N K k c.d W (offPsi hk c) (offR hk c)
    (offPsi hk c + 10 * lenPsi N K k)) v7
  Prog.lenBoundT (clr tX0) v8

/-- The steps of `prepG`. -/
def tG (β0 : Fin 256 → ℕ) (M31 : ℕ) : ℕ :=
  let v1 := Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0
  let v2 := embedF (ValVM.mkE cntE cntE_inj) v1 (cntOut W v1)
  let v3 := Prog.lenBoundT (clr (mw 12)) v2
  let v4 := Prog.lenBoundT (cp (mw GS) (mw GSC)) v3
  let v5 := tmplB tX0 (tmpl31 N K k c.d) v4
  let v6 := tmOut c M31 v5
  let v7 := Prog.lenBoundT (copiesP 1) v6
  let v8 := tmplB tX0 (stepG N K k c.d ++ wordsG N K k c.d W (offPsi hk c) (offR hk c)
    (offPsi hk c + 10 * lenPsi N K k)) v7
  Prog.timeBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0 + (cntT W v1 +
    (Prog.timeBoundT (clr (mw 12)) v2 + (Prog.timeBoundT (cp (mw GS) (mw GSC)) v3 +
    (tmplTT tX0 (tmpl31 N K k c.d) v4 + ((2 * M31 + 3) * simTmplSweeps N K k +
    (Prog.timeBoundT (copiesP 1) v6 + (tmplTT tX0 (stepG N K k c.d ++ wordsG N K k c.d W
      (offPsi hk c) (offR hk c) (offPsi hk c + 10 * lenPsi N K k)) v7 +
    Prog.timeBoundT (clr tX0) v8)))))))

/-- **The phase of `prepG`.** -/
theorem ph_prepG (β0 : Fin 256 → ℕ) (M31 : ℕ)
    (hin : (fun j => tmplB tX0 (tmpl31 N K k c.d) (Prog.lenBoundT (cp (mw GS) (mw GSC))
      (Prog.lenBoundT (clr (mw 12)) (embedF (ValVM.mkE cntE cntE_inj)
        (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0)
        (cntOut W (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0))))) (tm31 j)) ≤
      Sym.bnd (tmVars M31 N K k (lenA N K k c.d)) σTmF)
    (htop : ∀ j, tmplB tX0 (tmpl31 N K k c.d) (Prog.lenBoundT (cp (mw GS) (mw GSC))
      (Prog.lenBoundT (clr (mw 12)) (embedF (ValVM.mkE cntE cntE_inj)
        (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0)
        (cntOut W (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0))))) (tm31 j) ≤ M31) :
    Ph (prepG hk c W) β0 (tG hk c W β0 M31) (vG hk c W β0 M31) := by
  have k31 : ∀ x ∈ tmpl31 N K k c.d, x.1 ≠ tX0 := ne_of_keys (keys_tmpl31 N K k c.d) (by decide)
  have kG : ∀ x ∈ stepG N K k c.d ++ wordsG N K k c.d W (offPsi hk c) (offR hk c)
      (offPsi hk c + 10 * lenPsi N K k), x.1 ≠ tX0 :=
    ne_of_keys (keys_G N K k c.d W _ _ _) (by decide)
  exact (ph_prog _ β0).seq <| (ph_cnt W _).seq <| (ph_prog _ _).seq <| (ph_prog _ _).seq <|
    (ph_tmplP tX0 _ _ k31).seq <| (ph_tm c M31 _ hin htop).seq <| (ph_prog _ _).seq <|
    (ph_tmplP tX0 _ _ kG).seq (ph_prog _ _)

/-- **The phase of the key sum's preparation.** -/
theorem ph_keyPrep (N K k d : ℕ) (β : Fin 256 → ℕ) :
    Ph (keyPrep N K k d) β
      (Prog.timeBoundT (clrsP keyClr) β + (tmplTT tX0 (keyT N K k d) (Prog.lenBoundT (clrsP keyClr) β) +
        (1 + 1) * (2 * (supB (tmplB tX0 (keyT N K k d) (Prog.lenBoundT (clrsP keyClr) β)) + 1 + 1) + 3)))
      (Function.update (tmplB tX0 (keyT N K k d) (Prog.lenBoundT (clrsP keyClr) β)) (ms 87)
        (tmplB tX0 (keyT N K k d) (Prog.lenBoundT (clrsP keyClr) β) (ms 87) + 1)) :=
  (ph_prog _ β).seq <| (ph_tmplP tX0 _ _ (ne_of_keys (keys_keyT N K k d) (by decide))).seq
    (ph_putW _ _ _)

/-- **The phase of the framed `simKeyP`.** -/
theorem ph_simKey (β : Fin 256 → ℕ) (M N K m k W V off Lst Lpos Lst₂ W' V' off' : ℕ)
    (hin : (fun j => β (oK2 j)) ≤ ℓSK M N K m k W V off Lst Lpos Lst₂ W' V' off')
    (hM : ∀ j, β (oK2 j) ≤ M) :
    Ph (.frame (ValVM.mkE oK2 oK2_inj) (.prog simKeyP)) β
      ((2 * M + 3) * simKeySweeps N K m k W V off W' V' off')
      (embedF (ValVM.mkE oK2 oK2_inj) β fun j => if j = 0 then m * (2 * k) * (N * K) else M) := by
  refine ph_frame _ fun ℓ hℓ => ?_
  obtain ⟨h0, h1, h2⟩ := boundsT_simKeyP M N K m k W V off Lst Lpos Lst₂ W' V' off'
    (hℓ.trans hin) (fun t => (hℓ t).trans (hM t))
  refine ⟨h2, fun t => ?_⟩
  by_cases ht : t = 0
  · subst ht; simp only [if_true]; exact h0
  · simp only [if_neg ht]; exact h1 t

/-- **The phase of the final cleanup.** -/
theorem ph_finClr (β : Fin 256 → ℕ) :
    Ph (.prog (clrsP finClr)) β (Prog.timeBoundT (clrsP finClr) β)
      (Prog.lenBoundT (clrsP finClr) β) := ph_prog _ β

end WB2

/-! ### The body and the block -/

namespace WB2

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (W : ℕ)

/-- **The phase of the body**, from the phases of its parts and the bounds between them. -/
theorem ph_wfBody_aux {X1 X2 X3 X4 X5 X6 X7 : XProg 256}
    {β0 β1 β2 β3 β4 β5 β6 β7 : Fin 256 → ℕ} {T1 T2 T3 T4 T5 T6 T7 : ℕ}
    (h1 : Ph X1 β0 T1 β1) (h2 : Ph X2 β1 T2 β2) (h3 : Ph X3 β2 T3 β3) (h4 : Ph X4 β3 T4 β4)
    (h5 : Ph X5 β4 T5 β5) (h6 : Ph X6 β5 T6 β6) (h7 : Ph X7 β6 T7 β7) :
    Ph (.seq X1 (.seq X2 (.seq X3 (.seq X4 (.seq X5 (.seq X6 X7)))))) β0
      (T1 + (T2 + (T3 + (T4 + (T5 + (T6 + T7)))))) β7 :=
  h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7)))))

theorem ph_wfBody {β0 β1 β1' β2 β3 β3' β4 β5 β6 β7 : Fin 256 → ℕ} {T1 T2 T3 T4 T5 T6 T7 : ℕ}
    (h1 : Ph (prepT hk c W) β0 T1 β1) (g1 : β1 ≤ β1') (h2 : Ph runT β1' T2 β2)
    (h3 : Ph (prepG hk c W) β2 T3 β3) (g3 : β3 ≤ β3') (h4 : Ph runG β3' T4 β4)
    (h5 : Ph (keyPrep N K k c.d) β4 T5 β5)
    (h6 : Ph (.frame (ValVM.mkE oK2 oK2_inj) (.prog SigabaNeo.Tape.Prog.simKeyP)) β5 T6 β6)
    (h7 : Ph (.prog (clrsP finClr)) β6 T7 β7) :
    Ph (wfBody hk c W) β0 (T1 + (T2 + (T3 + (T4 + (T5 + (T6 + T7)))))) β7 := by
  have h2' : Ph runT β1 T2 β2 := fun ℓ hℓ => h2 ℓ (hℓ.trans g1)
  have h4' : Ph runG β3 T4 β4 := fun ℓ hℓ => h4 ℓ (hℓ.trans g3)
  unfold wfBody
  exact ph_wfBody_aux h1 h2' h3 h4' h5 h6 h7

/-- **The phase of the block**, from the phase of its body on the input in the machine's
coordinates. -/
theorem ph_wfB2 {β : Fin 256 → ℕ} {T : ℕ} {β' : Fin 256 → ℕ}
    (h : Ph (wfBody hk c W) (fun j => β (eW j)) T β') :
    Ph (wfB2 hk c W) β T (embedF eW β β') := by
  rw [wfB2]; exact ph_frame eW h

end WB2

end AdvancedEncryption.DualUse.Prog
