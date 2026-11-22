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

theorem natB_mono {n : ℕ} (t c : Fin n) {m m' : ℕ} (hm : m ≤ m') {β β' : Fin n → ℕ} (h : β ≤ β') :
    natB t c m β ≤ natB t c m' β' := fun i => by
  simp only [natB]
  split_ifs
  · exact hm
  · exact max_le_max (h c) hm
  · exact h i

/-- Two template lists with the same tapes, the values of the first below those of the second. -/
def TLe {n : ℕ} : List (Fin n × ℕ) → List (Fin n × ℕ) → Prop
  | [], [] => True
  | x :: l, y :: l' => x.1 = y.1 ∧ x.2 ≤ y.2 ∧ TLe l l'
  | _, _ => False

theorem tmplB_mono {n : ℕ} (c : Fin n) : ∀ (l l' : List (Fin n × ℕ)), TLe l l' →
    ∀ {β β' : Fin n → ℕ}, β ≤ β' → tmplB c l β ≤ tmplB c l' β'
  | [], [], _, _, _, h => h
  | x :: l, y :: l', ⟨h1, h2, h3⟩, _, _, h => by
    simp only [tmplB]
    rw [h1] at *
    exact tmplB_mono c l l' h3 (natB_mono y.1 c h2 h)
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim

theorem natB_leT {n : ℕ} (t c : Fin n) (m : ℕ) {β : Fin n → ℕ} {M : ℕ} (h : ∀ i, β i ≤ M)
    (hm : m ≤ M) : ∀ i, natB t c m β i ≤ M := fun i => by
  simp only [natB]; split_ifs
  · exact hm
  · exact max_le (h c) hm
  · exact h i

/-- **The steps of templates below a uniform bound.** -/
theorem tmplTT_le {n : ℕ} (c : Fin n) (M : ℕ) : ∀ (l : List (Fin n × ℕ)) (β : Fin n → ℕ),
    (∀ i, β i ≤ M) → (∀ x ∈ l, x.2 ≤ M) →
    tmplTT c l β ≤ (l.length + 1) * ((2 * M + 1) * (4 * M + 12))
  | [], β, hβ, _ => by
    simp only [tmplTT, List.length_nil, Nat.zero_add, Nat.one_mul]
    have := supB_le_of hβ
    nlinarith
  | x :: l, β, hβ, hl => by
    simp only [tmplTT, List.length_cons]
    have hx := hl x (by simp)
    have ih := tmplTT_le c M l (natB x.1 c x.2 β) (natB_leT x.1 c x.2 hβ hx)
      (fun y hy => hl y (by simp [hy]))
    have hs : max (supB β) x.2 ≤ M := max_le (supB_le_of hβ) hx
    have : (2 * x.2 + 1) * (4 * max (supB β) x.2 + 12) ≤ (2 * M + 1) * (4 * M + 12) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith

theorem tmplB_le {n : ℕ} (c : Fin n) (M : ℕ) : ∀ (l : List (Fin n × ℕ)) (β : Fin n → ℕ),
    (∀ i, β i ≤ M) → (∀ x ∈ l, x.2 ≤ M) → ∀ i, tmplB c l β i ≤ M
  | [], β, hβ, _ => hβ
  | x :: l, β, hβ, hl => tmplB_le c M l _ (natB_leT x.1 c x.2 hβ (hl x (by simp)))
      (fun y hy => hl y (by simp [hy]))

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

/-- The bounds of the frame of `capP` from `β`. -/
def capOut (W : ℕ) (β : Fin 256 → ℕ) : Fin 5 → ℕ :=
  ![β (mw 1) + W, 0, max (β (mw 5)) 1, 0, W]

/-- The bounds after `capP`. -/
def capV (W : ℕ) (β : Fin 256 → ℕ) : Fin 256 → ℕ := embedF (ValVM.mkE capE capE_inj) β (capOut W β)

/-- The steps of `capP`. -/
def capT2 (W : ℕ) (β : Fin 256 → ℕ) : ℕ :=
  Prog.capT W (β (mw GCNT) + β (mw 1) + β (mw 5) + β (mw 3) + β (mw 4) + W + 1)

/-- The bounds after `countP` and `capP`. -/
def ccV (W : ℕ) (β : Fin 256 → ℕ) : Fin 256 → ℕ :=
  capV W (embedF (ValVM.mkE cntE cntE_inj) β (cntOut W β))

theorem ph_cap (β : Fin 256 → ℕ) :
    Ph (.frame (ValVM.mkE capE capE_inj) (.prog (Prog.capP W))) β (capT2 W β) (capV W β) := by
  refine ph_frame _ fun ℓ hℓ => ?_
  obtain ⟨h1, h2⟩ := Prog.bounds_capP W (β (mw GCNT)) (β (mw 1)) (β (mw 5)) (β (mw 3)) (β (mw 4)) ℓ
    (fun j => by fin_cases j <;> exact hℓ _)
  refine ⟨h2, fun j => (h1 j).trans ?_⟩
  fin_cases j <;> simp [capOut]

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
  let v2 := ccV W v1
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
  let v2 := ccV W v1
  let v3 := Prog.lenBoundT (clr (mw 12)) v2
  let v4 := Prog.lenBoundT (cp (mw GS) (mw GSC)) v3
  let v5 := tmplB tX0 (tmpl31 N K k c.d) v4
  let v6 := tmOut c M31 v5
  let v7 := Prog.lenBoundT (copiesP 0) v6
  let v8 := tmplB tX0 (stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c)) v7
  let v9 := Prog.lenBoundT (clr tX0) v8
  let v10 := Function.update v9 (mw OB) (v9 (mw OB) + 1)
  Prog.timeBoundT (cp (mw GSC) (mw GS)) β0 + (cntT W v1 + (capT2 W (embedF (ValVM.mkE cntE cntE_inj) v1 (cntOut W v1)) + (Prog.timeBoundT (clr (mw 12)) v2 +
    (Prog.timeBoundT (cp (mw GS) (mw GSC)) v3 + (tmplTT tX0 (tmpl31 N K k c.d) v4 +
    ((2 * M31 + 3) * simTmplSweeps N K k + (Prog.timeBoundT (copiesP 0) v6 +
    (tmplTT tX0 (stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c)) v7 +
    (Prog.timeBoundT (clr tX0) v8 + ((1 + 1) * (2 * (supB v9 + 1 + 1) + 3) +
      (1 + 1) * (2 * (supB v10 + 1 + 1) + 3)))))))))))

/-- **The phase of `prepT`.** -/
theorem ph_prepT (β0 : Fin 256 → ℕ) (M31 : ℕ)
    (hin : (fun j => tmplB tX0 (tmpl31 N K k c.d) (Prog.lenBoundT (cp (mw GS) (mw GSC))
      (Prog.lenBoundT (clr (mw 12)) (ccV W (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0)))) (tm31 j)) ≤
      Sym.bnd (tmVars M31 N K k (lenA N K k c.d)) σTmF)
    (htop : ∀ j, tmplB tX0 (tmpl31 N K k c.d) (Prog.lenBoundT (cp (mw GS) (mw GSC))
      (Prog.lenBoundT (clr (mw 12)) (ccV W (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0)))) (tm31 j) ≤ M31) :
    Ph (prepT hk c W) β0 (tT hk c W β0 M31) (vT hk c W β0 M31) := by
  have k31 : ∀ x ∈ tmpl31 N K k c.d, x.1 ≠ tX0 := ne_of_keys (keys_tmpl31 N K k c.d) (by decide)
  have kT : ∀ x ∈ stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c),
      x.1 ≠ tX0 := ne_of_keys (keys_T N K k c.d W _ _ _) (by decide)
  exact (ph_prog _ β0).seq <| (ph_cnt W _).seq <| (ph_cap W _).seq <| (ph_prog _ _).seq <| (ph_prog _ _).seq <|
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
  let v2 := ccV W v1
  let v3 := Prog.lenBoundT (clr (mw 12)) v2
  let v4 := Prog.lenBoundT (cp (mw GS) (mw GSC)) v3
  let v5 := tmplB tX0 (tmpl31 N K k c.d) v4
  let v6 := tmOut c M31 v5
  let v7 := Prog.lenBoundT (copiesP 1) v6
  let v8 := tmplB tX0 (stepG N K k c.d ++ wordsG N K k c.d W (offPsi hk c) (offR hk c)
    (offPsi hk c + 10 * lenPsi N K k)) v7
  Prog.lenBoundT (clr (ms 92)) (Prog.lenBoundT (clr tX0) v8)

/-- The steps of `prepG`. -/
def tG (β0 : Fin 256 → ℕ) (M31 : ℕ) : ℕ :=
  let v1 := Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0
  let v2 := ccV W v1
  let v3 := Prog.lenBoundT (clr (mw 12)) v2
  let v4 := Prog.lenBoundT (cp (mw GS) (mw GSC)) v3
  let v5 := tmplB tX0 (tmpl31 N K k c.d) v4
  let v6 := tmOut c M31 v5
  let v7 := Prog.lenBoundT (copiesP 1) v6
  let v8 := tmplB tX0 (stepG N K k c.d ++ wordsG N K k c.d W (offPsi hk c) (offR hk c)
    (offPsi hk c + 10 * lenPsi N K k)) v7
  Prog.timeBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0 + (cntT W v1 + (capT2 W (embedF (ValVM.mkE cntE cntE_inj) v1 (cntOut W v1)) +
    (Prog.timeBoundT (clr (mw 12)) v2 + (Prog.timeBoundT (cp (mw GS) (mw GSC)) v3 +
    (tmplTT tX0 (tmpl31 N K k c.d) v4 + ((2 * M31 + 3) * simTmplSweeps N K k +
    (Prog.timeBoundT (copiesP 1) v6 + (tmplTT tX0 (stepG N K k c.d ++ wordsG N K k c.d W
      (offPsi hk c) (offR hk c) (offPsi hk c + 10 * lenPsi N K k)) v7 +
    (Prog.timeBoundT (clr tX0) v8 + Prog.timeBoundT (clr (ms 92)) (Prog.lenBoundT (clr tX0) v8))))))))))

/-- **The phase of `prepG`.** -/
theorem ph_prepG (β0 : Fin 256 → ℕ) (M31 : ℕ)
    (hin : (fun j => tmplB tX0 (tmpl31 N K k c.d) (Prog.lenBoundT (cp (mw GS) (mw GSC))
      (Prog.lenBoundT (clr (mw 12)) (ccV W (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0)))) (tm31 j)) ≤
      Sym.bnd (tmVars M31 N K k (lenA N K k c.d)) σTmF)
    (htop : ∀ j, tmplB tX0 (tmpl31 N K k c.d) (Prog.lenBoundT (cp (mw GS) (mw GSC))
      (Prog.lenBoundT (clr (mw 12)) (ccV W (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0)))) (tm31 j) ≤ M31) :
    Ph (prepG hk c W) β0 (tG hk c W β0 M31) (vG hk c W β0 M31) := by
  have k31 : ∀ x ∈ tmpl31 N K k c.d, x.1 ≠ tX0 := ne_of_keys (keys_tmpl31 N K k c.d) (by decide)
  have kG : ∀ x ∈ stepG N K k c.d ++ wordsG N K k c.d W (offPsi hk c) (offR hk c)
      (offPsi hk c + 10 * lenPsi N K k), x.1 ≠ tX0 :=
    ne_of_keys (keys_G N K k c.d W _ _ _) (by decide)
  exact (ph_prog _ β0).seq <| (ph_cnt W _).seq <| (ph_cap W _).seq <| (ph_prog _ _).seq <| (ph_prog _ _).seq <|
    (ph_tmplP tX0 _ _ k31).seq <| (ph_tm c M31 _ hin htop).seq <| (ph_prog _ _).seq <|
    (ph_tmplP tX0 _ _ kG).seq ((ph_prog _ _).seq (ph_prog _ _))

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

/-! ### The bounds with explicit parameters -/

namespace WB2

open SigabaNeo.Tape.ValVM SigabaNeo.Tape.Prog SigabaNeo.Tape.Prog.KST

/-- The bounds after `simTmplP` with explicit parameters. -/
def tmOutN (N K k d M31 : ℕ) (β : Fin 256 → ℕ) : Fin 256 → ℕ :=
  embedF (ValVM.mkE tm31 tm31_inj) β fun j =>
    Sym.pEval (tmVars M31 N K k (lenA N K k d)) (Sym.aGet σTmF' j.val)

theorem tmOut_eq {N K k : ℕ} (c : Conf N K k) (M31 : ℕ) (β : Fin 256 → ℕ) :
    tmOut c M31 β = tmOutN N K k c.d M31 β := rfl

/-- The bounds after `prepT` with explicit parameters (`oB oW oP` the stream offsets). -/
def vTn (N K k d W : ℕ) (lw : List (Fin 256 × ℕ)) (β0 : Fin 256 → ℕ) (M31 : ℕ) : Fin 256 → ℕ :=
  let v1 := Prog.lenBoundT (cp (mw GSC) (mw GS)) β0
  let v2 := ccV W v1
  let v3 := Prog.lenBoundT (clr (mw 12)) v2
  let v4 := Prog.lenBoundT (cp (mw GS) (mw GSC)) v3
  let v5 := tmplB tX0 (tmpl31 N K k d) v4
  let v6 := tmOutN N K k d M31 v5
  let v7 := Prog.lenBoundT (copiesP 0) v6
  let v8 := tmplB tX0 (stepT N K k d ++ lw) v7
  let v9 := Prog.lenBoundT (clr tX0) v8
  let v10 := Function.update v9 (mw OB) (v9 (mw OB) + 1)
  Function.update v10 (mw ZB) (v10 (mw ZB) + 1)

/-- The bounds after `prepG` with explicit parameters. -/
def vGn (N K k d W : ℕ) (lw : List (Fin 256 × ℕ)) (β0 : Fin 256 → ℕ) (M31 : ℕ) : Fin 256 → ℕ :=
  let v1 := Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0
  let v2 := ccV W v1
  let v3 := Prog.lenBoundT (clr (mw 12)) v2
  let v4 := Prog.lenBoundT (cp (mw GS) (mw GSC)) v3
  let v5 := tmplB tX0 (tmpl31 N K k d) v4
  let v6 := tmOutN N K k d M31 v5
  let v7 := Prog.lenBoundT (copiesP 1) v6
  let v8 := tmplB tX0 (stepG N K k d ++ lw) v7
  Prog.lenBoundT (clr (ms 92)) (Prog.lenBoundT (clr tX0) v8)

theorem TLe_refl {n : ℕ} : ∀ l : List (Fin n × ℕ), TLe l l
  | [] => trivial
  | x :: l => ⟨rfl, le_rfl, TLe_refl l⟩

theorem TLe_append {n : ℕ} : ∀ {l₁ l₁' l₂ l₂' : List (Fin n × ℕ)}, TLe l₁ l₁' → TLe l₂ l₂' →
    TLe (l₁ ++ l₂) (l₁' ++ l₂')
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, _, _, ⟨a, b, c⟩, h => ⟨a, b, TLe_append c h⟩
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim

theorem TLe_wordsT (N K k d W : ℕ) {oB oW oP oB' oW' oP' : ℕ} (h1 : oB ≤ oB') (h2 : oW ≤ oW')
    (h3 : oP ≤ oP') : TLe (wordsT N K k d W oB oW oP) (wordsT N K k d W oB' oW' oP') := by
  simp [wordsT, TLe, h1, h2, h3]

theorem TLe_wordsG (N K k d W : ℕ) {oP oR oX oP' oR' oX' : ℕ} (h1 : oP ≤ oP') (h2 : oR ≤ oR')
    (h3 : oX ≤ oX') : TLe (wordsG N K k d W oP oR oX) (wordsG N K k d W oP' oR' oX') := by
  simp [wordsG, TLe, h1, h2, h3]

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (W : ℕ)

/-- `vT` below its version at upper bounds of the offsets. -/
theorem vT_le (β0 : Fin 256 → ℕ) (M31 : ℕ) (lw : List (Fin 256 × ℕ))
    (hl : TLe (wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c)) lw) :
    vT hk c W β0 M31 ≤ vTn N K k c.d W lw β0 M31 := by
  simp only [vT, vTn]
  have hm := tmplB_mono tX0 _ _ (TLe_append (TLe_refl (stepT N K k c.d)) hl) (le_refl (Prog.lenBoundT (copiesP 0) (tmOut c M31 (tmplB tX0 (tmpl31 N K k c.d)
      (Prog.lenBoundT (cp (mw GS) (mw GSC)) (Prog.lenBoundT (clr (mw 12))
        (ccV W (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0))))))))
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

/-- `vG` below its version at upper bounds of the offsets. -/
theorem vG_le (β0 : Fin 256 → ℕ) (M31 : ℕ) (lw : List (Fin 256 × ℕ))
    (hl : TLe (wordsG N K k c.d W (offPsi hk c) (offR hk c) (offPsi hk c + 10 * lenPsi N K k)) lw) :
    vG hk c W β0 M31 ≤ vGn N K k c.d W lw β0 M31 := by
  simp only [vG, vGn]
  exact Prog.lenBoundT_mono _ (Prog.lenBoundT_mono _
    (tmplB_mono tX0 _ _ (TLe_append (TLe_refl _) hl) le_rfl))

end WB2

/-! ### Templates with explicit values -/

namespace WB2

open SigabaNeo.Tape.ValVM SigabaNeo.Lattices.Algo SigabaNeo.Lattices

/-- `wordsT` with the tree height `th` explicit. -/
def wordsTx (N K k d W th oB oW oP : ℕ) : List (Fin 256 × ℕ) :=
  [(ValVM.tTV, VT N K k d), (mw 10, VT N K k d), (mw 11, VT N K k d), (mw 12, K + 1), (mw 13, K + 2),
    (mw 14, (K + 1) * VT N K k d), (mw 15, (K + 2) * VT N K k d), (mw 16, (K + 3) * VT N K k d),
    (mw 20, K), (mw 27, 2), (mw 29, 1), (mw TNV, N * VT N K k d),
    (mw TNKV, N * ((K + 1) * VT N K k d)), (mw T2K, 2 * (K + 1)),
    (mw TLB, (2 * (K + 1) * N + 1) * ((K + 1) * VT N K k d)), (mw TCNT, 2 * (K + 1) * N + 1),
    (mw TH, th), (mw TN, N), (mw TN1, N - 1), (mw TN1V, (N - 1) * VT N K k d),
    (mw TKV, K * VT N K k d), (mw T2kNV, 2 * (N * ((K + 1) * VT N K k d))),
    (mw T2kkNV, 2 * (K + 1) * (N * ((K + 1) * VT N K k d))), (mw TA1, lenA N K k 1),
    (mw TAd, lenA N K k d), (mw TK1, K - 1), (mw ZNK1, N * K - 1), (mw TNK, N * K),
    (mw T4k, 2 * (2 * (K + 1))), (mw T10, 10), (mw INSW, 10 * (nBI N K * VT N K k d)),
    (mw TSl, nBI N K * VT N K k d), (mw TST, (W + 1) * (nBI N K * VT N K k d)),
    (mw TD2, 2 * ((W + 1) * (nBI N K * VT N K k d))), (mw TW, W),
    (mw TPAD, (W - 10) * (nBI N K * VT N K k d)), (mw TW9, W - 9),
    (mw TINS, 10 * (nBI N K * VT N K k d)), (mw 61, oB), (mw 62, oW), (mw 63, oP)]

theorem wordsT_eq (N K k d W oB oW oP : ℕ) :
    wordsT N K k d W oB oW oP = wordsTx N K k d W (treeHeight N (K + 1)) oB oW oP := rfl

theorem TLe_wordsTx (N K k d W : ℕ) {th oB oW oP th' oB' oW' oP' : ℕ} (h0 : th ≤ th')
    (h1 : oB ≤ oB') (h2 : oW ≤ oW') (h3 : oP ≤ oP') :
    TLe (wordsTx N K k d W th oB oW oP) (wordsTx N K k d W th' oB' oW' oP') := by
  simp [wordsTx, TLe, h0, h1, h2, h3]

theorem TLe_le {n : ℕ} {M : ℕ} : ∀ {l l' : List (Fin n × ℕ)}, TLe l l' → (∀ x ∈ l', x.2 ≤ M) →
    ∀ x ∈ l, x.2 ≤ M
  | [], [], _, _, _, hx => absurd hx (by simp)
  | x :: l, y :: l', ⟨_, h2, h3⟩, h, z, hz => by
    rcases List.mem_cons.mp hz with rfl | hz
    · exact h2.trans (h y (by simp))
    · exact TLe_le h3 (fun w hw => h w (by simp [hw])) z hz
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim

end WB2

/-! ### The steps of the preparations -/

namespace WB2

open SigabaNeo.Tape.ValVM SigabaNeo.Tape.Prog SigabaNeo.Tape.Prog.KST

theorem loopFree_clrsP : ∀ l : List (Fin 256), (clrsP l).LoopFree
  | [] => trivial
  | _ :: l => ⟨trivial, loopFree_clrsP l⟩

theorem pcount_clrsP : ∀ l : List (Fin 256), pcount (clrsP l) = l.length + 1
  | [] => rfl
  | _ :: l => by simp [clrsP, pcount, pcount_clrsP l]; ring

/-- A primitive below a uniform bound. -/
theorem tb_prim (p : Prim 256) (β : Fin 256 → ℕ) (M : ℕ) (h : ∀ t, β t ≤ M) :
    Prog.timeBoundT (.prim p) β ≤ 2 * M + 7 := by
  have := timeBoundT_le_pcount (.prim p) trivial β h
  simp only [pcount] at this
  omega

/-- The uniform term. -/
def uT (M : ℕ) : ℕ := (2 * M + 1) * (4 * M + 12)

theorem le_uT (M : ℕ) : 2 * M + 7 ≤ uT M := by simp only [uT]; nlinarith

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (W : ℕ)

set_option maxHeartbeats 2000000 in
/-- **The steps of `prepT`**, below a uniform bound of its intermediate tapes. -/
theorem tT_le (β0 : Fin 256 → ℕ) (M31 M : ℕ) (h0 : ∀ t, β0 t ≤ M)
    (h2 : ∀ t, ccV W (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0) t ≤ M)
    (h6 : ∀ t, tmOut c M31 (tmplB tX0 (tmpl31 N K k c.d) (Prog.lenBoundT (cp (mw GS) (mw GSC))
      (Prog.lenBoundT (clr (mw 12)) (ccV W (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0))))) t ≤ M)
    (h31 : ∀ x ∈ tmpl31 N K k c.d, x.2 ≤ M)
    (hl : ∀ x ∈ stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c), x.2 ≤ M) :
    tT hk c W β0 M31 ≤ cntT W (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0) +
      capT2 W (embedF (ValVM.mkE cntE cntE_inj) (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0) (cntOut W (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0))) +
      (2 * M31 + 3) * simTmplSweeps N K k + 90 * uT (M + 6) := by
  set v1 := Prog.lenBoundT (cp (mw GSC) (mw GS)) β0
  set v2 := ccV W v1
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
  show Prog.timeBoundT (cp (mw GSC) (mw GS)) β0 + (cntT W v1 + (capT2 W (embedF (ValVM.mkE cntE cntE_inj) v1 (cntOut W v1)) + (Prog.timeBoundT (clr (mw 12)) v2 +
    (Prog.timeBoundT (cp (mw GS) (mw GSC)) v3 + (tmplTT tX0 (tmpl31 N K k c.d) v4 +
    ((2 * M31 + 3) * simTmplSweeps N K k + (Prog.timeBoundT (copiesP 0) v6 +
    (tmplTT tX0 (stepT N K k c.d ++ wordsT N K k c.d W (offB c) (offW hk c) (offPsi hk c)) v7 +
    (Prog.timeBoundT (clr tX0) v8 + ((1 + 1) * (2 * (supB v9 + 1 + 1) + 3) +
      (1 + 1) * (2 * (supB v10 + 1 + 1) + 3))))))))))) ≤ _
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
/-- **The steps of `prepG`**, below a uniform bound of its intermediate tapes. -/
theorem tG_le (β0 : Fin 256 → ℕ) (M31 M : ℕ) (h0 : ∀ t, β0 t ≤ M)
    (h2 : ∀ t, ccV W (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0) t ≤ M)
    (h6 : ∀ t, tmOut c M31 (tmplB tX0 (tmpl31 N K k c.d) (Prog.lenBoundT (cp (mw GS) (mw GSC))
      (Prog.lenBoundT (clr (mw 12)) (ccV W (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0))))) t ≤ M)
    (h31 : ∀ x ∈ tmpl31 N K k c.d, x.2 ≤ M)
    (hl : ∀ x ∈ stepG N K k c.d ++ wordsG N K k c.d W (offPsi hk c) (offR hk c)
      (offPsi hk c + 10 * lenPsi N K k), x.2 ≤ M) :
    tG hk c W β0 M31 ≤ cntT W (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0) +
      capT2 W (embedF (ValVM.mkE cntE cntE_inj) (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0) (cntOut W (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0))) +
      (2 * M31 + 3) * simTmplSweeps N K k + 120 * uT (M + 40) := by
  set v1 := Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0
  set v2 := ccV W v1
  set v3 := Prog.lenBoundT (clr (mw 12)) v2
  set v4 := Prog.lenBoundT (cp (mw GS) (mw GSC)) v3
  set v5 := tmplB tX0 (tmpl31 N K k c.d) v4
  set v6 := tmOut c M31 v5
  set v7 := Prog.lenBoundT (copiesP 1) v6
  set v8 := tmplB tX0 (stepG N K k c.d ++ wordsG N K k c.d W (offPsi hk c) (offR hk c)
    (offPsi hk c + 10 * lenPsi N K k)) v7
  have h3 : ∀ t, v3 t ≤ M := Sym.lenBoundT_le_const (clr (mw 12)) rfl h2
  have h4 : ∀ t, v4 t ≤ M := Sym.lenBoundT_le_const (cp (mw GS) (mw GSC)) rfl h3
  have h7 : ∀ t, v7 t ≤ M := Sym.lenBoundT_le_const (copiesP 1) rfl h6
  have h8 : ∀ t, v8 t ≤ M := tmplB_le tX0 M _ v7 h7 hl
  have h9 : ∀ t, Prog.lenBoundT (clr tX0) v8 t ≤ M := Sym.lenBoundT_le_const (clr tX0) rfl h8
  show Prog.timeBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β0 + (cntT W v1 + (capT2 W (embedF (ValVM.mkE cntE cntE_inj) v1 (cntOut W v1)) +
    (Prog.timeBoundT (clr (mw 12)) v2 + (Prog.timeBoundT (cp (mw GS) (mw GSC)) v3 +
    (tmplTT tX0 (tmpl31 N K k c.d) v4 + ((2 * M31 + 3) * simTmplSweeps N K k +
    (Prog.timeBoundT (copiesP 1) v6 + (tmplTT tX0 (stepG N K k c.d ++ wordsG N K k c.d W
      (offPsi hk c) (offR hk c) (offPsi hk c + 10 * lenPsi N K k)) v7 +
    (Prog.timeBoundT (clr tX0) v8 + Prog.timeBoundT (clr (ms 92)) (Prog.lenBoundT (clr tX0) v8)))))))))) ≤ _
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
    (offPsi hk c + 10 * lenPsi N K k)).length = 46 := rfl
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

set_option maxHeartbeats 2000000 in
/-- **The steps of the key sum's preparation.** -/
theorem tK_le (N K k d : ℕ) (β : Fin 256 → ℕ) (M : ℕ) (h0 : ∀ t, β t ≤ M)
    (hl : ∀ x ∈ keyT N K k d, x.2 ≤ M) :
    Prog.timeBoundT (clrsP keyClr) β + (tmplTT tX0 (keyT N K k d) (Prog.lenBoundT (clrsP keyClr) β) +
      (1 + 1) * (2 * (supB (tmplB tX0 (keyT N K k d) (Prog.lenBoundT (clrsP keyClr) β)) + 1 + 1) + 3))
      ≤ 120 * uT (M + 100) := by
  have h1 : ∀ t, Prog.lenBoundT (clrsP keyClr) β t ≤ M :=
    Sym.lenBoundT_le_const (clrsP keyClr) (by
      show (clrsP keyClr).noGrowB = true
      have : ∀ l : List (Fin 256), (clrsP l).noGrowB = true := by
        intro l; induction l with
        | nil => rfl
        | cons x l ih => simp [clrsP, noGrowB, ih, Prim.noGrowB]
      exact this _) h0
  have a := timeBoundT_le_pcount (clrsP keyClr) (loopFree_clrsP _) β h0
  rw [pcount_clrsP, show keyClr.length = 92 from rfl] at a
  have hd := tmplTT_le tX0 M _ _ h1 hl
  rw [show (keyT N K k d).length = 18 from rfl] at hd
  have s := supB_le_of (tmplB_le tX0 M _ _ h1 hl)
  have u1 : (92 + 1) * (2 * (M + (92 + 1)) + 5) ≤ 93 * uT (M + 100) := by simp only [uT]; nlinarith
  have u2 : (18 + 1) * ((2 * M + 1) * (4 * M + 12)) ≤ 19 * uT (M + 100) := by
    have : (2 * M + 1) * (4 * M + 12) = uT M := rfl
    rw [this]; have : uT M ≤ uT (M + 100) := by simp only [uT]; nlinarith
    nlinarith
  have u3 : (1 + 1) * (2 * (supB (tmplB tX0 (keyT N K k d) (Prog.lenBoundT (clrsP keyClr) β)) + 1 + 1) + 3)
      ≤ uT (M + 100) := by simp only [uT]; nlinarith
  generalize (2 * M + 1) * (4 * M + 12) = P at hd u2
  generalize uT (M + 100) = U at *
  omega

/-- **The steps of the final cleanup.** -/
theorem tF_le (β : Fin 256 → ℕ) (M : ℕ) (h0 : ∀ t, β t ≤ M) :
    Prog.timeBoundT (clrsP finClr) β ≤ 256 * (2 * (M + 256) + 5) := by
  have a := timeBoundT_le_pcount (clrsP finClr) (loopFree_clrsP _) β h0
  rw [pcount_clrsP] at a
  have : finClr.length ≤ 255 := by
    have : finClr.length ≤ 256 := (List.length_filter_le _ _).trans (by simp)
    have h2 : finClr.length < 256 := by
      rw [finClr]
      exact List.length_filter_lt_length_iff_exists.mpr ⟨mw SDW, List.mem_finRange _, by simp⟩
    omega
  calc _ ≤ (finClr.length + 1) * (2 * (M + (finClr.length + 1)) + 5) := a
    _ ≤ 256 * (2 * (M + 256) + 5) := Nat.mul_le_mul (by omega) (by omega)

end WB2

end AdvancedEncryption.DualUse.Prog
