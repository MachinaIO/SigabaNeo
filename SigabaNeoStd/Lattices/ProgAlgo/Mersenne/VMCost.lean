import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMCert

/-!
# The clock of compiled ring-word codes

Per-tape length bounds of the machine of `RingVM` (`encB Mo N K B`): every tape of the operation
area at most `Mo` (an upper bound of `N K` and of the template lengths), the templates `K`, `N`,
`N K`, `N K`, the scratch blank, the register `x` at most `B x`.

* `InstrOK Mo N K B c T`: from `encB Mo N K B`, the compiled instruction `c` keeps the per-tape
  bounds and takes at most `T` steps.
* **`compile_bounds`**: for a cost `tc` of the instructions with `InstrOK … (tc c)` for every
  instruction of the code (`LeavesOK`), the whole code keeps the bounds and takes at most
  `vmTime Mo N K B tc c` steps; a loop `rep t body` is charged `B t` rounds of
  `2 · supB (encB …) + 3 + (its body) + 1`, plus `2`.
* The instruction bounds (`instrOK_*`, every instruction), from the certificates of
  `Mersenne/VMCert.lean` placed by `stepCert`/`opFrame` (`step5`, `step4`, `step2` for the layouts
  of the operations), composed along the loads, the operation and the store (`instrOK_opBin`,
  `instrOK_opUn`, `instrOK_opTm`); the cost table `instrTime`.
* **`compile_time`**: for bounds `B` closed under the code (`Closed`: ring results fit their
  registers, templates fit the operation area, copies fit), with `N K, K, N ≤ Mo`,
  `timeBoundT (compile c) (encB Mo N K B) ≤ vmTime Mo N K B (instrTime Mo N K B) c`.
-/

namespace SigabaNeo.Tape

namespace RingVM

open _root_.SigabaNeo.Tape.Sym Prog SpecT MersenneT

/-- **The per-tape bounds.** -/
def encB (Mo N K : ℕ) (B : Fin 200 → ℕ) : Fin 247 → ℕ := fun t =>
  if t.val < 40 then Mo else if t.val = 40 then K else if t.val = 41 then N
  else if t.val = 42 ∨ t.val = 43 then N * K
  else if h : 47 ≤ t.val then B ⟨t.val - 47, by have := t.isLt; omega⟩ else 0

theorem encB_tWd (Mo N K : ℕ) (B : Fin 200 → ℕ) (x : Fin 200) : encB Mo N K B (tWd x) = B x := by
  have h1 : ¬ (47 + x.val < 40) := by omega
  have h2 : 47 + x.val ≠ 40 := by omega
  have h3 : 47 + x.val ≠ 41 := by omega
  have h4 : ¬ (47 + x.val = 42 ∨ 47 + x.val = 43) := by omega
  simp only [encB, tWd, h1, h2, h3, h4, ↓reduceIte, Nat.le_add_right, ↓reduceDIte,
    Nat.add_sub_cancel_left]

/-- **An instruction keeps the bounds and takes at most `T` steps.** -/
structure InstrOK (Mo N K : ℕ) (B : Fin 200 → ℕ) (c : Code) (T : ℕ) : Prop where
  len : XProg.lenBoundT (compile c) (encB Mo N K B) ≤ encB Mo N K B
  time : XProg.timeBoundT (compile c) (encB Mo N K B) ≤ T

/-- **The clock of a code**, from a cost `tc` of its instructions. -/
noncomputable def vmTime (Mo N K : ℕ) (B : Fin 200 → ℕ) (tc : Code → ℕ) : Code → ℕ
  | .rep t b => B t * (2 * supB (encB Mo N K B) + 3 + vmTime Mo N K B tc b + 1) + 2
  | .seq p q => vmTime Mo N K B tc p + vmTime Mo N K B tc q
  | .ifb _ p q => max (vmTime Mo N K B tc p) (vmTime Mo N K B tc q) + 1
  | c => tc c

/-- Every instruction of the code meets its cost. -/
def LeavesOK (Mo N K : ℕ) (B : Fin 200 → ℕ) (tc : Code → ℕ) : Code → Prop
  | .rep _ b => LeavesOK Mo N K B tc b
  | .seq p q => LeavesOK Mo N K B tc p ∧ LeavesOK Mo N K B tc q
  | .ifb _ p q => LeavesOK Mo N K B tc p ∧ LeavesOK Mo N K B tc q
  | c => InstrOK Mo N K B c (tc c)

/-- **The bounds of a compiled code.** -/
theorem compile_bounds (Mo N K : ℕ) (B : Fin 200 → ℕ) (tc : Code → ℕ) :
    ∀ c : Code, LeavesOK Mo N K B tc c → InstrOK Mo N K B c (vmTime Mo N K B tc c)
  | .rep t b, h => by
    have ih := compile_bounds Mo N K B tc b h
    have hinv : XProg.loopStepT (tWd t) (compile b) (encB Mo N K B) ≤ encB Mo N K B :=
      ((XProg.lenBoundT_mono _) (tailB_le _ _)).trans ih.len
    refine ⟨XProg.lenBoundT_loop_le_of_inv _ _ le_rfl hinv, ?_⟩
    refine (XProg.timeBoundT_loop_le_of_inv _ _ le_rfl hinv).trans ?_
    rw [encB_tWd]
    show _ ≤ B t * (2 * supB (encB Mo N K B) + 3 + vmTime Mo N K B tc b + 1) + 2
    have hr : Prog.roundTimeT (XProg.timeBoundT (compile b)) (tWd t) (encB Mo N K B) ≤
        2 * supB (encB Mo N K B) + 3 + vmTime Mo N K B tc b :=
      Nat.add_le_add_left (((XProg.timeBoundT_mono _) (tailB_le _ _)).trans ih.time) _
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right hr 1)) 2
  | .seq p q, h => by
    have ihp := compile_bounds Mo N K B tc p h.1
    have ihq := compile_bounds Mo N K B tc q h.2
    refine ⟨((XProg.lenBoundT_mono _) ihp.len).trans ihq.len, ?_⟩
    show XProg.timeBoundT (compile p) _ + XProg.timeBoundT (compile q) _ ≤ _
    exact Nat.add_le_add ihp.time (((XProg.timeBoundT_mono _) ihp.len).trans ihq.time)
  | .ifb x p q, h => by
    have ihp := compile_bounds Mo N K B tc p h.1
    have ihq := compile_bounds Mo N K B tc q h.2
    refine ⟨fun t => max_le (ihp.len t) (ihq.len t), ?_⟩
    show max (XProg.timeBoundT (compile p) _) (XProg.timeBoundT (compile q) _) + 1 ≤ _
    exact Nat.add_le_add_right (max_le_max ihp.time ihq.time) 1
  | .add .., h | .sub .., h | .mul .., h | .canon .., h | .neg .., h | .digit .., h
  | .rotB .., h | .aut .., h | .rhoJ .., h | .mv .., h | .cp .., h | .drop .., h | .clr _, h
  | .tl _, h | .nop, h => h

/-! ### Frames -/

theorem frame_len_le {m : ℕ} (e : Fin m ↪ Fin 247) (p : XProg m) {ℓ ℓ' : Fin 247 → ℕ}
    (hin : ∀ j, XProg.lenBoundT p (fun i => ℓ (e i)) j ≤ ℓ' (e j))
    (hout : ∀ t, (∀ j, e j ≠ t) → ℓ t ≤ ℓ' t) :
    XProg.lenBoundT (.frame e p) ℓ ≤ ℓ' := by
  intro t
  show embedF e ℓ _ t ≤ _
  rcases embedF_cases e ℓ (XProg.lenBoundT p fun i => ℓ (e i)) t with ⟨hn, h⟩ | ⟨j, rfl, h⟩
  · rw [h]; refine hout t fun j hj => ?_
    subst hj; rw [partialInv_self] at hn; exact Option.some_ne_none _ hn
  · rw [h]; exact hin j

/-- **A certified program framed**: its time, and the bounds after it from the claims (the top
size on the unclaimed framed tapes). -/
theorem stepCert {n : ℕ} {p : Prog n} {σ claim : Asg} {w : Poly}
    (h : check 8 p σ claim w = true) (ρ : List ℕ) (e : Fin n ↪ Fin 247) {ℓ ℓ' : Fin 247 → ℕ}
    (hin : ∀ j : Fin n, ℓ (e j) ≤ pEval ρ (aGet σ j.val)) (htop : ∀ j, ℓ (e j) ≤ top ρ)
    (hout : ∀ j : Fin n, (if j.val < claim.length then pEval ρ (aGet claim j.val) else top ρ) ≤
      ℓ' (e j)) (hrest : ∀ t, (∀ j, e j ≠ t) → ℓ t ≤ ℓ' t) :
    XProg.timeBoundT (.frame e (.prog p)) ℓ ≤ (2 * top ρ + 3) * pEval ρ w ∧
      XProg.lenBoundT (.frame e (.prog p)) ℓ ≤ ℓ' := by
  obtain ⟨h1, h2, h3, h4⟩ := frame_of_check' h ρ e (fun j => hin j) htop
  refine ⟨h1, fun t => ?_⟩
  by_cases ht : ∃ j, e j = t
  · obtain ⟨j, rfl⟩ := ht
    have := hout j
    split_ifs at this with hj
    · exact (h2 j hj).trans this
    · exact (h3 j).trans this
  · push_neg at ht
    rw [h4 t ht]; exact hrest t ht

/-! ### The moves -/

theorem sup_fin1 (a : ℕ) : supB (fun _ : Fin 1 => a) = a :=
  le_antisymm (Finset.sup_le fun _ _ => le_rfl) (le_supB (fun _ : Fin 1 => a) 0)

theorem instrOK_clr (Mo N K : ℕ) (B : Fin 200 → ℕ) (t : Fin 200) :
    InstrOK Mo N K B (.clr t) (2 * B t + 3) where
  len := frame_len_le _ _ (fun j => by
      fin_cases j
      simp [XProg.lenBoundT, Prog.lenBoundT, Prim.lenT]) (fun _ _ => le_rfl)
  time := by
    show Prog.timeBoundT (Prog.clr 0) (fun _ => encB Mo N K B (f1 (tWd t) 0)) ≤ _
    simp only [Prog.timeBoundT, f1, encB_tWd, sup_fin1, Prim.pad]
    omega

theorem instrOK_tl (Mo N K : ℕ) (B : Fin 200 → ℕ) (t : Fin 200) :
    InstrOK Mo N K B (.tl t) (2 * B t + 3) where
  len := frame_len_le _ _ (fun j => by
      fin_cases j
      simp only [XProg.lenBoundT, Prog.lenBoundT, Prim.lenT, Function.update_self]
      show encB Mo N K B (tWd t) - 1 ≤ encB Mo N K B (tWd t)
      omega) (fun _ _ => le_rfl)
  time := by
    show Prog.timeBoundT (Prog.tl 0) (fun _ => encB Mo N K B (f1 (tWd t) 0)) ≤ _
    simp only [Prog.timeBoundT, f1, encB_tWd, sup_fin1, Prim.pad]
    omega

theorem instrOK_nop (Mo N K : ℕ) (B : Fin 200 → ℕ) : InstrOK Mo N K B .nop 3 where
  len := frame_len_le _ _ (fun j => by
      fin_cases j
      simp [XProg.lenBoundT, Prog.lenBoundT, Prim.lenT, nop]) (fun _ _ => le_rfl)
  time := by
    show Prog.timeBoundT (nop 0) (fun _ => encB Mo N K B (f1 tX0 0)) ≤ _
    simp [Prog.timeBoundT, f1, sup_fin1, Prim.pad, nop, encB, tX0]

theorem supB_le_of {n : ℕ} (ℓ : Fin n → ℕ) {M : ℕ} (h : ∀ j, ℓ j ≤ M) : supB ℓ ≤ M :=
  Finset.sup_le fun j _ => h j

@[simp] theorem encB_tX1 (Mo N K : ℕ) (B : Fin 200 → ℕ) : encB Mo N K B tX1 = 0 := by
  simp [encB, tX1]
@[simp] theorem encB_tX2 (Mo N K : ℕ) (B : Fin 200 → ℕ) : encB Mo N K B tX2 = 0 := by
  simp [encB, tX2]

/-- The variables of the move certificates: top, then the lengths `m`, `n`, `l`. -/
def ρMv (T m n l : ℕ) : List ℕ := [T, 0, 0, m, n, l, 0]

@[simp] theorem pEval_pm (T m n l : ℕ) : pEval (ρMv T m n l) pm = m := by
  simp [pm, mo, pEval, mEval, ρMv]
@[simp] theorem pEval_pn' (T m n l : ℕ) : pEval (ρMv T m n l) pn' = n := by
  simp [pn', mo, pEval, mEval, ρMv]
@[simp] theorem pEval_pl' (T m n l : ℕ) : pEval (ρMv T m n l) pl' = l := by
  simp [pl', mo, pEval, mEval, ρMv]
@[simp] theorem top_ρMv (T m n l : ℕ) : top (ρMv T m n l) = T := rfl

theorem instrOK_cp (Mo N K : ℕ) (B : Fin 200 → ℕ) (d s : Fin 200) (h : B s ≤ B d) :
    InstrOK Mo N K B (.cp d s) (2 * max (B d) (B s) + 3) := by
  by_cases hds : d = s
  · have := instrOK_nop Mo N K B
    have hc : compile (.cp d s) = nopX := dif_pos hds
    exact ⟨by rw [hc]; exact this.len, by rw [hc]; exact this.time.trans (by omega)⟩
  · have hc : compile (.cp d s) = .frame (mkE (fCp d s) (fCp_inj hds)) (.prog (Prog.cp 0 1)) :=
      dif_neg hds
    rw [show InstrOK Mo N K B (.cp d s) (2 * max (B d) (B s) + 3) =
      (XProg.lenBoundT (.frame (mkE (fCp d s) (fCp_inj hds)) (.prog (Prog.cp 0 1))) (encB Mo N K B)
        ≤ encB Mo N K B ∧ XProg.timeBoundT (.frame (mkE (fCp d s) (fCp_inj hds))
          (.prog (Prog.cp 0 1))) (encB Mo N K B) ≤ 2 * max (B d) (B s) + 3) by
      rw [← hc]; exact propext ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩]
    have e0 : fCp d s 0 = tWd d := rfl
    have e1 : fCp d s 1 = tWd s := rfl
    refine ⟨frame_len_le _ _ (fun j => ?_) (fun _ _ => le_rfl), ?_⟩
    · fin_cases j <;> simp [XProg.lenBoundT, Prog.lenBoundT, Prim.lenT, mkE, e0, e1, encB_tWd, h]
    · show Prog.timeBoundT (Prog.cp 0 1) (fun j => encB Mo N K B (fCp d s j)) ≤ _
      simp only [Prog.timeBoundT, Prim.pad]
      have := supB_le_of (fun j : Fin 2 => encB Mo N K B (fCp d s j)) (M := max (B d) (B s))
        (fun j => by fin_cases j <;> simp [e0, e1, encB_tWd])
      omega

theorem instrOK_mv (Mo N K : ℕ) (B : Fin 200 → ℕ) (d s c : Fin 200) :
    InstrOK Mo N K B (.mv d s c)
      ((2 * max (B s) (max (B d) (B c)) + 3) * (20 + 10 * B c) + 3) := by
  by_cases h : d = s ∨ d = c ∨ s = c
  · have := instrOK_nop Mo N K B
    have hc : compile (.mv d s c) = nopX := dif_pos h
    exact ⟨by rw [hc]; exact this.len, by rw [hc]; exact this.time.trans (by omega)⟩
  · have hc : compile (.mv d s c) = .frame (mkE (fMv d s c) (fMv_inj h)) (.prog ValVM.mvPc) :=
      dif_neg h
    have e0 : fMv d s c 0 = tWd s := rfl
    have e1 : fMv d s c 1 = tWd d := rfl
    have e2 : fMv d s c 2 = tX1 := rfl
    have e3 : fMv d s c 3 = tX2 := rfl
    have e4 : fMv d s c 4 = tWd c := rfl
    obtain ⟨ht, hl⟩ := stepCert check_mvPc (ρMv (max (B s) (max (B d) (B c))) (B s) (B d) (B c))
      (mkE (fMv d s c) (fMv_inj h)) (ℓ := encB Mo N K B) (ℓ' := encB Mo N K B)
      (fun j => by fin_cases j <;> simp [mkE, e0, e1, e2, e3, e4, encB_tWd, aGet])
      (fun j => by fin_cases j <;> simp [mkE, e0, e1, e2, e3, e4, encB_tWd])
      (fun j => by fin_cases j <;> simp [mkE, e0, e1, e2, e3, e4, encB_tWd, aGet])
      (fun _ _ => le_rfl)
    have hw : (2 * top (ρMv (max (B s) (max (B d) (B c))) (B s) (B d) (B c)) + 3) *
        pEval (ρMv (max (B s) (max (B d) (B c))) (B s) (B d) (B c)) wMv ≤
        (2 * max (B s) (max (B d) (B c)) + 3) * (20 + 10 * B c) := by
      rw [top_ρMv]
      simp [wMv, pEval, mEval, ρMv]

    exact ⟨by rw [hc]; exact hl, by rw [hc]; exact (ht.trans hw).trans (by omega)⟩

theorem instrOK_drop (Mo N K : ℕ) (B : Fin 200 → ℕ) (t c : Fin 200) :
    InstrOK Mo N K B (.drop t c) ((2 * max (B t) (B c) + 3) * (20 + 10 * B c) + 3) := by
  by_cases h : t = c
  · have := instrOK_nop Mo N K B
    have hc : compile (.drop t c) = nopX := dif_pos h
    exact ⟨by rw [hc]; exact this.len, by rw [hc]; exact this.time.trans (by omega)⟩
  · have hc : compile (.drop t c) = .frame (mkE (fDr t c) (fDr_inj h)) (.prog ValVM.dropPc) :=
      dif_neg h
    have e0 : fDr t c 0 = tWd t := rfl
    have e1 : fDr t c 1 = tX1 := rfl
    have e2 : fDr t c 2 = tWd c := rfl
    obtain ⟨ht, hl⟩ := stepCert check_dropPc (ρMv (max (B t) (B c)) (B t) (B c) 0)
      (mkE (fDr t c) (fDr_inj h)) (ℓ := encB Mo N K B) (ℓ' := encB Mo N K B)
      (fun j => by fin_cases j <;> simp [mkE, e0, e1, e2, encB_tWd, aGet])
      (fun j => by fin_cases j <;> simp [mkE, e0, e1, e2, encB_tWd])
      (fun j => by fin_cases j <;> simp [mkE, e0, e1, e2, encB_tWd, aGet])
      (fun _ _ => le_rfl)
    have hw : (2 * top (ρMv (max (B t) (B c)) (B t) (B c) 0) + 3) *
        pEval (ρMv (max (B t) (B c)) (B t) (B c) 0) wDr ≤
        (2 * max (B t) (B c) + 3) * (20 + 10 * B c) := by
      rw [top_ρMv]
      simp [wDr, pEval, mEval, ρMv]

    exact ⟨by rw [hc]; exact hl, by rw [hc]; exact (ht.trans hw).trans (by omega)⟩

/-! ### The operations -/

theorem aGet_append_lt (σp : Asg) (r i : ℕ) (h : i < σp.length) :
    aGet (σp ++ List.replicate r pTop) i = aGet σp i := by
  simp only [aGet, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left h]

theorem aGet_append_ge (σp : Asg) (r i : ℕ) (h : σp.length ≤ i) (h' : i < σp.length + r) :
    aGet (σp ++ List.replicate r pTop) i = pTop := by
  simp only [aGet, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right h, List.getElem?_replicate, if_pos (by omega)]
  rfl

theorem pEval_pTop (ρ : List ℕ) : pEval ρ pTop = top ρ := by
  cases ρ <;> simp [pTop, pEval, mEval, top]

/-- **An operation framed**, its scratch at the top size: `L` claimed tapes, the others at most
the top size before and after. -/
theorem opFrame {r : ℕ} {σp claim : Asg} {w : Poly} {P : Prog (σp.length + r)}
    (h : check 8 P (σp ++ List.replicate r pTop) claim w = true) (ρ : List ℕ)
    (e : Fin (σp.length + r) ↪ Fin 247) {ℓ ℓ' : Fin 247 → ℕ}
    (hcl : claim.length = σp.length)
    (hin : ∀ j : Fin (σp.length + r), j.val < σp.length → ℓ (e j) ≤ pEval ρ (aGet σp j.val))
    (hsc : ∀ j : Fin (σp.length + r), σp.length ≤ j.val → ℓ (e j) ≤ top ρ)
    (htop : ∀ j, ℓ (e j) ≤ top ρ)
    (hout : ∀ j : Fin (σp.length + r), j.val < σp.length → pEval ρ (aGet claim j.val) ≤ ℓ' (e j))
    (hsc' : ∀ j : Fin (σp.length + r), σp.length ≤ j.val → top ρ ≤ ℓ' (e j))
    (hrest : ∀ t, (∀ j, e j ≠ t) → ℓ t ≤ ℓ' t) :
    XProg.timeBoundT (.frame e (.prog P)) ℓ ≤ (2 * top ρ + 3) * pEval ρ w ∧
      XProg.lenBoundT (.frame e (.prog P)) ℓ ≤ ℓ' :=
  stepCert h ρ e
    (fun j => by
      by_cases hj : j.val < σp.length
      · rw [aGet_append_lt _ _ _ hj]; exact hin j hj
      · rw [aGet_append_ge _ _ _ (by omega) j.isLt, pEval_pTop]; exact hsc j (by omega))
    htop
    (fun j => by
      by_cases hj : j.val < σp.length
      · rw [if_pos (by omega)]; exact hout j hj
      · rw [if_neg (by omega)]; exact hsc' j (by omega))
    hrest

/-! ### Loads and stores -/

/-- The variables of the loads and stores: top, `N`, `K`, the register length `m`. -/
def ρLd (T N K m : ℕ) : List ℕ := [T, N, K, m, 0, 0, 0]

@[simp] theorem top_ρLd (T N K m : ℕ) : top (ρLd T N K m) = T := rfl
@[simp] theorem pEval_ρLd_pNK (T N K m : ℕ) : pEval (ρLd T N K m) pNK = N * K := by
  simp [pNK, mo, pEval, mEval, ρLd]
@[simp] theorem pEval_ρLd_pm (T N K m : ℕ) : pEval (ρLd T N K m) pm = m := by
  simp [pm, mo, pEval, mEval, ρLd]
@[simp] theorem pEval_ρLd_pTop (T N K m : ℕ) : pEval (ρLd T N K m) pTop = T := by
  simp [pTop, pEval, mEval, ρLd]
@[simp] theorem pEval_nil (ρ : List ℕ) : pEval ρ [] = 0 := rfl

theorem pEval_wIn (T N K m : ℕ) : pEval (ρLd T N K m) wIn = 30 + 10 * (N * K) := by
  simp [wIn, pEval, mEval, ρLd]

theorem loadA_step (i : ℕ) (hi : i < 40) (a : Fin 200) {N K : ℕ} (ℓ : Fin 247 → ℕ) (T : ℕ)
    (hT0 : ℓ ⟨i, by omega⟩ ≤ T) (hT1 : N * K ≤ T) (hT2 : ℓ (tWd a) ≤ T)
    (h42 : ℓ tNK = N * K) (hX0 : ℓ tX0 = 0) (hX1 : ℓ tX1 = 0) (hX2 : ℓ tX2 = 0) :
    XProg.timeBoundT (loadA i hi a) ℓ ≤ (2 * T + 3) * (30 + 10 * (N * K)) ∧
      XProg.lenBoundT (loadA i hi a) ℓ ≤ Function.update ℓ ⟨i, by omega⟩ (N * K) := by
  have e0 : fIn i hi a 0 = ⟨i, by omega⟩ := rfl
  have e1 : fIn i hi a 1 = tNK := rfl
  have e2 : fIn i hi a 2 = tWd a := rfl
  have e3 : fIn i hi a 3 = tX0 := rfl
  have e4 : fIn i hi a 4 = tX1 := rfl
  have e5 : fIn i hi a 5 = tX2 := rfl
  have nX0 : tX0 ≠ ⟨i, by omega⟩ := fun h => by have := congrArg Fin.val h; simp [tX0] at this; omega
  have nX1 : tX1 ≠ ⟨i, by omega⟩ := fun h => by have := congrArg Fin.val h; simp [tX1] at this; omega
  have nX2 : tX2 ≠ ⟨i, by omega⟩ := fun h => by have := congrArg Fin.val h; simp [tX2] at this; omega
  have n42 : tNK ≠ ⟨i, by omega⟩ := fun h => by have := congrArg Fin.val h; simp [tNK] at this; omega
  have nWa : tWd a ≠ ⟨i, by omega⟩ := fun h => by
    have := congrArg Fin.val h; simp [tWd] at this; omega
  obtain ⟨ht, hl⟩ := stepCert check_inP (ρLd T N K (ℓ (tWd a))) (mkE (fIn i hi a) (fIn_inj i hi a))
    (ℓ := ℓ) (ℓ' := Function.update ℓ ⟨i, by omega⟩ (N * K))
    (fun j => by
      fin_cases j <;> simp [mkE, e0, e1, e2, e3, e4, e5, aGet, hT0, h42, hX0, hX1, hX2])
    (fun j => by
      fin_cases j <;> simp [mkE, e0, e1, e2, e3, e4, e5, hT0, hT1, hT2, h42, hX0, hX1, hX2])
    (fun j => by
      fin_cases j <;> simp [mkE, e0, e1, e2, e3, e4, e5, aGet, Function.update_apply, nX0, nX1,
        nX2, n42, nWa, h42])
    (fun t ht => by
      have : t ≠ ⟨i, by omega⟩ := fun h => ht 0 (by rw [mkE, Function.Embedding.coeFn_mk, e0, h])
      rw [Function.update_of_ne this])
  refine ⟨ht.trans ?_, hl⟩
  rw [top_ρLd, pEval_wIn]

theorem loadT_step (t : Fin 200) (ℓ : Fin 247 → ℕ) (T : ℕ) (hT0 : ℓ (tO 2) ≤ T)
    (hT1 : ℓ (tWd t) ≤ T) :
    XProg.timeBoundT (loadT t) ℓ ≤ 2 * T + 3 ∧
      XProg.lenBoundT (loadT t) ℓ ≤ Function.update ℓ (tO 2) (ℓ (tWd t)) := by
  have e0 : fTm t 0 = tO 2 := rfl
  have e1 : fTm t 1 = tWd t := rfl
  have n1 : tWd t ≠ tO 2 := fun h => by have := congrArg Fin.val h; simp [tWd, tO] at this <;> omega
  refine ⟨?_, frame_len_le _ _ (fun j => ?_) (fun u hu => ?_)⟩
  · show Prog.timeBoundT (Prog.cp 0 1) (fun j => ℓ (fTm t j)) ≤ _
    simp only [Prog.timeBoundT, Prim.pad]
    have := supB_le_of (fun j : Fin 2 => ℓ (fTm t j)) (M := T)
      (fun j => by fin_cases j <;> simp [e0, e1, hT0, hT1])
    omega
  · fin_cases j <;> simp [XProg.lenBoundT, Prog.lenBoundT, Prim.lenT, mkE, e0, e1,
      Function.update_apply, n1]
  · have : u ≠ tO 2 := fun h => hu 0 (by rw [mkE, Function.Embedding.coeFn_mk, e0, h])
    rw [Function.update_of_ne this]

theorem pEval_wOut (T N K m : ℕ) : pEval (ρLd T N K m) wOut = 10 := by
  simp [wOut, pEval, mEval, ρLd]

theorem store_step (d : Fin 200) {N K : ℕ} (ℓ : Fin 247 → ℕ) (T : ℕ) (h0 : ℓ (tO 0) ≤ N * K)
    (hT1 : ℓ (tO 1) ≤ T) (hT2 : ℓ (tO 2) ≤ T) (hT0 : N * K ≤ T) (hT3 : ℓ (tWd d) ≤ T) :
    XProg.timeBoundT (store d) ℓ ≤ (2 * T + 3) * 10 ∧
      XProg.lenBoundT (store d) ℓ ≤ Function.update (Function.update (Function.update
        (Function.update ℓ (tWd d) (N * K)) (tO 0) 0) (tO 1) 0) (tO 2) 0 := by
  have e0 : fOut d 0 = tO 0 := rfl
  have e1 : fOut d 1 = tO 1 := rfl
  have e2 : fOut d 2 = tO 2 := rfl
  have e3 : fOut d 3 = tWd d := rfl
  obtain ⟨ht, hl⟩ := stepCert check_outP (ρLd T N K (ℓ (tWd d))) (mkE (fOut d) (fOut_inj d))
    (ℓ := ℓ) (ℓ' := Function.update (Function.update (Function.update
        (Function.update ℓ (tWd d) (N * K)) (tO 0) 0) (tO 1) 0) (tO 2) 0)
    (fun j => by fin_cases j <;> simp [mkE, e0, e1, e2, e3, aGet, h0, hT1, hT2])
    (fun j => by fin_cases j <;> simp [mkE, e0, e1, e2, e3, hT1, hT2, hT3] <;> omega)
    (fun j => by
      have n0 : tWd d ≠ tO 0 := fun h => by have := congrArg Fin.val h; simp [tWd, tO] at this <;> omega
      have n1 : tWd d ≠ tO 1 := fun h => by have := congrArg Fin.val h; simp [tWd, tO] at this <;> omega
      have n2 : tWd d ≠ tO 2 := fun h => by have := congrArg Fin.val h; simp [tWd, tO] at this <;> omega
      fin_cases j <;> simp [mkE, e0, e1, e2, e3, aGet, Function.update_of_ne n0,
        Function.update_of_ne n1, Function.update_of_ne n2])
    (fun u hu => by
      have h0' : u ≠ tO 0 := fun h => hu 0 (by rw [mkE, Function.Embedding.coeFn_mk, e0, h])
      have h1' : u ≠ tO 1 := fun h => hu 1 (by rw [mkE, Function.Embedding.coeFn_mk, e1, h])
      have h2' : u ≠ tO 2 := fun h => hu 2 (by rw [mkE, Function.Embedding.coeFn_mk, e2, h])
      have h3' : u ≠ tWd d := fun h => hu 3 (by rw [mkE, Function.Embedding.coeFn_mk, e3, h])
      rw [Function.update_of_ne h2', Function.update_of_ne h1', Function.update_of_ne h0',
        Function.update_of_ne h3'])
  refine ⟨ht.trans ?_, hl⟩
  rw [top_ρLd, pEval_wOut]

/-! ### The instructions of the operations -/

section Ops

variable (Mo N K : ℕ) (B : Fin 200 → ℕ)

/-- The bounds after loading the first operand, the second, and after the operation. -/
def L1 : Fin 247 → ℕ := Function.update (encB Mo N K B) (tO 1) (N * K)
def L2 : Fin 247 → ℕ := Function.update (L1 Mo N K B) (tO 2) (N * K)
def L3 : Fin 247 → ℕ := Function.update (L2 Mo N K B) (tO 0) (N * K)

theorem encB_tO (j : ℕ) (hj : j < 40) : encB Mo N K B (tO j hj) = Mo := by simp [encB, tO, hj]
@[simp] theorem encB_tNK : encB Mo N K B tNK = N * K := by simp [encB, tNK]
@[simp] theorem encB_tX0 : encB Mo N K B tX0 = 0 := by simp [encB, tX0]

theorem ne_tO_tWd (j : ℕ) (hj : j < 40) (x : Fin 200) : tWd x ≠ tO j hj := fun h => by
  have := congrArg Fin.val h; simp [tWd, tO] at this; omega

theorem L3_le_encB (hMo : N * K ≤ Mo) (d : Fin 200) (hd : N * K ≤ B d) :
    Function.update (Function.update (Function.update (Function.update (L3 Mo N K B) (tWd d)
      (N * K)) (tO 0) 0) (tO 1) 0) (tO 2) 0 ≤ encB Mo N K B := by
  intro t
  simp only [L3, L2, L1, Function.update_apply]
  split_ifs with h1 h2 h3 h4 <;> first
    | (subst_vars; simp [encB_tO])
    | (subst_vars; rw [encB_tWd]; exact hd)
    | exact le_rfl
    | (subst_vars; simp [encB_tO]; omega)

theorem instrOK_opBin {m : ℕ} (P : Prog (m + 1)) (e : Fin (m + 1) ↪ Fin 247) (d a b : Fin 200)
    (hMo : N * K ≤ Mo) (hd : N * K ≤ B d) (Top : ℕ)
    (hop : XProg.timeBoundT (.frame e (.prog P)) (L2 Mo N K B) ≤ Top ∧
      XProg.lenBoundT (.frame e (.prog P)) (L2 Mo N K B) ≤ L3 Mo N K B) :
    XProg.timeBoundT (opBin P e d a b) (encB Mo N K B) ≤
        (2 * max Mo (B a) + 3) * (30 + 10 * (N * K)) + (2 * max Mo (B b) + 3) * (30 + 10 * (N * K))
          + Top + (2 * max Mo (B d) + 3) * 10 ∧
      XProg.lenBoundT (opBin P e d a b) (encB Mo N K B) ≤ encB Mo N K B := by
  have na1 : ∀ x : Fin 200, tWd x ≠ tO 1 := fun x => ne_tO_tWd 1 (by omega) x
  have na2 : ∀ x : Fin 200, tWd x ≠ tO 2 := fun x => ne_tO_tWd 2 (by omega) x
  obtain ⟨t1, l1⟩ := loadA_step 1 (by omega) a (N := N) (K := K) (encB Mo N K B) (max Mo (B a))
    (by rw [show (⟨1, _⟩ : Fin 247) = tO 1 from rfl, encB_tO]; exact le_max_left _ _)
    (hMo.trans (le_max_left _ _)) (by rw [encB_tWd]; exact le_max_right _ _) (encB_tNK _ _ _ _)
    (encB_tX0 _ _ _ _) (encB_tX1 _ _ _ _) (encB_tX2 _ _ _ _)
  obtain ⟨t2, l2⟩ := loadA_step 2 (by omega) b (N := N) (K := K) (L1 Mo N K B) (max Mo (B b))
    (by simp [L1, Function.update_apply, tO, encB])
    (hMo.trans (le_max_left _ _))
    (by simp only [L1, Function.update_of_ne (na1 b)]; rw [encB_tWd]; exact le_max_right _ _)
    (by simp [L1, Function.update_apply, tNK, tO, encB])
    (by simp [L1, Function.update_apply, tX0, tO, encB])
    (by simp [L1, Function.update_apply, tX1, tO, encB])
    (by simp [L1, Function.update_apply, tX2, tO, encB])
  have hL1 : Function.update (encB Mo N K B) ⟨1, by omega⟩ (N * K) = L1 Mo N K B := rfl
  have hL2 : Function.update (L1 Mo N K B) ⟨2, by omega⟩ (N * K) = L2 Mo N K B := rfl
  rw [hL1] at l1
  rw [hL2] at l2
  obtain ⟨t4, l4⟩ := store_step d (N := N) (K := K) (L3 Mo N K B) (max Mo (B d))
    (by simp [L3]) (by simp [L3, L2, L1, Function.update_apply, tO]; omega)
    (by simp [L3, L2, L1, Function.update_apply, tO]; omega) (hMo.trans (le_max_left _ _))
    (by simp only [L3, L2, L1, Function.update_of_ne (ne_tO_tWd 0 (by omega) d),
          Function.update_of_ne (na1 d), Function.update_of_ne (na2 d)]
        rw [encB_tWd]; exact le_max_right _ _)
  have hl := L3_le_encB Mo N K B hMo d hd
  refine ⟨?_, ?_⟩
  · show XProg.timeBoundT (loadA 1 _ a) _ + (XProg.timeBoundT (loadA 2 _ b) _ +
      (XProg.timeBoundT (.frame e (.prog P)) _ + XProg.timeBoundT (store d) _)) ≤ _
    have m2 := (XProg.timeBoundT_mono (loadA 2 (by omega) b)) l1
    have mL2 := (XProg.lenBoundT_mono (loadA 2 (by omega) b)) l1
    have m3 := (XProg.timeBoundT_mono (.frame e (.prog P))) (mL2.trans l2)
    have mL3 := (XProg.lenBoundT_mono (.frame e (.prog P))) (mL2.trans l2)
    have m4 := (XProg.timeBoundT_mono (store d)) (mL3.trans hop.2)
    omega
  · show XProg.lenBoundT (store d) (XProg.lenBoundT (.frame e (.prog P))
      (XProg.lenBoundT (loadA 2 _ b) (XProg.lenBoundT (loadA 1 _ a) _))) ≤ _
    have mL2 := (XProg.lenBoundT_mono (loadA 2 (by omega) b)) l1
    have mL3 := (XProg.lenBoundT_mono (.frame e (.prog P))) (mL2.trans l2)
    exact ((XProg.lenBoundT_mono (store d)) (mL3.trans hop.2)).trans (l4.trans hl)

@[simp] theorem pEval_ρLd_pK (T m : ℕ) : pEval (ρLd T N K m) pK = K := by
  simp [pK, mo, pEval, mEval, ρLd]
@[simp] theorem pEval_ρLd_pN (T m : ℕ) : pEval (ρLd T N K m) pN = N := by
  simp [pN, mo, pEval, mEval, ρLd]

/-- **The operation frame of the layouts `[top, N K, x, K, N]`** (`add`, `sub`, `mul`, `canon`:
`x = N K`; `rotB`, `aut`: `x = j`; `digit`: `x = K`). -/
theorem step5 {r : ℕ} (p2 : Poly) (m v2 : ℕ) (hp2 : pEval (ρLd Mo N K m) p2 = v2) (hv2 : v2 ≤ Mo)
    {P : Prog ([pTop, pNK, p2, pK, pN].length + r)} {w : Poly}
    (h : check 8 P ([pTop, pNK, p2, pK, pN] ++ List.replicate r pTop) [pNK, pNK, p2, pK, pN] w =
      true) (hr : [pTop, pNK, p2, pK, pN].length + r ≤ 40)
    (two : ℕ) (h2 : two = 2 ∨ two = 43)
    (hMo : N * K ≤ Mo) (hK : K ≤ Mo) (hN : N ≤ Mo)
    (ℓ : Fin 247 → ℕ) (hℓ2 : ℓ (eOp ([pTop, pNK, p2, pK, pN].length + r) hr two h2 true true ⟨2, by show 2 < 5 + r; omega⟩) = v2)
    (hℓ0 : ℓ (tO 0) ≤ Mo) (hℓ1 : ℓ (tO 1) = N * K) (hK' : ℓ tK = K) (hN' : ℓ tN = N)
    (hsc : ∀ j : ℕ, (hj : j < 40) → 5 ≤ j → ℓ (tO j hj) = Mo) :
    XProg.timeBoundT (.frame (eOp ([pTop, pNK, p2, pK, pN].length + r) hr two h2 true true) (.prog P)) ℓ ≤
        (2 * Mo + 3) * pEval (ρLd Mo N K m) w ∧
      XProg.lenBoundT (.frame (eOp ([pTop, pNK, p2, pK, pN].length + r) hr two h2 true true) (.prog P)) ℓ ≤
        Function.update ℓ (tO 0) (N * K) := by
  have ge5 : ∀ j : Fin ([pTop, pNK, p2, pK, pN].length + r), 5 ≤ j.val →
      eOp ([pTop, pNK, p2, pK, pN].length + r) hr two h2 true true j = tO j.val (lt_of_lt_of_le j.isLt hr) := fun j hj =>
    Fin.ext (by
      show gOp two true true j.val = j.val
      simp [gOp, show j.val ≠ 2 by omega, show j.val ≠ 3 by omega, show j.val ≠ 4 by omega])
  have e0 : eOp ([pTop, pNK, p2, pK, pN].length + r) hr two h2 true true ⟨0, by show 0 < 5 + r; omega⟩ = tO 0 := rfl
  have e1 : eOp ([pTop, pNK, p2, pK, pN].length + r) hr two h2 true true ⟨1, by show 1 < 5 + r; omega⟩ = tO 1 := rfl
  have e3 : eOp ([pTop, pNK, p2, pK, pN].length + r) hr two h2 true true ⟨3, by show 3 < 5 + r; omega⟩ = tK := rfl
  have e4 : eOp ([pTop, pNK, p2, pK, pN].length + r) hr two h2 true true ⟨4, by show 4 < 5 + r; omega⟩ = tN := rfl
  have e2 : eOp ([pTop, pNK, p2, pK, pN].length + r) hr two h2 true true ⟨2, by show 2 < 5 + r; omega⟩ ≠ tO 0 := fun h => by
    have := congrArg Fin.val h
    simp only [eOp, mkE, Function.Embedding.coeFn_mk, fOp, ofW, gOp, tO] at this
    rcases h2 with rfl | rfl <;> simp at this
  have hlen : [pTop, pNK, p2, pK, pN].length = 5 := rfl
  obtain ⟨ht, hl⟩ := opFrame h (ρLd Mo N K m) (eOp ([pTop, pNK, p2, pK, pN].length + r) hr two h2 true true)
    (ℓ := ℓ) (ℓ' := Function.update ℓ (tO 0) (N * K)) rfl
    (fun j hj => by
      obtain ⟨v, hv⟩ := j
      simp only [hlen] at hj
      interval_cases v
      · rw [e0]; simpa [aGet] using hℓ0
      · rw [e1]; simp [aGet, hℓ1]
      · show _ ≤ pEval (ρLd Mo N K m) p2
        rw [hp2]; exact hℓ2.le
      · rw [e3]; simp [aGet, hK']
      · rw [e4]; simp [aGet, hN'])
    (fun j hj => by
      rw [ge5 j (by simpa [hlen] using hj), top_ρLd]; exact (hsc _ _ (by simpa [hlen] using hj)).le)
    (fun j => by
      by_cases hj : j.val < 5
      · obtain ⟨v, hv⟩ := j
        simp only at hj
        interval_cases v
        · rw [e0, top_ρLd]; exact hℓ0
        · rw [e1, top_ρLd, hℓ1]; exact hMo
        · rw [top_ρLd, hℓ2]; exact hv2
        · rw [e3, top_ρLd, hK']; exact hK
        · rw [e4, top_ρLd, hN']; exact hN
      · rw [ge5 j (by omega), top_ρLd]; exact (hsc _ _ (by omega)).le)
    (fun j hj => by
      obtain ⟨v, hv⟩ := j
      simp only [hlen] at hj
      interval_cases v
      · rw [e0]; simp [aGet]
      · rw [e1, Function.update_of_ne (by simp [tO])]; simp [aGet, hℓ1]
      · rw [Function.update_of_ne e2]
        show pEval (ρLd Mo N K m) p2 ≤ _
        rw [hp2, hℓ2]
      · rw [e3, Function.update_of_ne (by simp [tK, tO])]; simp [aGet, hK']
      · rw [e4, Function.update_of_ne (by simp [tN, tO])]; simp [aGet, hN'])
    (fun j hj => by
      rw [ge5 j (by simpa [hlen] using hj), top_ρLd, Function.update_of_ne (by
        simp only [tO, ne_eq, Fin.mk.injEq]; simp [hlen] at hj; omega)]
      exact (hsc _ _ (by simpa [hlen] using hj)).ge)
    (fun t ht => by
      rw [Function.update_of_ne (fun h => ht ⟨0, by show 0 < 5 + r; omega⟩ (by rw [e0, h]))])
  exact ⟨ht.trans (by rw [top_ρLd]), hl⟩

/-- **The operation frame of the layout `[top, N K]`** (`neg`). -/
theorem step2 {r : ℕ}
    {P : Prog ([pTop, pNK].length + r)} {w : Poly}
    (h : check 8 P ([pTop, pNK] ++ List.replicate r pTop) [pNK, pNK] w =
      true) (hr : [pTop, pNK].length + r ≤ 40)
    (two : ℕ) (h2 : two = 2 ∨ two = 43) (htwo : two = 2)
    (hMo : N * K ≤ Mo) (hK : K ≤ Mo) (hN : N ≤ Mo)
    (ℓ : Fin 247 → ℕ)
    (hℓ0 : ℓ (tO 0) ≤ Mo) (hℓ1 : ℓ (tO 1) = N * K)
    (hsc : ∀ j : ℕ, (hj : j < 40) → 2 ≤ j → ℓ (tO j hj) = Mo) :
    XProg.timeBoundT (.frame (eOp ([pTop, pNK].length + r) hr two h2 false false) (.prog P)) ℓ ≤
        (2 * Mo + 3) * pEval (ρLd Mo N K 0) w ∧
      XProg.lenBoundT (.frame (eOp ([pTop, pNK].length + r) hr two h2 false false) (.prog P)) ℓ ≤
        Function.update ℓ (tO 0) (N * K) := by
  have ge5 : ∀ j : Fin ([pTop, pNK].length + r), 2 ≤ j.val →
      eOp ([pTop, pNK].length + r) hr two h2 false false j = tO j.val (lt_of_lt_of_le j.isLt hr) := fun j hj =>
    Fin.ext (by
      show gOp two false false j.val = j.val
      unfold gOp; subst htwo; simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> omega)
  have e0 : eOp ([pTop, pNK].length + r) hr two h2 false false ⟨0, by show 0 < 2 + r; omega⟩ = tO 0 := rfl
  have e1 : eOp ([pTop, pNK].length + r) hr two h2 false false ⟨1, by show 1 < 2 + r; omega⟩ = tO 1 := rfl
  have hlen : [pTop, pNK].length = 2 := rfl
  obtain ⟨ht, hl⟩ := opFrame h (ρLd Mo N K 0) (eOp ([pTop, pNK].length + r) hr two h2 false false)
    (ℓ := ℓ) (ℓ' := Function.update ℓ (tO 0) (N * K)) rfl
    (fun j hj => by
      obtain ⟨v, hv⟩ := j
      simp only [hlen] at hj
      interval_cases v
      · rw [e0]; simpa [aGet] using hℓ0
      · rw [e1]; simp [aGet, hℓ1]
)
    (fun j hj => by
      rw [ge5 j (by simpa [hlen] using hj), top_ρLd]; exact (hsc _ _ (by simpa [hlen] using hj)).le)
    (fun j => by
      by_cases hj : j.val < 2
      · obtain ⟨v, hv⟩ := j
        simp only at hj
        interval_cases v
        · rw [e0, top_ρLd]; exact hℓ0
        · rw [e1, top_ρLd, hℓ1]; exact hMo
      · rw [ge5 j (by omega), top_ρLd]; exact (hsc _ _ (by omega)).le)
    (fun j hj => by
      obtain ⟨v, hv⟩ := j
      simp only [hlen] at hj
      interval_cases v
      · rw [e0]; simp [aGet]
      · rw [e1, Function.update_of_ne (by simp [tO])]; simp [aGet, hℓ1]
)
    (fun j hj => by
      rw [ge5 j (by simpa [hlen] using hj), top_ρLd, Function.update_of_ne (by
        simp only [tO, ne_eq, Fin.mk.injEq]; simp [hlen] at hj; omega)]
      exact (hsc _ _ (by simpa [hlen] using hj)).ge)
    (fun t ht => by
      rw [Function.update_of_ne (fun h => ht ⟨0, by show 0 < 2 + r; omega⟩ (by rw [e0, h]))])
  exact ⟨ht.trans (by rw [top_ρLd]), hl⟩

/-- **The operation frame of the layout `[top, N K, j, K]`** (`rhoJ`). -/
theorem step4 {r : ℕ} (p2 : Poly) (m v2 : ℕ) (hp2 : pEval (ρLd Mo N K m) p2 = v2) (hv2 : v2 ≤ Mo)
    {P : Prog ([pTop, pNK, p2, pK].length + r)} {w : Poly}
    (h : check 8 P ([pTop, pNK, p2, pK] ++ List.replicate r pTop) [pNK, pNK, p2, pK] w =
      true) (hr : [pTop, pNK, p2, pK].length + r ≤ 40)
    (two : ℕ) (h2 : two = 2 ∨ two = 43)
    (hMo : N * K ≤ Mo) (hK : K ≤ Mo) (hN : N ≤ Mo)
    (ℓ : Fin 247 → ℕ) (hℓ2 : ℓ (eOp ([pTop, pNK, p2, pK].length + r) hr two h2 true false ⟨2, by show 2 < 4 + r; omega⟩) = v2)
    (hℓ0 : ℓ (tO 0) ≤ Mo) (hℓ1 : ℓ (tO 1) = N * K) (hK' : ℓ tK = K)
    (hsc : ∀ j : ℕ, (hj : j < 40) → 4 ≤ j → ℓ (tO j hj) = Mo) :
    XProg.timeBoundT (.frame (eOp ([pTop, pNK, p2, pK].length + r) hr two h2 true false) (.prog P)) ℓ ≤
        (2 * Mo + 3) * pEval (ρLd Mo N K m) w ∧
      XProg.lenBoundT (.frame (eOp ([pTop, pNK, p2, pK].length + r) hr two h2 true false) (.prog P)) ℓ ≤
        Function.update ℓ (tO 0) (N * K) := by
  have ge5 : ∀ j : Fin ([pTop, pNK, p2, pK].length + r), 4 ≤ j.val →
      eOp ([pTop, pNK, p2, pK].length + r) hr two h2 true false j = tO j.val (lt_of_lt_of_le j.isLt hr) := fun j hj =>
    Fin.ext (by
      show gOp two true false j.val = j.val
      simp [gOp, show j.val ≠ 2 by omega, show j.val ≠ 3 by omega])
  have e0 : eOp ([pTop, pNK, p2, pK].length + r) hr two h2 true false ⟨0, by show 0 < 4 + r; omega⟩ = tO 0 := rfl
  have e1 : eOp ([pTop, pNK, p2, pK].length + r) hr two h2 true false ⟨1, by show 1 < 4 + r; omega⟩ = tO 1 := rfl
  have e3 : eOp ([pTop, pNK, p2, pK].length + r) hr two h2 true false ⟨3, by show 3 < 4 + r; omega⟩ = tK := rfl
  have e2 : eOp ([pTop, pNK, p2, pK].length + r) hr two h2 true false ⟨2, by show 2 < 4 + r; omega⟩ ≠ tO 0 := fun h => by
    have := congrArg Fin.val h
    simp only [eOp, mkE, Function.Embedding.coeFn_mk, fOp, ofW, gOp, tO] at this
    rcases h2 with rfl | rfl <;> simp at this
  have hlen : [pTop, pNK, p2, pK].length = 4 := rfl
  obtain ⟨ht, hl⟩ := opFrame h (ρLd Mo N K m) (eOp ([pTop, pNK, p2, pK].length + r) hr two h2 true false)
    (ℓ := ℓ) (ℓ' := Function.update ℓ (tO 0) (N * K)) rfl
    (fun j hj => by
      obtain ⟨v, hv⟩ := j
      simp only [hlen] at hj
      interval_cases v
      · rw [e0]; simpa [aGet] using hℓ0
      · rw [e1]; simp [aGet, hℓ1]
      · show _ ≤ pEval (ρLd Mo N K m) p2
        rw [hp2]; exact hℓ2.le
      · rw [e3]; simp [aGet, hK']
      )
    (fun j hj => by
      rw [ge5 j (by simpa [hlen] using hj), top_ρLd]; exact (hsc _ _ (by simpa [hlen] using hj)).le)
    (fun j => by
      by_cases hj : j.val < 4
      · obtain ⟨v, hv⟩ := j
        simp only at hj
        interval_cases v
        · rw [e0, top_ρLd]; exact hℓ0
        · rw [e1, top_ρLd, hℓ1]; exact hMo
        · rw [top_ρLd, hℓ2]; exact hv2
        · rw [e3, top_ρLd, hK']; exact hK
      · rw [ge5 j (by omega), top_ρLd]; exact (hsc _ _ (by omega)).le)
    (fun j hj => by
      obtain ⟨v, hv⟩ := j
      simp only [hlen] at hj
      interval_cases v
      · rw [e0]; simp [aGet]
      · rw [e1, Function.update_of_ne (by simp [tO])]; simp [aGet, hℓ1]
      · rw [Function.update_of_ne e2]
        show pEval (ρLd Mo N K m) p2 ≤ _
        rw [hp2, hℓ2]
      · rw [e3, Function.update_of_ne (by simp [tK, tO])]; simp [aGet, hK']
      )
    (fun j hj => by
      rw [ge5 j (by simpa [hlen] using hj), top_ρLd, Function.update_of_ne (by
        simp only [tO, ne_eq, Fin.mk.injEq]; simp [hlen] at hj; omega)]
      exact (hsc _ _ (by simpa [hlen] using hj)).ge)
    (fun t ht => by
      rw [Function.update_of_ne (fun h => ht ⟨0, by show 0 < 4 + r; omega⟩ (by rw [e0, h]))])
  exact ⟨ht.trans (by rw [top_ρLd]), hl⟩

theorem L2_facts (hMo : N * K ≤ Mo) :
    L2 Mo N K B (tO 0) = Mo ∧ L2 Mo N K B (tO 1) = N * K ∧ L2 Mo N K B (tO 2) = N * K ∧
      L2 Mo N K B tK = K ∧ L2 Mo N K B tN = N ∧
      ∀ j : ℕ, (hj : j < 40) → 5 ≤ j → L2 Mo N K B (tO j hj) = Mo := by
  refine ⟨by simp [L2, L1, tO, encB], by simp [L2, L1, tO, encB], by simp [L2, L1, tO, encB],
    by simp [L2, L1, tO, tK, encB], by simp [L2, L1, tO, tN, encB], fun j hj h5 => ?_⟩
  simp only [L2, L1, Function.update_apply, tO, Fin.mk.injEq]
  rw [if_neg (by omega), if_neg (by omega)]
  exact encB_tO Mo N K B j hj

theorem pEval_wAddRM : pEval (ρLd Mo N K 0) wAddRM = 40 * (N * K) + 44 * N + 7 := by
  simp [wAddRM, pEval, mEval, ρLd]; ring

/-- The time of `add`, `sub` (`mul` with `Wm`): two loads, the operation, the store. -/
def binTime (W : ℕ) (d a b : Fin 200) : ℕ :=
  (2 * max Mo (B a) + 3) * (30 + 10 * (N * K)) + (2 * max Mo (B b) + 3) * (30 + 10 * (N * K)) +
    (2 * Mo + 3) * W + (2 * max Mo (B d) + 3) * 10

theorem instrOK_add (hMo : N * K ≤ Mo) (hK : K ≤ Mo) (hN : N ≤ Mo) (d a b : Fin 200)
    (hd : N * K ≤ B d) :
    InstrOK Mo N K B (.add d a b) (binTime Mo N K B (40 * (N * K) + 44 * N + 7) d a b) := by
  obtain ⟨f0, f1, f2, fK, fN, f5⟩ := L2_facts Mo N K B hMo
  have hop := step5 Mo N K (r := 23) pNK 0 (N * K) (by simp) hMo (P := addRMP) checkT_addRMP
    (by decide) 2 (Or.inl rfl) hMo hK hN (L2 Mo N K B) f2 f0.le f1 fK fN f5
  rw [pEval_wAddRM] at hop
  obtain ⟨ht, hl⟩ := instrOK_opBin Mo N K B addRMP (eOp 28 (by decide) 2 (Or.inl rfl) true true)
    d a b hMo hd _ hop
  exact ⟨hl, ht⟩

theorem instrOK_sub (hMo : N * K ≤ Mo) (hK : K ≤ Mo) (hN : N ≤ Mo) (d a b : Fin 200)
    (hd : N * K ≤ B d) :
    InstrOK Mo N K B (.sub d a b) (binTime Mo N K B (40 * (N * K) + 44 * N + 7) d a b) := by
  obtain ⟨f0, f1, f2, fK, fN, f5⟩ := L2_facts Mo N K B hMo
  have hop := step5 Mo N K (r := 23) pNK 0 (N * K) (by simp) hMo (P := subRMP) checkT_subRMP
    (by decide) 2 (Or.inl rfl) hMo hK hN (L2 Mo N K B) f2 f0.le f1 fK fN f5
  rw [pEval_wAddRM] at hop
  obtain ⟨ht, hl⟩ := instrOK_opBin Mo N K B subRMP (eOp 28 (by decide) 2 (Or.inl rfl) true true)
    d a b hMo hd _ hop
  exact ⟨hl, ht⟩

theorem instrOK_mul (hMo : N * K ≤ Mo) (hK : K ≤ Mo) (hN : N ≤ Mo) (d a b : Fin 200)
    (hd : N * K ≤ B d) :
    InstrOK Mo N K B (.mul d a b) (binTime Mo N K B (pEval (ρLd Mo N K 0) wMulRM) d a b) := by
  obtain ⟨f0, f1, f2, fK, fN, f5⟩ := L2_facts Mo N K B hMo
  have hop := step5 Mo N K (r := 32) pNK 0 (N * K) (by simp) hMo (P := mulRMP) checkT_mulRMP
    (by decide) 2 (Or.inl rfl) hMo hK hN (L2 Mo N K B) f2 f0.le f1 fK fN f5
  obtain ⟨ht, hl⟩ := instrOK_opBin Mo N K B mulRMP (eOp 37 (by decide) 2 (Or.inl rfl) true true)
    d a b hMo hd _ hop
  exact ⟨hl, ht⟩

/-- The bounds after loading a template `t` (after the first operand). -/
def L2t (t : Fin 200) : Fin 247 → ℕ := Function.update (L1 Mo N K B) (tO 2) (B t)

theorem L2t_facts (hMo : N * K ≤ Mo) (t : Fin 200) :
    L2t Mo N K B t (tO 0) = Mo ∧ L2t Mo N K B t (tO 1) = N * K ∧ L2t Mo N K B t (tO 2) = B t ∧
      L2t Mo N K B t tK = K ∧ L2t Mo N K B t tN = N ∧
      ∀ j : ℕ, (hj : j < 40) → 5 ≤ j → L2t Mo N K B t (tO j hj) = Mo := by
  refine ⟨by simp [L2t, L1, tO, encB], by simp [L2t, L1, tO, encB], by simp [L2t, L1, tO],
    by simp [L2t, L1, tO, tK, encB], by simp [L2t, L1, tO, tN, encB], fun j hj h5 => ?_⟩
  simp only [L2t, L1, Function.update_apply, tO, Fin.mk.injEq]
  rw [if_neg (by omega), if_neg (by omega)]
  exact encB_tO Mo N K B j hj

/-- The time of `digit`, `rotB`, `aut`: load, template, the operation, the store. -/
def tmTime (W : ℕ) (d a t : Fin 200) : ℕ :=
  (2 * max Mo (B a) + 3) * (30 + 10 * (N * K)) + (2 * max Mo (B t) + 3) +
    (2 * Mo + 3) * W + (2 * max Mo (B d) + 3) * 10

theorem instrOK_opTm {m : ℕ} (P : Prog (m + 1)) (e : Fin (m + 1) ↪ Fin 247) (d a t : Fin 200)
    (hMo : N * K ≤ Mo) (hd : N * K ≤ B d) (ht : B t ≤ Mo) (Top : ℕ)
    (hop : XProg.timeBoundT (.frame e (.prog P)) (L2t Mo N K B t) ≤ Top ∧
      XProg.lenBoundT (.frame e (.prog P)) (L2t Mo N K B t) ≤
        Function.update (L2t Mo N K B t) (tO 0) (N * K)) :
    XProg.timeBoundT (opTm P e d a t) (encB Mo N K B) ≤
        (2 * max Mo (B a) + 3) * (30 + 10 * (N * K)) + (2 * max Mo (B t) + 3) + Top +
          (2 * max Mo (B d) + 3) * 10 ∧
      XProg.lenBoundT (opTm P e d a t) (encB Mo N K B) ≤ encB Mo N K B := by
  have na1 : ∀ x : Fin 200, tWd x ≠ tO 1 := fun x => ne_tO_tWd 1 (by omega) x
  have na2 : ∀ x : Fin 200, tWd x ≠ tO 2 := fun x => ne_tO_tWd 2 (by omega) x
  obtain ⟨t1, l1⟩ := loadA_step 1 (by omega) a (N := N) (K := K) (encB Mo N K B) (max Mo (B a))
    (by rw [show (⟨1, _⟩ : Fin 247) = tO 1 from rfl, encB_tO]; exact le_max_left _ _)
    (hMo.trans (le_max_left _ _)) (by rw [encB_tWd]; exact le_max_right _ _) (encB_tNK _ _ _ _)
    (encB_tX0 _ _ _ _) (encB_tX1 _ _ _ _) (encB_tX2 _ _ _ _)
  have hL1 : Function.update (encB Mo N K B) ⟨1, by omega⟩ (N * K) = L1 Mo N K B := rfl
  rw [hL1] at l1
  obtain ⟨t2, l2⟩ := loadT_step t (L1 Mo N K B) (max Mo (B t))
    (by simp [L1, Function.update_apply, tO, encB])
    (by simp only [L1, Function.update_of_ne (na1 t)]; rw [encB_tWd]; exact le_max_right _ _)
  have hL2 : Function.update (L1 Mo N K B) (tO 2) (L1 Mo N K B (tWd t)) = L2t Mo N K B t := by
    simp only [L2t, L1, Function.update_of_ne (na1 t), encB_tWd]
  rw [hL2] at l2
  obtain ⟨t4, l4⟩ := store_step d (N := N) (K := K) (Function.update (L2t Mo N K B t) (tO 0) (N * K))
    (max Mo (B d)) (by simp) (by simp [L2t, L1, Function.update_apply, tO]; omega)
    (by simp [L2t, L1, Function.update_apply, tO]; omega) (hMo.trans (le_max_left _ _))
    (by simp only [L2t, L1, Function.update_of_ne (ne_tO_tWd 0 (by omega) d),
          Function.update_of_ne (na1 d), Function.update_of_ne (na2 d)]
        rw [encB_tWd]; exact le_max_right _ _)
  have hl : Function.update (Function.update (Function.update (Function.update
      (Function.update (L2t Mo N K B t) (tO 0) (N * K)) (tWd d) (N * K)) (tO 0) 0) (tO 1) 0)
      (tO 2) 0 ≤ encB Mo N K B := by
    intro u
    simp only [L2t, L1, Function.update_apply]
    split_ifs with h1 h2 h3 h4 <;> first
      | (subst_vars; simp [encB_tO])
      | (subst_vars; rw [encB_tWd]; exact hd)
      | exact le_rfl
      | (subst_vars; simp [encB_tO]; omega)
  refine ⟨?_, ?_⟩
  · show XProg.timeBoundT (loadA 1 _ a) _ + (XProg.timeBoundT (loadT t) _ +
      (XProg.timeBoundT (.frame e (.prog P)) _ + XProg.timeBoundT (store d) _)) ≤ _
    have m2 := (XProg.timeBoundT_mono (loadT t)) l1
    have mL2 := (XProg.lenBoundT_mono (loadT t)) l1
    have m3 := (XProg.timeBoundT_mono (.frame e (.prog P))) (mL2.trans l2)
    have mL3 := (XProg.lenBoundT_mono (.frame e (.prog P))) (mL2.trans l2)
    have m4 := (XProg.timeBoundT_mono (store d)) (mL3.trans hop.2)
    omega
  · show XProg.lenBoundT (store d) (XProg.lenBoundT (.frame e (.prog P))
      (XProg.lenBoundT (loadT t) (XProg.lenBoundT (loadA 1 _ a) _))) ≤ _
    have mL2 := (XProg.lenBoundT_mono (loadT t)) l1
    have mL3 := (XProg.lenBoundT_mono (.frame e (.prog P))) (mL2.trans l2)
    exact ((XProg.lenBoundT_mono (store d)) (mL3.trans hop.2)).trans (l4.trans hl)

theorem instrOK_aut (hMo : N * K ≤ Mo) (hK : K ≤ Mo) (hN : N ≤ Mo) (d a t : Fin 200)
    (hd : N * K ≤ B d) (ht : B t ≤ Mo) :
    InstrOK Mo N K B (.aut d a t) (tmTime Mo N K B (pEval (ρLd Mo N K (B t)) wAut) d a t) := by
  obtain ⟨f0, f1, f2, fK, fN, f5⟩ := L2t_facts Mo N K B hMo t
  have hop := step5 Mo N K (r := 20) pm (B t) (B t) (by simp) ht (P := autMP) checkT_autMP
    (by decide) 2 (Or.inl rfl) hMo hK hN (L2t Mo N K B t) f2 f0.le f1 fK fN f5
  obtain ⟨h1, h2⟩ := instrOK_opTm Mo N K B autMP (eOp 25 (by decide) 2 (Or.inl rfl) true true)
    d a t hMo hd ht _ hop
  exact ⟨h2, h1⟩

theorem instrOK_rotB (hMo : N * K ≤ Mo) (hK : K ≤ Mo) (hN : N ≤ Mo) (d a t : Fin 200)
    (hd : N * K ≤ B d) (ht : B t ≤ Mo) :
    InstrOK Mo N K B (.rotB d a t) (tmTime Mo N K B (pEval (ρLd Mo N K (B t)) wRotB) d a t) := by
  obtain ⟨f0, f1, f2, fK, fN, f5⟩ := L2t_facts Mo N K B hMo t
  have hop := step5 Mo N K (r := 25) pm (B t) (B t) (by simp) ht (P := rotBP) checkT_rotBP
    (by decide) 2 (Or.inl rfl) hMo hK hN (L2t Mo N K B t) f2 f0.le f1 fK fN f5
  obtain ⟨h1, h2⟩ := instrOK_opTm Mo N K B rotBP (eOp 30 (by decide) 2 (Or.inl rfl) true true)
    d a t hMo hd ht _ hop
  exact ⟨h2, h1⟩

theorem instrOK_digit (hMo : N * K ≤ Mo) (hK : K ≤ Mo) (hN : N ≤ Mo) (d a t : Fin 200)
    (hd : N * K ≤ B d) (ht : B t ≤ Mo) :
    InstrOK Mo N K B (.digit d a t) (tmTime Mo N K B (pEval (ρLd Mo N K (B t)) wDigitM) d a t) := by
  obtain ⟨f0, f1, f2, fK, fN, f5⟩ := L2t_facts Mo N K B hMo t
  have hop := step5 Mo N K (r := 26) pm (B t) (B t) (by simp) ht (P := digitRWP)
    checkT_digitRWPm (by decide) 2 (Or.inl rfl) hMo hK hN (L2t Mo N K B t) f2 f0.le f1 fK fN f5
  obtain ⟨h1, h2⟩ := instrOK_opTm Mo N K B digitRWP (eOp 31 (by decide) 2 (Or.inl rfl) true true)
    d a t hMo hd ht _ hop
  exact ⟨h2, h1⟩

/-- The time of `canon`: load, the operation, the store. -/
def unTime (W : ℕ) (d a : Fin 200) : ℕ :=
  (2 * max Mo (B a) + 3) * (30 + 10 * (N * K)) + (2 * Mo + 3) * W + (2 * max Mo (B d) + 3) * 10

theorem instrOK_opUn {m : ℕ} (P : Prog (m + 1)) (e : Fin (m + 1) ↪ Fin 247) (d a : Fin 200)
    (hMo : N * K ≤ Mo) (hd : N * K ≤ B d) (Top : ℕ)
    (hop : XProg.timeBoundT (.frame e (.prog P)) (L1 Mo N K B) ≤ Top ∧
      XProg.lenBoundT (.frame e (.prog P)) (L1 Mo N K B) ≤
        Function.update (L1 Mo N K B) (tO 0) (N * K)) :
    XProg.timeBoundT (opUn P e d a) (encB Mo N K B) ≤
        (2 * max Mo (B a) + 3) * (30 + 10 * (N * K)) + Top + (2 * max Mo (B d) + 3) * 10 ∧
      XProg.lenBoundT (opUn P e d a) (encB Mo N K B) ≤ encB Mo N K B := by
  have na1 : ∀ x : Fin 200, tWd x ≠ tO 1 := fun x => ne_tO_tWd 1 (by omega) x
  obtain ⟨t1, l1⟩ := loadA_step 1 (by omega) a (N := N) (K := K) (encB Mo N K B) (max Mo (B a))
    (by rw [show (⟨1, _⟩ : Fin 247) = tO 1 from rfl, encB_tO]; exact le_max_left _ _)
    (hMo.trans (le_max_left _ _)) (by rw [encB_tWd]; exact le_max_right _ _) (encB_tNK _ _ _ _)
    (encB_tX0 _ _ _ _) (encB_tX1 _ _ _ _) (encB_tX2 _ _ _ _)
  have hL1 : Function.update (encB Mo N K B) ⟨1, by omega⟩ (N * K) = L1 Mo N K B := rfl
  rw [hL1] at l1
  obtain ⟨t4, l4⟩ := store_step d (N := N) (K := K) (Function.update (L1 Mo N K B) (tO 0) (N * K))
    (max Mo (B d)) (by simp) (by simp [L1, Function.update_apply, tO]; omega)
    (by simp [L1, Function.update_apply, tO, encB]) (hMo.trans (le_max_left _ _))
    (by simp only [L1, Function.update_of_ne (ne_tO_tWd 0 (by omega) d),
          Function.update_of_ne (na1 d)]
        rw [encB_tWd]; exact le_max_right _ _)
  have hl : Function.update (Function.update (Function.update (Function.update
      (Function.update (L1 Mo N K B) (tO 0) (N * K)) (tWd d) (N * K)) (tO 0) 0) (tO 1) 0)
      (tO 2) 0 ≤ encB Mo N K B := by
    intro u
    simp only [L1, Function.update_apply]
    split_ifs with h1 h2 h3 h4 <;> first
      | (subst_vars; simp [encB_tO])
      | (subst_vars; rw [encB_tWd]; exact hd)
      | exact le_rfl
      | (subst_vars; simp [encB_tO]; omega)
  refine ⟨?_, ?_⟩
  · show XProg.timeBoundT (loadA 1 _ a) _ + (XProg.timeBoundT (.frame e (.prog P)) _ +
      XProg.timeBoundT (store d) _) ≤ _
    have m3 := (XProg.timeBoundT_mono (.frame e (.prog P))) l1
    have mL3 := (XProg.lenBoundT_mono (.frame e (.prog P))) l1
    have m4 := (XProg.timeBoundT_mono (store d)) (mL3.trans hop.2)
    omega
  · show XProg.lenBoundT (store d) (XProg.lenBoundT (.frame e (.prog P))
      (XProg.lenBoundT (loadA 1 _ a) _)) ≤ _
    have mL3 := (XProg.lenBoundT_mono (.frame e (.prog P))) l1
    exact ((XProg.lenBoundT_mono (store d)) (mL3.trans hop.2)).trans (l4.trans hl)

theorem instrOK_canon (hMo : N * K ≤ Mo) (hK : K ≤ Mo) (hN : N ≤ Mo) (d a : Fin 200)
    (hd : N * K ≤ B d) :
    InstrOK Mo N K B (.canon d a) (unTime Mo N K B (pEval (ρLd Mo N K 0) wCanon) d a) := by
  have hop := step5 Mo N K (r := 23) pNK 0 (N * K) (by simp) hMo (P := canonRP) checkT_canonRP
    (by decide) 43 (Or.inr rfl) hMo hK hN (L1 Mo N K B)
    (by show L1 Mo N K B tOn = N * K; simp [L1, tOn, tO, encB])
    (by simp [L1, tO, encB]) (by simp [L1, tO]) (by simp [L1, tO, tK, encB])
    (by simp [L1, tO, tN, encB])
    (fun j hj h5 => by
      simp only [L1, Function.update_apply, tO, Fin.mk.injEq]
      rw [if_neg (by omega)]; exact encB_tO Mo N K B j hj)
  obtain ⟨h1, h2⟩ := instrOK_opUn Mo N K B canonRP (eOp 28 (by decide) 43 (Or.inr rfl) true true)
    d a hMo hd _ hop
  exact ⟨h2, h1⟩

theorem instrOK_neg (hMo : N * K ≤ Mo) (hK : K ≤ Mo) (hN : N ≤ Mo) (d a : Fin 200)
    (hd : N * K ≤ B d) :
    InstrOK Mo N K B (.neg d a) (unTime Mo N K B (pEval (ρLd Mo N K 0) wNotM) d a) := by
  have hop := step2 Mo N K (r := 9) (P := notP) checkT_notP (by decide) 2 (Or.inl rfl) rfl
    hMo hK hN (L1 Mo N K B) (by simp [L1, tO, encB]) (by simp [L1, tO])
    (fun j hj h2 => by
      simp only [L1, Function.update_apply, tO, Fin.mk.injEq]
      rw [if_neg (by omega)]; exact encB_tO Mo N K B j hj)
  obtain ⟨h1, h2⟩ := instrOK_opUn Mo N K B notP (eOp 11 (by decide) 2 (Or.inl rfl) false false)
    d a hMo hd _ hop
  exact ⟨h2, h1⟩

theorem instrOK_rhoJ (hMo : N * K ≤ Mo) (hK : K ≤ Mo) (hN : N ≤ Mo) (d a t : Fin 200)
    (hd : N * K ≤ B d) (ht : B t ≤ Mo) :
    InstrOK Mo N K B (.rhoJ d a t) (tmTime Mo N K B (pEval (ρLd Mo N K (B t)) wRhoJ) d a t) := by
  obtain ⟨f0, f1, f2, fK, -, f5⟩ := L2t_facts Mo N K B hMo t
  have hop := step4 Mo N K (r := 3) pm (B t) (B t) (by simp) ht (P := rhoJP) checkT_rhoJP
    (by decide) 2 (Or.inl rfl) hMo hK hN (L2t Mo N K B t) f2 f0.le f1 fK
    (fun j hj h4 => by
      rcases Nat.lt_or_ge j 5 with h | h
      · obtain rfl : j = 4 := by omega
        simp [L2t, L1, tO, encB]
      · exact f5 j hj h)
  obtain ⟨h1, h2⟩ := instrOK_opTm Mo N K B rhoJP (eOp 7 (by decide) 2 (Or.inl rfl) true false)
    d a t hMo hd ht _ hop
  exact ⟨h2, h1⟩

/-! ### Whole codes -/

/-- **The cost of each instruction** (the certified sweep polynomials of the operations at the
operation-area size `Mo`, the loads and stores at the sizes of their registers). -/
noncomputable def instrTime : Code → ℕ
  | .add d a b | .sub d a b => binTime Mo N K B (40 * (N * K) + 44 * N + 7) d a b
  | .mul d a b => binTime Mo N K B (pEval (ρLd Mo N K 0) wMulRM) d a b
  | .canon d a => unTime Mo N K B (pEval (ρLd Mo N K 0) wCanon) d a
  | .neg d a => unTime Mo N K B (pEval (ρLd Mo N K 0) wNotM) d a
  | .digit d a t => tmTime Mo N K B (pEval (ρLd Mo N K (B t)) wDigitM) d a t
  | .rotB d a t => tmTime Mo N K B (pEval (ρLd Mo N K (B t)) wRotB) d a t
  | .aut d a t => tmTime Mo N K B (pEval (ρLd Mo N K (B t)) wAut) d a t
  | .rhoJ d a t => tmTime Mo N K B (pEval (ρLd Mo N K (B t)) wRhoJ) d a t
  | .mv d s c => (2 * max (B s) (max (B d) (B c)) + 3) * (20 + 10 * B c) + 3
  | .cp d s => 2 * max (B d) (B s) + 3
  | .drop t c => (2 * max (B t) (B c) + 3) * (20 + 10 * B c) + 3
  | .clr t | .tl t => 2 * B t + 3
  | _ => 3

/-- **The bounds `B` are closed under the code**: every ring result fits its register
(`N K ≤ B d`), every template fits the operation area (`B t ≤ Mo`), every copy fits
(`B s ≤ B d`). -/
def Closed : Code → Prop
  | .add d _ _ | .sub d _ _ | .mul d _ _ | .canon d _ | .neg d _ => N * K ≤ B d
  | .digit d _ t | .rotB d _ t | .aut d _ t | .rhoJ d _ t => N * K ≤ B d ∧ B t ≤ Mo
  | .cp d s => B s ≤ B d
  | .rep _ b => Closed b
  | .seq p q | .ifb _ p q => Closed p ∧ Closed q
  | _ => True

theorem leavesOK_of_closed (hMo : N * K ≤ Mo) (hK : K ≤ Mo) (hN : N ≤ Mo) :
    ∀ c : Code, Closed Mo N K B c → LeavesOK Mo N K B (instrTime Mo N K B) c
  | .add d a b, h => instrOK_add Mo N K B hMo hK hN d a b h
  | .sub d a b, h => instrOK_sub Mo N K B hMo hK hN d a b h
  | .mul d a b, h => instrOK_mul Mo N K B hMo hK hN d a b h
  | .canon d a, h => instrOK_canon Mo N K B hMo hK hN d a h
  | .neg d a, h => instrOK_neg Mo N K B hMo hK hN d a h
  | .digit d a t, h => instrOK_digit Mo N K B hMo hK hN d a t h.1 h.2
  | .rotB d a t, h => instrOK_rotB Mo N K B hMo hK hN d a t h.1 h.2
  | .aut d a t, h => instrOK_aut Mo N K B hMo hK hN d a t h.1 h.2
  | .rhoJ d a t, h => instrOK_rhoJ Mo N K B hMo hK hN d a t h.1 h.2
  | .mv d s c, _ => instrOK_mv Mo N K B d s c
  | .cp d s, h => instrOK_cp Mo N K B d s h
  | .drop t c, _ => instrOK_drop Mo N K B t c
  | .clr t, _ => instrOK_clr Mo N K B t
  | .tl t, _ => instrOK_tl Mo N K B t
  | .nop, _ => instrOK_nop Mo N K B
  | .rep _ b, h => leavesOK_of_closed hMo hK hN b h
  | .seq p q, h => ⟨leavesOK_of_closed hMo hK hN p h.1, leavesOK_of_closed hMo hK hN q h.2⟩
  | .ifb _ p q, h => ⟨leavesOK_of_closed hMo hK hN p h.1, leavesOK_of_closed hMo hK hN q h.2⟩

/-- **The clock of a compiled code**: from the per-tape bounds `encB Mo N K B` (closed under the
code), at most `vmTime Mo N K B (instrTime Mo N K B) c` steps, and the bounds are kept. -/
theorem compile_time (hMo : N * K ≤ Mo) (hK : K ≤ Mo) (hN : N ≤ Mo) (c : Code)
    (hc : Closed Mo N K B c) :
    XProg.timeBoundT (compile c) (encB Mo N K B) ≤ vmTime Mo N K B (instrTime Mo N K B) c ∧
      XProg.lenBoundT (compile c) (encB Mo N K B) ≤ encB Mo N K B :=
  let h := compile_bounds Mo N K B _ c (leavesOK_of_closed Mo N K B hMo hK hN c hc)
  ⟨h.time, h.len⟩

end Ops

end RingVM

end SigabaNeo.Tape
