import PE.Impl.ExpLUT.Prog.EncTimeConf
import SigabaNeoStd.Machines.Prog.XAbs

/-!
# Placed per-tape bounds at fixed variable values (tight encryption clock, part 1)

`TB p ρ σ σ' T`: wherever `p` is placed (`map u p`, `u` injective, in a store of any size), from
per-tape bounds below `bnd ρ σ` on its own tapes and `top ρ` on every tape, its tapes end below
`bnd ρ σ'`, every tape stays below `top ρ`, and the compiled clock is at most `T`. It is the
`Sym.Sound` summary of the abstract interpreter (`SigabaNeoStd.Machines.Prog.AbsBound`) evaluated
at one value `ρ` of the variables, so it also covers programs outside the interpreter's fragment
(literal words `putW`), and composes sequentially (`TB.seq`).
-/

namespace AdvancedEncryption.ExpLUT.Prog.EncTight

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Tape.Sym

/-- A placed per-tape bound at the values `ρ`. -/
def TB {n : ℕ} (p : SigabaNeo.Tape.Prog n) (ρ : List ℕ) (σ σ' : Asg) (T : ℕ) : Prop :=
  ∀ (k : ℕ) (u : Fin n → Fin k), Function.Injective u → ∀ ℓ : Fin k → ℕ,
    (∀ j, ℓ (u j) ≤ bnd ρ σ j) → (∀ t, ℓ t ≤ top ρ) →
      (∀ j, lenBoundT (map u p) ℓ (u j) ≤ bnd ρ σ' j) ∧
        (∀ t, lenBoundT (map u p) ℓ t ≤ top ρ) ∧ timeBoundT (map u p) ℓ ≤ T

theorem noGrow_of_check {n fuel : ℕ} {p : SigabaNeo.Tape.Prog n} {σ claim : Asg} {w : Poly}
    (h : check fuel p σ claim w = true) : p.NoGrow := by
  unfold check at h
  rcases hr : absRun fuel p σ with _ | ⟨σ', w'⟩
  · rw [hr] at h; simp at h
  · exact noGrow_of_absRun fuel p hr

/-- **A checked certificate gives a placed bound** at every value of the variables. -/
theorem TB.of_check {n fuel : ℕ} {p : SigabaNeo.Tape.Prog n} {σ claim : Asg} {w : Poly}
    (h : check fuel p σ claim w = true) (ρ : List ℕ) :
    TB p ρ σ (claim ++ List.replicate n pTop) ((2 * top ρ + 3) * pEval ρ w) := by
  have hS := sound_of_check h
  have hg := noGrow_of_check h
  intro k u hu ℓ hℓ hM
  obtain ⟨a, b⟩ := hS ρ k u hu ℓ hℓ hM
  exact ⟨a, lenBoundT_le_const _ (hg.map u) hM, b⟩

theorem TB.seq {n : ℕ} {p q : SigabaNeo.Tape.Prog n} {ρ : List ℕ} {σ σ₁ σ₂ : Asg} {T U : ℕ}
    (hp : TB p ρ σ σ₁ T) (hq : TB q ρ σ₁ σ₂ U) : TB (.seq p q) ρ σ σ₂ (T + U) := by
  intro k u hu ℓ hℓ hM
  obtain ⟨a₁, b₁, c₁⟩ := hp k u hu ℓ hℓ hM
  obtain ⟨a₂, b₂, c₂⟩ := hq k u hu _ a₁ b₁
  exact ⟨a₂, b₂, Nat.add_le_add c₁ c₂⟩

theorem TB.mono {n : ℕ} {p : SigabaNeo.Tape.Prog n} {ρ : List ℕ} {σ₀ σ σ' σ'' : Asg} {T U : ℕ}
    (h : TB p ρ σ σ' T) (h₀ : ∀ j : Fin n, bnd ρ σ₀ j ≤ bnd ρ σ j)
    (h₁ : ∀ j : Fin n, bnd ρ σ' j ≤ bnd ρ σ'' j) (hT : T ≤ U) : TB p ρ σ₀ σ'' U := by
  intro k u hu ℓ hℓ hM
  obtain ⟨a, b, c⟩ := h k u hu ℓ (fun j => (hℓ j).trans (h₀ j)) hM
  exact ⟨fun j => (a j).trans (h₁ j), b, c.trans hT⟩

/-- A placed program leaves the tapes outside its placement alone. -/
theorem lenBoundT_map_off {n k : ℕ} (u : Fin n → Fin k) (p : SigabaNeo.Tape.Prog n)
    {t : Fin k} (ht : ∀ j, u j ≠ t) (ℓ : Fin k → ℕ) : lenBoundT (map u p) ℓ t = ℓ t :=
  lenBoundT_of_preserves t _ (preserves_map_of_not_mem ht p) ℓ

theorem bnd_aSet_apply {n : ℕ} (ρ : List ℕ) (σ : Asg) (i j : Fin n) (P : Poly) :
    bnd ρ (aSet σ i.val P) j = if j = i then pEval ρ P else bnd ρ σ j := by
  rw [bnd_aSet, Function.update_apply]

/-- A literal word: the tape holds exactly the word afterwards. -/
theorem TB.putW {n : ℕ} (i : Fin n) (w : List Bool) (ρ : List ℕ) (σ : Asg)
    (hw : w.length ≤ top ρ) :
    TB (putW i w) ρ σ (aSet σ i.val (pC w.length))
      ((w.length + 1) * (2 * (top ρ + (w.length + 1)) + 5)) := by
  intro k u hu ℓ hℓ hM
  rw [EncW.map_putW_enc, lenBoundT_putW]
  refine ⟨fun j => ?_, fun t => ?_, ?_⟩
  · rw [bnd_aSet_apply, Function.update_apply]
    by_cases hj : j = i
    · subst hj; simp
    · simpa [hj, hu.ne hj] using hℓ j
  · rw [Function.update_apply]; split_ifs
    · exact hw
    · exact hM t
  · have h := timeBoundT_le_pcount (Prog.putW (u i) w) (loopFree_putW _ _) ℓ hM
    rwa [pcount_putW] at h

/-- Clearing a tape. -/
theorem TB.clr {n : ℕ} (i : Fin n) (ρ : List ℕ) (σ : Asg) :
    TB (clr i) ρ σ (aSet σ i.val []) (2 * top ρ + 3) := by
  intro k u hu ℓ hℓ hM
  refine ⟨fun j => ?_, fun t => ?_, ?_⟩
  · show Function.update ℓ (u i) 0 (u j) ≤ _
    rw [bnd_aSet_apply, Function.update_apply]
    by_cases hj : j = i
    · subst hj; simp
    · simpa [hj, hu.ne hj] using hℓ j
  · show Function.update ℓ (u i) 0 t ≤ _
    rw [Function.update_apply]; split_ifs
    · exact Nat.zero_le _
    · exact hM t
  · show 2 * (supB ℓ + 0) + 3 ≤ _
    have := supB_le_const hM
    omega

/-- Copying a tape onto itself (the empty program of the loaders). -/
theorem TB.cpSelf {n : ℕ} (i : Fin n) (ρ : List ℕ) (σ : Asg) :
    TB (cp i i) ρ σ σ (2 * top ρ + 3) := by
  intro k u hu ℓ hℓ hM
  have e : lenBoundT (map u (cp i i)) ℓ = ℓ := by
    funext t
    show Function.update ℓ (u i) (ℓ (u i)) t = ℓ t
    simp
  rw [e]
  refine ⟨hℓ, hM, ?_⟩
  show 2 * (supB ℓ + 0) + 3 ≤ _
  have := supB_le_const hM
  omega

/-- The entries of `claim ++ rest` below `claim.length` are those of `claim`. -/
theorem bnd_append_of_length {n : ℕ} (ρ : List ℕ) (claim rest : Asg) (h : claim.length = n)
    (j : Fin n) : bnd ρ (claim ++ rest) j = bnd ρ claim j := by
  have hj : j.val < claim.length := h ▸ j.isLt
  simp only [bnd, aGet, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

/-- **A certificate checked at the values `ρ`**: the abstract run succeeds, each claimed tape
dominates the run's bound (capped by the top) numerically, and the clock is at most `T`. -/
def checkAt {n : ℕ} (ρ : List ℕ) (p : SigabaNeo.Tape.Prog n) (σ claim : Asg) (T : ℕ) : Bool :=
  match absRun 8 p σ with
  | some (σ', w) => (List.range claim.length).all (fun j =>
      Nat.ble (min (pEval ρ (aGet σ' j)) (top ρ)) (pEval ρ (aGet claim j))) &&
      Nat.ble ((2 * top ρ + 3) * pEval ρ w) T
  | none => false

theorem TB.of_checkAt {n : ℕ} {ρ : List ℕ} {p : SigabaNeo.Tape.Prog n} {σ claim : Asg} {T : ℕ}
    (h : checkAt ρ p σ claim T = true) : TB p ρ σ (claim ++ List.replicate n pTop) T := by
  unfold checkAt at h
  rcases hr : absRun 8 p σ with _ | ⟨σ', w⟩
  · rw [hr] at h; simp at h
  rw [hr] at h
  simp only [Bool.and_eq_true] at h
  have hS := absRun_sound 8 p hr
  have hg := noGrow_of_absRun 8 p hr
  intro k u hu ℓ hℓ hM
  obtain ⟨a, b⟩ := hS ρ k u hu ℓ hℓ hM
  have hl := lenBoundT_le_const _ (hg.map u) hM
  refine ⟨fun j => ?_, hl, b.trans (Nat.le_of_ble_eq_true h.2)⟩
  by_cases hj : j.val < claim.length
  · have e : bnd ρ (claim ++ List.replicate n pTop) j = pEval ρ (aGet claim j.val) := by
      simp only [bnd, aGet, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    rw [e]
    have hc := Nat.le_of_ble_eq_true (List.all_eq_true.mp h.1 j.val (List.mem_range.mpr hj))
    exact (le_min (a j) (hl (u j))).trans hc
  · have e : bnd ρ (claim ++ List.replicate n pTop) j = top ρ := by
      simp only [bnd, aGet, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega : claim.length ≤ j.val), List.getElem?_replicate]
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      exact pEval_of_isTop rfl ρ
    rw [e]; exact hl (u j)

/-! ### Sequencing equations, stated generically so that no concrete program is unfolded -/

theorem timeBoundT_seqL {k : ℕ} (p q r : SigabaNeo.Tape.Prog k) (ℓ : Fin k → ℕ) :
    timeBoundT (.seq (.seq p q) r) ℓ = timeBoundT p ℓ + timeBoundT q (lenBoundT p ℓ) +
      timeBoundT r (lenBoundT q (lenBoundT p ℓ)) := rfl

theorem lenBoundT_seqL {k : ℕ} (p q r : SigabaNeo.Tape.Prog k) (ℓ : Fin k → ℕ) :
    lenBoundT (.seq (.seq p q) r) ℓ = lenBoundT r (lenBoundT q (lenBoundT p ℓ)) := rfl

theorem timeBoundT_seqR {k : ℕ} (p q r : SigabaNeo.Tape.Prog k) (ℓ : Fin k → ℕ) :
    timeBoundT (.seq p (.seq q r)) ℓ = timeBoundT p ℓ + (timeBoundT q (lenBoundT p ℓ) +
      timeBoundT r (lenBoundT q (lenBoundT p ℓ))) := rfl

theorem lenBoundT_seqR {k : ℕ} (p q r : SigabaNeo.Tape.Prog k) (ℓ : Fin k → ℕ) :
    lenBoundT (.seq p (.seq q r)) ℓ = lenBoundT r (lenBoundT q (lenBoundT p ℓ)) := rfl

theorem xtime_seqL {k : ℕ} (p q r : XProg k) (ℓ : Fin k → ℕ) :
    XProg.timeBoundT (.seq (.seq p q) r) ℓ = XProg.timeBoundT p ℓ +
      XProg.timeBoundT q (XProg.lenBoundT p ℓ) +
        XProg.timeBoundT r (XProg.lenBoundT q (XProg.lenBoundT p ℓ)) := rfl

theorem xlen_seqL {k : ℕ} (p q r : XProg k) (ℓ : Fin k → ℕ) :
    XProg.lenBoundT (.seq (.seq p q) r) ℓ =
      XProg.lenBoundT r (XProg.lenBoundT q (XProg.lenBoundT p ℓ)) := rfl

theorem xtime_prog {k : ℕ} (p : SigabaNeo.Tape.Prog k) (ℓ : Fin k → ℕ) :
    XProg.timeBoundT (.prog p) ℓ = timeBoundT p ℓ := rfl

theorem xlen_prog {k : ℕ} (p : SigabaNeo.Tape.Prog k) (ℓ : Fin k → ℕ) :
    XProg.lenBoundT (.prog p) ℓ = lenBoundT p ℓ := rfl

theorem xtime_seq {k : ℕ} (p q : XProg k) (ℓ : Fin k → ℕ) :
    XProg.timeBoundT (.seq p q) ℓ = XProg.timeBoundT p ℓ + XProg.timeBoundT q (XProg.lenBoundT p ℓ) :=
  rfl

theorem xlen_seq {k : ℕ} (p q : XProg k) (ℓ : Fin k → ℕ) :
    XProg.lenBoundT (.seq p q) ℓ = XProg.lenBoundT q (XProg.lenBoundT p ℓ) := rfl

theorem xtime_frame {m k : ℕ} (e : Fin m ↪ Fin k) (p : XProg m) (ℓ : Fin k → ℕ) :
    XProg.timeBoundT (.frame e p) ℓ = XProg.timeBoundT p (fun j => ℓ (e j)) := rfl

theorem xlen_frame {m k : ℕ} (e : Fin m ↪ Fin k) (p : XProg m) (ℓ : Fin k → ℕ) :
    XProg.lenBoundT (.frame e p) ℓ = embedF e ℓ (XProg.lenBoundT p (fun j => ℓ (e j))) := rfl

end AdvancedEncryption.ExpLUT.Prog.EncTight
