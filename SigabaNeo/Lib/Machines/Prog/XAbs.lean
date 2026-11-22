import SigabaNeo.Lib.Machines.Prog.AbsBound

/-!
# Per-tape bounds of framed programs by symbolic evaluation

`SigabaNeo.Lib.Machines.Prog.AbsBound` certifies plain programs (`Prog`), charging every primitive
the *top* size (a bound on every tape). A framed program (`XProg`) runs each frame on its own tapes
only, so a primitive inside a frame is charged the longest of the frame's tapes: a large program
whose bulky words stay outside the frames of its expensive inner loops costs far less than its
top size times its primitives. Here the abstract interpreter is extended to framed programs:

* `XAst n`: framed programs whose plain leaves (`leaf p T`) and loops (`loop i a T`) carry a
  polynomial `T` bounding every tape of their level;
* `xabs fuel a σ = some (σ', c)`: on abstract stores (one polynomial per tape, none using the
  variable `0`), `σ'` bounds the tapes afterwards and `c` the **steps** (absolute, not sweeps);
* **`xabs_sound`**: `XSound a.toX σ σ' c`: from per-tape bounds `ℓ ≤ bnd ρ σ`,
  `lenBoundT a.toX ℓ ≤ bnd ρ σ'` and `timeBoundT a.toX ℓ ≤ pEval ρ c`, for all values `ρ` of the
  variables.

A leaf is analysed by `absRun` with the variable `0` set to the value of its `T` (`Sound`), a frame
by the summary of its body on the framed tapes, a loop at an invariant store (`fixIter`), charged
the entry bound of its counter times its round.
-/

namespace SigabaNeo.Tape

namespace Sym

open Prog

variable {n : ℕ}

/-! ### Polynomials free of the top variable -/

/-- The monomial does not use the variable `0`. -/
def mNoTop (m : Mono) : Bool := (m.headD 0).beq 0

/-- The polynomial does not use the variable `0`. -/
def pNoTop (p : Poly) : Bool := p.all fun t => mNoTop t.1

/-- No polynomial of the store uses the variable `0`. -/
def aNoTop (σ : Asg) : Bool := σ.all pNoTop

theorem mEval_cons_tail_of_noTop {m : Mono} (h : mNoTop m = true) (x : ℕ) (ρ : List ℕ) :
    mEval (x :: ρ.tail) m = mEval ρ m := by
  cases m with
  | nil => rw [mEval_nil, mEval_nil]
  | cons e es =>
    simp only [mNoTop, List.headD_cons] at h
    rw [Nat.eq_of_beq_eq_true h, mEval, mEval]
    simp

theorem pEval_cons_tail_of_noTop : ∀ {p : Poly}, pNoTop p = true → ∀ (x : ℕ) (ρ : List ℕ),
    pEval (x :: ρ.tail) p = pEval ρ p
  | [], _, _, _ => rfl
  | (m, c) :: p, h, x, ρ => by
    simp only [pNoTop, List.all_cons, Bool.and_eq_true] at h
    rw [pEval, pEval, mEval_cons_tail_of_noTop h.1, pEval_cons_tail_of_noTop h.2]

theorem pNoTop_aGet {σ : Asg} (h : aNoTop σ = true) (i : ℕ) : pNoTop (aGet σ i) = true := by
  unfold aGet
  by_cases hi : i < σ.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.all_eq_true.mp h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]; rfl

theorem bnd_cons_tail_of_noTop {σ : Asg} (h : aNoTop σ = true) (x : ℕ) (ρ : List ℕ) :
    (bnd (x :: ρ.tail) σ : Fin n → ℕ) = bnd ρ σ :=
  funext fun t => pEval_cons_tail_of_noTop (pNoTop_aGet h t.val) x ρ

/-- Every tape `t < n` of the store is below `T`. -/
def allLe (σ : Asg) (T : Poly) (n : ℕ) : Bool := (List.range n).all fun t => pLe (aGet σ t) T

theorem allLe_spec {σ : Asg} {T : Poly} (h : allLe σ T n = true) (ρ : List ℕ) (t : Fin n) :
    pEval ρ (aGet σ t.val) ≤ pEval ρ T :=
  pEval_le_of_pLe ρ (List.all_eq_true.mp h t.val (List.mem_range.mpr t.isLt))

/-! ### Substitution of polynomials for the variables -/

/-- `p ^ e`. -/
def pPow (p : Poly) : ℕ → Poly
  | 0 => pC 1
  | e + 1 => pMul p (pPow p e)

@[simp] theorem pEval_pPow (ρ : List ℕ) (p : Poly) : ∀ e, pEval ρ (pPow p e) = pEval ρ p ^ e
  | 0 => by simp [pPow]
  | e + 1 => by rw [pPow, pEval_pMul, pEval_pPow ρ p e, pow_succ, Nat.mul_comm]

/-- A monomial with the polynomials `θ` substituted for the variables. -/
def mSubst : List Poly → Mono → Poly
  | _, [] => pC 1
  | θ, e :: es => pMul (pPow (θ.headD []) e) (mSubst θ.tail es)

/-- A polynomial with the polynomials `θ` substituted for the variables. -/
def pSubst (θ : List Poly) : Poly → Poly
  | [] => []
  | (m, c) :: p => pAdd (pScale [] c (mSubst θ m)) (pSubst θ p)

theorem headD_map_pEval (ρ : List ℕ) (θ : List Poly) :
    (θ.map (pEval ρ)).headD 0 = pEval ρ (θ.headD []) := by
  cases θ <;> rfl

theorem pEval_mSubst (ρ : List ℕ) : ∀ (θ : List Poly) (m : Mono),
    pEval ρ (mSubst θ m) = mEval (θ.map (pEval ρ)) m
  | θ, [] => by simp [mSubst, mEval_nil]
  | θ, e :: es => by
    rw [mSubst, pEval_pMul, pEval_pPow, pEval_mSubst ρ θ.tail es, mEval, headD_map_pEval,
      List.map_tail]

theorem pEval_pSubst (ρ : List ℕ) (θ : List Poly) : ∀ p : Poly,
    pEval ρ (pSubst θ p) = pEval (θ.map (pEval ρ)) p
  | [] => rfl
  | (m, c) :: p => by
    rw [pSubst, pEval_pAdd, pEval_pScale, pEval_mSubst, pEval_pSubst ρ θ p, pEval, mEval_nil]
    ring

theorem pEval_aGet_map_pSubst (ρ : List ℕ) (θ : List Poly) (τ : Asg) (j : ℕ) :
    pEval ρ (aGet (τ.map (pSubst θ)) j) = pEval (θ.map (pEval ρ)) (aGet τ j) := by
  unfold aGet
  by_cases hj : j < τ.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj,
      List.getElem_map, pEval_pSubst]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]; rfl

/-- **A placed subprogram with a summary at substituted variables**: the summary `Sound p τ τ' w`
holds at every value of its variables, here the values of the polynomials `θ` of the caller's
variables (`θ` heads with the caller's level bound `T`, standing for the summary's top). -/
theorem Sound.callSubst {m : ℕ} {v : Fin m → Fin n} (hv : Function.Injective v) {p : Prog m}
    {τ τ' : Asg} {w : Poly} (hS : Sound p τ τ' w) (θ : List Poly) (T : Poly)
    (hθ : θ.headD [] = T) {σ : Asg} (ρ : List ℕ) {ℓ : Fin n → ℕ} (hℓ : ℓ ≤ bnd ρ σ)
    (hT : ∀ t, ℓ t ≤ pEval ρ T)
    (hin : ∀ j : Fin m, pEval ρ (aGet σ (v j).val) ≤ pEval ρ (pSubst θ (aGet τ j.val))) :
    Prog.lenBoundT (map v p) ℓ ≤ bnd ρ (setMany v (τ'.map (pSubst θ)) σ (List.finRange m)) ∧
      Prog.timeBoundT (map v p) ℓ ≤ (2 * pEval ρ T + 3) * pEval ρ (pSubst θ w) := by
  set ρ' := θ.map (pEval ρ)
  have htop : top ρ' = pEval ρ T := by rw [top, headD_map_pEval, hθ]
  have hin' : ∀ j, ℓ (id (v j)) ≤ bnd ρ' τ j := fun j =>
    ((hℓ (v j)).trans (hin j)).trans (le_of_eq (pEval_pSubst ρ θ _))
  obtain ⟨a, b⟩ := hS ρ' n (id ∘ v) (Function.injective_id.comp hv) ℓ hin'
    (fun t => (hT t).trans htop.ge)
  rw [htop, ← pEval_pSubst] at b
  refine ⟨fun t => ?_, b⟩
  by_cases ht : ∃ j, v j = t
  · obtain ⟨j, rfl⟩ := ht
    show _ ≤ pEval ρ (aGet (setMany v (τ'.map (pSubst θ)) σ (List.finRange m)) (v j).val)
    rw [aGet_setMany_of_mem hv _ _ σ j (List.mem_finRange j), pEval_aGet_map_pSubst]
    exact a j
  · push Not at ht
    rw [lenBoundT_of_preserves t _ (preserves_map_of_not_mem (u := v) ht p) ℓ]
    refine (hℓ t).trans (le_of_eq ?_)
    show pEval ρ (aGet σ t.val) = pEval ρ (aGet (setMany v _ σ (List.finRange m)) t.val)
    rw [aGet_setMany_of_not_mem v _ _ _ σ (fun j _ he => ht j (Fin.val_injective he))]


/-- **A summary from a checked certificate**: the claimed bounds on the first `claim.length`
tapes, the top on the others. -/
theorem sound_of_check {m : ℕ} {fuel : ℕ} {p : Prog m} {σ claim : Asg} {w : Poly}
    (h : check fuel p σ claim w = true) :
    Sound p σ (claim ++ List.replicate m pTop) w := by
  unfold check at h
  rcases hr : absRun fuel p σ with _ | ⟨σ', w'⟩
  · rw [hr] at h; simp at h
  rw [hr] at h
  simp only [Bool.and_eq_true] at h
  have hS := absRun_sound fuel p hr
  have hg := noGrow_of_absRun fuel p hr
  intro ρ k u hu ℓ hℓ hM
  obtain ⟨a, b⟩ := hS ρ k u hu ℓ hℓ hM
  refine ⟨fun j => ?_, b.trans (Nat.mul_le_mul_left _ (pEval_le_of_pLe ρ h.2))⟩
  show _ ≤ pEval ρ (aGet (claim ++ List.replicate m pTop) j.val)
  by_cases hj : j.val < claim.length
  · have e : aGet (claim ++ List.replicate m pTop) j.val = aGet claim j.val := by
      simp only [aGet, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    rw [e]
    have := aLe_spec ρ h.1 j.val
    rw [aGet_take σ' hj] at this
    exact (a j).trans this
  · have e : aGet (claim ++ List.replicate m pTop) j.val = pTop := by
      simp only [aGet, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : claim.length ≤ j.val),
        List.getElem?_replicate]
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]; rfl
    rw [e, pEval_of_isTop rfl]
    exact lenBoundT_le_const _ (hg.map u) hM _

/-- **A summary of a framed program at the values `ρ` of the variables**: from per-tape bounds
`ℓ ≤ bnd ρ σ`, the bounds afterwards are below `bnd ρ σ'` and the steps below `pEval ρ c`. -/
def XSoundAt {n : ℕ} (p : XProg n) (σ σ' : Asg) (c : Poly) (ρ : List ℕ) : Prop :=
  ∀ ℓ : Fin n → ℕ, ℓ ≤ bnd ρ σ →
    XProg.lenBoundT p ℓ ≤ bnd ρ σ' ∧ XProg.timeBoundT p ℓ ≤ pEval ρ c

/-- **A sound summary of a framed program** at every value of the variables satisfying `H`. -/
def XSound {n : ℕ} (H : List ℕ → Prop) (p : XProg n) (σ σ' : Asg) (c : Poly) : Prop :=
  ∀ ρ, H ρ → XSoundAt p σ σ' c ρ

/-- A bound of the tapes `0 … n-1` of a store: the join of their polynomials. -/
def autoT (σ : Asg) (n : ℕ) : Poly := ((List.range n).map (aGet σ)).foldl pJoin []

/-! ### Framed programs with annotations -/

/-- Framed programs whose leaves and loops carry a bound `T` of every tape of their level. -/
inductive XAst (H : List ℕ → Prop) : ℕ → Type
  /-- A plain program, every tape at most `T`. -/
  | leaf {n : ℕ} (p : Prog n) (T : Poly) : XAst H n
  /-- A frame. -/
  | frame {n m : ℕ} (e : Fin m ↪ Fin n) (a : XAst H m) : XAst H n
  | seq {n : ℕ} (a b : XAst H n) : XAst H n
  | ifBit {n : ℕ} (i : Fin n) (a b : XAst H n) : XAst H n
  | ifBlank {n : ℕ} (i : Fin n) (a b : XAst H n) : XAst H n
  /-- A loop, every tape at most `T` during its rounds. -/
  | loop {n : ℕ} (i : Fin n) (a : XAst H n) (T : Poly) : XAst H n
  /-- A plain program, its level bound computed from the abstract store (`autoT`). -/
  | leafA {n : ℕ} (p : Prog n) : XAst H n
  /-- A loop, its level bound computed from the invariant store (`autoT`). -/
  | loopA {n : ℕ} (i : Fin n) (a : XAst H n) : XAst H n
  /-- A placed subprogram `map v p` with a summary of `p` at the variables `θ` (`θ` heads with
  the level bound `T`). -/
  | call {n m : ℕ} (v : Fin m → Fin n) (p : Prog m) (τ τ' : Asg) (w : Poly) (θ : List Poly)
      (T : Poly) (hv : Function.Injective v) (hS : Sound p τ τ' w) : XAst H n
  /-- A framed program with a summary valid under `H` (e.g. a step whose cost is a variable),
  at the variables `θ`. -/
  | fcall {n m : ℕ} (e : Fin m ↪ Fin n) (p : XProg m) (τ τ' : Asg) (c : Poly) (θ : List Poly)
      (hS : ∀ ρ, H ρ → XSoundAt p τ τ' c (θ.map (pEval ρ))) : XAst H n

namespace XAst

/-- The framed program an `XAst` stands for. -/
def toX {H : List ℕ → Prop} : {n : ℕ} → XAst H n → XProg n
  | _, leaf p _ => .prog p
  | _, frame e a => .frame e a.toX
  | _, seq a b => .seq a.toX b.toX
  | _, ifBit i a b => .ifBit i a.toX b.toX
  | _, ifBlank i a b => .ifBlank i a.toX b.toX
  | _, loop i a _ => .loop i a.toX
  | _, call v p _ _ _ _ _ _ _ => .prog (map v p)
  | _, fcall e p _ _ _ _ _ => .frame e p
  | _, leafA p => .prog p
  | _, loopA i a => .loop i a.toX

/-- The cost `2 T + 3` of one primitive or round overhead under `T`. -/
def pSweep (T : Poly) : Poly := pAdd (pMul (pC 2) T) (pC 3)

@[simp] theorem pEval_pSweep (ρ : List ℕ) (T : Poly) : pEval ρ (pSweep T) = 2 * pEval ρ T + 3 := by
  simp [pSweep]

/-- **The abstract interpreter of framed programs**: the store afterwards and the steps. -/
def xabs {H : List ℕ → Prop} (fuel : ℕ) : {n : ℕ} → XAst H n → Asg → Option (Asg × Poly)
  | n, leaf p T, σ =>
    if allLe σ T n && aNoTop σ then
      match absRun fuel p σ with
      | some (σ', w) => if aNoTop σ' && pNoTop w then some (σ', pMul (pSweep T) w) else none
      | none => none
    else none
  | _, @frame _ _ m e a, σ =>
    let τ : Asg := (List.finRange m).map fun j => aGet σ (e j).val
    match xabs fuel a τ with
    | some (τ', c) => some (setMany e τ' σ (List.finRange m), c)
    | none => none
  | _, seq a b, σ => match xabs fuel a σ with
    | none => none
    | some (σ₁, c₁) => match xabs fuel b σ₁ with
      | none => none
      | some (σ₂, c₂) => some (σ₂, pAdd c₁ c₂)
  | _, ifBit _ a b, σ => match xabs fuel a σ, xabs fuel b σ with
    | some (σ₁, c₁), some (σ₂, c₂) => some (aJoin σ₁ σ₂, pAdd (pJoin c₁ c₂) (pC 1))
    | _, _ => none
  | _, ifBlank _ a b, σ => match xabs fuel a σ, xabs fuel b σ with
    | some (σ₁, c₁), some (σ₂, c₂) => some (aJoin σ₁ σ₂, pAdd (pJoin c₁ c₂) (pC 1))
    | _, _ => none
  | n, loop i a T, σ => match fixIter (xabs fuel a) fuel σ with
    | none => none
    | some (σi, _, cb) =>
      if allLe σi T n then
        some (σi, pAdd (pMul (aGet σ i.val) (pAdd cb (pAdd (pSweep T) (pC 1)))) (pC 2))
      else none
  | n, @call _ _ m v _ τ τ' w θ T _ _, σ =>
    if allLe σ T n && decide (θ.headD [] = T) &&
        (List.finRange m).all fun j => pLe (aGet σ (v j).val) (pSubst θ (aGet τ j.val)) then
      some (setMany v (τ'.map (pSubst θ)) σ (List.finRange m), pMul (pSweep T) (pSubst θ w))
    else none
  | n, leafA p, σ =>
    let T := autoT σ n
    if allLe σ T n && aNoTop σ then
      match absRun fuel p σ with
      | some (σ', w) => if aNoTop σ' && pNoTop w then some (σ', pMul (pSweep T) w) else none
      | none => none
    else none
  | n, loopA i a, σ => match fixIter (xabs fuel a) fuel σ with
    | none => none
    | some (σi, _, cb) =>
      let T := autoT σi n
      if allLe σi T n then
        some (σi, pAdd (pMul (aGet σ i.val) (pAdd cb (pAdd (pSweep T) (pC 1)))) (pC 2))
      else none
  | _, @fcall _ _ m e _ τ τ' c θ _, σ =>
    if (List.finRange m).all fun j => pLe (aGet σ (e j).val) (pSubst θ (aGet τ j.val)) then
      some (setMany e (τ'.map (pSubst θ)) σ (List.finRange m), pSubst θ c)
    else none

end XAst

open XAst

theorem XSound.leaf {H : List ℕ → Prop} {p : Prog n} {T : Poly} {σ σ' : Asg} {w : Poly} (h : Sound p σ σ' w)
    (hT : allLe σ T n = true) (hσ : aNoTop σ = true) (hσ' : aNoTop σ' = true)
    (hw : pNoTop w = true) : XSound H (.prog p) σ σ' (pMul (pSweep T) w) := by
  intro ρ _ ℓ hℓ
  set ρ' := pEval ρ T :: ρ.tail
  have e1 : (bnd ρ' σ : Fin n → ℕ) = bnd ρ σ := bnd_cons_tail_of_noTop hσ _ ρ
  have e2 : (bnd ρ' σ' : Fin n → ℕ) = bnd ρ σ' := bnd_cons_tail_of_noTop hσ' _ ρ
  have hM : ∀ t, ℓ t ≤ top ρ' := fun t => (hℓ t).trans (allLe_spec hT ρ t)
  obtain ⟨h1, h2⟩ := h.bounds ρ' (by rw [e1]; exact hℓ) hM
  refine ⟨by rw [← e2]; exact h1, ?_⟩
  show Prog.timeBoundT p ℓ ≤ _
  refine h2.trans (le_of_eq ?_)
  rw [pEval_pMul, pEval_pSweep, pEval_cons_tail_of_noTop hw]
  rfl

theorem aGet_map_finRange {m : ℕ} (f : Fin m → Poly) (j : Fin m) :
    aGet ((List.finRange m).map f) j.val = f j := by
  rw [aGet, List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_finRange]
  rfl

theorem XSound.frame {H : List ℕ → Prop} {m : ℕ} (e : Fin m ↪ Fin n) {p : XProg m} {σ τ' : Asg} {c : Poly}
    (h : XSound H p ((List.finRange m).map fun j => aGet σ (e j).val) τ' c) :
    XSound H (.frame e p) σ (setMany e τ' σ (List.finRange m)) c := by
  intro ρ hH ℓ hℓ
  have hin : (fun j => ℓ (e j)) ≤ bnd ρ ((List.finRange m).map fun j => aGet σ (e j).val) := by
    intro j
    show ℓ (e j) ≤ pEval ρ (aGet _ j.val)
    rw [aGet_map_finRange]
    exact hℓ (e j)
  obtain ⟨h1, h2⟩ := h ρ hH _ hin
  refine ⟨fun t => ?_, h2⟩
  show embedF e ℓ (XProg.lenBoundT p fun j => ℓ (e j)) t ≤ _
  rcases embedF_cases e ℓ (XProg.lenBoundT p fun j => ℓ (e j)) t with ⟨hn, h'⟩ | ⟨j, rfl, h'⟩
  · rw [h']
    refine (hℓ t).trans (le_of_eq ?_)
    show pEval ρ (aGet σ t.val) = pEval ρ (aGet (setMany e τ' σ (List.finRange m)) t.val)
    rw [aGet_setMany_of_not_mem _ τ' _ _ σ]
    intro j _ he
    have : e j = t := Fin.val_injective he
    subst this
    rw [partialInv_self] at hn
    exact Option.some_ne_none _ hn
  · rw [h']
    refine (h1 j).trans (le_of_eq ?_)
    show pEval ρ (aGet τ' j.val) = pEval ρ (aGet (setMany e τ' σ (List.finRange m)) (e j).val)
    rw [aGet_setMany_of_mem e.injective τ' _ σ j (List.mem_finRange j)]

theorem XSound.seq {H : List ℕ → Prop} {p q : XProg n} {σ σ₁ σ₂ : Asg} {c₁ c₂ : Poly}
    (h₁ : XSound H p σ σ₁ c₁) (h₂ : XSound H q σ₁ σ₂ c₂) : XSound H (.seq p q) σ σ₂ (pAdd c₁ c₂) := by
  intro ρ hH ℓ hℓ
  obtain ⟨a₁, b₁⟩ := h₁ ρ hH ℓ hℓ
  obtain ⟨a₂, b₂⟩ := h₂ ρ hH _ a₁
  refine ⟨a₂, ?_⟩
  show XProg.timeBoundT p ℓ + XProg.timeBoundT q (XProg.lenBoundT p ℓ) ≤ _
  rw [pEval_pAdd]; omega

theorem XSound.branch {H : List ℕ → Prop} {p q : XProg n} {σ σ₁ σ₂ : Asg} {c₁ c₂ : Poly}
    (h₁ : XSound H p σ σ₁ c₁) (h₂ : XSound H q σ σ₂ c₂) (ρ : List ℕ) (hH : H ρ) (ℓ : Fin n → ℕ)
    (hℓ : ℓ ≤ bnd ρ σ) :
    (fun t => max (XProg.lenBoundT p ℓ t) (XProg.lenBoundT q ℓ t)) ≤ bnd ρ (aJoin σ₁ σ₂) ∧
      max (XProg.timeBoundT p ℓ) (XProg.timeBoundT q ℓ) + 1 ≤
        pEval ρ (pAdd (pJoin c₁ c₂) (pC 1)) := by
  obtain ⟨a₁, b₁⟩ := h₁ ρ hH ℓ hℓ
  obtain ⟨a₂, b₂⟩ := h₂ ρ hH ℓ hℓ
  obtain ⟨hj₁, hj₂⟩ := le_pEval_pJoin ρ c₁ c₂
  refine ⟨fun t => max_le ((a₁ t).trans (le_aJoin ρ σ₁ σ₂ t.val).1)
    ((a₂ t).trans (le_aJoin ρ σ₁ σ₂ t.val).2), ?_⟩
  rw [pEval_pAdd, pEval_pC]
  omega

theorem XSound.ifBit {H : List ℕ → Prop} (i : Fin n) {p q : XProg n} {σ σ₁ σ₂ : Asg}
    {c₁ c₂ : Poly} (h₁ : XSound H p σ σ₁ c₁) (h₂ : XSound H q σ σ₂ c₂) :
    XSound H (.ifBit i p q) σ (aJoin σ₁ σ₂) (pAdd (pJoin c₁ c₂) (pC 1)) :=
  fun ρ hH ℓ hℓ => XSound.branch h₁ h₂ ρ hH ℓ hℓ

theorem XSound.ifBlank {H : List ℕ → Prop} (i : Fin n) {p q : XProg n} {σ σ₁ σ₂ : Asg}
    {c₁ c₂ : Poly} (h₁ : XSound H p σ σ₁ c₁) (h₂ : XSound H q σ σ₂ c₂) :
    XSound H (.ifBlank i p q) σ (aJoin σ₁ σ₂) (pAdd (pJoin c₁ c₂) (pC 1)) :=
  fun ρ hH ℓ hℓ => XSound.branch h₁ h₂ ρ hH ℓ hℓ

theorem XSound.loop {H : List ℕ → Prop} (i : Fin n) {body : XProg n} {σ σi σb : Asg}
    {cb T : Poly} (h : XSound H body σi σb cb) (hle : aLe σb σi = true)
    (hge : ∀ ρ (j : ℕ), pEval ρ (aGet σ j) ≤ pEval ρ (aGet σi j)) (hT : allLe σi T n = true) :
    XSound H (.loop i body) σ σi
      (pAdd (pMul (aGet σ i.val) (pAdd cb (pAdd (pSweep T) (pC 1)))) (pC 2)) := by
  intro ρ hH ℓ hℓ
  set ℓ' : Fin n → ℕ := bnd ρ σi
  have h0 : ℓ ≤ ℓ' := fun t => (hℓ t).trans (hge ρ t.val)
  have hinv : XProg.loopStepT i body ℓ' ≤ ℓ' := fun t =>
    ((h ρ hH _ (tailB_le i ℓ')).1 t).trans (aLe_spec ρ hle t.val)
  refine ⟨XProg.lenBoundT_loop_le_of_inv i body h0 hinv, ?_⟩
  have ht := XProg.timeBoundT_loop_le_of_inv i body h0 hinv
  have hr := XProg.roundTimeT_le body i ℓ'
  have hs : supB ℓ' ≤ pEval ρ T := supB_le_const fun t => allLe_spec hT ρ t
  have hb := (h ρ hH ℓ' le_rfl).2
  have hi : ℓ i ≤ pEval ρ (aGet σ i.val) := hℓ i
  simp only [pEval_pAdd, pEval_pMul, pEval_pC, pEval_pSweep]
  calc XProg.timeBoundT (.loop i body) ℓ
      ≤ ℓ i * (Prog.roundTimeT (XProg.timeBoundT body) i ℓ' + 1) + 2 := ht
    _ ≤ pEval ρ (aGet σ i.val) * (pEval ρ cb + (2 * pEval ρ T + 3 + 1)) + 2 :=
        Nat.add_le_add_right (Nat.mul_le_mul hi (by omega)) 2

/-! ### Soundness of the interpreter -/

theorem xabs_sound {H : List ℕ → Prop} (fuel : ℕ) : ∀ {n : ℕ} (a : XAst H n) {σ σ' : Asg}
    {c : Poly}, xabs fuel a σ = some (σ', c) → XSound H a.toX σ σ' c := by
  intro n a
  induction a with
  | leaf p T =>
    intro σ σ' c h
    simp only [xabs] at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true] at hc
    rcases hr : absRun fuel p σ with _ | ⟨σ₁, w⟩
    · rw [hr] at h; simp at h
    rw [hr] at h
    simp only at h
    split_ifs at h with hc'
    simp only [Bool.and_eq_true] at hc'
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact XSound.leaf (absRun_sound fuel p hr) hc.1 hc.2 hc'.1 hc'.2
  | frame e a ih =>
    intro σ σ' c h
    simp only [xabs] at h
    rcases hr : xabs fuel a ((List.finRange _).map fun j => aGet σ (e j).val) with _ | ⟨τ', c'⟩
    · rw [hr] at h; simp at h
    rw [hr] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact XSound.frame e (ih hr)
  | seq a b iha ihb =>
    intro σ σ' c h
    rcases h₁ : xabs fuel a σ with _ | ⟨σ₁, c₁⟩
    · simp [xabs, h₁] at h
    rcases h₂ : xabs fuel b σ₁ with _ | ⟨σ₂, c₂⟩
    · simp [xabs, h₁, h₂] at h
    simp only [xabs, h₁, h₂, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact XSound.seq (iha h₁) (ihb h₂)
  | ifBit i a b iha ihb =>
    intro σ σ' c h
    rcases h₁ : xabs fuel a σ with _ | ⟨σ₁, c₁⟩
    · simp [xabs, h₁] at h
    rcases h₂ : xabs fuel b σ with _ | ⟨σ₂, c₂⟩
    · simp [xabs, h₁, h₂] at h
    simp only [xabs, h₁, h₂, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact XSound.ifBit i (iha h₁) (ihb h₂)
  | ifBlank i a b iha ihb =>
    intro σ σ' c h
    rcases h₁ : xabs fuel a σ with _ | ⟨σ₁, c₁⟩
    · simp [xabs, h₁] at h
    rcases h₂ : xabs fuel b σ with _ | ⟨σ₂, c₂⟩
    · simp [xabs, h₁, h₂] at h
    simp only [xabs, h₁, h₂, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact XSound.ifBlank i (iha h₁) (ihb h₂)
  | loop i a T ih =>
    intro σ σ' c h
    rcases hf : fixIter (xabs fuel a) fuel σ with _ | ⟨σi, σb, cb⟩
    · simp [xabs, hf] at h
    simp only [xabs, hf] at h
    split_ifs at h with hT
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hrun, hle, -⟩ := fixIter_spec [] _ fuel σ σi σb cb hf
    exact XSound.loop i (ih hrun) hle (fun ρ j => (fixIter_spec ρ _ fuel σ σi σb cb hf).2.2 j) hT
  | call v p τ τ' w θ T hv hS =>
    intro σ σ' c h
    simp only [xabs] at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro ρ _ ℓ hℓ
    obtain ⟨h1, h2⟩ := Sound.callSubst hv hS θ T hc.1.2 ρ hℓ
      (fun t => (hℓ t).trans (allLe_spec hc.1.1 ρ t))
      (fun j => pEval_le_of_pLe ρ (hc.2 j (List.mem_finRange j)))
    refine ⟨h1, h2.trans (le_of_eq ?_)⟩
    rw [pEval_pMul, pEval_pSweep]
  | leafA p =>
    intro σ σ' c h
    simp only [xabs] at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true] at hc
    rcases hr : absRun fuel p σ with _ | ⟨σ₁, w⟩
    · rw [hr] at h; simp at h
    rw [hr] at h
    simp only at h
    split_ifs at h with hc'
    simp only [Bool.and_eq_true] at hc'
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact XSound.leaf (absRun_sound fuel p hr) hc.1 hc.2 hc'.1 hc'.2
  | loopA i a ih =>
    intro σ σ' c h
    rcases hf : fixIter (xabs fuel a) fuel σ with _ | ⟨σi, σb, cb⟩
    · simp [xabs, hf] at h
    simp only [xabs, hf] at h
    split_ifs at h with hT
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hrun, hle, -⟩ := fixIter_spec [] _ fuel σ σi σb cb hf
    exact XSound.loop i (ih hrun) hle (fun ρ j => (fixIter_spec ρ _ fuel σ σi σb cb hf).2.2 j) hT
  | fcall e p τ τ' c θ hS =>
    intro σ σ' c' h
    simp only [xabs] at h
    split_ifs at h with hc
    simp only [List.all_eq_true] at hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro ρ hH ℓ hℓ
    have hin : (fun j => ℓ (e j)) ≤ bnd (θ.map (pEval ρ)) τ := fun j =>
      ((hℓ (e j)).trans (pEval_le_of_pLe ρ (hc j (List.mem_finRange j)))).trans
        (le_of_eq (pEval_pSubst ρ θ _))
    obtain ⟨h1, h2⟩ := hS ρ hH _ hin
    refine ⟨fun t => ?_, h2.trans (le_of_eq (pEval_pSubst ρ θ c).symm)⟩
    show embedF e ℓ (XProg.lenBoundT p fun j => ℓ (e j)) t ≤ _
    rcases embedF_cases e ℓ (XProg.lenBoundT p fun j => ℓ (e j)) t with ⟨hn, h'⟩ | ⟨j, rfl, h'⟩
    · rw [h']
      refine (hℓ t).trans (le_of_eq ?_)
      show pEval ρ (aGet σ t.val) = pEval ρ (aGet (setMany e _ σ (List.finRange _)) t.val)
      rw [aGet_setMany_of_not_mem _ _ _ _ σ]
      intro j _ he
      have : e j = t := Fin.val_injective he
      subst this
      rw [partialInv_self] at hn
      exact Option.some_ne_none _ hn
    · rw [h']
      refine (h1 j).trans (le_of_eq ?_)
      show pEval (θ.map (pEval ρ)) (aGet τ' j.val) =
        pEval ρ (aGet (setMany e (τ'.map (pSubst θ)) σ (List.finRange _)) (e j).val)
      rw [aGet_setMany_of_mem e.injective _ _ σ j (List.mem_finRange j), pEval_aGet_map_pSubst]

/-! ### Certificates -/

/-- The certificate check: the abstract run succeeds, its store is below `claim` on the first
`claim.length` tapes, and its steps are below `c`. -/
def xcheck {H : List ℕ → Prop} (fuel : ℕ) (a : XAst H n) (σ claim : Asg) (c : Poly) : Bool :=
  match xabs fuel a σ with
  | some (σ', c') => aLe (σ'.take claim.length) claim && pLe c' c
  | none => false

/-- **The per-tape bounds from a checked certificate.** -/
theorem bounds_of_xcheck {H : List ℕ → Prop} {fuel : ℕ} {a : XAst H n} {σ claim : Asg}
    {c : Poly} (h : xcheck fuel a σ claim c = true) (ρ : List ℕ) (hH : H ρ) {ℓ : Fin n → ℕ}
    (hℓ : ℓ ≤ bnd ρ σ) :
    (∀ t : Fin n, t.val < claim.length →
      XProg.lenBoundT a.toX ℓ t ≤ pEval ρ (aGet claim t.val)) ∧
      XProg.timeBoundT a.toX ℓ ≤ pEval ρ c := by
  unfold xcheck at h
  rcases hr : xabs fuel a σ with _ | ⟨σ', c'⟩
  · rw [hr] at h; simp at h
  rw [hr] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := xabs_sound fuel a hr ρ hH ℓ hℓ
  refine ⟨fun t ht => (h1 t).trans ?_, h2.trans (pEval_le_of_pLe ρ h.2)⟩
  have := aLe_spec ρ h.1 t.val
  rwa [aGet_take σ' ht] at this

end Sym

end SigabaNeo.Tape
