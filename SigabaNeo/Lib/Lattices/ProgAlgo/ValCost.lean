import SigabaNeo.Lib.Lattices.ProgAlgo.ValWF

/-!
# The cost of compiled codes

Per-tape time bounds of `compileA cert c` from **static word bounds**: every word `x` stays below
`B x` during the run (the machine never lengthens a word except by `cp` into a word of a larger
bound and the result of a `gate`), the step's tapes below `bs`, the template `TV` at `V`, the
scratch blank between instructions. Each instruction is charged only its own frame
(`frame_of_check` with certificates of `inP`, `outP`, `mvPc`, `dropPc`, …); a loop round is charged
a sweep of the whole store (`2 M + 3`, `M` the longest bound).
-/

namespace SigabaNeo.Tape

namespace ValVM

open Sym Prog

/-! ### The certificates of the instruction programs -/

/-- The variable `i`. -/
def pX (i : ℕ) : Poly := [((List.replicate i 0) ++ [1], 1)]

theorem mEval_X : ∀ (ρ : List ℕ) (i : ℕ), mEval ρ ((List.replicate i 0) ++ [1]) = ρ.getD i 0
  | ρ, 0 => by cases ρ <;> simp [mEval]
  | ρ, i + 1 => by
    rw [List.replicate_succ, List.cons_append, mEval, pow_zero, one_mul, mEval_X ρ.tail i]
    cases ρ <;> simp

@[simp] theorem pEval_X (ρ : List ℕ) (i : ℕ) : pEval ρ (pX i) = ρ.getD i 0 := by
  simp [pX, pEval, mEval_X]

/-- The abstract store of the variables `1 … n` on the tapes `0 … n − 1`. -/
def xs (n : ℕ) : Asg := (List.range n).map fun j => pX (j + 1)

theorem check_inP : check 8 inP (xs 6) [pX 2, pX 2, pX 3, [], [], []] [([], 7), ([0, 0, 1], 6)] = true := by
  decide +kernel
theorem check_mvPc : check 8 mvPc (xs 5) [pX 1, pX 2, [], [], pX 5] [([], 4), ([0, 0, 0, 0, 0, 1], 6)] = true := by
  decide +kernel
theorem check_dropPc : check 8 dropPc (xs 3) [pX 1, [], pX 3] [([], 3), ([0, 0, 0, 1], 3)] = true := by
  decide +kernel
theorem check_outP : check 8 outP (xs 4) [[], [], [], pX 1] [([], 4)] = true := by decide +kernel
theorem check_cp : check 8 (Prog.cp 0 1 : Prog 2) (xs 2) [pX 2, pX 2] [([], 1)] = true := by
  decide +kernel
theorem check_clr : check 8 (Prog.clr 0 : Prog 1) (xs 1) [[]] [([], 1)] = true := by decide +kernel
theorem check_tl : check 8 (Prog.tl 0 : Prog 1) (xs 1) [pX 1] [([], 1)] = true := by decide +kernel
theorem check_nop : check 8 (Prog.nop 0 : Prog 1) (xs 1) [pX 1] [([], 1)] = true := by
  decide +kernel

/-- The values `top, ℓ (e 0), …` of the variables of a frame. -/
def rhoF {n : ℕ} (top : ℕ) (e : Fin n ↪ Fin 256) (ℓ : Fin 256 → ℕ) : List ℕ :=
  top :: List.ofFn fun j => ℓ (e j)

theorem bnd_xs {n : ℕ} (top : ℕ) (e : Fin n ↪ Fin 256) (ℓ : Fin 256 → ℕ) :
    bnd (rhoF top e ℓ) (xs n) = fun j => ℓ (e j) := by
  funext j
  simp [bnd, aGet, xs, rhoF, List.getD_eq_getElem?_getD]

theorem rhoF_get {n : ℕ} (top : ℕ) (e : Fin n ↪ Fin 256) (ℓ : Fin 256 → ℕ) (j : Fin n) :
    (rhoF top e ℓ).getD (j.val + 1) 0 = ℓ (e j) := by
  simp [rhoF, List.getD_eq_getElem?_getD]

/-- **A framed instruction**, from its certificate. -/
theorem frame_inst {n : ℕ} {p : Prog n} {claim : Asg} {w : Poly}
    (h : check 8 p (xs n) claim w = true) (e : Fin n ↪ Fin 256) (ℓ : Fin 256 → ℕ) (top : ℕ)
    (htop : ∀ j, ℓ (e j) ≤ top) :
    XProg.timeBoundT (.frame e (.prog p)) ℓ ≤ (2 * top + 3) * pEval (rhoF top e ℓ) w ∧
      (∀ j : Fin n, j.val < claim.length →
        XProg.lenBoundT (.frame e (.prog p)) ℓ (e j) ≤ pEval (rhoF top e ℓ) (aGet claim j.val)) ∧
      ∀ t, (∀ j, e j ≠ t) → XProg.lenBoundT (.frame e (.prog p)) ℓ t = ℓ t :=
  frame_of_check h (rhoF top e ℓ) e (by rw [bnd_xs]) htop

/-! ### Invariant bounds -/

/-- From every per-tape bound below `β`, at most `T` steps, and the bounds stay below `β`. -/
def Inv (X : XProg 256) (β : Fin 256 → ℕ) (T : ℕ) : Prop :=
  ∀ ℓ ≤ β, XProg.timeBoundT X ℓ ≤ T ∧ XProg.lenBoundT X ℓ ≤ β

theorem Inv.mono {X : XProg 256} {β : Fin 256 → ℕ} {T T' : ℕ} (h : Inv X β T) (hT : T ≤ T') :
    Inv X β T' := fun ℓ hℓ => ⟨(h ℓ hℓ).1.trans hT, (h ℓ hℓ).2⟩

theorem Inv.seq {X Y : XProg 256} {β : Fin 256 → ℕ} {T U : ℕ} (hX : Inv X β T) (hY : Inv Y β U) :
    Inv (.seq X Y) β (T + U) := fun ℓ hℓ =>
  ⟨Nat.add_le_add (hX ℓ hℓ).1 (hY _ (hX ℓ hℓ).2).1, (hY _ (hX ℓ hℓ).2).2⟩

theorem Inv.ifBit {X Y : XProg 256} {β : Fin 256 → ℕ} {T U : ℕ} (i : Fin 256) (hX : Inv X β T)
    (hY : Inv Y β U) : Inv (.ifBit i X Y) β (max T U + 1) := fun ℓ hℓ =>
  ⟨Nat.add_le_add_right (max_le_max (hX ℓ hℓ).1 (hY ℓ hℓ).1) 1,
    fun t => max_le ((hX ℓ hℓ).2 t) ((hY ℓ hℓ).2 t)⟩

theorem Inv.loop {X : XProg 256} {β : Fin 256 → ℕ} {T : ℕ} (i : Fin 256) (hX : Inv X β T) :
    Inv (.loop i X) β (β i * (2 * supB β + 3 + T + 1) + 2) := fun ℓ hℓ => by
  have hinv : XProg.loopStepT i X β ≤ β := (hX _ (tailB_le i β)).2
  refine ⟨(XProg.timeBoundT_loop_le_of_inv i X hℓ hinv).trans ?_,
    XProg.lenBoundT_loop_le_of_inv i X hℓ hinv⟩
  have := (hX _ (tailB_le i β)).1
  have h1 : Prog.roundTimeT (XProg.timeBoundT X) i β ≤ 2 * supB β + 3 + T := by
    simp only [Prog.roundTimeT]; omega
  exact Nat.add_le_add_right (Nat.mul_le_mul (hℓ i) (by omega)) 2

/-- **A framed instruction** keeps the bounds `β` and takes at most `T` steps. -/
theorem inv_frame {n : ℕ} {p : Prog n} {claim : Asg} {w : Poly}
    (h : check 8 p (xs n) claim w = true) (e : Fin n ↪ Fin 256) (β : Fin 256 → ℕ) (top : ℕ)
    (htop : ∀ j, β (e j) ≤ top) (T : ℕ)
    (hT : ∀ ℓ ≤ β, (2 * top + 3) * pEval (rhoF top e ℓ) w ≤ T)
    (hc : ∀ ℓ ≤ β, ∀ j : Fin n, pEval (rhoF top e ℓ) (aGet claim j.val) ≤ β (e j))
    (hl : claim.length = n) : Inv (.frame e (.prog p)) β T := fun ℓ hℓ => by
  obtain ⟨t1, t2, t3⟩ := frame_inst h e ℓ top (fun j => (hℓ _).trans (htop j))
  refine ⟨t1.trans (hT ℓ hℓ), fun t => ?_⟩
  by_cases ht : ∃ j, e j = t
  · obtain ⟨j, rfl⟩ := ht
    exact (t2 j (by rw [hl]; exact j.isLt)).trans (hc ℓ hℓ j)
  · push_neg at ht
    rw [t3 t ht]; exact hℓ t

/-! ### The bounds of the machine's store -/

/-- The bounds of a state: the step's tapes `bs`, the template `V`, the words `B`, blank scratch. -/
def encB (bs : Fin 132 → ℕ) (V : ℕ) (B : Fin 120 → ℕ) : Fin 256 → ℕ := fun t =>
  if h : t.val < 132 then bs ⟨t.val, h⟩ else if t.val = 132 then V
  else if h' : t.val < 253 then B ⟨t.val - 133, by omega⟩ else 0

section EncB

variable (bs : Fin 132 → ℕ) (V : ℕ) (B : Fin 120 → ℕ)

@[simp] theorem encB_tS (j : Fin 132) : encB bs V B (tS j) = bs j := by
  simp [encB, tS]

@[simp] theorem encB_tTV : encB bs V B tTV = V := by simp [encB, tTV]

@[simp] theorem encB_tWd (x : Fin 120) : encB bs V B (tWd x) = B x := by
  have h1 : ¬ (tWd x).val < 132 := by show ¬ (133 + x.val < 132); omega
  have h2 : (tWd x).val ≠ 132 := by show 133 + x.val ≠ 132; omega
  have h3 : (tWd x).val < 253 := by show 133 + x.val < 253; have := x.isLt; omega
  simp only [encB, dif_neg h1, if_neg h2, dif_pos h3]
  exact congrArg B (Fin.ext (by show 133 + x.val - 133 = x.val; omega))

theorem encB_hi (t : Fin 256) (h : 253 ≤ t.val) : encB bs V B t = 0 := by
  simp only [encB]; rw [dif_neg (by omega), if_neg (by omega), dif_neg (by omega)]

end EncB

theorem pEval_lin (ρ : List ℕ) (c c' i : ℕ) :
    pEval ρ [([], c), (List.replicate i 0 ++ [1], c')] = c + c' * ρ.getD i 0 := by
  simp [pEval, mEval, mEval_X]

theorem pEval_const (ρ : List ℕ) (c : ℕ) : pEval ρ [([], c)] = c := by simp [pEval, mEval]

theorem pEval_aGet_X (ρ : List ℕ) (σ : Asg) (j i : ℕ) (h : aGet σ j = pX i) :
    pEval ρ (aGet σ j) = ρ.getD i 0 := by rw [h, pEval_X]

theorem pEval_aGet_nil (ρ : List ℕ) (σ : Asg) (j : ℕ) (h : aGet σ j = []) :
    pEval ρ (aGet σ j) = 0 := by rw [h]; rfl

theorem rhoF_getD {n : ℕ} (top : ℕ) (e : Fin n ↪ Fin 256) (ℓ : Fin 256 → ℕ) (i : ℕ) (hi : i < n) :
    (rhoF top e ℓ).getD (i + 1) 0 = ℓ (e ⟨i, hi⟩) := rhoF_get top e ℓ ⟨i, hi⟩

/-! ### The instructions -/

section Inst

variable (bs : Fin 132 → ℕ) (V : ℕ) (B : Fin 120 → ℕ)

theorem fIn_vals (i : Fin 132) (a : Fin 120) :
    fIn i a 0 = tS i ∧ fIn i a 1 = tTV ∧ fIn i a 2 = tWd a ∧ 253 ≤ (fIn i a 3).val ∧
      253 ≤ (fIn i a 4).val ∧ 253 ≤ (fIn i a 5).val := by
  refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_, ?_, ?_, ?_⟩ <;> simp [fIn, ofV, tS, tTV, tWd]

/-- An operand in. -/
theorem inv_inP (i : Fin 132) (a : Fin 120) (hV : V ≤ bs i) :
    Inv (.frame (mkE (fIn i a) (fIn_inj i a)) (.prog inP)) (encB bs V B)
      ((2 * max (bs i) (max V (B a)) + 3) * (7 + 6 * V)) := by
  obtain ⟨f0, f1, f2, f3, f4, f5⟩ := fIn_vals i a
  have hb : ∀ j : Fin 6, encB bs V B (mkE (fIn i a) (fIn_inj i a) j) =
      ![bs i, V, B a, 0, 0, 0] j := by
    intro j
    show encB bs V B (fIn i a j) = _
    fin_cases j
    · simp [f0]
    · simp [f1]
    · simp [f2]
    · simp [encB_hi _ _ _ _ f3]
    · simp [encB_hi _ _ _ _ f4]
    · simp [encB_hi _ _ _ _ f5]
  refine inv_frame check_inP _ _ (max (bs i) (max V (B a))) (fun j => ?_) _ (fun ℓ hℓ => ?_)
    (fun ℓ hℓ j => ?_) rfl
  · rw [hb]; fin_cases j <;> simp
  · have h1 : ℓ (mkE (fIn i a) (fIn_inj i a) ⟨1, by decide⟩) ≤ V := by
      have := hℓ (mkE (fIn i a) (fIn_inj i a) ⟨1, by decide⟩); rw [hb] at this; exact this
    rw [show ([([], 7), ([0, 0, 1], 6)] : Poly) = [([], 7), (List.replicate 2 0 ++ [1], 6)] from rfl,
      pEval_lin, rhoF_getD _ _ _ 1 (by decide)]
    exact Nat.mul_le_mul_left _ (by omega)
  · have h1 : ℓ (mkE (fIn i a) (fIn_inj i a) ⟨1, by decide⟩) ≤ V := by
      have := hℓ (mkE (fIn i a) (fIn_inj i a) ⟨1, by decide⟩); rw [hb] at this; exact this
    have h2 : ℓ (mkE (fIn i a) (fIn_inj i a) ⟨2, by decide⟩) ≤ B a := by
      have := hℓ (mkE (fIn i a) (fIn_inj i a) ⟨2, by decide⟩); rw [hb] at this; exact this
    rw [hb]
    fin_cases j
    · rw [pEval_aGet_X _ _ _ 2 rfl, rhoF_getD _ _ _ 1 (by decide)]; exact h1.trans hV
    · rw [pEval_aGet_X _ _ _ 2 rfl, rhoF_getD _ _ _ 1 (by decide)]; exact h1
    · rw [pEval_aGet_X _ _ _ 3 rfl, rhoF_getD _ _ _ 2 (by decide)]; exact h2
    all_goals rw [pEval_aGet_nil _ _ _ rfl]; simp

end Inst

/-- A framed instruction, from the bounds `v` of its tapes. -/
theorem inv_frame' {n : ℕ} {p : Prog n} {claim : Asg} {w : Poly}
    (h : check 8 p (xs n) claim w = true) (e : Fin n ↪ Fin 256) (β : Fin 256 → ℕ) (v : Fin n → ℕ)
    (hv : ∀ j, β (e j) = v j) (top : ℕ) (htop : ∀ j, v j ≤ top) (T : ℕ)
    (hT : ∀ ℓ' : Fin n → ℕ, ℓ' ≤ v → (2 * top + 3) * pEval (top :: List.ofFn ℓ') w ≤ T)
    (hc : ∀ ℓ' : Fin n → ℕ, ℓ' ≤ v → ∀ j : Fin n, pEval (top :: List.ofFn ℓ') (aGet claim j.val) ≤ v j)
    (hl : claim.length = n) : Inv (.frame e (.prog p)) β T :=
  inv_frame h e β top (fun j => (hv j).symm ▸ htop j) T
    (fun ℓ hℓ => hT (fun j => ℓ (e j)) (fun j => (hv j) ▸ hℓ (e j)))
    (fun ℓ hℓ j => (hv j).symm ▸ hc (fun j => ℓ (e j)) (fun j => (hv j) ▸ hℓ (e j)) j) hl

theorem getD_ofFn_succ {n : ℕ} (top : ℕ) (ℓ' : Fin n → ℕ) (i : ℕ) (hi : i < n) :
    (top :: List.ofFn ℓ').getD (i + 1) 0 = ℓ' ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

section Inst2

variable (bs : Fin 132 → ℕ) (V : ℕ) (B : Fin 120 → ℕ)

theorem fOut_vals (d : Fin 120) : fOut d 0 = tS 0 ∧ fOut d 1 = tS 1 ∧ fOut d 2 = tS 2 ∧
    fOut d 3 = tWd d := by
  refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩ <;> simp [fOut, ofV, tS, tWd]

/-- A result out. -/
theorem inv_outP (d : Fin 120) (hd : bs 0 ≤ B d) :
    Inv (.frame (mkE (fOut d) (fOut_inj d)) (.prog outP)) (encB bs V B)
      ((2 * max (max (bs 0) (bs 1)) (max (bs 2) (B d)) + 3) * 4) := by
  obtain ⟨f0, f1, f2, f3⟩ := fOut_vals d
  refine inv_frame' check_outP _ _ ![bs 0, bs 1, bs 2, B d] (fun j => ?_)
    (max (max (bs 0) (bs 1)) (max (bs 2) (B d))) (fun j => ?_) _
    (fun ℓ' _ => ?_) (fun ℓ' hℓ j => ?_) rfl
  · show encB bs V B (fOut d j) = _
    fin_cases j <;> simp [f0, f1, f2, f3]
  · fin_cases j <;> simp
  · rw [pEval_const]
  · fin_cases j
    all_goals first
      | (rw [pEval_aGet_nil _ _ _ rfl]; exact Nat.zero_le _)
      | (rw [pEval_aGet_X _ _ _ 1 rfl, getD_ofFn_succ _ _ 0 (by decide)]
         exact (hℓ 0).trans (by simpa using hd))

theorem fMv_vals (d s : Fin 120) (c : Fin 256) : fMv d s c 0 = tWd s ∧ fMv d s c 1 = tWd d ∧
    253 ≤ (fMv d s c 2).val ∧ 253 ≤ (fMv d s c 3).val ∧ fMv d s c 4 = c := by
  refine ⟨Fin.ext ?_, Fin.ext ?_, ?_, ?_, Fin.ext ?_⟩ <;> simp [fMv, ofV, tWd]

/-- A move of `|c|` bits from the word `s` into the word `d` (`c` a word or `TV`). -/
theorem inv_mvPc (d s : Fin 120) (c : Fin 256) (hi : Function.Injective (fMv d s c)) (vc : ℕ)
    (hc : encB bs V B c = vc) :
    Inv (.frame (mkE (fMv d s c) hi) (.prog mvPc)) (encB bs V B)
      ((2 * max (max (B s) (B d)) vc + 3) * (4 + 6 * vc)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := fMv_vals d s c
  refine inv_frame' check_mvPc _ _ ![B s, B d, 0, 0, vc] (fun j => ?_)
    (max (max (B s) (B d)) vc) (fun j => ?_) _
    (fun ℓ' hℓ => ?_) (fun ℓ' hℓ j => ?_) rfl
  · show encB bs V B (fMv d s c j) = _
    fin_cases j
    · simp [f0]
    · simp [f1]
    · simp [encB_hi _ _ _ _ f2]
    · simp [encB_hi _ _ _ _ f3]
    · simp [f4, hc]
  · fin_cases j <;> simp
  · rw [show ([([], 4), ([0, 0, 0, 0, 0, 1], 6)] : Poly) =
      [([], 4), (List.replicate 5 0 ++ [1], 6)] from rfl, pEval_lin,
      getD_ofFn_succ _ _ 4 (by decide)]
    have : ℓ' ⟨4, by decide⟩ ≤ vc := by have := hℓ ⟨4, by decide⟩; exact this
    exact Nat.mul_le_mul_left _ (by omega)
  · fin_cases j
    · rw [pEval_aGet_X _ _ _ 1 rfl, getD_ofFn_succ _ _ 0 (by decide)]; exact hℓ 0
    · rw [pEval_aGet_X _ _ _ 2 rfl, getD_ofFn_succ _ _ 1 (by decide)]; exact hℓ 1
    · rw [pEval_aGet_nil _ _ _ rfl]; exact Nat.zero_le _
    · rw [pEval_aGet_nil _ _ _ rfl]; exact Nat.zero_le _
    · rw [pEval_aGet_X _ _ _ 5 rfl, getD_ofFn_succ _ _ 4 (by decide)]; exact hℓ 4

theorem fDr_vals (t c : Fin 120) : fDr t c 0 = tWd t ∧ 253 ≤ (fDr t c 1).val ∧ fDr t c 2 = tWd c := by
  refine ⟨Fin.ext ?_, ?_, Fin.ext ?_⟩ <;> simp [fDr, ofV, tWd]

/-- A drop of `|c|` bits of the word `t`. -/
theorem inv_dropPc (t c : Fin 120) (hi : Function.Injective (fDr t c)) :
    Inv (.frame (mkE (fDr t c) hi) (.prog dropPc)) (encB bs V B)
      ((2 * max (B t) (B c) + 3) * (3 + 3 * B c)) := by
  obtain ⟨f0, f1, f2⟩ := fDr_vals t c
  refine inv_frame' check_dropPc _ _ ![B t, 0, B c] (fun j => ?_) (max (B t) (B c))
    (fun j => ?_) _
    (fun ℓ' hℓ => ?_) (fun ℓ' hℓ j => ?_) rfl
  · show encB bs V B (fDr t c j) = _
    fin_cases j
    · simp [f0]
    · simp [encB_hi _ _ _ _ f1]
    · simp [f2]
  · fin_cases j <;> simp
  · rw [show ([([], 3), ([0, 0, 0, 1], 3)] : Poly) =
      [([], 3), (List.replicate 3 0 ++ [1], 3)] from rfl, pEval_lin,
      getD_ofFn_succ _ _ 2 (by decide)]
    have : ℓ' ⟨2, by decide⟩ ≤ B c := by have := hℓ ⟨2, by decide⟩; exact this
    exact Nat.mul_le_mul_left _ (by omega)
  · fin_cases j
    · rw [pEval_aGet_X _ _ _ 1 rfl, getD_ofFn_succ _ _ 0 (by decide)]; exact hℓ 0
    · rw [pEval_aGet_nil _ _ _ rfl]; exact Nat.zero_le _
    · rw [pEval_aGet_X _ _ _ 3 rfl, getD_ofFn_succ _ _ 2 (by decide)]; exact hℓ 2

theorem fCp_vals (d s : Fin 120) : fCp d s 0 = tWd d ∧ fCp d s 1 = tWd s := by
  refine ⟨Fin.ext ?_, Fin.ext ?_⟩ <;> simp [fCp, ofV, tWd]

/-- A copy of the word `s` into the word `d`. -/
theorem inv_cp (d s : Fin 120) (hi : Function.Injective (fCp d s)) (hds : B s ≤ B d) :
    Inv (.frame (mkE (fCp d s) hi) (.prog (Prog.cp 0 1))) (encB bs V B)
      ((2 * max (B d) (B s) + 3) * 1) := by
  obtain ⟨f0, f1⟩ := fCp_vals d s
  refine inv_frame' check_cp _ _ ![B d, B s] (fun j => ?_) (max (B d) (B s)) (fun j => ?_) _
    (fun ℓ' _ => ?_) (fun ℓ' hℓ j => ?_) rfl
  · show encB bs V B (fCp d s j) = _
    fin_cases j
    · simp [f0]
    · simp [f1]
  · fin_cases j <;> simp
  · rw [pEval_const]
  · fin_cases j
    · rw [pEval_aGet_X _ _ _ 2 rfl, getD_ofFn_succ _ _ 1 (by decide)]
      exact (hℓ 1).trans (by simpa using hds)
    · rw [pEval_aGet_X _ _ _ 2 rfl, getD_ofFn_succ _ _ 1 (by decide)]; exact hℓ 1

/-- An instruction on one tape. -/
theorem inv_one {p : Prog 1} {claim : Asg} (h : check 8 p (xs 1) claim [([], 1)] = true)
    (hl : claim.length = 1) (hcl : claim = [[]] ∨ claim = [pX 1]) (t : Fin 256) :
    Inv (.frame (mkE (f1 t) (f1_inj t)) (.prog p)) (encB bs V B) ((2 * encB bs V B t + 3) * 1) := by
  refine inv_frame' h _ _ ![encB bs V B t] (fun j => ?_) (encB bs V B t) (fun j => ?_) _
    (fun ℓ' _ => ?_) (fun ℓ' hℓ j => ?_) hl
  · fin_cases j; rfl
  · fin_cases j; simp
  · rw [pEval_const]
  · fin_cases j
    rcases hcl with rfl | rfl
    · rw [pEval_aGet_nil _ _ _ rfl]; exact Nat.zero_le _
    · rw [pEval_aGet_X _ _ _ 1 rfl, getD_ofFn_succ _ _ 0 (by decide)]; exact hℓ 0

/-- **The step**, framed on the step's tapes. -/
theorem inv_step {P : Prog 132} {Tst : ℕ} (htime : ∀ ℓ ≤ bs, Prog.timeBoundT P ℓ ≤ Tst)
    (hlen : ∀ ℓ ≤ bs, Prog.lenBoundT P ℓ ≤ bs) :
    Inv (.frame eS (.prog P)) (encB bs V B) Tst := fun ℓ hℓ => by
  have h0 : (fun j => ℓ (eS j)) ≤ bs := fun j => by
    have := hℓ (eS j); rwa [show eS j = tS j from rfl, encB_tS] at this
  refine ⟨htime _ h0, fun t => ?_⟩
  show embedF eS ℓ (Prog.lenBoundT P fun j => ℓ (eS j)) t ≤ _
  rcases embedF_cases eS ℓ (Prog.lenBoundT P fun j => ℓ (eS j)) t with ⟨_, h⟩ | ⟨j, hj, h⟩
  · rw [h]; exact hℓ t
  · rw [h, ← hj, show eS j = tS j from rfl, encB_tS]; exact hlen _ h0 j

end Inst2

end ValVM

end SigabaNeo.Tape
