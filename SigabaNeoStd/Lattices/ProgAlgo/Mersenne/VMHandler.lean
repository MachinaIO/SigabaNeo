import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMFront
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMCost
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMWF
import SigabaNeoStd.Machines.Prog.SampleTime
import SigabaNeoStd.Machines.Prog.Stream
import SigabaNeoStd.Machines.Inline.Regions

/-!
# A two-input handler around `RingVM` code (package G2, `pubP`/`chalP`)

The handler components of the reduction (`Generic.Comps`) map the words on their tapes `0`, `1`
to a word on tape `0`, every other tape blank. **`ringIO N K ra rb ro tm c : XProg 247`** runs
`RingVM` code `c` as such a component (on the `247` tapes of `RingVM`, i.e. `R = 245` scratch
tapes):

* the inputs are moved into the registers `ra`, `rb` (the operation-area tapes `0`, `1` become
  blank);
* the templates of `RingVM` (`K`, `N`, `N K` zeros, `N K` ones) and the register templates
  `replicate (tm r) false` (every other register) are **built at run time** (`natP`, by doubling:
  `O(log n)` states each, so templates of any length are cheap in states);
* the compiled code runs (`RingVM.law_compile`);
* register `ro` is moved to tape `0` and every other tape is cleared.

**`law_ringIO`**: `law (ringIO …) (io2 a b []) = pure (io2 (exec N K c (initW …) ro) [] [])`.
**`wf_ringIO`**, and the clock **`time_ringIO`**/**`len_ringIO`** from `RingVM.compile_time`.
-/

namespace SigabaNeo.Tape.RingVM.Handler
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.RingVM Cslib
open SigabaNeo.Tape.XProg (natP law_natP natP_bounds natB)
open scoped SigabaNeo.Tape.Prog

/-- The counter tape of the template builders (in the operation area). -/
def cT : Fin 247 := ⟨5, by decide⟩

/-- The registers that receive a built template: all but the two input registers. -/
def tRegs (ra rb : Fin 200) : List (Fin 200) :=
  (List.finRange 200).filter fun r => r ≠ ra ∧ r ≠ rb

/-- The templates to build: the `RingVM` zero templates, then the registers. -/
def tList (N K : ℕ) (ra rb : Fin 200) (tm : Fin 200 → ℕ) : List (Fin 247 × ℕ) :=
  (tK, K) :: (tN, N) :: (tNK, N * K) :: (tRegs ra rb).map fun r => (tWd r, tm r)

/-- The input moves. -/
def inP (ra rb : Fin 200) : Tape.Prog 247 :=
  Prog.cp (tWd ra) 0 ⨾ Prog.clr 0 ⨾ Prog.cp (tWd rb) 1 ⨾ Prog.clr 1

/-- The ones template: `N K` times `true` on tape `43`. -/
def onesP : Tape.Prog 247 := Prog.forN cT tNK (.prim (.snoc tOn true))

/-- **The entry**: inputs, templates, ones template, the counter cleared. -/
def preP (N K : ℕ) (ra rb : Fin 200) (tm : Fin 200 → ℕ) : XProg 247 :=
  .seq (.prog (inP ra rb)) (.seq (tmplsP cT (tList N K ra rb tm)) (.prog (onesP ⨾ Prog.clr cT)))

/-- Clear the listed tapes. -/
def clrL : List (Fin 247) → Tape.Prog 247
  | [] => .prim (.copy 0 0)
  | t :: l => Prog.clr t ⨾ clrL l

/-- All tapes but `0`. -/
def postTapes : List (Fin 247) := (List.finRange 247).filter fun t => t ≠ 0

/-- **The exit**: register `ro` to tape `0`, everything else cleared. -/
def postP (ro : Fin 200) : Tape.Prog 247 := Prog.cp 0 (tWd ro) ⨾ clrL postTapes

/-- **The handler.** -/
noncomputable def ringIO (N K : ℕ) (ra rb ro : Fin 200) (tm : Fin 200 → ℕ) (c : Code) : XProg 247 :=
  .seq (preP N K ra rb tm) (.seq (compile c) (.prog (postP ro)))

/-- The registers at the start of the code. -/
def initW (ra rb : Fin 200) (tm : Fin 200 → ℕ) (a b : List Bool) : St := fun r =>
  if r = ra then a else if r = rb then b else List.replicate (tm r) false

/-! ### Semantics -/

theorem tWd_inj : Function.Injective tWd := by
  intro x y h
  have := congrArg Fin.val h
  simp only [tWd] at this
  exact Fin.ext (by omega)

theorem tWd_val (x : Fin 200) : (tWd x).val = 47 + x.val := rfl

theorem run_clrL (l : List (Fin 247)) (s : Store 247) :
    (clrL l).run s = fun t => if t ∈ l then [] else s t := by
  induction l generalizing s with
  | nil => funext t; simp [clrL, Prog.run_prim, Prim.apply]
  | cons r l ih =>
    rw [clrL, Prog.run_seq, ih]
    funext t
    by_cases ht : t ∈ l <;> by_cases hr : t = r <;> simp [ht, hr]

theorem coinFree_clrL (l : List (Fin 247)) : (clrL l).CoinFree := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    simpa only [clrL, Prog.CoinFree, Prog.coinFreeB, Bool.true_and] using ih

theorem wf_clrL (l : List (Fin 247)) : (clrL l).WF := by
  induction l with
  | nil => trivial
  | cons r l ih => exact ⟨trivial, ih⟩

theorem run_postP (ro : Fin 200) (s : Store 247) :
    (postP ro).run s = io2 (R := 245) (s (tWd ro)) [] [] := by
  rw [postP, Prog.run_seq, Prog.run_copy, run_clrL]
  funext t
  by_cases h0 : t = 0
  · subst h0; simp [postTapes, io2]
  · have hm : t ∈ postTapes := by simp [postTapes, h0]
    rw [if_pos hm]
    have : t.val ≠ 0 := fun h => h0 (Fin.ext h)
    simp only [io2, this, if_false]
    split_ifs <;> rfl

theorem coinFree_postP (ro : Fin 200) : (postP ro).CoinFree := by
  simpa only [postP, Prog.CoinFree, Prog.coinFreeB, Bool.true_and] using coinFree_clrL postTapes

theorem run_inP {ra rb : Fin 200} (hab : ra ≠ rb) (a b : List Bool) :
    (inP ra rb).run (io2 (R := 245) a b []) =
      Function.update (Function.update (io2 (R := 245) [] [] []) (tWd ra) a) (tWd rb) b := by
  have h0 : ∀ x : Fin 200, (0 : Fin 247) ≠ tWd x := fun x h => by
    have := congrArg Fin.val h; simp [tWd] at this; omega
  have h1 : ∀ x : Fin 200, (1 : Fin 247) ≠ tWd x := fun x h => by
    have := congrArg Fin.val h; simp [tWd] at this; omega
  have hab' : tWd rb ≠ tWd ra := fun h => hab (tWd_inj h).symm
  simp only [inP, Prog.run_seq, Prog.run_copy, Prog.run_clear]
  funext t
  by_cases hb : t = tWd rb
  · subst hb; simp [Function.update_apply, hab', io2, (h0 rb).symm, (h1 rb).symm, h1 ra]
  by_cases ha : t = tWd ra
  · subst ha; simp [Function.update_apply, hab'.symm, io2, (h0 ra).symm, (h1 ra).symm]
  by_cases t1 : t = 1
  · subst t1; simp [io2, h1 ra, h1 rb]
  by_cases t0 : t = 0
  · subst t0; simp [io2, h0 ra, h0 rb]
  have e0 : t.val ≠ 0 := fun h => t0 (Fin.ext h)
  have e1 : t.val ≠ 1 := fun h => t1 (Fin.ext h)
  simp [Function.update_apply, io2, hb, ha, t1, t0, e0, e1]

theorem coinFree_inP (ra rb : Fin 200) : (inP ra rb).CoinFree := rfl

theorem tNK_ne_cT : tNK ≠ cT := by decide

theorem tWd_ne_0 (x : Fin 200) : tWd x ≠ 0 := fun h => by
  have := congrArg Fin.val h; simp [tWd] at this

theorem tWd_ne_1 (x : Fin 200) : tWd x ≠ 1 := fun h => by
  have := congrArg Fin.val h; simp [tWd] at this; omega

theorem tWd_ne_cT (x : Fin 200) : tWd x ≠ cT := fun h => by
  have := congrArg Fin.val h; simp [tWd, cT] at this; omega

theorem tWd_ne_tOn (x : Fin 200) : tWd x ≠ tOn := fun h => by
  have := congrArg Fin.val h; simp [tWd, tOn] at this; omega
theorem tOn_ne_cT : tOn ≠ cT := by decide

theorem run_onesP (s : Store 247) (hs : s cT = []) (h0 : s tOn = []) :
    (onesP ⨾ Prog.clr cT).run s = Function.update s tOn (List.replicate (s tNK).length true) := by
  rw [Prog.run_seq, onesP]
  have hfor := Prog.run_forN cT tNK (.prim (.snoc tOn true))
    (fun m => Function.update s tOn (List.replicate m true)) Nat.succ
    (fun m w => by
      rw [Prog.run_prim]
      funext t
      simp only [Prim.apply, Function.update_apply]
      by_cases ht : t = tOn
      · subst ht; simp [tOn_ne_cT, List.replicate_succ']
      · simp [ht])
    0 s (by
      have : Function.update s tOn (List.replicate 0 true) = s := by
        rw [List.replicate_zero, ← h0, Function.update_eq_self]
      rw [this])
  rw [hfor, Prog.run_clear]
  have hit : ∀ n, Nat.succ^[n] 0 = n := fun n => by rw [Nat.succ_iterate]; simp
  rw [hit]
  funext t
  simp only [Function.update_apply]
  by_cases ht : t = cT
  · subst ht; simp [tOn_ne_cT.symm, hs]
  · simp [ht]

theorem mem_tList {N K : ℕ} {ra rb : Fin 200} {tm : Fin 200 → ℕ} {p : Fin 247 × ℕ} :
    p ∈ tList N K ra rb tm ↔ p = (tK, K) ∨ p = (tN, N) ∨ p = (tNK, N * K) ∨
      ∃ r, r ≠ ra ∧ r ≠ rb ∧ p = (tWd r, tm r) := by
  simp only [tList, tRegs, List.mem_cons, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, decide_eq_true_eq]
  constructor
  · rintro (h | h | h | ⟨r, ⟨h1, h2⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨r, h1, h2, rfl⟩))
  · rintro (h | h | h | ⟨r, h1, h2, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨r, ⟨h1, h2⟩, rfl⟩))

theorem tList_ne_cT {N K : ℕ} {ra rb : Fin 200} {tm : Fin 200 → ℕ} :
    ∀ p ∈ tList N K ra rb tm, p.1 ≠ cT := by
  intro p hp
  rcases mem_tList.mp hp with rfl | rfl | rfl | ⟨r, -, -, rfl⟩
  · dsimp only; decide
  · dsimp only; decide
  · dsimp only; decide
  · intro h; have := congrArg Fin.val h; simp [tWd, cT] at this; omega

/-- The tape of a register, read back. -/
theorem enc_tWd (N K : ℕ) (w : St) (x : Fin 200) : enc N K w (tWd x) = w x := by
  have h1 : ¬ (47 + x.val < 40) := by omega
  have h2 : 47 + x.val ≠ 40 := by omega
  have h3 : 47 + x.val ≠ 41 := by omega
  have h4 : 47 + x.val ≠ 42 := by omega
  have h5 : 47 + x.val ≠ 43 := by omega
  simp only [enc, encO, tWd, h1, h2, h3, h4, h5, ↓reduceIte, Nat.le_add_right, ↓reduceDIte,
    Nat.add_sub_cancel_left]

/-- **The store at the start of the code.** -/
theorem pre_store (N K : ℕ) {ra rb : Fin 200} (hab : ra ≠ rb) (tm : Fin 200 → ℕ)
    (a b : List Bool) :
    Function.update (tmplsS (tList N K ra rb tm)
      (Function.update (Function.update (io2 (R := 245) [] [] []) (tWd ra) a) (tWd rb) b)) tOn
      (List.replicate (N * K) true) = enc N K (initW ra rb tm a b) := by
  set s1 := Function.update (Function.update (io2 (R := 245) [] [] []) (tWd ra) a) (tWd rb) b
  funext t
  by_cases hOn : t = tOn
  · subst hOn; simp [enc, encO, tOn]
  rw [Function.update_of_ne hOn]
  have hv43 : t.val ≠ 43 := fun h => hOn (Fin.ext h)
  -- the templates of `RingVM`
  have hmemK : ∀ n, (t, n) ∈ tList N K ra rb tm → (∀ p ∈ tList N K ra rb tm, p.1 = t → p.2 = n) →
      tmplsS (tList N K ra rb tm) s1 t = List.replicate n false :=
    fun n hm hu => tmplsS_apply_of_mem _ _ t n hm hu
  have hreg : ∀ r : Fin 200, ∀ q : Fin 247 × ℕ, q ∈ tList N K ra rb tm → q.1 = tWd r →
      r ≠ ra ∧ r ≠ rb ∧ q.2 = tm r := by
    intro r q hq he
    rcases mem_tList.mp hq with rfl | rfl | rfl | ⟨r', h1, h2, rfl⟩
    · have := congrArg Fin.val he; simp [tWd, tK] at this; omega
    · have := congrArg Fin.val he; simp [tWd, tN] at this; omega
    · have := congrArg Fin.val he; simp [tWd, tNK] at this; omega
    · have := tWd_inj he; subst this; exact ⟨h1, h2, rfl⟩
  by_cases hge : 47 ≤ t.val
  · obtain ⟨r, rfl⟩ : ∃ r : Fin 200, t = tWd r :=
      ⟨⟨t.val - 47, by have := t.isLt; omega⟩, Fin.ext (by simp [tWd]; omega)⟩
    rw [enc_tWd]
    by_cases hra : r = ra
    · subst hra
      rw [tmplsS_apply_of_not_mem _ _ _ fun q hq he => (hreg r q hq he).1 rfl]
      simp [s1, initW, Function.update_of_ne (fun h => hab (tWd_inj h)), Function.update_self]
    by_cases hrb : r = rb
    · subst hrb
      rw [tmplsS_apply_of_not_mem _ _ _ fun q hq he => (hreg r q hq he).2.1 rfl]
      simp [s1, initW, hra]
    · rw [hmemK (tm r) (mem_tList.mpr (Or.inr (Or.inr (Or.inr ⟨r, hra, hrb, rfl⟩))))
        fun q hq he => (hreg r q hq he).2.2]
      simp [initW, hra, hrb]
  · have hnr : ∀ x : Fin 200, t ≠ tWd x := fun x h => by
      subst h; simp [tWd] at hge
    by_cases h40 : t.val = 40
    · have ht : t = tK := Fin.ext h40
      subst ht
      rw [hmemK K (mem_tList.mpr (Or.inl rfl)) fun q hq he => by
        rcases mem_tList.mp hq with rfl | rfl | rfl | ⟨r', -, -, rfl⟩
        · rfl
        · exact absurd he (by dsimp only; decide)
        · exact absurd he (by dsimp only; decide)
        · exact absurd he.symm (hnr r')]
      simp [enc, encO, tK]
    by_cases h41 : t.val = 41
    · have ht : t = tN := Fin.ext h41
      subst ht
      rw [hmemK N (mem_tList.mpr (Or.inr (Or.inl rfl))) fun q hq he => by
        rcases mem_tList.mp hq with rfl | rfl | rfl | ⟨r', -, -, rfl⟩
        · exact absurd he (by dsimp only; decide)
        · rfl
        · exact absurd he (by dsimp only; decide)
        · exact absurd he.symm (hnr r')]
      simp [enc, encO, tN]
    by_cases h42 : t.val = 42
    · have ht : t = tNK := Fin.ext h42
      subst ht
      rw [hmemK (N * K) (mem_tList.mpr (Or.inr (Or.inr (Or.inl rfl)))) fun q hq he => by
        rcases mem_tList.mp hq with rfl | rfl | rfl | ⟨r', -, -, rfl⟩
        · exact absurd he (by dsimp only; decide)
        · exact absurd he (by dsimp only; decide)
        · rfl
        · exact absurd he.symm (hnr r')]
      simp [enc, encO, tNK]
    · have hnm : ∀ q ∈ tList N K ra rb tm, q.1 ≠ t := by
        intro q hq he
        rcases mem_tList.mp hq with rfl | rfl | rfl | ⟨r', -, -, rfl⟩
        · exact h40 (by rw [← he]; rfl)
        · exact h41 (by rw [← he]; rfl)
        · exact h42 (by rw [← he]; rfl)
        · exact hnr r' he.symm
      rw [tmplsS_apply_of_not_mem _ _ _ hnm]
      simp only [s1, Function.update_of_ne (hnr rb), Function.update_of_ne (hnr ra)]
      simp only [io2, enc, encO, h40, h41, h42, hv43, hge, ↓reduceIte, ↓reduceDIte]
      split_ifs <;> rfl

theorem coinFree_onesC : (onesP ⨾ Prog.clr cT).CoinFree := rfl

/-- **The entry ends in the store of the registers `initW`.** -/
theorem law_preP (N K : ℕ) {ra rb : Fin 200} (hab : ra ≠ rb) (tm : Fin 200 → ℕ)
    (a b : List Bool) :
    (preP N K ra rb tm).law (io2 (R := 245) a b []) = PMF.pure (enc N K (initW ra rb tm a b)) := by
  rw [preP, XProg.law_seq, XProg.law_prog, Prog.law_eq_run_of_coinFree _ (coinFree_inP ra rb),
    run_inP hab, PMF.pure_bind, XProg.law_seq]
  set s1 := Function.update (Function.update (io2 (R := 245) [] [] []) (tWd ra) a) (tWd rb) b
  have hc : s1 cT = [] := by
    have h1 : cT ≠ tWd rb := fun h => by have := congrArg Fin.val h; simp [tWd, cT] at this; omega
    have h2 : cT ≠ tWd ra := fun h => by have := congrArg Fin.val h; simp [tWd, cT] at this; omega
    simp only [s1]; rw [Function.update_of_ne h1, Function.update_of_ne h2]; rfl
  rw [law_tmplsP cT _ s1 hc tList_ne_cT, PMF.pure_bind, XProg.law_prog,
    Prog.law_eq_run_of_coinFree _ coinFree_onesC]
  have hcT : tmplsS (tList N K ra rb tm) s1 cT = [] := by
    rw [tmplsS_apply_of_not_mem _ _ _ fun q hq he => tList_ne_cT q hq he]; exact hc
  have hOn : tmplsS (tList N K ra rb tm) s1 tOn = [] := by
    rw [tmplsS_apply_of_not_mem _ _ _ fun q hq he => by
      rcases mem_tList.mp hq with rfl | rfl | rfl | ⟨r', -, -, rfl⟩
      · exact absurd he (by dsimp only; decide)
      · exact absurd he (by dsimp only; decide)
      · exact absurd he (by dsimp only; decide)
      · have := congrArg Fin.val he; simp [tWd, tOn] at this; omega]
    have h1 : tOn ≠ tWd rb := fun h => by have := congrArg Fin.val h; simp [tWd, tOn] at this; omega
    have h2 : tOn ≠ tWd ra := fun h => by have := congrArg Fin.val h; simp [tWd, tOn] at this; omega
    simp only [s1]; rw [Function.update_of_ne h1, Function.update_of_ne h2]; rfl
  have hNK : (tmplsS (tList N K ra rb tm) s1 tNK).length = N * K := by
    rw [tmplsS_apply_of_mem _ _ tNK (N * K) (mem_tList.mpr (Or.inr (Or.inr (Or.inl rfl))))
      fun q hq he => by
        rcases mem_tList.mp hq with rfl | rfl | rfl | ⟨r', -, -, rfl⟩
        · exact absurd he (by dsimp only; decide)
        · exact absurd he (by dsimp only; decide)
        · rfl
        · have := congrArg Fin.val he; simp [tWd, tNK] at this; omega]
    simp
  rw [run_onesP _ hcT hOn, hNK, pre_store N K hab tm a b]

/-- **The law of the handler**: the word of register `ro` after the code. -/
theorem law_ringIO {N K : ℕ} (hN : 0 < N) (hK : 0 < K) {ra rb : Fin 200} (hab : ra ≠ rb)
    (ro : Fin 200) (tm : Fin 200 → ℕ) (c : Code) (a b : List Bool) :
    (ringIO N K ra rb ro tm c).law (io2 (R := 245) a b []) =
      PMF.pure (io2 (R := 245) (exec N K c (initW ra rb tm a b) ro) [] []) := by
  rw [ringIO, XProg.law_seq, law_preP N K hab, PMF.pure_bind, XProg.law_seq, law_compile hN hK,
    PMF.pure_bind, XProg.law_prog, Prog.law_eq_run_of_coinFree _ (coinFree_postP ro), run_postP,
    enc_tWd]

/-! ### Well-formedness -/

theorem wf_tmplsP {k : ℕ} (c : Fin k) : ∀ l : List (Fin k × ℕ), (∀ p ∈ l, p.1 ≠ c) →
    (tmplsP c l).WF
  | [], _ => trivial
  | p :: l, h => ⟨XProg.wf_natP (h p (by simp)).symm p.2,
      wf_tmplsP c l fun q hq => h q (by simp [hq])⟩

theorem wf_preP (N K : ℕ) (ra rb : Fin 200) (tm : Fin 200 → ℕ) : (preP N K ra rb tm).WF :=
  ⟨⟨trivial, trivial, trivial, trivial⟩, wf_tmplsP cT _ tList_ne_cT,
    ⟨⟨trivial, trivial, show cT ∉ (Prim.snoc tOn true).writes by simp [Prim.writes]; decide⟩,
      trivial⟩⟩

/-- **The handler is well formed** when the code's loops leave their counters alone. -/
theorem wf_ringIO (N K : ℕ) (ra rb ro : Fin 200) (tm : Fin 200 → ℕ) (c : Code)
    (hc : loopOkB c = true) : (ringIO N K ra rb ro tm c).WF :=
  ⟨wf_preP N K ra rb tm, wf_compile c hc, trivial, wf_clrL _⟩

/-! ### Bounds -/

theorem tmpls_bounds {k : ℕ} (c : Fin k) : ∀ (l : List (Fin k × ℕ)) (ℓ f : Fin k → ℕ) (M : ℕ),
    (∀ i, ℓ i ≤ M) → ℓ ≤ Function.update f c M →
    (∀ p ∈ l, p.1 ≠ c ∧ p.2 ≤ M ∧ p.2 ≤ f p.1) →
    XProg.lenBoundT (tmplsP c l) ℓ ≤ Function.update f c M ∧
      (∀ i, XProg.lenBoundT (tmplsP c l) ℓ i ≤ M) ∧
      XProg.timeBoundT (tmplsP c l) ℓ ≤ l.length * ((2 * M + 1) * (4 * M + 12)) + (2 * M + 3)
  | [], ℓ, f, M, hM, hf, _ => by
    refine ⟨?_, ?_, ?_⟩
    · show Prim.lenT (.copy c c) ℓ ≤ _
      simp only [Prim.lenT, Function.update_eq_self]; exact hf
    · intro i; show Prim.lenT (.copy c c) ℓ i ≤ _
      simp only [Prim.lenT, Function.update_eq_self]; exact hM i
    · show 2 * (supB ℓ + Prim.pad (.copy c c)) + 3 ≤ _
      have := XProg.supB_le_of hM
      simp only [Prim.pad, List.length_nil, zero_mul, zero_add]; omega
  | p :: l, ℓ, f, M, hM, hf, hl => by
    obtain ⟨hpc, hpM, hpf⟩ := hl p (by simp)
    have hnat := natP_bounds (t := p.1) (c := c) (Ne.symm hpc) p.2 ℓ M hM hpM
    set ℓ' := XProg.lenBoundT (natP p.1 c p.2) ℓ
    have hν : ∀ i, natB p.1 c p.2 ℓ i ≤ M := fun i => by
      simp only [natB]; split_ifs
      · exact hpM
      · exact max_le (hM c) hpM
      · exact hM i
    have hνf : natB p.1 c p.2 ℓ ≤ Function.update f c M := fun i => by
      simp only [natB, Function.update_apply]
      by_cases hi : i = p.1
      · subst hi; simp [hpc, hpf]
      by_cases hic : i = c
      · subst hic; simp [hi]; exact ⟨hM i, hpM⟩
      · simp only [hi, hic, if_false]
        have := hf i; simpa [Function.update_apply, hic] using this
    have ih := tmpls_bounds c l ℓ' f M (fun i => (hnat.1 i).trans (hν i))
      (fun i => (hnat.1 i).trans (hνf i)) (fun q hq => hl q (by simp [hq]))
    refine ⟨ih.1, ih.2.1, ?_⟩
    show XProg.timeBoundT (natP p.1 c p.2) ℓ + XProg.timeBoundT (tmplsP c l) ℓ' ≤ _
    have h1 := hnat.2
    have h2 : (2 * p.2 + 1) * (4 * M + 12) ≤ (2 * M + 1) * (4 * M + 12) :=
      Nat.mul_le_mul_right _ (by omega)
    have h3 := ih.2.2
    generalize (2 * M + 1) * (4 * M + 12) = X at *
    rw [List.length_cons, Nat.succ_mul]
    omega

theorem clrL_bounds (l : List (Fin 247)) (ℓ : Fin 247 → ℕ) (M : ℕ) (hM : ∀ i, ℓ i ≤ M) :
    Prog.lenBoundT (clrL l) ℓ = (fun t => if t ∈ l then 0 else ℓ t) ∧
      Prog.timeBoundT (clrL l) ℓ ≤ (l.length + 1) * (2 * M + 3) := by
  induction l generalizing ℓ with
  | nil =>
    refine ⟨?_, ?_⟩
    · show Prim.lenT (.copy 0 0) ℓ = _
      simp [Prim.lenT]
    · show 2 * (supB ℓ + Prim.pad (.copy 0 0)) + 3 ≤ _
      have := XProg.supB_le_of hM; simp [Prim.pad]; omega
  | cons r l ih =>
    have hM' : ∀ i, Function.update ℓ r 0 i ≤ M := fun i => by
      simp only [Function.update_apply]; split_ifs <;> first | omega | exact hM i
    obtain ⟨h1, h2⟩ := ih (Function.update ℓ r 0) hM'
    refine ⟨?_, ?_⟩
    · show Prog.lenBoundT (clrL l) (Prim.lenT (.clear r) ℓ) = _
      simp only [Prim.lenT, h1]
      funext t
      by_cases ht : t ∈ l <;> by_cases hr : t = r <;> simp [ht, hr]
    · show 2 * (supB ℓ + Prim.pad (.clear r)) + 3 +
        Prog.timeBoundT (clrL l) (Prim.lenT (.clear r) ℓ) ≤ _
      have := XProg.supB_le_of hM
      simp only [Prim.pad, Prim.lenT, List.length_cons] at h2 ⊢
      nlinarith

theorem length_tList_le (N K : ℕ) (ra rb : Fin 200) (tm : Fin 200 → ℕ) :
    (tList N K ra rb tm).length ≤ 203 := by
  have : (tRegs ra rb).length ≤ 200 :=
    (List.length_filter_le _ _).trans (by simp)
  simp only [tList, List.length_cons, List.length_map]
  omega

theorem encB_le (Mo N K : ℕ) (B : Fin 200 → ℕ) (M : ℕ) (hMo : Mo ≤ M) (hK : K ≤ Mo) (hN : N ≤ Mo)
    (hNK : N * K ≤ Mo) (hB : ∀ r, B r ≤ M) : ∀ t, encB Mo N K B t ≤ M := by
  intro t
  simp only [encB]
  split_ifs <;> first | omega | exact hB _

/-- **The entry's bounds**: the registers within `B` (inputs and templates), every tape within
`M`. -/
theorem pre_bounds {N K Mo : ℕ} (hNK : N * K ≤ Mo) (hK : K ≤ Mo) (hN : N ≤ Mo)
    {ra rb : Fin 200} (hab : ra ≠ rb) (tm : Fin 200 → ℕ)
    (B : Fin 200 → ℕ) (La Lb M : ℕ) (hLa : La ≤ B ra) (hLb : Lb ≤ B rb)
    (htm : ∀ r, r ≠ ra → r ≠ rb → tm r ≤ B r) (hMo : Mo ≤ M) (hB : ∀ r, B r ≤ M) :
    XProg.lenBoundT (preP N K ra rb tm) (io2 (R := 245) La Lb 0) ≤ encB Mo N K B ∧
      XProg.timeBoundT (preP N K ra rb tm) (io2 (R := 245) La Lb 0) ≤
        4 * (2 * M + 3) + (203 * ((2 * M + 1) * (4 * M + 12)) + (2 * M + 3)) +
          (2 * (2 * M + 3) + (N * K * (4 * M + 9) + 2)) := by
  have hE := encB_le Mo N K B M hMo hK hN hNK hB
  have hLaM : La ≤ M := hLa.trans (hB ra)
  have hLbM : Lb ≤ M := hLb.trans (hB rb)
  set ℓ0 := io2 (R := 245) La Lb 0
  have hℓ0 : ∀ i, ℓ0 i ≤ M := fun i => by
    simp only [ℓ0, io2]; split_ifs <;> omega
  -- the inputs
  set ℓ1 := Prog.lenBoundT (inP ra rb) ℓ0
  have hab' : ra.val ≠ rb.val := fun h => hab (Fin.ext h)
  have hℓ1 : ∀ i, ℓ1 i = if i = tWd ra then La else if i = tWd rb then Lb else 0 := by
    intro i
    have hX : Function.update (Function.update ℓ0 (tWd ra) (ℓ0 0)) 0 0 1 = Lb := by
      rw [Function.update_of_ne (by decide : (1 : Fin 247) ≠ 0),
        Function.update_of_ne (tWd_ne_1 ra).symm]; rfl
    have h00 : ℓ0 0 = La := rfl
    simp only [ℓ1, inP, Prog.lenBoundT, Prim.lenT]
    rw [hX, h00]
    have hab2 : tWd ra ≠ tWd rb := fun h => hab (tWd_inj h)
    by_cases h1 : i = 1
    · subst h1
      rw [Function.update_self, if_neg (tWd_ne_1 ra).symm, if_neg (tWd_ne_1 rb).symm]
    rw [Function.update_of_ne h1]
    by_cases hb : i = tWd rb
    · subst hb; rw [Function.update_self, if_neg hab2.symm, if_pos rfl]
    rw [Function.update_of_ne hb]
    by_cases h0 : i = 0
    · subst h0
      rw [Function.update_self, if_neg (tWd_ne_0 ra).symm, if_neg (tWd_ne_0 rb).symm]
    rw [Function.update_of_ne h0]
    by_cases ha : i = tWd ra
    · subst ha; rw [Function.update_self, if_pos rfl]
    rw [Function.update_of_ne ha, if_neg ha, if_neg hb]
    simp only [ℓ0, io2]
    have e0 : i.val ≠ 0 := fun h => h0 (Fin.ext h)
    have e1 : i.val ≠ 1 := fun h => h1 (Fin.ext h)
    simp [e0, e1]
  have hℓ1M : ∀ i, ℓ1 i ≤ M := fun i => by
    rw [hℓ1 i]; split_ifs
    · exact hLaM
    · exact hLbM
    · exact Nat.zero_le _
  have hT1 : Prog.timeBoundT (inP ra rb) ℓ0 ≤ 4 * (2 * M + 3) := by
    have hs : ∀ ℓ : Fin 247 → ℕ, (∀ i, ℓ i ≤ M) → supB ℓ ≤ M := fun ℓ h => XProg.supB_le_of h
    simp only [inP, Prog.timeBoundT, Prog.lenBoundT, Prim.lenT, Prim.pad]
    have a1 := hs ℓ0 hℓ0
    have a2 := hs (Function.update ℓ0 (tWd ra) (ℓ0 0)) fun i => by
      simp only [Function.update_apply]; split_ifs <;> exact hℓ0 _
    have a3 := hs (Function.update (Function.update ℓ0 (tWd ra) (ℓ0 0)) 0 0) fun i => by
      simp only [Function.update_apply]; split_ifs <;> first | omega | exact hℓ0 _
    have a4 := hs (Function.update (Function.update (Function.update ℓ0 (tWd ra) (ℓ0 0)) 0 0)
      (tWd rb) (Function.update (Function.update ℓ0 (tWd ra) (ℓ0 0)) 0 0 1)) fun i => by
      simp only [Function.update_apply]; split_ifs <;> first | omega | exact hℓ0 _
    omega
  -- the templates
  set f0 := Function.update (encB Mo N K B) tOn 0
  have hf1 : ℓ1 ≤ Function.update f0 cT M := fun i => by
    rw [hℓ1]
    split_ifs with ha hb
    · subst ha
      rw [Function.update_of_ne (tWd_ne_cT ra)]; simp only [f0]
      rw [Function.update_of_ne (tWd_ne_tOn ra), encB_tWd]
      exact hLa
    · subst hb
      rw [Function.update_of_ne (tWd_ne_cT rb)]; simp only [f0]
      rw [Function.update_of_ne (tWd_ne_tOn rb), encB_tWd]
      exact hLb
    · exact Nat.zero_le _
  have hl : ∀ p ∈ tList N K ra rb tm, p.1 ≠ cT ∧ p.2 ≤ M ∧ p.2 ≤ f0 p.1 := by
    intro p hp
    refine ⟨tList_ne_cT p hp, ?_⟩
    rcases mem_tList.mp hp with rfl | rfl | rfl | ⟨r, h1, h2, rfl⟩
    · refine ⟨by omega, ?_⟩
      show _ ≤ f0 tK
      simp only [f0]
      rw [Function.update_of_ne (show tK ≠ tOn by decide)]
      simp [encB, tK]
    · refine ⟨by omega, ?_⟩
      show _ ≤ f0 tN
      simp only [f0]
      rw [Function.update_of_ne (show tN ≠ tOn by decide)]
      simp [encB, tN]
    · refine ⟨by omega, ?_⟩
      show _ ≤ f0 tNK
      simp only [f0]
      rw [Function.update_of_ne (show tNK ≠ tOn by decide)]
      simp [encB, tNK]
    · have hne : tWd r ≠ tOn := fun h => by
        have := congrArg Fin.val h; simp [tWd, tOn] at this; omega
      refine ⟨(htm r h1 h2).trans (hB r), ?_⟩
      simp only [f0, Function.update_of_ne hne, encB_tWd]
      exact htm r h1 h2
  obtain ⟨hl2, hl2M, hT2⟩ := tmpls_bounds cT (tList N K ra rb tm) ℓ1 f0 M hℓ1M hf1 hl
  set ℓ2 := XProg.lenBoundT (tmplsP cT (tList N K ra rb tm)) ℓ1
  -- the ones template
  have hOn2 : ℓ2 tOn = 0 := by
    have := hl2 tOn
    simp only [f0, Function.update_of_ne tOn_ne_cT, Function.update_self] at this
    omega
  have hNK2 : ℓ2 tNK ≤ N * K := by
    have := hl2 tNK
    simp only [f0, Function.update_of_ne tNK_ne_cT,
      Function.update_of_ne (show tNK ≠ tOn by decide)] at this
    simpa [encB, tNK] using this
  set ℓ3 := Function.update ℓ2 cT (ℓ2 tNK)
  set g := Prog.loopStepT cT (.prim (.snoc tOn true) : Tape.Prog 247)
  set h : ℕ → Fin 247 → ℕ := fun j => Function.update (Function.update ℓ2 cT (N * K)) tOn j
  have hg : ∀ j, g^[j] ℓ3 ≤ h j := by
    intro j
    induction j with
    | zero =>
      intro i
      simp only [Function.iterate_zero, id]
      by_cases h1 : i = tOn
      · subst h1
        simp only [ℓ3, h, Function.update_self, Function.update_of_ne tOn_ne_cT, hOn2, le_refl]
      by_cases h2 : i = cT
      · subst h2
        simp only [ℓ3, h, Function.update_self, Function.update_of_ne h1]; exact hNK2
      · simp only [ℓ3, h, Function.update_of_ne h1, Function.update_of_ne h2, le_refl]
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      intro i
      have hm := Prog.lenBoundT_mono (.prim (.snoc tOn true) : Tape.Prog 247)
        (tailB_mono cT ih) i
      refine hm.trans ?_
      show Prim.lenT (.snoc tOn true) (tailB cT (h j)) i ≤ h (j + 1) i
      simp only [Prim.lenT, tailB]
      by_cases h1 : i = tOn
      · subst h1
        simp only [h, Function.update_self, Function.update_of_ne tOn_ne_cT, le_refl]
      by_cases h2 : i = cT
      · subst h2
        simp only [h, Function.update_of_ne h1, Function.update_self]; omega
      · simp only [h, Function.update_of_ne h1, Function.update_of_ne h2, le_refl]
  have hhM : ∀ j ≤ N * K, ∀ i, h j i ≤ M := fun j hj i => by
    simp only [h, Function.update_apply]
    split_ifs <;> first | omega | exact hl2M i
  have hcnt : ℓ3 cT ≤ N * K := by
    show Function.update ℓ2 cT (ℓ2 tNK) cT ≤ N * K
    rw [Function.update_self]; exact hNK2
  set ℓ4 := Prog.lenBoundT (onesP ⨾ Prog.clr cT) ℓ2
  have hℓ4 : ℓ4 ≤ Function.update (h (N * K)) cT 0 := by
    show Prog.lenBoundT (Prog.clr cT) (Prog.lenBoundT (Prog.loop cT (.prim (.snoc tOn true)))
      (Prog.lenBoundT (Prog.cp cT tNK) ℓ2)) ≤ _
    have hl := iterSupT_le (g := g) (n := ℓ3 cT) (ℓ := ℓ3) (ℓ' := h (N * K)) fun j hj i =>
      (hg j i).trans (by
        simp only [h, Function.update_apply]
        split_ifs <;> omega)
    intro i
    simp only [Prog.lenBoundT, Prim.lenT, Function.update_apply]
    split_ifs
    · exact le_rfl
    · exact hl i
  have hT4 : Prog.timeBoundT (onesP ⨾ Prog.clr cT) ℓ2 ≤ 2 * (2 * M + 3) + (N * K * (4 * M + 9) + 2) := by
    show Prog.timeBoundT (Prog.cp cT tNK) ℓ2 + Prog.timeBoundT (Prog.loop cT
      (.prim (.snoc tOn true))) ℓ3 + Prog.timeBoundT (Prog.clr cT)
        (Prog.lenBoundT (Prog.loop cT (.prim (.snoc tOn true))) ℓ3) ≤ _
    have e1 : Prog.timeBoundT (Prog.cp cT tNK) ℓ2 ≤ 2 * M + 3 := by
      show 2 * (supB ℓ2 + 0) + 3 ≤ _; have := XProg.supB_le_of hl2M; omega
    have e2 : Prog.timeBoundT (Prog.loop cT (.prim (.snoc tOn true))) ℓ3 ≤ N * K * (4 * M + 9) + 2 := by
      refine (Prog.timeBoundT_loop_le cT _ ℓ3 (R := 4 * M + 8) fun j hj => ?_).trans ?_
      · have hb := hhM j (by omega)
        have hs : supB (g^[j] ℓ3) ≤ M := XProg.supB_le_of fun i => (hg j i).trans (hb i)
        have hs' : supB (tailB cT (g^[j] ℓ3)) ≤ M := (supB_mono (tailB_le _ _)).trans hs
        change 2 * supB (g^[j] ℓ3) + 3 + (2 * (supB (tailB cT (g^[j] ℓ3)) + 1) + 3) ≤ _
        omega
      · exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hcnt) 2
    have e3 : ∀ ℓ : Fin 247 → ℕ, (∀ i, ℓ i ≤ M) → Prog.timeBoundT (Prog.clr cT) ℓ ≤ 2 * M + 3 :=
      fun ℓ hℓ => by show 2 * (supB ℓ + 0) + 3 ≤ _; have := XProg.supB_le_of hℓ; omega
    have e3' := e3 (Prog.lenBoundT (Prog.loop cT (.prim (.snoc tOn true))) ℓ3) fun i => by
      have hl := iterSupT_le (g := g) (n := ℓ3 cT) (ℓ := ℓ3) (ℓ' := h (N * K)) fun j hj i =>
        (hg j i).trans (by simp only [h, Function.update_apply]; split_ifs <;> omega)
      exact (hl i).trans (hhM (N * K) le_rfl i)
    omega
  have hpre : XProg.lenBoundT (preP N K ra rb tm) ℓ0 ≤ encB Mo N K B := by
    show ℓ4 ≤ _
    intro i
    refine (hℓ4 i).trans ?_
    simp only [h, Function.update_apply]
    by_cases hc' : i = cT
    · subst hc'; simp [encB, cT]
    by_cases ho : i = tOn
    · subst ho; simp only [if_neg hc', if_pos rfl]; simp [encB, tOn]
    · simp only [hc', ho, if_false]
      have := hl2 i
      simpa [f0, Function.update_apply, hc', ho] using this
  have hTpre : XProg.timeBoundT (preP N K ra rb tm) ℓ0 ≤
      4 * (2 * M + 3) + (203 * ((2 * M + 1) * (4 * M + 12)) + (2 * M + 3)) +
        (2 * (2 * M + 3) + (N * K * (4 * M + 9) + 2)) := by
    change Prog.timeBoundT (inP ra rb) ℓ0 + (XProg.timeBoundT (tmplsP cT (tList N K ra rb tm)) ℓ1 +
      Prog.timeBoundT (onesP ⨾ Prog.clr cT) ℓ2) ≤ _
    have := Nat.mul_le_mul_right ((2 * M + 1) * (4 * M + 12)) (length_tList_le N K ra rb tm)
    omega
  exact ⟨hpre, hTpre⟩

/-- **The code and the exit**: from bounds within `encB Mo N K B`. -/
theorem tail_bounds {N K Mo : ℕ} (hNK : N * K ≤ Mo) (hK : K ≤ Mo) (hN : N ≤ Mo) (ro : Fin 200)
    (c : Code) (B : Fin 200 → ℕ) (hc : Closed Mo N K B c) (M : ℕ) (hMo : Mo ≤ M)
    (hB : ∀ r, B r ≤ M) (ℓ : Fin 247 → ℕ) (hℓ : ℓ ≤ encB Mo N K B) :
    XProg.lenBoundT (.seq (compile c) (.prog (postP ro))) ℓ ≤ io2 (R := 245) (B ro) 0 0 ∧
      XProg.timeBoundT (.seq (compile c) (.prog (postP ro))) ℓ ≤
        vmTime Mo N K B (instrTime Mo N K B) c + 249 * (2 * M + 3) := by
  have hE := encB_le Mo N K B M hMo hK hN hNK hB
  obtain ⟨hTc, hLc⟩ := compile_time Mo N K B hNK hK hN c hc
  have hcode := (XProg.timeBoundT_mono (compile c) hℓ).trans hTc
  have hlen := (XProg.lenBoundT_mono (compile c) hℓ).trans hLc
  set ℓc := XProg.lenBoundT (compile c) ℓ
  obtain ⟨hpl, hpt⟩ := clrL_bounds postTapes (Function.update ℓc 0 (ℓc (tWd ro))) M
    (fun i => by
      simp only [Function.update_apply]
      split_ifs <;> exact (hlen _).trans (hE _))
  have hpost_len : postTapes.length ≤ 247 :=
    (List.length_filter_le _ _).trans (by simp)
  have e : Prog.lenBoundT (postP ro) ℓc =
      Prog.lenBoundT (clrL postTapes) (Function.update ℓc 0 (ℓc (tWd ro))) := by
    rw [postP]; simp only [Prog.lenBoundT, Prim.lenT]
  have et : Prog.timeBoundT (postP ro) ℓc = 2 * (supB ℓc + 0) + 3 +
      Prog.timeBoundT (clrL postTapes) (Function.update ℓc 0 (ℓc (tWd ro))) := by
    rw [postP]; simp only [Prog.timeBoundT, Prog.lenBoundT, Prim.lenT, Prim.pad]
  refine ⟨?_, ?_⟩
  · change Prog.lenBoundT (postP ro) ℓc ≤ _
    rw [e, hpl]
    intro t
    by_cases h0 : t = 0
    · subst h0
      have hm : (0 : Fin 247) ∉ postTapes := by simp [postTapes]
      show (if (0 : Fin 247) ∈ postTapes then 0 else Function.update ℓc 0 (ℓc (tWd ro)) 0) ≤ _
      rw [if_neg hm, Function.update_self]
      have := hlen (tWd ro)
      rw [encB_tWd] at this
      simpa [io2] using this
    · have hm : t ∈ postTapes := by simp [postTapes, h0]
      show (if t ∈ postTapes then 0 else Function.update ℓc 0 (ℓc (tWd ro)) t) ≤ _
      rw [if_pos hm]; exact Nat.zero_le _
  · change XProg.timeBoundT (compile c) ℓ + Prog.timeBoundT (postP ro) ℓc ≤ _
    have hpost : Prog.timeBoundT (postP ro) ℓc ≤ 2 * M + 3 + 248 * (2 * M + 3) := by
      rw [et]
      have hs := XProg.supB_le_of fun i => (hlen i).trans (hE i)
      have := Nat.mul_le_mul_right (2 * M + 3) (Nat.add_le_add_right hpost_len 1)
      omega
    omega

/-- **The clock and the output bound of the handler**: for register bounds `B` closed under the
code (`RingVM.Closed`), at least the input lengths on `ra`, `rb` and the templates elsewhere, and
`M` above every bound. -/
theorem bounds_ringIO {N K Mo : ℕ} (hNK : N * K ≤ Mo) (hK : K ≤ Mo) (hN : N ≤ Mo)
    {ra rb : Fin 200} (hab : ra ≠ rb) (ro : Fin 200) (tm : Fin 200 → ℕ) (c : Code)
    (B : Fin 200 → ℕ) (hc : Closed Mo N K B c) (La Lb M : ℕ) (hLa : La ≤ B ra) (hLb : Lb ≤ B rb)
    (htm : ∀ r, r ≠ ra → r ≠ rb → tm r ≤ B r) (hMo : Mo ≤ M) (hB : ∀ r, B r ≤ M) :
    XProg.lenBoundT (ringIO N K ra rb ro tm c) (io2 (R := 245) La Lb 0) ≤
        io2 (R := 245) (B ro) 0 0 ∧
      XProg.timeBoundT (ringIO N K ra rb ro tm c) (io2 (R := 245) La Lb 0) ≤
        210 * ((2 * M + 1) * (4 * M + 12)) + vmTime Mo N K B (instrTime Mo N K B) c +
          300 * (2 * M + 3) := by
  obtain ⟨hpre, hTpre⟩ := pre_bounds hNK hK hN hab tm B La Lb M hLa hLb htm hMo hB
  obtain ⟨hl, ht⟩ := tail_bounds hNK hK hN ro c B hc M hMo hB _ hpre
  refine ⟨hl, ?_⟩
  change XProg.timeBoundT (preP N K ra rb tm) _ + XProg.timeBoundT (.seq (compile c)
    (.prog (postP ro))) (XProg.lenBoundT (preP N K ra rb tm) _) ≤ _
  have hNKM : N * K * (4 * M + 9) + 2 ≤ (2 * M + 1) * (4 * M + 12) := by
    have : N * K ≤ M := hNK.trans hMo
    nlinarith
  omega

/-! ### The variant with the word of `1`

`RingVM` has no instruction producing a nonzero constant from zero words; `ringIO1` also puts
`true :: replicate (tm r1) false` (the word of `1` when `tm r1 = N K − 1`) into the register
`r1`. -/

/-- **The handler with the word of `1` in `r1`.** -/
noncomputable def ringIO1 (N K : ℕ) (ra rb ro r1 : Fin 200) (tm : Fin 200 → ℕ) (c : Code) :
    XProg 247 :=
  .seq (preP N K ra rb tm) (.seq (.prog (.prim (.cons (tWd r1) true)))
    (.seq (compile c) (.prog (postP ro))))

/-- The registers at the start of the code of `ringIO1`. -/
def initW1 (ra rb r1 : Fin 200) (tm : Fin 200 → ℕ) (a b : List Bool) : St :=
  Function.update (initW ra rb tm a b) r1 (true :: List.replicate (tm r1) false)

theorem enc_update_tWd (N K : ℕ) (w : St) (r : Fin 200) (v : List Bool) :
    Function.update (enc N K w) (tWd r) v = enc N K (Function.update w r v) := by
  funext t
  by_cases ht : t = tWd r
  · subst ht; rw [Function.update_self, enc_tWd, Function.update_self]
  rw [Function.update_of_ne ht]
  by_cases hge : 47 ≤ t.val
  · obtain ⟨x, rfl⟩ : ∃ x : Fin 200, t = tWd x :=
      ⟨⟨t.val - 47, by have := t.isLt; omega⟩, Fin.ext (by simp [tWd]; omega)⟩
    have hx : x ≠ r := fun h => ht (by rw [h])
    rw [enc_tWd, enc_tWd, Function.update_of_ne hx]
  · simp only [enc, encO, hge, ↓reduceDIte]

theorem law_ringIO1 {N K : ℕ} (hN : 0 < N) (hK : 0 < K) {ra rb : Fin 200} (hab : ra ≠ rb)
    (ro r1 : Fin 200) (h1a : r1 ≠ ra) (h1b : r1 ≠ rb) (tm : Fin 200 → ℕ) (c : Code)
    (a b : List Bool) :
    (ringIO1 N K ra rb ro r1 tm c).law (io2 (R := 245) a b []) =
      PMF.pure (io2 (R := 245) (exec N K c (initW1 ra rb r1 tm a b) ro) [] []) := by
  rw [ringIO1, XProg.law_seq, law_preP N K hab, PMF.pure_bind, XProg.law_seq, XProg.law_prim,
    PMF.pure_bind]
  have h : Prim.apply (.cons (tWd r1) true) (enc N K (initW ra rb tm a b)) =
      enc N K (initW1 ra rb r1 tm a b) := by
    show Function.update (enc N K (initW ra rb tm a b)) (tWd r1)
      (true :: enc N K (initW ra rb tm a b) (tWd r1)) = _
    rw [enc_tWd, enc_update_tWd]
    simp [initW1, initW, h1a, h1b]
  rw [h, XProg.law_seq, law_compile hN hK, PMF.pure_bind, XProg.law_prog,
    Prog.law_eq_run_of_coinFree _ (coinFree_postP ro), run_postP, enc_tWd]

theorem wf_ringIO1 (N K : ℕ) (ra rb ro r1 : Fin 200) (tm : Fin 200 → ℕ) (c : Code)
    (hc : loopOkB c = true) : (ringIO1 N K ra rb ro r1 tm c).WF :=
  ⟨wf_preP N K ra rb tm, trivial, wf_compile c hc, trivial, wf_clrL _⟩

theorem bounds_ringIO1 {N K Mo : ℕ} (hNK : N * K ≤ Mo) (hK : K ≤ Mo) (hN : N ≤ Mo)
    {ra rb : Fin 200} (hab : ra ≠ rb) (ro r1 : Fin 200) (h1a : r1 ≠ ra) (h1b : r1 ≠ rb)
    (tm : Fin 200 → ℕ) (c : Code)
    (B : Fin 200 → ℕ) (hc : Closed Mo N K B c) (La Lb M : ℕ) (hLa : La ≤ B ra) (hLb : Lb ≤ B rb)
    (htm : ∀ r, r ≠ ra → r ≠ rb → r ≠ r1 → tm r ≤ B r) (h1 : tm r1 + 1 ≤ B r1) (hMo : Mo ≤ M)
    (hB : ∀ r, B r ≤ M) :
    XProg.lenBoundT (ringIO1 N K ra rb ro r1 tm c) (io2 (R := 245) La Lb 0) ≤
        io2 (R := 245) (B ro) 0 0 ∧
      XProg.timeBoundT (ringIO1 N K ra rb ro r1 tm c) (io2 (R := 245) La Lb 0) ≤
        210 * ((2 * M + 1) * (4 * M + 12)) + vmTime Mo N K B (instrTime Mo N K B) c +
          300 * (2 * M + 3) := by
  set B0 := Function.update B r1 (tm r1)
  have hB0 : ∀ r, B0 r ≤ M := fun r => by
    simp only [B0, Function.update_apply]; split_ifs
    · subst r; exact (by omega : tm r1 ≤ B r1).trans (hB r1)
    · exact hB r
  obtain ⟨hpre, hTpre⟩ := pre_bounds hNK hK hN hab tm B0 La Lb M
    (by simp [B0, Function.update_of_ne h1a.symm, hLa])
    (by simp [B0, Function.update_of_ne h1b.symm, hLb])
    (fun r ha hb => by
      simp only [B0, Function.update_apply]; split_ifs
      · subst r; exact le_rfl
      · exact htm r ha hb (by assumption))
    hMo hB0
  set ℓ1 := XProg.lenBoundT (preP N K ra rb tm) (io2 (R := 245) La Lb 0)
  have hcons : Prim.lenT (.cons (tWd r1) true) ℓ1 ≤ encB Mo N K B := by
    intro t
    simp only [Prim.lenT, Function.update_apply]
    split_ifs with ht
    · subst ht
      have := hpre (tWd r1)
      rw [encB_tWd] at this ⊢
      simp only [B0, Function.update_self] at this
      omega
    · refine (hpre t).trans ?_
      by_cases hge : 47 ≤ t.val
      · obtain ⟨x, rfl⟩ : ∃ x : Fin 200, t = tWd x :=
          ⟨⟨t.val - 47, by have := t.isLt; omega⟩, Fin.ext (by simp [tWd]; omega)⟩
        have hx : x ≠ r1 := fun h => ht (by rw [h])
        rw [encB_tWd, encB_tWd]; simp [B0, Function.update_of_ne hx]
      · simp only [encB, hge, ↓reduceDIte]; exact le_rfl
  obtain ⟨hl, ht⟩ := tail_bounds hNK hK hN ro c B hc M hMo hB _ hcons
  refine ⟨hl, ?_⟩
  change XProg.timeBoundT (preP N K ra rb tm) _ + (2 * (supB ℓ1 + 1) + 3 +
    XProg.timeBoundT (.seq (compile c) (.prog (postP ro))) (Prim.lenT (.cons (tWd r1) true) ℓ1))
      ≤ _
  have hs : supB ℓ1 ≤ M := XProg.supB_le_of fun i =>
    (hpre i).trans (encB_le Mo N K B0 M hMo hK hN hNK hB0 i)
  have hNKM : N * K * (4 * M + 9) + 2 ≤ (2 * M + 1) * (4 * M + 12) := by
    have : N * K ≤ M := hNK.trans hMo
    nlinarith
  omega

end SigabaNeo.Tape.RingVM.Handler