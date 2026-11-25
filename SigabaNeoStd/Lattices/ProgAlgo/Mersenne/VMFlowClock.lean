import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMCost

/-!
# A flow-sensitive clock of compiled ring-word codes (package F4)

`RingVM.compile_time` bounds the clock of a compiled code from **one** per-register bound `B`
closed under the whole code. The `Dec` code reuses registers with very different lengths (a
register holds a long stream in one block and a short loop counter in the next), so one static
bound charges the long length to the loop counters. Here the bounds follow the code:

* the abstract state is a list of `200` register bounds (`toB`);
* **`absRun P c B`**: the bound after the code and its clock, or `none` when a side condition
  fails. A copy `cp d s` sets the bound of `d` to that of `s` (`lenB_cp`, a strong update); a ring
  operation raises the bound of its destination to `N K`; a loop `rep t body` searches an
  invariant (at most `fuel` rounds of the body) and is charged `X t` rounds of
  `2 S + 3 + (body) + 1` (`S` above every tape of `encB Mo N K X`);
* **`absRun_sound`**: from any per-tape bounds below `encB Mo N K (toB B)`, the compiled code ends
  below `encB Mo N K (toB B')` within the computed clock.

`absRun` is computable, so the clock of a concrete code is checked by kernel evaluation.
-/

namespace SigabaNeo.Tape.RingVM.Flow
set_option autoImplicit false

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Tape.Sym SigabaNeo.Tape.Prog.MersenneT
  SigabaNeo.Tape.Prog.SpecT

/-! ### The abstract state: 200 bounds packed in one natural number

Register `i` occupies the bits `256 i … 256 i + 255` (kernel arithmetic on big numbers is fast,
list access is not). -/

/-- The width of a field. -/
def Wd : ℕ := 2 ^ 256

theorem Wd_pos : 0 < Wd := by unfold Wd; positivity

/-- Field `i`. -/
def pg (V i : ℕ) : ℕ := V / 2 ^ (256 * i) % Wd

/-- Set field `i` to `v` (`v < Wd`). -/
def ps (V i v : ℕ) : ℕ := V % 2 ^ (256 * i) + 2 ^ (256 * i) * (v + Wd * (V / (2 ^ (256 * i) * Wd)))

theorem pg_lt (V i : ℕ) : pg V i < Wd := Nat.mod_lt _ Wd_pos

theorem pg_ps_self (V i v : ℕ) (hv : v < Wd) : pg (ps V i v) i = v := by
  have ha : 0 < 2 ^ (256 * i) := by positivity
  rw [pg, ps, Nat.add_mul_div_left _ _ ha, Nat.div_eq_of_lt (Nat.mod_lt _ ha), zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]

theorem pg_ps_lt (V i j v : ℕ) (h : j < i) : pg (ps V i v) j = pg V j := by
  obtain ⟨c, rfl⟩ : ∃ c, i = j + 1 + c := ⟨i - j - 1, by omega⟩
  have hb : 0 < 2 ^ (256 * j) := by positivity
  have ha : 2 ^ (256 * (j + 1 + c)) = 2 ^ (256 * j) * (Wd * 2 ^ (256 * c)) := by
    rw [show 256 * (j + 1 + c) = 256 * j + 256 + 256 * c by ring, pow_add, pow_add, Wd]; ring
  have key : ∀ x R : ℕ, (x % 2 ^ (256 * (j + 1 + c)) + 2 ^ (256 * (j + 1 + c)) * R) / 2 ^ (256 * j) % Wd =
      x % 2 ^ (256 * (j + 1 + c)) / 2 ^ (256 * j) % Wd := by
    intro x R
    rw [ha, mul_assoc, Nat.add_mul_div_left _ _ hb, mul_assoc, Nat.add_mul_mod_self_left]
  have hV : V = V % 2 ^ (256 * (j + 1 + c)) + 2 ^ (256 * (j + 1 + c)) * (V / 2 ^ (256 * (j + 1 + c))) :=
    (Nat.mod_add_div _ _).symm
  rw [pg, pg, ps, key]
  conv_rhs => rw [hV]
  rw [key]

theorem pg_ps_gt (V i j v : ℕ) (hv : v < Wd) (h : i < j) : pg (ps V i v) j = pg V j := by
  obtain ⟨c, rfl⟩ : ∃ c, j = i + 1 + c := ⟨j - i - 1, by omega⟩
  have haW : 0 < 2 ^ (256 * i) * Wd := Nat.mul_pos (by positivity) Wd_pos
  have hb : 2 ^ (256 * (i + 1 + c)) = 2 ^ (256 * i) * Wd * 2 ^ (256 * c) := by
    rw [show 256 * (i + 1 + c) = 256 * i + 256 + 256 * c by ring, pow_add, pow_add, Wd]
  set a := 2 ^ (256 * i)
  have hx : V % a + a * v < a * Wd := by
    have h1 : V % a < a := Nat.mod_lt _ (by positivity)
    have h2 : a * v ≤ a * (Wd - 1) := Nat.mul_le_mul_left _ (by have := Wd_pos; omega)
    have h3 : a * (Wd - 1) + a = a * Wd := by
      rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ Wd_pos)]
    omega
  have e1 : ps V i v = (V % a + a * v) + a * Wd * (V / (a * Wd)) := by rw [ps]; ring
  rw [pg, pg, e1, hb, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ haW,
    Nat.div_eq_of_lt hx, zero_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    ← Nat.div_div_eq_div_mul]

theorem pg_ps_ne (V i j v : ℕ) (hv : v < Wd) (h : j ≠ i) : pg (ps V i v) j = pg V j := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact pg_ps_lt V i j v h
  · exact pg_ps_gt V i j v hv h

/-- The bound of the register `x`. -/
def toB (B : ℕ) : Fin 200 → ℕ := fun x => pg B x.val

/-- Set the bound of `x` (cut to the field width). -/
def bset (B : ℕ) (x : Fin 200) (v : ℕ) : ℕ := ps B x.val (min v (Wd - 1))

/-- Pointwise maximum. -/
def bmax (A B : ℕ) : ℕ := (List.range 200).foldr (fun i C => ps C i (max (pg A i) (pg B i))) 0

/-- Pointwise order. -/
def ble (A B : ℕ) : Bool := (List.range 200).all fun i => pg A i ≤ pg B i

/-- The largest bound. -/
def lmax (B : ℕ) : ℕ := (List.range 200).foldr (fun i m => max (pg B i) m) 0

theorem toB_bset (B : ℕ) (x : Fin 200) (v : ℕ) (hv : v < Wd) :
    toB (bset B x v) = Function.update (toB B) x v := by
  have hm : min v (Wd - 1) = v := min_eq_left (by omega)
  funext y
  by_cases h : y = x
  · subst h; rw [toB, bset, hm, pg_ps_self _ _ _ hv, Function.update_self]
  · rw [toB, bset, hm, pg_ps_ne _ _ _ _ hv (fun e => h (Fin.ext e)), Function.update_of_ne h]; rfl

theorem pg_foldr_ps (f : ℕ → ℕ) (hf : ∀ i, f i < Wd) (l : List ℕ) :
    ∀ (j : ℕ), j ∈ l → pg (l.foldr (fun i C => ps C i (f i)) 0) j = f j := by
  induction l with
  | nil => intro j h; simp at h
  | cons i l ih =>
    intro j h
    rw [List.foldr_cons]
    by_cases hij : j = i
    · subst hij; exact pg_ps_self _ _ _ (hf _)
    · rw [pg_ps_ne _ _ _ _ (hf _) hij]
      exact ih j (by simpa [hij] using h)

theorem toB_bmax (A B : ℕ) (x : Fin 200) : toB (bmax A B) x = max (toB A x) (toB B x) :=
  pg_foldr_ps (fun i => max (pg A i) (pg B i)) (fun i => max_lt (pg_lt _ _) (pg_lt _ _))
    _ _ (List.mem_range.mpr x.isLt)

theorem toB_le_of_ble {A B : ℕ} (h : ble A B = true) : toB A ≤ toB B := by
  intro x
  have := List.all_eq_true.mp h x.val (List.mem_range.mpr x.isLt)
  simpa [toB] using this

theorem le_foldr_max (f : ℕ → ℕ) : ∀ (l : List ℕ) (i : ℕ), i ∈ l → f i ≤ l.foldr (fun i m => max (f i) m) 0
  | [], i, h => by simp at h
  | j :: l, i, h => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (le_foldr_max f l i h).trans (le_max_right _ _)

theorem toB_le_lmax (B : ℕ) (x : Fin 200) : toB B x ≤ lmax B :=
  le_foldr_max (fun i => pg B i) _ _ (List.mem_range.mpr x.isLt)

theorem toB_lt (B : ℕ) (x : Fin 200) : toB B x < Wd := pg_lt _ _

/-! ### Parameters -/

/-- The parameters of the clock: the operation area `Mo`, `N`, `K`, a bound `Mt` of the template
lengths, the sweep counts of the operations. -/
structure VCP where
  Mo : ℕ
  N : ℕ
  K : ℕ
  Mt : ℕ
  cAdd : ℕ
  cMul : ℕ
  cCanon : ℕ
  cNeg : ℕ
  cDig : ℕ
  cRot : ℕ
  cAut : ℕ
  cRho : ℕ

/-- The parameters are valid: `N K, K, N, Mt ≤ Mo`, the sweep counts above the certified ones. -/
structure VCP.Valid (P : VCP) : Prop where
  hNK : P.N * P.K ≤ P.Mo
  hK : P.K ≤ P.Mo
  hN : P.N ≤ P.Mo
  hMt : P.Mt ≤ P.Mo
  hW : P.N * P.K < Wd
  add : 40 * (P.N * P.K) + 44 * P.N + 7 ≤ P.cAdd
  mul : pEval (ρLd P.Mo P.N P.K 0) wMulRM ≤ P.cMul
  canon : pEval (ρLd P.Mo P.N P.K 0) wCanon ≤ P.cCanon
  neg : pEval (ρLd P.Mo P.N P.K 0) wNotM ≤ P.cNeg
  dig : ∀ m ≤ P.Mt, pEval (ρLd P.Mo P.N P.K m) wDigitM ≤ P.cDig
  rot : ∀ m ≤ P.Mt, pEval (ρLd P.Mo P.N P.K m) wRotB ≤ P.cRot
  aut : ∀ m ≤ P.Mt, pEval (ρLd P.Mo P.N P.K m) wAut ≤ P.cAut
  rho : ∀ m ≤ P.Mt, pEval (ρLd P.Mo P.N P.K m) wRhoJ ≤ P.cRho

/-! ### The abstract run -/

/-- Search an invariant of a loop body (`f` its abstract run): at most `fuel` rounds. -/
def loopFix (f : ℕ → Option (ℕ × ℕ)) : ℕ → ℕ → Option (ℕ × ℕ)
  | 0, _ => none
  | n + 1, X =>
    match f X with
    | none => none
    | some (X', T) => if ble X' X then some (X, T) else loopFix f n (bmax X X')

variable (P : VCP)

/-- The bound after a ring result on `d`. -/
def rset (B : ℕ) (d : Fin 200) : ℕ := bset B d (max (toB B d) (P.N * P.K))

/-- **The abstract run** (bound after the code, its clock). -/
def absRun (fuel : ℕ) : Code → ℕ → Option (ℕ × ℕ)
  | .add d a b, B | .sub d a b, B =>
    let B' := rset P B d
    some (B', binTime P.Mo P.N P.K (toB B') P.cAdd d a b)
  | .mul d a b, B =>
    let B' := rset P B d
    some (B', binTime P.Mo P.N P.K (toB B') P.cMul d a b)
  | .canon d a, B =>
    let B' := rset P B d
    some (B', unTime P.Mo P.N P.K (toB B') P.cCanon d a)
  | .neg d a, B =>
    let B' := rset P B d
    some (B', unTime P.Mo P.N P.K (toB B') P.cNeg d a)
  | .digit d a t, B =>
    let B' := rset P B d
    if toB B' t ≤ P.Mt then some (B', tmTime P.Mo P.N P.K (toB B') P.cDig d a t) else none
  | .rotB d a t, B =>
    let B' := rset P B d
    if toB B' t ≤ P.Mt then some (B', tmTime P.Mo P.N P.K (toB B') P.cRot d a t) else none
  | .aut d a t, B =>
    let B' := rset P B d
    if toB B' t ≤ P.Mt then some (B', tmTime P.Mo P.N P.K (toB B') P.cAut d a t) else none
  | .rhoJ d a t, B =>
    let B' := rset P B d
    if toB B' t ≤ P.Mt then some (B', tmTime P.Mo P.N P.K (toB B') P.cRho d a t) else none
  | .mv d s c, B =>
    some (B, (2 * max (toB B s) (max (toB B d) (toB B c)) + 3) * (20 + 10 * toB B c) + 3)
  | .cp d s, B => some (bset B d (toB B s), 2 * max (toB B d) (toB B s) + 3)
  | .drop t c, B => some (B, (2 * max (toB B t) (toB B c) + 3) * (20 + 10 * toB B c) + 3)
  | .clr t, B | .tl t, B => some (B, 2 * toB B t + 3)
  | .nop, B => some (B, 3)
  | .seq p q, B =>
    match absRun fuel p B with
    | none => none
    | some (B1, T1) =>
      match absRun fuel q B1 with
      | none => none
      | some (B2, T2) => some (B2, T1 + T2)
  | .ifb _ p q, B =>
    match absRun fuel p B, absRun fuel q B with
    | some (B1, T1), some (B2, T2) => some (bmax B1 B2, max T1 T2 + 1)
    | _, _ => none
  | .rep t b, B =>
    match loopFix (absRun fuel b) fuel B with
    | none => none
    | some (X, Tb) => some (X, toB X t * (2 * max P.Mo (lmax X) + 3 + Tb + 1) + 2)

/-! ### Monotonicity of the sweep polynomials -/

theorem mEval_mono : ∀ {ρ ρ' : List ℕ}, List.Forall₂ (· ≤ ·) ρ ρ' → ∀ e : Mono, mEval ρ e ≤ mEval ρ' e
  | _, _, _, [] => by simp [mEval_nil]
  | [], [], _, a :: es => by
    simp only [mEval]
    exact Nat.mul_le_mul le_rfl (mEval_mono List.Forall₂.nil es)
  | x :: ρ, y :: ρ', List.Forall₂.cons hxy h, a :: es => by
    simp only [mEval, List.headD_cons, List.tail_cons]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left hxy a) (mEval_mono h es)

theorem pEval_mono {ρ ρ' : List ℕ} (h : List.Forall₂ (· ≤ ·) ρ ρ') : ∀ p : Poly, pEval ρ p ≤ pEval ρ' p
  | [] => le_rfl
  | (m, c) :: p => Nat.add_le_add (Nat.mul_le_mul_left _ (mEval_mono h m)) (pEval_mono h p)

theorem pEval_ρLd_mono (Mo N K : ℕ) {m m' : ℕ} (h : m ≤ m') (p : Poly) :
    pEval (ρLd Mo N K m) p ≤ pEval (ρLd Mo N K m') p :=
  pEval_mono (by simp [ρLd, h]) p

/-! ### Soundness -/

section Sound

variable {P}

theorem encB_mono (Mo N K : ℕ) {B B' : Fin 200 → ℕ} (h : B ≤ B') : encB Mo N K B ≤ encB Mo N K B' := by
  intro t
  unfold encB
  split_ifs <;> first | exact le_rfl | exact h _

/-- The clock statement of a code between two bound vectors. -/
def CodeOK (Mo N K : ℕ) (c : Code) (B B' : Fin 200 → ℕ) (T : ℕ) : Prop :=
  ∀ ℓ, ℓ ≤ encB Mo N K B → XProg.timeBoundT (compile c) ℓ ≤ T ∧
    XProg.lenBoundT (compile c) ℓ ≤ encB Mo N K B'

theorem codeOK_of_instr {Mo N K : ℕ} {c : Code} {B B' : Fin 200 → ℕ} {T T' : ℕ} (hB : B ≤ B')
    (h : InstrOK Mo N K B' c T) (hT : T ≤ T') : CodeOK Mo N K c B B' T' := fun ℓ hℓ =>
  have h' := hℓ.trans (encB_mono Mo N K hB)
  ⟨((XProg.timeBoundT_mono _) h').trans (h.time.trans hT), ((XProg.lenBoundT_mono _) h').trans h.len⟩

theorem binTime_mono (Mo N K : ℕ) (B : Fin 200 → ℕ) {W W' : ℕ} (h : W ≤ W') (d a b : Fin 200) :
    binTime Mo N K B W d a b ≤ binTime Mo N K B W' d a b := by
  unfold binTime; gcongr

theorem tmTime_mono (Mo N K : ℕ) (B : Fin 200 → ℕ) {W W' : ℕ} (h : W ≤ W') (d a t : Fin 200) :
    tmTime Mo N K B W d a t ≤ tmTime Mo N K B W' d a t := by
  unfold tmTime; gcongr

theorem unTime_mono (Mo N K : ℕ) (B : Fin 200 → ℕ) {W W' : ℕ} (h : W ≤ W') (d a : Fin 200) :
    unTime Mo N K B W d a ≤ unTime Mo N K B W' d a := by
  unfold unTime; gcongr

/-- **A copy sets the bound of its destination.** -/
theorem codeOK_cp (Mo N K : ℕ) (B : Fin 200 → ℕ) (d s : Fin 200) :
    CodeOK Mo N K (.cp d s) B (Function.update B d (B s)) (2 * max (B d) (B s) + 3) := by
  intro ℓ hℓ
  by_cases hds : d = s
  · subst hds
    have := instrOK_nop Mo N K B
    have hc : compile (.cp d d) = nopX := dif_pos rfl
    rw [hc, Function.update_eq_self]
    exact ⟨((XProg.timeBoundT_mono _) hℓ).trans (this.time.trans (by omega)),
      ((XProg.lenBoundT_mono _) hℓ).trans this.len⟩
  · have hc : compile (.cp d s) = .frame (mkE (fCp d s) (fCp_inj hds)) (.prog (Prog.cp 0 1)) :=
      dif_neg hds
    have e0 : fCp d s 0 = tWd d := rfl
    have e1 : fCp d s 1 = tWd s := rfl
    rw [hc]
    refine ⟨?_, frame_len_le _ _ (fun j => ?_) (fun t ht => ?_)⟩
    · show Prog.timeBoundT (Prog.cp 0 1) (fun j => ℓ (fCp d s j)) ≤ _
      simp only [Prog.timeBoundT, Prim.pad]
      have := supB_le_of (fun j : Fin 2 => ℓ (fCp d s j)) (M := max (B d) (B s))
        (fun j => by
          fin_cases j
          · exact (hℓ (tWd d)).trans (by rw [encB_tWd]; exact le_max_left _ _)
          · exact (hℓ (tWd s)).trans (by rw [encB_tWd]; exact le_max_right _ _))
      omega
    · have hs := hℓ (tWd s)
      rw [encB_tWd] at hs
      fin_cases j
      · simp [XProg.lenBoundT, Prog.lenBoundT, Prim.lenT, mkE, e0, e1, encB_tWd]
        exact hs
      · simp [XProg.lenBoundT, Prog.lenBoundT, Prim.lenT, mkE, e0, e1, encB_tWd,
          Function.update_of_ne (Ne.symm hds)]
        exact hs
    · have htd : t ≠ tWd d := fun e => ht 0 (by rw [e]; rfl)
      refine (hℓ t).trans (le_of_eq ?_)
      unfold encB
      split_ifs with h1 h2 h3 h4 h5 <;> try rfl
      have hx : (⟨t.val - 47, by have := t.isLt; omega⟩ : Fin 200) ≠ d := fun e => htd (by
        rw [← e]; exact Fin.ext (by simp [tWd]; omega))
      rw [Function.update_of_ne hx]

theorem supB_encB_le (Mo N K : ℕ) (B : Fin 200 → ℕ) (M : ℕ) (hNK : N * K ≤ Mo) (hK : K ≤ Mo)
    (hN : N ≤ Mo) (hB : ∀ x, B x ≤ M) : supB (encB Mo N K B) ≤ max Mo M :=
  supB_le_of _ fun t => by
    unfold encB
    split_ifs <;> first | omega | exact (hB _).trans (le_max_right _ _)

variable (hP : P.Valid)
include hP in
theorem toB_rset (B : ℕ) (d : Fin 200) :
    toB (rset P B d) = Function.update (toB B) d (max (toB B d) (P.N * P.K)) :=
  toB_bset _ _ _ (max_lt (toB_lt _ _) hP.hW)

include hP in
theorem le_rset (B : ℕ) (d : Fin 200) : toB B ≤ toB (rset P B d) := by
  rw [toB_rset hP B]
  intro x
  by_cases h : x = d
  · subst h; simp
  · rw [Function.update_of_ne h]

include hP in
theorem nk_le_rset (B : ℕ) (d : Fin 200) : P.N * P.K ≤ toB (rset P B d) d := by
  rw [toB_rset hP B]; simp

omit hP

theorem loopFix_spec (f : ℕ → Option (ℕ × ℕ)) :
    ∀ (n : ℕ) (X X' : ℕ) (T : ℕ), loopFix f n X = some (X', T) →
      toB X ≤ toB X' ∧ ∃ Y, f X' = some (Y, T) ∧ ble Y X' = true
  | 0, _, _, _, h => by simp [loopFix] at h
  | n + 1, X, X', T, h => by
    simp only [loopFix] at h
    split at h
    · simp at h
    · rename_i Y T' hf
      split_ifs at h with hle
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨le_rfl, Y, hf, hle⟩
      · obtain ⟨h2, h3⟩ := loopFix_spec f n _ _ _ h
        refine ⟨fun x => ?_, h3⟩
        exact (le_max_left _ _).trans ((toB_bmax X Y x).symm.le.trans (h2 x))

/-- **Soundness of the abstract run.** -/
theorem absRun_sound (hP : P.Valid) (fuel : ℕ) : ∀ (c : Code) (B B' : ℕ) (T : ℕ),
    absRun P fuel c B = some (B', T) → CodeOK P.Mo P.N P.K c (toB B) (toB B') T
  | .add d a b, B, B', T, h => by
    simp only [absRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact codeOK_of_instr (le_rset hP B d)
      (instrOK_add P.Mo P.N P.K _ hP.hNK hP.hK hP.hN d a b (nk_le_rset hP B d))
      (binTime_mono _ _ _ _ hP.add d a b)
  | .sub d a b, B, B', T, h => by
    simp only [absRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact codeOK_of_instr (le_rset hP B d)
      (instrOK_sub P.Mo P.N P.K _ hP.hNK hP.hK hP.hN d a b (nk_le_rset hP B d))
      (binTime_mono _ _ _ _ hP.add d a b)
  | .mul d a b, B, B', T, h => by
    simp only [absRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact codeOK_of_instr (le_rset hP B d)
      (instrOK_mul P.Mo P.N P.K _ hP.hNK hP.hK hP.hN d a b (nk_le_rset hP B d))
      (binTime_mono _ _ _ _ hP.mul d a b)
  | .canon d a, B, B', T, h => by
    simp only [absRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact codeOK_of_instr (le_rset hP B d)
      (instrOK_canon P.Mo P.N P.K _ hP.hNK hP.hK hP.hN d a (nk_le_rset hP B d))
      (unTime_mono _ _ _ _ hP.canon d a)
  | .neg d a, B, B', T, h => by
    simp only [absRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact codeOK_of_instr (le_rset hP B d)
      (instrOK_neg P.Mo P.N P.K _ hP.hNK hP.hK hP.hN d a (nk_le_rset hP B d))
      (unTime_mono _ _ _ _ hP.neg d a)
  | .digit d a t, B, B', T, h => by
    simp only [absRun] at h
    split_ifs at h with ht
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact codeOK_of_instr (le_rset hP B d)
      (instrOK_digit P.Mo P.N P.K _ hP.hNK hP.hK hP.hN d a t (nk_le_rset hP B d)
        (ht.trans hP.hMt)) (tmTime_mono _ _ _ _ (hP.dig _ ht) d a t)
  | .rotB d a t, B, B', T, h => by
    simp only [absRun] at h
    split_ifs at h with ht
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact codeOK_of_instr (le_rset hP B d)
      (instrOK_rotB P.Mo P.N P.K _ hP.hNK hP.hK hP.hN d a t (nk_le_rset hP B d)
        (ht.trans hP.hMt)) (tmTime_mono _ _ _ _ (hP.rot _ ht) d a t)
  | .aut d a t, B, B', T, h => by
    simp only [absRun] at h
    split_ifs at h with ht
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact codeOK_of_instr (le_rset hP B d)
      (instrOK_aut P.Mo P.N P.K _ hP.hNK hP.hK hP.hN d a t (nk_le_rset hP B d)
        (ht.trans hP.hMt)) (tmTime_mono _ _ _ _ (hP.aut _ ht) d a t)
  | .rhoJ d a t, B, B', T, h => by
    simp only [absRun] at h
    split_ifs at h with ht
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact codeOK_of_instr (le_rset hP B d)
      (instrOK_rhoJ P.Mo P.N P.K _ hP.hNK hP.hK hP.hN d a t (nk_le_rset hP B d)
        (ht.trans hP.hMt)) (tmTime_mono _ _ _ _ (hP.rho _ ht) d a t)
  | .mv d s c, B, B', T, h => by
    simp only [absRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (codeOK_of_instr le_rfl (instrOK_mv P.Mo P.N P.K _ d s c) le_rfl)
  | .cp d s, B, B', T, h => by
    simp only [absRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [toB_bset _ _ _ (toB_lt _ _)]
    exact codeOK_cp _ _ _ _ d s
  | .drop t c, B, B', T, h => by
    simp only [absRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (codeOK_of_instr le_rfl (instrOK_drop P.Mo P.N P.K _ t c) le_rfl)
  | .clr t, B, B', T, h => by
    simp only [absRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (codeOK_of_instr le_rfl (instrOK_clr P.Mo P.N P.K _ t) le_rfl)
  | .tl t, B, B', T, h => by
    simp only [absRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (codeOK_of_instr le_rfl (instrOK_tl P.Mo P.N P.K _ t) le_rfl)
  | .nop, B, B', T, h => by
    simp only [absRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (codeOK_of_instr le_rfl (instrOK_nop P.Mo P.N P.K _) le_rfl)
  | .seq p q, B, B', T, h => by
    simp only [absRun] at h
    rcases hp : absRun P fuel p B with _ | ⟨B1, T1⟩
    · simp [hp] at h
    rcases hq : absRun P fuel q B1 with _ | ⟨B2, T2⟩
    · simp [hp, hq] at h
    simp only [hp, hq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ok1 := absRun_sound hP fuel p B B1 T1 hp
    have ok2 := absRun_sound hP fuel q B1 B2 T2 hq
    intro ℓ hℓ
    obtain ⟨t1, n1⟩ := ok1 ℓ hℓ
    obtain ⟨t2, n2⟩ := ok2 _ n1
    exact ⟨by
      show XProg.timeBoundT (compile p) ℓ +
        XProg.timeBoundT (compile q) (XProg.lenBoundT (compile p) ℓ) ≤ T1 + T2
      omega, n2⟩
  | .ifb x p q, B, B', T, h => by
    simp only [absRun] at h
    rcases hp : absRun P fuel p B with _ | ⟨B1, T1⟩ <;>
      rcases hq : absRun P fuel q B with _ | ⟨B2, T2⟩ <;> simp [hp, hq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ok1 := absRun_sound hP fuel p B B1 T1 hp
    have ok2 := absRun_sound hP fuel q B B2 T2 hq
    refine fun ℓ hℓ => ⟨?_, fun u => ?_⟩
    · show max (XProg.timeBoundT (compile p) ℓ) (XProg.timeBoundT (compile q) ℓ) + 1 ≤ _
      have := (ok1 ℓ hℓ).1; have := (ok2 ℓ hℓ).1; omega
    · show max (XProg.lenBoundT (compile p) ℓ u) (XProg.lenBoundT (compile q) ℓ u) ≤ _
      refine max_le (((ok1 ℓ hℓ).2 u).trans ?_) (((ok2 ℓ hℓ).2 u).trans ?_)
      · exact encB_mono _ _ _ (fun y => by rw [toB_bmax]; exact le_max_left _ _) u
      · exact encB_mono _ _ _ (fun y => by rw [toB_bmax]; exact le_max_right _ _) u
  | .rep t b, B, B', T, h => by
    simp only [absRun] at h
    rcases hl : loopFix (absRun P fuel b) fuel B with _ | ⟨X, Tb⟩
    · simp [hl] at h
    simp only [hl, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hBX, Y, hY, hYX⟩ := loopFix_spec _ fuel B X Tb hl
    have okb := absRun_sound hP fuel b X Y Tb hY
    have hinv : XProg.loopStepT (tWd t) (compile b) (encB P.Mo P.N P.K (toB X)) ≤
        encB P.Mo P.N P.K (toB X) :=
      ((okb _ (tailB_le _ _)).2).trans (encB_mono _ _ _ (toB_le_of_ble hYX))
    intro ℓ hℓ
    have hℓX := hℓ.trans (encB_mono _ _ _ hBX)
    show XProg.timeBoundT (.loop (tWd t) (compile b)) ℓ ≤ _ ∧
      XProg.lenBoundT (.loop (tWd t) (compile b)) ℓ ≤ _
    refine ⟨?_, XProg.lenBoundT_loop_le_of_inv _ _ hℓX hinv⟩
    refine (XProg.timeBoundT_loop_le_of_inv _ _ hℓX hinv).trans ?_
    have h1 : ℓ (tWd t) ≤ toB X t := (hℓX (tWd t)).trans (by rw [encB_tWd])
    have hs := supB_encB_le P.Mo P.N P.K (toB X) (lmax X) hP.hNK hP.hK hP.hN (toB_le_lmax X)
    have hr : Prog.roundTimeT (XProg.timeBoundT (compile b)) (tWd t)
        (encB P.Mo P.N P.K (toB X)) ≤ 2 * max P.Mo (lmax X) + 3 + Tb := by
      show 2 * supB _ + 3 + XProg.timeBoundT (compile b) (tailB _ _) ≤ _
      have := (okb _ (tailB_le (tWd t) _)).1
      omega
    exact Nat.add_le_add_right (Nat.mul_le_mul h1 (Nat.add_le_add_right hr 1)) 2

end Sound

end SigabaNeo.Tape.RingVM.Flow