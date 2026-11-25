import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.Canon
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.Aut
import SigabaNeoStd.Lattices.ProgAlgo.Digits
import SigabaNeoStd.Machines.Prog.ValVM
import SigabaNeoStd.Machines.Prog.AppendW
import SigabaNeoStd.Machines.Prog.CoinFreeX

/-!
# A register machine on ring words modulo `2^K − 1`

`MVM.Code` is a small structured language over `nR = 64` word registers, with the ring operations
of `ℤ_{2^K − 1}[X]/(X^N + 1)` on words of `N` blocks of `K` bits (`SigabaNeo.Lattices.Algo.decRM`):

* `op o d a b` (`o : Op`): `d := canonW (opW o (takeD NK a) y)`, where the second argument `y`
  is the register `b` cut to `N K` bits for the **binary** operations (`add`, `sub`, `mul`) and the
  register `b` itself for the **counted** ones, whose count is `|b|` (`neg` ignores it; `aut`:
  `σ_{|b|}`, `rho`: `X^{−|b|}`, `rot`: `2^{−|b|}` on every coefficient, `dig`: the binary digit `|b|`
  of every coefficient). Every result is **canonicalized** (`canonW`), so on canonical words the
  operations are those of the ring (`canonW_eq`: `canonW (·) = encRM (decRM ·)`);
* word moves: `mv d s c` (shift `|c|` bits of the stream `s` into the register `d`), `mvR d s`
  (shift `N K` bits), `cp`, `drop t c` (drop `|c|` bits of `t`), `clr`, `tl`;
* `app d s` (`d := d ++ s`, so `app d d` doubles `d`) and `eqb f a b` (`f := [a = b]`, for
  pairwise distinct registers);
* control: `rep c body` (`|c|` rounds, each after dropping the first bit of `c`), `seq`, `ifb t p q`
  (on the first bit of `t`), `nop`.

`exec N K c w` is the semantics on registers `w : Fin 64 → List Bool`; it is **total and exact**.
`compile c : XProg 105` runs every instruction in a frame of its own tapes (so each one is charged
only its own words): the operands are loaded into the work tapes `X1`, `X2` (cut to `N K` bits by
`ValVM.inP`), the operation writes `X0`, `canonRP` writes `canonW X0` into `X1`, and the result is
copied into `d`. **`run_flat_compile`**: on `enc N K w` (templates of `K`, `N`, `N K` zeros and
`N K` ones, blank work tapes, the registers), the flattened program ends in `enc N K (exec N K c w)`;
**`law_compile`**: its law is the point mass there (the compiled program is coin free). `wf_compile`: the compiled program is well
formed when no `rep` body writes its counter (`Code.WFc`).
-/

namespace SigabaNeo.Tape

namespace MVM

open Prog SigabaNeo.Lattices.Algo

/-! ### The operations -/

/-- The ring operations. -/
inductive Op where
  | add | sub | mul | neg | aut | rho | rot | dig
  deriving DecidableEq

/-- The binary operations (second operand cut to `N K` bits). -/
def Op.bin : Op → Bool
  | .add | .sub | .mul => true
  | _ => false

/-- The word function of an operation. -/
def opW (N K : ℕ) : Op → List Bool → List Bool → List Bool
  | .add, x, y => addRMW N K x y
  | .sub, x, y => subRMW N K x y
  | .mul, x, y => mulRMW N K x y
  | .neg, x, _ => notW x
  | .aut, x, y => autMW N K y.length x
  | .rho, x, y => (rhoMW K)^[y.length] x
  | .rot, x, y => rotBW N K y.length x
  | .dig, x, y => digitRW N K y.length x

/-- The tapes of `notP` inside `37` tapes. -/
def uNeg : Fin 11 → Fin 37 := ![0, 1, 5, 6, 7, 8, 9, 10, 11, 12, 13]
/-- The tapes of `rhoJP` inside `37` tapes. -/
def uRho : Fin 7 → Fin 37 := ![0, 1, 2, 3, 5, 6, 7]

theorem uNeg_inj : Function.Injective uNeg := by decide
theorem uRho_inj : Function.Injective uRho := by decide

/-- The program of an operation, on `37` tapes: `0` output, `1` first operand, `2` second operand
(or count), `3` `4` templates `K`, `N`, scratch `5 … 36`. -/
def Op.prog : Op → Prog 37
  | .add => map (Fin.castLE (by decide)) addRMP
  | .sub => map (Fin.castLE (by decide)) subRMP
  | .mul => mulRMP
  | .neg => map uNeg notP
  | .aut => map (Fin.castLE (by decide)) autMP
  | .rho => map uRho rhoJP
  | .rot => map (Fin.castLE (by decide)) rotBP
  | .dig => map (Fin.castLE (by decide)) digitRWP

/-- The condition on the second argument: `N K` bits for the binary operations. -/
def Op.Q (N K : ℕ) (o : Op) (y : List Bool) : Prop := o.bin = true → y.length = N * K

section Spec

variable {N K : ℕ}

theorem castLE_ge {m : ℕ} (h : m ≤ 37) (i : Fin m) : (Fin.castLE h i).val = i.val := rfl

/-- **The specification of the operation programs.** -/
theorem run_op (hN : 0 < N) (o : Op) (s : Store 37) (hs : ∀ i : Fin 37, 5 ≤ i.val → s i = [])
    (hK : (s 3).length = K) (hN' : (s 4).length = N) (hx : (s 1).length = N * K)
    (hy : o.Q N K (s 2)) : run o.prog s = Function.update s 0 (opW N K o (s 1) (s 2)) := by
  cases o with
  | add =>
    exact run_addRMP_map (Fin.castLE_injective _) s (fun i hi => hs _ hi) hK hN' hx (hy rfl)
  | sub =>
    exact run_subRMP_map (Fin.castLE_injective _) s (fun i hi => hs _ hi) hK hN' hx (hy rfl)
  | mul => exact run_mulRMP s hs hK hN' hx
  | neg =>
    refine run_notP_map uNeg_inj s (fun i hi => hs _ ?_)
    fin_cases i <;> simp_all [uNeg]
  | aut =>
    exact run_autMP_map (Fin.castLE_injective _) s (fun i hi => hs _ hi) hK hN' hx hN
  | rho =>
    show run (map uRho rhoJP) s = _
    rw [run_rhoJP_map uRho_inj s (fun i hi => hs _ (by fin_cases i <;> simp_all [uRho]))]
    show Function.update s (uRho 0) ((rhoMW (s (uRho 3)).length)^[(s (uRho 2)).length]
      (s (uRho 1))) = _
    rw [show uRho 0 = 0 from rfl, show uRho 1 = 1 from rfl, show uRho 2 = 2 from rfl,
      show uRho 3 = 3 from rfl, hK]; rfl
  | rot =>
    exact run_rotBP_map (Fin.castLE_injective _) s (fun i hi => hs _ hi) hK hN' hx
  | dig =>
    exact run_map_eq_update (Fin.castLE_injective _) _ s 0 _
      (run_digitRWP (s ∘ Fin.castLE (by decide)) (fun i hi => hs _ hi) rfl hK hN' hx)

theorem length_opW (hN : 0 < N) (o : Op) {x : List Bool} (y : List Bool) (hx : x.length = N * K)
    (hy : o.Q N K y) : (opW N K o x y).length = N * K := by
  cases o with
  | add => exact length_addRMW N K hx y
  | sub => exact length_subRMW N K hx y
  | mul => exact length_mulRMW N K x y
  | neg => simp [opW, hx]
  | aut => exact length_autMW N K _ x hN
  | rho => simp [opW, hx]
  | rot => exact length_rotBW N K _ hx
  | dig => exact length_concatN fun _ _ => length_bitW _ _

theorem noGrow_op (o : Op) : o.prog.NoGrow := by
  cases o <;> first | rfl | (show (map _ _).noGrowB = true; rw [noGrowB_map]; rfl)

theorem wf_op (o : Op) : o.prog.WF := by
  cases o <;> exact wf_of_wfB (by decide)

theorem preserves_op (o : Op) : o.prog.Preserves 2 := by
  cases o <;> exact preserves_of_preservesB (by decide)

end Spec

/-! ### Code and semantics -/

/-- The number of registers. -/
abbrev nR : ℕ := 64

/-- The instructions. -/
inductive Code where
  /-- `d := canonW (opW o (takeD NK a) y)` (`y`: `b` cut to `N K` bits, or `b` itself). -/
  | op (o : Op) (d a b : Fin 64)
  /-- Move `|c|` bits from the stream `s` into the register `d` (pairwise distinct). -/
  | mv (d s c : Fin 64)
  /-- Move `N K` bits from the stream `s` into the register `d` (`d ≠ s`). -/
  | mvR (d s : Fin 64)
  /-- `d := s`. -/
  | cp (d s : Fin 64)
  /-- `t := t.drop |c|` (`t ≠ c`). -/
  | drop (t c : Fin 64)
  /-- `t := []`. -/
  | clr (t : Fin 64)
  /-- `t := t.tail`. -/
  | tl (t : Fin 64)
  /-- `d := d ++ s` (`app d d` doubles `d`). -/
  | app (d s : Fin 64)
  /-- `f := [decide (a = b)]` (pairwise distinct). -/
  | eqb (f a b : Fin 64)
  /-- `|c|` rounds of the body, each after dropping the first bit of `c`. -/
  | rep (c : Fin 64) (body : Code)
  | seq (p q : Code)
  /-- `p` if the first bit of `t` is `true`, else `q`. -/
  | ifb (t : Fin 64) (p q : Code)
  | nop

/-- Registers. -/
abbrev St := Fin 64 → List Bool

/-- The second argument of an operation. -/
def arg2 (N K : ℕ) (o : Op) (y : List Bool) : List Bool := if o.bin then takeD (N * K) y else y

/-- **The semantics.** -/
def exec (N K : ℕ) : Code → St → St
  | .op o d a b, w => Function.update w d
      (canonW N K (opW N K o (takeD (N * K) (w a)) (arg2 N K o (w b))))
  | .mv d s c, w => if d = s ∨ d = c ∨ s = c then w else
      Function.update (Function.update w s ((w s).drop (w c).length)) d
        (ValVM.shiftIn (w c).length (w d) (w s))
  | .mvR d s, w => if d = s then w else
      Function.update (Function.update w s ((w s).drop (N * K))) d
        (ValVM.shiftIn (N * K) (w d) (w s))
  | .cp d s, w => Function.update w d (w s)
  | .drop t c, w => if t = c then w else Function.update w t ((w t).drop (w c).length)
  | .clr t, w => Function.update w t []
  | .tl t, w => Function.update w t (w t).tail
  | .app d s, w => Function.update w d (w d ++ w s)
  | .eqb f a b, w => if f = a ∨ f = b ∨ a = b then w else Function.update w f [decide (w a = w b)]
  | .rep c body, w =>
    (fun w' => exec N K body (Function.update w' c (w' c).tail))^[(w c).length] w
  | .seq p q, w => exec N K q (exec N K p w)
  | .ifb t p q, w => if hd (w t) = true then exec N K p w else exec N K q w
  | .nop, w => w

/-- The registers an instruction may write. -/
def Code.writes : Code → Fin 64 → Bool
  | .op _ d _ _, r => d == r
  | .mv d s _, r => d == r || s == r
  | .mvR d s, r => d == r || s == r
  | .cp d _, r => d == r
  | .drop t _, r => t == r
  | .clr t, r => t == r
  | .tl t, r => t == r
  | .app d _, r => d == r
  | .eqb f _ _, r => f == r
  | .rep c body, r => c == r || body.writes r
  | .seq p q, r => p.writes r || q.writes r
  | .ifb _ p q, r => p.writes r || q.writes r
  | .nop, _ => false

/-- Every `rep` body leaves its counter alone. -/
def Code.WFc : Code → Prop
  | .rep c body => body.writes c = false ∧ body.WFc
  | .seq p q => p.WFc ∧ q.WFc
  | .ifb _ p q => p.WFc ∧ q.WFc
  | _ => True

/-! ### Tapes -/

/-- The tapes: scratch `0 … 31`, work `X0 X1 X2` (`32 … 34`), templates `K`, `N`, `N K` zeros,
`N K` ones (`35 … 38`), helpers `39`, `40`, registers `41 …`. -/
abbrev nT : ℕ := 105

/-- A tape map from its values. -/
def ofV {m : ℕ} (g : ℕ → ℕ) (hg : ∀ j < m, g j < 105) : Fin m → Fin 105 :=
  fun j => ⟨g j.val, hg j.val j.isLt⟩

theorem ofV_inj {m : ℕ} {g : ℕ → ℕ} {hg : ∀ j < m, g j < 105}
    (h : ∀ x y, x < m → y < m → g x = g y → x = y) : Function.Injective (ofV g hg) :=
  fun x y hxy => Fin.ext (h x.val y.val x.isLt y.isLt (congrArg Fin.val hxy))

/-- An embedding from an injective function. -/
def mkE {m n : ℕ} (f : Fin m → Fin n) (h : Function.Injective f) : Fin m ↪ Fin n := ⟨f, h⟩

theorem mkE_apply {m n : ℕ} (f : Fin m → Fin n) (h : Function.Injective f) (j : Fin m) :
    mkE f h j = f j := rfl

/-- The register `r`. -/
def tR (r : Fin 64) : Fin 105 := ⟨41 + r.val, by have := r.isLt; omega⟩

theorem tR_val (r : Fin 64) : (tR r).val = 41 + r.val := rfl

/-- Load `x` (`33` or `34`) from the register `a`: `[x, zeros, a, X0, H1, H2]`. -/
def fLd (x : ℕ) (a : Fin 64) : Fin 6 → Fin 105 :=
  ofV (fun j => if j = 0 then x % 41 else if j = 1 then 37 else if j = 2 then 41 + a.val
    else if j = 3 then 32 else if j = 4 then 39 else 40)
    (by intro j hj; have := a.isLt; split_ifs <;> omega)

theorem fLd_inj (x : ℕ) (hx : x = 33 ∨ x = 34) (a : Fin 64) : Function.Injective (fLd x a) := by
  refine ofV_inj ?_
  intro p q hp hq h
  have := a.isLt
  rcases hx with rfl | rfl <;> ((try simp only at h); split_ifs at h <;> omega)

/-- The operation's tapes: `[X0, X1, third, K, N, scratch 0 … 31]`. -/
def fOp (t2 : ℕ) : Fin 37 → Fin 105 :=
  ofV (fun j => if j = 0 then 32 else if j = 1 then 33 else if j = 2 then t2 % 105
    else if j = 3 then 35 else if j = 4 then 36 else j - 5)
    (by intro j hj; split_ifs <;> omega)

theorem fOp_inj (t2 : ℕ) (h : t2 = 34 ∨ (41 ≤ t2 ∧ t2 < 105)) : Function.Injective (fOp t2) := by
  refine ofV_inj ?_
  intro p q hp hq e
  rcases h with rfl | ⟨h1, h2⟩
  · (try simp only at e); split_ifs at e <;> omega
  · have : t2 % 105 = t2 := Nat.mod_eq_of_lt h2
    simp only [this] at e; split_ifs at e <;> omega

/-- The canonicalization's tapes: `[X1, X0, ones, K, N, scratch 0 … 22]`. -/
def fCan : Fin 28 → Fin 105 :=
  ofV (fun j => if j = 0 then 33 else if j = 1 then 32 else if j = 2 then 38
    else if j = 3 then 35 else if j = 4 then 36 else j - 5)
    (by intro j hj; split_ifs <;> omega)

theorem fCan_inj : Function.Injective fCan := by
  refine ofV_inj ?_
  intro p q hp hq e
  (try simp only at e); split_ifs at e <;> omega

theorem fOp_ge5 (t2 : ℕ) (i : Fin 37) (hi : 5 ≤ i.val) : (fOp t2 i).val = i.val - 5 := by
  show (if i.val = 0 then 32 else if i.val = 1 then 33 else if i.val = 2 then t2 % 105
    else if i.val = 3 then 35 else if i.val = 4 then 36 else i.val - 5) = _
  split_ifs <;> omega

theorem fCan_ge5 (i : Fin 28) (hi : 5 ≤ i.val) : (fCan i).val = i.val - 5 := by
  show (if i.val = 0 then 33 else if i.val = 1 then 32 else if i.val = 2 then 38
    else if i.val = 3 then 35 else if i.val = 4 then 36 else i.val - 5) = _
  split_ifs <;> omega

/-- The result's tapes: `[d, X0, X1, X2]`. -/
def fOut (d : Fin 64) : Fin 4 → Fin 105 :=
  ofV (fun j => if j = 0 then 41 + d.val else if j = 1 then 32 else if j = 2 then 33 else 34)
    (by intro j hj; have := d.isLt; split_ifs <;> omega)

theorem fOut_inj (d : Fin 64) : Function.Injective (fOut d) := by
  refine ofV_inj ?_
  intro p q hp hq e
  have := d.isLt
  (try simp only at e); split_ifs at e <;> omega

/-- `mvPc` on `[stream s, register d, H1, H2, template c]`. -/
def fMv (d s : Fin 64) (c : ℕ) : Fin 5 → Fin 105 :=
  ofV (fun j => if j = 0 then 41 + s.val else if j = 1 then 41 + d.val else if j = 2 then 39
    else if j = 3 then 40 else c % 105)
    (by intro j hj; have := d.isLt; have := s.isLt; split_ifs <;> omega)

theorem fMv_inj {d s : Fin 64} {c : ℕ} (hds : d ≠ s)
    (hc : c = 37 ∨ (41 ≤ c ∧ c < 105 ∧ c ≠ 41 + d.val ∧ c ≠ 41 + s.val)) :
    Function.Injective (fMv d s c) := by
  have hds' : d.val ≠ s.val := fun h => hds (Fin.ext h)
  have := d.isLt; have := s.isLt
  refine ofV_inj ?_
  intro p q hp hq e
  rcases hc with rfl | ⟨h1, h2, h3, h4⟩
  · (try simp only at e); split_ifs at e <;> omega
  · have : c % 105 = c := Nat.mod_eq_of_lt h2
    simp only [this] at e; split_ifs at e <;> omega

/-- `cp 0 1` on `[d, s]`. -/
def fCp (d s : Fin 64) : Fin 2 → Fin 105 :=
  ofV (fun j => if j = 0 then 41 + d.val else 41 + s.val)
    (by intro j hj; have := d.isLt; have := s.isLt; split_ifs <;> omega)

theorem fCp_inj {d s : Fin 64} (h : d ≠ s) : Function.Injective (fCp d s) := by
  have hds : d.val ≠ s.val := fun e => h (Fin.ext e)
  refine ofV_inj ?_
  intro p q hp hq e
  (try simp only at e); split_ifs at e <;> omega

/-- `dropPc` on `[t, H1, c]`. -/
def fDr (t c : Fin 64) : Fin 3 → Fin 105 :=
  ofV (fun j => if j = 0 then 41 + t.val else if j = 1 then 39 else 41 + c.val)
    (by intro j hj; have := t.isLt; have := c.isLt; split_ifs <;> omega)

theorem fDr_inj {t c : Fin 64} (h : t ≠ c) : Function.Injective (fDr t c) := by
  have htc : t.val ≠ c.val := fun e => h (Fin.ext e)
  refine ofV_inj ?_
  intro p q hp hq e
  have := t.isLt; have := c.isLt
  (try simp only at e); split_ifs at e <;> omega

/-- `appT` on `[d, s, H1, H2]`. -/
def fAp (d s : Fin 64) : Fin 4 → Fin 105 :=
  ofV (fun j => if j = 0 then 41 + d.val else if j = 1 then 41 + s.val else if j = 2 then 39 else 40)
    (by intro j hj; have := d.isLt; have := s.isLt; split_ifs <;> omega)

theorem fAp_inj {d s : Fin 64} (h : d ≠ s) : Function.Injective (fAp d s) := by
  have hds : d.val ≠ s.val := fun e => h (Fin.ext e)
  refine ofV_inj ?_
  intro p q hp hq e
  have := d.isLt; have := s.isLt
  (try simp only at e); split_ifs at e <;> omega

/-- `appT` (doubling) on `[d, H1, H2]`. -/
def fAp1 (d : Fin 64) : Fin 3 → Fin 105 :=
  ofV (fun j => if j = 0 then 41 + d.val else if j = 1 then 39 else 40)
    (by intro j hj; have := d.isLt; split_ifs <;> omega)

theorem fAp1_inj (d : Fin 64) : Function.Injective (fAp1 d) := by
  refine ofV_inj ?_
  intro p q hp hq e
  have := d.isLt
  (try simp only at e); split_ifs at e <;> omega

/-- `eq` on `[a, b, f]`. -/
def fEq (f a b : Fin 64) : Fin 3 → Fin 105 :=
  ofV (fun j => if j = 0 then 41 + a.val else if j = 1 then 41 + b.val else 41 + f.val)
    (by intro j hj; have := a.isLt; have := b.isLt; have := f.isLt; split_ifs <;> omega)

theorem fEq_inj {f a b : Fin 64} (h : ¬(f = a ∨ f = b ∨ a = b)) : Function.Injective (fEq f a b) := by
  have h1 : f.val ≠ a.val := fun e => h (Or.inl (Fin.ext e))
  have h2 : f.val ≠ b.val := fun e => h (Or.inr (Or.inl (Fin.ext e)))
  have h3 : a.val ≠ b.val := fun e => h (Or.inr (Or.inr (Fin.ext e)))
  refine ofV_inj ?_
  intro p q hp hq e
  have := a.isLt; have := b.isLt; have := f.isLt
  (try simp only at e); split_ifs at e <;> omega

/-- One tape. -/
def f1 (t : Fin 105) : Fin 1 → Fin 105 := fun _ => t

theorem f1_inj (t : Fin 105) : Function.Injective (f1 t) := fun x y _ => Subsingleton.elim x y

/-- The tape `X0`. -/
def tX0 : Fin 105 := ⟨32, by decide⟩

/-- Result out: `d := X1`, clear `X0 X1 X2`. -/
def outQ : Prog 4 := cp 0 2 ⨾ clr 1 ⨾ clr 2 ⨾ clr 3

/-- The third tape of an operation: `X2` for the binary ones, the count register otherwise. -/
def t2Of (o : Op) (b : Fin 64) : ℕ := if o.bin then 34 else 41 + b.val

theorem t2Of_ok (o : Op) (b : Fin 64) : t2Of o b = 34 ∨ (41 ≤ t2Of o b ∧ t2Of o b < 105) := by
  unfold t2Of; have := b.isLt; split_ifs
  · exact Or.inl rfl
  · exact Or.inr ⟨by omega, by omega⟩

/-- The no-op. -/
def nopX : XProg 105 := .frame (mkE (f1 tX0) (f1_inj _)) (.prog (nop 0))

/-! ### The compiler -/

/-- **The program of a code**, every instruction in the frame of its own tapes. -/
def compile : Code → XProg 105
  | .op o d a b =>
    .seq (.frame (mkE (fLd 33 a) (fLd_inj 33 (Or.inl rfl) a)) (.prog ValVM.inP)) <|
    .seq (.frame (mkE (fLd 34 b) (fLd_inj 34 (Or.inr rfl) b)) (.prog ValVM.inP)) <|
    .seq (.frame (mkE (fOp (t2Of o b)) (fOp_inj _ (t2Of_ok o b))) (.prog o.prog)) <|
    .seq (.frame (mkE fCan fCan_inj) (.prog canonRP))
      (.frame (mkE (fOut d) (fOut_inj d)) (.prog outQ))
  | .mv d s c => if h : d = s ∨ d = c ∨ s = c then nopX else
      .frame (mkE (fMv d s (41 + c.val)) (fMv_inj (fun e => h (Or.inl e)) (Or.inr ⟨by omega,
        by have := c.isLt; omega,
        fun e => h (Or.inr (Or.inl (Fin.ext (by omega)))),
        fun e => h (Or.inr (Or.inr (Fin.ext (by omega))))⟩))) (.prog ValVM.mvPc)
  | .mvR d s => if h : d = s then nopX else
      .frame (mkE (fMv d s 37) (fMv_inj h (Or.inl rfl))) (.prog ValVM.mvPc)
  | .cp d s => if h : d = s then nopX else .frame (mkE (fCp d s) (fCp_inj h)) (.prog (Prog.cp 0 1))
  | .drop t c => if h : t = c then nopX else .frame (mkE (fDr t c) (fDr_inj h)) (.prog ValVM.dropPc)
  | .clr t => .frame (mkE (f1 (tR t)) (f1_inj _)) (.prog (Prog.clr 0))
  | .tl t => .frame (mkE (f1 (tR t)) (f1_inj _)) (.prog (Prog.tl 0))
  | .app d s => if h : d = s then .frame (mkE (fAp1 d) (fAp1_inj d)) (.prog (appT 0 0 1 2)) else
      .frame (mkE (fAp d s) (fAp_inj h)) (.prog (appT 0 1 2 3))
  | .eqb f a b => if h : f = a ∨ f = b ∨ a = b then nopX else
      .frame (mkE (fEq f a b) (fEq_inj h)) (.prog (.prim (.eq 0 1 2)))
  | .rep c body => .loop (tR c) (compile body)
  | .seq p q => .seq (compile p) (compile q)
  | .ifb t p q => .ifBit (tR t) (compile p) (compile q)
  | .nop => nopX

/-! ### The encoding -/

/-- The store with the work words `x0 x1 x2`, the templates, blank scratch and the registers. -/
def encX (N K : ℕ) (x0 x1 x2 : List Bool) (w : St) : Store 105 := fun t =>
  if t.val < 32 then [] else if t.val = 32 then x0 else if t.val = 33 then x1
  else if t.val = 34 then x2 else if t.val = 35 then List.replicate K false
  else if t.val = 36 then List.replicate N false else if t.val = 37 then List.replicate (N * K) false
  else if t.val = 38 then List.replicate (N * K) true
  else if h : 41 ≤ t.val then w ⟨t.val - 41, by have := t.isLt; omega⟩ else []

/-- **The store of the registers `w`.** -/
def enc (N K : ℕ) (w : St) : Store 105 := encX N K [] [] [] w

section Enc

variable {N K : ℕ} {x0 x1 x2 : List Bool} {w : St}

theorem encX_val (t : Fin 105) : encX N K x0 x1 x2 w t =
    if t.val < 32 then [] else if t.val = 32 then x0 else if t.val = 33 then x1
    else if t.val = 34 then x2 else if t.val = 35 then List.replicate K false
    else if t.val = 36 then List.replicate N false else if t.val = 37 then List.replicate (N * K) false
    else if t.val = 38 then List.replicate (N * K) true
    else if h : 41 ≤ t.val then w ⟨t.val - 41, by have := t.isLt; omega⟩ else [] := rfl

@[simp] theorem encX_tR (r : Fin 64) : encX N K x0 x1 x2 w (tR r) = w r := by
  rw [encX_val]
  have h41 : (tR r).val = 41 + r.val := rfl
  simp only [h41]
  split_ifs <;> first | omega | exact congrArg w (Fin.ext (by simp))

theorem encX_at (t : Fin 105) (n : ℕ) (h : t.val = n) : encX N K x0 x1 x2 w t =
    if n < 32 then [] else if n = 32 then x0 else if n = 33 then x1
    else if n = 34 then x2 else if n = 35 then List.replicate K false
    else if n = 36 then List.replicate N false else if n = 37 then List.replicate (N * K) false
    else if n = 38 then List.replicate (N * K) true
    else if h' : 41 ≤ n then w ⟨n - 41, by have := t.isLt; omega⟩ else [] := by
  subst h; rfl

theorem update_tR (r : Fin 64) (v : List Bool) :
    Function.update (encX N K x0 x1 x2 w) (tR r) v = encX N K x0 x1 x2 (Function.update w r v) := by
  funext t
  rw [Function.update_apply, encX_val, encX_val]
  by_cases h : t = tR r
  · subst h
    have h41 : (tR r).val = 41 + r.val := rfl
    simp only [if_true, h41]
    split_ifs <;> first | omega | simp
  · rw [if_neg h]
    have h' : t.val ≠ 41 + r.val := fun e => h (Fin.ext e)
    split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 <;> try rfl
    rw [Function.update_of_ne]
    intro e
    exact h' (by have := congrArg Fin.val e; simp at this; omega)

/-- Update a fixed tape. -/
theorem update_fixed (n : ℕ) (hn : n < 41) (v : List Bool) :
    Function.update (encX N K x0 x1 x2 w) ⟨n, by omega⟩ v = fun t =>
      if t.val = n then v else encX N K x0 x1 x2 w t := by
  funext t
  rw [Function.update_apply]
  congr 1
  exact propext ⟨fun h => by rw [h], fun h => Fin.ext h⟩

theorem update_X0 (v : List Bool) :
    Function.update (encX N K x0 x1 x2 w) ⟨32, by decide⟩ v = encX N K v x1 x2 w := by
  rw [update_fixed 32 (by decide)]
  funext t; rw [encX_val, encX_val]; split_ifs <;> first | rfl | omega

theorem update_X1 (v : List Bool) :
    Function.update (encX N K x0 x1 x2 w) ⟨33, by decide⟩ v = encX N K x0 v x2 w := by
  rw [update_fixed 33 (by decide)]
  funext t; rw [encX_val, encX_val]; split_ifs <;> first | rfl | omega

theorem update_X2 (v : List Bool) :
    Function.update (encX N K x0 x1 x2 w) ⟨34, by decide⟩ v = encX N K x0 x1 v w := by
  rw [update_fixed 34 (by decide)]
  funext t; rw [encX_val, encX_val]; split_ifs <;> first | rfl | omega

theorem tR_inj {r r' : Fin 64} (h : tR r = tR r') : r = r' :=
  Fin.ext (by have := congrArg Fin.val h; simp [tR] at this; omega)

theorem tailAt_tR (r : Fin 64) : tailAt (tR r) (enc N K w) = enc N K
    (Function.update w r (w r).tail) := by
  rw [tailAt, enc, encX_tR, update_tR]; rfl

end Enc

/-! ### Correctness of the instructions -/

section Correct

variable {N K : ℕ}

theorem run_clr_blank {n k : ℕ} {u : Fin n → Fin k} (hu : Function.Injective u) (j : Fin n)
    (s : Store k) (h : s (u j) = []) : run (map u (Prog.clr j)) s = s := by
  rw [run_map_eq_update hu _ s j [] (run_clear j _), ← h, Function.update_eq_self]

theorem run_outQ (t : Store 4) :
    run outQ t = Function.update (Function.update (Function.update (Function.update t 0 (t 2))
      1 []) 2 []) 3 [] := by
  simp [outQ, run_seq, run_copy, run_clear]

theorem run_map_outQ {k : ℕ} {u : Fin 4 → Fin k} (hu : Function.Injective u) (S : Store k) :
    run (map u outQ) S = Function.update (Function.update (Function.update (Function.update S
      (u 0) (S (u 2))) (u 1) []) (u 2) []) (u 3) [] := by
  rw [run_map hu, run_outQ, extend_update hu, extend_update hu, extend_update hu,
    extend_update hu, extend_comp_self]
  rfl

/-- Loading an operand. -/
theorem run_load (x : ℕ) (hx : x = 33 ∨ x = 34) (a : Fin 64) (x0' x1 x2 : List Bool) (w : St)
    (h0 : x0' = []) :
    run (map (fLd x a) ValVM.inP) (encX N K x0' x1 x2 w) =
      Function.update (encX N K x0' x1 x2 w) ⟨x, by omega⟩ (takeD (N * K) (w a)) := by
  subst h0
  have hu := fLd_inj x hx a
  rw [run_map_eq_update hu ValVM.inP _ 0 _ (ValVM.run_inP _ ?_ ?_ ?_)]
  · congr 1
    · exact Fin.ext (by rcases hx with rfl | rfl <;> rfl)
    · simp only [Function.comp_apply]
      have e1 : fLd x a 1 = ⟨37, by decide⟩ := Fin.ext (by simp [fLd, ofV])
      have e2 : fLd x a 2 = tR a := Fin.ext (by simp [fLd, ofV, tR])
      rw [e1, e2, encX_tR, encX_at _ 37 rfl]
      simp
  all_goals
    simp only [Function.comp_apply]
    rw [encX_at _ _ rfl]
    simp [fLd, ofV]

/-- **An operation instruction.** -/
theorem run_opI (hN : 0 < N) (hK : 0 < K) (o : Op) (d a b : Fin 64) (w : St) :
    run (XProg.flat (compile (.op o d a b))) (enc N K w) = enc N K (exec N K (.op o d a b) w) := by
  show run (map (fLd 33 a) ValVM.inP ⨾ (map (fLd 34 b) ValVM.inP ⨾ (map (fOp (t2Of o b)) o.prog ⨾
    (map fCan canonRP ⨾ map (fOut d) outQ)))) _ = _
  simp only [run_seq]
  rw [enc, run_load 33 (Or.inl rfl) a _ _ _ _ rfl, update_X1, run_load 34 (Or.inr rfl) b _ _ _ _ rfl,
    update_X2]
  set x1 := takeD (N * K) (w a)
  set x2 := takeD (N * K) (w b)
  have hx1 : x1.length = N * K := length_takeD _ _
  -- the operation
  have hu := fOp_inj _ (t2Of_ok o b)
  have e2 : (encX N K [] x1 x2 w ∘ fOp (t2Of o b)) 2 = arg2 N K o (w b) := by
    have hv : (fOp (t2Of o b) 2).val = t2Of o b % 105 := rfl
    simp only [Function.comp_apply, arg2]
    cases hb : o.bin
    · have ht : t2Of o b = 41 + b.val := by simp [t2Of, hb]
      have : fOp (t2Of o b) 2 = tR b :=
        Fin.ext (by rw [hv, ht]; show _ = 41 + b.val; have := b.isLt; omega)
      rw [this, encX_tR]; simp
    · have ht : t2Of o b = 34 := by simp [t2Of, hb]
      rw [encX_at _ 34 (by rw [hv, ht])]; simp [x2]
  have hQ : o.Q N K (arg2 N K o (w b)) := by
    intro hb; simp [arg2, hb]
  rw [run_map_eq_update hu o.prog _ 0 _ (run_op hN o _ ?_ ?_ ?_ ?_ (by rw [e2]; exact hQ))]
  rotate_left
  · intro i hi
    simp only [Function.comp_apply]
    rw [encX_at _ (i.val - 5) (fOp_ge5 _ i hi)]
    rw [if_pos (by omega)]
  · simp only [Function.comp_apply]; rw [encX_at _ 35 (by simp [fOp, ofV])]; simp
  · simp only [Function.comp_apply]; rw [encX_at _ 36 (by simp [fOp, ofV])]; simp
  · simp only [Function.comp_apply]; rw [encX_at _ 33 (by simp [fOp, ofV])]; simp [hx1]
  have e1 : (encX N K [] x1 x2 w ∘ fOp (t2Of o b)) 1 = x1 := by
    simp only [Function.comp_apply]; rw [encX_at _ 33 (by simp [fOp, ofV])]; simp
  rw [e1, e2, show fOp (t2Of o b) 0 = ⟨32, by decide⟩ from Fin.ext (by simp [fOp, ofV]), update_X0]
  set y := opW N K o x1 (arg2 N K o (w b))
  have hy : y.length = N * K := length_opW hN o _ hx1 hQ
  -- the canonicalization
  rw [run_canonRP_map (K := K) (N := N) fCan_inj hK _ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi
    rw [encX_at _ (i.val - 5) (fCan_ge5 i hi)]
    rw [if_pos (by omega)]
  · rw [encX_at _ 35 (by simp [fCan, ofV])]; simp
  · rw [encX_at _ 36 (by simp [fCan, ofV])]; simp
  · rw [encX_at _ 32 (by simp [fCan, ofV])]; simp [hy]
  · rw [encX_at _ 38 (by simp [fCan, ofV])]; simp
  rw [show fCan 0 = ⟨33, by decide⟩ from Fin.ext (by simp [fCan, ofV]),
    show fCan 1 = ⟨32, by decide⟩ from Fin.ext (by simp [fCan, ofV])]
  rw [encX_at _ 32 rfl, update_X1]
  simp only [show ¬ (32 < 32) from by omega, if_false, if_true]
  -- the result
  rw [run_map_outQ (fOut_inj d), show fOut d 0 = tR d from Fin.ext rfl,
    show fOut d 1 = ⟨32, by decide⟩ from Fin.ext rfl, show fOut d 2 = ⟨33, by decide⟩ from Fin.ext rfl,
    show fOut d 3 = ⟨34, by decide⟩ from Fin.ext rfl, encX_at _ 33 rfl]
  simp only [show ¬ (33 < 32) from by omega, show ¬ (33 = 32) from by omega, if_false, if_true]
  rw [update_tR, update_X0, update_X1, update_X2]
  rfl

theorem run_nopX (S : Store 105) : run (XProg.flat nopX) S = S := by
  show run (map (f1 tX0) (nop 0)) _ = _
  rw [run_map (f1_inj _)]
  simp only [run_nop]
  exact extend_comp_self _

theorem encX_H1 {x0 x1 x2 : List Bool} {w : St} : encX N K x0 x1 x2 w ⟨39, by decide⟩ = [] := rfl
theorem encX_H2 {x0 x1 x2 : List Bool} {w : St} : encX N K x0 x1 x2 w ⟨40, by decide⟩ = [] := rfl

theorem tR_ne_H1 (r : Fin 64) : tR r ≠ ⟨39, by decide⟩ := fun e => by
  have := congrArg Fin.val e; simp [tR] at this; omega
theorem tR_ne_H2 (r : Fin 64) : tR r ≠ ⟨40, by decide⟩ := fun e => by
  have := congrArg Fin.val e; simp [tR] at this; omega

theorem run_mvI {d s' : Fin 64} {c : ℕ} (h : Function.Injective (fMv d s' c)) (w : St)
    (hc4 : fMv d s' c 4 = tc) (hc : enc N K w tc = v) :
    run (map (fMv d s' c) ValVM.mvPc) (enc N K w) =
      enc N K (Function.update (Function.update w s' ((w s').drop v.length)) d
        (ValVM.shiftIn v.length (w d) (w s'))) := by
  rw [ValVM.run_mvPc_map h _ (by rw [show fMv d s' c 2 = ⟨39, by decide⟩ from Fin.ext rfl]; rfl)
    (by rw [show fMv d s' c 3 = ⟨40, by decide⟩ from Fin.ext rfl]; rfl)]
  rw [show fMv d s' c 0 = tR s' from Fin.ext rfl, show fMv d s' c 1 = tR d from Fin.ext rfl, hc4, hc,
    enc, encX_tR, encX_tR, update_tR, update_tR]
  rfl

/-- **The flattened program computes the semantics.** -/
theorem run_flat_compile (hN : 0 < N) (hK : 0 < K) :
    ∀ (c : Code) (w : St), run (XProg.flat (compile c)) (enc N K w) = enc N K (exec N K c w)
  | .op o d a b, w => run_opI hN hK o d a b w
  | .mv d s' c, w => by
    by_cases h : d = s' ∨ d = c ∨ s' = c
    · simp only [compile, dif_pos h, exec, if_pos h]; exact run_nopX _
    · simp only [compile, dif_neg h, exec, if_neg h]
      show run (map (fMv d s' (41 + c.val)) ValVM.mvPc) _ = _
      exact run_mvI (tc := tR c) (v := w c) (fMv_inj (fun e => h (Or.inl e)) (Or.inr ⟨by omega,
        by have := c.isLt; omega, fun e => h (Or.inr (Or.inl (Fin.ext (by omega)))),
        fun e => h (Or.inr (Or.inr (Fin.ext (by omega))))⟩)) w
        (Fin.ext (show (41 + c.val) % 105 = 41 + c.val from Nat.mod_eq_of_lt (by omega)))
        (encX_tR c)
  | .mvR d s', w => by
    by_cases h : d = s'
    · simp only [compile, dif_pos h, exec, if_pos h]; exact run_nopX _
    · simp only [compile, dif_neg h, exec, if_neg h]
      show run (map (fMv d s' 37) ValVM.mvPc) _ = _
      have := run_mvI (N := N) (K := K) (fMv_inj h (Or.inl rfl)) w
        (tc := ⟨37, by decide⟩) (v := List.replicate (N * K) false) (Fin.ext rfl) rfl
      rw [List.length_replicate] at this
      exact this
  | .cp d s', w => by
    by_cases h : d = s'
    · subst h; simp only [compile, dif_pos rfl, exec, Function.update_eq_self]; exact run_nopX _
    · simp only [compile, dif_neg h, exec]
      show run (map (fCp d s') (Prog.cp 0 1)) _ = _
      rw [run_map_eq_update (fCp_inj h) _ _ 0 _ (run_copy 0 1 _)]
      rw [show fCp d s' 0 = tR d from Fin.ext rfl, Function.comp_apply,
        show fCp d s' 1 = tR s' from Fin.ext rfl, enc, encX_tR, update_tR]; rfl
  | .drop t c, w => by
    by_cases h : t = c
    · simp only [compile, dif_pos h, exec, if_pos h]; exact run_nopX _
    · simp only [compile, dif_neg h, exec, if_neg h]
      show run (map (fDr t c) ValVM.dropPc) _ = _
      have h1 : enc N K w (fDr t c 1) = [] := rfl
      rw [ValVM.run_dropPc_map (fDr_inj h) _ h1]
      rw [show fDr t c 0 = tR t from Fin.ext rfl, show fDr t c 2 = tR c from Fin.ext rfl, enc,
        encX_tR, encX_tR, update_tR]; rfl
  | .clr t, w => by
    show run (map (f1 (tR t)) (Prog.clr 0)) _ = _
    rw [run_map_eq_update (f1_inj _) _ _ 0 _ (run_clear 0 _)]
    rw [show f1 (tR t) 0 = tR t from rfl, enc, update_tR]; rfl
  | .tl t, w => by
    show run (map (f1 (tR t)) (Prog.tl 0)) _ = _
    rw [run_map_eq_update (f1_inj _) _ _ 0 _ (run_tail 0 _)]
    rw [show f1 (tR t) 0 = tR t from rfl, Function.comp_apply, enc]
    rw [show (f1 (tR t) 0) = tR t from rfl, encX_tR, update_tR]; rfl
  | .rep c body, w => by
    show run (Prog.loop (tR c) (XProg.flat (compile body))) _ = _
    rw [run_loop, enc, encX_tR, exec]
    have ih := run_flat_compile hN hK body
    have key : ∀ (m : ℕ) (w' : St),
        (fun t => run (XProg.flat (compile body)) (tailAt (tR c) t))^[m] (enc N K w') =
          enc N K ((fun w'' => exec N K body (Function.update w'' c (w'' c).tail))^[m] w') := by
      intro m
      induction m with
      | zero => intro w'; rfl
      | succ m ihm =>
        intro w'
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, tailAt_tR, ih, ihm]
    exact key _ w
  | .seq p q, w => by
    show run (XProg.flat (compile p) ⨾ XProg.flat (compile q)) _ = _
    rw [run_seq, run_flat_compile hN hK p, run_flat_compile hN hK q]
    rfl
  | .ifb t p q, w => by
    show run (Prog.ifBit (tR t) (XProg.flat (compile p)) (XProg.flat (compile q))) _ = _
    rw [run_ifBit, enc, encX_tR, exec]
    split_ifs
    · exact run_flat_compile hN hK p w
    · exact run_flat_compile hN hK q w
  | .app d s', w => by
    by_cases h : d = s'
    · subst h
      simp only [compile, dif_pos rfl, exec]
      show run (map (fAp1 d) (appT 0 0 1 2)) _ = _
      rw [run_map_eq_update (fAp1_inj d) _ _ 0 _ (run_appT_blank (by decide) (by decide)
        (by decide) _ (by simp only [Function.comp_apply]; exact encX_at _ 39 rfl)
        (by simp only [Function.comp_apply]; exact encX_at _ 40 rfl))]
      rw [show fAp1 d 0 = tR d from Fin.ext rfl, Function.comp_apply,
        show fAp1 d 0 = tR d from Fin.ext rfl, enc, encX_tR, update_tR]; rfl
    · simp only [compile, dif_neg h, exec]
      show run (map (fAp d s') (appT 0 1 2 3)) _ = _
      rw [run_map_eq_update (fAp_inj h) _ _ 0 _ (run_appT_blank (by decide) (by decide)
        (by decide) _ (by simp only [Function.comp_apply]; exact encX_at _ 39 rfl)
        (by simp only [Function.comp_apply]; exact encX_at _ 40 rfl))]
      rw [show fAp d s' 0 = tR d from Fin.ext rfl, Function.comp_apply, Function.comp_apply,
        show fAp d s' 0 = tR d from Fin.ext rfl, show fAp d s' 1 = tR s' from Fin.ext rfl, enc,
        encX_tR, encX_tR, update_tR]; rfl
  | .eqb f a b, w => by
    by_cases h : f = a ∨ f = b ∨ a = b
    · simp only [compile, dif_pos h, exec, if_pos h]; exact run_nopX _
    · simp only [compile, dif_neg h, exec, if_neg h]
      show run (map (fEq f a b) (.prim (.eq 0 1 2))) _ = _
      rw [run_map_eq_update (fEq_inj h) _ _ 2 _ (run_prim _ _)]
      rw [show fEq f a b 2 = tR f from Fin.ext rfl, Function.comp_apply, Function.comp_apply,
        show fEq f a b 0 = tR a from Fin.ext rfl, show fEq f a b 1 = tR b from Fin.ext rfl, enc,
        encX_tR, encX_tR, update_tR]; rfl
  | .nop, w => run_nopX _

theorem noGrow_nopX : (XProg.flat nopX).NoGrow := by
  show (map _ (nop 0)).noGrowB = true; rw [noGrowB_map]; rfl

theorem coinFree_flat_compile : ∀ c : Code, (XProg.flat (compile c)).CoinFree
  | .op o d a b => by
    show (map _ ValVM.inP ⨾ (map _ ValVM.inP ⨾ (map _ o.prog ⨾ (map _ canonRP ⨾
      map _ outQ)))).coinFreeB = true
    simp only [coinFreeB, coinFreeB_mapP, Bool.and_eq_true]
    refine ⟨rfl, rfl, ?_, rfl, rfl⟩
    cases o <;> first | rfl | (show (map _ _).coinFreeB = true; rw [coinFreeB_mapP]; rfl)
  | .mv d s c => by
    unfold compile; split_ifs
    · rfl
    · show (map _ ValVM.mvPc).coinFreeB = true; rw [coinFreeB_mapP]; rfl
  | .mvR d s => by
    unfold compile; split_ifs
    · rfl
    · show (map _ ValVM.mvPc).coinFreeB = true; rw [coinFreeB_mapP]; rfl
  | .cp d s => by
    unfold compile; split_ifs
    · rfl
    · rfl
  | .drop t c => by
    unfold compile; split_ifs
    · rfl
    · show (map _ ValVM.dropPc).coinFreeB = true; rw [coinFreeB_mapP]; rfl
  | .clr t => rfl
  | .tl t => rfl
  | .app d s => by
    unfold compile; split_ifs
    · show (map _ (appT 0 0 1 2)).coinFreeB = true; rw [coinFreeB_mapP]; rfl
    · show (map _ (appT 0 1 2 3)).coinFreeB = true; rw [coinFreeB_mapP]; rfl
  | .eqb f a b => by
    unfold compile; split_ifs
    · rfl
    · rfl
  | .rep c body => coinFree_flat_compile body
  | .seq p q => by
    show (XProg.flat (compile p)).coinFreeB && (XProg.flat (compile q)).coinFreeB = true
    rw [coinFree_flat_compile p, coinFree_flat_compile q]; rfl
  | .ifb t p q => by
    show (XProg.flat (compile p)).coinFreeB && (XProg.flat (compile q)).coinFreeB = true
    rw [coinFree_flat_compile p, coinFree_flat_compile q]; rfl
  | .nop => rfl

/-- A framed program whose flattening is coin free denotes the run of its flattening. -/
theorem denote_eq_run_flat_cf : ∀ {k : ℕ} (p : XProg k), (XProg.flat p).CoinFree →
    ∀ s, p.denote s = pure (Prog.run (XProg.flat p) s)
  | _, .prog p, h, s => denote_eq_run_of_coinFree p h s
  | _, .frame e p, h, s => by
    have hp : (XProg.flat p).CoinFree := by
      have := h; simp only [XProg.flat, CoinFree] at this; rwa [coinFreeB_mapP] at this
    rw [XProg.denote, denote_eq_run_flat_cf p hp, map_pure, XProg.flat, run_map e.injective,
      XProg.embedF_eq_extend]
    rfl
  | _, .seq p q, h, s => by
    simp only [XProg.flat, CoinFree, coinFreeB, Bool.and_eq_true] at h
    rw [XProg.denote, denote_eq_run_flat_cf p h.1, pure_bind, denote_eq_run_flat_cf q h.2]; rfl
  | _, .ifBlank i p q, h, s => by
    simp only [XProg.flat, CoinFree, coinFreeB, Bool.and_eq_true] at h
    rw [XProg.denote, XProg.flat, run_ifBlank, denote_eq_run_flat_cf p h.1,
      denote_eq_run_flat_cf q h.2]
    split_ifs <;> rfl
  | _, .ifBit i p q, h, s => by
    simp only [XProg.flat, CoinFree, coinFreeB, Bool.and_eq_true] at h
    rw [XProg.denote, XProg.flat, run_ifBit, denote_eq_run_flat_cf p h.1,
      denote_eq_run_flat_cf q h.2]
    simp only [head?_eq_some_true]
    split_ifs <;> rfl
  | _, .loop i b, h, s => by
    have hb : (XProg.flat b).CoinFree := h
    rw [XProg.denote, XProg.flat, run_loop]
    have : (fun t => XProg.denote b (tailAt i t)) =
        fun t => pure (Prog.run (XProg.flat b) (tailAt i t)) :=
      funext fun t => denote_eq_run_flat_cf b hb _
    rw [this]
    exact iterate_pure (fun t => Prog.run (XProg.flat b) (tailAt i t)) _ s

/-- **The law of a compiled code**: the point mass at the encoding of its semantics. -/
theorem law_compile (hN : 0 < N) (hK : 0 < K) (c : Code) (w : St) :
    (compile c).law (enc N K w) = PMF.pure (enc N K (exec N K c w)) := by
  rw [XProg.law, denote_eq_run_flat_cf _ (coinFree_flat_compile c), Cslib.ProbComp.eval_pure,
    run_flat_compile hN hK c w]

/-! ### Well-formedness -/

theorem preserves_nopX (r : Fin 64) : nopX.Preserves (tR r) := by
  intro j h
  have hv := congrArg Fin.val h
  rw [tR_val] at hv
  simp [mkE, f1, tX0] at hv
  omega

theorem preserves_compile : ∀ (c : Code) (r : Fin 64), c.writes r = false →
    (compile c).Preserves (tR r)
  | .op o d a b, r, h => by
    simp only [Code.writes, beq_eq_false_iff_ne, ne_eq] at h
    have hd : d.val ≠ r.val := fun e => h (Fin.ext e)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j hj; have hv := congrArg Fin.val hj
      fin_cases j <;> first | exact preserves_of_preservesB (by decide) |
        (simp [mkE, fLd, ofV, tR_val] at hv; omega)
    · intro j hj; have hv := congrArg Fin.val hj
      fin_cases j <;> first | exact preserves_of_preservesB (by decide) |
        (simp [mkE, fLd, ofV, tR_val] at hv; omega)
    · intro j hj
      by_cases j2 : j = 2
      · subst j2; exact preserves_op o
      · exfalso
        have hv := congrArg Fin.val hj
        have hj' : j.val ≠ 2 := fun e => j2 (Fin.ext e)
        simp only [mkE, Function.Embedding.coeFn_mk, fOp, ofV, tR_val] at hv
        split_ifs at hv <;> omega
    · intro j hj; have hv := congrArg Fin.val hj
      exfalso
      simp only [mkE, Function.Embedding.coeFn_mk, fCan, ofV, tR_val] at hv
      split_ifs at hv <;> omega
    · intro j hj; have hv := congrArg Fin.val hj
      fin_cases j <;> (simp [mkE, fOut, ofV, tR_val] at hv; omega)
  | .mv d s c, r, h => by
    simp only [Code.writes, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
    have hd : d.val ≠ r.val := fun e => h.1 (Fin.ext e)
    have hs : s.val ≠ r.val := fun e => h.2 (Fin.ext e)
    unfold compile; split_ifs
    · exact preserves_nopX r
    · intro j hj; have hv := congrArg Fin.val hj
      fin_cases j <;> first | exact preserves_of_preservesB (by decide) |
        (simp [mkE, fMv, ofV, tR_val] at hv; omega)
  | .mvR d s, r, h => by
    simp only [Code.writes, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
    have hd : d.val ≠ r.val := fun e => h.1 (Fin.ext e)
    have hs : s.val ≠ r.val := fun e => h.2 (Fin.ext e)
    unfold compile; split_ifs
    · exact preserves_nopX r
    · intro j hj; have hv := congrArg Fin.val hj
      fin_cases j <;> first | exact preserves_of_preservesB (by decide) |
        (simp [mkE, fMv, ofV, tR_val] at hv; omega)
  | .cp d s, r, h => by
    simp only [Code.writes, beq_eq_false_iff_ne, ne_eq] at h
    have hd : d.val ≠ r.val := fun e => h (Fin.ext e)
    unfold compile; split_ifs
    · exact preserves_nopX r
    · intro j hj; have hv := congrArg Fin.val hj
      fin_cases j <;> first | exact preserves_of_preservesB (by decide) |
        (simp [mkE, fCp, ofV, tR_val] at hv; omega)
  | .drop t c, r, h => by
    simp only [Code.writes, beq_eq_false_iff_ne, ne_eq] at h
    have ht : t.val ≠ r.val := fun e => h (Fin.ext e)
    unfold compile; split_ifs
    · exact preserves_nopX r
    · intro j hj; have hv := congrArg Fin.val hj
      fin_cases j <;> first | exact preserves_of_preservesB (by decide) |
        (simp [mkE, fDr, ofV, tR_val] at hv; omega)
  | .clr t, r, h => by
    simp only [Code.writes, beq_eq_false_iff_ne, ne_eq] at h
    intro j hj; exact absurd (tR_inj ((show f1 (tR t) j = tR t from rfl).symm.trans hj)) h
  | .tl t, r, h => by
    simp only [Code.writes, beq_eq_false_iff_ne, ne_eq] at h
    intro j hj; exact absurd (tR_inj ((show f1 (tR t) j = tR t from rfl).symm.trans hj)) h
  | .app d s, r, h => by
    simp only [Code.writes, beq_eq_false_iff_ne, ne_eq] at h
    have hd : d.val ≠ r.val := fun e => h (Fin.ext e)
    unfold compile; split_ifs
    · intro j hj; have hv := congrArg Fin.val hj
      fin_cases j <;> (simp [mkE, fAp1, ofV, tR_val] at hv; omega)
    · intro j hj; have hv := congrArg Fin.val hj
      fin_cases j <;> first | exact preserves_of_preservesB (by decide) |
        (simp [mkE, fAp, ofV, tR_val] at hv; omega)
  | .eqb f a b, r, h => by
    simp only [Code.writes, beq_eq_false_iff_ne, ne_eq] at h
    have hf : f.val ≠ r.val := fun e => h (Fin.ext e)
    unfold compile; split_ifs
    · exact preserves_nopX r
    · intro j hj; have hv := congrArg Fin.val hj
      fin_cases j <;> first | exact preserves_of_preservesB (by decide) |
        (simp [mkE, fEq, ofV, tR_val] at hv; omega)
  | .rep c body, r, h => by
    simp only [Code.writes, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
    exact ⟨fun e => h.1 (tR_inj e), preserves_compile body r h.2⟩
  | .seq p q, r, h => by
    simp only [Code.writes, Bool.or_eq_false_iff] at h
    exact ⟨preserves_compile p r h.1, preserves_compile q r h.2⟩
  | .ifb t p q, r, h => by
    simp only [Code.writes, Bool.or_eq_false_iff] at h
    exact ⟨preserves_compile p r h.1, preserves_compile q r h.2⟩
  | .nop, r, _ => preserves_nopX r

theorem wf_compile : ∀ c : Code, c.WFc → (compile c).WF
  | .op o d a b, _ => ⟨wf_of_wfB (by decide), wf_of_wfB (by decide), wf_op o,
      wf_of_wfB (by decide), wf_of_wfB (by decide)⟩
  | .mv d s c, _ => by
    unfold compile; split_ifs
    · exact trivial
    · exact wf_of_wfB (by decide)
  | .mvR d s, _ => by
    unfold compile; split_ifs
    · exact trivial
    · exact wf_of_wfB (by decide)
  | .cp d s, _ => by
    unfold compile; split_ifs
    · exact trivial
    · exact trivial
  | .drop t c, _ => by
    unfold compile; split_ifs
    · exact trivial
    · exact wf_of_wfB (by decide)
  | .clr t, _ => trivial
  | .tl t, _ => trivial
  | .app d s, _ => by
    unfold compile; split_ifs
    · exact wf_of_wfB (by decide)
    · exact wf_of_wfB (by decide)
  | .eqb f a b, _ => by
    unfold compile; split_ifs
    · exact trivial
    · exact trivial
  | .rep c body, h => ⟨wf_compile body h.2, preserves_compile body c h.1⟩
  | .seq p q, h => ⟨wf_compile p h.1, wf_compile q h.2⟩
  | .ifb t p q, h => ⟨wf_compile p h.1, wf_compile q h.2⟩
  | .nop, _ => trivial

end Correct

end MVM

end SigabaNeo.Tape
