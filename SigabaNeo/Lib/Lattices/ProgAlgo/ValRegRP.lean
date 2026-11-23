import SigabaNeo.Lib.Lattices.ProgAlgo.ValReg
import SigabaNeo.Lib.Lattices.ProgAlgo.ValFhat
import SigabaNeo.Lib.Lattices.Homomorphic.RegProg

/-!
# Register programs on the word machine

The slot program of a register program `rp : RP (Fin n) W'` (`rpSP`: slot `0` the constant,
`1 … n` the inputs, `n + 1 + r` the register `r`; its word is `RP.rpW`) runs on the store
`C :: ins ++ regs ++ C^pad` as `RP.run` on the registers (`rl_rpSP`). So, after `rloopC`, `OUTW`
holds the register `r` written last, and by `RP.run_eq_valueOf` this is `SLP.valueOf` of the
unfolding `RP.toSLP rp` at the wire of `r`:

* with the single `gate` (`blockSpec_gate`): the value of the predicate (`outw_rloopC_gate`);
* with the NAND block (`blockSpec_nandC`): the word of `fhatV` at that wire (`outw_rloopC_nand`).
-/

namespace SigabaNeo.Tape

namespace ValVM

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP SigabaNeo.Lattices.Algo SigabaNeo.Encode

set_option linter.unusedSimpArgs false

variable {V : ℕ} {f : List Bool → List Bool → List Bool}

/-! ### Running a register program under a map -/

theorem RP_run_map {ι α β : Type*} {W' : ℕ} (P : α → Prop) (g : α → β) (inp : ι → α) (one : α)
    (step : α → α → α) (inp' : ι → β) (one' : β) (step' : β → β → β)
    (hi : ∀ i, inp' i = g (inp i)) (ho : one' = g one)
    (hs : ∀ a b, P a → P b → step' (g a) (g b) = g (step a b))
    (hP : ∀ a b, P a → P b → P (step a b)) (hPi : ∀ i, P (inp i)) (hPo : P one) :
    ∀ (rp : RP ι W') (regs : Fin W' → α), (∀ r, P (regs r)) →
      RP.run inp' one' step' rp (g ∘ regs) = g ∘ RP.run inp one step rp regs := by
  have hsrc : ∀ (regs : Fin W' → α) (s : Src ι W'),
      s.val inp' one' (g ∘ regs) = g (s.val inp one regs) := by
    intro regs s; cases s <;> simp [Src.val, hi, ho]
  have hsP : ∀ (regs : Fin W' → α), (∀ r, P (regs r)) → ∀ s : Src ι W', P (s.val inp one regs) := by
    intro regs h s; cases s <;> simp [Src.val, hPi, hPo, h]
  intro rp
  induction rp with
  | nil => intro regs _; rfl
  | cons ins rp ih =>
    intro regs h
    rw [RP.run_cons, RP.run_cons, hsrc, hsrc, hs _ _ (hsP regs h _) (hsP regs h _)]
    have e : Function.update (g ∘ regs) ins.dst (g (step (ins.a.val inp one regs)
        (ins.b.val inp one regs))) = g ∘ Function.update regs ins.dst
        (step (ins.a.val inp one regs) (ins.b.val inp one regs)) := by
      funext r; by_cases hr : r = ins.dst
      · subst hr; simp
      · simp [Function.update_of_ne hr]
    rw [e]
    exact ih _ (fun r => by
      by_cases hr : r = ins.dst
      · subst hr; rw [Function.update_self]; exact hP _ _ (hsP regs h _) (hsP regs h _)
      · rw [Function.update_of_ne hr]; exact h r)

/-! ### The slot program of a register program -/

variable {n W' : ℕ}

/-- **The slot program of a register program** on `n` inputs. -/
def rpSP (rp : RP (Fin n) W') : SProg :=
  rp.map fun ins => (RP.regSlot n ins.dst, ins.a.slot, ins.b.slot)

theorem spW_rpSP (S : ℕ) (rp : RP (Fin n) W') : spW S (rpSP rp) = RP.rpW S rp := by
  induction rp with
  | nil => rfl
  | cons ins rp ih =>
    rw [rpSP, List.map_cons, spW_cons, ← rpSP, ih, RP.rpW_cons]
    rfl

theorem length_rpSP (rp : RP (Fin n) W') : (rpSP rp).length = rp.length := by simp [rpSP]

theorem bnd_rpSP {W : ℕ} (h : n + W' ≤ W) (rp : RP (Fin n) W') :
    ∀ g ∈ rpSP rp, g.1 ≤ W ∧ g.2.1 ≤ W ∧ g.2.2 ≤ W := by
  intro g hg
  simp only [rpSP, List.mem_map] at hg
  obtain ⟨ins, -, rfl⟩ := hg
  have h1 := ins.a.slot_lt
  have h2 := ins.b.slot_lt
  have h3 := ins.dst.isLt
  simp only [RP.regSlot]
  omega

/-- The store: the constant, the inputs, the registers, the padding. -/
def rStore (C : List Bool) (ins : List (List Bool)) (regs : Fin W' → List Bool) (pad : ℕ) :
    List (List Bool) := C :: ins ++ List.ofFn regs ++ List.replicate pad C

theorem length_rStore (C : List Bool) (ins : List (List Bool)) (regs : Fin W' → List Bool)
    (pad : ℕ) : (rStore C ins regs pad).length = 1 + ins.length + W' + pad := by
  simp [rStore]; omega

/-- The inputs of a store. -/
def inpOf (C : List Bool) (ins : List (List Bool)) : Fin n → List Bool := fun i => ins.getD i C

theorem getD_rStore_src (C : List Bool) (ins : List (List Bool)) (hins : ins.length = n)
    (regs : Fin W' → List Bool) (pad : ℕ) (s : Src (Fin n) W') :
    (rStore C ins regs pad).getD s.slot C = s.val (inpOf C ins) C regs := by
  cases s with
  | one => simp [rStore, Src.slot, Src.val]
  | input i =>
    have hi : i.val < ins.length := by rw [hins]; exact i.isLt
    simp only [rStore, Src.slot, Src.val, inpOf, List.cons_append, List.getD_cons_succ,
      List.append_assoc]
    rw [List.getD_append _ _ _ _ hi]
  | reg r =>
    simp only [rStore, Src.slot, Src.val, List.cons_append, List.append_assoc]
    rw [show n + 1 + r.val = (r.val + n) + 1 by omega, List.getD_cons_succ,
      List.getD_append_right _ _ _ _ (by omega), hins, Nat.add_sub_cancel,
      List.getD_append _ _ _ _ (by simp)]
    simp

theorem set_rStore (C : List Bool) (ins : List (List Bool)) (hins : ins.length = n)
    (regs : Fin W' → List Bool) (pad : ℕ) (r : Fin W') (v : List Bool) :
    (rStore C ins regs pad).set (RP.regSlot n r) v = rStore C ins (Function.update regs r v) pad := by
  simp only [rStore, RP.regSlot, List.cons_append, List.append_assoc]
  rw [show n + 1 + r.val = (r.val + n) + 1 by omega, List.set_cons_succ,
    List.set_append_right _ _ (by omega), hins, Nat.add_sub_cancel,
    List.set_append_left _ _ (by simp)]
  congr 3
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_set, List.getElem_ofFn, Function.update_apply]
  by_cases hj : j = r.val
  · subst hj; simp
  · rw [if_neg (Ne.symm hj), if_neg (fun e => hj (by rw [← e]))]

/-- **A register program on the slots is `RP.run` on the registers.** -/
theorem rl_rpSP (F : List Bool → List Bool → List Bool) (C : List Bool) (ins : List (List Bool))
    (hins : ins.length = n) (pad : ℕ) :
    ∀ (rp : RP (Fin n) W') (regs : Fin W' → List Bool),
      rl F C (rStore C ins regs pad) (rpSP rp) =
        rStore C ins (RP.run (inpOf C ins) C F rp regs) pad := by
  intro rp
  induction rp with
  | nil => intro regs; rfl
  | cons ins' rp ih =>
    intro regs
    rw [rpSP, List.map_cons, rl_cons, ← rpSP, rlStep]
    simp only
    rw [getD_rStore_src C ins hins, getD_rStore_src C ins hins, set_rStore C ins hins, ih,
      RP.run_cons]

/-! ### The machine -/

/-- **A register program on the machine** (`rloopC`): from the store `C :: ins ++ C^(W − n)` and
the word `RP.rpW W rp`, `OUTW` ends with the register written last, the value of the unfolding
`RP.toSLP rp` at its wire, for any step `F` of a block. -/
theorem outw_rloopC {blk : Code} {S W : ℕ} {F : List Bool → List Bool → List Bool}
    {Ctx : St → Prop} (hB : BlockSpec V f blk S F Ctx) {C : List Bool} {ins : List (List Bool)}
    (hins : ins.length = n) (rp : RP (Fin n) W') (hW : n + W' ≤ W) (w : St)
    (hD : RegData S W C (C :: ins ++ List.replicate (W - n) C) (rpSP rp) w) (hc : Ctx w)
    (hG : w GST = (C :: ins ++ List.replicate (W - n) C).flatten) (hGS : w GS = RP.rpW W rp)
    (hN : (w GCNT).length = rp.length) {ins' : Instr (Fin n) W'} (hl : rp.getLast? = some ins') :
    exec V f (rloopC blk) w OUTW =
      SLP.valueOf (inpOf C ins) C F (RP.toSLP rp).1 ((RP.toSLP rp).2 ins'.dst) := by
  have hst : C :: ins ++ List.replicate (W - n) C = rStore C ins (fun _ : Fin W' => C) (W - n - W') := by
    rw [rStore, List.append_assoc, List.ofFn_const, ← List.replicate_add]
    congr 3; omega
  rw [hst] at hD hG
  obtain ⟨-, E2, -, -⟩ := exec_rloopC hB w hD hc hG (by rw [hGS, spW_rpSP])
    (by rw [hN, length_rpSP])
  have hl' : (rpSP rp).getLast? = some (RP.regSlot n ins'.dst, ins'.a.slot, ins'.b.slot) := by
    rw [rpSP, List.getLast?_map, hl]; rfl
  rw [E2 _ (by rw [hl']; rfl), rl_rpSP F C ins hins, ← RP.run_eq_valueOf]
  simp only [rStore, RP.regSlot, List.cons_append, List.append_assoc]
  rw [show n + 1 + ins'.dst.val = (ins'.dst.val + n) + 1 by omega, List.getD_cons_succ,
    List.getD_append_right _ _ _ _ (by omega), hins, Nat.add_sub_cancel,
    List.getD_append _ _ _ _ (by simp)]
  simp

theorem inpOf_map (C : List Bool) (g : Fin n → List Bool) :
    inpOf C ((List.finRange n).map g) = g := by
  funext i
  simp [inpOf, List.getD_eq_getElem?_getD]

/-- **The single gate**: `OUTW` ends with the value of the unfolding, for the step `f` itself. -/
theorem outw_rloopC_gate (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V)
    {W : ℕ} {one : List Bool} (h1 : one.length = V) {inp : Fin n → List Bool}
    (hin : ∀ i, (inp i).length = V) (rp : RP (Fin n) W') (hW : n + W' ≤ W) (w : St)
    (hD : RegData V W one (one :: (List.finRange n).map inp ++ List.replicate (W - n) one)
      (rpSP rp) w)
    (hG : w GST = (one :: (List.finRange n).map inp ++ List.replicate (W - n) one).flatten)
    (hGS : w GS = RP.rpW W rp) (hN : (w GCNT).length = rp.length) {ins' : Instr (Fin n) W'}
    (hl : rp.getLast? = some ins') :
    exec V f (rloopC (.gate RES IA IB)) w OUTW =
      SLP.valueOf inp one f (RP.toSLP rp).1 ((RP.toSLP rp).2 ins'.dst) := by
  rw [outw_rloopC (blockSpec_gate hf) (by simp) rp hW w hD trivial hG hGS hN hl, inpOf_map,
    valueOf_fV hf inp one hin h1]

/-- **`f̂` as a program**: its shadow is the value of the predicate's program on bundles, the step
the NAND block's shadow. -/
theorem fhatV_eq_valueOf {N k : ℕ} {A α : Type*} (one : α) (step : α → α → α)
    (inB : A → BI N k → α) (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (gv : OI N k → ℕ) (q : ℕ) (p : SLP A) (w : Wire A) :
    fhatV one step inB ordT ordO gv q p w = SLP.valueOf inB (constRepVV one (step one one) gv)
      (nandV one step ordT ordO gv (step one one) q) p w := by
  have hr : ∀ bs : List (BI N k → α), repV one inB (step one one) gv bs =
      SLP.wireVal inB (constRepVV one (step one one) gv) bs := by
    intro bs; funext w; cases w <;> rfl
  have key : ∀ (p : SLP A) (bs : List (BI N k → α)),
      p.foldl (compileStepV one step ordT ordO gv inB (step one one) q) bs =
        SLP.run inB (constRepVV one (step one one) gv)
          (nandV one step ordT ordO gv (step one one) q) p bs := by
    intro p
    induction p with
    | nil => intro bs; rfl
    | cons g p ih => intro bs; rw [List.foldl_cons, ih, compileStepV, hr]; rfl
  rw [fhatV, key, hr]; rfl

/-- The word of the constant bundle. -/
abbrev cstW (V : ℕ) (f : List Bool → List Bool → List Bool) (N K : ℕ) (one : List Bool) :
    List Bool := bw (N := N) (k := K + 1) (constRepVV one (fV V f one one) (gvExp (2 ^ K)))

/-- **The NAND block**: `OUTW` ends with the word of `fhatV` at the wire of the register written
last, for the input bundles `inB`. -/
theorem outw_rloopC_nand (hf : ∀ a b, a.length = V → b.length = V → (f a b).length = V)
    {N K W : ℕ} (hN : 0 < N) {one : List Bool} (h1 : one.length = V)
    {inB : Fin n → BI N (K + 1) → List Bool} (hin : ∀ i b, (inB i b).length = V)
    (rp : RP (Fin n) W') (hW : n + W' ≤ W) (w : St)
    (hD : RegData ((Enum.list (α := BI N (K + 1))).length * V) W
      (cstW V f N K one)
      (cstW V f N K one ::
        (List.finRange n).map (fun i => bw (inB i)) ++
        List.replicate (W - n) (cstW V f N K one))
      (rpSP rp) w)
    (hc : NCtx V K N one (fV V f one one) w)
    (hG : w GST = (cstW V f N K one ::
        (List.finRange n).map (fun i => bw (inB i)) ++
        List.replicate (W - n) (cstW V f N K one)).flatten)
    (hGS : w GS = RP.rpW W rp) (hN' : (w GCNT).length = rp.length) {ins' : Instr (Fin n) W'}
    (hl : rp.getLast? = some ins') :
    exec V f (rloopC nandC) w OUTW =
      bw (fhatV one (fV V f) inB (enumT N (K + 1)) (enumO N (K + 1)) (gvExp (2 ^ K)) (2 ^ K)
        (RP.toSLP rp).1 ((RP.toSLP rp).2 ins'.dst)) := by
  set zv := fV V f one one with hzv
  have hz : zv.length = V := by rw [hzv, fV]; exact hf _ _ (by simp) (by simp)
  set cst := constRepVV (N := N) (k := K + 1) one zv (gvExp (2 ^ K)) with hcst
  rw [outw_rloopC (blockSpec_nandC hf hN one zv h1 hz) (by simp) rp hW w hD hc hG hGS hN' hl,
    inpOf_map, ← RP.run_eq_valueOf]
  have hm := RP_run_map (fun A : BI N (K + 1) → List Bool => ∀ b, (A b).length = V) bw inB cst
    (nandV one (fV V f) (enumT N (K + 1)) (enumO N (K + 1)) (gvExp (2 ^ K)) zv (2 ^ K))
    (fun i => bw (inB i)) (bw cst) (nandW V N K f one zv) (fun _ => rfl) rfl
    (fun A B hA hB => by rw [nandW, ubw_bw hA, ubw_bw hB])
    (fun A B hA hB => nandV_len hf h1 hz _ _ hA hB) (fun i => hin i)
    (constRepVV_len one zv h1 hz _) rp (fun _ => cst) (fun _ => constRepVV_len one zv h1 hz _)
  have hm' := congrFun hm ins'.dst
  simp only [Function.comp_apply] at hm'
  rw [show (fun _ : Fin W' => bw cst) = bw ∘ (fun _ : Fin W' => cst) from rfl, hm',
    RP.run_eq_valueOf, fhatV_eq_valueOf]

end ValVM

end SigabaNeo.Tape
