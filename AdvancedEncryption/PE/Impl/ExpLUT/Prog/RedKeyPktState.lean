import PE.Impl.ExpLUT.Prog.RedKeyPktBridge

/-!
# The packet stream, part 9: the states of the branching program (generic `N K`)

The payloads of the step records are `X^{z_i}` and `X^{z_i + w x_i}` for the states `z_i` of
`bpOf (progOf C)` on the attribute. The walk keeps the state as a **unary** word (`swZu`):

* the symbol `x_i`: 8 bits (most significant first) popped from the attribute stream `swA`, Horner
  in unary (`swSymC`, `swAu`);
* `u_i = z_i + 2^{14} x_i` (`swUu`; `swT14` unary `2^{14}`);
* `X^{z_i}`, `X^{u_i}` by `rho` on the word `swOne` with the counts `2N − z_i`, `2N − u_i`
  (`swT2N` unary `2N`), appended to `swQZ`, `swQU`;
* the next state: the `14` bits at `14 u_i` of the current table (`swCcur`, advanced by `swTtab`
  per step), converted to unary by doubling (`swUnaryC`).

**`exec_swLoopC`**: `swQZ`, `swQU` end with the words of the `16` payload pairs of the states
`swSt C xs` (`swSt C xs (i + 1) = val (takeD 14 (C.drop (tl i + 14 u_i)))`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyPkt

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo.NegaG
open SigabaNeo.Lattices.Algo (encRM val toBits)
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

/-! ### Registers (before the slab loops; all scratch) -/

@[simp, vmreg] abbrev swA : Fin 64 := 32
@[simp, vmreg] abbrev swBit : Fin 64 := 33
@[simp, vmreg] abbrev swAu : Fin 64 := 34
@[simp, vmreg] abbrev swZu : Fin 64 := 35
@[simp, vmreg] abbrev swUu : Fin 64 := 36
@[simp, vmreg] abbrev swT14 : Fin 64 := 37
@[simp, vmreg] abbrev swT2N : Fin 64 := 39
@[simp, vmreg] abbrev swR : Fin 64 := 40
@[simp, vmreg] abbrev swOne : Fin 64 := 41
@[simp, vmreg] abbrev swQZ : Fin 64 := 42
@[simp, vmreg] abbrev swQU : Fin 64 := 43
@[simp, vmreg] abbrev swCcur : Fin 64 := 44
@[simp, vmreg] abbrev swTtab : Fin 64 := 45
@[simp, vmreg] abbrev swT : Fin 64 := 46
@[simp, vmreg] abbrev swT14b : Fin 64 := 47
@[simp, vmreg] abbrev swZb : Fin 64 := 48
@[simp, vmreg] abbrev swW : Fin 64 := 49
@[simp, vmreg] abbrev swCnt : Fin 64 := 50
@[simp, vmreg] abbrev swT8 : Fin 64 := 51
@[simp, vmreg] abbrev swB1 : Fin 64 := 52
@[simp, vmreg] abbrev swP : Fin 64 := 53
@[simp, vmreg] abbrev swLoop : Fin 64 := 54
@[simp, vmreg] abbrev swT16 : Fin 64 := 55

/-! ### Horner in unary -/

/-- The value of bits, most significant first. -/
def hornerB : List Bool → ℕ → ℕ
  | [], v => v
  | b :: l, v => hornerB l (2 * v + b.toNat)

/-- The round: `Au := 2 Au + bit`. -/
def swSymBody : Code :=
  .seq (.app swAu swAu) <| .seq (.cp swBit swB1) <| .seq (.mv swBit swA swB1)
    (.ifb swBit (.app swAu swB1) .nop)

/-- **`Au :=` the value of the next `|swT8|` bits of `swA`** (most significant first). -/
def swSymC : Code := .seq (.clr swAu) (.seq (.cp swCnt swT8) (.rep swCnt swSymBody))

theorem exec_swSymBody {N K : ℕ} (w : St) (v : ℕ) (b : Bool) (L : List Bool)
    (hAu : w swAu = List.replicate v false) (hA : w swA = b :: L) (hB1 : w swB1 = [false]) :
    exec N K swSymBody w swAu = List.replicate (2 * v + b.toNat) false ∧
      exec N K swSymBody w swA = L ∧
      ∀ r, r ≠ swAu → r ≠ swBit → r ≠ swA → exec N K swSymBody w r = w r := by
  have e1 : exec N K (.mv swBit swA swB1) (exec N K (.cp swBit swB1) (exec N K (.app swAu swAu) w)) =
      Function.update (Function.update (Function.update w swAu (w swAu ++ w swAu)) swA L) swBit [b] := by
    simp only [exec_mv, exec_cp, exec_app]
    rw [if_neg (by decide)]
    simp only [Function.update_apply, show (swB1 : Fin 64) ≠ swBit by decide,
      show (swB1 : Fin 64) ≠ swAu by decide, show (swA : Fin 64) ≠ swBit by decide,
      show (swA : Fin 64) ≠ swAu by decide, if_true, if_false, hB1, hA, List.length_singleton]
    funext r
    simp only [Function.update_apply]
    split_ifs <;> simp_all [ValVM.shiftIn, takeD]
  have hE : exec N K swSymBody w = exec N K (.ifb swBit (.app swAu swB1) .nop)
      (Function.update (Function.update (Function.update w swAu (w swAu ++ w swAu)) swA L) swBit [b]) := by
    rw [← e1]; rfl
  rw [hE]
  cases b
  · simp only [exec_ifb, Function.update_self, hd_cons, Bool.false_eq_true, if_false, exec_nop]
    refine ⟨?_, ?_, ?_⟩
    · simp only [Function.update_apply, show (swAu : Fin 64) ≠ swBit by decide,
        show (swAu : Fin 64) ≠ swA by decide, if_false, if_true, hAu, ← List.replicate_add]
      congr 1; simp; ring
    · simp [Function.update_apply]
    · intro r h1 h2 h3; simp [Function.update_apply, h1, h2, h3]
  · simp only [exec_ifb, Function.update_self, hd_cons, if_true, exec_app]
    refine ⟨?_, ?_, ?_⟩
    · simp only [Function.update_apply, show (swAu : Fin 64) ≠ swBit by decide,
        show (swAu : Fin 64) ≠ swA by decide, show (swB1 : Fin 64) ≠ swBit by decide,
        show (swB1 : Fin 64) ≠ swA by decide, show (swB1 : Fin 64) ≠ swAu by decide, if_false,
        if_true, hAu, hB1, ← List.replicate_add]
      rw [← List.replicate_succ']
      congr 1; simp; ring
    · simp [Function.update_apply]
    · intro r h1 h2 h3; simp [Function.update_apply, h1, h2, h3]

theorem hornerB_append (l : List Bool) (b : Bool) (v : ℕ) :
    hornerB (l ++ [b]) v = 2 * hornerB l v + b.toNat := by
  induction l generalizing v with
  | nil => rfl
  | cons a l ih => exact ih _

theorem exec_swSymC {N K : ℕ} (w : St) (bits L : List Bool) (hA : w swA = bits ++ L)
    (hn : (w swT8).length = bits.length) (hB1 : w swB1 = [false]) :
    exec N K swSymC w swAu = List.replicate (hornerB bits 0) false ∧ exec N K swSymC w swA = L ∧
      ∀ r, r ≠ swAu → r ≠ swBit → r ≠ swA → r ≠ swCnt → exec N K swSymC w r = w r := by
  set w1 := exec N K (.cp swCnt swT8) (exec N K (.clr swAu) w) with hw1
  have hc : (w1 swCnt).length = bits.length := by simp [hw1, hn]
  have key := exec_rep_inv2 (N := N) (K := K) swCnt swSymBody (by decide)
    (fun j v => v swAu = List.replicate (hornerB (bits.take j) 0) false ∧
      v swA = bits.drop j ++ L) w1
    ⟨by simp [hw1, hornerB], by simp [hw1, Function.update_apply, hA]⟩
    (by
      intro j v hj hP _ hfr
      rw [hc] at hj
      obtain ⟨h1, h2⟩ := hP
      have hcons : bits.drop j ++ L = bits[j] :: (bits.drop (j + 1) ++ L) := by
        rw [List.drop_eq_getElem_cons hj]; rfl
      obtain ⟨e1, e2, -⟩ := exec_swSymBody (N := N) (K := K) (Function.update v swCnt (v swCnt).tail)
        _ bits[j] _ (by rw [Function.update_of_ne (by decide)]; exact h1)
        (by rw [Function.update_of_ne (by decide), h2, hcons])
        (by rw [Function.update_of_ne (by decide), hfr _ (by decide) (by decide), hw1]; simp [hB1])
      have ht : bits.take (j + 1) = bits.take j ++ [bits[j]] := by
        rw [List.take_succ, List.getElem?_eq_getElem hj]; rfl
      refine ⟨by rw [e1, ht, hornerB_append], e2⟩)
  rw [hc, List.take_length, List.drop_length, List.nil_append] at key
  refine ⟨key.1, key.2, fun r h1 h2 h3 h4 => ?_⟩
  show exec N K (.rep swCnt swSymBody) w1 r = w r
  rw [exec_writes _ _ r (by simp [Code.writes, swSymBody, Ne.symm h1, Ne.symm h2, Ne.symm h3,
    Ne.symm h4])]
  simp [hw1, Function.update_apply, h1, h4]

/-! ### Bits to unary -/

/-- The round: `Zu += W` if the bit, drop the bit, `W := 2 W`. -/
def swUnaryBody : Code := .seq (.ifb swZb (.app swZu swW) .nop) (.seq (.tl swZb) (.app swW swW))

/-- **`Zu :=` the value of the `|swT14b|` bits of `swZb`** (least significant first). -/
def swUnaryC : Code := .seq (.clr swZu) (.seq (.cp swW swB1) (.seq (.cp swCnt swT14b)
  (.rep swCnt swUnaryBody)))

theorem exec_swUnaryC {N K : ℕ} (w : St) (bits : List Bool) (hZb : w swZb = bits)
    (hn : (w swT14b).length = bits.length) (hB1 : w swB1 = [false]) :
    exec N K swUnaryC w swZu = List.replicate (val bits) false ∧
      ∀ r, r ≠ swZu → r ≠ swW → r ≠ swCnt → r ≠ swZb → exec N K swUnaryC w r = w r := by
  set w1 := exec N K (.cp swCnt swT14b) (exec N K (.cp swW swB1) (exec N K (.clr swZu) w)) with hw1
  have hc : (w1 swCnt).length = bits.length := by simp [hw1, hn]
  have key := exec_rep_inv2 (N := N) (K := K) swCnt swUnaryBody (by decide)
    (fun j v => v swZu = List.replicate (val (bits.take j)) false ∧
      v swW = List.replicate (2 ^ j) false ∧ v swZb = bits.drop j) w1
    ⟨by simp [hw1, Function.update_apply], by simp [hw1, Function.update_apply, hB1],
     by simp [hw1, Function.update_apply, hZb]⟩
    (by
      intro j v hj hP _ _
      rw [hc] at hj
      obtain ⟨h1, h2, h3⟩ := hP
      set vv := Function.update v swCnt (v swCnt).tail
      have hd : hd (vv swZb) = bits[j] := by
        simp only [vv, Function.update_apply, show (swZb : Fin 64) ≠ swCnt by decide, if_false, h3]
        rw [List.drop_eq_getElem_cons hj]; rfl
      have ht : bits.take (j + 1) = bits.take j ++ [bits[j]] := by
        rw [List.take_succ, List.getElem?_eq_getElem hj]; rfl
      have hval : val (bits.take (j + 1)) = val (bits.take j) + 2 ^ j * bits[j].toNat := by
        rw [ht, SigabaNeo.Lattices.Algo.val_append, List.length_take, Nat.min_eq_left hj.le]
        simp
      have hW : List.replicate (2 ^ j) false ++ List.replicate (2 ^ j) false =
          List.replicate (2 ^ (j + 1)) false := by
        rw [← List.replicate_add, pow_succ, mul_two]
      simp only [swUnaryBody, exec_seq, exec_ifb, hd]
      cases hb : bits[j]
      · simp only [Bool.false_eq_true, if_false, exec_nop, exec_tl, exec_app]
        refine ⟨?_, ?_, ?_⟩
        · simp only [Function.update_apply, vv, show (swZu : Fin 64) ≠ swW by decide,
            show (swZu : Fin 64) ≠ swZb by decide, show (swZu : Fin 64) ≠ swCnt by decide, if_false,
            h1, hval, hb]
          simp
        · simp only [Function.update_apply, vv, show (swW : Fin 64) ≠ swZb by decide,
            show (swW : Fin 64) ≠ swCnt by decide, if_false, if_true, h2, hW]
        · simp only [Function.update_apply, vv, show (swZb : Fin 64) ≠ swW by decide,
            show (swZb : Fin 64) ≠ swCnt by decide, if_false, if_true, h3, List.tail_drop]
      · simp only [if_true, exec_tl, exec_app]
        refine ⟨?_, ?_, ?_⟩
        · simp only [Function.update_apply, vv, show (swZu : Fin 64) ≠ swW by decide,
            show (swZu : Fin 64) ≠ swZb by decide, show (swZu : Fin 64) ≠ swCnt by decide,
            show (swW : Fin 64) ≠ swCnt by decide, if_false, if_true, h1, h2, hval, hb,
            ← List.replicate_add]
          simp
        · simp only [Function.update_apply, vv, show (swW : Fin 64) ≠ swZb by decide,
            show (swW : Fin 64) ≠ swZu by decide, show (swW : Fin 64) ≠ swCnt by decide,
            if_false, if_true, h2, hW]
        · simp only [Function.update_apply, vv, show (swZb : Fin 64) ≠ swW by decide,
            show (swZb : Fin 64) ≠ swZu by decide, show (swZb : Fin 64) ≠ swCnt by decide,
            if_false, if_true, h3, List.tail_drop])
  rw [hc, List.take_length] at key
  refine ⟨key.1, fun r h1 h2 h3 h4 => ?_⟩
  show exec N K (.rep swCnt swUnaryBody) w1 r = w r
  rw [exec_writes _ _ r (by simp [Code.writes, swUnaryBody, Ne.symm h1, Ne.symm h2, Ne.symm h3,
    Ne.symm h4])]
  simp [hw1, Function.update_apply, h1, h2, h3]

/-! ### One step of the walk -/

/-- `Uu := Zu ++ Au^{|swT14|}`. -/
def swUC : Code := .seq (.cp swUu swZu) (.seq (.cp swCnt swT14) (.rep swCnt (.app swUu swAu)))

/-- `q ++= X^{−(2N − |e|)} One` for the unary exponent `e`. -/
def swMonoC (e q : Fin 64) : Code :=
  .seq (.cp swR swT2N) <| .seq (.drop swR e) <| .seq (.op .rho swP swOne swR) (.app q swP)

/-- `Zb :=` the `14` bits at `14 |Uu|` of the current table. -/
def swReadC : Code :=
  .seq (.cp swT swCcur) <| .seq (.cp swCnt swT14b) <| .seq (.rep swCnt (.drop swT swUu)) <|
  .seq (.cp swZb swT14b) (.mv swZb swT swT14b)

/-- **One step of the walk.** -/
def swStepC : Code :=
  .seq swSymC <| .seq swUC <| .seq (swMonoC swZu swQZ) <| .seq (swMonoC swUu swQU) <|
  .seq swReadC <| .seq swUnaryC (.drop swCcur swTtab)

/-- The registers of the walk's constants. -/
def swConstR (r : Fin 64) : Bool :=
  r == swT8 || r == swT14 || r == swT2N || r == swOne || r == swT14b || r == swTtab || r == swB1

/-- The constants of the walk. -/
structure SwConst (N K tl : ℕ) (O : List Bool) (w : St) : Prop where
  t8 : (w swT8).length = 8
  t14 : (w swT14).length = 2 ^ 14
  t2N : w swT2N = List.replicate (2 * N) false
  one : w swOne = O
  t14b : (w swT14b).length = 14
  ttab : (w swTtab).length = tl
  b1 : w swB1 = [false]

theorem SwConst.of_frame {N K tl : ℕ} {O : List Bool} {w w' : St} (h : SwConst N K tl O w)
    (hw : ∀ r, swConstR r = true → w' r = w r) : SwConst N K tl O w' :=
  ⟨by rw [hw _ rfl]; exact h.t8, by rw [hw _ rfl]; exact h.t14, by rw [hw _ rfl]; exact h.t2N,
   by rw [hw _ rfl]; exact h.one, by rw [hw _ rfl]; exact h.t14b, by rw [hw _ rfl]; exact h.ttab,
   by rw [hw _ rfl]; exact h.b1⟩

/-- The word of `X^{−(2N − e)} O`. -/
def swMonoW (N K e : ℕ) (O : List Bool) : List Bool :=
  canonW N K ((rhoMW K)^[2 * N - e] (takeD (N * K) O))

theorem swStepC_writes : ∀ r : Fin 64, swConstR r = true ∨ r = swLoop → swStepC.writes r = false := by
  decide

theorem exec_rep_drop {N K : ℕ} (c t e : Fin 64) (hct : c ≠ t) (hce : c ≠ e) (hte : t ≠ e) (w : St) :
    exec N K (.rep c (.drop t e)) w t = (w t).drop ((w c).length * (w e).length) := by
  have key := exec_rep_inv2 (N := N) (K := K) c (.drop t e) (by simp [Code.writes, Ne.symm hct])
    (fun j v => v t = (w t).drop (j * (w e).length)) w (by simp)
    (fun j v _ hP _ hfr => by
      simp only [exec_drop, if_neg hte, Function.update_self]
      rw [Function.update_of_ne (Ne.symm hce), Function.update_of_ne (Ne.symm hct), hP,
        hfr e (by simp [Code.writes, hte]) (Ne.symm hce), List.drop_drop]
      congr 1; ring)
  exact key

theorem exec_rep_app {N K : ℕ} (c d s : Fin 64) (hcd : c ≠ d) (hcs : c ≠ s) (hds : d ≠ s) (w : St) :
    exec N K (.rep c (.app d s)) w d = w d ++ (List.replicate (w c).length (w s)).flatten :=
  exec_repAppC c d s hcd hcs hds w

theorem flatten_replicate_false (n m : ℕ) :
    (List.replicate n (List.replicate m false)).flatten = List.replicate (n * m) false := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, ih, ← List.replicate_add]; congr 1; ring

theorem exec_swMonoC {N K : ℕ} (e q : Fin 64) (he : e ≠ swR ∧ e ≠ swP ∧ e ≠ swT2N)
    (hq : q ≠ swR ∧ q ≠ swP ∧ q ≠ swOne ∧ q ≠ swT2N) (w : St) (n : ℕ)
    (hT : w swT2N = List.replicate (2 * N) false) (hE : w e = List.replicate n false) :
    exec N K (swMonoC e q) w q = w q ++ swMonoW N K n (w swOne) ∧
      ∀ r, r ≠ swR → r ≠ swP → r ≠ q → exec N K (swMonoC e q) w r = w r := by
  obtain ⟨he1, he2, he3⟩ := he
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hq
  simp only [swMonoC, exec_seq, exec_cp, exec_drop, exec_rho, exec_app,
    if_neg (show (swR : Fin 64) ≠ e from Ne.symm he1)]
  refine ⟨?_, fun r h1 h2 h3 => by simp [Function.update_apply, h1, h2, h3]⟩
  simp only [Function.update_self, Function.update_apply, if_neg hq1, if_neg hq2,
    show (swP : Fin 64) ≠ swR by decide, show (swOne : Fin 64) ≠ swR by decide, if_neg he1,
    if_true, if_false, hT, hE, List.length_replicate, List.length_drop]
  rfl

theorem exec_swReadC {N K : ℕ} (w : St) (u : ℕ) (hU : w swUu = List.replicate u false)
    (h14 : (w swT14b).length = 14) :
    exec N K swReadC w swZb = takeD 14 ((w swCcur).drop (14 * u)) ∧
      ∀ r, r ≠ swT → r ≠ swCnt → r ≠ swZb → exec N K swReadC w r = w r := by
  have e3 := exec_rep_drop (N := N) (K := K) swCnt swT swUu (by decide) (by decide) (by decide)
    (exec N K (.cp swCnt swT14b) (exec N K (.cp swT swCcur) w))
  set v := exec N K (.rep swCnt (.drop swT swUu)) (exec N K (.cp swCnt swT14b)
    (exec N K (.cp swT swCcur) w)) with hv
  have vT : v swT = (w swCcur).drop (14 * u) := by
    rw [e3]; simp [Function.update_apply, hU, h14]
  have vfr : ∀ r, r ≠ swT → r ≠ swCnt → v r = w r := by
    intro r h1 h2
    rw [hv, exec_writes _ _ r (by simp [Code.writes, Ne.symm h1, Ne.symm h2])]
    simp [Function.update_apply, h1, h2]
  have hE : exec N K swReadC w = exec N K (.mv swZb swT swT14b) (exec N K (.cp swZb swT14b) v) := rfl
  rw [hE]
  simp only [exec_mv, exec_cp, if_neg (show ¬((swZb : Fin 64) = swT ∨ swZb = swT14b ∨ swT = swT14b) by decide)]
  refine ⟨?_, fun r h1 h2 h3 => ?_⟩
  · simp only [Function.update_self, Function.update_apply, show (swT14b : Fin 64) ≠ swZb by decide,
      show (swT : Fin 64) ≠ swZb by decide, if_false]
    rw [vT, vfr _ (by decide) (by decide), h14]
    unfold ValVM.shiftIn
    rw [List.drop_left' (by simpa using h14)]
  · simp only [Function.update_apply, h1, h3, if_false]
    exact vfr r h1 h2

/-- **One step**: from the state `z` (unary in `swZu`) and the symbol bits `bits` at the head of
`swA`. -/
theorem exec_swStepC {N K tl : ℕ} {O : List Bool} (w : St) (hc : SwConst N K tl O w)
    (z : ℕ) (hz : w swZu = List.replicate z false) (bits L : List Bool) (hb : bits.length = 8)
    (hA : w swA = bits ++ L) (Cc qz qu : List Bool) (hC : w swCcur = Cc) (hqz : w swQZ = qz)
    (hqu : w swQU = qu) :
    let w' := exec N K swStepC w
    let u := z + 2 ^ 14 * hornerB bits 0
    w' swZu = List.replicate (val (takeD 14 (Cc.drop (14 * u)))) false ∧ w' swA = L ∧
      w' swCcur = Cc.drop tl ∧ w' swQZ = qz ++ swMonoW N K z O ∧
      w' swQU = qu ++ swMonoW N K u O ∧ SwConst N K tl O w' := by
  intro w' u
  have hconst : SwConst N K tl O w' :=
    hc.of_frame fun r hr => exec_writes _ _ r (swStepC_writes r (Or.inl hr))
  -- the symbol
  obtain ⟨a1, a2, a3⟩ := exec_swSymC (N := N) (K := K) w bits L hA (by rw [hc.t8, hb]) hc.b1
  set w1 := exec N K swSymC w with hw1
  have c1 : SwConst N K tl O w1 := hc.of_frame fun r hr => a3 r (by revert hr; revert r; decide)
    (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)
  -- `Uu`
  set w2 := exec N K swUC w1 with hw2
  have f2 : ∀ r, r ≠ swUu → r ≠ swCnt → w2 r = w1 r := by
    intro r h1 h2
    rw [hw2, exec_writes _ _ r (by simp [swUC, Code.writes, Ne.symm h1, Ne.symm h2])]
  have e2 : w2 swUu = List.replicate u false := by
    rw [hw2, swUC, exec_seq, exec_seq, exec_rep_app _ _ _ (by decide) (by decide) (by decide)]
    simp only [exec_cp, Function.update_self, Function.update_apply,
      show (swUu : Fin 64) ≠ swCnt by decide, show (swAu : Fin 64) ≠ swCnt by decide,
      show (swAu : Fin 64) ≠ swUu by decide, show (swT14 : Fin 64) ≠ swUu by decide, if_false]
    rw [a1, a3 _ (by decide) (by decide) (by decide) (by decide), hz, c1.t14,
      flatten_replicate_false, ← List.replicate_add]
  have c2 : SwConst N K tl O w2 := c1.of_frame fun r hr => f2 r (by revert hr; revert r; decide)
    (by revert hr; revert r; decide)
  -- the monomials
  obtain ⟨m1, m2⟩ := exec_swMonoC (N := N) (K := K) swZu swQZ (by decide) (by decide) w2 z c2.t2N
    (by rw [f2 _ (by decide) (by decide), a3 _ (by decide) (by decide) (by decide) (by decide), hz])
  set w3 := exec N K (swMonoC swZu swQZ) w2 with hw3
  have c3 : SwConst N K tl O w3 := c2.of_frame fun r hr => m2 r (by revert hr; revert r; decide)
    (by revert hr; revert r; decide) (by revert hr; revert r; decide)
  obtain ⟨n1, n2⟩ := exec_swMonoC (N := N) (K := K) swUu swQU (by decide) (by decide) w3 u c3.t2N
    (by rw [m2 _ (by decide) (by decide) (by decide), e2])
  set w4 := exec N K (swMonoC swUu swQU) w3 with hw4
  have c4 : SwConst N K tl O w4 := c3.of_frame fun r hr => n2 r (by revert hr; revert r; decide)
    (by revert hr; revert r; decide) (by revert hr; revert r; decide)
  -- the next state
  obtain ⟨r1, r2⟩ := exec_swReadC (N := N) (K := K) w4 u
    (by rw [n2 _ (by decide) (by decide) (by decide), m2 _ (by decide) (by decide) (by decide), e2])
    c4.t14b
  set w5 := exec N K swReadC w4 with hw5
  have c5 : SwConst N K tl O w5 := c4.of_frame fun r hr => r2 r (by revert hr; revert r; decide)
    (by revert hr; revert r; decide) (by revert hr; revert r; decide)
  obtain ⟨u1, u2⟩ := exec_swUnaryC (N := N) (K := K) w5 _ r1 (by rw [c5.t14b, length_takeD]) c5.b1
  set w6 := exec N K swUnaryC w5 with hw6
  have hw' : w' = exec N K (.drop swCcur swTtab) w6 := rfl
  -- frames
  have fCc : w4 swCcur = Cc := by
    rw [n2 _ (by decide) (by decide) (by decide), m2 _ (by decide) (by decide) (by decide),
      f2 _ (by decide) (by decide), a3 _ (by decide) (by decide) (by decide) (by decide), hC]
  rw [fCc] at r1 u1
  refine ⟨?_, ?_, ?_, ?_, ?_, hconst⟩
  · rw [hw', exec_drop, if_neg (by decide), Function.update_of_ne (by decide), u1]
  · rw [hw', exec_drop, if_neg (by decide), Function.update_of_ne (by decide),
      u2 _ (by decide) (by decide) (by decide) (by decide),
      r2 _ (by decide) (by decide) (by decide), n2 _ (by decide) (by decide) (by decide),
      m2 _ (by decide) (by decide) (by decide), f2 _ (by decide) (by decide), a2]
  · have c6 : SwConst N K tl O w6 := c5.of_frame fun r hr => u2 r (by revert hr; revert r; decide)
      (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)
    rw [hw', exec_drop, if_neg (by decide), Function.update_self, c6.ttab,
      u2 swCcur (by decide) (by decide) (by decide) (by decide),
      r2 swCcur (by decide) (by decide) (by decide), fCc]
  · rw [hw', exec_drop, if_neg (by decide), Function.update_of_ne (by decide),
      u2 _ (by decide) (by decide) (by decide) (by decide),
      r2 _ (by decide) (by decide) (by decide), n2 _ (by decide) (by decide) (by decide), m1,
      f2 _ (by decide) (by decide), a3 _ (by decide) (by decide) (by decide) (by decide), hqz,
      c2.one]
  · rw [hw', exec_drop, if_neg (by decide), Function.update_of_ne (by decide),
      u2 _ (by decide) (by decide) (by decide) (by decide),
      r2 _ (by decide) (by decide) (by decide), n1, m2 _ (by decide) (by decide) (by decide),
      f2 _ (by decide) (by decide), a3 _ (by decide) (by decide) (by decide) (by decide), hqu,
      c3.one]

/-! ### The walk -/

/-- The states of the walk (`tl` bits per table). -/
def swSt (C : List Bool) (tl : ℕ) (xs : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => val (takeD 14 ((C.drop (tl * i)).drop (14 * (swSt C tl xs i + 2 ^ 14 * xs i))))

/-- **The walk**: `16` steps. -/
def swLoopC : Code :=
  .seq (.clr swZu) <| .seq (.clr swQZ) <| .seq (.clr swQU) <| .seq (.cp swLoop swT16)
    (.rep swLoop swStepC)

theorem exec_swLoopC {N K tl : ℕ} {O : List Bool} (w : St) (hc : SwConst N K tl O w)
    (blk : ℕ → List Bool) (hblk : ∀ i, (blk i).length = 8) (L C : List Bool)
    (hA : w swA = (List.range 16).flatMap blk ++ L) (hC : w swCcur = C)
    (h16 : (w swT16).length = 16) :
    let w' := exec N K swLoopC w
    let xs := fun i => hornerB (blk i) 0
    w' swQZ = (List.range 16).flatMap (fun i => swMonoW N K (swSt C tl xs i) O) ∧
      w' swQU = (List.range 16).flatMap (fun i => swMonoW N K (swSt C tl xs i + 2 ^ 14 * xs i) O) ∧
      ∀ r, swLoopC.writes r = false → w' r = w r := by
  intro w' xs
  set w1 := exec N K (.cp swLoop swT16) (exec N K (.clr swQU) (exec N K (.clr swQZ)
    (exec N K (.clr swZu) w))) with hw1
  have f1 : ∀ r, r ≠ swLoop → r ≠ swQU → r ≠ swQZ → r ≠ swZu → w1 r = w r := by
    intro r a b c d; simp [hw1, Function.update_apply, a, b, c, d]
  have hcnt : (w1 swLoop).length = 16 := by simp [hw1, h16]
  have key := exec_rep_inv2 (N := N) (K := K) swLoop swStepC (swStepC_writes _ (Or.inr rfl))
    (fun i v => v swZu = List.replicate (swSt C tl xs i) false ∧
      v swA = (List.range' i (16 - i)).flatMap blk ++ L ∧ v swCcur = C.drop (tl * i) ∧
      v swQZ = (List.range i).flatMap (fun i => swMonoW N K (swSt C tl xs i) O) ∧
      v swQU = (List.range i).flatMap (fun i => swMonoW N K (swSt C tl xs i + 2 ^ 14 * xs i) O) ∧
      SwConst N K tl O v) w1
    ⟨by simp [hw1, Function.update_apply, swSt],
     by rw [f1 _ (by decide) (by decide) (by decide) (by decide), hA, List.range_eq_range'],
     by rw [f1 _ (by decide) (by decide) (by decide) (by decide), hC]; simp,
     by simp [hw1, Function.update_apply], by simp [hw1, Function.update_apply],
     hc.of_frame fun r hr => f1 r (by revert hr; revert r; decide) (by revert hr; revert r; decide)
       (by revert hr; revert r; decide) (by revert hr; revert r; decide)⟩
    (by
      intro i v hi hP _ _
      rw [hcnt] at hi
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP
      set vv := Function.update v swLoop (v swLoop).tail
      have hvv : ∀ r, r ≠ swLoop → vv r = v r := fun r h => Function.update_of_ne h _ _
      obtain ⟨k, hk⟩ : ∃ k, 16 - i = k + 1 := ⟨16 - i - 1, by omega⟩
      have hA' : vv swA = blk i ++ ((List.range' (i + 1) (16 - (i + 1))).flatMap blk ++ L) := by
        rw [hvv _ (by decide), h2, hk, range'_flatMap_cons, List.append_assoc,
          show 16 - (i + 1) = k by omega]
      obtain ⟨s1, s2, s3, s4, s5, s6⟩ := exec_swStepC (N := N) (K := K) vv
        (h6.of_frame fun r hr => hvv r (by revert hr; revert r; decide)) (swSt C tl xs i)
        (by rw [hvv _ (by decide), h1]) (blk i) _ (hblk i) hA' _ _ _
        (by rw [hvv _ (by decide), h3]) (by rw [hvv _ (by decide), h4])
        (by rw [hvv _ (by decide), h5])
      refine ⟨by rw [s1]; rfl, s2, by rw [s3, List.drop_drop]; congr 1, ?_, ?_, s6⟩
      · rw [s4, List.range_succ, List.flatMap_append]; simp
      · rw [s5, List.range_succ, List.flatMap_append]; simp; rfl)
  rw [hcnt] at key
  obtain ⟨-, -, -, k4, k5, -⟩ := key
  refine ⟨k4, k5, fun r hr => ?_⟩
  exact exec_writes _ _ r hr

end AdvancedEncryption.ExpLUT.Prog.RedKeyPkt
