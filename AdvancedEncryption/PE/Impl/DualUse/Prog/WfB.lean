import PE.Impl.DualUse.Prog.WfIns
import SigabaNeo.Lib.Lattices.ProgAlgo.KeySumT

/-!
# The `W_f` block of the key component

`wfB gen W : XProg 256` writes the word of `W_f = simW sd C` (`WfSpec`,
`PE.Impl.DualUse.Prog.KeyP`) from `sdEnc sd` (tape `0`) and the gate list `gsW W (parse C)` of a
window predicate (tape `1`):

1. the **`f̂` gate generator** `gen : XProg 136` (a parameter, `GenSpec`), framed by `eG` (its tapes
   `0 1 2 3` on `1 233 234 4`): from `gsW W gs` the gate stream
   `gatesW ixT nT W (fhatProg K (ordT₀ N k) (ordO₀ N k) gs).1 0` of the simulation of `f̂`, a gate
   counter and the positions `posW W N k (fhatPos …)` of the output wires of `f̂`;
2. the predicate's gate stream, counter and output position (`convP`, `PE.Impl.DualUse.Prog.WfPred`,
   on `1 244 245 89`);
3. the input stores of the two simulations (`insTP`, `insGP`, `PE.Impl.DualUse.Prog.WfIns`, on
   `232` and `246`);
4. the templates of the simulation of `f̂` (`tmplWT`), the evaluator `slpEvalP uE vE (simStepP
   ginvTopP)` (`run_slpSim`, store on `232`), its store moved to `3`;
5. the templates of the Ring-GSW simulation (`tmplWG`), the evaluator `slpEvalP uE vE (simStepP
   ginvGswP)`, its store moved to `88`;
6. the templates of the key sum (`tmplWK`) and `simKeyP` on the tapes `2 … 95` (`oK`), which writes
   the word of `W_f` on tape `2` (`run_simKeyP_sd`);
7. every tape but `0` and `2` cleared.

The steps after the generator form one coin-free `Prog 256` (`wfRest`).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.Prog Matrix AdvancedEncryption.RingBTVW AdvancedEncryption.DualUse.Algo
  Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord
open scoped SigabaNeo.Tape.Prog

set_option linter.unusedSimpArgs false

/-! ### Generic pieces -/

/-- Put constant words on tapes, in order. -/
def putsP {k : ℕ} [NeZero k] : List (Fin k × List Bool) → Prog k
  | [] => nop 0
  | x :: l => SigabaNeo.Tape.Prog.putW x.1 x.2 ⨾ putsP l

/-- The store after `putsP`. -/
def putsS {k : ℕ} (l : List (Fin k × List Bool)) (s : Store k) : Store k :=
  l.foldl (fun s x => Function.update s x.1 x.2) s

theorem run_putsP {k : ℕ} [NeZero k] : ∀ (l : List (Fin k × List Bool)) (s : Store k),
    run (putsP l) s = putsS l s
  | [], s => by simp [putsP, putsS]
  | x :: l, s => by
    rw [putsP, run_seq, SigabaNeo.Tape.Prog.run_putW, run_putsP l]
    rfl

theorem putsS_cons {k : ℕ} (x : Fin k × List Bool) (l : List (Fin k × List Bool)) (s : Store k) :
    putsS (x :: l) s = putsS l (Function.update s x.1 x.2) := rfl

theorem putsS_nil {k : ℕ} (s : Store k) : putsS [] s = s := rfl

theorem coinFree_putsP {k : ℕ} [NeZero k] : ∀ l : List (Fin k × List Bool), (putsP l).CoinFree
  | [] => rfl
  | x :: l => by
    have h1 := SigabaNeo.Tape.Prog.coinFree_putW x.1 x.2
    have h2 := coinFree_putsP l
    simp only [CoinFree] at h1 h2
    simp [CoinFree, putsP, coinFreeB, h1, h2]

theorem wf_putsP {k : ℕ} [NeZero k] : ∀ l : List (Fin k × List Bool), (putsP l).WF
  | [] => trivial
  | x :: l => ⟨SigabaNeo.Tape.Prog.wf_putW _ _, wf_putsP l⟩

/-- Clear tapes, in order. -/
def clrsP {k : ℕ} [NeZero k] : List (Fin k) → Prog k
  | [] => nop 0
  | t :: l => clr t ⨾ clrsP l

theorem run_clrsP {k : ℕ} [NeZero k] : ∀ (l : List (Fin k)) (s : Store k),
    run (clrsP l) s = fun t => if t ∈ l then [] else s t
  | [], s => by simp [clrsP]
  | x :: l, s => by
    rw [clrsP, run_seq, run_clear, run_clrsP l]
    funext t
    by_cases h : t = x
    · subst h; simp
    · simp [h, Function.update_of_ne h]

theorem coinFree_clrsP {k : ℕ} [NeZero k] : ∀ l : List (Fin k), (clrsP l).CoinFree
  | [] => rfl
  | x :: l => by
    have h2 := coinFree_clrsP l
    simp only [CoinFree] at h2
    simp [CoinFree, clrsP, coinFreeB, h2]

theorem wf_clrsP {k : ℕ} [NeZero k] : ∀ l : List (Fin k), (clrsP l).WF
  | [] => trivial
  | _ :: l => ⟨trivial, wf_clrsP l⟩

theorem coinFree_of_noGrow {k : ℕ} : ∀ p : Prog k, p.NoGrow → p.CoinFree
  | .prim _, _ => rfl
  | .coin _, h => absurd h (by simp [NoGrow, noGrowB])
  | .seq p q, h | .ifBlank _ p q, h | .ifBit _ p q, h => by
    simp only [NoGrow, noGrowB, Bool.and_eq_true] at h
    have h1 := coinFree_of_noGrow p h.1
    have h2 := coinFree_of_noGrow q h.2
    simp only [CoinFree] at h1 h2
    simp [CoinFree, coinFreeB, h1, h2]
  | .loop _ b, h => coinFree_of_noGrow b h

theorem coinFreeB_map' {n k : ℕ} {u : Fin n → Fin k} : ∀ p : Prog n, (Prog.map u p).coinFreeB = p.coinFreeB
  | .prim _ | .coin _ => rfl
  | .seq p q | .ifBlank _ p q | .ifBit _ p q => by
    simp only [Prog.map, coinFreeB, coinFreeB_map' p, coinFreeB_map' q]
  | .loop _ b => by simp only [Prog.map, coinFreeB, coinFreeB_map' b]

theorem coinFree_map {n k : ℕ} (u : Fin n → Fin k) {p : Prog n} (h : p.CoinFree) :
    (Prog.map u p).CoinFree := by
  simp only [CoinFree] at h ⊢; rw [coinFreeB_map']; exact h

/-! ### The placements -/

/-- The gate program's tapes of the evaluators: `100 … 231`. -/
def uE : Fin 132 → Fin 256 := fun j => ⟨j.val + 100, by omega⟩

/-- The evaluators' own tapes: `232 … 243`, then the values `101`, `102`, `100`. -/
def vE : Fin 15 → Fin 256 := ![232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 101, 102, 100]

theorem uE_val (j : Fin 132) : (uE j).val = j.val + 100 := rfl

theorem uE_inj : Function.Injective uE := fun a b h => by
  simp only [uE, Fin.mk.injEq] at h; exact Fin.ext (by omega)

theorem vE_inj : Function.Injective vE := by decide

theorem placed_E : Placed (m := 129) uE vE where
  hu := uE_inj
  hv := vE_inj
  v12 := by decide
  v13 := by decide
  v14 := by decide
  disj := by
    intro i j h
    have h' := congrArg Fin.val h
    rw [uE_val] at h'
    fin_cases i <;> simp only [vE] at h' ⊢ <;> first | decide | (exfalso; revert h'; norm_num; omega)


/-- The tapes of `simKeyP`: `2 … 95`. -/
def oK : Fin 94 → Fin 256 := fun j => ⟨j.val + 2, by omega⟩

theorem oK_inj : Function.Injective oK := fun a b h => by
  simp only [oK, Fin.mk.injEq] at h; exact Fin.ext (by omega)

theorem oK_val (j : Fin 94) : (oK j).val = j.val + 2 := rfl

/-- The tapes of the predicate's conversion. -/
def cM : Fin 13 → Fin 256 := ![1, 244, 245, 89, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem cM_inj : Function.Injective cM := by decide

/-- The tapes of the input store of the simulation of `f̂`. -/
def iT : Fin 9 → Fin 256 := ![0, 232, 234, 247, 248, 249, 250, 251, 252]

theorem iT_inj : Function.Injective iT := by decide

/-- The tapes of the input store of the simulation of the predicate. -/
def iG : Fin 9 → Fin 256 := ![0, 246, 245, 247, 248, 249, 250, 251, 252]

theorem iG_inj : Function.Injective iG := by decide

/-- The tape of the generator's tape `j`. -/
def eGv (n : ℕ) : ℕ :=
  if n = 0 then 1 else if n = 1 then 233 else if n = 2 then 234 else if n = 3 then 4 else n + 96

theorem eGv_lt {n : ℕ} (h : n < 136) : eGv n < 256 := by unfold eGv; split_ifs <;> omega

/-- **The frame of the generator**: its tapes `0 1 2 3` on `1 233 234 4`, the others on
`100 … 231`. -/
def eGen : Fin 136 ↪ Fin 256 :=
  ⟨fun j => ⟨eGv j.val, eGv_lt j.isLt⟩, fun a b h => by
    have h' := congrArg Fin.val h
    simp only [eGv] at h'
    apply Fin.ext
    split_ifs at h' <;> omega⟩

theorem eGen_val (j : Fin 136) : (eGen j).val = eGv j.val := rfl

/-! ### The templates -/

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

/-- The number of inputs of the simulation of `f̂`. -/
abbrev nT (N K k : ℕ) (hk : 2 ^ K < 2 ^ k) : ℕ := (Enum.list (α := JT N K k hk)).length

/-- `replicate n false`. -/
abbrev rp (n : ℕ) : List Bool := List.replicate n false

/-- The templates of the simulation of `f̂` (`SimPre`, `GPreTop`, the evaluator's `V`, `W`). -/
def tmplWT (N K k d W : ℕ) : List (Fin 256 × List Bool) :=
  [(103, rp K), (104, rp N), (105, rp (N * K)), (106, rp 1), (107, rp (2 * k)), (108, rp (2 * k)),
    (109, rp (d * (2 * k))), (110, rp 1), (111, rp 1), (112, rp d), (113, rp (lenA N K k 1)),
    (114, rp (lenA N K k d)), (115, rp (VT N K k d)), (116, rp (1 * (2 * k) * N)),
    (117, rp (d * (2 * k) * N)), (119, gadW N K k), (120, zeroW (lenA N K k d)), (121, oneW N K),
    (186, rp K), (187, rp (2 * k * N)), (188, rp k), (189, rp (2 * k * (2 * k * (N * K)))),
    (235, rp (VT N K k d)), (236, rp W)]

/-- The templates of the simulation of the predicate (`SimPre`, `GPreGsw`, the evaluator's `V`). -/
def tmplWG (N K k d : ℕ) : List (Fin 256 × List Bool) :=
  [(103, rp K), (104, rp N), (105, rp (N * K)), (106, rp 2), (107, rp (2 * k)), (108, rp (2 * k)),
    (109, rp (d * (2 * k))), (110, rp 1), (111, rp 1), (112, rp d), (113, rp (lenA N K k 2)),
    (114, rp (lenA N K k d)), (115, rp (VG N K k d)), (116, rp (2 * (2 * k) * N)),
    (117, rp (d * (2 * k) * N)), (119, gswGadW N K k), (120, zeroW (lenA N K k d)), (121, oneW N K),
    (186, rp K), (187, rp (2 * k * N)), (188, rp k), (189, rp (2 * k * (2 * k * (N * K)))),
    (190, rp (2 * k * (N * K))), (191, rp (2 * k * (N * K))), (193, rp (k * (2 * k * (N * K)))),
    (194, rp (k * (2 * k * (N * K)))), (235, rp (VG N K k d))]

/-- The templates of the key sum (`KTmpl`, on `5 … 19`) and of the last read (`90 91 92`). -/
def tmplWK (N K k d W : ℕ) : List (Fin 256 × List Bool) :=
  [(5, rp K), (6, rp N), (7, rp (N * K)), (8, rp k), (9, rp (2 * k)), (10, rp (2 * k)),
    (11, rp (2 * k * N)), (12, rp (2 * k * (N * K))), (13, rp (2 * k * (2 * k * (N * K)))),
    (14, rp d), (15, rp (d * (2 * k) * (N * K))), (16, rp (d * (2 * k) * N)), (17, rp W),
    (18, rp (VT N K k d)), (19, rp (lenA N K k 1)), (90, rp W), (91, rp (VG N K k d)),
    (92, rp (lenA N K k 2))]

/-- Every tape but `0` and `2`. -/
@[irreducible] def clrW : List (Fin 256) := (List.finRange 256).filter fun t => t ≠ 0 ∧ t ≠ 2

theorem mem_clrW (t : Fin 256) : t ∈ clrW ↔ t ≠ 0 ∧ t ≠ 2 := by simp [clrW]

/-! ### The program -/

variable (c) in
/-- The steps between the two evaluators: the store of `f̂` moved to `3`, the inputs of the
Ring-GSW simulation, its templates. -/
def wfMid : Prog 256 :=
  cp 3 232 ⨾ cp 232 246 ⨾ clr 246 ⨾ cp 233 244 ⨾ clr 244 ⨾ cp 234 245 ⨾ clr 245 ⨾
    putsP (tmplWG N K k c.d)

variable (c) in
/-- The steps before the key sum: the store of the predicate moved to `88`, the templates. -/
def wfPreK (W : ℕ) : Prog 256 := cp 88 232 ⨾ clr 232 ⨾ putsP (tmplWK N K k c.d W)

variable (hk c) in
/-- **The coin-free part of the `W_f` block.** -/
noncomputable def wfRest (W : ℕ) : Prog 256 :=
  Prog.map cM (convP W) ⨾ Prog.map iT (insTP hk c) ⨾ Prog.map iG (insGP hk c) ⨾
    putsP (tmplWT N K k c.d W) ⨾ slpEvalP uE vE (simStepP ginvTopP) ⨾ wfMid c ⨾
    slpEvalP uE vE (simStepP ginvGswP) ⨾ wfPreK c W ⨾ Prog.map oK simKeyP ⨾ clrsP clrW

variable (hk c) in
/-- **The `W_f` block**: the generator, then `wfRest`. -/
noncomputable def wfB (gen : XProg 136) (W : ℕ) : XProg 256 :=
  XProg.seq (XProg.frame eGen gen) (XProg.prog (wfRest hk c W))

/-! ### The specification of the generator -/

/-- The gate program of the simulation of `f̂`. -/
abbrev fhatP (N K k : ℕ) (gs : GateList) := (fhatProg K (ordT₀ N k) (ordO₀ N k) gs).1

/-- The input of the generator: the gate list on tape `0`. -/
def genIn (W : ℕ) (gs : GateList) : Store 136 := fun j => if j.val = 0 then SigabaNeo.Tape.Prog.gsW W gs else []

variable (hk) in
/-- The output of the generator: the gate list kept on tape `0`, the gate stream of `f̂` on tape
`1`, a gate counter on tape `2`, the positions of the output wires of `f̂` on tape `3`. -/
def genOut (W : ℕ) (gs : GateList) : Store 136 := fun j =>
  if j.val = 0 then SigabaNeo.Tape.Prog.gsW W gs
  else if j.val = 1 then gatesW (ixT N K k hk) (nT N K k hk) W (fhatP N K k gs) 0
  else if j.val = 2 then rp (fhatP N K k gs).length
  else if j.val = 3 then posW W N k (fhatPos K (ordT₀ N k) (ordO₀ N k) gs (ixT N K k hk) (nT N K k hk))
  else []

variable (N hk) in
/-- **The `f̂` gate generator** (WS-L1): on the gate lists `gs` with `Ok gs`, from `gsW W gs` it
writes the gate stream of the simulation of `f̂`, a gate counter and the positions of the output
wires (`genOut`); it is well formed. -/
structure GenSpec (gen : XProg 136) (W : ℕ) (Ok : GateList → Prop) : Prop where
  wf : gen.WF
  law : ∀ gs, Ok gs → gen.law (genIn W gs) = PMF.pure (genOut (N := N) (K := K) hk W gs)

variable (N hk) in
/-- The bounds the evaluators need on a gate list: `W` bounds every position (`f̂`'s inputs and
gates, the predicate's wires) and every index of the list. -/
structure WOk (W : ℕ) (gs : GateList) : Prop where
  hT : nT N K k hk + (fhatP N K k gs).length ≤ W
  hG : gs.length + 10 ≤ W
  bnd : BndG W gs

/-! ### Blank tapes -/

/-- Every tape outside `ks` is blank. -/
def Blk (s : Store 256) (ks : List ℕ) : Prop := ∀ t : Fin 256, t.val ∉ ks → s t = []

theorem Blk.upd {s : Store 256} {ks : List ℕ} (h : Blk s ks) (a : Fin 256) (w : List Bool) :
    Blk (Function.update s a w) (a.val :: ks) := fun t ht => by
  have h1 : t ≠ a := fun e => ht (by simp [e])
  rw [Function.update_of_ne h1]; exact h t (fun e => ht (List.mem_cons_of_mem _ e))

theorem Blk.mono {s : Store 256} {ks ks' : List ℕ} (h : Blk s ks) (hs : ∀ x ∈ ks, x ∈ ks') :
    Blk s ks' := fun t ht => h t (fun e => ht (hs _ e))

theorem Blk.puts : ∀ (l : List (Fin 256 × List Bool)) {s : Store 256} {ks : List ℕ}, Blk s ks →
    Blk (putsS l s) (l.map (fun x => x.1.val) ++ ks)
  | [], _, _, h => h
  | x :: l, _, _, h => by
    rw [putsS_cons]
    refine (Blk.puts l (h.upd x.1 x.2)).mono (fun y hy => ?_)
    simp only [List.mem_append, List.mem_cons, List.mem_map, List.map_cons] at hy ⊢
    rcases hy with h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h

theorem putsS_of_not_mem : ∀ (l : List (Fin 256 × List Bool)) (s : Store 256) (t : Fin 256),
    (∀ x ∈ l, x.1 ≠ t) → putsS l s t = s t
  | [], _, _, _ => rfl
  | x :: l, s, t, h => by
    rw [putsS_cons, putsS_of_not_mem l _ t (fun y hy => h y (by simp [hy])),
      Function.update_of_ne (Ne.symm (h x (by simp)))]

/-! ### The steps -/

theorem law_genStep {gen : XProg 136} {W : ℕ} {Ok : GateList → Prop} (hg : GenSpec N hk gen W Ok)
    {gs : GateList} (hok : Ok gs) (s : Store 256) (h1 : s 1 = SigabaNeo.Tape.Prog.gsW W gs)
    (hb : ∀ j : Fin 136, j.val ≠ 0 → s (eGen j) = []) :
    (XProg.frame eGen gen).law s = PMF.pure (Function.update (Function.update (Function.update s 233
      (gatesW (ixT N K k hk) (nT N K k hk) W (fhatP N K k gs) 0)) 234 (rp (fhatP N K k gs).length)) 4
      (posW W N k (fhatPos K (ordT₀ N k) (ordO₀ N k) gs (ixT N K k hk) (nT N K k hk)))) := by
  have hin : (fun j => s (eGen j)) = genIn W gs := by
    funext j
    simp only [genIn]
    split_ifs with h
    · rw [show eGen j = 1 from Fin.ext (by rw [eGen_val, eGv, if_pos h]; rfl), h1]
    · exact hb j h
  rw [XProg.law_frame, hin, hg.law gs hok, PMF.pure_map]
  congr 1
  refine embedF_eq_of _ _ _ _ (fun j => ?_) (fun t ht => ?_)
  · simp only [genOut]
    have hv := eGen_val j
    simp only [eGv] at hv
    split_ifs at hv ⊢ with h0 h1' h2 h3
    · rw [show eGen j = 1 from Fin.ext hv]; simp [Function.update_apply, h1]
    · rw [show eGen j = 233 from Fin.ext hv]; simp [Function.update_apply]
    · rw [show eGen j = 234 from Fin.ext hv]; simp [Function.update_apply]
    · rw [show eGen j = 4 from Fin.ext hv]; simp [Function.update_apply]
    · have e1 : eGen j ≠ 233 := fun e => by rw [e] at hv; simp at hv <;> omega
      have e2 : eGen j ≠ 234 := fun e => by rw [e] at hv; simp at hv <;> omega
      have e3 : eGen j ≠ 4 := fun e => by rw [e] at hv; simp at hv <;> omega
      rw [Function.update_of_ne e3, Function.update_of_ne e2, Function.update_of_ne e1]
      exact hb j h0
  · have n1 : t ≠ 233 := fun e => ht ⟨1, by decide⟩ (by rw [e]; rfl)
    have n2 : t ≠ 234 := fun e => ht ⟨2, by decide⟩ (by rw [e]; rfl)
    have n3 : t ≠ 4 := fun e => ht ⟨3, by decide⟩ (by rw [e]; rfl)
    rw [Function.update_of_ne n3, Function.update_of_ne n2, Function.update_of_ne n1]

/-- The conversion of the predicate's gate list, on the tapes `cM`. -/
theorem run_convStep {W : ℕ} (hW : 0 < W) {gs : GateList} (hb : BndG W gs) (s : Store 256)
    (h1 : s 1 = SigabaNeo.Tape.Prog.gsW W gs) (hz : ∀ i : Fin 13, i ≠ 0 → s (cM i) = []) :
    run (Prog.map cM (convP W)) s = Function.update (Function.update (Function.update
      (Function.update s 1 []) 244 (gatesW (fun i : Fin 10 => i.val) 10 W (predOf 10 gs).1 0)) 245
      (rp gs.length)) 89 (unaryW W (gs.length + 10)) := by
  have hin : s ∘ cM = fun i => if i = 0 then SigabaNeo.Tape.Prog.gsW W gs else [] := by
    funext i
    split_ifs with h
    · subst h; exact h1
    · exact hz i h
  have hout : (![[], gatesW (fun i : Fin 10 => i.val) 10 W (predOf 10 gs).1 0,
      List.replicate gs.length false, unaryW W (gs.length + 10), [], [], [], [], [], [], [], [], []] :
        Store 13) = Function.update (Function.update (Function.update (Function.update (s ∘ cM) 0 [])
          1 (gatesW (fun i : Fin 10 => i.val) 10 W (predOf 10 gs).1 0)) 2 (rp gs.length)) 3
          (unaryW W (gs.length + 10)) := by
    rw [hin]
    funext i
    fin_cases i <;> rfl
  rw [run_map cM_inj, run_convP hW gs hb _ hin, hout, extend_update cM_inj, extend_update cM_inj,
    extend_update cM_inj, extend_update cM_inj, extend_comp_self]
  rfl

theorem run_insTStep (hN : 0 < N) (hK : 0 < K) (sd : SimData hk c) (s : Store 256)
    (h0 : s 0 = (sdEnc hk c).enc sd) (hb : ∀ t : Fin 9, 3 ≤ t.val → s (iT t) = []) :
    run (Prog.map iT (insTP hk c)) s = Function.update s 232 (s 232 ++
      rp ((s 234).length * VT N K k c.d) ++ (insTW sd ++ [simOneW N K k c.d (gadW N K k)]).flatten) :=
  run_map_eq_update iT_inj _ s 1 _ (run_insTP hk c hN hK sd (s ∘ iT) h0 hb)

theorem run_insGStep (hN : 0 < N) (hK : 0 < K) (sd : SimData hk c) (s : Store 256)
    (h0 : s 0 = (sdEnc hk c).enc sd) (hb : ∀ t : Fin 9, 3 ≤ t.val → s (iG t) = []) :
    run (Prog.map iG (insGP hk c)) s = Function.update s 246 (s 246 ++
      rp ((s 245).length * VG N K k c.d) ++ (insGW sd ++ [simOneW N K k c.d (gswGadW N K k)]).flatten) :=
  run_map_eq_update iG_inj _ s 1 _ (run_insGP hk c hN hK sd (s ∘ iG) h0 hb)

/-! ### The preconditions of the evaluators -/

theorem keys_tmplWT (d W : ℕ) : (tmplWT N K k d W).map (fun x => x.1.val) = [103, 104, 105, 106, 107,
    108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 119, 120, 121, 186, 187, 188, 189, 235, 236] := rfl

theorem keys_tmplWG (d : ℕ) : (tmplWG N K k d).map (fun x => x.1.val) = [103, 104, 105, 106, 107,
    108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 119, 120, 121, 186, 187, 188, 189, 190, 191,
    193, 194, 235] := rfl

theorem keys_tmplWK (d W : ℕ) : (tmplWK N K k d W).map (fun x => x.1.val) = [5, 6, 7, 8, 9, 10, 11,
    12, 13, 14, 15, 16, 17, 18, 19, 90, 91, 92] := rfl

/-- A tape outside the keys of a template list keeps its word. -/
theorem putsS_out {l : List (Fin 256 × List Bool)} {ks : List ℕ}
    (hk : l.map (fun x => x.1.val) = ks) (s : Store 256) (t : Fin 256) (ht : t.val ∉ ks) :
    putsS l s t = s t :=
  putsS_of_not_mem l s t fun x hx e => ht (by rw [← hk, ← e]; exact List.mem_map_of_mem hx)

theorem vG_val : ∀ i : Fin 48, 2 ≤ i.val → (vG i).val = i.val + 84 := by decide

theorem simPre_T (W : ℕ) (s : Store 256)
    (hb : ∀ t : Fin 256, (122 ≤ t.val ∧ t.val < 186) ∨ (190 ≤ t.val ∧ t.val < 219) → s t = []) :
    SimPre N K k 1 c.d (gadW N K k) (GPreTop N K k) (putsS (tmplWT N K k c.d W) s ∘ uE) where
  blank := fun i h1 h2 => by
    show putsS _ s (uE i) = []
    rw [putsS_out (keys_tmplWT c.d W) _ _ (by rw [uE_val]; simp <;> omega)]
    exact hb _ (Or.inl ⟨by rw [uE_val]; omega, by rw [uE_val]; omega⟩)
  h3 := by show (putsS _ s 103).length = K; simp [putsS, tmplWT]
  h4 := by show (putsS _ s 104).length = N; simp [putsS, tmplWT]
  h5 := by show (putsS _ s 105).length = N * K; simp [putsS, tmplWT]
  h6 := by show (putsS _ s 106).length = 1; simp [putsS, tmplWT]
  h7 := by show (putsS _ s 107).length = 2 * k; simp [putsS, tmplWT]
  h8 := by show (putsS _ s 108).length = 2 * k; simp [putsS, tmplWT]
  h9 := by show (putsS _ s 109).length = c.d * (2 * k); simp [putsS, tmplWT]
  h10 := by show (putsS _ s 110).length = 1; simp [putsS, tmplWT]
  h11 := by show (putsS _ s 111).length = 1; simp [putsS, tmplWT]
  h12 := by show (putsS _ s 112).length = c.d; simp [putsS, tmplWT]
  h13 := by show (putsS _ s 113).length = lenA N K k 1; simp [putsS, tmplWT]
  h14 := by show (putsS _ s 114).length = lenA N K k c.d; simp [putsS, tmplWT]
  h15 := by show (putsS _ s 115).length = _; simp [putsS, tmplWT]
  h16 := by show (putsS _ s 116).length = 1 * (2 * k) * N; simp [putsS, tmplWT]
  h17 := by show (putsS _ s 117).length = c.d * (2 * k) * N; simp [putsS, tmplWT]
  h19 := by show putsS _ s 119 = _; simp [putsS, tmplWT]
  h20 := by show putsS _ s 120 = _; simp [putsS, tmplWT]
  h21 := by show putsS _ s 121 = _; simp [putsS, tmplWT]
  g := by
    refine ⟨fun i h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
    · show putsS _ s (uE (vG i)) = []
      have hv : (uE (vG i)).val = i.val + 184 := by rw [uE_val, vG_val i (by omega)]
      rw [putsS_out (keys_tmplWT c.d W) _ _ (by rw [hv]; simp <;> omega)]
      exact hb _ (Or.inr ⟨by omega, by omega⟩)
    · show (putsS _ s 186).length = K; simp [putsS, tmplWT]
    · show (putsS _ s 187).length = 2 * k * N; simp [putsS, tmplWT]
    · show (putsS _ s 188).length = k; simp [putsS, tmplWT]
    · show (putsS _ s 189).length = 2 * k * (2 * k * (N * K)); simp [putsS, tmplWT]

theorem simPre_G (s : Store 256)
    (hb : ∀ t : Fin 256, (122 ≤ t.val ∧ t.val < 186) ∨ t.val = 192 ∨ (196 ≤ t.val ∧ t.val < 230) →
      s t = []) :
    SimPre N K k 2 c.d (gswGadW N K k) (GPreGsw N K k) (putsS (tmplWG N K k c.d) s ∘ uE) where
  blank := fun i h1 h2 => by
    show putsS _ s (uE i) = []
    rw [putsS_out (keys_tmplWG c.d) _ _ (by rw [uE_val]; simp <;> omega)]
    exact hb _ (Or.inl ⟨by rw [uE_val]; omega, by rw [uE_val]; omega⟩)
  h3 := by show (putsS _ s 103).length = K; simp [putsS, tmplWG]
  h4 := by show (putsS _ s 104).length = N; simp [putsS, tmplWG]
  h5 := by show (putsS _ s 105).length = N * K; simp [putsS, tmplWG]
  h6 := by show (putsS _ s 106).length = 2; simp [putsS, tmplWG]
  h7 := by show (putsS _ s 107).length = 2 * k; simp [putsS, tmplWG]
  h8 := by show (putsS _ s 108).length = 2 * k; simp [putsS, tmplWG]
  h9 := by show (putsS _ s 109).length = c.d * (2 * k); simp [putsS, tmplWG]
  h10 := by show (putsS _ s 110).length = 1; simp [putsS, tmplWG]
  h11 := by show (putsS _ s 111).length = 1; simp [putsS, tmplWG]
  h12 := by show (putsS _ s 112).length = c.d; simp [putsS, tmplWG]
  h13 := by show (putsS _ s 113).length = lenA N K k 2; simp [putsS, tmplWG]
  h14 := by show (putsS _ s 114).length = lenA N K k c.d; simp [putsS, tmplWG]
  h15 := by show (putsS _ s 115).length = _; simp [putsS, tmplWG]
  h16 := by show (putsS _ s 116).length = 2 * (2 * k) * N; simp [putsS, tmplWG]
  h17 := by show (putsS _ s 117).length = c.d * (2 * k) * N; simp [putsS, tmplWG]
  h19 := by show putsS _ s 119 = _; simp [putsS, tmplWG]
  h20 := by show putsS _ s 120 = _; simp [putsS, tmplWG]
  h21 := by show putsS _ s 121 = _; simp [putsS, tmplWG]
  g := by
    refine ⟨fun i h1 h2 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show putsS _ s (uE (vG i)) = []
      have hv : (uE (vG i)).val = i.val + 184 := by rw [uE_val, vG_val i (by omega)]
      rw [putsS_out (keys_tmplWG c.d) _ _ (by rw [hv]; simp <;> omega)]
      exact hb _ (Or.inr (Or.inr ⟨by omega, by omega⟩))
    · show putsS _ s 192 = []
      rw [putsS_out (keys_tmplWG c.d) _ _ (by decide)]
      exact hb _ (Or.inr (Or.inl rfl))
    · show (putsS _ s 186).length = K; simp [putsS, tmplWG]
    · show (putsS _ s 187).length = 2 * k * N; simp [putsS, tmplWG]
    · show (putsS _ s 188).length = k; simp [putsS, tmplWG]
    · show (putsS _ s 189).length = 2 * k * (2 * k * (N * K)); simp [putsS, tmplWG]
    · show (putsS _ s 190).length = 2 * k * (N * K); simp [putsS, tmplWG]
    · show (putsS _ s 191).length = 2 * k * (N * K); simp [putsS, tmplWG]
    · show (putsS _ s 193).length = k * (2 * k * (N * K)); simp [putsS, tmplWG]
    · show (putsS _ s 194).length = k * (2 * k * (N * K)); simp [putsS, tmplWG]

/-! ### The key sum -/

theorem tmpl_of_mem {l : List (Fin 256 × List Bool)} {s : Store 256} (h : ∀ x ∈ l, s x.1 = x.2)
    {t : Fin 256} {w : List Bool} (hm : (t, w) ∈ l) : s t = w := h _ hm

/-! ### Coin-freeness and well-formedness -/

theorem coinFree_wfRest (W : ℕ) : (wfRest hk c W).CoinFree := by
  have h1 := coinFree_map cM (coinFree_convP W)
  have h2 := coinFree_map iT (coinFree_insTP hk c)
  have h3 := coinFree_map iG (coinFree_insGP hk c)
  have h4 := coinFree_putsP (tmplWT N K k c.d W)
  have h5 := coinFree_of_noGrow _ (noGrow_slpEvalP (u := uE) (v := vE) (stepSpec_simTop N K k c.d))
  have h6 := coinFree_putsP (tmplWG N K k c.d)
  have h7 := coinFree_of_noGrow _ (noGrow_slpEvalP (u := uE) (v := vE) (stepSpec_simGsw N K k c.d))
  have h8 := coinFree_putsP (tmplWK N K k c.d W)
  have h9 := coinFree_map oK (coinFree_of_noGrow _ noGrow_simKeyP)
  have h10 := coinFree_clrsP clrW
  simp only [CoinFree] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [CoinFree, wfRest, wfMid, wfPreK, coinFreeB, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

theorem wf_wfRest (W : ℕ) : (wfRest hk c W).WF :=
  ⟨WF.map cM_inj (wf_convP W), WF.map iT_inj (wf_insTP hk c), WF.map iG_inj (wf_insGP hk c),
    wf_putsP _, wf_slpEvalP placed_E (stepSpec_simTop N K k c.d),
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, wf_putsP _⟩,
    wf_slpEvalP placed_E (stepSpec_simGsw N K k c.d), ⟨trivial, trivial, wf_putsP _⟩,
    WF.map oK_inj wf_simKeyP, wf_clrsP _⟩

/-! ### More store lemmas -/

theorem blk_io2 (a b : List Bool) : Blk (io2 (R := 254) a b []) [0, 1] := fun t ht => by
  have h0 : t.val ≠ 0 := fun e => ht (by simp [e])
  have h1 : t.val ≠ 1 := fun e => ht (by simp [e])
  simp [io2, h0, h1]

theorem putsS_mem : ∀ (l : List (Fin 256 × List Bool)) (s : Store 256),
    (l.map (fun x => x.1.val)).Nodup → ∀ x ∈ l, putsS l s x.1 = x.2
  | [], _, _, _, hx => absurd hx (by simp)
  | y :: l, s, hn, x, hx => by
    rw [putsS_cons]
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [putsS_of_not_mem l _ _ (fun z hz e => hn.1 ⟨z, hz, by rw [e]⟩), Function.update_self]
    · exact putsS_mem l _ hn.2 x hx

theorem run_wfMid (s : Store 256) : run (wfMid c) s = putsS (tmplWG N K k c.d)
    (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update s 3 (s 232)) 232 (s 246)) 246 []) 233 (s 244)) 244 [])
      234 (s 245)) 245 []) := by
  simp only [wfMid, run_seq, run_copy, run_clear, run_putsP]
  congr 1

theorem run_wfPreK (W : ℕ) (s : Store 256) : run (wfPreK c W) s = putsS (tmplWK N K k c.d W)
    (Function.update (Function.update s 88 (s 232)) 232 []) := by
  simp only [wfPreK, run_seq, run_copy, run_clear, run_putsP]

end AdvancedEncryption.DualUse.Prog
