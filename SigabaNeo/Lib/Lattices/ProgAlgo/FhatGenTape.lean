import SigabaNeo.Lib.Lattices.ProgAlgo.FhatGenPos
import SigabaNeo.Lib.Lattices.ProgAlgo.GateListLayout
import SigabaNeo.Lib.Machines.Prog.Sample

/-!
# Generating gate tapes: the tape program

The register machine runs on the tapes `4 … 122` of a store of `136` tapes (`place`, `uV`):

* `constsP` (with growing words, `natP`): the templates and constants of the machine, the pad
  template on `123`;
* `countP`: the number of gates of the list `gsW W gs` on tape `0` into the register `63`;
  the list itself into the source stream;
* the machine code `fhatC` (`Prog.map uV`), the gate stream of `f̂` and its counter to `1`, `2`;
* the output reset, the machine code `posC`, the positions to `3`; the other tapes cleared.
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Lattices

namespace FhatGen

open SigabaNeo.Tape SigabaNeo.Tape.RegVM SLP Algo
open scoped Prog

/-! ### The parameters -/

/-- The template width. -/
def Mv (N k W : ℕ) : ℕ := (W + 12) * (4 * k * N * k) + 2 * W + 2 * N + k + 4 * k * N + 4

/-- The list capacity. -/
def Cv (N k W : ℕ) : ℕ := (W + 2) * (4 * k * N * k) + k + 3

/-- The output pad. -/
def Pv (N k W : ℕ) : ℕ := 2 * W * (W + 4 * k * N * k + 1)

/-- The machine's parameters. -/
def envG (N k W n : ℕ) : Env :=
  { n := n, W := W, M := Mv N k W, C := Cv N k W, pad := List.replicate (Pv N k W) true }

/-- The constant registers `0 … 15`. -/
def cst0 (N k K n : ℕ) (r : ℕ) : ℕ :=
  [n, n + 1, k, k + 1, K, N, 2, 0, 2 * k * N, 2 * k * N + 1, 4 * k * N * k, treeHeight N k,
    4 * k * N, 1, 11, 2 * k * k * N].getD r 0

/-- The state after the constants: empty lists, no source. -/
def σC (N k K n : ℕ) : St :=
  { out := [], t := 0, sc := fun r => cst0 N k K n r.val, ls := fun _ => [], src := [] }

/-- The value of the VM tape `j` after the constants: a length and a bit. -/
def valsV (N k K W n : ℕ) (j : ℕ) : ℕ × Bool :=
  if j = 0 then (Pv N k W, true) else if j = 1 then (Pv N k W, true)
  else if j = 2 then (Mv N k W - (n + 1), true) else if j = 3 then (Mv N k W, true)
  else if j = 4 then (W, true) else if j = 5 then (n, true) else if j = 6 then (0, false)
  else if j < 15 then (0, false) else if j < 31 then (0, false)
  else if j < 95 then (cst0 N k K n (j - 31), true)
  else (Cv N k W * (Mv N k W + 1), false)

theorem valsV_lo (N k K W n j : ℕ) (h : 6 ≤ j) (h' : j < 31) : valsV N k K W n j = (0, false) := by
  unfold valsV; split_ifs <;> first | omega | rfl

theorem valsV_R (N k K W n j : ℕ) (h : 31 ≤ j) (h' : j < 95) :
    valsV N k K W n j = (cst0 N k K n (j - 31), true) := by
  unfold valsV; split_ifs <;> first | omega | rfl

theorem valsV_L (N k K W n j : ℕ) (h : 95 ≤ j) :
    valsV N k K W n j = (Cv N k W * (Mv N k W + 1), false) := by
  unfold valsV; split_ifs <;> first | omega | rfl

theorem enc_σC (N k K W n : ℕ) (j : Fin RegVM.K) :
    enc (envG N k W n) (σC N k K n) (fun _ => []) j =
      List.replicate (valsV N k K W n j.val).1 (valsV N k K W n j.val).2 := by
  rcases tape_cases j with rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
    ⟨r, rfl⟩ | ⟨l, rfl⟩
  · rw [enc_OUT, show tOUT.val = 0 from rfl]; simp [envG, σC, valsV]
  · rw [enc_OC, show tOC.val = 1 from rfl]; simp [envG, σC, valsV]
  · rw [enc_CO, show tCO.val = 2 from rfl]; simp [envG, σC, valsV]
  · rw [enc_T, show tT.val = 3 from rfl]; simp [envG, σC, valsV]
  · rw [enc_W, show tW.val = 4 from rfl]; simp [envG, σC, valsV]
  · rw [enc_N, show tN.val = 5 from rfl]; simp [envG, σC, valsV]
  · rw [enc_SRC, show tSRC.val = 6 from rfl]; simp [envG, σC, valsV, senc]
  · have := i.isLt
    rw [enc_X, show (tX i).val = 7 + i.val from rfl, valsV_lo _ _ _ _ _ _ (by omega) (by omega)]; rfl
  · have := i.isLt; simp only [nD] at this
    rw [enc_C, show (tC i).val = 15 + i.val from rfl, valsV_lo _ _ _ _ _ _ (by omega) (by omega)]; rfl
  · have := r.isLt; simp only [nS] at this
    rw [enc_R, show (tR r).val = 31 + r.val from rfl, valsV_R _ _ _ _ _ _ (by omega) (by omega)]
    simp [σC]
  · rw [enc_L, show (tL l).val = 95 + l.val from rfl, valsV_L _ _ _ _ _ _ (by omega)]
    simp [σC, lenc, envG]

/-! ### The machine's tapes in the store -/

/-- The VM tape `j` is the tape `j + 4`. -/
def uV (j : Fin RegVM.K) : Fin 136 := ⟨j.val + 4, by have : j.val < 119 := j.isLt; omega⟩

theorem uV_inj : Function.Injective uV := fun a b h => by
  simp only [uV, Fin.mk.injEq] at h; exact Fin.ext (by omega)

/-- The store `s` with the machine's tapes `v`. -/
def place (s : Store 136) (v : Store RegVM.K) : Store 136 := fun i =>
  if h : 4 ≤ i.val ∧ i.val < 123 then v ⟨i.val - 4, by show i.val - 4 < 119; omega⟩ else s i

@[simp] theorem place_uV (s : Store 136) (v : Store RegVM.K) (j : Fin RegVM.K) :
    place s v (uV j) = v j := by
  have : j.val < 119 := j.isLt
  unfold place
  rw [dif_pos (show 4 ≤ (uV j).val ∧ (uV j).val < 123 by simp only [uV]; omega)]
  congr 1

theorem place_out (s : Store 136) (v : Store RegVM.K) (i : Fin 136)
    (hi : i.val < 4 ∨ 123 ≤ i.val) : place s v i = s i := by
  simp only [place]; rw [dif_neg (by omega)]

theorem place_comp (s : Store 136) (v : Store RegVM.K) : place s v ∘ uV = v := by
  funext j; simp

theorem extend_place (s : Store 136) (v w : Store RegVM.K) :
    Function.extend uV w (place s v) = place s w := by
  funext i
  by_cases h : 4 ≤ i.val ∧ i.val < 123
  · have hi : i = uV ⟨i.val - 4, by simp [RegVM.K, nD, nS, nL]; omega⟩ := by
      ext; simp [uV]; omega
    rw [hi, uV_inj.extend_apply, place_uV]
  · rw [Function.extend_apply' _ _ _ (by
      rintro ⟨j, rfl⟩; have : j.val < 119 := j.isLt
      exact h ⟨by simp [uV], by simp [uV]; omega⟩)]
    simp only [place, dif_neg h]

theorem run_map_place (p : Prog RegVM.K) (s : Store 136) (v : Store RegVM.K) :
    Prog.run (Prog.map uV p) (place s v) = place s (Prog.run p v) := by
  rw [Prog.run_map uV_inj, place_comp, extend_place]

theorem update_place (s : Store 136) (v : Store RegVM.K) (i : Fin 136)
    (hi : i.val < 4 ∨ 123 ≤ i.val) (w : List Bool) :
    Function.update (place s v) i w = place (Function.update s i w) v := by
  funext x
  by_cases hx : x = i
  · subst hx; simp [place_out _ _ _ hi]
  · rw [Function.update_of_ne hx]
    simp only [place]; split_ifs <;> simp [Function.update_of_ne hx]

theorem update_place_uV (s : Store 136) (v : Store RegVM.K) (j : Fin RegVM.K) (w : List Bool) :
    Function.update (place s v) (uV j) w = place s (Function.update v j w) := by
  funext x
  by_cases hx : x = uV j
  · subst hx; simp
  · rw [Function.update_of_ne hx]
    simp only [place]; split_ifs with h
    · rw [Function.update_of_ne]; rintro rfl; exact hx (by ext; simp [uV]; omega)
    · rfl

/-! ### The constants, with growing words -/

/-- All ones, keeping the width. -/
def oneOp : DigitOp := fun _ _ _ => (true, false)

theorem carryOp_oneOp_snd (w ys : List Bool) :
    (carryOp oneOp w ys).2 = List.replicate w.length true := by
  induction w generalizing ys with
  | nil => rfl
  | cons x xs ih => simp [carryOp, oneOp, ih, List.replicate_succ]

/-- The tape `124` is the counter of `natP`. -/
def tCnt : Fin 136 := 124

/-- `t := replicate v b` (from any `t`, with a blank `124`). -/
def itemP (t : Fin 136) (v : ℕ) (b : Bool) : XProg 136 :=
  XProg.seq (XProg.natP t tCnt v)
    (XProg.prog (if b then Prog.prim (.carry oneOp t t) else Prog.nop t))

theorem law_itemP (t : Fin 136) (ht : t ≠ tCnt) (v : ℕ) (b : Bool) (s : Store 136)
    (hc : s tCnt = []) :
    (itemP t v b).law s = PMF.pure (Function.update s t (List.replicate v b)) := by
  rw [itemP, XProg.law_seq, XProg.law_natP (Ne.symm ht) v s hc, PMF.pure_bind]
  cases b
  · rw [if_neg (by simp), XProg.law_prog_run (Prog.nop t) rfl, Prog.run_nop]
  · rw [if_pos rfl, XProg.law_prog_run (Prog.prim (.carry oneOp t t)) rfl, Prog.run_prim]
    simp [Prim.apply, carryOp_oneOp_snd]

/-- Run the items of a list of tapes. -/
def itemsP (f : Fin 136 → ℕ × Bool) : List (Fin 136) → XProg 136
  | [] => XProg.prog (Prog.nop 0)
  | t :: ts => XProg.seq (itemP t (f t).1 (f t).2) (itemsP f ts)

theorem law_itemsP (f : Fin 136 → ℕ × Bool) : ∀ (ts : List (Fin 136)), tCnt ∉ ts →
    ∀ s : Store 136, s tCnt = [] →
      (itemsP f ts).law s = PMF.pure (fun i => if i ∈ ts then List.replicate (f i).1 (f i).2 else s i)
  | [], _, s, _ => by
    rw [itemsP, XProg.law_prog_run (Prog.nop 0) rfl, Prog.run_nop]; simp
  | t :: ts, hts, s, hc => by
    have ht : t ≠ tCnt := fun h => hts (by simp [h])
    have hts' : tCnt ∉ ts := fun h => hts (by simp [h])
    rw [itemsP, XProg.law_seq, law_itemP t ht _ _ s hc, PMF.pure_bind,
      law_itemsP f ts hts' _ (by rw [Function.update_of_ne (Ne.symm ht)]; exact hc)]
    congr 1; funext i
    by_cases h1 : i ∈ ts
    · simp [h1]
    · by_cases h2 : i = t
      · subst h2; simp [h1]
      · simp [h1, h2, Function.update_of_ne h2]

/-- The tapes of the constants. -/
def tsC : List (Fin 136) := (List.finRange 136).filter (fun i => 4 ≤ i.val ∧ i.val ≤ 123)

/-- The constants, by tape. -/
def valsT (N k K W n : ℕ) (i : Fin 136) : ℕ × Bool :=
  if i.val = 123 then (Pv N k W, true) else valsV N k K W n (i.val - 4)

/-- **The constants**: the machine's templates and constant registers, the pad template on `123`. -/
def constsP (N k K W n : ℕ) : XProg 136 := itemsP (valsT N k K W n) tsC

theorem law_constsP (N k K W n : ℕ) (s : Store 136) (hs : ∀ i : Fin 136, 4 ≤ i.val → s i = []) :
    (constsP N k K W n).law s = PMF.pure (place (Function.update s 123
      (List.replicate (Pv N k W) true)) (enc (envG N k W n) (σC N k K n) (fun _ => []))) := by
  rw [constsP, law_itemsP _ tsC (by decide) s (hs _ (by decide))]
  congr 1; funext i
  by_cases h1 : 4 ≤ i.val ∧ i.val < 123
  · have hm : i ∈ tsC := by simp [tsC]; omega
    rw [if_pos hm]
    simp only [place, dif_pos h1]
    rw [enc_σC]
    have : valsT N k K W n i = valsV N k K W n (i.val - 4) := by
      unfold valsT; rw [if_neg (by omega)]
    rw [this]
  · by_cases h2 : i.val = 123
    · have hm : i ∈ tsC := by simp [tsC]; omega
      have hi : i = 123 := Fin.ext h2
      rw [if_pos hm, place_out _ _ _ (by omega), hi]; simp [valsT]
    · have hm : i ∉ tsC := by simp [tsC]; omega
      rw [if_neg hm, place_out _ _ _ (by omega), Function.update_of_ne (fun h => h2 (by rw [h]; rfl))]

/-! ### Counting the gates -/

/-- One round of the count: two words of the list dropped, the counter `126` decremented. -/
def countBody : Prog 136 :=
  Prog.ifBlank 125 (Prog.nop 125)
    (Prog.dropBy 125 8 127 ⨾ Prog.dropBy 125 8 127 ⨾ Prog.tl 126)

/-- **The count**: `63 := |gs|` (tape `98`), the source `10 :=` the list. Scratch: `125 … 128`. -/
def countP : Prog 136 :=
  Prog.cp 125 0 ⨾ Prog.cp 126 8 ⨾ Prog.cp 128 8 ⨾ Prog.loop 128 countBody ⨾ Prog.cp 98 8 ⨾
    Prog.dropBy 98 126 127 ⨾ Prog.clr 126 ⨾ Prog.cp 10 0

theorem run_countBody (W : ℕ) (st : Store 136) (h127 : st 127 = [])
    (h8 : st 8 = List.replicate W true) :
    Prog.run countBody st = if st 125 = [] then st else
      Function.update (Function.update st 125 (((st 125).drop W).drop W)) 126 (st 126).tail := by
  rw [countBody, Prog.run_ifBlank]
  split_ifs with h
  · exact Prog.run_nop _ _
  · simp only [Prog.run_seq, Prog.run_dropBy 125 8 127 (by decide : (127 : Fin 136) ≠ 125), Prog.run_tail]
    funext x
    simp only [Function.update_apply]
    split_ifs <;> simp_all

/-- The count's step on (list, counter). -/
def cstep (W : ℕ) (a : List Bool × List Bool) : List Bool × List Bool :=
  if a.1 = [] then a else ((a.1.drop W).drop W, a.2.tail)

theorem gsW_cons (W : ℕ) (g : ℕ × ℕ) (gs : GateList) :
    Prog.gsW W (g :: gs) = Prog.unaryW W g.1 ++ (Prog.unaryW W g.2 ++ Prog.gsW W gs) := by
  simp [Prog.gsW]

theorem iter_cstep (W : ℕ) (hW : 0 < W) : ∀ (m : ℕ) (gs : GateList) (R : ℕ),
    (∀ g ∈ gs, g.1 ≤ W ∧ g.2 ≤ W) →
    (cstep W)^[m] (Prog.gsW W gs, List.replicate R true) =
      (Prog.gsW W (gs.drop m), List.replicate (R - min m gs.length) true)
  | 0, gs, R, _ => by simp
  | m + 1, [], R, _ => by
    rw [Function.iterate_succ_apply]
    have : cstep W (Prog.gsW W [], List.replicate R true) = (Prog.gsW W [], List.replicate R true) := by
      simp [cstep, Prog.gsW]
    rw [this, iter_cstep W hW m [] R (by simp)]; simp
  | m + 1, g :: gs, R, hb => by
    rw [Function.iterate_succ_apply]
    have hg := hb g (by simp)
    have h1 := Prog.length_unaryW hg.1
    have h2 := Prog.length_unaryW hg.2
    have : cstep W (Prog.gsW W (g :: gs), List.replicate R true) =
        (Prog.gsW W gs, List.replicate (R - 1) true) := by
      have hne : Prog.gsW W (g :: gs) ≠ [] := by
        rw [gsW_cons]; intro h; have := congrArg List.length h
        rw [List.length_append, h1] at this; simp at this; omega
      unfold cstep
      rw [if_neg hne]
      simp only [gsW_cons]
      rw [List.drop_left' h1, List.drop_left' h2]; simp [List.tail_replicate]
    rw [this, iter_cstep W hW m gs (R - 1) (fun g' hg' => hb g' (by simp [hg']))]
    simp only [List.drop_succ_cons, List.length_cons]
    congr 2; omega

theorem run_countP (W : ℕ) (hW : 0 < W) (gs : GateList) (hb : ∀ g ∈ gs, g.1 ≤ W ∧ g.2 ≤ W)
    (hgW : gs.length ≤ W) (s : Store 136) (h0 : s 0 = Prog.gsW W gs)
    (h8 : s 8 = List.replicate W true) (h125 : s 125 = []) (h126 : s 126 = [])
    (h127 : s 127 = []) (h128 : s 128 = []) :
    Prog.run countP s = Function.update (Function.update s 98 (List.replicate gs.length true)) 10
      (Prog.gsW W gs) := by
  set G : List Bool × List Bool → Store 136 := fun a =>
    Function.update (Function.update s 125 a.1) 126 a.2
  have hstep : ∀ a w, True → Prog.run countBody (Function.update (G a) 128 w) =
      Function.update (G (cstep W a)) 128 w := by
    intro a w _
    rw [run_countBody W _ (by simp [G, h127]) (by simp [G, h8])]
    simp only [G, cstep]
    by_cases ha : a.1 = []
    · rw [if_pos (by simp [ha]), if_pos ha]
    · rw [if_neg (by simpa using ha), if_neg ha]
      funext x; simp only [Function.update_apply]; split_ifs <;> simp_all
  have hloop := Prog.run_loop_iter 128 countBody G (cstep W) (fun _ => True) hstep (fun _ _ => trivial)
    (List.replicate W true) (Prog.gsW W gs, List.replicate W true) trivial
  rw [List.length_replicate, iter_cstep W hW W gs W hb, List.drop_of_length_le hgW,
    min_eq_right hgW] at hloop
  have e1 : Prog.run (Prog.cp 125 0 ⨾ Prog.cp 126 8 ⨾ Prog.cp 128 8) s =
      Function.update (G (Prog.gsW W gs, List.replicate W true)) 128 (List.replicate W true) := by
    simp only [Prog.run_seq, Prog.run_copy, G, h0, h8]
    funext x; simp only [Function.update_apply]; split_ifs <;> simp_all
  simp only [countP, Prog.run_seq] at e1 ⊢
  rw [e1, hloop]
  simp only [Prog.run_copy, Prog.run_dropBy 98 126 127 (by decide : (127 : Fin 136) ≠ 98),
    Prog.run_clear, G]
  funext x; simp only [Function.update_apply]
  split_ifs <;> simp_all [Prog.gsW, List.drop_replicate]
  all_goals omega

/-! ### The two runs of the machine -/

/-- The state after the count: the constants, `63 := |gs|`, the source. -/
def σA (N k K n : ℕ) (gs : GateList) : St :=
  { out := [], t := 0, sc := Function.update (σC N k K n).sc 63 gs.length, ls := fun _ => [],
    src := srcOf gs }

theorem treeHeight_le (N k : ℕ) : treeHeight N k ≤ 2 * k * N + 1 := by
  unfold treeHeight
  refine Nat.clog_le_of_le_pow ?_
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
  have := Nat.lt_two_pow_self (n := 2 * k * N + 1)
  omega

/-- The program of `f̂`. -/
abbrev fhF (N k K : ℕ) (gs : GateList) :=
  fhatSLPL (ordT₀ N k) (ordO₀ N k) (gvExp (2 ^ K)) (2 ^ K) (predOf 10 gs).1 (predOf 10 gs).2

theorem cst0_le (N k K n r : ℕ) : cst0 N k K n r ≤ n + 1 + K + N + 4 * k * N * k +
    treeHeight N k + 2 * k * k * N + 4 * k * N + 2 * k * N + k + 14 := by
  unfold cst0
  rw [List.getD_eq_getElem?_getD]
  cases h : ([n, n + 1, k, k + 1, K, N, 2, 0, 2 * k * N, 2 * k * N + 1, 4 * k * N * k,
      treeHeight N k, 4 * k * N, 1, 11, 2 * k * k * N] : List ℕ)[r]? with
  | none => simp
  | some x =>
    have hx := List.mem_of_getElem? h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [Option.getD_some]
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> omega

set_option maxHeartbeats 4000000 in
theorem vm_runs {N k K W n : ℕ} (hk : 0 < k) (hN : 0 < N) (hK : K ≤ k + 1)
    (ix' : Fin 10 × BI N k → ℕ) (hix : ∀ i b, ix' (i, b) = i.val * (4 * k * N * k) + codec b)
    (hixn : ∀ j, ix' j < n) (gs : GateList) (hgs : gs ≠ []) (hb : ∀ g ∈ gs, g.1 ≤ W ∧ g.2 ≤ W)
    (hG : gs.length + 10 ≤ W) (hT : n + (fhF N k K gs).1.length ≤ W) :
    ∃ σ1 : St, exec (envG N k W n) fhatC (σA N k K n gs) = σ1 ∧
      σ1.out = Prog.gatesW ix' n W (fhF N k K gs).1 0 ∧ σ1.t = (fhF N k K gs).1.length ∧
      Inv (envG N k W n) σ1 ∧
      (exec (envG N k W n) posC { σ1 with out := [] }).out = uw W n ++ uw W n ++
        Prog.posW W N k (fun c i j => pfix n (n + 1 + (fhF N k K gs).1.length) N k
          (repList (envG N k W n) ix' (fhF N k K gs).2) c i j) := by
  set E := envG N k W n with hE
  set B := 4 * k * N * k with hB
  have hkN : 1 ≤ k * N := Nat.mul_pos hk hN
  have e1B : B = 4 * (k * N) * k := by rw [hB]; ring
  have h4kN : 4 * (k * N) ≤ B := by rw [e1B]; exact Nat.le_mul_of_pos_right _ hk
  have hBpos : 1 ≤ B := by omega
  have hkB : k ≤ B := by
    have : k ≤ k * N := Nat.le_mul_of_pos_right _ hN
    omega
  have hNB : N ≤ B := by
    have : N ≤ k * N := Nat.le_mul_of_pos_left _ hk
    omega
  have h2kNk : 2 * (k * N) * k ≤ B := by rw [e1B]; nlinarith
  have hkkN : 2 * k * k * N ≤ B := by
    have : 2 * k * k * N = 2 * (k * N) * k := by ring
    omega
  have hnW : n ≤ W := by omega
  have hWB : W ≤ W * B := Nat.le_mul_of_pos_right _ hBpos
  have hgB : gs.length * B ≤ W * B := Nat.mul_le_mul_right _ (by omega)
  have hM : E.M = W * B + 12 * B + 2 * W + 2 * N + k + 4 * (k * N) + 4 := by
    show Mv N k W = _; unfold Mv; ring
  have hC : E.C = W * B + 2 * B + k + 3 := by show Cv N k W = _; unfold Cv; ring
  have hWM : E.W ≤ E.M := by show W ≤ _; rw [hM]; omega
  have hnM : E.n + 1 ≤ E.M := by show n + 1 ≤ _; rw [hM]; omega
  have hsb : StepB E N k gs.length := by
    refine ⟨hk, hN, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hM, show 4 * k * N * k = B from rfl]; omega
    · rw [hM, show 4 * k * N * k = B from rfl, show 4 * k * N = 4 * (k * N) by ring,
        Nat.add_mul]; omega
    · rw [hC, show (2 * k * N + 1) * k = 2 * (k * N) * k + k by ring]; omega
    · rw [hC]; omega
    · rw [hC, show 4 * k * N * k = B from rfl]; omega
    · rw [hC, show 4 * k * N * k = B from rfl]; omega
    · rw [hM]; omega
  have hth := treeHeight_le N k
  have h2kN : 2 * k * N ≤ B := by
    have : 2 * k * N = 2 * (k * N) := by ring
    omega
  have h4kN' : 4 * k * N ≤ B := by
    have : 4 * k * N = 4 * (k * N) := by ring
    omega
  have hsc : ∀ r : SR, r.val < 16 → (σA N k K n gs).sc r = cst0 N k K n r.val := fun r hr => by
    simp [σA, σC, Function.update_of_ne (show r ≠ 63 by rintro rfl; revert hr; decide)]
  have hc : AllC (E := E) N k K (σA N k K n gs) := by
    refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩ <;>
      (rw [hsc _ (by decide)]; rfl)
  have hI : Inv E (σA N k K n gs) := by
    refine ⟨fun l => by simp [σA], fun x hx => ?_⟩
    simp only [σA, srcOf, List.mem_flatMap, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hx
    obtain ⟨g, hg, rfl | rfl⟩ := hx
    · exact (hb g hg).1
    · exact (hb g hg).2
  have hS : ScOK E (σA N k K n gs) := by
    intro r
    simp only [σA, σC, Function.update_apply]
    split_ifs
    · show gs.length ≤ E.M; rw [hM]; omega
    · show cst0 N k K n r.val ≤ E.M
      have := cst0_le N k K n r.val
      rw [← hB] at this
      rw [hM]; omega
  have hmk : mk E ix' [] (σA N k K n gs) = σA N k K n gs := rfl
  obtain ⟨sc', ls', e1, d23, f1, hI1, hS1⟩ := exec_fhatC hnM hWM hK ix' hix hixn gs hgs hsb
    (σA N k K n gs) hc hI hS (rfl) (by simp [σA, σC])
    (by show n + (fhF N k K gs).1.length ≤ E.M; rw [hM]; omega)
  rw [hmk] at e1
  set σ1 := mk E ix' (fhF N k K gs).1 (setSLS (σA N k K n gs) sc' ls' [])
  refine ⟨σ1, e1, rfl, rfl, hI1, ?_⟩
  have hfr : ∀ r : SR, r.val < 16 → sc' r = cst0 N k K n r.val := fun r hr => by
    rw [f1 r hr]; simp [σA, σC, Function.update_of_ne (show r ≠ 63 by rintro rfl; revert hr; decide)]
  obtain ⟨ho, -, -, -⟩ := exec_posC (E := E) hk hN { σ1 with out := [] }
    (repList E ix' (fhF N k K gs).2)
    (by show sc' 0 = n; rw [hfr 0 (by decide)]; rfl)
    (by show sc' 2 = k; rw [hfr 2 (by decide)]; rfl)
    (by show sc' 5 = N; rw [hfr 5 (by decide)]; rfl)
    (by show sc' 7 = 0; rw [hfr 7 (by decide)]; rfl)
    (by show sc' 15 = _; rw [hfr 15 (by decide)]; rfl) d23
    (fun x hx => (hI1.1 23).2 x (by show x ∈ ls' 23; rw [d23]; exact hx))
    (by show n + 1 + (fhF N k K gs).1.length ≤ E.M; rw [hM]; omega)
    (by rw [hM, show 4 * k * N * k = B from rfl]; omega) (by rw [hC]; omega)
  rw [ho, posList_eq]
  rfl

end FhatGen

end SigabaNeo.Lattices
