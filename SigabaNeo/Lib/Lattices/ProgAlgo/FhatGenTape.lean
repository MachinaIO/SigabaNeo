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
  if r = 0 then n else if r = 1 then n + 1 else if r = 2 then k else if r = 3 then k + 1
  else if r = 4 then K else if r = 5 then N else if r = 6 then 2 else if r = 7 then 0
  else if r = 8 then 2 * k * N else if r = 9 then 2 * k * N + 1 else if r = 10 then 4 * k * N * k
  else if r = 11 then treeHeight N k else if r = 12 then 4 * k * N else if r = 13 then 1
  else if r = 14 then 11 else if r = 15 then 2 * k * k * N else 0

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

end FhatGen

end SigabaNeo.Lattices
