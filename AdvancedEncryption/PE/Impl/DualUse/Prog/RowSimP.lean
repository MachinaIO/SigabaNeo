import PE.Impl.DualUse.Prog.KeyP
import PE.Impl.DualUse.Algo.RowSimData
import SigabaNeo.Lib.Machines.Prog.Moves
import SigabaNeo.Lib.Machines.Prog.FrameIO

/-!
# Tape helpers for the crafted simulation data

Generic pieces of the blocks `bfX` (`KeyGen`) and `cfX` (`Dec`), which write the word of a crafted
`SimData`, run the `W_f` block on it, and read the result back:

* `getAt o L src dst tmp a b`: `dst := dst ++ take L (drop o src)` (`law_getAt`);
* `wLoopP`: the `W`-part loop: per row, the stash `X` (then `Z` zeros) and the next row of `F`
  (`law_wLoopP`, `iterate_wStep`);
* `skipLoopP`: per row, drop `Z` bits and move the next row (`law_skipLoopP`);
* `io1 w`: the store with `w` on tape `0`, every other tape blank; `eLo m`: the frame `0 ↦ 0`,
  `j ↦ j + 1`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape Cslib Cslib.Probability
open SigabaNeo.Tape.Prog (tailsP run_tailsP coinFree_tailsP wf_tailsP)

variable {n : ℕ}

/-! ### Reading a block -/

/-- `dst := dst ++ take L (drop o src)`, through the blank tapes `tmp`, `a`, `b`. -/
def getAt (o L : ℕ) (src dst tmp a b : Fin n) : XProg n :=
  XProg.seq (XProg.prog (Prog.seq (.prim (.copy tmp src)) (tailsP tmp o)))
    (XProg.seq (prefP L tmp dst a b) (XProg.prog (.prim (.clear tmp))))

theorem coinFree_cpTails (tmp src : Fin n) (o : ℕ) :
    (Prog.seq (.prim (.copy tmp src)) (tailsP tmp o)).CoinFree := by
  have := coinFree_tailsP tmp o
  simp only [Prog.CoinFree] at this
  simp [Prog.CoinFree, Prog.coinFreeB, this]

theorem law_getAt (o L : ℕ) {src dst tmp a b : Fin n} (h1 : tmp ≠ dst) (h2 : a ≠ dst) (h3 : a ≠ b)
    (h4 : dst ≠ b) (h5 : tmp ≠ a) (h6 : tmp ≠ b) (s : Store n) (htmp : s tmp = [])
    (ha : s a = []) (hb : s b = []) :
    (getAt o L src dst tmp a b).law s =
      PMF.pure (Function.update s dst (s dst ++ ((s src).drop o).take L)) := by
  rw [getAt, XProg.law_seq_pure (by rw [XProg.law_prog, Prog.law_eq_run_of_coinFree _ (coinFree_cpTails _ _ _)]),
    XProg.law_seq_pure (law_prefP _ h2 h3 h4 h5 _ (by
      simp [Prog.run_seq, run_tailsP, Prog.run_prim, Prim.apply, Function.update_apply, ha,
        Ne.symm h5])
      (by simp [Prog.run_seq, run_tailsP, Prog.run_prim, Prim.apply, Function.update_apply, hb,
        Ne.symm h6])), XProg.law_prim]
  congr 1
  simp only [Prog.run_seq, run_tailsP, Prog.run_prim, Prim.apply]
  funext t
  simp only [Function.update_apply]
  by_cases ht : t = tmp
  · subst ht; simp [h1, htmp]
  · by_cases hd : t = dst
    · subst hd; simp [Ne.symm h1]
    · simp [ht, hd]

theorem wf_getAt (o L : ℕ) (src dst tmp a b : Fin n) : (getAt o L src dst tmp a b).WF :=
  ⟨⟨trivial, wf_tailsP _ _⟩, wf_prefP _ _ _ _ _, trivial⟩

/-! ### The `W`-part loop -/

/-- One round on (output, rows, stash): the stash, then the next row; the stash becomes `Z` zeros. -/
def wStep (Z R : ℕ) (a : List Bool × List Bool × List Bool) : List Bool × List Bool × List Bool :=
  (a.1 ++ a.2.2.take Z ++ a.2.1.take R, a.2.1.drop R, a.2.2.drop Z ++ List.replicate Z false)

theorem iterate_wStep (Z R : ℕ) : ∀ (rows : List (List Bool)), (∀ r ∈ rows, r.length = R) →
    ∀ (O X rest : List Bool), X.length = Z →
      ((wStep Z R)^[rows.length] (O, rows.flatten ++ rest, X)).1 =
          O ++ wPart X (List.replicate Z false) rows ∧
        ((wStep Z R)^[rows.length] (O, rows.flatten ++ rest, X)).2.1 = rest
  | [], _, O, X, rest, _ => by simp [wPart]
  | r :: rs, hr, O, X, rest, hX => by
    have hr0 : r.length = R := hr r (by simp)
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : wStep Z R (O, (r :: rs).flatten ++ rest, X) =
        (O ++ X ++ r, rs.flatten ++ rest, List.replicate Z false) := by
      simp only [wStep, List.flatten_cons, List.append_assoc]
      rw [List.take_of_length_le (le_of_eq hX), List.drop_of_length_le (le_of_eq hX),
        List.take_left' hr0, List.drop_left' hr0, List.nil_append]
    rw [e]
    obtain ⟨h1, h2⟩ := iterate_wStep Z R rs (fun r' hr' => hr r' (by simp [hr'])) (O ++ X ++ r)
      (List.replicate Z false) rest (by simp)
    refine ⟨?_, h2⟩
    rw [h1, wPart]
    simp

/-- **The `W`-part loop**: `|tn|` rounds of: move the stash `x` (`|tz|` bits) to `out`, refill it
with `|tz|` zeros, move `|tr|` bits of `f` to `out` (counters `c`, `c'`). -/
def wLoopP (out f x c c' tn tz tr : Fin n) : XProg n :=
  XProg.forN c tn (XProg.seq (XProg.moveP out x c' tz)
    (XProg.seq (XProg.zerosP x c' tz) (XProg.moveP out f c' tr)))

theorem law_wLoopP {out f x c c' tn tz tr : Fin n} (hd : [out, f, x, c, c', tn, tz, tr].Nodup)
    (s : Store n) (hc : s c = []) (hc' : s c' = []) :
    (wLoopP out f x c c' tn tz tr).law s =
      PMF.pure (Function.update (Function.update (Function.update (Function.update s
        out ((wStep (s tz).length (s tr).length)^[(s tn).length] (s out, s f, s x)).1)
        f ((wStep (s tz).length (s tr).length)^[(s tn).length] (s out, s f, s x)).2.1)
        x ((wStep (s tz).length (s tr).length)^[(s tn).length] (s out, s f, s x)).2.2) c []) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h03, h04, h05, h06, h07⟩, ⟨h12, h13, h14, h15, h16, h17⟩,
    ⟨h23, h24, h25, h26, h27⟩, ⟨h34, h35, h36, h37⟩, ⟨h45, h46, h47⟩, ⟨h56, h57⟩, h67, -⟩ := hd
  set Z := (s tz).length
  set R := (s tr).length
  let G : List Bool × List Bool × List Bool → Store n := fun a =>
    Function.update (Function.update (Function.update s out a.1) f a.2.1) x a.2.2
  have hG : ∀ a (t : Fin n), t ≠ out → t ≠ f → t ≠ x → G a t = s t := by
    intro a t h1 h2 h3; simp [G, Function.update_apply, h1, h2, h3]
  rw [wLoopP, XProg.law_forN_det _ G (wStep Z R) _ (s out, s f, s x) s]
  · funext t
    simp only [G, Function.update_apply]
    by_cases h1 : t = c
    · simp [h1]
    · by_cases ho : t = out <;> by_cases hf : t = f <;> by_cases hx : t = x <;> simp_all
  · intro a w
    have Go : G a out = a.1 := by simp [G, Function.update_apply, h01, h02]
    have Gf : G a f = a.2.1 := by simp [G, Function.update_apply, h12]
    have Gx : G a x = a.2.2 := by simp [G]
    have Gs : ∀ t, t ≠ out → t ≠ f → t ≠ x → G (wStep Z R a) t = G a t := fun t h1 h2 h3 => by
      rw [hG _ t h1 h2 h3, hG _ t h1 h2 h3]
    have Go' : G (wStep Z R a) out = (wStep Z R a).1 := by simp [G, Function.update_apply, h01, h02]
    have Gf' : G (wStep Z R a) f = (wStep Z R a).2.1 := by simp [G, Function.update_apply, h12]
    have Gx' : G (wStep Z R a) x = (wStep Z R a).2.2 := by simp [G]
    have Go'' : Function.update (G (wStep Z R a)) c w out = (wStep Z R a).1 := by
      rw [Function.update_of_ne h03, Go']
    have Gf'' : Function.update (G (wStep Z R a)) c w f = (wStep Z R a).2.1 := by
      rw [Function.update_of_ne h13, Gf']
    have Gx'' : Function.update (G (wStep Z R a)) c w x = (wStep Z R a).2.2 := by
      rw [Function.update_of_ne h23, Gx']
    have e1 : (Function.update (G a) c w) c' = [] := by
      rw [Function.update_of_ne (Ne.symm h34), hG a c' (Ne.symm h04) (Ne.symm h14) (Ne.symm h24)]
      exact hc'
    have so : (Function.update (G a) c w) out = a.1 := by rw [Function.update_of_ne h03, Go]
    have sf : (Function.update (G a) c w) f = a.2.1 := by rw [Function.update_of_ne h13, Gf]
    have sx : (Function.update (G a) c w) x = a.2.2 := by rw [Function.update_of_ne h23, Gx]
    have sz : (Function.update (G a) c w) tz = s tz := by
      rw [Function.update_of_ne (Ne.symm h36), hG a tz (Ne.symm h06) (Ne.symm h16) (Ne.symm h26)]
    have sr : (Function.update (G a) c w) tr = s tr := by
      rw [Function.update_of_ne (Ne.symm h37), hG a tr (Ne.symm h07) (Ne.symm h17) (Ne.symm h27)]
    have sc : (Function.update (G a) c w) c = w := Function.update_self _ _ _
    have sO : ∀ t, t ≠ c → (Function.update (G a) c w) t = G a t := fun t h =>
      Function.update_of_ne h _ _
    generalize Function.update (G a) c w = S1 at e1 so sf sx sz sr sc sO
    rw [XProg.law_seq_pure (XProg.law_moveP h02 h04 h24 h46 _ e1),
      XProg.law_seq_pure (XProg.law_zerosP h24 h46 _ (by
        rw [Function.update_of_ne (Ne.symm h24), Function.update_of_ne (Ne.symm h04)]; exact e1)),
      XProg.law_moveP h01 h04 h14 h47 _ (by
        rw [Function.update_of_ne (Ne.symm h24), Function.update_of_ne (Ne.symm h24),
          Function.update_of_ne (Ne.symm h04)]; exact e1)]
    congr 1
    funext t
    have hz' : (S1 tz).length = Z := by rw [sz]
    have hr' : (S1 tr).length = R := by rw [sr]
    by_cases ho : t = out
    · subst ho
      rw [Go'']
      simp [Function.update_apply, h12, Ne.symm h12, h01, Ne.symm h01, h02, Ne.symm h02, h03, Ne.symm h06,
        Ne.symm h07, Ne.symm h26, Ne.symm h27, Ne.symm h16, Ne.symm h17, so, sf, sx, sz, sr, Go',
        wStep, Z, R]
    · by_cases hf : t = f
      · subst hf
        rw [Gf'']
        simp [Function.update_apply, h01, Ne.symm h01, h12, Ne.symm h12, h13, Ne.symm h07,
          Ne.symm h17, Ne.symm h27, Ne.symm h06, Ne.symm h16, Ne.symm h26, so, sf, sx, sz, sr, 
          wStep, Z, R]
      · by_cases hx : t = x
        · subst hx
          rw [Gx'']
          simp [Function.update_apply, h02, Ne.symm h02, h12, Ne.symm h12, h23, Ne.symm h06,
            Ne.symm h26, Ne.symm h16, so, sf, sx, sz, sr, wStep, Z, R]
        · simp only [Function.update_apply, if_neg ho, if_neg hf, if_neg hx]
          by_cases hc0 : t = c
          · subst hc0; simp [sc]
          · rw [if_neg hc0, sO t hc0, Gs t ho hf hx]

theorem wf_wLoopP {out f x c c' tn tz tr : Fin n} (h1 : out ≠ c') (h2 : x ≠ c') (h3 : f ≠ c')
    (h4 : out ≠ c) (h5 : x ≠ c) (h6 : f ≠ c) (h7 : c' ≠ c) :
    (wLoopP out f x c c' tn tz tr).WF := by
  refine ⟨trivial, ⟨XProg.wf_moveP h1 h2, XProg.wf_zerosP h2, XProg.wf_moveP h1 h3⟩, ?_⟩
  simp [wLoopP, XProg.moveP, XProg.zerosP, XProg.forN, XProg.Preserves, Prog.Preserves,
    Prim.writes, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7, h7]

/-! ### The loop reading the rows back -/

/-- One round on (output, source): skip `Z` bits, move the next `R`. -/
def skStep (Z R : ℕ) (a : List Bool × List Bool) : List Bool × List Bool :=
  (a.1 ++ (a.2.drop Z).take R, (a.2.drop Z).drop R)

theorem iterate_skStep (Z R : ℕ) : ∀ (rows : List (List Bool)), (∀ r ∈ rows, r.length = R) →
    ∀ (O X rest : List Bool), X.length = Z →
      ((skStep Z R)^[rows.length] (O, wPart X (List.replicate Z false) rows ++ rest)) =
        (O ++ rows.flatten, rest)
  | [], _, O, X, rest, _ => by simp [wPart]
  | r :: rs, hr, O, X, rest, hX => by
    have hr0 : r.length = R := hr r (by simp)
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : skStep Z R (O, wPart X (List.replicate Z false) (r :: rs) ++ rest) =
        (O ++ r, wPart (List.replicate Z false) (List.replicate Z false) rs ++ rest) := by
      simp only [skStep, wPart, List.append_assoc]
      rw [List.drop_left' hX, List.take_left' hr0, List.drop_left' hr0]
    rw [e, iterate_skStep Z R rs (fun r' hr' => hr r' (by simp [hr'])) (O ++ r) _ rest (by simp)]
    simp

/-- **The reading loop**: `|tn|` rounds of: drop `|tz|` bits of `src`, move `|tr|` bits of `src`
to `out` (counters `c`, `c'`). -/
def skipLoopP (out src c c' tn tz tr : Fin n) : XProg n :=
  XProg.forN c tn (XProg.seq (XProg.dropP src c' tz) (XProg.moveP out src c' tr))

theorem law_skipLoopP {out src c c' tn tz tr : Fin n} (hd : [out, src, c, c', tn, tz, tr].Nodup)
    (s : Store n) (hc : s c = []) (hc' : s c' = []) :
    (skipLoopP out src c c' tn tz tr).law s =
      PMF.pure (Function.update (Function.update (Function.update s
        out ((skStep (s tz).length (s tr).length)^[(s tn).length] (s out, s src)).1)
        src ((skStep (s tz).length (s tr).length)^[(s tn).length] (s out, s src)).2) c []) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h03, h04, h05, h06⟩, ⟨h12, h13, h14, h15, h16⟩,
    ⟨h23, h24, h25, h26⟩, ⟨h34, h35, h36⟩, ⟨h45, h46⟩, h56, -⟩ := hd
  set Z := (s tz).length
  set R := (s tr).length
  let G : List Bool × List Bool → Store n := fun a =>
    Function.update (Function.update s out a.1) src a.2
  have hG : ∀ a (t : Fin n), t ≠ out → t ≠ src → G a t = s t := by
    intro a t h1 h2; simp [G, Function.update_apply, h1, h2]
  rw [skipLoopP, XProg.law_forN_det _ G (skStep Z R) _ (s out, s src) s]
  · funext t
    simp only [G, Function.update_apply]
    by_cases h1 : t = c
    · simp [h1]
    · by_cases ho : t = out <;> by_cases hf : t = src <;> simp_all
  · intro a w
    have Go'' : Function.update (G (skStep Z R a)) c w out = (skStep Z R a).1 := by
      rw [Function.update_of_ne h02]; simp [G, Function.update_apply, h01]
    have Gs'' : Function.update (G (skStep Z R a)) c w src = (skStep Z R a).2 := by
      rw [Function.update_of_ne h12]; simp [G]
    have e1 : (Function.update (G a) c w) c' = [] := by
      rw [Function.update_of_ne (Ne.symm h23), hG a c' (Ne.symm h03) (Ne.symm h13)]
      exact hc'
    have so : (Function.update (G a) c w) out = a.1 := by
      rw [Function.update_of_ne h02]; simp [G, Function.update_apply, h01]
    have sf : (Function.update (G a) c w) src = a.2 := by
      rw [Function.update_of_ne h12]; simp [G]
    have sz : (Function.update (G a) c w) tz = s tz := by
      rw [Function.update_of_ne (Ne.symm h25), hG a tz (Ne.symm h05) (Ne.symm h15)]
    have sr : (Function.update (G a) c w) tr = s tr := by
      rw [Function.update_of_ne (Ne.symm h26), hG a tr (Ne.symm h06) (Ne.symm h16)]
    have sc : (Function.update (G a) c w) c = w := Function.update_self _ _ _
    have sO : ∀ t, t ≠ c → t ≠ out → t ≠ src →
        (Function.update (G a) c w) t = Function.update (G (skStep Z R a)) c w t := fun t h h1 h2 => by
      rw [Function.update_of_ne h, Function.update_of_ne h, hG _ t h1 h2, hG _ t h1 h2]
    generalize Function.update (G a) c w = S1 at e1 so sf sz sr sc sO
    rw [XProg.law_seq_pure (XProg.law_dropP h13 h35 _ e1),
      XProg.law_moveP h01 h03 h13 h36 _ (by rw [Function.update_of_ne (Ne.symm h13)]; exact e1)]
    congr 1
    funext t
    by_cases ho : t = out
    · subst ho
      rw [Go'']
      simp [Function.update_apply, h01, Ne.symm h01, Ne.symm h05, Ne.symm h06, Ne.symm h16, so, sf,
        sz, sr, skStep, Z, R]
    · by_cases hf : t = src
      · subst hf
        rw [Gs'']
        simp [Function.update_apply, h01, Ne.symm h01, Ne.symm h15, Ne.symm h16, so, sf, sz, sr,
          skStep, Z, R]
      · simp only [Function.update_apply, if_neg ho, if_neg hf]
        by_cases hc0 : t = c
        · subst hc0; simp [sc]
        · rw [sO t hc0 ho hf, Function.update_of_ne hc0, if_neg hc0]

theorem wf_skipLoopP {out src c c' tn tz tr : Fin n} (h1 : out ≠ c') (h2 : src ≠ c')
    (h4 : out ≠ c) (h5 : src ≠ c) (h7 : c' ≠ c) :
    (skipLoopP out src c c' tn tz tr).WF := by
  refine ⟨trivial, ⟨XProg.wf_dropP h2, XProg.wf_moveP h1 h2⟩, ?_⟩
  simp [skipLoopP, XProg.moveP, XProg.dropP, XProg.forN, XProg.Preserves, Prog.Preserves,
    Prim.writes, Ne.symm h4, Ne.symm h5, Ne.symm h7, h7]

/-! ### Frames and stores -/

/-- The store with `w` on tape `0`, every other tape blank. -/
def io1 {m : ℕ} [NeZero m] (w : List Bool) : Store m := Function.update (fun _ => []) 0 w

/-- The frame `0 ↦ 0`, `j ↦ j + 1` (it skips tape `1`). -/
def eLo (m : ℕ) (hm : m + 1 ≤ 256) : Fin m ↪ Fin 256 :=
  ⟨fun j => ⟨if j.val = 0 then 0 else j.val + 1, by split_ifs <;> omega⟩, by
    intro a b h
    simp only [Fin.mk.injEq] at h
    ext
    split_ifs at h <;> omega⟩

theorem eLo_val {m : ℕ} {hm : m + 1 ≤ 256} (j : Fin m) :
    (eLo m hm j).val = if j.val = 0 then 0 else j.val + 1 := rfl

end AdvancedEncryption.DualUse.Prog
