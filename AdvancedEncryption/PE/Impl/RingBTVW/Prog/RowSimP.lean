import PE.Impl.RingBTVW.Prog.KeyP
import PE.Impl.RingBTVW.Algo.RowSimData
import SigabaNeoStd.Machines.Prog.Moves
import SigabaNeoStd.Machines.Prog.FrameIO

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

namespace AdvancedEncryption.RingBTVW.Prog

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
  (a.1 ++ a.2.2.take Z ++ a.2.1.take R, a.2.1.drop R, List.replicate Z false)

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
      rw [List.take_of_length_le (le_of_eq hX), List.take_left' hr0, List.drop_left' hr0]
    rw [e]
    obtain ⟨h1, h2⟩ := iterate_wStep Z R rs (fun r' hr' => hr r' (by simp [hr'])) (O ++ X ++ r)
      (List.replicate Z false) rest (by simp)
    refine ⟨?_, h2⟩
    rw [h1, wPart]
    simp

/-- **The `W`-part loop**: `|tn|` rounds of: move the stash `x` (`|tz|` bits) to `out`, refill it
with `|tz|` zeros, move `|tr|` bits of `f` to `out` (counters `c`, `c'`). -/
def wLoopP (out f x c c' tn tz tr : Fin n) : XProg n :=
  XProg.forN c tn (XProg.seq (XProg.moveP out x c' tz) (XProg.seq (XProg.prog (.prim (.clear x)))
    (XProg.seq (XProg.zerosP x c' tz) (XProg.moveP out f c' tr))))

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
      XProg.law_seq_pure (XProg.law_prim _ _), Prim.apply,
      XProg.law_seq_pure (XProg.law_zerosP h24 h46 _ (by
        rw [Function.update_of_ne (Ne.symm h24), Function.update_of_ne (Ne.symm h24),
          Function.update_of_ne (Ne.symm h04)]; exact e1)),
      XProg.law_moveP h01 h04 h14 h47 _ (by
        rw [Function.update_of_ne (Ne.symm h24), Function.update_of_ne (Ne.symm h24),
          Function.update_of_ne (Ne.symm h24), Function.update_of_ne (Ne.symm h04)]; exact e1)]
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
  refine ⟨trivial, ⟨XProg.wf_moveP h1 h2, trivial, XProg.wf_zerosP h2, XProg.wf_moveP h1 h3⟩, ?_⟩
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

/-! ### Stores as association lists -/

/-- The store of an association list (the first entry of a tape wins, blank by default). -/
def sto {m : ℕ} (l : List (Fin m × List Bool)) : Store m :=
  fun t => ((l.find? fun x => x.1 = t).map Prod.snd).getD []

@[simp] theorem sto_nil {m : ℕ} (t : Fin m) : sto [] t = [] := rfl

@[simp] theorem sto_cons {m : ℕ} (a : Fin m) (v : List Bool) (l : List (Fin m × List Bool))
    (t : Fin m) : sto ((a, v) :: l) t = if a = t then v else sto l t := by
  by_cases h : a = t <;> simp [sto, List.find?, h]

theorem update_sto {m : ℕ} (l : List (Fin m × List Bool)) (a : Fin m) (v : List Bool) :
    Function.update (sto l) a v = sto ((a, v) :: l) := by
  funext t
  by_cases h : t = a
  · subst h; simp
  · simp [Function.update_apply, h, Ne.symm h]

theorem tmplS_sto {m : ℕ} : ∀ (tl : List (Fin m × ℕ)) (l : List (Fin m × List Bool)),
    tmplS tl (sto l) = sto ((tl.reverse.map fun x => (x.1, List.replicate x.2 false)) ++ l)
  | [], l => rfl
  | x :: tl, l => by
    rw [tmplS, List.foldl_cons, ← tmplS, update_sto, tmplS_sto tl]
    simp

theorem io1_sto {m : ℕ} [NeZero m] (w : List Bool) : io1 (m := m) w = sto [(0, w)] := by
  rw [io1, ← update_sto]; rfl

theorem clear_sto {m : ℕ} (cl : List (Fin m)) (l : List (Fin m × List Bool)) :
    (fun t => if t ∈ cl then [] else sto l t) = sto ((cl.map fun t => (t, [])) ++ l) := by
  funext t
  induction cl with
  | nil => simp
  | cons a cl ih =>
    simp only [List.mem_cons, List.map_cons, List.cons_append, sto_cons] at ih ⊢
    by_cases h : a = t
    · subst h; simp
    · simp [h, Ne.symm h, ih]

/-! ### The frame `eLo` on the stores of the blocks -/

theorem io2_eLo {m : ℕ} [NeZero m] {hm : m + 1 ≤ 256} (a b : List Bool) :
    (fun j => io2 (R := 254) a b [] (eLo m hm j)) = sto [(0, a)] := by
  funext j
  simp only [io2, eLo_val, sto_cons, sto_nil]
  by_cases h : j.val = 0
  · have : (0 : Fin m) = j := Fin.ext (by simp [h])
    simp [h, this]
  · have : (0 : Fin m) ≠ j := fun e => h (by rw [← e]; simp)
    simp [h, this]

theorem embedF_eLo {m : ℕ} [NeZero m] {hm : m + 1 ≤ 256} (a b a' : List Bool) :
    embedF (eLo m hm) (io2 (R := 254) a b []) (sto [(0, a')]) = io2 (R := 254) a' b [] := by
  refine embedF_eq_of _ _ _ _ (fun j => ?_) (fun t ht => ?_)
  · simp only [io2, eLo_val, sto_cons, sto_nil]
    by_cases h : j.val = 0
    · have : (0 : Fin m) = j := Fin.ext (by simp [h])
      simp [h, this]
    · have : (0 : Fin m) ≠ j := fun e => h (by rw [← e]; simp)
      simp [h, this]
  · have h0 : t.val ≠ 0 := fun h => ht 0 (Fin.ext (by rw [eLo_val]; simp [h]))
    simp only [io2, h0, if_false]

theorem eLo_eq_two {m : ℕ} {hm : m + 1 ≤ 256} (j : Fin m) : eLo m hm j = 2 ↔ j.val = 1 := by
  rw [Fin.ext_iff, eLo_val]
  constructor
  · intro h; split_ifs at h <;> simp at h <;> omega
  · intro h; simp [h]

theorem upd_eLo {m : ℕ} [NeZero m] {hm : m + 1 ≤ 256} (h1 : 1 < m) (a v : List Bool) :
    (fun j => Function.update (io2 (R := 254) a [] []) 2 v (eLo m hm j)) =
      sto [(⟨1, h1⟩, v), (0, a)] := by
  funext j
  rw [Function.update_apply, sto_cons, sto_cons, sto_nil]
  by_cases h' : j.val = 1
  · have e1 : (⟨1, h1⟩ : Fin m) = j := Fin.ext (by simp [h'])
    rw [if_pos ((eLo_eq_two j).mpr h'), if_pos e1]
  · have e1 : (⟨1, h1⟩ : Fin m) ≠ j := fun e => h' (by rw [← e])
    rw [if_neg (fun e => h' ((eLo_eq_two j).mp e)), if_neg e1]
    simp only [io2, eLo_val]
    by_cases h : j.val = 0
    · have e0 : (0 : Fin m) = j := Fin.ext (by simp [h])
      simp [h, e0]
    · have e0 : (0 : Fin m) ≠ j := fun e => h (by rw [← e]; simp)
      simp [h, e0]

theorem embedF_eLo_upd {m : ℕ} [NeZero m] {hm : m + 1 ≤ 256} (h1 : 1 < m) (a v a' v' : List Bool) :
    embedF (eLo m hm) (Function.update (io2 (R := 254) a [] []) 2 v) (sto [(⟨1, h1⟩, v'), (0, a')]) =
      Function.update (io2 (R := 254) a' [] []) 2 v' := by
  refine embedF_eq_of _ _ _ _ (fun j => ?_) (fun t ht => ?_)
  · rw [← upd_eLo (hm := hm) h1 a' v']
  · have h0 : t.val ≠ 0 := fun h => ht 0 (Fin.ext (by rw [eLo_val]; simp [h]))
    have h2 : t ≠ 2 := fun h => ht ⟨1, h1⟩ (Fin.ext (by rw [eLo_val, h]; simp))
    simp only [Function.update_apply, h2, if_false, io2, h0]

/-- Normalize association-list stores. -/
macro "norm_sto" : tactic =>
  `(tactic| try simp only [update_sto, tmplS_sto, sto_cons, sto_nil, reduceIte, Fin.reduceEq,
    List.drop_zero, List.nil_append, List.reverse_cons, List.reverse_nil, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.length_replicate, List.singleton_append])

end AdvancedEncryption.RingBTVW.Prog
