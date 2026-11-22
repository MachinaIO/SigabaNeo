import PE.Impl.DualUse.Prog.KeyP
import PE.Impl.DualUse.Algo.KeyMatrix
import PE.Impl.DualUse.Prog.KeyTryRealLaw
import SigabaNeo.Lib.Machines.Prog.FrameIO
import SigabaNeo.Lib.Machines.Prog.LoadB

/-!
# The machine of `KeyGen`, compiled from a tape program

`keyGenP bfX W cf : XProg 256` computes `KeyGen` from its input `encodeTuple [pw, msk, C]` (tape
`255`, at most `n + 1` bits by the bounded loader) and writes `encodeTuple [sk]` on tape `0`:

1. the length guard `leP n` (`n = nKG`, the length of the inputs with `|C| ≤ c.L`): longer inputs
   (their predicates are longer than `c.L`) are answered by the empty tuple;
2. the input is parsed (`unfrP` three times): `msk` on tape `0`, `C` on tape `1`;
3. the front end `frontP c.L W` (`PE.Gates.DateWindow`): `true :: gsW W (parse C)` for a window
   predicate, `[false]` for another short one, `[]` for a long one;
4. **window predicates**: the key row `B_f̂` (the block `bfX`, a parameter meeting `BfSpec`; one
   instance is `bfB`, `PE.Impl.DualUse.Prog.BfB`), then one try of box rejection with the real
   trapdoor and fresh coins (`ProgKeyR.keyTryRCoinsP`), and the output framed (`frP`);
   **other short predicates**: the framed dummy key; **long predicates**: the empty tuple;
5. every tape but `0` cleared.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo Matrix AdvancedEncryption.RingBTVW AdvancedEncryption.DualUse.Algo
  Turing Cslib
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow
open scoped SigabaNeo.Tape.Prog

/-! ### Parsing -/

/-- The tapes of `unfrP` with destination `d`. -/
def uU (d : Fin 256) : Fin 4 → Fin 256 := ![255, d, 251, 252]

theorem run_unfrAt {d : Fin 256} (hu : Function.Injective (uU d)) (s : Store 256)
    (u r : List Bool) (h : s 255 = MultiTapeTM.frame u ++ r) (h252 : s 252 = []) :
    run (Prog.map (uU d) unfrP) s =
      Function.update (Function.update (Function.update s 255 r) d (s d ++ u)) 251 [] := by
  rw [run_map hu, run_unfrP (s ∘ uU d) u r h h252, extend_update hu, extend_update hu,
    extend_update hu, extend_comp_self]
  rfl

/-- Parse `encodeTuple [pw, a, b]`: `a` on tape `0`, `b` on tape `1`. -/
def parseP : Prog 256 :=
  clr 254 ⨾ Prog.map (uU 253) unfrP ⨾ Prog.map (uU 0) unfrP ⨾ Prog.map (uU 1) unfrP ⨾ clr 253 ⨾
    clr 255

theorem run_parseP (p a b : List Bool) (f : List Bool) :
    run parseP (Function.update (Function.update (fun _ => []) 255 (SigabaNeo.encodeTuple [p, a, b]))
      254 f) = io2 (R := 254) a b [] := by
  simp only [parseP, run_seq, run_clear]
  have e : SigabaNeo.encodeTuple [p, a, b] =
      MultiTapeTM.frame p ++ (MultiTapeTM.frame a ++ (MultiTapeTM.frame b ++ [])) := by
    simp [encodeTuple_cons, encodeTuple_nil]
  rw [run_unfrAt (d := 253) (by decide) _ p (MultiTapeTM.frame a ++ (MultiTapeTM.frame b ++ []))
    (by simp [e]) (by simp)]
  rw [run_unfrAt (d := 0) (by decide) _ a (MultiTapeTM.frame b ++ []) (by simp) (by simp)]
  rw [run_unfrAt (d := 1) (by decide) _ b [] (by simp) (by simp)]
  funext t
  by_cases h0 : t = 0
  · subst h0; simp [io2]
  by_cases h1 : t = 1
  · subst h1; simp [io2]
  have h0' : t.val ≠ 0 := fun h => h0 (Fin.ext h)
  have h1' : t.val ≠ 1 := fun h => h1 (Fin.ext h)
  simp only [Function.update_apply, io2, h0, h1, h0', h1', if_false]
  split_ifs <;> rfl

/-! ### The window branch -/

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

/-- The tapes of `frP` on tape `0`. -/
def uF : Fin 3 → Fin 256 := ![0, 253, 254]

theorem run_frAt (s : Store 256) (h254 : s 254 = []) :
    run (Prog.map uF frP) s = Function.update (Function.update s 0 (MultiTapeTM.frame (s 0))) 253 [] := by
  rw [run_map (by decide), run_frP (s ∘ uF) h254, extend_update (by decide), extend_update (by decide),
    extend_comp_self]
  rfl

/-- The tapes of the real key try: the first `101`. -/
def eKR : Fin 101 ↪ Fin 256 := Fin.castLEEmb (by norm_num)

theorem eKR_val (j : Fin 101) : (eKR j).val = j.val := rfl

variable (hk c) in
/-- The templates of the real key try: those of the simulated one and `92`, `93`, `100`. -/
def keyTmplR (cf : KeyCfg) : List (Fin 256 × ℕ) :=
  keyTmpl hk c cf ++ [(92, 2 * k * N), (93, 2 * k * (2 * k * (N * K))), (100, 2 * k)]

/-- The tapes cleared after the key try. -/
def keyClrR : List (Fin 256) := keyClr ++ [90, 91, 92, 93, 100, 253]

variable (hk c) in
/-- **The key-row block**: from the word of a master secret key (tape `0`) and the gate list
`gsW W (parse C)` of a window predicate of at most `c.L` bits (tape `1`), the word of the key row
`B_f̂ = keyMatrix mpk (predC C)` on tape `2`, the master key kept on tape `0`, every other tape
blank. -/
structure BfSpec (bfX : XProg 256) (W : ℕ) : Prop where
  wf : bfX.WF
  law : ∀ (msk : SKey hk c) (C : List Bool), C.length ≤ c.L → (∃ w : Window, winWord w = C) →
    bfX.law (io2 (R := 254) ((mskEnc hk c).enc msk) (SigabaNeo.Tape.Prog.gsW W (parse C)) []) =
      PMF.pure (Function.update (io2 (R := 254) ((mskEnc hk c).enc msk) [] []) 2
        (rowW N K k (keyMatrix msk.1 (predC C))))

variable (hk c) in
/-- The trapdoor `(e, t)` read from the word of the master secret key (tape `0`) onto `90`, `91`. -/
def etP : XProg 256 :=
  XProg.seq (XProg.prog (cp 91 0 ⨾ tailsP 91 (lenPK hk c + 2 * k * (N * K)) ⨾ cp 102 0 ⨾
    tailsP 102 (lenPK hk c)))
    (XProg.seq (prefP (2 * k * (N * K)) 102 90 103 104) (XProg.prog (clr 102)))

variable (hk c) in
/-- **The window branch.** -/
noncomputable def winR (bfX : XProg 256) (W : ℕ) (cf : KeyCfg) : XProg 256 :=
  XProg.seq (XProg.prog (.prim (.tail 1))) <| XProg.seq bfX <|
  XProg.seq (prefP (lenPK hk c) 0 1 100 101) <| XProg.seq (etP hk c) <|
  XProg.seq (putW 4 cf.sW) <| XProg.seq (putW 5 (powW K (cf.B - 1))) <|
  XProg.seq (tmplP 120 (keyTmplR hk c cf)) <|
  XProg.seq (XProg.frame eKR (XProg.prog ProgKeyR.keyTryRCoinsP)) <|
  XProg.seq (XProg.prog (Prog.map uF frP)) (clearL keyClrR)

theorem coinFree_etPre : (cp 91 0 ⨾ tailsP 91 (lenPK hk c + 2 * k * (N * K)) ⨾ cp 102 0 ⨾
    tailsP (102 : Fin 256) (lenPK hk c)).CoinFree := by
  have h1 := coinFree_tailsP (91 : Fin 256) (lenPK hk c + 2 * k * (N * K))
  have h2 := coinFree_tailsP (102 : Fin 256) (lenPK hk c)
  simp only [CoinFree] at h1 h2
  simp [CoinFree, coinFreeB, h1, h2]

theorem law_etP (s : Store 256) (h90 : s 90 = []) (h102 : s 102 = []) (h103 : s 103 = [])
    (h104 : s 104 = []) :
    (etP hk c).law s = PMF.pure (Function.update (Function.update s 91
      ((s 0).drop (lenPK hk c + 2 * k * (N * K)))) 90
      (((s 0).drop (lenPK hk c)).take (2 * k * (N * K)))) := by
  rw [etP, XProg.law_seq_pure (by rw [XProg.law_prog, law_eq_run_of_coinFree _ coinFree_etPre]),
    XProg.law_seq_pure (law_prefP _ (by decide) (by decide) (by decide) (by decide) _
      (by simp [run_tailsP, Function.update_apply, h103]) (by simp [run_tailsP, Function.update_apply, h104])),
    XProg.law_prim]
  congr 1
  simp only [run_seq, run_copy, run_tailsP, Prim.apply]
  funext t
  simp only [Function.update_apply]
  split_ifs <;> simp_all

variable (hk c) in
/-- The store before the real key try. -/
def winSR (mw bw : List Bool) (cf : KeyCfg) : Store 256 :=
  tmplS (keyTmplR hk c cf) (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (io2 (R := 254) mw [] []) 2 bw) 1 (mw.take (lenPK hk c))) 91
    (mw.drop (lenPK hk c + 2 * k * (N * K)))) 90 ((mw.drop (lenPK hk c)).take (2 * k * (N * K)))) 4
    cf.sW) 5 (powW K (cf.B - 1)))

theorem keyTmplR_keys (cf : KeyCfg) : (keyTmplR hk c cf).map (fun x => x.1.val) =
    [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 92, 93, 100] := rfl

theorem tmplS_out' {l : List (Fin 256 × ℕ)} {ks : List ℕ} (hks : l.map (fun x => x.1.val) = ks)
    (s : Store 256) (t : Fin 256) (ht : t.val ∉ ks) : tmplS l s t = s t :=
  tmplS_apply_of_not_mem l s t fun x hx e => ht (by rw [← hks, ← e]; exact List.mem_map_of_mem hx)

/-- The window branch from the generator to the store before the try. -/
theorem law_winPrep {bfX : XProg 256} {W : ℕ} (hbf : BfSpec hk c bfX W)
    (cf : KeyCfg) (msk : SKey hk c) (C : List Bool) (hL : C.length ≤ c.L)
    (hC : ∃ w : Window, winWord w = C)
    (X : XProg 256) :
    (XProg.seq (XProg.prog (.prim (.tail 1))) <| XProg.seq bfX <|
      XProg.seq (prefP (lenPK hk c) 0 1 100 101) <| XProg.seq (etP hk c) <|
      XProg.seq (putW 4 cf.sW) <| XProg.seq (putW 5 (powW K (cf.B - 1))) <|
      XProg.seq (tmplP 120 (keyTmplR hk c cf)) X).law
        (io2 (R := 254) ((mskEnc hk c).enc msk) (true :: SigabaNeo.Tape.Prog.gsW W (parse C)) []) =
      X.law (winSR hk c ((mskEnc hk c).enc msk) (rowW N K k (keyMatrix msk.1 (predC C))) cf) := by
  have e1 : (Prim.tail (1 : Fin 256)).apply
      (io2 (R := 254) ((mskEnc hk c).enc msk) (true :: SigabaNeo.Tape.Prog.gsW W (parse C)) []) =
      io2 (R := 254) ((mskEnc hk c).enc msk) (SigabaNeo.Tape.Prog.gsW W (parse C)) [] := by
    funext t
    simp only [Prim.apply, Function.update_apply, io2]
    split_ifs <;> first | rfl | (exfalso; simp_all [Fin.ext_iff])
  rw [XProg.law_seq_pure (XProg.law_prim _ _), e1, XProg.law_seq_pure (hbf.law msk C hL hC),
    XProg.law_seq_pure (law_prefP _ (by decide) (by decide) (by decide) (by decide) _
      (by simp [Function.update_apply, io2]) (by simp [Function.update_apply, io2])),
    XProg.law_seq_pure (law_etP _ (by simp [Function.update_apply, io2])
      (by simp [Function.update_apply, io2]) (by simp [Function.update_apply, io2])
      (by simp [Function.update_apply, io2])),
    XProg.law_seq_pure (law_putW _ _ _), XProg.law_seq_pure (law_putW _ _ _),
    XProg.law_seq_pure (law_tmplP _ _ _ (by simp [Function.update_apply, io2])
      (fun x hx e => by
        have := List.mem_map_of_mem (f := fun x : Fin 256 × ℕ => x.1.val) hx
        rw [keyTmplR_keys, e] at this; simp at this))]
  congr 1

theorem msk_parts (msk : SKey hk c) :
    ((mskEnc hk c).enc msk).take (lenPK hk c) = (pkEnc hk c).enc msk.1 ∧
    ((mskEnc hk c).enc msk).drop (lenPK hk c + 2 * k * (N * K)) = (ringEnc N K).enc msk.2.2 ∧
    (((mskEnc hk c).enc msk).drop (lenPK hk c)).take (2 * k * (N * K)) = rowW N K k msk.2.1 := by
  rw [mskEnc_eq]
  have hp : ((pkEnc hk c).enc msk.1).length = lenPK hk c := length_enc_fixLen _ _
  have he : (rowW N K k msk.2.1).length = 2 * k * (N * K) := Algo.length_rowW _
  refine ⟨List.take_left' hp, ?_, ?_⟩
  · rw [← List.drop_drop, List.drop_left' hp, List.drop_left' he]
  · rw [List.drop_left' hp, List.take_left' he]

theorem winSR_low {mw bw : List Bool} {cf : KeyCfg} (t : Fin 256)
    (ht : t.val ∉ [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 92, 93,
      100]) :
    winSR hk c mw bw cf t = Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (io2 (R := 254) mw [] []) 2 bw) 1 (mw.take (lenPK hk c))) 91
      (mw.drop (lenPK hk c + 2 * k * (N * K)))) 90 ((mw.drop (lenPK hk c)).take (2 * k * (N * K)))) 4
      cf.sW) 5 (powW K (cf.B - 1)) t :=
  tmplS_out' (keyTmplR_keys (hk := hk) (c := c) cf) _ t ht

theorem winSR_blank {mw bw : List Bool} {cf : KeyCfg} (t : Fin 256)
    (ht : t.val ∉ [0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
      24, 25, 90, 91, 92, 93, 100]) : winSR hk c mw bw cf t = [] := by
  rw [winSR_low t (fun h => ht (by simp at h ⊢; omega))]
  have h0 : t.val ≠ 0 := fun h => ht (by simp [h])
  have h1 : t.val ≠ 1 := fun h => ht (by simp [h])
  simp only [Function.update_apply, io2, h0, h1, if_false]
  split_ifs with a b c d e f <;> first | rfl | (exfalso; apply ht; subst_vars; decide)

theorem winSR_tmpl {mw bw : List Bool} {cf : KeyCfg} :
    let s := winSR hk c mw bw cf
    (s 6).length = K ∧ (s 7).length = N ∧ (s 8).length = N * K ∧ (s 9).length = cf.B ∧
    (s 10).length = (c.d + Algo.nT k) * N ∧ (s 11).length = (c.d + Algo.nT k) * N * K ∧
    (s 12).length = k ∧ (s 13).length = 2 * k ∧ (s 14).length = 1 ∧ (s 15).length = 1 ∧
    (s 16).length = c.d ∧ (s 17).length = Algo.nT k ∧ (s 18).length = c.d * (N * K) ∧
    (s 19).length = Algo.nT k * (N * K) ∧ (s 20).length = 2 * k * (N * K) ∧ (s 21).length = c.d * N ∧
    (s 22).length = lenPK hk c - N * K ∧ (s 23).length = lenPK hk c ∧
    (s 24).length = lenPK hk c + (c.d + Algo.nT k) * N * K + 2 * k * (N * K) ∧
    (s 25).length = cf.m ∧ (s 92).length = 2 * k * N ∧ (s 93).length = 2 * k * (2 * k * (N * K)) ∧
    (s 100).length = 2 * k := by
  intro s
  simp only [s, winSR, keyTmplR, keyTmpl, tmplS, List.foldl_cons, List.foldl_nil, List.cons_append,
    List.nil_append, Function.update_apply]
  simp

theorem coinFree_frAt : (Prog.map uF frP).CoinFree := coinFree_mapP uF coinFree_frP

/-- **The law of the window branch**: the image of `keyM msk C` under the framed key. -/
theorem law_winR {bfX : XProg 256} {W : ℕ} (hbf : BfSpec hk c bfX W)
    (cf : KeyCfg) (hcf : cf.Valid hk c) (msk : SKey hk c) (C : List Bool)
    (hL : C.length ≤ c.L) (hC : ∃ w : Window, winWord w = C) :
    (winR hk c bfX W cf).law
        (io2 (R := 254) ((mskEnc hk c).enc msk) (true :: SigabaNeo.Tape.Prog.gsW W (parse C)) []) =
      (DualUse.keyM hk c msk C).map fun sk =>
        io2 (R := 254) (MultiTapeTM.frame ((skEnc hk c).enc sk)) [] [] := by
  rw [winR, law_winPrep hbf cf msk C hL hC]
  set S := winSR hk c ((mskEnc hk c).enc msk) (rowW N K k (keyMatrix msk.1 (predC C))) cf with hS
  obtain ⟨p1, p2, p3⟩ := msk_parts (hk := hk) (c := c) msk
  have low := fun t ht => winSR_low (hk := hk) (c := c) (mw := (mskEnc hk c).enc msk)
    (bw := rowW N K k (keyMatrix msk.1 (predC C))) (cf := cf) t ht
  have bl := fun t ht => winSR_blank (hk := hk) (c := c) (mw := (mskEnc hk c).enc msk)
    (bw := rowW N K k (keyMatrix msk.1 (predC C))) (cf := cf) t ht
  obtain ⟨t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24,
    t25, t92, t93, t100⟩ := winSR_tmpl (hk := hk) (c := c) (mw := (mskEnc hk c).enc msk)
    (bw := rowW N K k (keyMatrix msk.1 (predC C))) (cf := cf)
  have s1 : S 1 = (pkEnc hk c).enc msk.1 := by
    rw [hS, low 1 (by decide)]; simp [Function.update_apply, p1]
  have s2 : S 2 = rowW N K k (keyMatrix msk.1 (predC C)) := by
    rw [hS, low 2 (by decide)]; simp [Function.update_apply]
  have s4 : S 4 = cf.sW := by rw [hS, low 4 (by decide)]; simp [Function.update_apply]
  have s5 : S 5 = powW K (cf.B - 1) := by rw [hS, low 5 (by decide)]; simp
  have s90 : S 90 = rowW N K k msk.2.1 := by
    rw [hS, low 90 (by decide)]; simp [Function.update_apply, p3]
  have s91 : S 91 = (ringEnc N K).enc msk.2.2 := by
    rw [hS, low 91 (by decide)]; simp [Function.update_apply, p2]
  rw [XProg.law_seq, XProg.law_frame, XProg.law_prog,
    ProgKeyR.law_keyTryRCoinsP_keyM hk cf hcf msk C hC (fun j => S (eKR j))
      (fun j h1 h2 => bl _ (by rw [eKR_val]; simp; omega))
      (fun j h1 h2 => bl _ (by rw [eKR_val]; simp; omega)) (bl 3 (by decide))
      s1 s2 s4 s90 s91 s5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25
      t92 t93 t100, PMF.map_comp, PMF.bind_map]
  rw [← PMF.bind_pure_comp]
  congr 1
  funext sk
  simp only [Function.comp_apply]
  rw [embedF_upd, embedF_comp, show eKR 0 = 0 from rfl, XProg.law_seq, XProg.law_prog,
    law_eq_run_of_coinFree _ coinFree_frAt,
    run_frAt _ (by rw [Function.update_of_ne (by decide), hS]; exact bl 254 (by decide)),
    PMF.pure_bind, law_clearL]
  congr 1
  have key : ∀ t : Fin 256, t.val ∈ [0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18,
      19, 20, 21, 22, 23, 24, 25, 90, 91, 92, 93, 100] → t ≠ 0 → t ∈ keyClrR := by
    intro t hmem ht
    have ht' : t.val ≠ 0 := fun e => ht (Fin.ext e)
    simp only [keyClrR, keyClr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      Fin.ext_iff, Fin.val_ofNat] at hmem ⊢
    omega
  funext t
  by_cases t0 : t = 0
  · subst t0; simp [keyClrR, keyClr, io2]
  · have t0' : t.val ≠ 0 := fun e => t0 (Fin.ext e)
    have rhs : io2 (R := 254) (MultiTapeTM.frame ((skEnc hk c).enc sk)) [] [] t = [] := by
      simp only [io2, t0', if_false]; split_ifs <;> rfl
    rw [rhs]
    split_ifs with hm
    · rfl
    · rw [Function.update_apply]
      split_ifs with h253
      · rfl
      · simp only [Function.update_of_ne t0]
        rw [hS]
        exact bl t (fun hmem => hm (key t hmem t0))

/-! ### The program -/

theorem law_dumBM (msk : SKey hk c) :
    (dumB hk c).law (io2 (R := 254) ((mskEnc hk c).enc msk) [false] []) =
      PMF.pure (io2 (R := 254) ((skEnc hk c).enc (msk.1, dummyKey c)) [] []) := by
  rw [dumB, XProg.law_seq_pure (XProg.law_prim _ _),
    XProg.law_seq_pure (law_prefP _ (by decide) (by decide) (by decide) (by decide) _
      (by simp [Prim.apply, Function.update_apply, io2]) (by simp [Prim.apply, Function.update_apply, io2])),
    XProg.law_seq_pure (law_putW _ _ _), XProg.law_seq_pure (XProg.law_prim _ _), XProg.law_prim]
  congr 1
  funext t
  simp only [Prim.apply, Function.update_apply]
  by_cases h2 : t = 2
  · subst h2; simp [io2]
  · by_cases h0 : t = 0
    · subst h0
      simp [io2, (msk_parts (hk := hk) (c := c) msk).1]
      rfl
    · by_cases h1 : t = 1
      · subst h1; simp [io2]
      · have : t.val ≠ 0 := fun h' => h0 (Fin.ext h')
        have : t.val ≠ 1 := fun h' => h1 (Fin.ext h')
        simp [h0, h1, h2, io2, *]

variable (hk c) in
/-- **The dummy branch**, framed. -/
noncomputable def dumR : XProg 256 := XProg.seq (dumB hk c) (XProg.prog (Prog.map uF frP))

theorem law_dumR (msk : SKey hk c) :
    (dumR hk c).law (io2 (R := 254) ((mskEnc hk c).enc msk) [false] []) =
      PMF.pure (io2 (R := 254) (MultiTapeTM.frame ((skEnc hk c).enc (msk.1, dummyKey c))) [] []) := by
  rw [dumR, XProg.law_seq_pure (law_dumBM msk), XProg.law_prog,
    law_eq_run_of_coinFree _ coinFree_frAt, run_frAt _ (by simp [io2])]
  congr 1
  funext t
  simp only [Function.update_apply, io2]
  split_ifs <;> simp_all

variable (hk c) in
/-- The branches on the output of the front end. -/
noncomputable def branchK (bfX : XProg 256) (W : ℕ) (cf : KeyCfg) : XProg 256 :=
  XProg.ifBit 1 (winR hk c bfX W cf) (XProg.ifBlank 1 longB (dumR hk c))

/-- The tapes of the guard. -/
def uL : Fin 3 → Fin 256 := ![255, 254, 253]

variable (hk c) in
/-- The longest input of `KeyGen` with a predicate of at most `c.L` bits. -/
def nKG : ℕ := (2 * (pw).length + 1) + (2 * fixLen (mskEnc hk c) + 1) + (2 * c.L + 1)

variable (hk c) in
/-- **The program of `KeyGen`**: input on tape `255`, output on tape `0`. -/
noncomputable def keyGenP (bfX : XProg 256) (W : ℕ) (cf : KeyCfg) : XProg 256 :=
  XProg.seq (XProg.prog (Prog.map uL (leP (nKG hk c))))
    (XProg.ifBlank 254 (XProg.prog (clr 255))
      (XProg.seq (XProg.prog parseP) <| XProg.seq (XProg.frame eFr (frontP c.L W)) <|
        XProg.seq (branchK hk c bfX W cf) (clearL clrAll)))

theorem run_leAt (n : ℕ) (s : Store 256) :
    run (Prog.map uL (leP n)) s = Function.update (Function.update s 254
      (if (s 255).length ≤ n then [true] else [])) 253 [] := by
  rw [run_map (by decide), run_leP n (s ∘ uL), extend_update (by decide), extend_update (by decide),
    extend_comp_self]
  rfl

theorem coinFree_leAt (n : ℕ) : (Prog.map uL (leP n)).CoinFree := coinFree_mapP uL (coinFree_leP n)

theorem length_encodeTuple_KG (msk : SKey hk c) (C : List Bool) :
    (SigabaNeo.encodeTuple [pw, (mskEnc hk c).enc msk, C]).length =
      (2 * (pw).length + 1) + (2 * fixLen (mskEnc hk c) + 1) + (2 * C.length + 1) := by
  simp only [encodeTuple_cons, encodeTuple_nil, List.length_append, length_frame,
    length_enc_fixLen, List.length_nil]
  omega

/-- **The law of `KeyGen` as a tape program**: from the first `nKG + 1` bits of the input, on
predicates of at most `c.L` bits the image of `keyM` under the framed key, otherwise the empty
tuple. -/
theorem law_keyGenP {bfX : XProg 256} {W : ℕ} (hbf : BfSpec hk c bfX W)
    (cf : KeyCfg) (hcf : cf.Valid hk c) (msk : SKey hk c) (C : List Bool) :
    (keyGenP hk c bfX W cf).law (inputStore 255
        ((SigabaNeo.encodeTuple [pw, (mskEnc hk c).enc msk, C]).take (nKG hk c + 1))) =
      if C.length ≤ c.L then (DualUse.keyM hk c msk C).map fun sk =>
        io2 (R := 254) (SigabaNeo.encodeTuple [(skEnc hk c).enc sk]) [] []
      else PMF.pure (io2 (R := 254) [] [] []) := by
  set x := SigabaNeo.encodeTuple [pw, (mskEnc hk c).enc msk, C] with hx
  have hlen := length_encodeTuple_KG (hk := hk) (c := c) msk C
  rw [keyGenP, XProg.law_seq, XProg.law_prog, law_eq_run_of_coinFree _ (coinFree_leAt _),
    PMF.pure_bind, run_leAt, XProg.law_ifBlank]
  by_cases hn : x.length ≤ nKG hk c
  · -- the input is read whole
    have ht : x.take (nKG hk c + 1) = x := List.take_of_length_le (by omega)
    rw [ht]
    have e255 : inputStore (k := 256) 255 x 255 = x := by simp [inputStore]
    rw [Function.update_of_ne (by decide), Function.update_self, e255, if_pos hn,
      if_neg (by simp)]
    have es : Function.update (Function.update (inputStore 255 x) 254 [true]) 253 [] =
        Function.update (Function.update (fun _ : Fin 256 => ([] : List Bool)) 255 x) 254 [true] := by
      funext t
      by_cases h253 : t = 253
      · subst h253; simp [inputStore]
      · simp [Function.update_apply, inputStore, h253]
    have hpc : parseP.CoinFree := by
      have h1 := coinFree_mapP (uU 253) coinFree_unfrP
      have h2 := coinFree_mapP (uU 0) coinFree_unfrP
      have h3 := coinFree_mapP (uU 1) coinFree_unfrP
      simp only [CoinFree] at h1 h2 h3
      simp [CoinFree, parseP, coinFreeB, h1, h2, h3]
    rw [es, XProg.law_seq, XProg.law_prog, law_eq_run_of_coinFree _ hpc, PMF.pure_bind,
      run_parseP, XProg.law_seq_pure (by rw [XProg.law_frame, io2_eFr, law_frontP, PMF.pure_map,
        embedF_eFr]), XProg.law_seq, branchK, XProg.law_ifBit]
    have e : (clearL clrAll).law ∘ (fun w => io2 (R := 254) w [] []) =
        PMF.pure ∘ (fun w => io2 (R := 254) w [] []) := funext law_clrAll
    by_cases hL : C.length ≤ c.L
    · rw [if_pos hL]
      by_cases hw : ∃ w : Window, winWord w = C
      · rw [frontV_win hL hw, if_pos (by simp [io2]), law_winR hbf cf hcf msk C hL hw,
          PMF.bind_map]
        have e' : (clearL clrAll).law ∘ (fun sk => io2 (R := 254)
            (MultiTapeTM.frame ((skEnc hk c).enc sk)) [] []) =
            PMF.pure ∘ (fun sk => io2 (R := 254) (SigabaNeo.encodeTuple [(skEnc hk c).enc sk]) [] []) := by
          funext sk; simp only [Function.comp_apply, law_clrAll, encodeTuple_single]
        rw [e', PMF.bind_pure_comp]
      · rw [frontV_short_not hL hw, if_neg (by simp [io2]), XProg.law_ifBlank, if_neg (by simp [io2]),
          law_dumR, PMF.pure_bind, law_clrAll, keyM_of_not hk c msk C hw, PMF.pure_map,
          encodeTuple_single]
    · rw [if_neg hL, frontV_long hL, if_neg (by simp [io2]), XProg.law_ifBlank, if_pos (by simp [io2]),
        law_longB, PMF.pure_bind, law_clrAll]
  · -- a longer input: its predicate is longer than `c.L`
    have hL : ¬ C.length ≤ c.L := by
      intro h; apply hn; rw [hlen, nKG]; omega
    have hlt : ¬ (x.take (nKG hk c + 1)).length ≤ nKG hk c := by
      rw [List.length_take]; omega
    have e255 : inputStore (k := 256) 255 (x.take (nKG hk c + 1)) 255 = x.take (nKG hk c + 1) := by
      simp [inputStore]
    rw [Function.update_of_ne (by decide), Function.update_self, e255, if_neg hlt, if_pos rfl,
      if_neg hL, XProg.law_prim]
    congr 1
    funext t
    simp only [Prim.apply, Function.update_apply, inputStore, io2]
    split_ifs <;> rfl

end AdvancedEncryption.DualUse.Prog

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.Prog Turing
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

/-! ### The machine -/

theorem wf_keyGenP {bfX : XProg 256} {W : ℕ} (hbf : BfSpec hk c bfX W) (cf : KeyCfg) :
    (keyGenP hk c bfX W cf).WF := by
  have hk1 : ∀ x ∈ keyTmplR hk c cf, x.1 ≠ (120 : Fin 256) := fun x hx e => by
    have := List.mem_map_of_mem (f := fun x : Fin 256 × ℕ => x.1.val) hx
    rw [keyTmplR_keys, e] at this; simp at this
  refine ⟨WF.map (by decide) (wf_leP _), trivial, ?_, ?_⟩
  · exact ⟨trivial, WF.map (by decide) wf_unfrP, WF.map (by decide) wf_unfrP,
      WF.map (by decide) wf_unfrP, trivial, trivial⟩
  · refine ⟨Gates.DateWindow.wf_frontP _ _, ⟨?_, wf_clearL _, ⟨trivial, wf_prefP _ _ _ _ _,
      wf_putW _ _, trivial, trivial⟩, WF.map (by decide) wf_frP⟩, wf_clearL _⟩
    · exact ⟨trivial, hbf.wf, wf_prefP _ _ _ _ _,
        ⟨⟨trivial, wf_tailsP _ _, trivial, wf_tailsP _ _⟩, wf_prefP _ _ _ _ _, trivial⟩,
        wf_putW _ _, wf_putW _ _, wf_tmplP _ _ hk1, ProgKeyR.wf_keyTryRCoinsP,
        WF.map (by decide) wf_frP, wf_clearL _⟩

variable (hk c) in
/-- **The machine of `KeyGen`**: input on tape `255` (at most `nKG + 1` bits loaded), output on
tape `0`. -/
noncomputable def keyMachineP (bfX : XProg 256) (W : ℕ) (cf : KeyCfg) : Machine :=
  (keyGenP hk c bfX W cf).toMachineB 255 0 (nKG hk c)

theorem run_keyMachineP {bfX : XProg 256} {W : ℕ} (hbf : BfSpec hk c bfX W) (cf : KeyCfg)
    (hcf : cf.Valid hk c) (msk : SKey hk c) (C : List Bool) :
    (keyMachineP hk c bfX W cf).run (SigabaNeo.encodeTuple [pw, (mskEnc hk c).enc msk, C]) =
      if C.length ≤ c.L then (DualUse.keyM hk c msk C).map fun sk =>
        SigabaNeo.encodeTuple [(skEnc hk c).enc sk]
      else PMF.pure (SigabaNeo.encodeTuple []) := by
  rw [keyMachineP, XProg.run_toMachineB _ (wf_keyGenP hbf cf), law_keyGenP hbf cf hcf msk C]
  split_ifs
  · rw [PMF.map_comp]; rfl
  · rw [PMF.pure_map]; rfl

theorem keyMachineP_short {bfX : XProg 256} {W : ℕ} (hbf : BfSpec hk c bfX W) (cf : KeyCfg)
    (hcf : cf.Valid hk c) (msk : SKey hk c) (C : List Bool) (hC : C.length ≤ c.L) :
    (keyMachineP hk c bfX W cf).run (SigabaNeo.encodeTuple [pw, (mskEnc hk c).enc msk, C]) =
      (DualUse.keyM hk c msk C).map fun sk => SigabaNeo.encodeTuple [(skEnc hk c).enc sk] := by
  rw [run_keyMachineP hbf cf hcf, if_pos hC]

theorem keyMachineP_long {bfX : XProg 256} {W : ℕ} (hbf : BfSpec hk c bfX W) (cf : KeyCfg)
    (hcf : cf.Valid hk c) (msk : SKey hk c) (C : List Bool) (hC : ¬ C.length ≤ c.L) :
    (keyMachineP hk c bfX W cf).run (SigabaNeo.encodeTuple [pw, (mskEnc hk c).enc msk, C]) =
      PMF.pure (SigabaNeo.encodeTuple []) := by
  rw [run_keyMachineP hbf cf hcf, if_neg hC]

end AdvancedEncryption.DualUse.Prog
