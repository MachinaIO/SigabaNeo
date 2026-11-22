import PE.Impl.DualUse.Prog.WfB
import PE.Impl.DualUse.Prog.KeySumStore
import SigabaNeo.Lib.Lattices.ProgAlgo.SLPPK

/-!
# The key row `B_f̂` block of `KeyGen`

`bfB gen W : XProg 256` writes the word of the key row `B_f̂ = keyMatrix mpk (predC C)` on tape `2`
from the word of a master secret key (tape `0`) and the gate list `gsW W (parse C)` of a window
predicate (tape `1`), all other tapes blank (`law_bfB`):

1. the `f̂` gate generator `gen` (framed by `eGen` as in the `W_f` block, `GenSpec`): the gate
   stream of `f̂` on `233`, a gate counter on `234`, the positions of the output wires on `4`;
2. the input store of `EvalF` on `232`: padding, the rows `B_j` (in the order of the codec) and the
   gadget row (`bfInsP`, the builder `bldP` of `PE.Impl.DualUse.Prog.WfIns`);
3. the templates of the BGG+ NAND of public keys `nandP` and of the evaluator, then
   `slpEvalP uN vE nandP` (`run_slpPK`);
4. the store moved to `3`, the templates of the key sum, `keySumP` on the tapes `2 … 87`
   (`run_keySumP_keyMatrix`);
5. every tape but `0` and `2` cleared.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo Matrix AdvancedEncryption.RingBTVW AdvancedEncryption.DualUse.Algo
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow
open scoped SigabaNeo.Tape.Prog

/-! ### Placements -/

/-- The tapes of `nandP`: `100 … 164`. -/
def uN : Fin 65 → Fin 256 := fun j => ⟨j.val + 100, by omega⟩

theorem uN_val (j : Fin 65) : (uN j).val = j.val + 100 := rfl

theorem uN_inj : Function.Injective uN := fun a b h => by
  simp only [uN, Fin.mk.injEq] at h; exact Fin.ext (by omega)

theorem placed_N : Placed (m := 62) uN vE where
  hu := uN_inj
  hv := vE_inj
  v12 := by decide
  v13 := by decide
  v14 := by decide
  disj := by
    intro i j h
    have h' := congrArg Fin.val h
    rw [uN_val] at h'
    fin_cases i <;> simp only [vE] at h' ⊢ <;> first | decide | (exfalso; revert h'; norm_num; omega)

/-- The tapes of `keySumP`: `2 … 87`. -/
def oB : Fin 86 → Fin 256 := fun j => ⟨j.val + 2, by omega⟩

theorem oB_inj : Function.Injective oB := fun a b h => by
  simp only [oB, Fin.mk.injEq] at h; exact Fin.ext (by omega)

theorem oB_val (j : Fin 86) : (oB j).val = j.val + 2 := rfl

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

/-! ### The program -/

/-- The templates of `nandP` (`NandPre` on `103 … 111`) and of the evaluator (`235`, `236`). -/
def tmplB (N K k W : ℕ) : List (Fin 256 × List Bool) :=
  [(103, rp K), (104, rp N), (105, rp (N * K)), (106, rp k), (107, rp (2 * k)), (108, rp 1),
    (109, rp (2 * k * N)), (110, rp (2 * k * (N * K))), (111, rp (2 * k * (2 * k * (N * K)))),
    (235, rp (2 * k * (N * K))), (236, rp W)]

/-- The templates of the key sum (`KTmpl` on `5 … 18`). -/
def tmplK (N K k W : ℕ) : List (Fin 256 × List Bool) :=
  [(5, rp K), (6, rp N), (7, rp (N * K)), (8, rp k), (9, rp (2 * k)), (10, rp (2 * k)),
    (11, rp (2 * k * N)), (12, rp (2 * k * (N * K))), (13, rp (2 * k * (2 * k * (N * K)))),
    (14, rp 1), (15, rp (1 * (2 * k) * (N * K))), (16, rp (1 * (2 * k) * N)), (17, rp W),
    (18, rp (2 * k * (N * K)))]

variable (hk c) in
/-- **The input store of `EvalF`**: the rows `B_j` read from the word of the public key. -/
noncomputable def bfInsP : Prog 9 :=
  bldP (offB c) 0 (lenA N K k 1) 0 0 (lenA N K k 1) (fun _ => clr 2) (Enum.list (α := JT N K k hk))
    (gadW N K k)

variable (hk c) in
/-- **The coin-free part of the block.** -/
noncomputable def bfRest (W : ℕ) : Prog 256 :=
  Prog.map iT (bfInsP hk c) ⨾ putsP (tmplB N K k W) ⨾ slpEvalP uN vE nandP ⨾ cp 3 232 ⨾ clr 232 ⨾
    putsP (tmplK N K k W) ⨾ Prog.map oB keySumP ⨾ clrsP clrW

variable (hk c) in
/-- **The `B_f̂` block.** -/
noncomputable def bfB (gen : XProg 136) (W : ℕ) : XProg 256 :=
  XProg.seq (XProg.frame eGen gen) (XProg.prog (bfRest hk c W))

/-! ### The rows `B_j` in the word of a public key -/

theorem pk_dropB (mpk : PK hk c) (r : List Bool) :
    ((pkEnc hk c).enc mpk ++ r).drop (offB c) =
      (Enum.list (α := JT N K k hk)).flatMap (fun j => rowW N K k (mpk.Bj j)) ++
        ((ringEnc N K).enc mpk.p ++ r) := by
  have e : (pkEnc hk c).enc mpk = (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc mpk.B₀ ++
      ((matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc mpk.B₁ ++
        ((FixedEnc.fun (α := JT N K k hk) (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k))).enc
          mpk.Bj ++ (ringEnc N K).enc mpk.p)) := rfl
  rw [e, List.append_assoc, List.append_assoc, offB, drop_app2 (length_enc_fixLen _ _)
    (length_enc_fixLen _ _), fun_enc_flatMap, List.append_assoc]
  congr 1
  refine List.flatMap_congr fun j _ => ?_
  rw [matEnc_cols]
  rfl

/-- The inputs of `EvalF`: the rows `B_j` in the order of the codec. -/
def insB (mpk : PK hk c) : List (List Bool) :=
  (Enum.list (α := JT N K k hk)).map fun j => rowW N K k (mpk.Bj j)

theorem run_bfInsP (mpk : PK hk c) (r : List Bool) (s : Store 9)
    (h0 : s 0 = (pkEnc hk c).enc mpk ++ r) (hb : ∀ t : Fin 9, 3 ≤ t.val → s t = []) :
    run (bfInsP hk c) s = Function.update s 1 (s 1 ++
      List.replicate ((s 2).length * lenA N K k 1) false ++ (insB mpk ++ [gadW N K k]).flatten) := by
  rw [bfInsP]
  refine Eq.trans (run_bldP (α := JT N K k hk) (P := fun _ => clr 2)
    (fA := fun j => rowW N K k (mpk.Bj j)) (fB := fun _ => []) (fC := fun _ => [])
    (sd := (pkEnc hk c).enc mpk ++ r) (rB := (pkEnc hk c).enc mpk ++ r) (fun _ => length_rowW' _) (fun _ => rfl) (fun _ => rfl)
    (fun _ r' _ _ => by simp [run_clear]) _ _ (by rw [length_gadW, lenA]; ring)
    (pk_dropB mpk r) (by simp) s h0 hb) ?_
  simp [insB]

theorem coinFree_bfRest (W : ℕ) : (bfRest hk c W).CoinFree := by
  have h1 := coinFree_map iT (coinFree_bldP (P := fun (_ : JT N K k hk) => clr (2 : Fin 3))
    (fun _ => rfl) (Enum.list (α := JT N K k hk)) (gadW N K k) (oA := offB c) (oB := 0)
    (a := lenA N K k 1) (b := 0) (m := 0) (V := lenA N K k 1))
  have h2 := coinFree_putsP (tmplB N K k W)
  have h3 := coinFree_of_noGrow _ (noGrow_slpEvalP (u := uN) (v := vE) (stepSpec_nandP N K k))
  have h4 := coinFree_putsP (tmplK N K k W)
  have h5 := coinFree_map oB (coinFree_of_noGrow _ noGrow_keySumP)
  have h6 := coinFree_clrsP clrW
  simp only [CoinFree] at h1 h2 h3 h4 h5 h6
  simp [CoinFree, bfRest, bfInsP, coinFreeB, h1, h2, h3, h4, h5, h6]

theorem wf_bfRest (W : ℕ) : (bfRest hk c W).WF :=
  ⟨WF.map iT_inj (wf_bldP (P := fun (_ : JT N K k hk) => clr (2 : Fin 3)) (fun _ => trivial) _ _), wf_putsP _, wf_slpEvalP placed_N (stepSpec_nandP N K k),
    trivial, trivial, wf_putsP _, WF.map oB_inj wf_keySumP, wf_clrsP _⟩

theorem keys_tmplB (W : ℕ) : (tmplB N K k W).map (fun x => x.1.val) =
    [103, 104, 105, 106, 107, 108, 109, 110, 111, 235, 236] := rfl

theorem keys_tmplK (W : ℕ) : (tmplK N K k W).map (fun x => x.1.val) =
    [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] := rfl

/-- **The law of the `B_f̂` block**, for every generator meeting `GenSpec`, on the gate lists with
`Ok` whose positions `W` bounds (`WOk`). -/
theorem law_bfB {gen : XProg 136} {W : ℕ} {Ok : GateList → Prop} (hg : GenSpec N hk gen W Ok)
    (msk : SKey hk c) (C : List Bool) (hok : Ok (parse C)) (hw : WOk N hk W (parse C)) :
    (bfB hk c gen W).law (io2 (R := 254) ((mskEnc hk c).enc msk) (SigabaNeo.Tape.Prog.gsW W (parse C)) []) =
      PMF.pure (Function.update (io2 (R := 254) ((mskEnc hk c).enc msk) [] []) 2
        (rowW N K k (keyMatrix msk.1 (predC C)))) := by
  rw [bfB, XProg.law_seq, law_genStep hg hok _ (by simp [io2]) (fun j hj => by
      have hv := eGen_val j
      simp only [eGv] at hv
      simp only [io2]
      rw [if_neg (by split_ifs at hv <;> omega), if_neg (by split_ifs at hv <;> omega)]),
    PMF.pure_bind, XProg.law_prog, law_eq_run_of_coinFree _ (coinFree_bfRest W)]
  congr 1
  simp only [bfRest, run_seq]
  -- the generator
  generalize hs1 : Function.update (Function.update (Function.update (io2 (R := 254)
    ((mskEnc hk c).enc msk) (SigabaNeo.Tape.Prog.gsW W (parse C)) []) 233
    (gatesW (ixT N K k hk) (nT N K k hk) W (fhatP N K k (parse C)) 0)) 234
    (rp (fhatP N K k (parse C)).length)) 4
    (posW W N k (fhatPos K (ordT₀ N k) (ordO₀ N k) (parse C) (ixT N K k hk) (nT N K k hk))) = s1
  have B1 : Blk s1 [4, 234, 233, 0, 1] := by
    rw [← hs1]; exact (((blk_io2 _ _).upd 233 _).upd 234 _).upd 4 _
  have f1 : s1 0 = (mskEnc hk c).enc msk ∧
      s1 233 = gatesW (ixT N K k hk) (nT N K k hk) W (fhatP N K k (parse C)) 0 ∧
      s1 234 = rp (fhatP N K k (parse C)).length ∧
      s1 4 = posW W N k (fhatPos K (ordT₀ N k) (ordO₀ N k) (parse C) (ixT N K k hk) (nT N K k hk)) := by
    subst hs1; simp [io2]
  clear hs1
  obtain ⟨f10, f1233, f1234, f14⟩ := f1
  -- the input store of `EvalF`
  have h0 : (s1 ∘ iT) 0 = (pkEnc hk c).enc msk.1 ++
      (rowW N K k msk.2.1 ++ (ringEnc N K).enc msk.2.2) := by
    show s1 0 = _; rw [f10, mskEnc_eq]
  rw [run_map_eq_update iT_inj _ s1 1 _ (run_bfInsP msk.1 _ (s1 ∘ iT) h0
      (fun t ht => B1 _ (by fin_cases t <;> simp_all [iT]))),
    show iT 1 = 232 from rfl, show (s1 ∘ iT) 1 = s1 232 from rfl,
    show (s1 ∘ iT) 2 = s1 234 from rfl, B1 232 (by decide), f1234, List.length_replicate,
    List.nil_append]
  generalize hs3 : Function.update s1 232 (rp ((fhatP N K k (parse C)).length * lenA N K k 1) ++
    (insB msk.1 ++ [gadW N K k]).flatten) = s3
  have B3 : Blk s3 [232, 4, 234, 233, 0, 1] := by rw [← hs3]; exact B1.upd 232 _
  have f3 : s3 0 = (mskEnc hk c).enc msk ∧
      s3 232 = rp ((fhatP N K k (parse C)).length * lenA N K k 1) ++
        (insB msk.1 ++ [gadW N K k]).flatten ∧
      s3 233 = gatesW (ixT N K k hk) (nT N K k hk) W (fhatP N K k (parse C)) 0 ∧
      s3 234 = rp (fhatP N K k (parse C)).length ∧
      s3 4 = posW W N k (fhatPos K (ordT₀ N k) (ordO₀ N k) (parse C) (ixT N K k hk) (nT N K k hk)) := by
    subst hs3; simp [Function.update_apply, f10, f1233, f1234, f14]
  clear hs3 B1 f10 f1233 f1234 f14
  obtain ⟨f30, f3232, f3233, f3234, f34⟩ := f3
  -- `EvalF`
  have hins : ∀ x ∈ insB (hk := hk) (c := c) msk.1, x.length = 2 * k * (N * K) := by
    intro x hx
    simp only [insB, List.mem_map] at hx
    obtain ⟨j, -, rfl⟩ := hx
    exact Algo.length_rowW _
  have hn : (insB (hk := hk) (c := c) msk.1).length = nT N K k hk := by simp [insB]
  rw [run_putsP (tmplB N K k W), run_slpPK placed_N (putsS (tmplB N K k W) s3)
    (fun i hi => by
      fin_cases i <;> simp at hi <;>
        (rw [putsS_out (keys_tmplB W) _ _ (by decide)]; exact B3 _ (by decide)))
    ⟨fun i hi => by
        show putsS _ s3 (uN i) = []
        rw [putsS_out (keys_tmplB W) _ _ (by rw [uN_val]; simp <;> omega)]
        exact B3 _ (by rw [uN_val]; simp <;> omega),
      by show (putsS _ s3 103).length = K; simp [putsS, tmplB],
      by show (putsS _ s3 104).length = N; simp [putsS, tmplB],
      by show (putsS _ s3 105).length = N * K; simp [putsS, tmplB],
      by show (putsS _ s3 106).length = k; simp [putsS, tmplB],
      by show (putsS _ s3 107).length = 2 * k; simp [putsS, tmplB],
      by show (putsS _ s3 108).length = 1; simp [putsS, tmplB],
      by show (putsS _ s3 109).length = 2 * k * N; simp [putsS, tmplB],
      by show (putsS _ s3 110).length = 2 * k * (N * K); simp [putsS, tmplB],
      by show (putsS _ s3 111).length = 2 * k * (2 * k * (N * K)); simp [putsS, tmplB]⟩
    (by show (putsS _ s3 235).length = _; simp [putsS, tmplB])
    (by show (putsS _ s3 236).length = W; simp [putsS, tmplB])
    hins hn (fun j => enumIx_lt (α := JT N K k hk) j) (ix := ixT N K k hk)
    (fhatP N K k (parse C)) hw.hT (rp ((fhatP N K k (parse C)).length * lenA N K k 1))
    (by rw [List.length_replicate, lenA]; ring)
    (by show putsS _ s3 232 = _; rw [putsS_out (keys_tmplB W) _ _ (by decide), f3232])
    (by show putsS _ s3 233 = _; rw [putsS_out (keys_tmplB W) _ _ (by decide), f3233])
    (by show (putsS _ s3 234).length = _
        rw [putsS_out (keys_tmplB W) _ _ (by decide), f3234, List.length_replicate])]
  generalize hst : (insB (hk := hk) (c := c) msk.1 ++ [gadW N K k] ++ SLP.values
    (fun i => (insB (hk := hk) (c := c) msk.1).getD (ixT N K k hk i) []) (gadW N K k)
    (nandPKW N K k) (fhatP N K k (parse C))).flatten = st
  generalize hs5 : Function.update (Function.update (Function.update (putsS (tmplB N K k W) s3)
    (vE 0) st) (vE 1) []) (vE 2) [] = s5
  have B5 : Blk s5 ([234, 233, 232] ++ [103, 104, 105, 106, 107, 108, 109, 110, 111, 235, 236] ++
      [232, 4, 234, 233, 0, 1]) := by
    rw [← hs5]
    refine Blk.mono ((((Blk.puts _ B3).upd _ _).upd _ _).upd _ _) ?_
    rw [keys_tmplB]; decide
  have f5 : s5 0 = (mskEnc hk c).enc msk ∧ s5 232 = st ∧ s5 233 = [] ∧ s5 234 = [] ∧
      s5 4 = posW W N k (fhatPos K (ordT₀ N k) (ordO₀ N k) (parse C) (ixT N K k hk) (nT N K k hk)) := by
    subst hs5
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Function.update_apply, show vE 0 = 232 from rfl, show vE 1 = 233 from rfl,
        show vE 2 = 234 from rfl] <;> simp
    all_goals (rw [putsS_out (keys_tmplB W) _ _ (by decide)]; assumption)
  clear hs5 f30 f3232 f3233 f3234 f34 B3
  obtain ⟨f50, f5232, f5233, f5234, f54⟩ := f5
  -- the key sum
  simp only [run_copy, run_clear, run_putsP, f5232]
  generalize hm5 : Function.update (Function.update s5 3 st) 232 [] = m5
  have Bm5 : Blk m5 (232 :: 3 :: ([234, 233, 232] ++ [103, 104, 105, 106, 107, 108, 109, 110, 111,
      235, 236] ++ [232, 4, 234, 233, 0, 1])) := by
    rw [← hm5]; exact (B5.upd 3 _).upd 232 _
  have gm : m5 0 = (mskEnc hk c).enc msk ∧ m5 3 = st ∧
      m5 4 = posW W N k (fhatPos K (ordT₀ N k) (ordO₀ N k) (parse C) (ixT N K k hk) (nT N K k hk)) := by
    subst hm5; simp [Function.update_apply, f50, f54]
  clear hm5 B5 f50 f5232 f5233 f5234 f54
  obtain ⟨g0, g3, g4⟩ := gm
  have hBK := Blk.puts (tmplK N K k W) Bm5
  rw [keys_tmplK] at hBK
  have m := fun t w (h : (t, w) ∈ tmplK N K k W) =>
    tmpl_of_mem (fun x hx => putsS_mem (tmplK N K k W) m5 (by rw [keys_tmplK]; decide) x hx) h
  rw [run_map_eq_update oB_inj keySumP (putsS (tmplK N K k W) m5) 0 _ (run_keySumP_keyMatrix hk msk.1 (parse C) hins hn
    (fun j => enumIx_lt (α := JT N K k hk) j)
    (fun j => by
      simp only [insB]
      exact getD_enumIx (α := JT N K k hk) (fun j => rowW N K k (msk.1.Bj j)) [] j)
    hw.hT (putsS (tmplK N K k W) m5 ∘ oB)
    { h3 := by show (putsS _ m5 5).length = K; rw [m 5 (rp K) (by simp [tmplK])]; simp
      h4 := by show (putsS _ m5 6).length = N; rw [m 6 (rp N) (by simp [tmplK])]; simp
      h5 := by show (putsS _ m5 7).length = N * K; rw [m 7 (rp (N * K)) (by simp [tmplK])]; simp
      h6 := by show (putsS _ m5 8).length = k; rw [m 8 (rp k) (by simp [tmplK])]; simp
      h7 := by show (putsS _ m5 9).length = 2 * k; rw [m 9 (rp (2 * k)) (by simp [tmplK])]; simp
      h8 := by show (putsS _ m5 10).length = 2 * k; rw [m 10 (rp (2 * k)) (by simp [tmplK])]; simp
      h9 := by show (putsS _ m5 11).length = 2 * k * N; rw [m 11 (rp (2 * k * N)) (by simp [tmplK])]; simp
      h10 := by
        show (putsS _ m5 12).length = 2 * k * (N * K)
        rw [m 12 (rp (2 * k * (N * K))) (by simp [tmplK])]; simp
      h11 := by
        show (putsS _ m5 13).length = 2 * k * (2 * k * (N * K))
        rw [m 13 (rp (2 * k * (2 * k * (N * K)))) (by simp [tmplK])]; simp
      h12 := by show (putsS _ m5 14).length = 1; rw [m 14 (rp 1) (by simp [tmplK])]; simp
      h13 := by
        show (putsS _ m5 15).length = 1 * (2 * k) * (N * K)
        rw [m 15 (rp (1 * (2 * k) * (N * K))) (by simp [tmplK])]; simp
      h14 := by
        show (putsS _ m5 16).length = 1 * (2 * k) * N
        rw [m 16 (rp (1 * (2 * k) * N)) (by simp [tmplK])]; simp
      h15 := by show (putsS _ m5 17).length = W; rw [m 17 (rp W) (by simp [tmplK])]; simp
      h16 := by
        show (putsS _ m5 18).length = 2 * k * (N * K)
        rw [m 18 (rp (2 * k * (N * K))) (by simp [tmplK])]; simp
      h17 := by show (putsS _ m5 19).length = 0; rw [hBK 19 (by decide)]; rfl }
    (fun t ht => hBK (oB t) (by rw [oB_val]; simp; omega))
    (by show putsS _ m5 3 = _; rw [putsS_out (keys_tmplK W) _ _ (by decide), g3, ← hst]; rfl)
    (by show putsS _ m5 4 = _; rw [putsS_out (keys_tmplK W) _ _ (by decide), g4]; rfl))]
  rw [show oB 0 = 2 from rfl]
  -- the final clearing
  rw [run_clrsP]
  funext t
  by_cases t0 : t = 0
  · subst t0
    simp [mem_clrW, io2, putsS_out (keys_tmplK W) _ 0 (by decide), g0]
  · by_cases t2 : t = 2
    · subst t2; simp [mem_clrW, io2, predC]
    · have t0' : t.val ≠ 0 := fun e => t0 (Fin.ext e)
      simp [mem_clrW, t0, t2, io2, t0']

end AdvancedEncryption.DualUse.Prog
