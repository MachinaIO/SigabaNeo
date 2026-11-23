import PE.Impl.DualUse.Prog.DecP

/-!
# The machine of `Dec`, compiled from a tape program

`decGenP cfX W : XProg 256` computes `Dec` from its input `encodeTuple [pw, sk, C, ct]` (tape `255`,
at most `nDec + 1` bits by the bounded loader): the length guard, the parsing (`sk ++ ct` on tape `0`,
`C` on tape `1`), the front end, and

* for a window predicate: the evaluation of `c_f̂` (the block `cfX`, a parameter meeting `CfSpec`),
  then the end of decryption `decFinB`;
* for another short predicate: the framed dummy answer `[false]`; for a long one: the empty tuple.

It is coin-free when `cfX` is, so its machine `decMachineP` is deterministic
(`deterministic_decMachineP`), and it computes `decM` (`decMachineP_law`).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo Matrix AdvancedEncryption.RingBTVW AdvancedEncryption.DualUse.Algo Turing
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord
open scoped SigabaNeo.Tape.Prog

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

variable (hk c) in
/-- **The block evaluating `c_f̂`**: from the data word `sk ++ ct` (tape `0`) and the block word
`blockWord W C` of a predicate of the class (`ValidC`) of at most `c.L` bits (tape `1`), the word of
`c_f̂ = evalCiphertext mpk (predC C) ct` on tape `2`, the data word kept, every other tape blank;
well formed and coin-free. -/
structure CfSpec (cfX : XProg 256) (W : ℕ) : Prop where
  wf : cfX.WF
  coinFree : cfX.CoinFree
  law : ∀ (sk : SK hk c) (C : List Bool) (ct : CT hk c), C.length ≤ c.L → ValidC C →
    cfX.law (io2 (R := 254) ((skEnc hk c).enc sk ++ (ctEnc hk c).enc ct) (blockWord W C) []) =
      PMF.pure (Function.update (io2 (R := 254) ((skEnc hk c).enc sk ++ (ctEnc hk c).enc ct) [] [])
        2 (rowW N K k (evalCiphertext sk.1 (predC C) ct)))

/-- Parse `encodeTuple [pw, a, b, e]`: `a ++ e` on tape `0`, `b` on tape `1`. -/
def parse4P : Prog 256 :=
  clr 254 ⨾ Prog.map (uU 253) unfrP ⨾ Prog.map (uU 0) unfrP ⨾ Prog.map (uU 1) unfrP ⨾
    Prog.map (uU 0) unfrP ⨾ clr 253 ⨾ clr 255

theorem run_parse4P (p a b e : List Bool) (f : List Bool) :
    run parse4P (Function.update (Function.update (fun _ => [])
      255 (SigabaNeo.encodeTuple [p, a, b, e])) 254 f) = io2 (R := 254) (a ++ e) b [] := by
  simp only [parse4P, run_seq, run_clear]
  have h : SigabaNeo.encodeTuple [p, a, b, e] = MultiTapeTM.frame p ++ (MultiTapeTM.frame a ++
      (MultiTapeTM.frame b ++ (MultiTapeTM.frame e ++ []))) := by
    simp [encodeTuple_cons, encodeTuple_nil]
  rw [run_unfrAt (d := 253) (by decide) _ p (MultiTapeTM.frame a ++ (MultiTapeTM.frame b ++
    (MultiTapeTM.frame e ++ []))) (by simp [h]) (by simp)]
  conv in (Prog.map (uU 0) unfrP).run (Function.update _ 251 []) =>
    rw [run_unfrAt (d := 0) (by decide) _ a (MultiTapeTM.frame b ++ (MultiTapeTM.frame e ++ []))
      (by simp) (by simp)]
  rw [run_unfrAt (d := 1) (by decide) _ b (MultiTapeTM.frame e ++ []) (by simp) (by simp)]
  rw [run_unfrAt (d := 0) (by decide) _ e [] (by simp) (by simp)]
  funext t
  by_cases h0 : t = 0
  · subst h0; simp [io2]
  by_cases h1 : t = 1
  · subst h1; simp [io2]
  have h0' : t.val ≠ 0 := fun h => h0 (Fin.ext h)
  have h1' : t.val ≠ 1 := fun h => h1 (Fin.ext h)
  simp only [Function.update_apply, io2, h0, h1, h0', h1', if_false]
  split_ifs <;> rfl

/-- The framed dummy answer `[false]`. -/
def dumDec : XProg 256 := XProg.seq (XProg.prog (clr 0)) (putW 0 [true, false, false])

variable (hk c) in
/-- The branches on the output of the front end. -/
noncomputable def branchD (cfX : XProg 256) : XProg 256 :=
  XProg.ifBit 1 (XProg.seq (XProg.prog (.prim (.tail 1))) (XProg.seq cfX (decFinB hk c)))
    (XProg.ifBlank 1 longB dumDec)

variable (hk c) in
/-- The longest input of `Dec` with a predicate of at most `c.L` bits. -/
def nDec : ℕ := (2 * (pw).length + 1) + (2 * fixLen (skEnc hk c) + 1) + (2 * c.L + 1) +
  (2 * fixLen (ctEnc hk c) + 1)

variable (hk c) in
/-- **The program of `Dec`** for a front end `fr` framed by `e` (`FrontSpec`, `FrEmb`): input on
tape `255`, output on tape `0`. -/
noncomputable def decGenF {R : ℕ} (e : Fin (R + 2) ↪ Fin 256) (fr : XProg (R + 2))
    (cfX : XProg 256) : XProg 256 :=
  XProg.seq (XProg.prog (Prog.map uL (leP (nDec hk c))))
    (XProg.ifBlank 254 (XProg.prog (clr 255))
      (XProg.seq (XProg.prog parse4P) <| XProg.seq (XProg.frame e fr) <|
        XProg.seq (branchD hk c cfX) (clearL clrAll)))

theorem length_encodeTuple_Dec (sk : SK hk c) (C : List Bool) (ct : CT hk c) :
    (SigabaNeo.encodeTuple [pw, (skEnc hk c).enc sk, C, (ctEnc hk c).enc ct]).length =
      (2 * (pw).length + 1) + (2 * fixLen (skEnc hk c) + 1) + (2 * C.length + 1) +
        (2 * fixLen (ctEnc hk c) + 1) := by
  simp only [encodeTuple_cons, encodeTuple_nil, List.length_append, length_frame,
    length_enc_fixLen, List.length_nil]
  omega

/-- **The law of `Dec` as a tape program** for any front end, on predicates of at most `c.L`
bits. -/
theorem law_decGenF {R : ℕ} {e : Fin (R + 2) ↪ Fin 256} (he : FrEmb e) {fr : XProg (R + 2)}
    {W : ℕ} {FT FL : ℕ → ℕ} {FS : ℕ} (hfr : FrontSpec fr c.L W FT FL FS)
    {cfX : XProg 256} (hcf : CfSpec hk c cfX W) (hK2 : 2 ≤ K)
    (sk : SK hk c) (C : List Bool) (ct : CT hk c) (hL : C.length ≤ c.L) :
    (decGenF hk c e fr cfX).law (inputStore 255
        ((SigabaNeo.encodeTuple [pw, (skEnc hk c).enc sk, C, (ctEnc hk c).enc ct]).take
          (nDec hk c + 1))) =
      PMF.pure (io2 (R := 254) (SigabaNeo.encodeTuple [decM hk c sk C ct]) [] []) := by
  set x := SigabaNeo.encodeTuple [pw, (skEnc hk c).enc sk, C, (ctEnc hk c).enc ct] with hx
  have hlen := length_encodeTuple_Dec (hk := hk) (c := c) sk C ct
  have hn : x.length ≤ nDec hk c := by rw [hlen, nDec]; omega
  have ht : x.take (nDec hk c + 1) = x := List.take_of_length_le (by omega)
  have e255 : inputStore (k := 256) 255 x 255 = x := by simp [inputStore]
  rw [ht, decGenF, XProg.law_seq, XProg.law_prog, law_eq_run_of_coinFree _ (coinFree_leAt _),
    PMF.pure_bind, run_leAt, XProg.law_ifBlank, Function.update_of_ne (by decide),
    Function.update_self, e255, if_pos hn, if_neg (by simp)]
  have es : Function.update (Function.update (inputStore 255 x) 254 [true]) 253 [] =
      Function.update (Function.update (fun _ : Fin 256 => ([] : List Bool)) 255 x) 254 [true] := by
    funext t
    by_cases h253 : t = 253
    · subst h253; simp [inputStore]
    · simp [Function.update_apply, inputStore, h253]
  have hpc : parse4P.CoinFree := by
    have h1 := coinFree_mapP (uU 253) coinFree_unfrP
    have h2 := coinFree_mapP (uU 0) coinFree_unfrP
    have h3 := coinFree_mapP (uU 1) coinFree_unfrP
    simp only [CoinFree] at h1 h2 h3
    simp [CoinFree, parse4P, coinFreeB, h1, h2, h3]
  rw [es, XProg.law_seq, XProg.law_prog, law_eq_run_of_coinFree _ hpc, PMF.pure_bind,
    run_parse4P, XProg.law_seq_pure (law_frame_frEmb he hfr _ C), XProg.law_seq, branchD,
    XProg.law_ifBit]
  by_cases hw : ValidC C
  · have e1 : (Prim.tail (1 : Fin 256)).apply (io2 (R := 254) ((skEnc hk c).enc sk ++
        (ctEnc hk c).enc ct) (true :: blockWord W C) []) =
        io2 (R := 254) ((skEnc hk c).enc sk ++ (ctEnc hk c).enc ct) (blockWord W C) [] := by
      funext t
      simp only [Prim.apply, Function.update_apply, io2]
      split_ifs <;> first | rfl | (exfalso; simp_all [Fin.ext_iff])
    rw [frontG_valid hL hw, if_pos (by simp [io2]), XProg.law_seq_pure (XProg.law_prim _ _), e1,
      XProg.law_seq_pure (hcf.law sk C ct hL hw), law_decFinB hK2, PMF.pure_bind, law_clrAll,
      decM_win hk c sk C ct hw]
    rfl
  · rw [frontG_short_not hL hw, if_neg (by simp [io2]), XProg.law_ifBlank, if_neg (by simp [io2]),
      dumDec, XProg.law_seq_pure (XProg.law_prim _ _), law_putW, PMF.pure_bind, law_clearL]
    congr 1
    have hd : decM hk c sk C ct = [false] := by
      classical
      unfold decM; rw [if_neg hw]
    rw [hd]
    funext t
    by_cases t0 : t = 0
    · subst t0; simp [io2, mem_clrAll, encodeTuple_single, MultiTapeTM.frame, Prim.apply]
    · have t0' : t.val ≠ 0 := fun e => t0 (Fin.ext e)
      simp only [mem_clrAll, ne_eq, t0, not_false_eq_true, if_true, io2, t0', if_false]
      split_ifs <;> rfl

/-! ### The machine -/

theorem wf_getP (o L : ℕ) (dst : Fin 256) : (getP o L dst).WF :=
  ⟨⟨trivial, wf_tailsP _ _⟩, wf_prefP _ _ _ _ _, trivial⟩

theorem wf_decFinB : (decFinB hk c).WF := by
  have hk1 : ∀ x ∈ decTmpl c, x.1 ≠ (120 : Fin 256) := fun x hx e => by
    simp only [decTmpl, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h | h | h | h | h <;> (subst h; simp at e)
  exact ⟨wf_getP _ _ _, wf_getP _ _ _, wf_getP _ _ _, wf_getP _ _ _, wf_getP _ _ _, wf_getP _ _ _,
    wf_putW _ _, wf_tmplP _ _ hk1, ProgKeyR.wf_decFP, ⟨trivial, trivial⟩, wf_prefP _ _ _ _ _,
    trivial, WF.map (by decide) wf_ballP, trivial, ⟨wf_putW _ _, wf_putW _ _⟩, wf_clearL _⟩

theorem wf_decGenF {R : ℕ} (e : Fin (R + 2) ↪ Fin 256) {fr : XProg (R + 2)} (hfr : fr.WF)
    {cfX : XProg 256} {W : ℕ} (hcf : CfSpec hk c cfX W) :
    (decGenF hk c e fr cfX).WF :=
  ⟨WF.map (by decide) (wf_leP _), trivial,
    ⟨trivial, WF.map (by decide) wf_unfrP, WF.map (by decide) wf_unfrP,
      WF.map (by decide) wf_unfrP, WF.map (by decide) wf_unfrP, trivial, trivial⟩,
    hfr,
    ⟨⟨trivial, hcf.wf, wf_decFinB⟩, wf_clearL _, ⟨trivial, wf_putW _ _⟩⟩, wf_clearL _⟩

theorem coinFree_decGenF {R : ℕ} (e : Fin (R + 2) ↪ Fin 256) {fr : XProg (R + 2)}
    (hfr : fr.CoinFree) {cfX : XProg 256} {W : ℕ} (hcf : CfSpec hk c cfX W) :
    (decGenF hk c e fr cfX).CoinFree := by
  have hpc : parse4P.CoinFree := by
    have h1 := coinFree_mapP (uU 253) coinFree_unfrP
    have h2 := coinFree_mapP (uU 0) coinFree_unfrP
    have h3 := coinFree_mapP (uU 1) coinFree_unfrP
    simp only [CoinFree] at h1 h2 h3
    simp [CoinFree, parse4P, coinFreeB, h1, h2, h3]
  exact XProg.coinFree_seq (coinFree_leAt _) (XProg.coinFree_ifBlank _ rfl
    (XProg.coinFree_seq hpc (XProg.coinFree_seq (XProg.coinFree_frame e hfr) (XProg.coinFree_seq
      (XProg.coinFree_ifBit _ (XProg.coinFree_seq rfl (XProg.coinFree_seq hcf.coinFree cfX_decFinB))
        (XProg.coinFree_ifBlank _ (cfX_clearL _) (XProg.coinFree_seq rfl (cfX_putW _ _))))
      (cfX_clearL _)))))

variable (hk c) in
/-- **The machine of `Dec`** for a framed front end: input on tape `255` (at most `nDec + 1` bits
loaded), output on tape `0`. -/
noncomputable def decMachineF {R : ℕ} (e : Fin (R + 2) ↪ Fin 256) (fr : XProg (R + 2))
    (cfX : XProg 256) : Machine :=
  (decGenF hk c e fr cfX).toMachineB 255 0 (nDec hk c)

theorem deterministic_decMachineF {R : ℕ} (e : Fin (R + 2) ↪ Fin 256) {fr : XProg (R + 2)}
    (hfr : fr.CoinFree) {cfX : XProg 256} {W : ℕ} (hcf : CfSpec hk c cfX W) :
    (decMachineF hk c e fr cfX).Deterministic :=
  XProg.deterministic_toMachineB _ (coinFree_decGenF e hfr hcf) _ _ _

theorem decMachineF_law {R : ℕ} {e : Fin (R + 2) ↪ Fin 256} (he : FrEmb e) {fr : XProg (R + 2)}
    {W : ℕ} {FT FL : ℕ → ℕ} {FS : ℕ} (hfr : FrontSpec fr c.L W FT FL FS)
    {cfX : XProg 256} (hcf : CfSpec hk c cfX W) (hK2 : 2 ≤ K)
    (sk : SK hk c) (C : List Bool) (ct : CT hk c) (hL : C.length ≤ c.L) :
    (decMachineF hk c e fr cfX).run
        (SigabaNeo.encodeTuple [pw, (skEnc hk c).enc sk, C, (ctEnc hk c).enc ct]) =
      PMF.pure (SigabaNeo.encodeTuple [decM hk c sk C ct]) := by
  rw [decMachineF, XProg.run_toMachineB _ (wf_decGenF e hfr.wf hcf),
    law_decGenF he hfr hcf hK2 sk C ct hL, PMF.pure_map]
  rfl

end AdvancedEncryption.DualUse.Prog
