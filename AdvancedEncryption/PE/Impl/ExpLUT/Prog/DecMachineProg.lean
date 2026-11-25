import PE.Impl.ExpLUT.Prog.DecMachineCode
import PE.Impl.ExpLUT.Prog.DecFront
import SigabaNeoStd.Machines.Prog.LenEq
import SigabaNeoStd.Machines.Prog.Stream
import SigabaNeoStd.Machines.Prog.DetX
import SigabaNeoStd.Machines.Prog.CapN

/-!
# The `Dec` machine (package F4)

`decProgram D : XProg 256` on the input `encodeTuple [pw, sk, C, ct]` (tape `255`):

1. `frontP`: parse (`parseD`: `sk`, `C`, `ct` onto the registers `76`, `73`, `77`, i.e. the tapes
   `123`, `120`, `124`), then the length test `|C| = predLen` (`lenEqP`, flag on tape `249`);
2. a valid predicate word: the templates (`tmplsP`, by doubling, counter `250`: the `RingVM`
   templates `K`, `N`, `N K` on `40 … 42` and the register templates of `DInit`), the all-ones
   word on `43` and the constants on the registers `3`, `75` (`constP`), the compiled code
   `decCode` framed on the tapes `0 … 246` (`vmE`), and the output `[true, b, false]` (the frame of
   `[b]`) on tape `0` from register `179` (`outP`);
3. otherwise the frame of `[false]` on tape `0` (`invP`).

**`law_decProgram`**: the output tape is `encodeTuple [decOutW D sk C ct]` (for `D.b = 22`), and
**`decSpec_decMP`**: `decMP D L = (decProgram D).toMachineT 255 0 (decInputLength D L)` meets
`DecSpec D L` (it is coin-free, hence deterministic).
-/

namespace AdvancedEncryption.ExpLUT.Prog.DecM

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo
open SigabaNeo.Tape.XProg (natP law_natP)
open scoped SigabaNeo.Tape.Prog

variable (D : Dims)

/-! ### The program -/

/-- **The templates** (tape, length). -/
def tmplList : List (Fin 256 × ℕ) :=
  [(40, D.K), (41, D.N), (42, D.N * D.K),
    (tR 1, 1), (tR 2, D.N * D.K), (tR 3, D.N * D.K - 1), (tR 4, D.K), (tR 5, D.K - 1),
    (tR 6, 2 * D.K * (D.N * D.K)), (tR 7, 4 * D.K * (D.N * D.K)), (tR 8, 2 * D.K), (tR 9, 2),
    (tR 10, 2 * (2 * D.K) * D.K * (2 * D.K * (D.N * D.K))), (tR 12, 2 ^ 22), (tR 13, 22),
    (tR 14, 14), (tR 15, D.K - 2), (tR 16, dmBC D * (D.N * D.K)), (tR 17, dmBC D),
    (tR 18, dmJC D), (tR 19, dmJC D * (D.N * D.K)), (tR 56, D.K * (D.N * D.K)), (tR 74, dmJ D),
    (tR 78, 14 * 2 ^ 22),
    (tR 180, dm2 * (dmBC D * (D.N * D.K))),
    (tR 181, dmJ D * (dm2 * (dmCol D * (D.N * D.K)))),
    (tR 182, dmPos * (dmCol D * (D.N * D.K))),
    (tR 183, dmPos * (dmDig D * (dm2 * (dmCol D * (D.N * D.K))))),
    (tR 184, dmB D * (dmDig D * (dm2 * (dmCol D * (D.N * D.K))))),
    (tR 185, dm2 * (D.N * D.K)),
    (tR 186, dmB D * (dmDig D * (dmCol D * (D.N * D.K)))),
    (tR 187, dmPos * (dmDig D * (dmCol D * (D.N * D.K)))),
    (tR 188, 4 * D.K), (tR 189, famMLen D)] ++
  ((List.range 22).map fun t => (tR (kReg t), κD D t)) ++
  ((List.range 14).map fun b => (tR (rReg b), ρD D.N b))

/-- The tapes of the templates. -/
def tmplTapes : List (Fin 256) :=
  [40, 41, 42, tR 1, tR 2, tR 3, tR 4, tR 5, tR 6, tR 7, tR 8, tR 9, tR 10, tR 12, tR 13, tR 14,
    tR 15, tR 16, tR 17, tR 18, tR 19, tR 56, tR 74, tR 78, tR 180, tR 181, tR 182, tR 183, tR 184,
    tR 185, tR 186, tR 187, tR 188, tR 189] ++
  ((List.range 22).map fun t => tR (kReg t)) ++ ((List.range 14).map fun b => tR (rReg b))

theorem tmplList_fst : (tmplList D).map Prod.fst = tmplTapes := by
  simp [tmplList, tmplTapes, List.map_map, Function.comp_def]

theorem nodup_tmplTapes : tmplTapes.Nodup := by decide +kernel

theorem tmplTapes_range : ∀ u ∈ tmplTapes, (40 ≤ u.val ∧ u.val ≤ 42) ∨ (47 ≤ u.val ∧ u.val < 247) := by
  decide +kernel

/-- The all-ones word on `43`, then `ONE` on register `3` and `[true]` on register `75`. -/
def constP : Tape.Prog 256 :=
  Prog.forN 250 42 (.prim (.snoc 43 true)) ⨾ .prim (.cons (tR 3) true) ⨾ .prim (.snoc (tR 75) true)

/-- The output: the frame `[true, b, false]` of the word `[b]` of register `179`. -/
def outP : Tape.Prog 256 :=
  Prog.cp 0 (tR 179) ⨾ .prim (.cons 0 true) ⨾ .prim (.snoc 0 false)

/-- The output for an invalid predicate word: the frame of `[false]`. -/
def invP : Tape.Prog 256 :=
  .prim (.snoc 0 true) ⨾ .prim (.snoc 0 false) ⨾ .prim (.snoc 0 false)

/-- The tapes of the length test. -/
def lenMap : Fin 6 → Fin 256 := ![120, 249, 250, 251, 252, 253]

theorem lenMap_inj : Function.Injective lenMap := by decide

/-- Parsing and the length test (flag on `249`). -/
def frontP : Tape.Prog 256 := parseD ⨾ Prog.map lenMap (Prog.lenEqP predLen)

/-- An unframing step on the tapes `uI d` (framed). -/
def unfrX (d : Fin 256) (h : Function.Injective (uI d)) : XProg 256 :=
  .frame ⟨uI d, h⟩ (.prog Prog.unfrP)

/-- Parsing, every step framed on its own tapes. -/
def parseX : XProg 256 :=
  .seq (unfrX 253 (by decide)) (.seq (unfrX 123 (by decide)) (.seq (unfrX 120 (by decide))
    (.seq (unfrX 124 (by decide)) (.prog (Prog.clr 253)))))

/-- The length test, framed on its tapes. -/
def lenX : XProg 256 := .frame ⟨lenMap, lenMap_inj⟩ (.prog (Prog.lenEqP predLen))

/-- The branch of a valid predicate word. -/
def validP : XProg 256 :=
  .seq (tmplsP 250 (tmplList D))
    (.seq (.prog constP) (.seq (.frame vmE (compile decCode)) (.prog outP)))

/-- **The program of `Dec`.** -/
def decProgram : XProg 256 :=
  .seq parseX (.seq lenX (.ifBit 249 (validP D) (.prog invP)))

/-! ### Parsing and the length test -/

/-- The store after parsing. -/
def S1 (a b e : List Bool) : Store 256 :=
  fun t => if t = 123 then a else if t = 120 then b else if t = 124 then e else []

theorem run_parseD_input (p a b e : List Bool) :
    parseD.run (inputStore 255 (encodeTuple [p, a, b, e])) = S1 a b e := by
  rw [run_parseD _ p a b e (by simp [inputStore]) (by simp [inputStore]) (by simp [inputStore])]
  funext t
  by_cases h1 : t = 251
  · subst h1; simp [S1]
  by_cases h2 : t = 124
  · subst h2; simp [S1, inputStore]
  by_cases h3 : t = 120
  · subst h3; simp [S1, inputStore]
  by_cases h4 : t = 123
  · subst h4; simp [S1, inputStore]
  by_cases h5 : t = 255
  · subst h5; simp [S1]
  simp [S1, inputStore, h1, h2, h3, h4]

theorem run_frontP (p a b e : List Bool) :
    frontP.run (inputStore 255 (encodeTuple [p, a, b, e])) =
      Function.update (S1 a b e) 249 [decide (b.length = predLen)] := by
  rw [frontP, Prog.run_seq, run_parseD_input, Prog.run_map lenMap_inj]
  have hs : (S1 a b e) ∘ lenMap = Prog.in0 b := by
    funext j; fin_cases j <;> simp [lenMap, S1, Prog.in0]
  rw [hs, Prog.run_lenEqP, ← hs, extend_update lenMap_inj, extend_comp_self]
  rfl

/-! ### The templates and constants -/

theorem tmpl_mem {s : Store 256} {t : Fin 256} {n : ℕ} (hm : (t, n) ∈ tmplList D) :
    tmplsS (tmplList D) s t = List.replicate n false := by
  refine tmplsS_apply_of_mem _ s t n hm (fun p hp hpt => ?_)
  have hnd : ((tmplList D).map Prod.fst).Nodup := by rw [tmplList_fst]; exact nodup_tmplTapes
  rw [List.inj_on_of_nodup_map hnd hp hm hpt]

theorem tmpl_not {s : Store 256} {t : Fin 256} (h : t ∉ tmplTapes) :
    tmplsS (tmplList D) s t = s t :=
  tmplsS_apply_of_not_mem _ s t (fun p hp e => h (by
    rw [← tmplList_fst D]; exact List.mem_map.2 ⟨p, hp, e⟩))

theorem run_constP (s : Store 256) (h43 : s 43 = []) (h250 : s 250 = []) :
    constP.run s = Function.update (Function.update (Function.update s 43
      (List.replicate (s 42).length true)) (tR 3) (true :: s (tR 3))) (tR 75)
        (s (tR 75) ++ [true]) := by
  have hfor := Prog.run_forN (250 : Fin 256) 42 (.prim (.snoc 43 true))
    (fun m => Function.update s 43 (List.replicate m true)) Nat.succ
    (fun m w => by
      rw [Prog.run_prim]
      funext t
      simp only [Prim.apply, Function.update_apply]
      by_cases ht : t = 43
      · subst ht; simp [List.replicate_succ']
      · simp [ht])
    0 s (by rw [List.replicate_zero, ← h43, Function.update_eq_self])
  rw [constP, Prog.run_seq, hfor, Prog.run_seq, Prog.run_prim, Prog.run_prim]
  have hit : Nat.succ^[(s 42).length] 0 = (s 42).length := by rw [Nat.succ_iterate]; simp
  rw [hit]
  have e250 : Function.update (Function.update s 43 (List.replicate (s 42).length true)) 250 [] =
      Function.update s 43 (List.replicate (s 42).length true) := by
    rw [Function.update_eq_self_iff, Function.update_of_ne (by decide), h250]
  rw [e250]
  simp only [Prim.apply]
  rw [Function.update_of_ne (show tR 3 ≠ (43 : Fin 256) by decide),
    Function.update_of_ne (show tR 75 ≠ tR 3 by decide),
    Function.update_of_ne (show tR 75 ≠ (43 : Fin 256) by decide)]

/-! ### Entering and leaving the ring-word machine -/

theorem vmE_val (t : Fin 247) : (vmE t).val = t.val := rfl

theorem tR_eq_vmE (x : Fin 200) : tR x = vmE (tWd x) := Fin.ext rfl

/-- The tapes of the machine are the encoding of its registers. -/
theorem vm_in {N K : ℕ} (s : Store 256)
    (h0 : ∀ t : Fin 256, t.val < 40 ∨ (44 ≤ t.val ∧ t.val < 47) → s t = [])
    (h40 : s 40 = List.replicate K false) (h41 : s 41 = List.replicate N false)
    (h42 : s 42 = List.replicate (N * K) false) (h43 : s 43 = List.replicate (N * K) true) :
    (fun j => s (vmE j)) = enc N K (fun x => s (tR x)) := by
  funext t
  show s (vmE t) = encO N K (fun _ => []) _ t
  unfold encO
  have ht := t.isLt
  split_ifs with a1 a2 a3 a4 a5 a6
  · exact h0 _ (Or.inl a1)
  · rw [show vmE t = 40 from Fin.ext (by rw [vmE_val, a2]; rfl), h40]
  · rw [show vmE t = 41 from Fin.ext (by rw [vmE_val, a3]; rfl), h41]
  · rw [show vmE t = 42 from Fin.ext (by rw [vmE_val, a4]; rfl), h42]
  · rw [show vmE t = 43 from Fin.ext (by rw [vmE_val, a5]; rfl), h43]
  · exact congrArg s (Fin.ext (by simp only [vmE_val, tR]; omega))
  · exact h0 _ (Or.inr ⟨by rw [vmE_val]; omega, by rw [vmE_val]; omega⟩)

/-- The tapes after the code. -/
theorem vm_out_tR {N K : ℕ} (s : Store 256) (w : St) (x : Fin 200) :
    embedF vmE s (enc N K w) (tR x) = w x := by
  rw [tR_eq_vmE, embedF_apply_self]; exact encO_tWd x

theorem vm_out_0 {N K : ℕ} (s : Store 256) (w : St) :
    embedF vmE s (enc N K w) 0 = [] := by
  rw [show (0 : Fin 256) = vmE (tO 0) from rfl, embedF_apply_self]; exact encO_tO 0 (by decide)

/-! ### The registers before the code -/

/-- The store before the templates (valid predicate word). -/
abbrev S2 (a b e : List Bool) : Store 256 := Function.update (S1 a b e) 249 [true]

/-- The store before the code. -/
def S3 (a b e : List Bool) : Store 256 := constP.run (tmplsS (tmplList D) (S2 a b e))

theorem S2_other (a b e : List Bool) (t : Fin 256) (h1 : t ≠ 123) (h2 : t ≠ 120) (h3 : t ≠ 124)
    (h4 : t ≠ 249) : S2 a b e t = [] := by
  simp [S2, S1, h1, h2, h3, h4]

theorem S3_eq (a b e : List Bool) : S3 D a b e =
    Function.update (Function.update (Function.update (tmplsS (tmplList D) (S2 a b e)) 43
      (List.replicate (D.N * D.K) true)) (tR 3) (true :: List.replicate (D.N * D.K - 1) false))
      (tR 75) [true] := by
  rw [S3, run_constP]
  · rw [tmpl_mem D (t := 42) (n := D.N * D.K) (by simp [tmplList]), List.length_replicate,
      tmpl_mem D (t := tR 3) (n := D.N * D.K - 1) (by simp [tmplList]),
      tmpl_not D (t := tR 75) (by decide +kernel),
      S2_other a b e _ (by decide) (by decide) (by decide) (by decide)]
    rfl
  · rw [tmpl_not D (by decide +kernel), S2_other a b e _ (by decide) (by decide) (by decide) (by decide)]
  · rw [tmpl_not D (by decide +kernel), S2_other a b e _ (by decide) (by decide) (by decide) (by decide)]

theorem S3_tmpl (a b e : List Bool) {t : Fin 256} {n : ℕ} (hm : (t, n) ∈ tmplList D)
    (h43 : t ≠ 43) (h3 : t ≠ tR 3) (h75 : t ≠ tR 75) : S3 D a b e t = List.replicate n false := by
  rw [S3_eq, Function.update_of_ne h75, Function.update_of_ne h3, Function.update_of_ne h43,
    tmpl_mem D hm]

theorem S3_not (a b e : List Bool) {t : Fin 256} (hm : t ∉ tmplTapes)
    (h43 : t ≠ 43) (h3 : t ≠ tR 3) (h75 : t ≠ tR 75) : S3 D a b e t = S2 a b e t := by
  rw [S3_eq, Function.update_of_ne h75, Function.update_of_ne h3, Function.update_of_ne h43,
    tmpl_not D hm]

theorem tR_ne_43 (x : Fin 200) : tR x ≠ 43 := fun h => by
  have := congrArg Fin.val h; simp [tR] at this; omega

theorem tR_ne (x y : Fin 200) (h : x ≠ y) : tR x ≠ tR y := fun e => h (Fin.ext (by
  have := congrArg Fin.val e; simp [tR] at this; omega))

theorem S3_reg (a b e : List Bool) {x : Fin 200} {n : ℕ} (hm : (tR x, n) ∈ tmplList D)
    (h3 : x ≠ 3) (h75 : x ≠ 75) : S3 D a b e (tR x) = List.replicate n false :=
  S3_tmpl D a b e hm (tR_ne_43 x) (tR_ne x 3 h3) (tR_ne x 75 h75)

theorem kap_mem {t : ℕ} (ht : t < 22) : (tR (kReg t), κD D t) ∈ tmplList D := by
  refine List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨t, ?_, rfl⟩))
  exact List.mem_range.2 ht

theorem rho_mem {b : ℕ} (hb : b < 14) : (tR (rReg b), ρD D.N b) ∈ tmplList D :=
  List.mem_append_right _ (List.mem_map.2 ⟨b, List.mem_range.2 hb, rfl⟩)

theorem kReg_ne3 (t : ℕ) (_ht : t < 22) : kReg t ≠ 3 := fun h => by
  have := congrArg Fin.val h; simp [kReg] at this; omega
theorem kReg_ne75 (t : ℕ) (_ht : t < 22) : kReg t ≠ 75 := fun h => by
  have := congrArg Fin.val h; simp [kReg] at this; omega
theorem rReg_ne3 (b : ℕ) (_hb : b < 14) : rReg b ≠ 3 := fun h => by
  have := congrArg Fin.val h; simp [rReg] at this; omega
theorem rReg_ne75 (b : ℕ) (_hb : b < 14) : rReg b ≠ 75 := fun h => by
  have := congrArg Fin.val h; simp [rReg] at this; omega

set_option maxHeartbeats 1000000 in
/-- **The registers before the code.** -/
theorem dInit_S3 (sk : SKt D) (C : List Bool) (ct : CTt D) :
    DInit D sk C ct (fun x => S3 D ((skEnc D).enc sk) C ((ctEnc D).enc ct) (tR x)) := by
  set a := (skEnc D).enc sk
  set e := (ctEnc D).enc ct
  have R : ∀ (x : Fin 200) (n : ℕ), (tR x, n) ∈ tmplList D → x ≠ 3 → x ≠ 75 →
      S3 D a C e (tR x) = List.replicate n false := fun x n hm h3 h75 => S3_reg D a C e hm h3 h75
  have L : ∀ (x : Fin 200) (n : ℕ), (tR x, n) ∈ tmplList D → x ≠ 3 → x ≠ 75 →
      (S3 D a C e (tR x)).length = n := fun x n hm h3 h75 => by
    rw [R x n hm h3 h75, List.length_replicate]
  exact
    { c :=
      { z := by
          rw [S3_not D a C e (by decide +kernel) (by decide) (by decide) (by decide)]
          exact S2_other a C e _ (by decide) (by decide) (by decide) (by decide)
        one := R 1 1 (by simp [tmplList]) (by decide) (by decide)
        zero := R 2 _ (by simp [tmplList]) (by decide) (by decide)
        k := R 4 _ (by simp [tmplList]) (by decide) (by decide) }
      r3 := by rw [S3_eq, Function.update_of_ne (tR_ne 3 75 (by decide)), Function.update_self]
      r5 := R 5 _ (by simp [tmplList]) (by decide) (by decide)
      r6 := R 6 _ (by simp [tmplList]) (by decide) (by decide)
      r7 := R 7 _ (by simp [tmplList]) (by decide) (by decide)
      r8 := R 8 _ (by simp [tmplList]) (by decide) (by decide)
      r9 := R 9 _ (by simp [tmplList]) (by decide) (by decide)
      r10 := R 10 _ (by simp [tmplList]) (by decide) (by decide)
      r12 := R 12 _ (by simp [tmplList]) (by decide) (by decide)
      r13 := R 13 _ (by simp [tmplList]) (by decide) (by decide)
      r14 := R 14 _ (by simp [tmplList]) (by decide) (by decide)
      r15 := L 15 _ (by simp [tmplList]) (by decide) (by decide)
      r16 := L 16 _ (by simp [tmplList]) (by decide) (by decide)
      r17 := L 17 _ (by simp [tmplList]) (by decide) (by decide)
      r18 := L 18 _ (by simp [tmplList]) (by decide) (by decide)
      r19 := L 19 _ (by simp [tmplList]) (by decide) (by decide)
      kap := fun t ht => R _ _ (kap_mem D ht) (kReg_ne3 t ht) (kReg_ne75 t ht)
      rho := fun b hb => R _ _ (rho_mem D hb) (rReg_ne3 b hb) (rReg_ne75 b hb)
      r56 := R 56 _ (by simp [tmplList]) (by decide) (by decide)
      r73 := by
        rw [S3_not D a C e (by decide +kernel) (by decide) (by decide) (by decide)]
        rw [S2, Function.update_of_ne (by decide)]; simp [S1, show (tR 73 : Fin 256) = 120 from rfl]
      r74 := L 74 _ (by simp [tmplList]) (by decide) (by decide)
      r75 := by rw [S3_eq, Function.update_self]
      r76 := by
        rw [S3_not D a C e (by decide +kernel) (by decide) (by decide) (by decide)]
        rw [S2, Function.update_of_ne (by decide)]; simp [S1, a, show (tR 76 : Fin 256) = 123 from rfl]
      r77 := by
        rw [S3_not D a C e (by decide +kernel) (by decide) (by decide) (by decide)]
        rw [S2, Function.update_of_ne (by decide)]; simp [S1, e, show (tR 77 : Fin 256) = 124 from rfl]
      r78 := R 78 _ (by simp [tmplList]) (by decide) (by decide)
      r180 := L 180 _ (by simp [tmplList]) (by decide) (by decide)
      r181 := L 181 _ (by simp [tmplList]) (by decide) (by decide)
      r182 := L 182 _ (by simp [tmplList]) (by decide) (by decide)
      r183 := L 183 _ (by simp [tmplList]) (by decide) (by decide)
      r184 := L 184 _ (by simp [tmplList]) (by decide) (by decide)
      r185 := L 185 _ (by simp [tmplList]) (by decide) (by decide)
      r186 := L 186 _ (by simp [tmplList]) (by decide) (by decide)
      r187 := L 187 _ (by simp [tmplList]) (by decide) (by decide)
      r188 := R 188 _ (by simp [tmplList]) (by decide) (by decide)
      r189 := R 189 _ (by simp [tmplList]) (by decide) (by decide) }

/-! ### Coin-freeness and well-formedness -/

theorem coinFree_parseD : parseD.CoinFree := by
  have h1 := Prog.coinFree_mapP (uI 253) Prog.coinFree_unfrP
  have h2 := Prog.coinFree_mapP (uI 123) Prog.coinFree_unfrP
  have h3 := Prog.coinFree_mapP (uI 120) Prog.coinFree_unfrP
  have h4 := Prog.coinFree_mapP (uI 124) Prog.coinFree_unfrP
  simp only [Prog.CoinFree] at h1 h2 h3 h4
  simp [Prog.CoinFree, parseD, Prog.coinFreeB, h1, h2, h3, h4]

theorem coinFree_frontP : frontP.CoinFree := by
  have h1 := coinFree_parseD
  have h2 := Prog.coinFree_mapP lenMap (Prog.coinFree_lenEqP predLen)
  simp only [Prog.CoinFree] at h1 h2
  simp [Prog.CoinFree, frontP, Prog.coinFreeB, h1, h2]

theorem coinFree_constP : constP.CoinFree := rfl
theorem coinFree_outP : outP.CoinFree := rfl
theorem coinFree_invP : invP.CoinFree := rfl

theorem coinFree_tmplsP (c : Fin 256) : ∀ l : List (Fin 256 × ℕ), (tmplsP c l).CoinFree
  | [] => rfl
  | _ :: l => XProg.coinFree_seq (XProg.coinFree_natP _ _ _) (coinFree_tmplsP c l)

theorem coinFree_parseX : parseX.CoinFree :=
  XProg.coinFree_seq (XProg.coinFree_frame _ (XProg.coinFree_prog Prog.coinFree_unfrP))
    (XProg.coinFree_seq (XProg.coinFree_frame _ (XProg.coinFree_prog Prog.coinFree_unfrP))
    (XProg.coinFree_seq (XProg.coinFree_frame _ (XProg.coinFree_prog Prog.coinFree_unfrP))
    (XProg.coinFree_seq (XProg.coinFree_frame _ (XProg.coinFree_prog Prog.coinFree_unfrP))
      (XProg.coinFree_prog rfl))))

theorem coinFree_lenX : lenX.CoinFree :=
  XProg.coinFree_frame _ (XProg.coinFree_prog (Prog.coinFree_lenEqP _))

theorem coinFree_decProgram : (decProgram D).CoinFree :=
  XProg.coinFree_seq coinFree_parseX (XProg.coinFree_seq coinFree_lenX (XProg.coinFree_ifBit _ (XProg.coinFree_seq (coinFree_tmplsP _ _)
      (XProg.coinFree_seq (XProg.coinFree_prog coinFree_constP)
        (XProg.coinFree_seq (XProg.coinFree_frame _ (coinFree_compile _))
          (XProg.coinFree_prog coinFree_outP))))
      (XProg.coinFree_prog coinFree_invP)))

theorem wf_tmplsP (c : Fin 256) : ∀ l : List (Fin 256 × ℕ), (∀ p ∈ l, p.1 ≠ c) →
    (tmplsP c l).WF
  | [], _ => trivial
  | p :: l, h => ⟨XProg.wf_natP (Ne.symm (h p (by simp))) _,
      wf_tmplsP c l fun q hq => h q (by simp [hq])⟩

theorem tmpl_ne_250 : ∀ p ∈ tmplList D, p.1 ≠ 250 := fun p hp h => by
  have hm : p.1 ∈ tmplTapes := by rw [← tmplList_fst D]; exact List.mem_map_of_mem hp
  rw [h] at hm
  exact absurd hm (by decide +kernel)

theorem loopOk_decCode : loopOkB decCode = true := by decide +kernel

theorem wf_frontP : frontP.WF :=
  ⟨⟨Prog.WF.map (by decide) Prog.wf_unfrP, Prog.WF.map (by decide) Prog.wf_unfrP,
    Prog.WF.map (by decide) Prog.wf_unfrP, Prog.WF.map (by decide) Prog.wf_unfrP, trivial⟩,
    Prog.WF.map lenMap_inj (Prog.wf_lenEqP _)⟩

theorem wf_constP : constP.WF := by
  refine ⟨?_, trivial, trivial⟩
  unfold Prog.forN
  exact ⟨trivial, trivial, by simp [Prog.Preserves, Prim.writes]⟩

theorem wf_validP : (validP D).WF :=
  ⟨wf_tmplsP _ _ (tmpl_ne_250 D), wf_constP, wf_compile _ loopOk_decCode, trivial, trivial,
    trivial⟩

theorem wf_decProgram : (decProgram D).WF :=
  ⟨⟨Prog.wf_unfrP, Prog.wf_unfrP, Prog.wf_unfrP, Prog.wf_unfrP, trivial⟩,
    Prog.wf_lenEqP _, wf_validP D, trivial, trivial, trivial⟩

/-! ### The law -/

theorem law_ifBit' {k : ℕ} (i : Fin k) (p q : XProg k) (s : Store k) :
    (XProg.ifBit i p q).law s = if (s i).head? = some true then p.law s else q.law s := by
  simp only [XProg.law, XProg.denote]; split_ifs <;> rfl

theorem encodeTuple_bit (b : Bool) : encodeTuple [[b]] = [true, b, false] := by
  simp [Prog.encodeTuple_single, Turing.MultiTapeTM.frame]

theorem S3_low (a b e : List Bool) (t : Fin 256)
    (ht : t.val < 40 ∨ (44 ≤ t.val ∧ t.val < 47)) : S3 D a b e t = [] := by
  have hm : t ∉ tmplTapes := fun hm => by have := tmplTapes_range t hm; omega
  have hv : ∀ u : Fin 256, 47 ≤ u.val → t ≠ u := fun u hu h => by subst h; omega
  rw [S3_not D a b e hm (fun h => by subst h; simp at ht) (hv _ (by decide)) (hv _ (by decide))]
  exact S2_other a b e t (hv _ (by decide)) (hv _ (by decide)) (hv _ (by decide))
    (hv _ (by decide))

/-- The code on the machine and the output, for any code. -/
theorem law_vm_out {N K : ℕ} (hN : 0 < N) (hK : 0 < K) (c : Code) (s : Store 256)
    (h0 : ∀ t : Fin 256, t.val < 40 ∨ (44 ≤ t.val ∧ t.val < 47) → s t = [])
    (h40 : s 40 = List.replicate K false) (h41 : s 41 = List.replicate N false)
    (h42 : s 42 = List.replicate (N * K) false) (h43 : s 43 = List.replicate (N * K) true) :
    ((XProg.seq (.frame vmE (compile c)) (.prog outP)).law s).map (fun s => s 0) =
      PMF.pure ((true :: exec N K c (fun x => s (tR x)) 179) ++ [false]) := by
  rw [XProg.law_seq, XProg.law_frame, vm_in s h0 h40 h41 h42 h43, law_compile hN hK, PMF.pure_map,
    PMF.pure_bind, XProg.law_prog, Prog.law_eq_run_of_coinFree _ coinFree_outP, PMF.pure_map]
  refine congrArg PMF.pure ?_
  simp only [outP, Prog.run_seq, Prog.run_prim, Prim.apply, Function.update_self]
  rw [vm_out_tR]

set_option maxRecDepth 100000 in
/-- **The valid branch** ends with the frame of the decoded bit on tape `0`. -/
theorem law_validP (hb : D.b = 22) (sk : SKt D) (C : List Bool) (ct : CTt D)
    (hC : C.length = predLen) :
    ((validP D).law (S2 ((skEnc D).enc sk) C ((ctEnc D).enc ct))).map (fun s => s 0) =
      PMF.pure [true, decodeBit D (decryptRaw (helperMap D) sk.1 (bpOf (progOf C)) sk.2 ct),
        false] := by
  set a := (skEnc D).enc sk
  set e := (ctEnc D).enc ct
  have hK : 0 < D.K := by have := D.hK; omega
  have h250 : S2 a C e 250 = [] := S2_other a C e _ (by decide) (by decide) (by decide) (by decide)
  have h43 : S3 D a C e 43 = List.replicate (D.N * D.K) true := by
    rw [S3_eq, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self]
  have hvm := law_vm_out (N := D.N) (K := D.K) D.N_pos hK decCode (S3 D a C e) (S3_low D a C e)
      (S3_tmpl D a C e (by simp [tmplList]) (by decide) (by decide) (by decide))
      (S3_tmpl D a C e (by simp [tmplList]) (by decide) (by decide) (by decide))
      (S3_tmpl D a C e (by simp [tmplList]) (by decide) (by decide) (by decide)) h43
  rw [exec_decCode hb hC (dInit_S3 D sk C ct)] at hvm
  rw [validP, XProg.law_seq, law_tmplsP 250 _ _ h250 (tmpl_ne_250 D), PMF.pure_bind,
    XProg.law_seq, XProg.law_prog, Prog.law_eq_run_of_coinFree _ coinFree_constP, PMF.pure_bind]
  exact hvm

theorem embedF_eq_extend {m : ℕ} (e : Fin m ↪ Fin 256) (s : Store 256) (g : Store m) :
    embedF e s g = Function.extend e g s := by
  funext l
  rcases embedF_cases e s g l with ⟨h1, h2⟩ | ⟨j, rfl, h2⟩
  · rw [h2, Function.extend_apply']
    rintro ⟨a, rfl⟩
    rw [partialInv_self] at h1
    exact Option.some_ne_none _ h1
  · rw [h2, e.injective.extend_apply]

theorem law_frame_prog {m : ℕ} (e : Fin m ↪ Fin 256) (p : Tape.Prog m) (hp : p.CoinFree)
    (s : Store 256) : (XProg.frame e (.prog p)).law s = PMF.pure ((Prog.map e p).run s) := by
  rw [XProg.law_frame, XProg.law_prog, Prog.law_eq_run_of_coinFree _ hp, PMF.pure_map,
    Prog.run_map e.injective, embedF_eq_extend]
  rfl

theorem law_parseX (s : Store 256) : parseX.law s = PMF.pure (parseD.run s) := by
  simp only [parseX, unfrX, XProg.law_seq, law_frame_prog _ _ Prog.coinFree_unfrP, PMF.pure_bind,
    XProg.law_prog, Prog.law_eq_run_of_coinFree _ (rfl : (Prog.clr (253 : Fin 256)).CoinFree)]
  rfl

theorem law_front (s : Store 256) (r : XProg 256) :
    (XProg.seq parseX (.seq lenX r)).law s = r.law (frontP.run s) := by
  rw [XProg.law_seq, law_parseX, PMF.pure_bind, XProg.law_seq, lenX,
    law_frame_prog _ _ (Prog.coinFree_lenEqP _), PMF.pure_bind]
  rfl

/-- **The law of `Dec`** on the output tape. -/
theorem law_decProgram (hb : D.b = 22) (sk : SKt D) (C : List Bool) (ct : CTt D) :
    ((decProgram D).law (inputStore 255
      (encodeTuple [pwW, (skEnc D).enc sk, C, (ctEnc D).enc ct]))).map (fun s => s 0) =
      PMF.pure (encodeTuple [decOutW D sk C ct]) := by
  rw [decProgram, law_front, run_frontP, law_ifBit']
  by_cases hC : C.length = predLen
  · rw [decide_eq_true hC, if_pos (by simp), law_validP D hb sk C ct hC, decOutW, if_pos hC,
      encodeTuple_bit]
  · rw [decide_eq_false hC, if_neg (by simp), XProg.law_prog,
      Prog.law_eq_run_of_coinFree _ coinFree_invP, PMF.pure_map, decOutW, if_neg hC,
      encodeTuple_bit]
    congr 1

/-! ### The machine -/

/-- The length index of a fixed-length encoding. -/
def dfixLen {α : Type} {n : ℕ} (_ : FixedEnc α n) : ℕ := n

/-- The longest input with a predicate word of at most `L` bits. -/
def decInputLength (L : ℕ) : ℕ :=
  (2 * pwW.length + 1) + (2 * dfixLen (skEnc D) + 1) + (2 * L + 1) + (2 * dfixLen (ctEnc D) + 1)

theorem length_decInput (sk : SKt D) (C : List Bool) (ct : CTt D) (hL : C.length ≤ L) :
    (encodeTuple [pwW, (skEnc D).enc sk, C, (ctEnc D).enc ct]).length ≤ decInputLength D L := by
  simp only [Prog.encodeTuple_cons, Prog.encodeTuple_nil, List.length_append, Prog.length_frame,
    List.length_nil, (skEnc D).length, (ctEnc D).length, decInputLength, dfixLen]
  omega

/-- **The `Dec` machine** for predicate words of at most `L` bits. -/
noncomputable def decMP (L : ℕ) : Machine :=
  (decProgram D).toMachineT 255 0 (decInputLength D L)

/-- **The `Dec` machine meets `DecSpec`.** -/
theorem decSpec_decMP (hb : D.b = 22) (L : ℕ) : DecSpec D L (decMP D L) := by
  refine ⟨XProg.deterministic_toMachineT _ (coinFree_decProgram D) _ _ _, fun sk C ct hL => ?_⟩
  rw [decMP, XProg.run_toMachineT _ (wf_decProgram D) _ _ _ _ (length_decInput D sk C ct hL),
    law_decProgram D hb]

theorem time_decMP (L : ℕ) : (decMP D L).time =
    XProg.totalTimeT (decProgram D) 255 0 (decInputLength D L) := rfl

end AdvancedEncryption.ExpLUT.Prog.DecM
