import PE.Impl.DualUse.Prog.KeyTrySimLaw
import PE.Impl.DualUse.Prog.KeyFront
import PE.Impl.DualUse.Prog.FrontSpec
import PE.Impl.DualUse.Prog.UBound
import PE.Impl.DualUse.Prog.PsiBits
import PE.Impl.DualUse.ReductionOracle

/-!
# The key component of the reduction's handlers

`keyPF sdP e fr wfB … : XProg 256` answers a key query `C` (tape `1`) from the packed secret `p`
(tape `0`):

1. `sdP` (framed on the tapes `0, 2, …, 82`) turns the packed secret into the word
   `sdEnc (sdOf p)` of the simulation data (`SdSpec`; written by WS-M4);
2. a front end `fr` meeting `FrontSpec` (framed by `e`) replaces `C` by `frontW c.L W C`
   (the branching-program front end is `frontBP`, `Prog/FrontBP.lean`);
3. on the first bit of the front end's output:
   * **a window predicate** (`true :: gsW W (parse C)`): the block `wfB` writes the word of
     `W_f = simW sd C` on tape `2` (`WfSpec`), the public key (the first `|pkEnc|` bits of
     `sdEnc sd`), the norm word `sW`, `powW K (B − 1)` and the templates of the key try are
     written on the tapes `1, 4, 5, 6 … 25`, then `keyTrySimCoinsP` (`ProgKey`) draws the key;
   * **a short non-window predicate** (`[false]`): the dummy key `skEnc (mpk, dummyKey)`;
   * **a long predicate** (`[]`): the empty word;
4. every tape but `0` is cleared.

**`law_keyPF`**: on `io2 (encS p) C []` the law of `keyPF` is `(KGsim (sdOf p) C).map (io2 · [] [])`
for every `C` (`Comps.law_key`), **`law_keyP_spPack`** in the form of the packed challenger.

The width: the SLP evaluator of the simulations (`slpEvalP`, 132 injective tapes), `simKeyP`
(94 tapes) and `keyTrySimCoinsP` (90 tapes) do not fit the 82 tapes of the other components
(`R = 80`); the key component has `R = 254` (`XProg 256`) and the other components are lifted
(`liftP`, `PE.Impl.DualUse.Prog.Lift`).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.XProg Matrix AdvancedEncryption.RingBTVW Cslib Cslib.Probability
  AdvancedEncryption.DualUse.Algo
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord

/-! ### Generic helpers -/

section Helpers

variable {n m : ℕ}

/-- Append a constant word to a tape. -/
def putW (t : Fin n) : List Bool → XProg n
  | [] => prog (.prim (.copy t t))
  | b :: w => seq (prog (.prim (.snoc t b))) (putW t w)

theorem law_putW (t : Fin n) : ∀ (w : List Bool) (s : Store n),
    (putW t w).law s = PMF.pure (Function.update s t (s t ++ w))
  | [], s => by
    rw [putW, law_prim]; simp [Prim.apply]
  | b :: w, s => by
    rw [putW, law_seq_pure (law_prim _ _), law_putW t w]
    simp [Prim.apply]

theorem wf_putW (t : Fin n) : ∀ w : List Bool, (putW t w).WF
  | [] => trivial
  | _ :: w => ⟨trivial, wf_putW t w⟩

/-- `dst := dst ++ take P src`, through the blank tapes `a`, `b`. -/
def prefP (P : ℕ) (src dst a b : Fin n) : XProg n :=
  seq (prog (.prim (.copy a src))) (seq (prog (Prog.moveFront P a dst b)) (prog (.prim (.clear a))))

theorem law_prefP (P : ℕ) {src dst a b : Fin n} (h1 : a ≠ dst) (h2 : a ≠ b) (h3 : dst ≠ b)
    (h4 : src ≠ a) (s : Store n) (ha : s a = []) (hb : s b = []) :
    (prefP P src dst a b).law s =
      PMF.pure (Function.update s dst (s dst ++ (s src).take P)) := by
  have hm := Prog.law_moveFront P h1 h2 h3 ((Prim.copy a src).apply s)
    (by simp [Prim.apply, Function.update_apply, h2.symm, hb])
  rw [prefP, law_seq_pure (law_prim _ _), law_seq_pure (by rw [law_prog]; exact hm), law_prim]
  congr 1
  funext t
  simp only [Prim.apply, Function.update_apply]
  by_cases hta : t = a
  · subst hta; simp [h1, ha]
  · by_cases htd : t = dst
    · subst htd; simp [h1.symm, h4]
    · simp [hta, htd]

theorem wf_prefP (P : ℕ) (src dst a b : Fin n) : (prefP P src dst a b).WF :=
  ⟨trivial, Prog.wf_moveFront _ _ _ _, trivial⟩

/-- Templates `t := replicate n false` (counter tape `c`). -/
def tmplP (c : Fin n) : List (Fin n × ℕ) → XProg n
  | [] => prog (.prim (.copy c c))
  | x :: l => seq (natP x.1 c x.2) (tmplP c l)

/-- The store after the templates. -/
def tmplS (l : List (Fin n × ℕ)) (s : Store n) : Store n :=
  l.foldl (fun s x => Function.update s x.1 (List.replicate x.2 false)) s

theorem law_tmplP (c : Fin n) : ∀ (l : List (Fin n × ℕ)) (s : Store n), s c = [] →
    (∀ x ∈ l, x.1 ≠ c) → (tmplP c l).law s = PMF.pure (tmplS l s)
  | [], s, _, _ => by rw [tmplP, law_prim]; simp [Prim.apply, tmplS]
  | x :: l, s, hc, hl => by
    rw [tmplP, law_seq_pure (law_natP (Ne.symm (hl x (by simp))) x.2 s hc)]
    exact law_tmplP c l _ (by rw [Function.update_of_ne (Ne.symm (hl x (by simp)))]; exact hc)
      (fun y hy => hl y (by simp [hy]))

theorem wf_tmplP (c : Fin n) : ∀ l : List (Fin n × ℕ), (∀ x ∈ l, x.1 ≠ c) → (tmplP c l).WF
  | [], _ => trivial
  | x :: l, hl => ⟨wf_natP (Ne.symm (hl x (by simp))) x.2,
      wf_tmplP c l fun y hy => hl y (by simp [hy])⟩

theorem tmplS_apply_of_not_mem (l : List (Fin n × ℕ)) (s : Store n) (t : Fin n)
    (h : ∀ x ∈ l, x.1 ≠ t) : tmplS l s t = s t := by
  induction l generalizing s with
  | nil => rfl
  | cons x l ih =>
    rw [tmplS, List.foldl_cons, ← tmplS, ih _ (fun y hy => h y (by simp [hy])),
      Function.update_of_ne (Ne.symm (h x (by simp)))]

end Helpers

/-! ### The frames -/

/-- The tapes of `sdP`: `0`, then `2, …, 82`. -/
def eSd : Fin 82 ↪ Fin 256 :=
  ⟨fun j => ⟨if j.val = 0 then 0 else j.val + 1, by split_ifs <;> omega⟩, by
    intro a b h
    simp only [Fin.mk.injEq] at h
    ext
    split_ifs at h <;> omega⟩

/-- The tapes of the front end: `1`, then `83, …, 89`. -/
def eFr : Fin 8 ↪ Fin 256 :=
  ⟨fun j => ⟨if j.val = 0 then 1 else j.val + 82, by split_ifs <;> omega⟩, by
    intro a b h
    simp only [Fin.mk.injEq] at h
    ext
    split_ifs at h <;> omega⟩

/-- The tapes of the key try: the first `90`. -/
def eKT : Fin 90 ↪ Fin 256 := Fin.castLEEmb (by norm_num)

theorem eSd_val (j : Fin 82) : (eSd j).val = if j.val = 0 then 0 else j.val + 1 := rfl
theorem eFr_val (j : Fin 8) : (eFr j).val = if j.val = 0 then 1 else j.val + 82 := rfl
theorem eKT_val (j : Fin 90) : (eKT j).val = j.val := rfl

theorem frEmb_eFr : FrEmb eFr := fun _ => rfl

theorem io2_eSd {α : Type} (a b d : α) :
    (fun j => io2 (R := 254) a b d (eSd j)) = io2 (R := 80) a d d := by
  funext j
  simp only [io2, eSd_val]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem embedF_eSd {α : Type} (a b a' d : α) :
    embedF eSd (io2 (R := 254) a b d) (io2 (R := 80) a' d d) = io2 (R := 254) a' b d := by
  refine embedF_eq_of _ _ _ _ (fun j => ?_) (fun t ht => ?_)
  · simp only [io2, eSd_val]; split_ifs <;> first | rfl | (exfalso; omega)
  · have h0 : t.val ≠ 0 := fun h => ht 0 (Fin.ext (by rw [eSd_val]; simp [h]))
    simp only [io2, h0, ite_false]

theorem io2_eFr {α : Type} (a b d : α) :
    (fun j => io2 (R := 254) a b d (eFr j)) = io2 (R := 6) b d d := by
  funext j
  simp only [io2, eFr_val]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem embedF_eFr {α : Type} (a b b' d : α) :
    embedF eFr (io2 (R := 254) a b d) (io2 (R := 6) b' d d) = io2 (R := 254) a b' d := by
  refine embedF_eq_of _ _ _ _ (fun j => ?_) (fun t ht => ?_)
  · simp only [io2, eFr_val]; split_ifs <;> first | rfl | (exfalso; omega)
  · have h1 : t.val ≠ 1 := fun h => ht 0 (Fin.ext (by rw [eFr_val]; simp [h]))
    simp only [io2, h1, ite_false]

/-! ### The specifications of the parameters -/

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

variable (hk c) in
/-- **The SimData block** (WS-M4): from the packed secret `p` (tape `0`, `XProg 82`), the word
`sdEnc (sdOf p)` alone on tape `0`. -/
structure SdSpec {Sig : Type} (sdP : XProg 82) (encS : Sig → List Bool)
    (sdOf : Sig → SimData hk c) (Ok : Sig → Prop) : Prop where
  wf : sdP.WF
  law : ∀ p, Ok p → sdP.law (io2 (R := 80) (encS p) [] []) =
    PMF.pure (io2 (R := 80) ((sdEnc hk c).enc (sdOf p)) [] [])

variable (hk c) in
/-- **The `W_f` block**: from `sdEnc sd` (tape `0`) and the block word `blockWord W C` of a predicate
`C` of the class (`ValidC`) of at most `c.L` bits (tape `1`), the word of `W_f = simW sd C` on
tape `2`, `sdEnc sd` kept on tape `0`, every other tape blank. -/
structure WfSpec (wfB : XProg 256) (W : ℕ) : Prop where
  wf : wfB.WF
  law : ∀ (sd : SimData hk c) (C : List Bool), C.length ≤ c.L → ValidC C →
    wfB.law (io2 (R := 254) ((sdEnc hk c).enc sd) (blockWord W C) []) =
      PMF.pure (Function.update (io2 (R := 254) ((sdEnc hk c).enc sd) [] []) 2
        (colsW N K k c.d (simW sd C)))

variable (hk c) in
/-- **The spec of a `W_f` block on the stream**: the block reads the instruction stream, the tail
`(blockWord W C).tail` of the block word (the head is the bit `f(0)`, kept by `bfX`, `cfX`). -/
structure WfSpecS (wfB : XProg 256) (W : ℕ) : Prop where
  wf : wfB.WF
  law : ∀ (sd : SimData hk c) (C : List Bool), C.length ≤ c.L → ValidC C →
    wfB.law (io2 (R := 254) ((sdEnc hk c).enc sd) (blockWord W C).tail []) =
      PMF.pure (Function.update (io2 (R := 254) ((sdEnc hk c).enc sd) [] []) 2
        (colsW N K k c.d (simW sd C)))

/-- The constants of the key try: the coefficient width `B`, the number `m` of coins and the norm
word `sW`. -/
structure KeyCfg where
  B : ℕ
  m : ℕ
  sW : List Bool

variable (hk c) in
/-- The configuration of the key try fits `c`. -/
structure KeyCfg.Valid (cf : KeyCfg) : Prop where
  h0 : 0 < k
  hK0 : 0 < K
  hB : 2 ^ cf.B ≤ 2 ^ K
  hm : nCoef c.d (TrapCol k) N * cf.B = cf.m
  hBig : c.Big = Finset.univ.map (keyEmbE (d := c.d) (Wt := TrapCol k) (N := N) cf.B hB cf.m hm)
  hsl : cf.sW.length = K
  hSmall : c.Small = keyBall (2 ^ K) c.d (TrapCol k) N (val cf.sW)
  hdec : c.dec = decG hk h0

/-! ### The program -/

variable (hk c) in
/-- The length of the word of a public key. -/
abbrev lenPK : ℕ := fixLen (pkEnc hk c)

variable (hk c) in
/-- The templates of the key try (tapes `6 … 25`). -/
def keyTmpl (cf : KeyCfg) : List (Fin 256 × ℕ) :=
  [(6, K), (7, N), (8, N * K), (9, cf.B), (10, (c.d + nT k) * N), (11, (c.d + nT k) * N * K),
    (12, k), (13, 2 * k), (14, 1), (15, 1), (16, c.d), (17, nT k), (18, c.d * (N * K)),
    (19, nT k * (N * K)), (20, 2 * k * (N * K)), (21, c.d * N), (22, lenPK hk c - N * K),
    (23, lenPK hk c), (24, lenPK hk c + (c.d + nT k) * N * K + 2 * k * (N * K)), (25, cf.m)]

/-- The tapes cleared at the end. -/
def keyClr : List (Fin 256) :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

theorem mem_keyClr (t : Fin 256) : t ∈ keyClr ↔ 1 ≤ t.val ∧ t.val ≤ 25 := by
  simp only [keyClr, List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff]
  constructor
  · rintro (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h) <;> rw [h] <;> decide
  · intro h; norm_num; omega

variable (hk c) in
/-- **The window branch**: `W_f`, the inputs and templates of the key try, the key try. -/
noncomputable def winB (wfB : XProg 256) (cf : KeyCfg) : XProg 256 :=
  seq (prog (.prim (.tail 1))) <| seq wfB <| seq (prefP (lenPK hk c) 0 1 100 101) <|
  seq (putW 4 cf.sW) <| seq (putW 5 (powW K (cf.B - 1))) <| seq (tmplP 120 (keyTmpl hk c cf)) <|
  seq (frame eKT (prog ProgKey.keyTrySimCoinsP)) (clearL keyClr)

variable (hk c) in
/-- **The dummy branch**: `skEnc (mpk, dummyKey)`. -/
noncomputable def dumB : XProg 256 :=
  seq (prog (.prim (.clear 1))) <| seq (prefP (lenPK hk c) 0 2 100 101) <|
  seq (putW 2 ((keyEnc (N := N) (K := K) c).enc (dummyKey c))) <|
  seq (prog (.prim (.copy 0 2))) (prog (.prim (.clear 2)))

/-- **The long branch**: the empty word. -/
def longB : XProg 256 := clearL [0]

variable (hk c) in
/-- The branches on the output of the front end. -/
noncomputable def branchB (wfB : XProg 256) (cf : KeyCfg) : XProg 256 :=
  ifBit 1 (winB hk c wfB cf) (ifBlank 1 longB (dumB hk c))

/-- Every tape but `0`. -/
@[irreducible] def clrAll : List (Fin 256) := (List.finRange 256).filter fun t => t ≠ 0

theorem mem_clrAll (t : Fin 256) : t ∈ clrAll ↔ t ≠ 0 := by simp [clrAll]

theorem length_clrAll_le : clrAll.length ≤ 256 := by
  rw [clrAll]; exact (List.length_filter_le _ _).trans (by rw [List.length_finRange])

variable (hk c) in
/-- **The key component** for a front end `fr` (`FrontSpec`): the SimData block, the front end, the
branches, then every tape but `0` cleared (for the per-tape length bound). -/
noncomputable def keyPF {R : ℕ} (sdP : XProg 82) (e : Fin (R + 2) ↪ Fin 256) (fr : XProg (R + 2))
    (wfB : XProg 256) (cf : KeyCfg) : XProg 256 :=
  seq (frame eSd sdP) <| seq (frame e fr) <| seq (branchB hk c wfB cf) (clearL clrAll)

/-! ### The laws of the branches -/

theorem law_longB (a : List Bool) : longB.law (io2 (R := 254) a [] []) =
    PMF.pure (io2 (R := 254) [] [] []) := by
  rw [longB, law_clearL]
  congr 1
  funext t
  simp only [List.mem_singleton, io2]
  by_cases h : t = 0
  · subst h; simp
  · have : t.val ≠ 0 := fun h' => h (Fin.ext h')
    simp [h, this]

theorem sdEnc_take (sd : SimData hk c) :
    ((sdEnc hk c).enc sd).take (lenPK hk c) = (pkEnc hk c).enc sd.mpk := by
  rw [sdEnc_enc, List.take_left' (length_enc_fixLen _ _)]

theorem law_dumB (sd : SimData hk c) :
    (dumB hk c).law (io2 (R := 254) ((sdEnc hk c).enc sd) [false] []) =
      PMF.pure (io2 (R := 254) ((skEnc hk c).enc (sd.mpk, dummyKey c)) [] []) := by
  rw [dumB, law_seq_pure (law_prim _ _),
    law_seq_pure (law_prefP _ (by decide) (by decide) (by decide) (by decide) _
      (by simp [Prim.apply, Function.update_apply, io2]) (by simp [Prim.apply, Function.update_apply, io2])),
    law_seq_pure (law_putW _ _ _), law_seq_pure (law_prim _ _), law_prim]
  congr 1
  funext t
  simp only [Prim.apply, Function.update_apply]
  by_cases h2 : t = 2
  · subst h2; simp [io2]
  · by_cases h0 : t = 0
    · subst h0
      simp [io2, sdEnc_take]
      rfl
    · by_cases h1 : t = 1
      · subst h1; simp [io2]
      · have : t.val ≠ 0 := fun h' => h0 (Fin.ext h')
        have : t.val ≠ 1 := fun h' => h1 (Fin.ext h')
        simp [h0, h1, h2, io2, *]

/-! ### The window branch -/

variable (hk c) in
/-- The store before the key try. -/
def winS (sdw wfw : List Bool) (cf : KeyCfg) : Store 256 :=
  tmplS (keyTmpl hk c cf) (Function.update (Function.update (Function.update (Function.update
    (io2 (R := 254) sdw [] []) 2 wfw) 1 (sdw.take (lenPK hk c))) 4 cf.sW) 5 (powW K (cf.B - 1)))

theorem keyTmpl_ne {cf : KeyCfg} {t : Fin 256} (ht : 26 ≤ t.val ∨ t.val ≤ 5 ∨ t.val = 120) :
    ∀ x ∈ keyTmpl hk c cf, x.1 ≠ t := by
  intro x hx
  simp only [keyTmpl, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    (rw [h]; intro e; rw [← e] at ht; simp at ht)

theorem winS_ge {sdw wfw : List Bool} {cf : KeyCfg} (t : Fin 256) (ht : 26 ≤ t.val) :
    winS hk c sdw wfw cf t = [] := by
  rw [winS, tmplS_apply_of_not_mem _ _ _ (keyTmpl_ne (Or.inl ht))]
  have h0 : t.val ≠ 0 := by omega
  have h1 : t ≠ 1 := fun e => by rw [e] at ht; revert ht; decide
  have h2 : t ≠ 2 := fun e => by rw [e] at ht; revert ht; decide
  have h4 : t ≠ 4 := fun e => by rw [e] at ht; revert ht; decide
  have h5 : t ≠ 5 := fun e => by rw [e] at ht; revert ht; decide
  have h1' : t.val ≠ 1 := fun e => h1 (Fin.ext e)
  simp [Function.update_apply, h1, h2, h4, h5, io2, h0, h1']

theorem winS_low {sdw wfw : List Bool} {cf : KeyCfg} (t : Fin 256) (ht : t.val ≤ 5) :
    winS hk c sdw wfw cf t = Function.update (Function.update (Function.update (Function.update
      (io2 (R := 254) sdw [] []) 2 wfw) 1 (sdw.take (lenPK hk c))) 4 cf.sW) 5 (powW K (cf.B - 1))
      t := by
  rw [winS, tmplS_apply_of_not_mem _ _ _ (keyTmpl_ne (Or.inr (Or.inl ht)))]

theorem winS_tmpl {sdw wfw : List Bool} {cf : KeyCfg} :
    let s := winS hk c sdw wfw cf
    (s 6).length = K ∧ (s 7).length = N ∧ (s 8).length = N * K ∧ (s 9).length = cf.B ∧
    (s 10).length = (c.d + nT k) * N ∧ (s 11).length = (c.d + nT k) * N * K ∧
    (s 12).length = k ∧ (s 13).length = 2 * k ∧ (s 14).length = 1 ∧ (s 15).length = 1 ∧
    (s 16).length = c.d ∧ (s 17).length = nT k ∧ (s 18).length = c.d * (N * K) ∧
    (s 19).length = nT k * (N * K) ∧ (s 20).length = 2 * k * (N * K) ∧ (s 21).length = c.d * N ∧
    (s 22).length = lenPK hk c - N * K ∧ (s 23).length = lenPK hk c ∧
    (s 24).length = lenPK hk c + (c.d + nT k) * N * K + 2 * k * (N * K) ∧
    (s 25).length = cf.m := by
  intro s
  simp only [s, winS, keyTmpl, tmplS, List.foldl_cons, List.foldl_nil, Function.update_apply]
  simp

theorem winS_120 {sdw wfw : List Bool} {cf : KeyCfg} : winS hk c sdw wfw cf 120 = [] := by
  rw [winS, tmplS_apply_of_not_mem _ _ _ (keyTmpl_ne (Or.inr (Or.inr rfl)))]
  simp [Function.update_apply, io2]

/-- The inputs and templates of the key try. -/
theorem law_prep (sdw wfw : List Bool) (cf : KeyCfg) (X : XProg 256) :
    (seq (prefP (lenPK hk c) 0 1 100 101) <| seq (putW 4 cf.sW) <|
      seq (putW 5 (powW K (cf.B - 1))) <| seq (tmplP 120 (keyTmpl hk c cf)) X).law
        (Function.update (io2 (R := 254) sdw [] []) 2 wfw) = X.law (winS hk c sdw wfw cf) := by
  rw [law_seq_pure (law_prefP _ (by decide) (by decide) (by decide) (by decide) _
      (by simp [Function.update_apply, io2]) (by simp [Function.update_apply, io2])),
    law_seq_pure (law_putW _ _ _), law_seq_pure (law_putW _ _ _),
    law_seq_pure (law_tmplP _ _ _ (by simp [Function.update_apply, io2])
      (keyTmpl_ne (Or.inr (Or.inr rfl))))]
  congr 2

theorem view_eKT (s : Store 256) (j : Fin 90) : (fun j => s (eKT j)) j = s ⟨j.val, by omega⟩ := rfl

theorem clear_final (s : Store 256) (w : List Bool) (hs : ∀ t : Fin 256, 26 ≤ t.val → s t = []) :
    (fun t => if t ∈ keyClr then [] else Function.update s 0 w t) = io2 (R := 254) w [] [] := by
  funext t
  by_cases h0 : t = 0
  · subst h0; simp [keyClr, io2]
  · have h0' : t.val ≠ 0 := fun e => h0 (Fin.ext e)
    simp only [io2, h0', ite_false, Function.update_of_ne h0]
    split_ifs with hm <;> first | rfl | (rw [mem_keyClr] at hm; exact hs t (by omega))

variable (hk c) in
theorem law_winB (wfB : XProg 256) {W : ℕ} (hwf : WfSpec hk c wfB W) (cf : KeyCfg)
    (hcf : cf.Valid hk c) (sd : SimData hk c) (C : List Bool) (hL : C.length ≤ c.L)
    (hC : ValidC C) :
    (winB hk c wfB cf).law
        (io2 (R := 254) ((sdEnc hk c).enc sd) (true :: blockWord W C) []) =
      (KGsim sd C).map fun w => io2 (R := 254) w [] [] := by
  have e1 : (Prim.tail 1).apply
      (io2 (R := 254) ((sdEnc hk c).enc sd) (true :: blockWord W C) []) =
      io2 (R := 254) ((sdEnc hk c).enc sd) (blockWord W C) [] := by
    funext t
    simp only [Prim.apply, Function.update_apply, io2]
    split_ifs <;> first | rfl | (exfalso; simp_all [Fin.ext_iff])
  rw [winB, law_seq_pure (law_prim _ _), e1, law_seq_pure (hwf.law sd C hL hC), law_prep, law_seq,
    law_frame, law_prog]
  set s := winS hk c ((sdEnc hk c).enc sd) (colsW N K k c.d (simW sd C)) cf with hs
  have hlow := fun t ht => winS_low (hk := hk) (c := c) (sdw := (sdEnc hk c).enc sd)
    (wfw := colsW N K k c.d (simW sd C)) (cf := cf) t ht
  obtain ⟨t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23,
    t24, t25⟩ := winS_tmpl (hk := hk) (c := c) (sdw := (sdEnc hk c).enc sd)
    (wfw := colsW N K k c.d (simW sd C)) (cf := cf)
  have s1 : s 1 = (pkEnc hk c).enc sd.mpk := by
    rw [hs, hlow 1 (by decide)]; simp [Function.update_apply, sdEnc_take]
  have s2 : s 2 = colsW N K k c.d (simW sd C) := by
    rw [hs, hlow 2 (by decide)]; simp [Function.update_apply]
  have s3 : s 3 = [] := by rw [hs, hlow 3 (by decide)]; simp [Function.update_apply, io2]
  have s4 : s 4 = cf.sW := by rw [hs, hlow 4 (by decide)]; simp [Function.update_apply]
  have s5 : s 5 = powW K (cf.B - 1) := by rw [hs, hlow 5 (by decide)]; simp
  rw [ProgKey.law_keyTrySimCoinsP_KGsim hk hcf.h0 hcf.hK0 cf.B hcf.hB cf.m hcf.hm hcf.hBig hcf.hsl
    rfl hcf.hSmall hcf.hdec sd C hL hC (P := lenPK hk c) (fun j => s (eKT j))
    (fun j hj => winS_ge _ (by rw [eKT_val]; exact hj)) (by exact s3) (by exact s1) (by exact s2)
    (by exact s4) (by show (s 1).length = _; rw [s1]; exact length_enc_fixLen _ _) (by exact s5)
    (by exact t6) (by exact t7) (by exact t8) (by exact t9) (by exact t10) (by exact t11)
    (by exact t12) (by exact t13) (by exact t14) (by exact t15) (by exact t16) (by exact t17)
    (by exact t18) (by exact t19) (by exact t20) (by exact t21) (by exact t22) (by exact t23)
    (by exact t24) (by exact t25), PMF.map_comp, PMF.bind_map]
  rw [← PMF.bind_pure_comp]
  congr 1
  funext w
  simp only [Function.comp_apply]
  have e0 : eKT 0 = 0 := rfl
  rw [embedF_upd, embedF_comp, law_clearL, e0, clear_final s w (fun t ht => by rw [hs]; exact winS_ge t ht)]

/-! ### The law of the key component -/

variable (hk c) in
/-- The branches on the output of the front end. -/
theorem law_branchB {wfB : XProg 256} {W : ℕ} (hwf : WfSpec hk c wfB W) (cf : KeyCfg)
    (hcf : cf.Valid hk c) (sd : SimData hk c) (C : List Bool) :
    (branchB hk c wfB cf).law (io2 (R := 254) ((sdEnc hk c).enc sd) (frontW c.L W C) []) =
      (KGsim sd C).map fun w => io2 (R := 254) w [] [] := by
  rw [branchB, law_ifBit]
  by_cases hl : C.length ≤ c.L
  · by_cases hw : ValidC C
    · rw [frontW, frontG_valid hl hw, if_pos (by simp [io2])]
      exact law_winB hk c wfB hwf cf hcf sd C hl hw
    · unfold KGsim
      rw [if_pos hl, frontW, frontG_short_not hl hw, if_neg hw, if_neg (by simp [io2]), law_ifBlank,
        if_neg (by simp [io2]), law_dumB, PMF.pure_map]
  · unfold KGsim
    rw [frontW, frontG_long hl, if_neg hl, if_neg (by simp [io2]), law_ifBlank, if_pos (by simp [io2]),
      law_longB, PMF.pure_map]

theorem law_clrAll (w : List Bool) : (clearL clrAll).law (io2 (R := 254) w [] []) =
    PMF.pure (io2 (R := 254) w [] []) := by
  rw [law_clearL]
  congr 1
  funext t
  simp only [mem_clrAll]
  by_cases h : t = 0
  · subst h; simp
  · have : t.val ≠ 0 := fun e => h (Fin.ext e)
    simp [h, io2, this]

variable (hk c) in
/-- **The law of the key component** for any front end meeting `FrontSpec`: for every query `C`,
the image of the simulated key oracle `KGsim (sdOf p) C` of the simulation data of the packed
secret. -/
theorem law_keyPF {Sig : Type} {sdP : XProg 82} {encS : Sig → List Bool}
    {sdOf : Sig → SimData hk c} {Ok : Sig → Prop} (hsd : SdSpec hk c sdP encS sdOf Ok)
    {R : ℕ} {e : Fin (R + 2) ↪ Fin 256} (he : FrEmb e) {fr : XProg (R + 2)} {W : ℕ}
    {FT FL : ℕ → ℕ} {FS : ℕ} (hfr : FrontSpec fr c.L W FT FL FS)
    {wfB : XProg 256} (hwf : WfSpec hk c wfB W) (cf : KeyCfg) (hcf : cf.Valid hk c)
    (p : Sig) (hp : Ok p) (C : List Bool) :
    (keyPF hk c sdP e fr wfB cf).law (io2 (R := 254) (encS p) C []) =
      (KGsim (sdOf p) C).map fun w => io2 (R := 254) w [] [] := by
  rw [keyPF, law_seq_pure (by rw [law_frame, io2_eSd, hsd.law p hp, PMF.pure_map, embedF_eSd]),
    law_seq_pure (law_frame_frEmb he hfr _ C), law_seq, law_branchB hk c hwf cf hcf, PMF.bind_map]
  have e : (clearL clrAll).law ∘ (fun w => io2 (R := 254) w [] []) =
      PMF.pure ∘ (fun w => io2 (R := 254) w [] []) := funext law_clrAll
  rw [e, PMF.bind_pure_comp]

theorem wf_keyPF {sdP : XProg 82} (hsd : sdP.WF) {R : ℕ} (e : Fin (R + 2) ↪ Fin 256)
    {fr : XProg (R + 2)} (hfr : fr.WF) {wfB : XProg 256}
    (hwf : wfB.WF) (cf : KeyCfg) : (keyPF hk c sdP e fr wfB cf).WF :=
  ⟨hsd, hfr,
    ⟨⟨trivial, hwf, wf_prefP _ _ _ _ _, wf_putW _ _, wf_putW _ _,
      wf_tmplP _ _ (keyTmpl_ne (Or.inr (Or.inr rfl))), ProgKey.wf_keyTrySimCoinsP, wf_clearL _⟩,
    wf_clearL _, trivial, wf_prefP _ _ _ _ _, wf_putW _ _, trivial, trivial⟩, wf_clearL _⟩

/-! ### The packed challenger -/

variable {Sec Inst : Type}

/-- **The key component of the packed challenger** (`Comps.law_key` for `spPack`, `R = 254`): the
secret word `encS (inst, σ)` of the codes. -/
theorem law_keyP_spPack [NeZero c.d] (st : PUniv.Attr → PMF (Inst × Sec))
    (viewI : Inst → Sec → PK hk c × CT hk c) (sdI : Inst → Sec → SimData hk c)
    {sdP : XProg 82} {encS : Inst × Sec → List Bool} {Ok : Inst × Sec → Prop}
    (hsd : SdSpec hk c sdP encS (fun p => sdI p.1 p.2) Ok)
    {R : ℕ} {e : Fin (R + 2) ↪ Fin 256} (he : FrEmb e) {fr : XProg (R + 2)} {W : ℕ}
    {FT FL : ℕ → ℕ} {FS : ℕ} (hfr : FrontSpec fr c.L W FT FL FS)
    {wfB : XProg 256} (hwf : WfSpec hk c wfB W) (cf : KeyCfg) (hcf : cf.Valid hk c)
    (p : Inst × Sec) (hp : Ok p) (C : List Bool) :
    (keyPF hk c sdP e fr wfB cf).law (io2 (R := 254) (encS p) C []) =
      ((spPack st viewI sdI).key p C).map fun sk => io2 (R := 254) sk [] [] :=
  law_keyPF hk c hsd he hfr hwf cf hcf p hp C

end AdvancedEncryption.DualUse.Prog
