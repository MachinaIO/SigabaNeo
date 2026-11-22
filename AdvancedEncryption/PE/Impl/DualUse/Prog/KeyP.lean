import PE.Impl.DualUse.Prog.KeyTrySimLaw
import PE.Impl.DualUse.Prog.KeyFront
import PE.Impl.DualUse.Prog.UBound
import PE.Impl.DualUse.Prog.PsiBits
import PE.Impl.DualUse.ReductionOracle

/-!
# The key component of the reduction's handlers

`keyP sdP wfB … : XProg 256` answers a key query `C` (tape `1`) from the packed secret `p`
(tape `0`):

1. `sdP` (framed on the tapes `0, 2, …, 82`) turns the packed secret into the word
   `sdEnc (sdOf p)` of the simulation data (`SdSpec`; written by WS-M4);
2. the front end `frontP c.L W` (framed on the tapes `1, 83, …, 89`) replaces `C` by
   `frontV c.L W C` (`PE.Gates.DateWindow.law_frontP`);
3. on the first bit of the front end's output:
   * **a window predicate** (`true :: gsW W (parse C)`): the block `wfB` writes the word of
     `W_f = simW sd C` on tape `2` (`WfSpec`), the public key (the first `|pkEnc|` bits of
     `sdEnc sd`), the norm word `sW`, `powW K (B − 1)` and the templates of the key try are
     written on the tapes `1, 4, 5, 6 … 25`, then `keyTrySimCoinsP` (`ProgKey`) draws the key;
   * **a short non-window predicate** (`[false]`): the dummy key `skEnc (mpk, dummyKey)`;
   * **a long predicate** (`[]`): the empty word;
4. every tape but `0` is cleared.

**`law_keyP`**: on `io2 (encS p) C []` the law of `keyP` is `(KGsim (sdOf p) C).map (io2 · [] [])`
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
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow

/-! ### Generic helpers -/

section Helpers

variable {n m : ℕ}

/-- An embedded store, from its values on and off the frame. -/
theorem embedF_eq_of (e : Fin m ↪ Fin n) (s s' : Store n) (g : Store m)
    (h1 : ∀ j, s' (e j) = g j) (h2 : ∀ t, (∀ j, e j ≠ t) → s' t = s t) : embedF e s g = s' := by
  funext t
  rcases embedF_cases e s g t with ⟨hn, h⟩ | ⟨j, rfl, h⟩
  · rw [h, h2 t]
    intro j hj
    subst hj
    rw [partialInv_self] at hn
    exact Option.some_ne_none _ hn
  · rw [h, h1]

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

theorem io2_eSd (a b d : List Bool) :
    (fun j => io2 (R := 254) a b d (eSd j)) = io2 (R := 80) a d d := by
  funext j
  simp only [io2, eSd_val]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem embedF_eSd (a b a' : List Bool) :
    embedF eSd (io2 (R := 254) a b []) (io2 (R := 80) a' [] []) = io2 (R := 254) a' b [] := by
  refine embedF_eq_of _ _ _ _ (fun j => ?_) (fun t ht => ?_)
  · simp only [io2, eSd_val]; split_ifs <;> first | rfl | (exfalso; omega)
  · have h0 : t.val ≠ 0 := fun h => ht 0 (Fin.ext (by rw [eSd_val]; simp [h]))
    simp only [io2, h0, ite_false]

theorem io2_eFr (a b : List Bool) :
    (fun j => io2 (R := 254) a b [] (eFr j)) = io2 (R := 6) b [] [] := by
  funext j
  simp only [io2, eFr_val]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem embedF_eFr (a b b' : List Bool) :
    embedF eFr (io2 (R := 254) a b []) (io2 (R := 6) b' [] []) = io2 (R := 254) a b' [] := by
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
/-- **The `W_f` block**: from `sdEnc sd` (tape `0`) and the gate list `gsW W (parse C)` of a window
predicate of at most `c.L` bits (tape `1`), the word of `W_f = simW sd C` on tape `2`, `sdEnc sd`
kept on tape `0`, every other tape blank. -/
structure WfSpec (wfB : XProg 256) (W : ℕ) : Prop where
  wf : wfB.WF
  law : ∀ (sd : SimData hk c) (C : List Bool), C.length ≤ c.L → (∃ w : Window, winWord w = C) →
    wfB.law (io2 (R := 254) ((sdEnc hk c).enc sd) (SigabaNeo.Tape.Prog.gsW W (parse C)) []) =
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
/-- **The key component.** -/
noncomputable def keyP (sdP : XProg 82) (wfB : XProg 256) (W : ℕ) (cf : KeyCfg) : XProg 256 :=
  seq (frame eSd sdP) <| seq (frame eFr (frontP c.L W)) <|
    ifBit 1 (winB hk c wfB cf) (ifBlank 1 longB (dumB hk c))

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

end AdvancedEncryption.DualUse.Prog
