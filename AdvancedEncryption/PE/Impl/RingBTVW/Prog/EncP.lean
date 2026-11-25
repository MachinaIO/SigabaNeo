import PE.Impl.RingBTVW.Prog.EncSem
import SigabaNeoStd.Machines.Prog.Moves

/-!
# `Enc` as a tape program

`encP X : XProg 124` realizes the law `encM` of `Enc` exactly:

1. **parsing** (`encParseP`): the input `encodeTuple [pw, mpk, x, [M]]` (tape `120`) is read frame by
   frame (`unframeP`, counters built by `natP`): the fields `B₀`, `B₁`, the `B_j`, `p` of `mpk`,
   the date bits and the message bit land on the tapes `1 … 6`;
2. **the coins** (framed samplers, scratch `52 … 56`): `s`, `e₀`, `e₁ = [σ | ea | ez]`, the binary
   `Rᵢ`, the flooding errors, `e'` on the tapes `7 … 12`;
3. **templates** (`natP`, built by doubling): the output register `0` and the tapes `13 … 38`;
4. **the core** `encCoreP` (framed on the tapes `0 … 119`);
5. **the output**: the frame of the output register on tape `122` (`frameApP`).
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.XProg Matrix AdvancedEncryption.RingBTVW.Fresh Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

/-! ### Parsing -/

/-- Drop `n` bits of the input (counter template `121`, scratch `123`). -/
def dropChunk (n : ℕ) : XProg 124 :=
  seq (natP 121 123 n) (seq (dropP 120 123 121) (prog (.prim (.clear 121))))

/-- Read `n` framed bits of the input into `D`. -/
def ufChunk (D : Fin 124) (n : ℕ) : XProg 124 :=
  seq (natP 121 123 n) (seq (unframeP 120 D 123 121) (prog (.prim (.clear 121))))

theorem law_dropChunk (n : ℕ) (s : Store 124) (h121 : s 121 = []) (h123 : s 123 = []) :
    (dropChunk n).law s = PMF.pure (Function.update s 120 ((s 120).drop n)) := by
  rw [dropChunk, law_seq, law_natP (by decide) n s h123, PMF.pure_bind, law_seq,
    law_dropP (by decide) (by decide) _ (by simp [h123]), PMF.pure_bind, law_prim]
  congr 1
  funext t
  simp only [Prim.apply, Function.update_apply]
  by_cases h1 : t = 121
  · subst h1; simp [h121]
  · simp [h1]

theorem law_ufChunk (D : Fin 124) (hD : D.val < 120) (n : ℕ) (s : Store 124) (h121 : s 121 = [])
    (h123 : s 123 = []) (u rest : List Bool) (hW : s 120 = u.flatMap (fun b => [true, b]) ++ rest)
    (hn : u.length = n) :
    (ufChunk D n).law s = PMF.pure (Function.update (Function.update s D (s D ++ u)) 120 rest) := by
  have hD120 : (120 : Fin 124) ≠ D := fun h => by subst h; simp at hD
  have hD121 : D ≠ 121 := fun h => by subst h; simp at hD
  have hD123 : D ≠ 123 := fun h => by subst h; simp at hD
  rw [ufChunk, law_seq, law_natP (by decide) n s h123, PMF.pure_bind, law_seq,
    law_unframeP hD120 (by decide) hD123 (by decide) _ (by simp [h123]) u rest
      (by simp [Function.update_apply, hW]) (by simp [hn]), PMF.pure_bind, law_prim]
  congr 1
  funext t
  simp only [Prim.apply, Function.update_apply]
  by_cases h1 : t = 121
  · subst h1; simp [h121, Ne.symm hD121]
  · by_cases h2 : t = D
    · subst h2; simp [h1, hD120]
    · simp [h1, h2]

/-! ### The coins -/

/-- The sampler appending to tape `t` (scratch `52 … 56`). -/
def eSm (t : Fin 124) (ht : 57 ≤ t.val ∨ t.val ≤ 51) (ht' : t ≠ 121) : Fin 7 ↪ Fin 124 :=
  ⟨![t, 121, 52, 53, 54, 55, 56], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [Fin.ext_iff] <;> omega⟩

theorem eSm_apply (t : Fin 124) (ht : 57 ≤ t.val ∨ t.val ≤ 51) (ht' : t ≠ 121) (j : Fin 7) :
    eSm t ht ht' j = ![t, 121, 52, 53, 54, 55, 56] j := rfl

abbrev e7 := eSm 7 (by decide) (by decide)
abbrev e8 := eSm 8 (by decide) (by decide)
abbrev e9 := eSm 9 (by decide) (by decide)
abbrev e10 := eSm 10 (by decide) (by decide)
abbrev e11 := eSm 11 (by decide) (by decide)
abbrev e12 := eSm 12 (by decide) (by decide)

/-- **A framed sampler followed by a program** (stores of 124 tapes). -/
theorem law_seq_smp124 {e : Fin 7 ↪ Fin 124} {p : XProg 7} {μ : PMF (List Bool)}
    (hp : AppendLaw p 0 P5 μ) {α : Type} (ν : PMF α) (g : α → List Bool) (hμ : μ = ν.map g)
    (q : XProg 124) (s : Store 124) (hs : ∀ j : Fin 7, 2 ≤ j.val → s (e j) = []) :
    (seq (frame e p) q).law s = ν.bind fun v => q.law (Function.update s (e 0) (s (e 0) ++ g v)) := by
  have hP : P5 (fun j => s (e j)) :=
    ⟨⟨hs 2 (by decide), hs 3 (by decide), hs 4 (by decide)⟩, hs 5 (by decide), hs 6 (by decide)⟩
  rw [law_seq, appendLaw_frame e hp s hP, hμ, PMF.map_comp, PMF.bind_map]
  rfl

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- **The parser of the input of `Enc`.** -/
def encParseP : XProg 124 :=
  seq (dropChunk (2 * pw.length + 1)) <|
  seq (ufChunk 1 ((Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K)))) <|
  seq (ufChunk 2 ((Enum.list (α := Fin 1)).length * ((Enum.list (α := TrapCol k)).length * (N * K)))) <|
  seq (ufChunk 3 ((Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).length *
    ((Enum.list (α := Fin 1)).length * ((Enum.list (α := RingBTVW.Fresh.Col k)).length * (N * K))))) <|
  seq (ufChunk 4 (N * K)) <| seq (prog (.prim (.tail 120))) <| seq (ufChunk 5 nA) <|
  seq (prog (.prim (.tail 120))) <| ufChunk 6 1

theorem flatMap_pairs_append (u v : List Bool) :
    (u ++ v).flatMap (fun b => [true, b]) =
      u.flatMap (fun b => [true, b]) ++ v.flatMap (fun b => [true, b]) := List.flatMap_append

theorem length_frameE (w : List Bool) : (Turing.MultiTapeTM.frame w).length = 2 * w.length + 1 := by
  simp [Turing.MultiTapeTM.frame]; ring

set_option maxHeartbeats 4000000 in
/-- **The law of the parser.** -/
theorem law_encParseP (mpk : PK hk c) (x : PUniv.Attr) (b : Bool) (s : Store 124)
    (hin : s 120 = encodeTuple [pw, (pkEnc hk c).enc mpk, encAttr x, [b]])
    (hD : ∀ i : Fin 124, 1 ≤ i.val → i.val ≤ 6 → s i = []) (h121 : s 121 = []) (h123 : s 123 = []) :
    (encParseP hk c).law s = PMF.pure
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update s 1 ((matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc mpk.B₀))
          2 ((matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc mpk.B₁))
          3 ((FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
            (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Fresh.Col k))).enc mpk.Bj))
          4 ((ringEnc N K).enc mpk.p)) 5 (encAttr x)) 6 [b]) 120 [false]) := by
  have e : encodeTuple [pw, (pkEnc hk c).enc mpk, encAttr x, [b]] =
      Turing.MultiTapeTM.frame pw ++ (Turing.MultiTapeTM.frame ((pkEnc hk c).enc mpk) ++
        (Turing.MultiTapeTM.frame (encAttr x) ++ (Turing.MultiTapeTM.frame [b] ++ []))) := rfl
  rw [encParseP, law_seq, law_dropChunk _ s h121 h123, PMF.pure_bind]
  rw [hin, e, ← length_frameE, List.drop_left' rfl]
  set wB0 := (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc mpk.B₀
  set wB1 := (matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc mpk.B₁
  set wBj := (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
    (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Fresh.Col k))).enc mpk.Bj
  set wp := (ringEnc N K).enc mpk.p
  set P : List Bool → List Bool := fun u => u.flatMap (fun b => [true, b])
  have hpk : Turing.MultiTapeTM.frame ((pkEnc hk c).enc mpk) =
      P wB0 ++ (P wB1 ++ (P wBj ++ (P wp ++ [false]))) := by
    show (wB0 ++ (wB1 ++ (wBj ++ wp))).flatMap _ ++ [false] = _
    simp only [List.flatMap_append, List.append_assoc, P]
  have hfx : ∀ w : List Bool, Turing.MultiTapeTM.frame w = P w ++ [false] := fun w => rfl
  rw [hpk, hfx (encAttr x), hfx [b]]
  simp only [List.append_assoc, List.append_nil]
  have hs : ∀ i : Fin 124, i ≠ 120 → Function.update s 120 (P wB0 ++ (P wB1 ++ (P wBj ++ (P wp ++
      ([false] ++ (P (encAttr x) ++ ([false] ++ (P [b] ++ [false])))))))) i = s i :=
    fun i hi => Function.update_of_ne hi _ _
  rw [law_seq, law_ufChunk 1 (by decide) _ _ (by simp [h121]) (by simp [h123]) wB0 _ (by simp only [Function.update_self]; rfl)
    ((matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).length _), PMF.pure_bind]
  rw [law_seq, law_ufChunk 2 (by decide) _ _ (by simp [h121]) (by simp [h123]) wB1 _ (by simp only [Function.update_self]; rfl)
    ((matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).length _), PMF.pure_bind]
  rw [law_seq, law_ufChunk 3 (by decide) _ _ (by simp [h121]) (by simp [h123]) wBj _ (by simp only [Function.update_self]; rfl)
    ((FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
      (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Fresh.Col k))).length _), PMF.pure_bind]
  rw [law_seq, law_ufChunk 4 (by decide) _ _ (by simp [h121]) (by simp [h123]) wp _ (by simp only [Function.update_self]; rfl)
    ((ringEnc N K).length _), PMF.pure_bind]
  rw [law_seq, law_prim, PMF.pure_bind]
  rw [law_seq, law_ufChunk 5 (by decide) _ _ (by simp [Prim.apply, h121]) (by simp [Prim.apply, h123])
    (encAttr x) _ (by simp only [Prim.apply, Function.update_self, List.tail_cons]; rfl) (BranchingProgram.length_encAttr x), PMF.pure_bind]
  rw [law_seq, law_prim, PMF.pure_bind]
  rw [law_ufChunk 6 (by decide) 1 _ ?q1 ?q2 [b] [false] ?q3 rfl]
  · congr 1
    funext t
    fin_cases t <;> simp [Prim.apply, hD]
  · simp [Prim.apply, h121]
  · simp [Prim.apply, h123]
  · simp only [Prim.apply, Function.update_self, List.tail_cons]; rfl

/-! ### Templates -/

/-- Templates `t := 0^n` for a list of tapes (scratch `123`). -/
def natL : List (Fin 124 × ℕ) → XProg 124
  | [] => prog (.prim (.copy 123 123))
  | p :: l => seq (natP p.1 123 p.2) (natL l)

theorem law_natL : ∀ (l : List (Fin 124 × ℕ)) (s : Store 124), (∀ p ∈ l, p.1 ≠ 123) → s 123 = [] →
    (natL l).law s = PMF.pure (l.foldl (fun (t : Store 124) (q : Fin 124 × ℕ) =>
      Function.update t q.1 (List.replicate q.2 false)) s)
  | [], s, _, _ => by rw [natL, law_prim]; simp [Prim.apply]
  | p :: l, s, hl, hs => by
    rw [natL, law_seq, law_natP (Ne.symm (hl p (by simp))) p.2 s hs, PMF.pure_bind,
      law_natL l _ (fun q hq => hl q (by simp [hq])) (by
        rw [Function.update_of_ne (Ne.symm (hl p (by simp)))]; exact hs)]
    rfl

theorem wf_natL : ∀ (l : List (Fin 124 × ℕ)), (∀ p ∈ l, p.1 ≠ 123) → (natL l).WF
  | [], _ => trivial
  | p :: l, h => ⟨wf_natP (Ne.symm (h p (by simp))) _, wf_natL l (fun q hq => h q (by simp [hq]))⟩

/-- The templates of the core and the output register. -/
def tmplList : List (Fin 124 × ℕ) :=
  [(0, ctLen hk c), (13, K), (14, N), (15, N * K), (16, 1), (17, 1), (18, k), (19, c.d),
    (20, nTrap k), (21, 2 * k), (22, nA), (23, 2 * k * (N * K)), (24, 2 * (2 * k) * (N * K)),
    (25, 2 * (2 * k) * N), (26, 2 * k * N), (27, nA * (2 * (2 * k))), (28, (k - K) * N),
    (29, nJenc (N := N) hk), (30, 1 * c.d * (N * K)), (31, c.d * N), (32, 1 * nTrap k * (N * K)),
    (33, nTrap k * N), (34, nA * (2 * (2 * k) * (N * K))), (35, nA * (2 * (2 * k)) * (k * N)),
    (36, nJenc (N := N) hk * (1 * (2 * k) * (N * K))), (37, N * K - K), (38, k * (N * K))]

theorem tmplList_ne : ∀ p ∈ tmplList hk c, p.1 ≠ 123 := by
  intro p hp
  simp only [tmplList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
    decide

/-! ### The core and the output -/

theorem le118 : (118 : ℕ) ≤ 122 := by norm_num

/-- The tapes `0 … 119`. -/
abbrev e120 : Fin 120 ↪ Fin 124 := liftE le118

/-- Templates, the core, the frame of the output register on tape `122`. -/
def encTail : XProg 124 :=
  seq (natL (tmplList hk c)) (seq (frame e120 (prog encCoreP)) (frameApP 122 0 123 121))

theorem foldl_upd_not_mem : ∀ (l : List (Fin 124 × ℕ)) (s : Store 124) (t : Fin 124),
    (∀ p ∈ l, p.1 ≠ t) →
    l.foldl (fun (u : Store 124) (q : Fin 124 × ℕ) => Function.update u q.1 (List.replicate q.2 false))
      s t = s t
  | [], s, t, _ => rfl
  | p :: l, s, t, h => by
    rw [List.foldl_cons, foldl_upd_not_mem l _ t (fun q hq => h q (by simp [hq])),
      Function.update_of_ne (Ne.symm (h p (by simp)))]

theorem tmpl_lt : ∀ p ∈ tmplList hk c, ∀ t : Fin 124, 39 ≤ t.val → p.1 ≠ t := by
  intro p hp t ht
  simp only [tmplList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (intro h; rw [← h] at ht; simp at ht)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **The tail of `Enc`**: from the words of the fields and the coins on the tapes `1 … 12` (the
other tapes below `124` blank but `120`), the output tape receives the tuple of the ciphertext. -/
theorem law_encTail (hN : 0 < N) (hK : 0 < K) (mpk : PK hk c) (x : PUniv.Attr) (b : Bool)
    (r : EncCoins (Sdw (N := N) hk) (Fin c.d) (TrapCol k))
    (rr : (Sdw (N := N) hk).Attr × RingBTVW.Fresh.Col k → (Fin c.d → Bool)) (hRm : r.Rm = rMat rr)
    (s : Store 124) (hS : ∀ i : Fin 124, (i.val = 0 ∨ 13 ≤ i.val) → i.val ≠ 120 → s i = [])
    (h1 : s 1 = (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc mpk.B₀)
    (h2 : s 2 = (matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc mpk.B₁)
    (h3 : s 3 = (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
      (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Fresh.Col k))).enc mpk.Bj)
    (h4 : s 4 = (ringEnc N K).enc mpk.p) (h5 : s 5 = encAttr x) (h6 : s 6 = [b])
    (h7 : s 7 = (ringEnc N K).enc r.s)
    (h8 : s 8 = (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc r.e₀)
    (h9 : s 9 = (matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc r.e₁)
    (h10 : s 10 = (rmTEnc c).enc (rMat (R := Rg N K) rr))
    (h11 : s 11 = (eEnc (N := N) hk).enc r.ej) (h12 : s 12 = (ringEnc N K).enc r.e') :
    ((encTail hk c).law s).map (fun s => s 122) =
      PMF.pure (encodeTuple [(ctEnc hk c).enc (encrypt mpk (attrBits x) b r)]) := by
  rw [encTail, law_seq, law_natL _ s (tmplList_ne hk c) (hS 123 (by simp) (by simp)),
    PMF.pure_bind, law_seq, law_frame, law_prog_run _ noGrow_encCoreP, PMF.pure_map, PMF.pure_bind,
    law_frameApP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) _ ?q1 ?q2,
    PMF.pure_map]
  · set S1 := (tmplList hk c).foldl (fun (t : Store 124) (q : Fin 124 × ℕ) =>
      Function.update t q.1 (List.replicate q.2 false)) s with hS1
    have h0 : embedF e120 S1 (encCoreP.run fun j => S1 (e120 j)) 0 =
        encCoreP.run (fun j => S1 (e120 j)) 0 := embedF_apply_self e120 S1 _ 0
    have h122 : embedF e120 S1 (encCoreP.run fun j => S1 (e120 j)) 122 = [] := by
      rcases embedF_cases e120 S1 (encCoreP.run fun j => S1 (e120 j)) 122 with ⟨-, h⟩ | ⟨j, hj, -⟩
      · rw [h, hS1]; simp [tmplList, hS]
      · exact absurd (congrArg Fin.val hj) (by simp; omega)
    simp only [Function.update_self, h122, List.nil_append, h0]
    rw [encCore_out hk c hN hK mpk x b r rr hRm]
    · rw [show encodeTuple [(ctEnc hk c).enc (encrypt mpk (attrBits x) b r)] =
        Turing.MultiTapeTM.frame ((ctEnc hk c).enc (encrypt mpk (attrBits x) b r)) ++ []
        from rfl, List.append_nil]
    · intro i hi
      show S1 (e120 i) = []
      rw [hS1, foldl_upd_not_mem _ _ _ (fun p hp => tmpl_lt hk c p hp (e120 i) (by simp; omega))]
      exact hS _ (Or.inr (by simp; omega)) (by simp; omega)
    all_goals (simp only [hS1, tmplList, List.foldl]; simp only [Function.update_apply]
               simp (config := { decide := true }) only [Fin.isValue, ite_true, ite_false]
               try first | rfl | simp | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h6 |
                 exact h7 | exact h8 | exact h9 | exact h10 | exact h11 | exact h12)
  all_goals
    rcases embedF_cases e120 _ _ _ with ⟨-, h⟩ | ⟨j, hj, -⟩
    · rw [h, foldl_upd_not_mem _ _ _ (fun p hp => tmpl_lt hk c p hp _ (by decide))]
      exact hS _ (Or.inr (by decide)) (by decide)
    · exact absurd (congrArg Fin.val hj) (by simp; omega)

/-- **`Enc` as a tape program.** -/
def encP (X : ChiSampler c) : XProg 124 :=
  seq (encParseP hk c) <| seq (frame e7 (coinsF (N * K))) <|
  seq (frame e8 (repF ((Enum.list (α := Fin c.d)).length * N) X.P)) <|
  seq (frame e9 (repF N X.P)) <|
  seq (frame e9 (repF ((Enum.list (α := RingBTVW.Fresh.Col k)).length * N) X.P)) <|
  seq (frame e9 (repF ((Enum.list (α := RingBTVW.Fresh.Col k)).length * N) X.P)) <|
  seq (frame e10 (repF (nR hk c) (entB N K))) <| seq (frame e11 (repF (nE (N := N) hk) (entF K c.w))) <|
  seq (frame e12 (repF N X.P)) <| encTail hk c

macro "smp_tac" : tactic => `(tactic| (
  intro j hj
  fin_cases j <;> simp at hj <;>
    simp [eSm_apply, Function.update_apply, inputStore]))

set_option maxHeartbeats 16000000 in
/-- **The law of `Enc`**: on the input `encodeTuple [pw, mpk, x, [M]]`, the output tape has the
law of the encoded `ct ← encM mpk x M`. -/
theorem law_encP [NeZero c.d] (hN : 0 < N) (hK : 0 < K) (X : ChiSampler c) (mpk : PK hk c)
    (x : PUniv.Attr) (b : Bool) :
    ((encP hk c X).law (inputStore 120 (encodeTuple [pw, (pkEnc hk c).enc mpk, encAttr x, [b]]))).map
      (fun s => s 122) =
      (encM hk c mpk x b).map fun ct => encodeTuple [(ctEnc hk c).enc ct] := by
  have hχT : catPow (μχ c) N = (χR c).map (ringEnc N K).enc := (χR_enc c).symm
  have hχE : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Enum ι],
      catPow (μχ c) ((Enum.list (α := ι)).length * N) =
      (rowLaw (χR c) ι).map (matEnc (N := N) (K := K) (Fin 1) ι).enc := by
    intro ι _ _ _
    rw [rowLaw_enc, χR_enc, catPow_mul]
  have hRm : catPow (μB N K) (nR hk c) =
      (Cslib.Probability.PMF.pi fun _ : (Sdw (N := N) hk).Attr × RingBTVW.Fresh.Col k =>
        PMF.uniformOfFintype (Fin c.d → Bool)).map fun rr => (rmTEnc c).enc (rMat (R := Rg N K) rr) := by
    refine (rmLaw_eq hk c hN hK).symm.trans ?_
    exact PMF.map_comp _ _ _
  rw [encP, law_seq, law_encParseP hk c mpk x b _ (by simp [inputStore])
    (fun i h1 h2 => by
      rw [inputStore, Function.update_of_ne (fun h => by subst h; simp at h2)]) (by simp [inputStore]) (by simp [inputStore]),
    PMF.pure_bind]
  rw [encM, PMF.map_comp, show coinsM hk c = lawCoinsC hk c from rfl, lawCoinsC_eq, lawRmBin]
  simp only [PMF.map_bind, PMF.pure_map, PMF.bind_map]
  rw [law_seq_smp124 (law_coinsF5 _) _ _ (unif_ring N K).symm _ _ (by smp_tac), PMF.map_bind]
  refine congrArg _ (funext fun sv => ?_)
  rw [law_seq_smp124 (law_repF X.law _) _ _ (hχE (Fin c.d)) _ _ (by smp_tac), PMF.map_bind]
  refine congrArg _ (funext fun e₀ => ?_)
  rw [law_seq_smp124 (law_repF X.law _) _ _ hχT _ _ (by smp_tac), PMF.map_bind]
  refine congrArg _ (funext fun σ => ?_)
  rw [law_seq_smp124 (law_repF X.law _) _ _ (hχE (RingBTVW.Fresh.Col k)) _ _ (by smp_tac), PMF.map_bind]
  refine congrArg _ (funext fun ea => ?_)
  rw [law_seq_smp124 (law_repF X.law _) _ _ (hχE (RingBTVW.Fresh.Col k)) _ _ (by smp_tac), PMF.map_bind]
  refine congrArg _ (funext fun ez => ?_)
  rw [law_seq_smp124 (law_repF law_entB _) _ _ hRm _ _ (by smp_tac), PMF.map_bind]
  refine congrArg _ (funext fun rr => ?_)
  simp only [Function.comp_apply, PMF.map_bind]
  rw [law_seq_smp124 (law_repF (law_entF c.w) (nE (N := N) hk)) _ _
    (by exact (eLaw_eq hk c).symm) _ _ (by smp_tac),
    PMF.map_bind]
  refine congrArg _ (funext fun ej => ?_)
  rw [law_seq_smp124 (law_repF X.law _) _ _ hχT _ _ (by smp_tac), PMF.map_bind]
  refine congrArg _ (funext fun e' => ?_)
  rw [PMF.pure_map, law_encTail hk c hN hK mpk x b ⟨sv, e₀, trapRowU' σ ea ez, rMat rr, ej, e'⟩ rr rfl]
  · rfl
  · intro i h1 h2
    repeat (rw [Function.update_of_ne (by intro h; subst h; simp [eSm_apply] at h1 h2)])
    rw [inputStore, Function.update_of_ne (fun h => h2 (by subst h; rfl))]
  all_goals simp only [Function.update_apply, eSm_apply, Matrix.cons_val_zero, inputStore]
  all_goals (simp (config := { decide := true }) only [ite_true, ite_false, List.nil_append]
             try rfl)
  all_goals rw [trapRow_enc, List.append_assoc]

end AdvancedEncryption.RingBTVW.Prog

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.PE.BranchingProgram

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-! ### Well-formedness and the machine -/

theorem wf_dropChunk (n : ℕ) : (dropChunk n).WF :=
  ⟨wf_natP (by decide) _, XProg.wf_dropP (by decide), trivial⟩

theorem wf_ufChunk (D : Fin 124) (hD : D.val < 120) (n : ℕ) : (ufChunk D n).WF :=
  ⟨wf_natP (by decide) _, XProg.wf_unframeP (by decide) (fun h => by subst h; simp at hD), trivial⟩

theorem wf_encParseP : (encParseP hk c).WF :=
  ⟨wf_dropChunk _, wf_ufChunk _ (by decide) _, wf_ufChunk _ (by decide) _, wf_ufChunk _ (by decide) _,
    wf_ufChunk _ (by decide) _, trivial, wf_ufChunk _ (by decide) _, trivial,
    wf_ufChunk _ (by decide) _⟩

theorem wf_encTail : (encTail hk c).WF :=
  ⟨wf_natL _ (tmplList_ne hk c), wf_encCoreP, XProg.wf_frameApP (by decide) (by decide)⟩

theorem wf_encP (X : ChiSampler c) : (encP hk c X).WF :=
  ⟨wf_encParseP hk c, wf_coinsF _, wf_repF X.wf X.pres6 _, wf_repF X.wf X.pres6 _,
    wf_repF X.wf X.pres6 _, wf_repF X.wf X.pres6 _,
    wf_repF (body := entB N K) ⟨wf_coinAp _ _, wf_zerosF _⟩
      ⟨preserves_coinAp (by decide) (by decide), preserves_zerosF _ (by decide)⟩ _,
    wf_repF (body := entF K c.w) ⟨wf_coinsF _, wf_zerosF _⟩
      ⟨preserves_coinsF _ (by decide), preserves_zerosF _ (by decide)⟩ _,
    wf_repF X.wf X.pres6 _, wf_encTail hk c⟩

/-- The length of the input word of `Enc`. -/
def nInE : ℕ :=
  (2 * pw.length + 1) + ((2 * ((Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length *
    (N * K)) + ((Enum.list (α := Fin 1)).length * ((Enum.list (α := TrapCol k)).length * (N * K)) +
    ((Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).length *
      ((Enum.list (α := Fin 1)).length * ((Enum.list (α := RingBTVW.Fresh.Col k)).length * (N * K))) +
      N * K))) + 1) + ((2 * nA + 1) + ((2 * 1 + 1) + 0)))

theorem length_encIn (mpk : PK hk c) (x : PUniv.Attr) (b : Bool) :
    (encodeTuple [pw, (pkEnc hk c).enc mpk, encAttr x, [b]]).length = nInE hk c := by
  show (Turing.MultiTapeTM.frame pw ++ (Turing.MultiTapeTM.frame ((pkEnc hk c).enc mpk) ++
    (Turing.MultiTapeTM.frame (encAttr x) ++ (Turing.MultiTapeTM.frame [b] ++ [])))).length = _
  simp only [List.length_append, length_frameE, PE.BranchingProgram.length_encAttr, List.length_nil,
    List.length_singleton]
  rw [(pkEnc hk c).length]
  rfl

/-- **The machine of `Enc`**: the compiled `encP`, input on tape `120`, output tape `122`. -/
noncomputable def encMP (X : ChiSampler c) : Machine := (encP hk c X).toMachineT 120 122 (nInE hk c)

/-- **The law of the machine of `Enc`.** -/
theorem run_encMP [NeZero c.d] (hN : 0 < N) (hK : 0 < K) (X : ChiSampler c) (mpk : PK hk c)
    (x : PUniv.Attr) (b : Bool) :
    (encMP hk c X).run (encodeTuple [pw, (pkEnc hk c).enc mpk, encAttr x, [b]]) =
      (encM hk c mpk x b).map fun ct => encodeTuple [(ctEnc hk c).enc ct] := by
  rw [encMP, XProg.run_toMachineT _ (wf_encP hk c X) 120 122 (nInE hk c) _
    (le_of_eq (length_encIn hk c mpk x b)), law_encP hk c hN hK X mpk x b]

end AdvancedEncryption.RingBTVW.Prog
