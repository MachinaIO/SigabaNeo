import PE.Impl.ExpLUT.Prog.RedKeySimES

/-!
# `KGsim` on the VM (module 6b, part 7): the paired evaluator inside a slab loop (generic VM)

`seEvalC` (`RedKeySimES`) reads or writes every register of the MVM except its own inputs, so a
loop over the slabs has no free register for its counter. `seEvalC2` is `seEvalC` with the step
counter built from `rTe ++ rBit1` (`14 + 1` bits) instead of `rT15`: it never touches register
`28` (`seLoopC`, the slab counter of `RedKeySimE`). **`exec_seEvalC2`** is `exec_seEvalC` with a
trailing `rest` in the step stream `rAinS`, and also gives the final `rAinS = rest` and
`rCs = C.drop (16 tl)` (the coefficient word is consumed by `16` tables).
-/

set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)

variable {N K : ℕ}

/-- The slab counter of the outer loop (unused by `seEvalC2`). -/
@[simp, vmreg] abbrev seLoopC : Fin 64 := 28

/-- **The paired `EvalPK`** (`T = 16`), the step counter from `rTe ++ rBit1`. -/
def seEvalC2 : Code :=
  .seq (.cp rCst rTe) <| .seq (.app rCst rBit1) <| .seq (.rep rCst (seStepK cfA)) (seStepK cfV)

theorem seEvalC2_writes_loop : seEvalC2.writes seLoopC = false := by decide

/-- **`seEvalC2` computes the paired `EvalPK`**, consuming `16` step records of `rAinS` and `16`
tables of `rCs`. -/
theorem exec_seEvalC2 (hN : 0 < N) (hK : 0 < K) (w : St) (g b n tl : ℕ) (hg : 0 < g)
    (hb : b ≤ K) (hn : n ≤ 2 ^ K - 1) (D : SeBits N K) (μ0 xc : Rq N K)
    (hin : SeStepIn w g b n tl D μ0) (hco : CoefIn w 14 n b xc)
    (Ain : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) (A0 : Fin 2 → Fin 2 × Fin K → Rq N K)
    (Cin : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (pz pu : ℕ → Rq N K)
    (z : ℕ → Fin 2 × Fin K → Rq N K) (rd : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K)
    (L0 : List (Fin 2 × Fin K → Rq N K)) (C : List Bool) (rest : List (Rq N K))
    (hL0 : L0.length = n) (hbL : 2 ^ b ≤ n) (hn0 : 0 < n)
    (hA : w rA = encL N K (matL A0)) (hSc : w seSc = encL N K (seRows L0))
    (hS : w rAinS = encL N K (seStepsL Ain Cin pz z rd pu (List.range 16) ++ rest))
    (hC : w rCs = C) :
    exec N K seEvalC2 w rA = encL N K (matL (evalVM (fun i => if i < 15 then
      cvA 14 n b xc (C.drop (tl * i)) else cvV n b (C.drop (tl * 15))) g D.Hf D.Aa b μ0 n Ain A0 16)) ∧
    exec N K seEvalC2 w seSc = encL N K (seRows (seEvalVM (fun i => if i < 15 then
      cvA 14 n b xc (C.drop (tl * i)) else cvV n b (C.drop (tl * 15))) g D b μ0 n Ain A0 Cin pz pu z rd
      L0 16)) ∧
    exec N K seEvalC2 w rAinS = encL N K rest ∧
    exec N K seEvalC2 w rCs = C.drop (tl * 16) := by
  set cvs : ℕ → Rq N K → Rq N K := fun i => if i < 15 then
      cvA 14 n b xc (C.drop (tl * i)) else cvV n b (C.drop (tl * 15)) with hcvs
  unfold seEvalC2
  simp only [exec_seq]
  generalize hW1 : exec N K (.app rCst rBit1) (exec N K (.cp rCst rTe) w) = W1
  have r1 : ∀ r : Fin 64, r ≠ rCst → W1 r = w r := fun r hr => by
    rw [← hW1, exec_app, Function.update_of_ne hr, exec_cp, Function.update_of_ne hr]
  have hc : (W1 rCst).length = 15 := by
    rw [← hW1, exec_app, Function.update_self, exec_cp, Function.update_self, hco.te,
      Function.update_of_ne (by decide), hco.bit1]
    simp
  have co : ∀ {w' : St}, (∀ r : Fin 64, seRoS r = true → r ≠ rCst → w' r = w r) →
      CoefIn w' 14 n b xc :=
    fun hw => ⟨by rw [hw _ (by decide) (by decide), hco.one],
      by rw [hw _ (by decide) (by decide), hco.xc], by rw [hw _ (by decide) (by decide), hco.bit1],
      by rw [hw _ (by decide) (by decide), hco.te], by rw [hw _ (by decide) (by decide), hco.tw],
      by rw [hw _ (by decide) (by decide), hco.tb], by rw [hw _ (by decide) (by decide), hco.z]⟩
  have key := exec_rep_inv2 (N := N) (K := K) rCst (seStepK cfA)
    (seStepK_roS cfA coefW_cfA rCst (by decide))
    (fun i w' => w' rA = encL N K (matL (evalVM cvs g D.Hf D.Aa b μ0 n Ain A0 i)) ∧
      w' seSc = encL N K (seRows (seEvalVM cvs g D b μ0 n Ain A0 Cin pz pu z rd L0 i)) ∧
      w' rAinS = encL N K (seStepsL Ain Cin pz z rd pu ((List.range 16).drop i) ++ rest) ∧
      w' rCs = C.drop (tl * i)) W1
    ⟨by rw [r1 _ (by decide), hA]; rfl, by rw [r1 _ (by decide), hSc]; rfl,
      by rw [r1 _ (by decide), hS]; rfl, by rw [r1 _ (by decide), hC]; simp⟩ ?_
  · rw [hc] at key
    obtain ⟨k1, k2, k3, k4⟩ := key
    generalize hW2 : exec N K (.rep rCst (seStepK cfA)) W1 = W2
    rw [hW2] at k1 k2 k3 k4
    have f2 : ∀ r : Fin 64, seRoS r = true → r ≠ rCst → W2 r = w r := fun r hr hrc => by
      have hw : (Code.rep rCst (seStepK cfA)).writes r = false := by
        simp only [Code.writes, seStepK_roS cfA coefW_cfA r hr, Bool.or_false, beq_eq_false_iff_ne]
        exact Ne.symm hrc
      rw [← hW2, exec_writes _ _ _ hw, r1 r hrc]
    have hin2 := hin.of_roS f2
    have hco2 := co f2
    rw [drop_range_succ (by norm_num : 15 < 16)] at k3
    simp only [seStepsL, List.flatMap_cons] at k3
    have hdrop : (List.range 16).drop 16 = [] := by simp
    rw [hdrop, List.flatMap_nil, List.append_nil] at k3
    have hcfV := hcf_cfV hK W2 14 n b hb xc hco2
    obtain ⟨s1, s2, s3, s4⟩ := exec_seStepK hN hK cfV coefW_cfV (cvV n b (W2 rCs)) W2 hcfV
      g b n tl hg hn D μ0 hin2 _ (Cin 15) (Ain 15) (rd 15) (pz 15) (pu 15) (z 15) _ rest
      (length_seEvalVM cvs g D b μ0 n Ain A0 Cin pz pu z rd L0 hL0 15) hbL hn0 k1 k2 k3
    rw [k4] at s1 s2
    refine ⟨?_, ?_, s3, ?_⟩
    · rw [s1]; rfl
    · rw [s2]; rfl
    · rw [s4, k4, List.drop_drop]
      congr 1
  · intro i w' hi hP _ hfr
    rw [hc] at hi
    obtain ⟨p1, p2, p3, p4⟩ := hP
    generalize hW0 : Function.update w' rCst (w' rCst).tail = W0
    have f0 : ∀ r : Fin 64, seRoS r = true → r ≠ rCst → W0 r = w r := fun r hr hr' => by
      rw [← hW0, Function.update_of_ne hr', hfr r (seStepK_roS cfA coefW_cfA r hr) hr', r1 r hr']
    have hin0 := hin.of_roS f0
    have hco0 := co f0
    have q1 : W0 rA = encL N K (matL (evalVM cvs g D.Hf D.Aa b μ0 n Ain A0 i)) := by
      rw [← hW0, Function.update_of_ne (by decide), p1]
    have q2 : W0 seSc = encL N K (seRows (seEvalVM cvs g D b μ0 n Ain A0 Cin pz pu z rd L0 i)) := by
      rw [← hW0, Function.update_of_ne (by decide), p2]
    have q3 : W0 rAinS = encL N K (seStepRec (Ain i) (Cin i) (pz i) (z i) (rd i) (pu i) ++
        (seStepsL Ain Cin pz z rd pu ((List.range 16).drop (i + 1)) ++ rest)) := by
      rw [← hW0, Function.update_of_ne (by decide), p3, drop_range_succ (by omega)]
      simp [seStepsL]
    have q4 : W0 rCs = C.drop (tl * i) := by rw [← hW0, Function.update_of_ne (by decide), p4]
    obtain ⟨s1, s2, s3, s4⟩ := exec_seStepK hN hK cfA coefW_cfA (cvA 14 n b xc (W0 rCs)) W0
      (hcf_cfA hN hK W0 14 n b hb xc hco0) g b n tl hg hn D μ0 hin0 _ (Cin i) (Ain i) (rd i) (pz i)
      (pu i) (z i) _ _ (length_seEvalVM cvs g D b μ0 n Ain A0 Cin pz pu z rd L0 hL0 i) hbL hn0 q1 q2 q3
    rw [q4] at s1 s2
    have hcv : cvA 14 n b xc (C.drop (tl * i)) = cvs i := by
      rw [hcvs]; simp only [if_pos (show i < 15 by omega)]
    refine ⟨?_, ?_, s3, ?_⟩
    · rw [s1, hcv]; rfl
    · rw [s2, hcv]; rfl
    · rw [s4, q4, List.drop_drop]
      congr 1

/-! ### Popping chunks of a stream -/

/-- Pop one chunk (`|tmpl|` bits) of the stream `src`, append it to `dst` (through `X`). -/
def sePopC (dst src tmpl X : Fin 64) : Code :=
  .seq (.cp X tmpl) (.seq (.mv X src tmpl) (.app dst X))

theorem exec_sePopC (dst src tmpl X : Fin 64) (h1 : X ≠ src) (h2 : X ≠ tmpl) (h3 : src ≠ tmpl)
    (h4 : dst ≠ X) (h5 : dst ≠ src) (w : St) (x rest : List (Rq N K)) (c : ℕ)
    (hx : x.length = c) (ht : (w tmpl).length = c * (N * K)) (hs : w src = encL N K (x ++ rest)) :
    exec N K (sePopC dst src tmpl X) w dst = w dst ++ encL N K x ∧
    exec N K (sePopC dst src tmpl X) w src = encL N K rest ∧
    (∀ r : Fin 64, r ≠ dst → r ≠ src → r ≠ X → exec N K (sePopC dst src tmpl X) w r = w r) := by
  unfold sePopC
  simp only [exec_seq, exec_cp, exec_mv, exec_app]
  rw [if_neg (by tauto)]
  have e1 : Function.update w X (w tmpl) tmpl = w tmpl := Function.update_of_ne (Ne.symm h2) _ _
  have e2 : Function.update w X (w tmpl) src = w src := Function.update_of_ne (Ne.symm h1) _ _
  have hsh : ValVM.shiftIn (w tmpl).length (w tmpl) (w src) = encL N K x := by
    unfold ValVM.shiftIn
    rw [List.drop_left, hs, ht, takeD_encL _ _ hx]
  simp only [e1, e2, Function.update_self, hsh]
  refine ⟨?_, ?_, ?_⟩
  · rw [Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h4]
  · rw [Function.update_of_ne (Ne.symm h5), Function.update_of_ne (Ne.symm h1), Function.update_self,
      ht, hs, ← hx, drop_encL _ _ rfl]
  · intro r r1 r2 r3
    rw [Function.update_of_ne r1, Function.update_of_ne r3, Function.update_of_ne r2,
      Function.update_of_ne r3]

/-- Pop `|cnt|` chunks. -/
def sePopsC (cnt dst src tmpl X : Fin 64) : Code := .rep cnt (sePopC dst src tmpl X)

theorem exec_sePopsC (cnt dst src tmpl X : Fin 64) (h1 : X ≠ src) (h2 : X ≠ tmpl) (h3 : src ≠ tmpl)
    (h4 : dst ≠ X) (h5 : dst ≠ src) (h6 : cnt ≠ dst) (h7 : cnt ≠ src) (h8 : cnt ≠ X)
    (h9 : cnt ≠ tmpl) (h10 : dst ≠ tmpl) (w : St)
    (chunks : List (List (Rq N K))) (rest : List (Rq N K)) (c : ℕ)
    (hch : ∀ x ∈ chunks, x.length = c) (hcnt : (w cnt).length = chunks.length)
    (ht : (w tmpl).length = c * (N * K)) (hs : w src = encL N K (chunks.flatten ++ rest)) :
    exec N K (sePopsC cnt dst src tmpl X) w dst = w dst ++ encL N K chunks.flatten ∧
    exec N K (sePopsC cnt dst src tmpl X) w src = encL N K rest := by
  have hb : (sePopC dst src tmpl X).writes cnt = false := by
    simp [sePopC, Code.writes, Ne.symm h6, Ne.symm h7, Ne.symm h8]
  have hbt : (sePopC dst src tmpl X).writes tmpl = false := by
    simp [sePopC, Code.writes, h2, h3, h10]
  have key := exec_rep_inv2 (N := N) (K := K) cnt (sePopC dst src tmpl X) hb
    (fun m w' => w' dst = w dst ++ encL N K (chunks.take m).flatten ∧
      w' src = encL N K ((chunks.drop m).flatten ++ rest)) w ⟨by simp, by simp [hs]⟩ ?_
  · rw [hcnt] at key
    unfold sePopsC
    simpa using key
  · intro m w' hm hP _ hfr
    rw [hcnt] at hm
    obtain ⟨p1, p2⟩ := hP
    have htm : Function.update w' cnt (w' cnt).tail tmpl = w tmpl := by
      rw [Function.update_of_ne (Ne.symm h9), hfr tmpl hbt (Ne.symm h9)]
    have hsrc : Function.update w' cnt (w' cnt).tail src =
        encL N K (chunks[m] ++ ((chunks.drop (m + 1)).flatten ++ rest)) := by
      rw [Function.update_of_ne (Ne.symm h7), p2, List.drop_eq_getElem_cons hm, List.flatten_cons,
        List.append_assoc]
    obtain ⟨e1, e2, -⟩ := exec_sePopC (N := N) (K := K) dst src tmpl X h1 h2 h3 h4 h5 _ _ _ c
      (hch _ (List.getElem_mem hm)) (by rw [htm, ht]) hsrc
    refine ⟨?_, ?_⟩
    · rw [e1, Function.update_of_ne (Ne.symm h6), p1, take_succ_getElem chunks hm,
        List.flatten_append, encL_append, List.append_assoc]
      simp
    · rw [e2]


/-! ### Loading a slab's packet -/

/-- **The packet of a slab** in the stream `rAinS`: the per-bit records, the start slab, `A₀`, the
`16` step records. -/
def sePacket (D : SeBits N K) (b : ℕ) (L0 : List (Fin 2 × Fin K → Rq N K))
    (A0 : Fin 2 → Fin 2 × Fin K → Rq N K) (Ain : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K)
    (Cin : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (pz pu : ℕ → Rq N K)
    (z : ℕ → Fin 2 × Fin K → Rq N K) (rd : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K) :
    List (Rq N K) :=
  seStream D (List.range b) ++ (seRows L0 ++ (matL A0 ++ seStepsL Ain Cin pz z rd pu (List.range 16)))

/-- Load a packet: `seSW`, `seSc`, `rA` from the head of `rAinS`. -/
def seLoadC : Code :=
  .seq (.clr seSW) <| .seq (.cp rJ rTb) <| .seq (sePopsC rJ seSW rAinS seTRec seMu) <|
  .seq (.clr seSc) <| .seq (.cp rJ rTW) <| .seq (sePopsC rJ seSc rAinS rT2KNK seMu) <|
  .seq (.clr rA) (sePopC rA rAinS rT4KNK seMu)

theorem seStream_flatten (D : SeBits N K) (l : List ℕ) :
    seStream D l = (l.map (seRec D)).flatten := by
  simp [seStream, List.flatMap]

theorem seRows_flatten (L : List (Fin 2 × Fin K → Rq N K)) : seRows L = (L.map vecL).flatten := by
  simp [seRows, List.flatMap]

theorem exec_seLoadC (w : St) (b n : ℕ) (D : SeBits N K) (L0 : List (Fin 2 × Fin K → Rq N K))
    (A0 : Fin 2 → Fin 2 × Fin K → Rq N K) (Ain : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K)
    (Cin : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (pz pu : ℕ → Rq N K)
    (z : ℕ → Fin 2 × Fin K → Rq N K) (rd : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K)
    (rest : List (Rq N K)) (hL0 : L0.length = n)
    (hS : w rAinS = encL N K (sePacket D b L0 A0 Ain Cin pz pu z rd ++ rest))
    (htb : (w rTb).length = b) (htr : (w seTRec).length = (32 * K ^ 3 + 12 * K) * (N * K))
    (htw : (w rTW).length = n) (hT : MulTmpl N K w) :
    exec N K seLoadC w seSW = encL N K (seStream D (List.range b)) ∧
    exec N K seLoadC w seSc = encL N K (seRows L0) ∧
    exec N K seLoadC w rA = encL N K (matL A0) ∧
    exec N K seLoadC w rAinS = encL N K (seStepsL Ain Cin pz z rd pu (List.range 16) ++ rest) := by
  unfold seLoadC
  simp only [exec_seq]
  -- the records
  generalize hW1 : exec N K (.cp rJ rTb) (exec N K (.clr seSW) w) = W1
  have f1 : ∀ r : Fin 64, r ≠ rJ → r ≠ seSW → W1 r = w r := fun r h1 h2 => by
    rw [← hW1, exec_cp, Function.update_of_ne h1, exec_clr, Function.update_of_ne h2]
  obtain ⟨a1, a2⟩ := exec_sePopsC (N := N) (K := K) rJ seSW rAinS seTRec seMu (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) W1 ((List.range b).map (seRec D))
    (seRows L0 ++ (matL A0 ++ seStepsL Ain Cin pz z rd pu (List.range 16)) ++ rest)
    (32 * K ^ 3 + 12 * K) (fun x hx => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
      exact length_seRec D t)
    (by rw [← hW1, exec_cp, Function.update_self]; simp [htb])
    (by rw [f1 _ (by decide) (by decide), htr])
    (by rw [f1 _ (by decide) (by decide), hS, sePacket, ← seStream_flatten]; simp)
  generalize hW2 : exec N K (sePopsC rJ seSW rAinS seTRec seMu) W1 = W2
  rw [hW2] at a1 a2
  have f2 : ∀ r : Fin 64, r ≠ rJ → r ≠ seSW → r ≠ rAinS → r ≠ seMu → W2 r = w r :=
    fun r h1 h2 h3 h4 => by
      rw [← hW2, exec_writes _ _ _ (by simp [sePopsC, sePopC, Code.writes, Ne.symm h1, Ne.symm h2,
        Ne.symm h3, Ne.symm h4]), f1 r h1 h2]
  have s1 : W1 seSW = [] := by rw [← hW1, exec_cp, Function.update_of_ne (by decide)]; simp
  rw [s1, List.nil_append, ← seStream_flatten] at a1
  -- the start slab
  generalize hW3 : exec N K (.cp rJ rTW) (exec N K (.clr seSc) W2) = W3
  have f3 : ∀ r : Fin 64, r ≠ rJ → r ≠ seSc → W3 r = W2 r := fun r h1 h2 => by
    rw [← hW3, exec_cp, Function.update_of_ne h1, exec_clr, Function.update_of_ne h2]
  obtain ⟨b1, b2⟩ := exec_sePopsC (N := N) (K := K) rJ seSc rAinS rT2KNK seMu (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) W3 (L0.map vecL) (matL A0 ++ seStepsL Ain Cin pz z rd pu (List.range 16) ++ rest)
    (2 * K) (fun x hx => by
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
      exact length_vecL v)
    (by rw [← hW3, exec_cp, Function.update_self, exec_clr, Function.update_of_ne (by decide),
      f2 _ (by decide) (by decide) (by decide) (by decide), htw]; simp [hL0])
    (by rw [f3 _ (by decide) (by decide), f2 _ (by decide) (by decide) (by decide) (by decide),
      hT.t2KNK]; simp)
    (by rw [f3 _ (by decide) (by decide), a2, ← seRows_flatten]; simp)
  generalize hW4 : exec N K (sePopsC rJ seSc rAinS rT2KNK seMu) W3 = W4
  rw [hW4] at b1 b2
  have f4 : ∀ r : Fin 64, r ≠ rJ → r ≠ seSc → r ≠ rAinS → r ≠ seMu → W4 r = W2 r :=
    fun r h1 h2 h3 h4 => by
      rw [← hW4, exec_writes _ _ _ (by simp [sePopsC, sePopC, Code.writes, Ne.symm h1, Ne.symm h2,
        Ne.symm h3, Ne.symm h4]), f3 r h1 h2]
  have s3 : W3 seSc = [] := by rw [← hW3, exec_cp, Function.update_of_ne (by decide)]; simp
  rw [s3, List.nil_append, ← seRows_flatten] at b1
  -- `A₀`
  obtain ⟨c1, c2, -⟩ := exec_sePopC (N := N) (K := K) rA rAinS rT4KNK seMu (by decide) (by decide)
    (by decide) (by decide) (by decide) (exec N K (.clr rA) W4) (matL A0)
    (seStepsL Ain Cin pz z rd pu (List.range 16) ++ rest) (4 * K) (length_matL A0)
    (by
      rw [exec_clr, Function.update_of_ne (by decide), f4 _ (by decide) (by decide) (by decide)
        (by decide), f2 _ (by decide) (by decide) (by decide) (by decide), hT.t4KNK]
      simp only [length_encL, List.length_replicate]
      ring)
    (by rw [exec_clr, Function.update_of_ne (by decide), b2, List.append_assoc])
  refine ⟨?_, ?_, ?_, c2⟩
  · rw [exec_writes _ _ _ (by decide), exec_clr, Function.update_of_ne (by decide),
      f4 _ (by decide) (by decide) (by decide) (by decide), a1]
  · rw [exec_writes _ _ _ (by decide), exec_clr, Function.update_of_ne (by decide), b1]
  · rw [c1, exec_clr, Function.update_self, List.nil_append]

/-! ### The loop over the slabs -/

/-- One slab: load its packet, evaluate, append the slab to the back of `rAinS`. -/
def seSlabC : Code := .seq seLoadC (.seq seEvalC2 (.app rAinS seSc))

/-- **The loop over the slabs** (`|seLoopC|` slabs). -/
def seLoopKC : Code := .rep seLoopC seSlabC

theorem seSlabC_writes_loop : seSlabC.writes seLoopC = false := by decide

/-- The registers holding the constants of the evaluation (never written by a slab). -/
def seConstR (r : Fin 64) : Bool :=
  decide (18 ≤ r.val ∧ r.val ≤ 27) || r == rKc || decide (57 ≤ r.val)

theorem seSlabC_const : ∀ r : Fin 64, seConstR r = true → seSlabC.writes r = false := by decide

/-- **The constants of the evaluation** (all registers `seConstR`). -/
structure SeConst (w : St) (g b n tl : ℕ) (μ0 xc : Rq N K) : Prop where
  tb : w rTb = List.replicate b false
  bit1 : w rBit1 = [false]
  trec : (w seTRec).length = (32 * K ^ 3 + 12 * K) * (N * K)
  tw : w rTW = List.replicate n false
  kc : (w rKc).length = g
  tm : MulTmpl N K w
  one : w rOne = encRM N K 1
  mu0 : w rMu0 = encRM N K μ0
  t4K : w rT4K = List.replicate (4 * K) false
  ttab : w rTtab = List.replicate tl false
  xc : w rXc = encRM N K xc
  te : w rTe = List.replicate 14 false

theorem SeConst.of_frame {w w' : St} {g b n tl : ℕ} {μ0 xc : Rq N K} (h : SeConst w g b n tl μ0 xc)
    (hw : ∀ r : Fin 64, seConstR r = true → w' r = w r) : SeConst w' g b n tl μ0 xc :=
  ⟨by rw [hw _ (by decide)]; exact h.tb, by rw [hw _ (by decide)]; exact h.bit1,
   by rw [hw _ (by decide)]; exact h.trec, by rw [hw _ (by decide)]; exact h.tw,
   by rw [hw _ (by decide)]; exact h.kc,
   h.tm.of_writes fun q hq => hw q (by simp [seConstR]; omega),
   by rw [hw _ (by decide)]; exact h.one, by rw [hw _ (by decide)]; exact h.mu0,
   by rw [hw _ (by decide)]; exact h.t4K, by rw [hw _ (by decide)]; exact h.ttab,
   by rw [hw _ (by decide)]; exact h.xc, by rw [hw _ (by decide)]; exact h.te⟩

theorem SeConst.stepIn {w : St} {g b n tl : ℕ} {μ0 xc : Rq N K} (h : SeConst w g b n tl μ0 xc)
    (D : SeBits N K) (hsw : w seSW = encL N K (seStream D (List.range b))) :
    SeStepIn w g b n tl D μ0 :=
  ⟨⟨hsw, h.tb, h.bit1, h.trec, by rw [h.tw, List.length_replicate], h.kc, h.tm⟩, h.one, h.mu0,
    h.t4K, h.ttab⟩

theorem SeConst.coefIn {w : St} {g b n tl : ℕ} {μ0 xc : Rq N K} (h : SeConst w g b n tl μ0 xc) :
    CoefIn w 14 n b xc :=
  ⟨h.one, h.xc, h.bit1, h.te, h.tw, h.tb, h.tm.z⟩

/-- The coefficient functions of the `16` steps from a coefficient word. -/
noncomputable def seCvs (n b tl : ℕ) (xc : Rq N K) (C : List Bool) (i : ℕ) : Rq N K → Rq N K :=
  if i < 15 then cvA 14 n b xc (C.drop (tl * i)) else cvV n b (C.drop (tl * 15))

/-- **One slab**: the packet is consumed, the slab `seEvalVM … 16` appended to `rAinS`, the
coefficient word advanced by `16` tables. -/
theorem exec_seSlabC (hN : 0 < N) (hK : 0 < K) (w : St) (g b n tl : ℕ) (hg : 0 < g)
    (hb : b ≤ K) (hn : n ≤ 2 ^ K - 1) (μ0 xc : Rq N K) (hc : SeConst w g b n tl μ0 xc)
    (D : SeBits N K) (L0 : List (Fin 2 × Fin K → Rq N K))
    (A0 : Fin 2 → Fin 2 × Fin K → Rq N K) (Ain : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K)
    (Cin : ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (pz pu : ℕ → Rq N K)
    (z : ℕ → Fin 2 × Fin K → Rq N K) (rd : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K)
    (C : List Bool) (rest : List (Rq N K)) (hL0 : L0.length = n) (hbL : 2 ^ b ≤ n) (hn0 : 0 < n)
    (hS : w rAinS = encL N K (sePacket D b L0 A0 Ain Cin pz pu z rd ++ rest)) (hC : w rCs = C) :
    exec N K seSlabC w rAinS = encL N K (rest ++ seRows (seEvalVM (seCvs n b tl xc C) g D b μ0 n
      Ain A0 Cin pz pu z rd L0 16)) ∧
    exec N K seSlabC w rCs = C.drop (tl * 16) := by
  unfold seSlabC
  simp only [exec_seq]
  obtain ⟨l1, l2, l3, l4⟩ := exec_seLoadC w b n D L0 A0 Ain Cin pz pu z rd rest hL0 hS
    (by rw [hc.tb, List.length_replicate]) hc.trec (by rw [hc.tw, List.length_replicate]) hc.tm
  generalize hW1 : exec N K seLoadC w = W1
  rw [hW1] at l1 l2 l3 l4
  have f1 : ∀ r : Fin 64, seConstR r = true → W1 r = w r := fun r hr => by
    rw [← hW1]; exact exec_writes _ _ _ (by revert r; decide)
  have hc1 := hc.of_frame f1
  have hC1 : W1 rCs = C := by rw [← hW1, exec_writes _ _ _ (by decide), hC]
  obtain ⟨e1, e2, e3, e4⟩ := exec_seEvalC2 hN hK W1 g b n tl hg hb hn D μ0 xc (hc1.stepIn D l1)
    hc1.coefIn Ain A0 Cin pz pu z rd L0 C rest hL0 hbL hn0 l3 l2 l4 hC1
  refine ⟨?_, ?_⟩
  · rw [exec_app, Function.update_self, e3, e2, encL_append]
    rfl
  · rw [exec_app, Function.update_of_ne (by decide), e4]

/-- **The loop over the slabs**: slab `k` with the packet `pk k` and the coefficient word
`Cf.drop (16 tl k)`; afterwards `rAinS` holds the output slabs, slab-major. -/
theorem exec_seLoopKC (hN : 0 < N) (hK : 0 < K) (w : St) (g b n tl : ℕ) (hg : 0 < g)
    (hb : b ≤ K) (hn : n ≤ 2 ^ K - 1) (μ0 xc : Rq N K) (hc : SeConst w g b n tl μ0 xc) (nS : ℕ)
    (D : ℕ → SeBits N K) (L0 : ℕ → List (Fin 2 × Fin K → Rq N K))
    (A0 : Fin 2 → Fin 2 × Fin K → Rq N K) (Ain : ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K)
    (Cin : ℕ → ℕ → Fin 2 → Fin 2 × Fin K → Rq N K) (pz pu : ℕ → ℕ → Rq N K)
    (z : ℕ → ℕ → Fin 2 × Fin K → Rq N K) (rd : ℕ → ℕ → DigI K → Fin 2 → Fin 2 × Fin K → Rq N K)
    (Cf : List Bool) (hL0 : ∀ k, (L0 k).length = n) (hbL : 2 ^ b ≤ n) (hn0 : 0 < n)
    (hS : w rAinS = encL N K ((List.range nS).flatMap fun k =>
      sePacket (D k) b (L0 k) A0 Ain (Cin k) (pz k) (pu k) (z k) (rd k)))
    (hC : w rCs = Cf) (hL : (w seLoopC).length = nS) :
    exec N K seLoopKC w rAinS = encL N K ((List.range nS).flatMap fun k =>
      seRows (seEvalVM (seCvs n b tl xc (Cf.drop (tl * 16 * k))) g (D k) b μ0 n Ain A0 (Cin k)
        (pz k) (pu k) (z k) (rd k) (L0 k) 16)) ∧
    exec N K seLoopKC w rCs = Cf.drop (tl * 16 * nS) ∧
    (∀ r : Fin 64, seConstR r = true → exec N K seLoopKC w r = w r) := by
  set out : ℕ → List (Rq N K) := fun k =>
    seRows (seEvalVM (seCvs n b tl xc (Cf.drop (tl * 16 * k))) g (D k) b μ0 n Ain A0 (Cin k)
      (pz k) (pu k) (z k) (rd k) (L0 k) 16) with hout
  set pk : ℕ → List (Rq N K) := fun k =>
    sePacket (D k) b (L0 k) A0 Ain (Cin k) (pz k) (pu k) (z k) (rd k) with hpk
  have key := exec_rep_inv2 (N := N) (K := K) seLoopC seSlabC seSlabC_writes_loop
    (fun k w' => w' rAinS = encL N K (((List.range nS).drop k).flatMap pk ++
      (List.range k).flatMap out) ∧ w' rCs = Cf.drop (tl * 16 * k)) w
    ⟨by rw [hS]; simp, by rw [hC]; simp⟩ ?_
  · rw [hL] at key
    refine ⟨?_, key.2, fun r hr => exec_writes _ _ _ ?_⟩
    · unfold seLoopKC; rw [key.1, List.drop_of_length_le (by simp)]; simp
    · simp only [seLoopKC, Code.writes, seSlabC_const r hr, Bool.or_false, beq_eq_false_iff_ne]
      intro e; subst e; simp [seConstR] at hr
  · intro k w' hk hP _ hfr
    rw [hL] at hk
    obtain ⟨p1, p2⟩ := hP
    have hc0 : SeConst (Function.update w' seLoopC (w' seLoopC).tail) g b n tl μ0 xc :=
      hc.of_frame fun r hr => by
        have hr' : r ≠ seLoopC := by intro e; subst e; simp [seConstR] at hr
        rw [Function.update_of_ne hr', hfr r (seSlabC_const r hr) hr']
    obtain ⟨s1, s2⟩ := exec_seSlabC hN hK _ g b n tl hg hb hn μ0 xc hc0 (D k) (L0 k) A0 Ain
      (Cin k) (pz k) (pu k) (z k) (rd k) (Cf.drop (tl * 16 * k))
      (((List.range nS).drop (k + 1)).flatMap pk ++ (List.range k).flatMap out) (hL0 k) hbL hn0
      (by rw [Function.update_of_ne (by decide), p1, drop_range_succ hk]; simp [hpk])
      (by rw [Function.update_of_ne (by decide), p2])
    refine ⟨?_, ?_⟩
    · rw [s1, List.range_succ, List.flatMap_append]
      simp [hout]
    · rw [s2, List.drop_drop]
      congr 1

end AdvancedEncryption.ExpLUT.Prog
