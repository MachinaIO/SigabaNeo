import PE.Impl.DualUse.Prog.C0
import PE.Impl.DualUse.Prog.UBLoop

/-!
# `Setup` as a tape program

`setupP X : XProg 96` realizes the law `setupM` of `Setup` exactly, from fair coins, with the χ
coefficient sampler `X.P` of an explicit sampler `X : ChiSampler c` (the error law `χc` of a
configuration is abstract, so the sampler is a parameter; `PE.Impl.DualUse.Prog.Chi` gives one
for the centered binomial laws).

1. **Sampling** (the 7-tape samplers of `PE.Impl.DualUse.Prog.Setup5`, framed so that each appends
   to its own tape, scratch on the tapes `2 … 6`): `B₀` (fair bits, tape `82`), `a` (fair bits,
   `83`), `t` (`N` χ coefficients, `84`), `e` (`2k · N` χ coefficients, `85`), the `B_j` (fair bits,
   `86`), `p` (fair bits, `87`) — in the order of `setupLaw`.
2. **The trapdoor row**: `a ++ t ++ e` on tape `0`, the block `c0P` (`PE.Impl.DualUse.Prog.C0`,
   framed on the tapes `0 … 81`) computes the word of `b = t a + e`; then `a ++ b` on tape `0` and
   the block `b1P` (`PE.Impl.DualUse.Prog.B1`) computes `B₁ = [1 | a | G̲ − b] = trapRow a e t`.
3. **The output**: tape `0` := `B₀ ++ B₁ ++ B_j ++ p`, the word of `mpk`; its frame is appended to
   the output tape `91` (`frameApP`); then tape `0` := `mpk ++ e ++ t`, the word of `msk`, and its
   frame. The output tape holds `encodeTuple [pkEnc mpk, mskEnc msk]`.

Appends go through the tapes `88` (copy), `89` (stream), `90` (counter); the input word sits on
tape `94` and is never read.

**`law_setupP`**: on the input store `inputStore 94 x` (any `x`), the output tape has the law
`(setupM hk c).map fun v => encodeTuple [pkEnc v.1, mskEnc v.2]`. `wf_setupP`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.XProg Matrix AdvancedEncryption.RingBTVW Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow

variable {N K k : ℕ}

/-- **An explicit χ coefficient sampler** for the configuration `c`: a 7-tape program appending
the word `zmodEnc K` of a χ sample to tape `0` (scratch `2, 3, 4`), leaving tape `6` alone, with a
shape bound on its time. -/
structure ChiSampler (c : Conf N K k) where
  /-- The program. -/
  P : XProg 7
  /-- Its law. -/
  law : AppendLaw P 0 P3 (μχ c)
  /-- It is well formed. -/
  wf : P.WF
  /-- It leaves tape `6` alone. -/
  pres6 : P.Preserves 6
  /-- Its shape bound. -/
  B : Bnd
  /-- The shape bound holds. -/
  atb : ATBb P B

/-! ### Framed samplers -/

/-- The sampler appending to tape `82`. -/
def eB0 : Fin 7 ↪ Fin 96 := ⟨![82, 93, 2, 3, 4, 5, 6], by decide⟩
/-- The sampler appending to tape `83`. -/
def eAa : Fin 7 ↪ Fin 96 := ⟨![83, 93, 2, 3, 4, 5, 6], by decide⟩
/-- The sampler appending to tape `84`. -/
def eTt : Fin 7 ↪ Fin 96 := ⟨![84, 93, 2, 3, 4, 5, 6], by decide⟩
/-- The sampler appending to tape `85`. -/
def eEe : Fin 7 ↪ Fin 96 := ⟨![85, 93, 2, 3, 4, 5, 6], by decide⟩
/-- The sampler appending to tape `86`. -/
def eBj : Fin 7 ↪ Fin 96 := ⟨![86, 93, 2, 3, 4, 5, 6], by decide⟩
/-- The sampler appending to tape `87`. -/
def ePp : Fin 7 ↪ Fin 96 := ⟨![87, 93, 2, 3, 4, 5, 6], by decide⟩

/-- **A framed sampler followed by a program**: the law binds the sampled value. -/
theorem law_seq_smp {e : Fin 7 ↪ Fin 96} (he : ∀ j : Fin 7, 2 ≤ j.val → (e j).val = j.val)
    {p : XProg 7} {μ : PMF (List Bool)} (hp : AppendLaw p 0 P5 μ) {α : Type} (ν : PMF α)
    (g : α → List Bool) (hμ : μ = ν.map g) (q : XProg 96) (s : Store 96)
    (hs : ∀ j : Fin 96, 2 ≤ j.val → j.val ≤ 6 → s j = []) :
    (seq (frame e p) q).law s = ν.bind fun v => q.law (Function.update s (e 0) (s (e 0) ++ g v)) := by
  have hP : P5 (fun j => s (e j)) := by
    have h : ∀ j : Fin 7, 2 ≤ j.val → s (e j) = [] := fun j hj =>
      hs _ (by rw [he j hj]; exact hj) (by rw [he j hj]; omega)
    exact ⟨⟨h 2 (by decide), h 3 (by decide), h 4 (by decide)⟩, h 5 (by decide), h 6 (by decide)⟩
  rw [law_seq, appendLaw_frame e hp s hP, hμ, PMF.map_comp, PMF.bind_map]
  rfl

/-! ### Appending a copy of a tape -/

/-- `r := r ++ a` (through the copy tape `88`, stream `89`, counter `90`). -/
def appC (r a : Fin 96) : XProg 96 := seq (prog (.prim (.copy 88 a))) (appendTapeP r 88 89 90)

theorem law_appC {r a : Fin 96} (hr88 : r ≠ 88) (hr89 : r ≠ 89) (hr90 : r ≠ 90) (s : Store 96)
    (h88 : s 88 = []) (h89 : s 89 = []) (h90 : s 90 = []) :
    (appC r a).law s = PMF.pure (Function.update s r (s r ++ s a)) := by
  rw [appC, law_seq, law_prim, PMF.pure_bind, law_appendTapeP hr88 hr89 hr90 (by decide) (by decide)
    (by decide) _ (by simp [Prim.apply, h89]) (by simp [Prim.apply, h90])]
  congr 1
  funext t
  simp only [Prim.apply, Function.update_apply]
  by_cases h1 : t = 88
  · subst h1; simp [hr88.symm, h88]
  · by_cases h2 : t = r
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem wf_appC (r a : Fin 96) (hr : r ≠ 90) : (appC r a).WF :=
  ⟨trivial, wf_appendTapeP hr (by decide)⟩

/-! ### Lifted components -/

theorem eighty_le : (80 : ℕ) ≤ 94 := by norm_num

/-- The tapes `0 … 81`. -/
abbrev e82 : Fin 82 ↪ Fin 96 := liftE eighty_le

/-- **A lifted component** on a store whose tapes `1 … 81` are blank. -/
theorem law_lift82 {p : XProg 82} {W W' : List Bool}
    (hp : p.law (ioS (R := 80) W [] []) = PMF.pure (ioS (R := 80) W' [] [])) (s : Store 96)
    (h0 : s 0 = W) (hs : ∀ j : Fin 96, 1 ≤ j.val → j.val < 82 → s j = []) :
    (frame e82 p).law s = PMF.pure (Function.update s 0 W') := by
  have hres : (fun j => s (e82 j)) = ioS (R := 80) W [] [] := by
    funext j
    simp only [ioS]
    split_ifs with h1 h2
    · rw [← h0]; congr 1; exact Fin.ext (by simp [h1])
    · exact hs _ (by simp [h2]) (by simp)
    · exact hs _ (by simp; omega) (by simp)
  rw [law_frame, hres, hp, PMF.pure_map]
  congr 1
  funext l
  rcases embedF_cases e82 s (ioS (R := 80) W' [] []) l with ⟨hl, h⟩ | ⟨i, rfl, h⟩
  · rw [h, Function.update_of_ne]
    rintro rfl
    rw [show (0 : Fin 96) = e82 0 from rfl, partialInv_self] at hl
    exact Option.some_ne_none _ hl
  · rw [h]
    simp only [ioS]
    split_ifs with h1 h2
    · rw [show e82 i = 0 from Fin.ext (by simp [h1]), Function.update_self]
    · rw [Function.update_of_ne (fun h => h1 (by rw [← liftE_val eighty_le i, h]; rfl))]
      exact (hs _ (by simp [h2]) (by simp)).symm
    · rw [Function.update_of_ne (fun h => h1 (by rw [← liftE_val eighty_le i, h]; rfl))]
      exact (hs _ (by simp; omega) (by simp)).symm

/-! ### The program -/

variable (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The number of bits of a row `1 × Col k`. -/
abbrev nRowC (N K k : ℕ) : ℕ :=
  (Enum.list (α := Fin 1)).length * ((Enum.list (α := RingBTVW.Col k)).length * (N * K))

/-- The number of bits of `B₀`. -/
abbrev nRowD (N K d : ℕ) : ℕ :=
  (Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin d)).length * (N * K))

/-- The number of bits of the `B_j`. -/
abbrev nBj : ℕ :=
  (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).length * nRowC N K k

/-- The deterministic part of `Setup`. -/
def setupDet : XProg 96 :=
  seq (prog (.prim (.copy 0 83))) <| seq (appC 0 84) <| seq (appC 0 85) <|
  seq (frame e82 (c0P 0 (2 * k * (N * K)) (2 * k) N K)) <|
  seq (prog (.prim (.copy 92 0))) <| seq (prog (.prim (.copy 0 83))) <| seq (appC 0 92) <|
  seq (frame e82 (b1P N K k)) <|
  seq (prog (.prim (.copy 92 0))) <| seq (prog (.prim (.copy 0 82))) <| seq (appC 0 92) <|
  seq (appC 0 86) <| seq (appC 0 87) <| seq (frameApP 91 0 89 90) <|
  seq (appC 0 85) <| seq (appC 0 84) <| frameApP 91 0 89 90

/-- **`Setup` as a tape program.** -/
def setupP (X : ChiSampler c) : XProg 96 :=
  seq (frame eB0 (coinsF (nRowD N K c.d))) <| seq (frame eAa (coinsF (nRowC N K k))) <|
  seq (frame eTt (repF N X.P)) <|
  seq (frame eEe (repF ((Enum.list (α := RingBTVW.Col k)).length * N) X.P)) <|
  seq (frame eBj (coinsF (nBj (N := N) hk))) <| seq (frame ePp (coinsF (N * K))) <| setupDet (N := N) (K := K) (k := k)


/-! ### The words -/

theorem law_seq_pure' {k : ℕ} {p q : XProg k} {s s' : Store k} (h : p.law s = PMF.pure s') :
    (seq p q).law s = q.law s' := by
  rw [law_seq, h, PMF.pure_bind]

theorem length_rowC (a : Matrix (Fin 1) (RingBTVW.Col k) (Rg N K)) :
    ((matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc a).length = 2 * k * (N * K) := by
  rw [matEnc_cols, colsW, length_matW, Nat.one_mul]

/-- **The word of `t a + e`** computed by `c0P`. -/
theorem c0_word (a e : Matrix (Fin 1) (RingBTVW.Col k) (Rg N K)) (t : Rg N K) :
    matAddW N K (1 * (2 * k)) (matMulW N K 1 1 (2 * k) ((ringEnc N K).enc t)
      ((matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc a))
      ((matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc e) =
      (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc (scalar t * a + e) := by
  have hsw : (ringEnc N K).enc t = matW N K 1 1 (scalar t) := by rw [matW_one_one]; rfl
  rw [matEnc_cols, matEnc_cols, matEnc_cols, colsW, colsW, colsW, hsw, matMulW_enc, matAddW_enc]
  congr 1

/-- Blank tapes below `82` stay blank under updates of the tapes `0` and `≥ 82`. -/
macro "blank_tac " h:ident : tactic => `(tactic| (
  intro j h1 h2
  simp only [Function.update_apply]
  split_ifs <;> (try subst_vars) <;> first | (simp at h1 h2; done) | (simp at *; omega) |
    exact $h _ (by omega)))

variable {hk c} in
/-- **The deterministic part of `Setup`**: from the words of `B₀, a, t, e, B_j, p` on the tapes
`82 … 87` (the tapes `0 … 81`, `88 … 92` blank), the output tape `91` ends with the tuple of the
words of `mpk = (B₀, trapRow a e t, B_j, p)` and `msk = (mpk, e, t)`. -/
theorem law_setupDet (hN : 0 < N) (hK : 0 < K) (B₀ : Matrix (Fin 1) (Fin c.d) (Rg N K))
    (a : Matrix (Fin 1) (RingBTVW.Col k) (Rg N K)) (t : Rg N K)
    (e : Matrix (Fin 1) (RingBTVW.Col k) (Rg N K))
    (Bj : (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index →
      Matrix (Fin 1) (RingBTVW.Col k) (Rg N K)) (p : Rg N K) (s : Store 96)
    (h82 : s 82 = (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc B₀)
    (h83 : s 83 = (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc a)
    (h84 : s 84 = (ringEnc N K).enc t)
    (h85 : s 85 = (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc e)
    (h86 : s 86 = (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
      (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k))).enc Bj)
    (h87 : s 87 = (ringEnc N K).enc p)
    (hlow : ∀ j : Fin 96, j.val < 82 → s j = []) (h88 : s 88 = []) (h89 : s 89 = [])
    (h90 : s 90 = []) (h91 : s 91 = []) :
    ∃ s', (setupDet (N := N) (K := K) (k := k)).law s = PMF.pure s' ∧
      s' 91 = encodeTuple [(pkEnc hk c).enc ⟨B₀, trapRow (Sdw (N := N) hk) a e t, Bj, p⟩,
        (mskEnc hk c).enc (⟨B₀, trapRow (Sdw (N := N) hk) a e t, Bj, p⟩, e, t)] := by
  set aw := (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc a
  set tw := (ringEnc N K).enc t
  set ew := (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc e
  set bw := (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc (scalar t * a + e)
  have hs0 : s 0 = [] := hlow 0 (by decide)
  unfold setupDet
  -- `a ++ t ++ e`
  rw [law_seq_pure' (law_prim _ _)]
  simp only [Prim.apply]
  rw [law_seq_pure' (law_appC (by decide) (by decide) (by decide) _ (by simp [h88])
    (by simp [h89]) (by simp [h90]))]
  rw [law_seq_pure' (law_appC (by decide) (by decide) (by decide) _ (by simp [h88])
    (by simp [h89]) (by simp [h90]))]
  -- `b = t a + e`
  have hc0 := law_c0P_words (oB := 0) (oS := 2 * k * (N * K)) (d := 2 * k) (N := N) (K := K)
    (aw ++ tw ++ ew) [] aw (tw ++ ew) aw tw ew [] (by simp) rfl (length_rowC a) (by simp)
    (length_rowC a) ((ringEnc N K).length t) (length_rowC e) (by
      rw [show tw = matW N K 1 1 (scalar t) by rw [matW_one_one]; rfl,
        show aw = colsW N K k 1 a from matEnc_cols a, colsW, matMulW_enc, length_matW]; ring)
  have hcw : matAddW N K (1 * (2 * k)) (matMulW N K 1 1 (2 * k) tw aw) ew = bw := c0_word a e t
  rw [hcw] at hc0
  rw [law_seq_pure' (law_lift82 hc0 _ (by simp [h83, h84, h85]) (by blank_tac hlow))]
  -- `a ++ b`, then `B₁`
  rw [law_seq_pure' (law_prim _ _), law_seq_pure' (law_prim _ _)]
  simp only [Prim.apply]
  rw [law_seq_pure' (law_appC (by decide) (by decide) (by decide) _ (by simp [h88])
    (by simp [h89]) (by simp [h90]))]
  have hb1 := law_b1P hk hN hK (a, scalar t * a + e)
  rw [← trapRow_eq_toB₁] at hb1
  rw [law_seq_pure' (law_lift82 hb1 _ (by simp [h83]; rfl) (by blank_tac hlow))]
  -- `mpk`
  rw [law_seq_pure' (law_prim _ _), law_seq_pure' (law_prim _ _)]
  simp only [Prim.apply]
  rw [law_seq_pure' (law_appC (by decide) (by decide) (by decide) _ (by simp [h88])
    (by simp [h89]) (by simp [h90]))]
  rw [law_seq_pure' (law_appC (by decide) (by decide) (by decide) _ (by simp [h88])
    (by simp [h89]) (by simp [h90]))]
  rw [law_seq_pure' (law_appC (by decide) (by decide) (by decide) _ (by simp [h88])
    (by simp [h89]) (by simp [h90]))]
  rw [law_seq_pure' (law_frameApP (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) _ (by simp [h89]) (by simp [h90]))]
  -- `msk`
  rw [law_seq_pure' (law_appC (by decide) (by decide) (by decide) _ (by simp [h88])
    (by simp [h89]) (by simp [h90]))]
  rw [law_seq_pure' (law_appC (by decide) (by decide) (by decide) _ (by simp [h88])
    (by simp [h89]) (by simp [h90]))]
  rw [law_frameApP (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) _ (by simp [h89]) (by simp [h90])]
  refine ⟨_, rfl, ?_⟩
  simp only [Function.update_self, Function.update_apply]
  simp [h82, h84, h85, h86, h87, h91, encodeTuple, pkEnc, mskEnc, FixedEnc.comap,
    FixedEnc.prod, List.append_assoc]
  rfl


variable {hk c} in
theorem law_setupDet' (hN : 0 < N) (hK : 0 < K) (B₀ : Matrix (Fin 1) (Fin c.d) (Rg N K))
    (a : Matrix (Fin 1) (RingBTVW.Col k) (Rg N K)) (t : Rg N K)
    (e : Matrix (Fin 1) (RingBTVW.Col k) (Rg N K))
    (Bj : (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index →
      Matrix (Fin 1) (RingBTVW.Col k) (Rg N K)) (p : Rg N K) {s : Store 96}
    (h82 : s 82 = (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc B₀)
    (h83 : s 83 = (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc a)
    (h84 : s 84 = (ringEnc N K).enc t)
    (h85 : s 85 = (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc e)
    (h86 : s 86 = (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
      (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k))).enc Bj)
    (h87 : s 87 = (ringEnc N K).enc p)
    (hlow : ∀ j : Fin 96, j.val < 82 → s j = []) (h88 : s 88 = []) (h89 : s 89 = [])
    (h90 : s 90 = []) (h91 : s 91 = []) :
    ((setupDet (N := N) (K := K) (k := k)).law s).map (fun s => s 91) =
      PMF.pure (encodeTuple [(pkEnc hk c).enc ⟨B₀, trapRow (Sdw (N := N) hk) a e t, Bj, p⟩,
        (mskEnc hk c).enc (⟨B₀, trapRow (Sdw (N := N) hk) a e t, Bj, p⟩, e, t)]) := by
  obtain ⟨s', hs', h⟩ := law_setupDet hN hK B₀ a t e Bj p s h82 h83 h84 h85 h86 h87 hlow h88 h89
    h90 h91
  rw [hs', PMF.pure_map, h]

/-! ### The law -/

/-- The tapes `2 … 6` of a store built from the input store by updates of the tapes `≥ 82`. -/
macro "mid_tac" : tactic => `(tactic| (
  intro j h1 h2
  simp only [Function.update_apply, inputStore, eB0, ePp, eBj, eEe, eTt, eAa,
    Function.Embedding.coeFn_mk, Matrix.cons_val_zero]
  split_ifs <;> (try subst_vars) <;> first | (simp at h1 h2; done) | (simp at *; omega) | rfl))

set_option maxHeartbeats 2000000 in
/-- **The law of `Setup`**: on any input word, the output tape `91` has the law of the encoded
`(mpk, msk) ← setupM`. -/
theorem law_setupP (hN : 0 < N) (hK : 0 < K) (X : ChiSampler c) (x : List Bool) :
    ((setupP hk c X).law (inputStore 94 x)).map (fun s => s 91) =
      (setupM hk c).map fun v => encodeTuple [(pkEnc hk c).enc v.1, (mskEnc hk c).enc v.2] := by
  have hχT : catPow (μχ c) N = (χR c).map (ringEnc N K).enc := (χR_enc c).symm
  have hχE : catPow (μχ c) ((Enum.list (α := RingBTVW.Col k)).length * N) =
      (rowLaw (χR c) (RingBTVW.Col k)).map (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc := by
    rw [rowLaw_enc, χR_enc, catPow_mul]
  unfold setupP setupM setupLaw
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.pure_map]
  rw [law_seq_smp (e := eB0) (fun j hj => by fin_cases j <;> simp_all [eB0]) (law_coinsF5 _) _ _
    (unif_row (Fin c.d)).symm _ _ (by mid_tac), PMF.map_bind]
  refine congrArg _ (funext fun B₀ => ?_)
  rw [law_seq_smp (e := eAa) (fun j hj => by fin_cases j <;> simp_all [eAa]) (law_coinsF5 _) _ _
    (unif_row (RingBTVW.Col k)).symm _ _ (by mid_tac), PMF.map_bind]
  refine congrArg _ (funext fun a => ?_)
  rw [law_seq_smp (e := eTt) (fun j hj => by fin_cases j <;> simp_all [eTt]) (law_repF X.law _) _ _
    hχT _ _ (by mid_tac), PMF.map_bind]
  refine congrArg _ (funext fun t => ?_)
  rw [law_seq_smp (e := eEe) (fun j hj => by fin_cases j <;> simp_all [eEe]) (law_repF X.law _) _ _
    hχE _ _ (by mid_tac), PMF.map_bind]
  refine congrArg _ (funext fun e => ?_)
  rw [law_seq_smp (e := eBj) (fun j hj => by fin_cases j <;> simp_all [eBj]) (law_coinsF5 _) _ _
    (unif_fun _ (unif_row (RingBTVW.Col k))).symm _ _ (by mid_tac), PMF.map_bind]
  refine congrArg _ (funext fun Bj => ?_)
  rw [law_seq_smp (e := ePp) (fun j hj => by fin_cases j <;> simp_all [ePp]) (law_coinsF5 _) _ _
    (unif_ring N K).symm _ _ (by mid_tac), PMF.map_bind]
  refine congrArg _ (funext fun p => ?_)
  rw [law_setupDet' hN hK B₀ a t e Bj p]
  · rfl
  all_goals first
    | (intro j hj
       simp only [eB0, ePp, eBj, eEe, eTt, eAa, Function.Embedding.coeFn_mk, Function.update_apply,
         inputStore, Matrix.cons_val_zero]
       split_ifs <;> (try subst_vars) <;> first | (simp at hj; done) | (simp at *; omega) | rfl)
    | simp [eB0, ePp, eBj, eEe, eTt, eAa, inputStore]

/-! ### Well-formedness -/

theorem wf_setupDet : (setupDet (N := N) (K := K) (k := k)).WF :=
  ⟨trivial, wf_appC _ _ (by decide), wf_appC _ _ (by decide), wf_c0P _ _ _ _ _, trivial, trivial,
    wf_appC _ _ (by decide), wf_b1P _ _ _, trivial, trivial, wf_appC _ _ (by decide),
    wf_appC _ _ (by decide), wf_appC _ _ (by decide), wf_frameApP (by decide) (by decide),
    wf_appC _ _ (by decide), wf_appC _ _ (by decide), wf_frameApP (by decide) (by decide)⟩

theorem wf_setupP (X : ChiSampler c) : (setupP hk c X).WF :=
  ⟨wf_coinsF _, wf_coinsF _, wf_repF X.wf X.pres6 _, wf_repF X.wf X.pres6 _, wf_coinsF _,
    wf_coinsF _, wf_setupDet⟩

end AdvancedEncryption.DualUse.Prog

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The length of the input word of `Setup`. -/
def nInS : ℕ := (encodeTuple [pw]).length

/-- **The machine of `Setup`**: the compiled `setupP`, input on tape `94`, output tape `91`. -/
noncomputable def setupMP (X : ChiSampler c) : Machine :=
  (setupP hk c X).toMachineT 94 91 nInS

/-- **The law of the machine of `Setup`.** -/
theorem run_setupMP (hN : 0 < N) (hK : 0 < K) (X : ChiSampler c) :
    (setupMP hk c X).run (encodeTuple [pw]) =
      (setupM hk c).map fun v => encodeTuple [(pkEnc hk c).enc v.1, (mskEnc hk c).enc v.2] := by
  rw [setupMP, XProg.run_toMachineT _ (wf_setupP hk c X) 94 91 nInS (encodeTuple [pw]) le_rfl, law_setupP hk c hN hK X]

end AdvancedEncryption.DualUse.Prog
