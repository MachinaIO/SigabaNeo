import PE.Impl.RingBTVW.Prog.SetupLaws

/-!
# The setup of the reduction of hybrid 5 as a tape program

`setup5P : XProg 7` (the component layout `XProg (R + 2)` with `R = 5`: inputs on tapes `0`, `1`,
blank scratch `2 … 6`; output on tape `0`, everything else blank at the end). On the instance word
`w` (tape `0`) and the date `encAttr x` (tape `1`) it appends to `w` the word of a secret
`σ ← setup5 x` (`sec5Enc`), from fair coins:

1. `encAttr x` (`appendTapeP`, tape `1` blanked);
2. `N · K` fair bits (`u₀`), the fair bits of the columns `w`;
3. the `Rᵢ`: `10 · 2k · d` binary ring elements (`entB`: a fair bit, then `N · K − 1` zeros);
4. the errors: `|JC| · N` flooding coefficients (`entF`: `min w K` fair bits, then `K − w`
   zeros).

Every count is built on the fly (`natP`, by doubling), so no template is needed.
**`law_setup5P`**: for the instance word `(inst5Enc d).enc i`, the output law is
`(setup5 x).map fun σ => (inst5Enc d).prod sec5Enc` of `(i, σ)` — the `law_setup` field of the
handlers' components for the packed secret `(i, σ)`.

Tapes: `2` coin, `3` `4` inner counter and its scratch, `5` `6` outer counter and its scratch.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.XProg Matrix
  AdvancedEncryption.RingBTVW.Fresh Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord

variable {N K k : ℕ}

/-! ### Blocks -/

/-- The inner scratch is blank. -/
def P3 (s : Store 7) : Prop := s 2 = [] ∧ s 3 = [] ∧ s 4 = []

/-- All scratch tapes are blank. -/
def P5 (s : Store 7) : Prop := P3 s ∧ s 5 = [] ∧ s 6 = []

theorem P3_upd {s : Store 7} {i : Fin 7} (hi : 5 ≤ i.val ∨ i = 0) (w : List Bool) (h : P3 s) :
    P3 (Function.update s i w) := by
  obtain ⟨h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> rw [Function.update_of_ne (by rintro rfl; omega)] <;> assumption

/-- `n` fair bits. -/
def coinsF (n : ℕ) : XProg 7 := withCount 3 4 n (forN 4 3 (coinAp 0 2))

theorem law_coinsF (n : ℕ) : AppendLaw (coinsF n) 0 P3 (BitString.uniformList n) := by
  have h := AppendLaw.withCount (k := 7) (r := 0) (t := 3) (c := 4) (P := fun s => s 2 = []) (n := n)
    (appendLaw_coins (k := 7) (r := 0) (b := 2) (c := 4) (t := 3) (by decide) (by decide) (by decide) n)
    (fun s w hs => by rwa [Function.update_of_ne (by decide)]) (by decide) (by decide)
  exact h.mono (fun s ⟨h2, h3, h4⟩ => ⟨h2, h3, h4⟩) rfl

/-- `n` zeros. -/
def zerosF (n : ℕ) : XProg 7 := withCount 3 4 n (forN 4 3 (bitAp 0 false))

theorem law_zerosF (n : ℕ) :
    AppendLaw (zerosF n) 0 P3 (PMF.pure (List.replicate n false)) := by
  have h := AppendLaw.withCount (k := 7) (r := 0) (t := 3) (c := 4) (P := fun s => s 2 = []) (n := n)
    (appendLaw_bits (k := 7) (r := 0) (c := 4) (t := 3) (by decide) false n (fun s => s 2 = [])
      (fun s w hs => by rwa [Function.update_of_ne (by decide)])
      (fun s w hs => by rwa [Function.update_of_ne (by decide)]))
    (fun s w hs => by rwa [Function.update_of_ne (by decide)]) (by decide) (by decide)
  exact h.mono (fun s ⟨h2, h3, h4⟩ => ⟨h2, h3, h4⟩) rfl

theorem P3_upd0 (s : Store 7) (w : List Bool) (h : P3 s) : P3 (Function.update s 0 w) :=
  P3_upd (Or.inr rfl) w h

/-- A binary ring element. -/
def entB (N K : ℕ) : XProg 7 := seq (coinAp 0 2) (zerosF (N * K - 1))

theorem law_entB : AppendLaw (entB N K) 0 P3 (μB N K) :=
  AppendLaw.seq ((appendLaw_coinAp (r := 0) (b := 2) (by decide)).mono (fun s h => h.1) rfl)
    (law_zerosF _) P3_upd0

/-- A flooding coefficient. -/
def entF (K w : ℕ) : XProg 7 := seq (coinsF (min w K)) (zerosF (K - w))

theorem law_entF (w : ℕ) : AppendLaw (entF K w) 0 P3 (μF K w) :=
  AppendLaw.seq (law_coinsF _) (law_zerosF _) P3_upd0

/-- `n` independent copies of a block (outer counter `5`, scratch `6`). -/
def repF (n : ℕ) (body : XProg 7) : XProg 7 := withCount 5 6 n (forN 6 5 body)

theorem law_repF {body : XProg 7} {μ : PMF (List Bool)} (hb : AppendLaw body 0 P3 μ) (n : ℕ) :
    AppendLaw (repF n body) 0 P5 (catPow μ n) := by
  have h1 := AppendLaw.forN (c := 6) (t := 5) (n := n) hb P3_upd0
    (fun s w hs => P3_upd (Or.inl (by decide)) w hs) (by decide)
  have h2 := AppendLaw.withCount (P := P3) h1 (fun s w hs => P3_upd (Or.inl (by decide)) w hs)
    (by decide) (by decide)
  exact h2.mono (fun s h => h) rfl

theorem law_coinsF5 (n : ℕ) : AppendLaw (coinsF n) 0 P5 (BitString.uniformList n) :=
  (law_coinsF n).mono (fun _ h => h.1) rfl

theorem P5_upd0 (s : Store 7) (w : List Bool) (h : P5 s) : P5 (Function.update s 0 w) :=
  ⟨P3_upd0 s w h.1, by rw [Function.update_of_ne (by decide)]; exact h.2.1,
    by rw [Function.update_of_ne (by decide)]; exact h.2.2⟩

/-! ### The program -/

variable (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The number of fair bits of the columns `w`. -/
def nW : ℕ := (Enum.list (α := JC (Sdw (N := N) hk))).length * ((Enum.list (α := Fin c.d)).length * 1)

/-- The number of entries of the `Rᵢ`. -/
def nR : ℕ := (Enum.list (α := (Sdw (N := N) hk).Attr × RingBTVW.Fresh.Col k)).length * (List.finRange c.d).length

/-- The number of flooding coefficients. -/
def nE : ℕ := (Enum.list (α := JC (Sdw (N := N) hk) × Fin N)).length

/-- The random part of the secret. -/
def tail5P : XProg 7 :=
  seq (coinsF (N * K)) (seq (coinsF (nW hk c)) (seq (repF (nR hk c) (entB N K))
    (repF (nE (N := N) hk) (entF K c.w))))

theorem law_tail5P :
    AppendLaw (tail5P hk c) 0 P5 (cat (BitString.uniformList (N * K))
      (cat (BitString.uniformList (nW hk c)) (cat (catPow (μB N K) (nR hk c))
        (catPow (μF K c.w) (nE (N := N) hk))))) :=
  AppendLaw.seq (law_coinsF5 _) (AppendLaw.seq (law_coinsF5 _)
    (AppendLaw.seq (law_repF law_entB _) (law_repF (law_entF _) _) P5_upd0) P5_upd0) P5_upd0

/-- **The setup of hybrid 5.** -/
def setup5P : XProg 7 := seq (appendTapeP 0 1 3 4) (tail5P hk c)

/-- **The law of the setup of hybrid 5**: on the instance word of `i` and the date `x`, the word
of the packed secret `(i, σ)`, `σ ← setup5 x`. -/
theorem law_setup5P [NeZero c.d] (hN : 0 < N) (hK : 0 < K)
    (i : Pub (Fin c.d) (Rg N K) k × Pub (Fin c.d) (Rg N K) k) (x : PUniv.Attr) :
    (setup5P hk c).law (ioS (R := 5) ((inst5Enc (N := N) (K := K) (k := k) c.d).enc i)
      (encAttr x) []) =
      (setup5 hk c x).map fun σ =>
        ioS (R := 5) (((inst5Enc (N := N) (K := K) (k := k) c.d).prod (sec5Enc hk c)).enc (i, σ))
          [] [] := by
  set w := (inst5Enc (N := N) (K := K) (k := k) c.d).enc i
  rw [setup5P, law_seq, law_appendTapeP (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) _ rfl rfl, PMF.pure_bind]
  have hP : P5 (Function.update (Function.update (ioS (R := 5) w (encAttr x) []) 0
      (ioS (R := 5) w (encAttr x) [] 0 ++ ioS (R := 5) w (encAttr x) [] 1)) 1 []) := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> rfl
  rw [law_tail5P hk c _ hP]
  have hR : (setup5 hk c x).map (fun σ => ioS (R := 5)
      (((inst5Enc (N := N) (K := K) (k := k) c.d).prod (sec5Enc hk c)).enc (i, σ)) [] []) =
      ((setup5 hk c x).map (sec5Enc hk c).enc).map (fun v => ioS (R := 5) (w ++ v) [] []) := by
    rw [PMF.map_comp]; rfl
  rw [hR, setup5_enc hk c hN hK, cat_pure_left, PMF.map_comp]
  congr 1
  funext u
  funext j
  fin_cases j <;> simp [ioS, List.append_assoc]

/-! ### Well-formedness -/

theorem wf_coinsF (n : ℕ) : (coinsF n).WF :=
  wf_withCount (by decide) (wf_forN (wf_coinAp _ _) (preserves_coinAp (by decide) (by decide)))

theorem wf_zerosF (n : ℕ) : (zerosF n).WF :=
  wf_withCount (by decide) (wf_forN (wf_bitAp _ _) (preserves_bitAp _ (by decide)))

theorem preserves_coinsF (n : ℕ) {i : Fin 7} (hi : 5 ≤ i.val) : (coinsF n).Preserves i :=
  preserves_withCount (by rintro rfl; simp at hi) (by rintro rfl; simp at hi)
    ⟨by simp [Preserves, Prog.Preserves, Prim.writes]; rintro rfl; simp at hi,
      by rintro rfl; simp at hi, preserves_coinAp (by rintro rfl; simp at hi)
        (by rintro rfl; simp at hi)⟩

theorem preserves_zerosF (n : ℕ) {i : Fin 7} (hi : 5 ≤ i.val) : (zerosF n).Preserves i :=
  preserves_withCount (by rintro rfl; simp at hi) (by rintro rfl; simp at hi)
    ⟨by simp [Preserves, Prog.Preserves, Prim.writes]; rintro rfl; simp at hi,
      by rintro rfl; simp at hi, preserves_bitAp _ (by rintro rfl; simp at hi)⟩

theorem wf_repF {body : XProg 7} (hb : body.WF) (hp : body.Preserves 6) (n : ℕ) :
    (repF n body).WF := wf_withCount (by decide) (wf_forN hb hp)

/-- **`setup5P` is well formed.** -/
theorem wf_setup5P : (setup5P hk c).WF :=
  ⟨wf_appendTapeP (by decide) (by decide), wf_coinsF _, wf_coinsF _,
    wf_repF (body := entB N K) ⟨wf_coinAp _ _, wf_zerosF _⟩
      ⟨preserves_coinAp (by decide) (by decide), preserves_zerosF _ (by decide)⟩ _,
    wf_repF (body := entF K c.w) ⟨wf_coinsF _, wf_zerosF _⟩ ⟨preserves_coinsF _ (by decide), preserves_zerosF _ (by decide)⟩ _⟩

end AdvancedEncryption.RingBTVW.Prog
