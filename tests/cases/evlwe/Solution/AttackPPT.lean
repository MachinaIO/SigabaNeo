import Solution.Attack

/-!
# The Post attack is uniform strict PPT

Certificates in cslib-frontier's polynomial-time calculus for every function of
`Solution/Attack.lean`, and `attack_isPPT`.
-/

namespace TestCase.EvLWE

open SigabaNeo.Lattices

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM TestCase

/-! ### Dimensions -/

@[fun_prop] theorem n_tidy : ComputableTidilyInPolyTime EvLWE.n encUnary encUnary := by
  unfold EvLWE.n; fun_prop
@[fun_prop] theorem w_tidy : ComputableTidilyInPolyTime EvLWE.w encUnary encUnary := by
  unfold EvLWE.w; fun_prop
@[fun_prop] theorem W_tidy : ComputableTidilyInPolyTime EvLWE.W encUnary encUnary := by
  unfold EvLWE.W EvLWE.w; fun_prop
@[fun_prop] theorem m_tidy : ComputableTidilyInPolyTime EvLWE.m encUnary encUnary := by
  unfold EvLWE.m EvLWE.n EvLWE.w; fun_prop
@[fun_prop] theorem k_tidy : ComputableTidilyInPolyTime EvLWE.k encUnary encUnary := by
  unfold EvLWE.k EvLWE.m EvLWE.n EvLWE.w; fun_prop
@[fun_prop] theorem W_plain : ComputableInPolyTime EvLWE.W encUnary encUnary := .of_tidy W_tidy
@[fun_prop] theorem m_plain : ComputableInPolyTime EvLWE.m encUnary encUnary := .of_tidy m_tidy
@[fun_prop] theorem k_plain : ComputableInPolyTime EvLWE.k encUnary encUnary := .of_tidy k_tidy

/-! ### Reading entries -/

@[fun_prop] theorem entryAt_poly {α : Type} {input : α ↪ List Bool} {l : α → ℕ}
    {word : α → List Bool} {idx : α → ℕ} (hl : ComputableInPolyTime l input encUnary)
    (hw : ComputableInPolyTime word input encBits) (hi : ComputableInPolyTime idx input encUnary) :
    ComputableInPolyTime (fun a => entryAt (l a) (word a) (idx a)) input encNat := by
  unfold entryAt; fun_prop

@[fun_prop] theorem qOf_poly {α : Type} {input : α ↪ List Bool} {l : α → ℕ}
    {word : α → List Bool} (hl : ComputableInPolyTime l input encUnary)
    (hw : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime (fun a => qOf (l a) (word a)) input encNat := by
  unfold qOf; fun_prop

@[fun_prop] theorem cAt_poly {α : Type} {input : α ↪ List Bool} {l : α → ℕ}
    {word : α → List Bool} {r : α → ℕ} (hl : ComputableInPolyTime l input encUnary)
    (hw : ComputableInPolyTime word input encBits) (hr : ComputableInPolyTime r input encUnary) :
    ComputableInPolyTime (fun a => cAt (l a) (word a) (r a)) input encNat := by
  unfold cAt; fun_prop

@[fun_prop] theorem kAt_poly {α : Type} {input : α ↪ List Bool} {l : α → ℕ}
    {word : α → List Bool} {r j : α → ℕ} (hl : ComputableInPolyTime l input encUnary)
    (hw : ComputableInPolyTime word input encBits) (hr : ComputableInPolyTime r input encUnary)
    (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun a => kAt (l a) (word a) (r a) (j a)) input encNat := by
  unfold kAt; fun_prop

@[fun_prop] theorem auxAt_poly {α : Type} {input : α ↪ List Bool} {l : α → ℕ}
    {word : α → List Bool} {j : α → ℕ} (hl : ComputableInPolyTime l input encUnary)
    (hw : ComputableInPolyTime word input encBits) (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun a => auxAt (l a) (word a) (j a)) input encNat := by
  unfold auxAt; fun_prop

/-! ### Loops over a range -/

/-- A sum over `range count` whose body also reads the input. -/
theorem sumRange {γ : Type} {encIn : γ ↪ List Bool} {count : γ → ℕ} {f : γ → ℕ → ℕ}
    (hc : ComputableTidilyInPolyTime count encIn encUnary)
    (hf : ComputableInPolyTime (fun p : γ × ℕ => f p.1 p.2) (encPair encIn encUnary) encNat) :
    ComputableInPolyTime (fun x => ((List.range (count x)).map (f x)).sum) encIn encNat :=
  ComputableInPolyTime.binary_sum.comp
    (ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.mapWithInput (ComputableTidilyInPolyTime.range.comp hc) hf.tidy))

/-! ### Parities and columns -/

theorem kBit_poly {α : Type} {input : α ↪ List Bool} {l : α → ℕ}
    {word : α → List Bool} {r j : α → ℕ} (hl : ComputableInPolyTime l input encUnary)
    (hw : ComputableInPolyTime word input encBits) (hr : ComputableInPolyTime r input encUnary)
    (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun a => kBit (l a) (word a) (r a) (j a)) input encNat := by
  have hx := (kAt_poly hl hw hr hj).tidy
  have hq := (qOf_poly hl hw).tidy
  have h2 : ComputableTidilyInPolyTime (fun _ : α => 2) input encNat := .const 2
  have h1 : ComputableTidilyInPolyTime (fun _ : α => 1) input encNat := .const 1
  have hlt := ComputableTidilyInPolyTime.binary_lt'
    (ComputableTidilyInPolyTime.binary_mul' h2 hx) hq
  have hm1 := ComputableTidilyInPolyTime.binary_mod' hx h2
  have hm2 := ComputableTidilyInPolyTime.binary_mod'
    (ComputableTidilyInPolyTime.binary_add' hx h1) h2
  unfold kBit
  exact .of_tidy (by fun_prop)

theorem colVec_poly {α : Type} {input : α ↪ List Bool} {l : α → ℕ}
    {word : α → List Bool} {j : α → ℕ} (hl : ComputableTidilyInPolyTime l input encUnary)
    (hw : ComputableInPolyTime word input encBits) (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun a => colVec (l a) (word a) (j a)) input encNat := by
  unfold colVec
  refine sumRange (count := fun a => EvLWE.m (l a)) (by fun_prop) ?_
  have hl' := ComputableInPolyTime.of_tidy hl
  have hb := (kBit_poly (input := encPair input encUnary) (l := fun p => l p.1)
    (word := fun p => word p.1) (r := fun p => p.2) (j := fun p => j p.1)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)).tidy
  have hp : ComputableTidilyInPolyTime (fun p : α × ℕ => 2 ^ p.2) (encPair input encUnary) encNat :=
    ComputableTidilyInPolyTime.binary_two_pow.comp (by fun_prop)
  exact .of_tidy (ComputableTidilyInPolyTime.binary_mul' hb hp)

theorem wAt_poly {α : Type} {input : α ↪ List Bool} {l : α → ℕ}
    {word : α → List Bool} {j : α → ℕ} (hl : ComputableTidilyInPolyTime l input encUnary)
    (hw : ComputableInPolyTime word input encBits) (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun a => wAt (l a) (word a) (j a)) input encNat := by
  have hl' := ComputableInPolyTime.of_tidy hl
  have hsum : ComputableInPolyTime (fun a => ((List.range (EvLWE.m (l a))).map
      fun r => cAt (l a) (word a) r * kAt (l a) (word a) r (j a)).sum) input encNat := by
    refine sumRange (count := fun a => EvLWE.m (l a)) (by fun_prop) ?_
    have hc := (cAt_poly (input := encPair input encUnary) (l := fun p => l p.1)
      (word := fun p => word p.1) (r := fun p => p.2) (by fun_prop) (by fun_prop)
      (by fun_prop)).tidy
    have hk := (kAt_poly (input := encPair input encUnary) (l := fun p => l p.1)
      (word := fun p => word p.1) (r := fun p => p.2) (j := fun p => j p.1) (by fun_prop)
      (by fun_prop) (by fun_prop) (by fun_prop)).tidy
    exact .of_tidy (ComputableTidilyInPolyTime.binary_mul' hc hk)
  have hq := (qOf_poly hl' hw).tidy
  have ha := (auxAt_poly hl' hw hj).tidy
  unfold wAt
  exact .of_tidy (ComputableTidilyInPolyTime.binary_mod'
    (ComputableTidilyInPolyTime.binary_add' hsum.tidy
      (ComputableTidilyInPolyTime.binary_sub' hq ha)) hq)

/-! ### Elimination -/

/-- Basis triples `(pivot, vector, mask)`: the pivot in unary, the numbers in binary. -/
abbrev encT : ℕ × ℕ × ℕ ↪ List Bool := encPair encUnary (encPair encNat encNat)
abbrev encVM : ℕ × ℕ ↪ List Bool := encPair encNat encNat

theorem size_mod_two_pow_le (a M : ℕ) : (encNat (a % 2 ^ M)).length ≤ M := by
  rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_le]
  exact Nat.mod_lt _ (by positivity)

theorem reduceStep_tidy : ComputableTidilyInPolyTime
    (fun p : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ × ℕ) => reduceStep p.1.1 p.1.2 p.2)
    (encFoldStep encUnary encVM encT) encVM := by
  have hv : ComputableInPolyTime (fun p : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ × ℕ) => p.1.2.1)
      (encFoldStep encUnary encVM encT) encNat := by fun_prop
  have hm : ComputableInPolyTime (fun p : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ × ℕ) => p.1.2.2)
      (encFoldStep encUnary encVM encT) encNat := by fun_prop
  have hb1 : ComputableInPolyTime (fun p : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ × ℕ) => p.2.2.1)
      (encFoldStep encUnary encVM encT) encNat := by fun_prop
  have hb2 : ComputableInPolyTime (fun p : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ × ℕ) => p.2.2.2)
      (encFoldStep encUnary encVM encT) encNat := by fun_prop
  have hP : ComputableTidilyInPolyTime (fun p : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ × ℕ) => 2 ^ p.1.1)
      (encFoldStep encUnary encVM encT) encNat :=
    ComputableTidilyInPolyTime.binary_two_pow.comp (by fun_prop)
  have hx1 := ComputableTidilyInPolyTime.binary_mod' (ComputableInPolyTime.binary_xor' hv hb1).tidy hP
  have hx2 := ComputableTidilyInPolyTime.binary_mod' (ComputableInPolyTime.binary_xor' hm hb2).tidy hP
  have ht := ComputableTidilyInPolyTime.binary_testBit hv.tidy
    (i := fun p : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ × ℕ) => p.2.1) (by fun_prop)
  have hacc : ComputableTidilyInPolyTime (fun p : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ × ℕ) => p.1.2)
      (encFoldStep encUnary encVM encT) encVM := by fun_prop
  exact ComputableTidilyInPolyTime.ite' (encC := encBool) ht (hx1.pair hx2) hacc

/-- `reduce`, on `((M, basis), (v, mask))`. -/
theorem reduce_tidy : ComputableTidilyInPolyTime
    (fun x : (ℕ × List (ℕ × ℕ × ℕ)) × (ℕ × ℕ) => reduce x.1.1 x.1.2 x.2.1 x.2.2)
    (encPair (encPair encUnary (encList encT)) encVM) encVM := by
  unfold reduce
  have hP : ComputableTidilyInPolyTime (fun x : (ℕ × List (ℕ × ℕ × ℕ)) × (ℕ × ℕ) => 2 ^ x.1.1)
      (encPair (encPair encUnary (encList encT)) encVM) encNat :=
    ComputableTidilyInPolyTime.binary_two_pow.comp (by fun_prop)
  have hi1 := ComputableTidilyInPolyTime.binary_mod'
    (left := fun x : (ℕ × List (ℕ × ℕ × ℕ)) × (ℕ × ℕ) => x.2.1) (by fun_prop) hP
  have hi2 := ComputableTidilyInPolyTime.binary_mod'
    (left := fun x : (ℕ × List (ℕ × ℕ × ℕ)) × (ℕ × ℕ) => x.2.2) (by fun_prop) hP
  have hpar : ComputableTidilyInPolyTime (fun x : (ℕ × List (ℕ × ℕ × ℕ)) × (ℕ × ℕ) => x.1.1)
      (encPair (encPair encUnary (encList encT)) encVM) encUnary := by fun_prop
  have hlist : ComputableTidilyInPolyTime (fun x : (ℕ × List (ℕ × ℕ × ℕ)) × (ℕ × ℕ) => x.1.2)
      (encPair (encPair encUnary (encList encT)) encVM) (encList encT) := by fun_prop
  have hgrowth : PolyBounded
      (fun x => (encPair (encPair encUnary (encList encT)) encVM x).length)
      (fun x : (ℕ × List (ℕ × ℕ × ℕ)) × (ℕ × ℕ) => 3 * x.1.1 + 1) := by
    refine PolyBounded.of_forall_le 3 1 fun x => ?_
    simp only [length_encPair, encUnary_apply, List.length_replicate, pow_one]
    omega
  exact ComputableTidilyInPolyTime.foldlWith_of_bounded_growth (encA := encT)
    (encL := encList encT) (step := reduceStep) hpar hlist (hi1.pair hi2) reduceStep_tidy
    hgrowth (by
    intro x st b _
    unfold reduceStep
    split_ifs
    · simp only [length_encPair]
      have h1 := size_mod_two_pow_le (st.1 ^^^ b.2.1) x.1.1
      have h2 := size_mod_two_pow_le (st.2 ^^^ b.2.2) x.1.1
      omega
    · omega)

theorem reduce_lt (M : ℕ) (basis : List (ℕ × ℕ × ℕ)) (v mk : ℕ) :
    (reduce M basis v mk).1 < 2 ^ M ∧ (reduce M basis v mk).2 < 2 ^ M := by
  unfold reduce
  have key : ∀ (l : List (ℕ × ℕ × ℕ)) (acc : ℕ × ℕ), acc.1 < 2 ^ M → acc.2 < 2 ^ M →
      (l.foldl (reduceStep M) acc).1 < 2 ^ M ∧ (l.foldl (reduceStep M) acc).2 < 2 ^ M := by
    intro l
    induction l with
    | nil => intro acc h1 h2; exact ⟨h1, h2⟩
    | cons b l ih =>
      intro acc h1 h2
      simp only [List.foldl_cons]
      apply ih
      · unfold reduceStep; split_ifs
        · exact Nat.mod_lt _ (by positivity)
        · exact h1
      · unfold reduceStep; split_ifs
        · exact Nat.mod_lt _ (by positivity)
        · exact h2
  exact key _ _ (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))

theorem length_encNat_lt {a M : ℕ} (h : a < 2 ^ M) : (encNat a).length ≤ M := by
  rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_le]; exact h

theorem log_le_of_lt {a M : ℕ} (h : a < 2 ^ M) : Nat.log 2 a ≤ M := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · exact (Nat.log_lt_of_lt_pow (by omega) h).le

abbrev encSt : List (ℕ × ℕ × ℕ) × ℕ ↪ List Bool := encPair (encList encT) encNat
abbrev encKW : ℕ × List Bool ↪ List Bool := encPair encUnary encBits

theorem elimStep_tidy : ComputableTidilyInPolyTime
    (fun p : ((ℕ × List Bool) × (List (ℕ × ℕ × ℕ) × ℕ)) × ℕ => elimStep p.1.1.1 p.1.1.2 p.1.2 p.2)
    (encFoldStep encKW encSt encUnary) encSt := by
  have hκ : ComputableInPolyTime (fun p : ((ℕ × List Bool) × (List (ℕ × ℕ × ℕ) × ℕ)) × ℕ => p.1.1.1)
      (encFoldStep encKW encSt encUnary) encUnary := by fun_prop
  have hcol := colVec_poly (input := encFoldStep encKW encSt encUnary) (l := fun p => p.1.1.1)
    (word := fun p => p.1.1.2) (j := fun p => p.2) (by fun_prop) (by fun_prop) (by fun_prop)
  have hM : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × (List (ℕ × ℕ × ℕ) × ℕ)) × ℕ => EvLWE.m p.1.1.1 + 1)
      (encFoldStep encKW encSt encUnary) encUnary := by fun_prop
  have hP : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × (List (ℕ × ℕ × ℕ) × ℕ)) × ℕ => 2 ^ p.2)
      (encFoldStep encKW encSt encUnary) encNat :=
    ComputableTidilyInPolyTime.binary_two_pow.comp (by fun_prop)
  have hr : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × (List (ℕ × ℕ × ℕ) × ℕ)) × ℕ =>
        reduce (EvLWE.m p.1.1.1 + 1) p.1.2.1 (colVec p.1.1.1 p.1.1.2 p.2) (2 ^ p.2))
      (encFoldStep encKW encSt encUnary) encVM := by
    have hb0 : ComputableTidilyInPolyTime
        (fun p : ((ℕ × List Bool) × (List (ℕ × ℕ × ℕ) × ℕ)) × ℕ => p.1.2.1)
        (encFoldStep encKW encSt encUnary) (encList encT) := by fun_prop
    have hg : ComputableTidilyInPolyTime
        (fun p : ((ℕ × List Bool) × (List (ℕ × ℕ × ℕ) × ℕ)) × ℕ =>
          ((EvLWE.m p.1.1.1 + 1, p.1.2.1), (colVec p.1.1.1 p.1.1.2 p.2, 2 ^ p.2)))
        (encFoldStep encKW encSt encUnary) (encPair (encPair encUnary (encList encT)) encVM) :=
      (hM.prod hb0).prod (hcol.tidy.prod hP)
    have hr0 := ComputableTidilyInPolyTime.comp reduce_tidy hg
    simpa only [Function.comp_def] using hr0
  have hr1 : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × (List (ℕ × ℕ × ℕ) × ℕ)) × ℕ =>
        (reduce (EvLWE.m p.1.1.1 + 1) p.1.2.1 (colVec p.1.1.1 p.1.1.2 p.2) (2 ^ p.2)).1)
      (encFoldStep encKW encSt encUnary) encNat := (ComputableTidilyInPolyTime.fst _ _).comp hr
  have hr2 : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × (List (ℕ × ℕ × ℕ) × ℕ)) × ℕ =>
        (reduce (EvLWE.m p.1.1.1 + 1) p.1.2.1 (colVec p.1.1.1 p.1.1.2 p.2) (2 ^ p.2)).2)
      (encFoldStep encKW encSt encUnary) encNat := (ComputableTidilyInPolyTime.snd _ _).comp hr
  have hlog := ComputableTidilyInPolyTime.binary_log_two.comp hr1
  have hst2 : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × (List (ℕ × ℕ × ℕ) × ℕ)) × ℕ => p.1.2.2)
      (encFoldStep encKW encSt encUnary) encNat := by fun_prop
  have hz0 : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × (List (ℕ × ℕ × ℕ) × ℕ)) × ℕ => p.1.2.2 == 0)
      (encFoldStep encKW encSt encUnary) encBool := by
    convert ComputableTidilyInPolyTime.decide_eq' hst2 (.const 0) using 2 with p
  have hz1 : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × (List (ℕ × ℕ × ℕ) × ℕ)) × ℕ =>
        (reduce (EvLWE.m p.1.1.1 + 1) p.1.2.1 (colVec p.1.1.1 p.1.1.2 p.2) (2 ^ p.2)).1 == 0)
      (encFoldStep encKW encSt encUnary) encBool := by
    convert ComputableTidilyInPolyTime.decide_eq' hr1 (.const 0) using 2 with p
  have hb : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × (List (ℕ × ℕ × ℕ) × ℕ)) × ℕ => p.1.2.1)
      (encFoldStep encKW encSt encUnary) (encList encT) := by fun_prop
  have htriple : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × (List (ℕ × ℕ × ℕ) × ℕ)) × ℕ =>
        [(Nat.log 2 (reduce (EvLWE.m p.1.1.1 + 1) p.1.2.1 (colVec p.1.1.1 p.1.1.2 p.2) (2 ^ p.2)).1,
          reduce (EvLWE.m p.1.1.1 + 1) p.1.2.1 (colVec p.1.1.1 p.1.1.2 p.2) (2 ^ p.2))])
      (encFoldStep encKW encSt encUnary) (encList encT) :=
    ComputableTidilyInPolyTime.cons' (hlog.prod hr) (.const [])
  have happ := ComputableTidilyInPolyTime.listAppend' hb htriple
  have hfound := hb.prod hr2
  have hins := happ.prod (ComputableTidilyInPolyTime.const (encMid := encNat) 0)
  have hacc : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × (List (ℕ × ℕ × ℕ) × ℕ)) × ℕ => p.1.2)
      (encFoldStep encKW encSt encUnary) encSt := by fun_prop
  unfold elimStep
  exact ComputableTidilyInPolyTime.ite' (encC := encBool) hz0
    (ComputableTidilyInPolyTime.ite' (encC := encBool) hz1 hfound hins) hacc

theorem length_encList_append_single {α : Type} (enc : α ↪ List Bool) (l : List α) (t : α) :
    (encList enc (l ++ [t])).length = (encList enc l).length + (2 * (enc t).length + 1) := by
  simp [length_encList]

theorem m_le (κ : ℕ) : EvLWE.m κ + 2 ≤ 64 * (κ + 1) ^ 2 := by
  simp only [EvLWE.m, EvLWE.n, EvLWE.w]; nlinarith

theorem elimStep_growth (κ : ℕ) (word : List Bool) (st : List (ℕ × ℕ × ℕ) × ℕ) (j : ℕ) :
    (encSt (elimStep κ word st j)).length ≤ (encSt st).length + 30 * (EvLWE.m κ + 2) := by
  obtain ⟨hr1, hr2⟩ := reduce_lt (EvLWE.m κ + 1) st.1 (colVec κ word j) (2 ^ j)
  have h1 := length_encNat_lt hr1
  have h2 := length_encNat_lt hr2
  have hl := log_le_of_lt hr1
  unfold elimStep
  by_cases hs : st.2 = 0
  · have hs' : (st.2 == 0) = true := by simp [hs]
    simp only [hs', ite_true]
    split_ifs
    · simp only [length_encPair, hs, encNat_apply, Nat.zero_bits, List.length_nil] at h1 h2 ⊢
      omega
    · simp only [length_encPair, length_encList_append_single, encUnary_apply,
        List.length_replicate, hs, encNat_apply, Nat.zero_bits, List.length_nil] at h1 h2 ⊢
      omega
  · have hs' : (st.2 == 0) = false := by simp [hs]
    simp only [hs', Bool.false_eq_true, ite_false]
    omega

theorem depMask_poly : ComputableInPolyTime (fun p : ℕ × List Bool => depMask p.1 p.2)
    encKW encNat := by
  have hlist : ComputableTidilyInPolyTime (fun p : ℕ × List Bool => List.range (EvLWE.m p.1 + 1))
      encKW (encList encUnary) := ComputableTidilyInPolyTime.range.comp (by fun_prop)
  have hgrowth : PolyBounded (fun x => (encKW x).length)
      (fun p : ℕ × List Bool => 30 * (EvLWE.m p.1 + 2)) := by
    refine PolyBounded.of_forall_le 1920 2 fun p => ?_
    have hm := m_le p.1
    simp only [length_encPair, encUnary_apply, List.length_replicate]
    have hle : p.1 + 1 ≤ 2 * p.1 + 1 + (encBits p.2).length + 1 := by omega
    have hsq := Nat.pow_le_pow_left hle 2
    nlinarith
  have hfold := ComputableTidilyInPolyTime.foldlWithInput_of_bounded_growth
    (encA := encUnary) (encL := encList encUnary) (encB := encSt)
    (list := fun p : ℕ × List Bool => List.range (EvLWE.m p.1 + 1))
    (init := fun _ => (([] : List (ℕ × ℕ × ℕ)), 0)) (step := fun p => elimStep p.1 p.2)
    (.const _) ⟨hlist, elimStep_tidy, inferInstance, inferInstance⟩
    ⟨hgrowth, fun p st j _ => elimStep_growth p.1 p.2 st j⟩
  have := (ComputableTidilyInPolyTime.snd _ _).comp hfold
  exact .of_tidy (by simpa only [Function.comp_def, depMask] using this)

theorem parityOut_poly : ComputableInPolyTime (fun p : ℕ × List Bool => parityOut p.1 p.2)
    encKW encBool := by
  have hsum : ComputableInPolyTime (fun p : ℕ × List Bool => ((List.range (EvLWE.m p.1 + 1)).map
      fun j => if (depMask p.1 p.2).testBit j then wAt p.1 p.2 j else 0).sum) encKW encNat := by
    refine sumRange (count := fun p : ℕ × List Bool => EvLWE.m p.1 + 1) (by fun_prop) ?_
    have hd := (depMask_poly.comp (by fun_prop :
      ComputableInPolyTime (fun q : (ℕ × List Bool) × ℕ => q.1) (encPair encKW encUnary) encKW)).tidy
    have ht := ComputableTidilyInPolyTime.binary_testBit hd
      (i := fun q : (ℕ × List Bool) × ℕ => q.2) (by fun_prop)
    have hw := (wAt_poly (input := encPair encKW encUnary) (l := fun q => q.1.1)
      (word := fun q => q.1.2) (j := fun q => q.2) (by fun_prop) (by fun_prop) (by fun_prop)).tidy
    exact .of_tidy (ComputableTidilyInPolyTime.ite' (encC := encBool) ht hw (.const 0))
  have h2 : ComputableTidilyInPolyTime (fun _ : ℕ × List Bool => 2) encKW encNat := .const 2
  have hm := ComputableTidilyInPolyTime.binary_mod' hsum.tidy h2
  unfold parityOut
  exact .of_tidy (ComputableTidilyInPolyTime.decide_eq' hm (.const 0))

theorem attack_isPPT : IsPPT encBool attack := by
  have h := parityOut_poly
  unfold attack
  ppt

end TestCase.EvLWE