import SigabaNeoStd.Lattices.Homomorphic.GSWCircuit
import SigabaNeoStd.Lattices.Homomorphic.BoolCompare

/-!
# The number of gates of `f̂`

Explicit upper bounds on the number of gates each building block of the Ring-GSW compiler
(`GSWCircuit`) appends to a program, and the closed form for `f̂`.

* Gadgets (namespace `SLP`): `fullAdd` appends `14` gates, `rippleAdd` `14` per bit, `muxL` `4`,
  `andL` `2`, `notL` `1` per bit; `modAdd` of `w`-bit numbers at most `addGates w = 32 w + 18`,
  `modSub` at most `33 w`.
* One term of a coefficient (`termStep`): at most `termGates k = 35 k + 18`; `leaves` over a list
  of `n` terms at most `n · termGates k`.
* `pairRound`, `rounds`, `foldSum`: each modular addition removes one number, so starting from `L`
  numbers the tree and the final fold together append at most `addGates k · |L|` gates
  (`length_rounds_add`, `length_foldSum`).
* `coefCircuit` (one output coefficient over `n` terms): at most
  `coefGates n k = n · termGates k + (n + 1) · addGates k ≤ (n + 1)(67 k + 36)`.
* `nandBlock` (`m` output coefficients): at most `m · coefGates n k`; for the explicit orders
  `n = 2kN`, `m = 4kN`: `nandGates N k`.
* `fhatSLP` of a straight-line program with `g` gates: at most `fhatGates N k g = 1 + g · nandGates N k`
  gates (`length_fhatSLP`), and `fhatGates N k g ≤ 1 + g · 4kN · (2kN + 1) · (67k + 36)`
  (`fhatGates_le`).

The core lemmas are stated for an arbitrary list of terms (`length_coefCore`, `length_foldl_le`), so
they apply as well to the compiler with explicit orders (`Algo/FhatGates`).
-/

namespace SigabaNeo.Lattices

open Cslib

/-- A left fold whose step increases a measure by at most `c` increases it by at most
`length · c`. -/
theorem length_foldl_le {σ α : Type*} (m : σ → ℕ) (f : σ → α → σ) (c : ℕ)
    (hf : ∀ s a, m (f s a) ≤ m s + c) : ∀ (l : List α) (s : σ), m (l.foldl f s) ≤ m s + l.length * c
  | [], s => by simp
  | a :: l, s => by
    have := length_foldl_le m f c hf l (f s a)
    have := hf s a
    simp only [List.foldl_cons, List.length_cons]
    nlinarith

namespace SLP

variable {ι : Type*}

theorem length_addNand (p : SLP ι) (a b : Wire ι) : (addNand p a b).1.length = p.length + 1 := by
  simp [addNand]

theorem length_xorW (p : SLP ι) (a b : Wire ι) : (xorW p a b).1.length = p.length + 4 := by
  simp [xorW, addNand]

theorem length_muxW (p : SLP ι) (s a b : Wire ι) : (muxW p s a b).1.length = p.length + 4 := by
  simp [muxW, notW, addNand]

theorem length_fullAdd (p : SLP ι) (a b c : Wire ι) : (fullAdd p a b c).1.length = p.length + 14 := by
  simp [fullAdd, xorW, orW, notW, addNand]

theorem length_rippleAdd : ∀ (p : SLP ι) (as bs : List (Wire ι)) (c : Wire ι),
    (rippleAdd p as bs c).1.length ≤ p.length + 14 * as.length ∧
      (rippleAdd p as bs c).2.length ≤ as.length + 1
  | p, [], _, c => by simp [rippleAdd]
  | p, _ :: _, [], c => by simp [rippleAdd]
  | p, a :: as, b :: bs, c => by
    have ih := length_rippleAdd (fullAdd p a b c).1 as bs (fullAdd p a b c).2.2
    rw [length_fullAdd] at ih
    simp only [rippleAdd, List.length_cons]
    omega

theorem length_muxL (s : Wire ι) : ∀ (p : SLP ι) (as bs : List (Wire ι)),
    (muxL s p as bs).1.length ≤ p.length + 4 * as.length ∧ (muxL s p as bs).2.length ≤ as.length
  | p, [], _ => by simp [muxL]
  | p, _ :: _, [] => by simp [muxL]
  | p, a :: as, b :: bs => by
    have ih := length_muxL s (muxW p s a b).1 as bs
    rw [length_muxW] at ih
    simp only [muxL, List.length_cons]
    omega

theorem length_andL (d : Wire ι) : ∀ (p : SLP ι) (as : List (Wire ι)),
    (andL d p as).1.length = p.length + 2 * as.length ∧ (andL d p as).2.length = as.length
  | p, [] => by simp [andL]
  | p, a :: as => by
    have ih := length_andL d (andW p d a).1 as
    rw [length_andW] at ih
    simp only [andL, List.length_cons]
    omega

theorem length_notL : ∀ (p : SLP ι) (as : List (Wire ι)),
    (notL p as).1.length = p.length + as.length ∧ (notL p as).2.length = as.length
  | p, [] => by simp [notL]
  | p, a :: as => by
    have ih := length_notL (notW p a).1 as
    rw [length_notW] at ih
    simp only [notL, List.length_cons]
    omega

theorem constL_length (z : Wire ι) : ∀ (w m : ℕ), (constL z w m).length = w
  | 0, _ => rfl
  | w + 1, m => by simp [constL, constL_length z w (m / 2)]

/-- The gates of a modular addition of `w`-bit numbers. -/
def addGates (w : ℕ) : ℕ := 32 * w + 18

theorem length_modAdd (z : Wire ι) (q w : ℕ) (p : SLP ι) (as bs : List (Wire ι))
    (ha : as.length ≤ w) :
    (modAdd z q w p as bs).1.length ≤ p.length + addGates w ∧ (modAdd z q w p as bs).2.length ≤ w := by
  obtain ⟨h1, h1'⟩ := length_rippleAdd p as bs z
  obtain ⟨h2, h2'⟩ := length_rippleAdd (rippleAdd p as bs z).1 (rippleAdd p as bs z).2
    (constL z (w + 1) (2 ^ (w + 1) - q)) z
  set r₂ := rippleAdd (rippleAdd p as bs z).1 (rippleAdd p as bs z).2
    (constL z (w + 1) (2 ^ (w + 1) - q)) z
  have ht : (r₂.2.take (w + 1)).length ≤ w + 1 := by simp
  refine ⟨?_, by simp [modAdd]⟩
  show (muxL _ r₂.1 (r₂.2.take (w + 1)) (rippleAdd p as bs z).2).1.length ≤ _
  refine le_trans (length_muxL _ _ _ _).1 ?_
  unfold addGates
  omega

/-- The gates of a modular subtraction of `w`-bit numbers. -/
theorem length_modSub (z : Wire ι) (q w : ℕ) (p : SLP ι) (as bs : List (Wire ι))
    (ha : as.length ≤ w) (hb : bs.length ≤ w) :
    (modSub z q w p as bs).1.length ≤ p.length + 33 * w ∧ (modSub z q w p as bs).2.length ≤ w := by
  obtain ⟨h1, -⟩ := length_notL p bs
  obtain ⟨h2, -⟩ := length_rippleAdd (notL p bs).1 as (notL p bs).2 .one
  set r₂ := rippleAdd (notL p bs).1 as (notL p bs).2 .one
  obtain ⟨h3, -⟩ := length_rippleAdd r₂.1 (r₂.2.take w) (constL z w q) z
  set r₃ := rippleAdd r₂.1 (r₂.2.take w) (constL z w q) z
  have ht : (r₂.2.take w).length ≤ w := by simp
  show (muxL _ r₃.1 (r₂.2.take w) (r₃.2.take w)).1.length ≤ _ ∧
    (muxL _ r₃.1 (r₂.2.take w) (r₃.2.take w)).2.length ≤ _
  have h4 := length_muxL (r₂.2.getD w .one) r₃.1 (r₂.2.take w) (r₃.2.take w)
  constructor
  · refine le_trans h4.1 ?_
    omega
  · exact h4.2.trans ht

end SLP

open SLP

variable {N q k : ℕ} {ι : Type*}

/-- The gates of one term of a coefficient. -/
def termGates (k : ℕ) : ℕ := 35 * k + 18

theorem length_termStep (z : Wire ι) (q k : ℕ) (repA repB : BI N k → Wire ι) (a : Fin 2)
    (col : Fin 2 × Fin k) (t : Fin N) (st : SLP ι × List (Wire ι)) (e : (Fin 2 × Fin k) × Fin N)
    (hst : st.2.length ≤ k) :
    (termStep z q k repA repB a col t st e).1.length ≤ st.1.length + termGates k ∧
      (termStep z q k repA repB a col t st e).2.length ≤ k := by
  unfold termStep termGates
  split_ifs with h
  · have hc : (coefW repA a e.1 ⟨t.val - e.2.val, by omega⟩).length = k := length_bitsL _ _
    obtain ⟨h1, h1'⟩ := length_andL (repB (e.1.1, col, e.1.2, e.2)) st.1
      (coefW repA a e.1 ⟨t.val - e.2.val, by omega⟩)
    rw [hc] at h1 h1'
    obtain ⟨h2, h2'⟩ := length_modSub z q k _ st.2 _ hst h1'.le
    dsimp only
    exact ⟨by omega, h2'⟩
  · have hc : (coefW repA a e.1 ⟨N + t.val - e.2.val, by omega⟩).length = k := length_bitsL _ _
    obtain ⟨h1, h1'⟩ := length_andL (repB (e.1.1, col, e.1.2, e.2)) st.1
      (coefW repA a e.1 ⟨N + t.val - e.2.val, by omega⟩)
    rw [hc] at h1 h1'
    obtain ⟨h2, h2'⟩ := length_modAdd z q k _ st.2 (andL _ st.1 _).2 hst
    unfold addGates at h2
    dsimp only
    exact ⟨by omega, h2'⟩

theorem length_leaves (z : Wire ι) (q k : ℕ) (repA repB : BI N k → Wire ι) (a : Fin 2)
    (col : Fin 2 × Fin k) (t : Fin N) :
    ∀ (p : SLP ι) (es : List ((Fin 2 × Fin k) × Fin N)),
      (leaves z q k repA repB a col t p es).1.length ≤ p.length + es.length * termGates k ∧
        (leaves z q k repA repB a col t p es).2.length = es.length ∧
        ∀ ws ∈ (leaves z q k repA repB a col t p es).2, ws.length ≤ k
  | p, [] => by simp [leaves]
  | p, e :: es => by
    obtain ⟨h1, h1'⟩ := length_termStep z q k repA repB a col t (p, constL z k 0) e
      (by simp [constL_length])
    have ih := length_leaves z q k repA repB a col t
      (termStep z q k repA repB a col t (p, constL z k 0) e).1 es
    simp only [leaves, List.length_cons, List.mem_cons]
    refine ⟨by simp only at h1; nlinarith [ih.1], by rw [ih.2.1], ?_⟩
    rintro ws (rfl | hws)
    · exact h1'
    · exact ih.2.2 ws hws

/-- Each modular addition of a round removes one number. -/
theorem length_pairRound_add (z : Wire ι) (q k : ℕ) : ∀ (p : SLP ι) (L : List (List (Wire ι))),
    (∀ ws ∈ L, ws.length ≤ k) →
      (pairRound z q k p L).1.length + addGates k * (pairRound z q k p L).2.length ≤
          p.length + addGates k * L.length ∧
        ∀ ws ∈ (pairRound z q k p L).2, ws.length ≤ k
  | p, [], _ => by simp [pairRound]
  | p, [a], hL => by simpa [pairRound] using hL
  | p, a :: b :: rest, hL => by
    obtain ⟨h1, h1'⟩ := length_modAdd z q k p a b (hL a (by simp))
    have ih := length_pairRound_add z q k (modAdd z q k p a b).1 rest
      (fun ws hws => hL ws (by simp [hws]))
    simp only [pairRound, List.length_cons, List.mem_cons]
    refine ⟨by nlinarith [ih.1], ?_⟩
    rintro ws (rfl | hws)
    · exact h1'
    · exact ih.2 ws hws

theorem length_rounds_add (z : Wire ι) (q k : ℕ) : ∀ (h : ℕ) (p : SLP ι) (L : List (List (Wire ι))),
    (∀ ws ∈ L, ws.length ≤ k) →
      (rounds z q k h p L).1.length + addGates k * (rounds z q k h p L).2.length ≤
          p.length + addGates k * L.length ∧
        ∀ ws ∈ (rounds z q k h p L).2, ws.length ≤ k
  | 0, p, L, hL => by simpa [rounds] using hL
  | h + 1, p, L, hL => by
    obtain ⟨h1, h1'⟩ := length_pairRound_add z q k p L hL
    have ih := length_rounds_add z q k h (pairRound z q k p L).1 (pairRound z q k p L).2 h1'
    simp only [rounds]
    exact ⟨by omega, ih.2⟩

theorem length_foldl_modAdd (z : Wire ι) (q k : ℕ) :
    ∀ (L : List (List (Wire ι))) (st : SLP ι × List (Wire ι)), st.2.length ≤ k →
      (L.foldl (fun st b => modAdd z q k st.1 st.2 b) st).1.length ≤
        st.1.length + addGates k * L.length
  | [], st, _ => by simp
  | b :: L, st, hst => by
    obtain ⟨h1, h1'⟩ := length_modAdd z q k st.1 st.2 b hst
    have ih := length_foldl_modAdd z q k L (modAdd z q k st.1 st.2 b) h1'
    simp only [List.foldl_cons, List.length_cons]
    nlinarith

theorem length_foldSum (z : Wire ι) (q k : ℕ) (p : SLP ι) (L : List (List (Wire ι)))
    (hL : ∀ ws ∈ L, ws.length ≤ k) :
    (foldSum z q k p L).1.length ≤ p.length + addGates k * L.length := by
  cases L with
  | nil => simp [foldSum]
  | cons a rest =>
    have := length_foldl_modAdd z q k rest (p, a) (hL a (by simp))
    simp only [foldSum, List.length_cons]
    nlinarith

/-- The gates of one output coefficient over `n` terms. -/
def coefGates (n k : ℕ) : ℕ := n * termGates k + (n + 1) * addGates k

theorem coefGates_le (n k : ℕ) : coefGates n k ≤ (n + 1) * (67 * k + 36) := by
  unfold coefGates termGates addGates; nlinarith

/-- **The gates of one output coefficient**, for any list of terms `es` (the body of
`coefCircuit`). -/
theorem length_coefCore (z : Wire ι) (q k : ℕ) (repA repB : BI N k → Wire ι) (Gv : ℕ) (a : Fin 2)
    (col : Fin 2 × Fin k) (t : Fin N) (h : ℕ) (es : List ((Fin 2 × Fin k) × Fin N)) (p : SLP ι) :
    (let r := leaves z q k repA repB a col t p es
     let r' := rounds z q k h r.1 (constL z k Gv :: r.2)
     foldSum z q k r'.1 r'.2).1.length ≤ p.length + coefGates es.length k := by
  obtain ⟨h1, h1l, h1'⟩ := length_leaves z q k repA repB a col t p es
  set r := leaves z q k repA repB a col t p es
  have hL : ∀ ws ∈ constL z k Gv :: r.2, ws.length ≤ k := by
    rintro ws (_ | ⟨_, hws⟩)
    · simp [constL_length]
    · exact h1' ws hws
  obtain ⟨h2, h2'⟩ := length_rounds_add z q k h r.1 _ hL
  have h3 := length_foldSum z q k (rounds z q k h r.1 (constL z k Gv :: r.2)).1 _ h2'
  simp only [List.length_cons, h1l] at h2
  show (foldSum z q k (rounds z q k h r.1 (constL z k Gv :: r.2)).1
    (rounds z q k h r.1 (constL z k Gv :: r.2)).2).1.length ≤ _
  unfold coefGates
  nlinarith

@[simp] theorem length_enumT' (N k : ℕ) : (enumT N k).length = 2 * k * N := by
  rw [length_enumT]; simp [Fintype.card_prod]

@[simp] theorem length_enumO' (N k : ℕ) : (enumO N k).length = 4 * k * N := by
  rw [← List.toFinset_card_of_nodup (nodup_enumO N k), show (enumO N k).toFinset = Finset.univ from
    Finset.eq_univ_of_forall fun e => List.mem_toFinset.mpr (mem_enumO e)]
  simp [Fintype.card_prod]; ring

theorem length_coefCircuit (z : Wire ι) (q k : ℕ) (repA repB : BI N k → Wire ι) (Gv : ℕ) (a : Fin 2)
    (col : Fin 2 × Fin k) (t : Fin N) (p : SLP ι) :
    (coefCircuit z q k repA repB Gv a col t p).1.length ≤ p.length + coefGates (2 * k * N) k := by
  have := length_coefCore z q k repA repB Gv a col t (treeHeight N k) (enumT N k) p
  rw [length_enumT'] at this
  exact this

/-- The gates of a NAND block. -/
def nandGates (N k : ℕ) : ℕ := 4 * k * N * coefGates (2 * k * N) k

section NeZero

variable [NeZero q]

theorem length_blockStep (z : Wire ι) (hk : q < 2 ^ k) (repA repB : BI N k → Wire ι)
    (st : SLP ι × (OI N k → List (Wire ι))) (o : OI N k) :
    (blockStep z q k hk repA repB st o).1.length ≤ st.1.length + coefGates (2 * k * N) k :=
  length_coefCircuit z q k repA repB _ _ _ _ st.1

theorem length_nandBlock (z : Wire ι) (hk : q < 2 ^ k) (repA repB : BI N k → Wire ι) (p : SLP ι) :
    (nandBlock z q k hk repA repB p).1.length ≤ p.length + nandGates N k := by
  have := length_foldl_le (fun st : SLP ι × (OI N k → List (Wire ι)) => st.1.length)
    (blockStep z q k hk repA repB) _ (length_blockStep z hk repA repB) (enumO N k)
    (p, fun _ => [])
  rw [length_enumO'] at this
  exact this

theorem length_compileSLP {A : Type*} (z : Wire (A × BI N k)) (hk : q < 2 ^ k) (p : SLP A)
    (w : Wire A) (prog : SLP (A × BI N k)) :
    (compileSLP z hk p w prog).1.length ≤ prog.length + p.length * nandGates N k :=
  length_foldl_le (fun st : SLP (A × BI N k) × List (BI N k → Wire (A × BI N k)) => st.1.length)
    (compileStep z hk) _ (fun st _ => length_nandBlock z hk _ _ st.1) p (prog, [])

/-- The gates of `f̂` for a straight-line program with `g` gates. -/
def fhatGates (N k g : ℕ) : ℕ := 1 + g * nandGates N k

theorem fhatGates_le (N k g : ℕ) :
    fhatGates N k g ≤ 1 + g * (4 * k * N * ((2 * k * N + 1) * (67 * k + 36))) := by
  unfold fhatGates nandGates
  have := coefGates_le (2 * k * N) k
  have h2 : 4 * k * N * coefGates (2 * k * N) k ≤ 4 * k * N * ((2 * k * N + 1) * (67 * k + 36)) :=
    Nat.mul_le_mul_left _ this
  have := Nat.mul_le_mul_left g h2
  omega

/-- **The number of gates of `f̂`** for a straight-line program `p`. -/
theorem length_fhatSLP {A : Type*} (hk : q < 2 ^ k) (p : SLP A) (w : Wire A) :
    (fhatSLP (N := N) hk p w).1.length ≤ fhatGates N k p.length := by
  have := length_compileSLP (N := N) (.gate 0) hk p w [⟨.one, .one⟩]
  simpa [fhatSLP, fhatGates] using this

end NeZero

end SigabaNeo.Lattices
