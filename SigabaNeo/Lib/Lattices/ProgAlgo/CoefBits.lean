import SigabaNeo.Lib.Lattices.ProgAlgo.BinMul

/-!
# The bits of the coefficients of ring words as a tape program

For a stream of `E` ring words (`N` coefficients of `K` bits each, least significant bit first),
`coefBitsP : Prog 13` shifts into the register `0`, for each word, the bit `b` of the coefficient
`t` for `b < K` (outer) and `t < N` (inner), then `P` zeros (the bits `b ≥ K` of a binary
decomposition of width `k > K`): the bits `ψ_j` of BGG+ encodings of Ring-GSW ciphertexts, in
the order of their index `(b, t)`.

Tapes: `0` the output register, `1` the stream, templates `2` (`K`), `3` (`N`), `4` (`N K`),
`5` (`E`), `6` (`P`); scratch `7 … 12`, blank before and after.

**`run_coefBitsP`**: the register receives `eStepC` iterated `E` times; `eStepC_eq` evaluates a
step: the bits `hd (w.drop (b + t K))`, then `P` zeros.
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo

namespace Prog

open scoped Prog

/-! ### The abstract steps -/

/-- One coefficient: shift in the head of the stream, then skip `K` bits. -/
def tStepC (K : ℕ) (a : List Bool × List Bool) : List Bool × List Bool :=
  ((a.1 ++ [hd a.2]).tail, a.2.drop K)

/-- One bit position: the `N` coefficients from the current position, then move by one bit. -/
def bStepC (N K : ℕ) (a : List Bool × List Bool) : List Bool × List Bool :=
  (((tStepC K)^[N] (a.1, a.2)).1, a.2.tail)

/-- One ring word: the `K` bit positions, `P` zeros, then the next word. -/
def eStepC (N K P : ℕ) (a : List Bool × List Bool) : List Bool × List Bool :=
  ((((bStepC N K)^[K] (a.1, a.2)).1 ++ List.replicate P false).drop P, a.2.drop (N * K))

/-! ### The program -/

def dpT : Fin 3 → Fin 13 := ![11, 12, 2]
def flC : Fin 3 → Fin 13 := ![0, 12, 6]
def dpE : Fin 3 → Fin 13 := ![1, 12, 4]
theorem dpT_inj : Function.Injective dpT := by decide
theorem flC_inj : Function.Injective flC := by decide
theorem dpE_inj : Function.Injective dpE := by decide

/-- One coefficient. -/
def tBodyC : Prog 13 := push 0 11 ⨾ map dpT dropP
/-- One bit position. -/
def bBodyC : Prog 13 := cp 11 10 ⨾ forN 9 3 tBodyC ⨾ clr 11 ⨾ tl 10
/-- One ring word. -/
def eBodyC : Prog 13 := cp 10 1 ⨾ forN 8 2 bBodyC ⨾ map flC (fillP false) ⨾ clr 10 ⨾ map dpE dropP

/-- **The coefficient bits of a stream of ring words.** -/
def coefBitsP : Prog 13 := forN 7 5 eBodyC

theorem noGrow_coefBitsP : coefBitsP.NoGrow := rfl
theorem wf_coefBitsP : coefBitsP.WF := wf_of_wfB (by decide)

/-! ### The laws -/

def tGC (S : Store 13) : List Bool × List Bool → Store 13
  | (z, d2) => Function.update (Function.update S 0 z) 11 d2

theorem run_tBodyC {K : ℕ} (S : Store 13) (h12 : S 12 = []) (hK : (S 2).length = K) (a)
    (w : List Bool) :
    run tBodyC (Function.update (tGC S a) 9 w) = Function.update (tGC S (tStepC K a)) 9 w := by
  obtain ⟨z, d2⟩ := a
  simp only [tBodyC, run_seq, run_push]
  rw [run_dropP_map dpT_inj _ (by simp [dpT, tGC, h12])]
  funext t
  fin_cases t <;> simp [dpT, tGC, tStepC, hK]

def bGC (S : Store 13) : List Bool × List Bool → Store 13
  | (z, d) => Function.update (Function.update S 0 z) 10 d

theorem run_bBodyC {N K : ℕ} (S : Store 13) (h9 : S 9 = []) (h11 : S 11 = []) (h12 : S 12 = [])
    (hK : (S 2).length = K) (hN : (S 3).length = N) (a) (w : List Bool) :
    run bBodyC (Function.update (bGC S a) 8 w) = Function.update (bGC S (bStepC N K a)) 8 w := by
  obtain ⟨z, d⟩ := a
  set T := Function.update (bGC S (z, d)) 8 w with hT
  have e0 : run (cp 11 10) T = tGC T (z, d) := by
    funext t; simp only [run_copy, tGC, hT, bGC]; fin_cases t <;> simp
  have hloop := run_forN 9 3 tBodyC (tGC T) (tStepC K)
    (fun a w' => run_tBodyC T (by simp [hT, bGC, h12]) (by simp [hT, bGC, hK]) a w') (z, d) _ rfl
  have hsplit : run bBodyC T = run (clr 11 ⨾ tl 10) (run (forN 9 3 tBodyC) (run (cp 11 10) T)) := rfl
  rw [hsplit, e0, hloop]
  have e3 : tGC T (z, d) 3 = S 3 := by simp [tGC, hT, bGC]
  rw [e3, hN]
  funext t
  simp only [run_seq, run_clear, run_tail]
  fin_cases t <;> simp [tGC, hT, bGC, bStepC, h9, h11]

def eGC (S : Store 13) : List Bool × List Bool → Store 13
  | (z, ps) => Function.update (Function.update S 0 z) 1 ps

theorem run_eBodyC {N K P : ℕ} (S : Store 13) (h8 : S 8 = []) (h9 : S 9 = []) (h10 : S 10 = [])
    (h11 : S 11 = []) (h12 : S 12 = []) (hK : (S 2).length = K) (hN : (S 3).length = N)
    (hNK : (S 4).length = N * K) (hP : (S 6).length = P) (a) (w : List Bool) :
    run eBodyC (Function.update (eGC S a) 7 w) = Function.update (eGC S (eStepC N K P a)) 7 w := by
  obtain ⟨z, ps⟩ := a
  set T := Function.update (eGC S (z, ps)) 7 w with hT
  have e0 : run (cp 10 1) T = bGC T (z, ps) := by
    funext t; simp only [run_copy, bGC, hT, eGC]; fin_cases t <;> simp
  have hloop := run_forN 8 2 bBodyC (bGC T) (bStepC N K)
    (fun a w' => run_bBodyC T (by simp [hT, eGC, h9]) (by simp [hT, eGC, h11])
      (by simp [hT, eGC, h12]) (by simp [hT, eGC, hK]) (by simp [hT, eGC, hN]) a w') (z, ps) _ rfl
  have hsplit : run eBodyC T = run (map flC (fillP false) ⨾ clr 10 ⨾ map dpE dropP)
      (run (forN 8 2 bBodyC) (run (cp 10 1) T)) := rfl
  rw [hsplit, e0, hloop]
  have e2 : bGC T (z, ps) 2 = S 2 := by simp [bGC, hT, eGC]
  rw [e2, hK]
  simp only [run_seq, run_clear]
  rw [run_fillP_map flC_inj _ _ (by simp [flC, bGC, hT, eGC, h12]),
    run_dropP_map dpE_inj _ (by simp [dpE, flC, bGC, hT, eGC, h12])]
  funext t
  fin_cases t <;> simp [flC, dpE, bGC, hT, eGC, eStepC, h8, h10, hP, hNK]

/-- **The coefficient bits of a stream of ring words**: the register `0` and the stream `1`
after `|s 5|` words. -/
theorem run_coefBitsP {N K P : ℕ} (S : Store 13) (hS : ∀ i : Fin 13, 7 ≤ i.val → S i = [])
    (hK : (S 2).length = K) (hN : (S 3).length = N) (hNK : (S 4).length = N * K)
    (hP : (S 6).length = P) :
    run coefBitsP S = eGC S ((eStepC N K P)^[(S 5).length] (S 0, S 1)) := by
  have h := run_forN 7 5 eBodyC (eGC S) (eStepC N K P)
    (fun a w => run_eBodyC S (hS 8 (by decide)) (hS 9 (by decide)) (hS 10 (by decide))
      (hS 11 (by decide)) (hS 12 (by decide)) hK hN hNK hP a w) (S 0, S 1) S
    (by funext t; simp only [eGC]; fin_cases t <;> simp)
  rw [coefBitsP, h]
  funext t
  simp only [eGC]
  fin_cases t <;> simp [hS]

/-! ### The steps on words -/

theorem length_flatMap_eq {α : Type} {n : ℕ} (l : List α) (f : α → List Bool)
    (h : ∀ x ∈ l, (f x).length = n) : (l.flatMap f).length = l.length * n := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, h a (by simp),
      ih (fun x hx => h x (by simp [hx])), List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem tStepC_iter (K : ℕ) : ∀ (n : ℕ) (z d : List Bool),
    (tStepC K)^[n] (z, d) =
      ((z ++ (List.range n).map fun t => hd (d.drop (t * K))).drop n, d.drop (n * K))
  | 0, z, d => by simp
  | n + 1, z, d => by
    rw [Function.iterate_succ_apply', tStepC_iter K n z d, tStepC]
    dsimp only
    have hl : ((List.range n).map fun t => hd (d.drop (t * K))).length = n := by simp
    have := drop_append_drop z ((List.range n).map fun t => hd (d.drop (t * K)))
      [hd (d.drop (n * K))]
    rw [hl] at this
    simp only [List.length_singleton] at this
    rw [← List.drop_one, this]
    simp only [List.range_succ, List.map_append, List.map_singleton, List.append_assoc,
      List.drop_drop, Prod.mk.injEq, true_and]
    congr 1
    ring

theorem bStepC_iter (N K : ℕ) : ∀ (m : ℕ) (z d : List Bool),
    (bStepC N K)^[m] (z, d) =
      ((z ++ (List.range m).flatMap fun b => (List.range N).map fun t => hd (d.drop (b + t * K))).drop
        (m * N), d.drop m)
  | 0, z, d => by simp
  | m + 1, z, d => by
    rw [Function.iterate_succ_apply', bStepC_iter N K m z d, bStepC, tStepC_iter]
    dsimp only
    have hl : ((List.range m).flatMap fun b => (List.range N).map fun t =>
        hd (d.drop (b + t * K))).length = m * N := by
      rw [length_flatMap_eq _ _ (n := N) (fun _ _ => by simp), List.length_range]
    have hT : ((List.range N).map fun t => hd ((d.drop m).drop (t * K))).length = N := by simp
    have := drop_append_drop z ((List.range m).flatMap fun b => (List.range N).map fun t =>
        hd (d.drop (b + t * K))) ((List.range N).map fun t => hd ((d.drop m).drop (t * K)))
    rw [hl, hT] at this
    rw [this, List.range_succ, List.flatMap_append, List.flatMap_singleton, ← List.drop_one,
      List.drop_drop, Nat.succ_mul]
    simp only [List.drop_drop, List.append_assoc]

/-- **One ring word**: its coefficient bits `hd (w.drop (b + t K))`, `b < K`, `t < N`, then
`P` zeros. -/
theorem eStepC_eq (N K P : ℕ) (z w : List Bool) :
    eStepC N K P (z, w) =
      ((z ++ ((List.range K).flatMap fun b => (List.range N).map fun t => hd (w.drop (b + t * K))) ++
        List.replicate P false).drop (K * N + P), w.drop (N * K)) := by
  rw [eStepC, bStepC_iter]
  dsimp only
  have hl : ((List.range K).flatMap fun b => (List.range N).map fun t =>
      hd (w.drop (b + t * K))).length = K * N := by
    rw [length_flatMap_eq _ _ (n := N) (fun _ _ => by simp), List.length_range]
  have := drop_append_drop z ((List.range K).flatMap fun b => (List.range N).map fun t =>
      hd (w.drop (b + t * K))) (List.replicate P false)
  rw [hl, List.length_replicate] at this
  rw [this, List.append_assoc]

end Prog

end SigabaNeo.Tape
