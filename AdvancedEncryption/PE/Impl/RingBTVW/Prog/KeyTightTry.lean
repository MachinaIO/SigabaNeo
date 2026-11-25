import PE.Impl.RingBTVW.Prog.KeyTightLib
import PE.Impl.RingBTVW.Prog.KeyTryRealLaw

/-!
# The real key try, per tape

`ub_keyTryR` (`PE.Impl.RingBTVW.Prog.KeyGenP`) bounds the key try `keyTryRCoinsP` uniformly by
`23 (M + 1)² + tbC · (2M + 1)^tbD` (`tbD = 8`, `tbC = 11494`): every loop of its matrix products,
gadget inverse, ring operations is charged the uniform bound `M`. Here:

* `ph_coinsAt`: drawing the coins costs `m` rounds of a few primitives (`m` the template on tape
  `25`), and leaves the coins and the counter at `m` bits;
* `absRun_keyTry`: the abstract interpreter on `keyTryRP ⨾ clr 3` from the store `σKR` (the
  templates of `keyTmplR` with their lengths, the data words — public key, key row, `e`, `t`, the
  output — at the top, the norm word and `powW` of `K` bits, scratch blank) yields the sweeps `wKR`,
  a polynomial in `N, K, k, d, nT, P, B, m` and the top, each loop charged its own counter;
* **`ph_keyTryR_v`**: the key try from per-tape bounds below `σKR` takes at most
  `coinT S m + (2 top + 3) · wKR` steps.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg
open scoped SigabaNeo.Tape.Prog

/-! ### The coins -/

section Coins

variable {k : ℕ}

theorem supB_update_le_add (ℓ : Fin k → ℕ) (i : Fin k) (v : ℕ) :
    supB (Function.update ℓ i v) ≤ supB ℓ + v :=
  supB_le_of fun t => by
    by_cases h : t = i
    · subst h; simp
    · rw [Function.update_of_ne h]; exact (le_supB ℓ t).trans (Nat.le_add_right _ _)

theorem timeBoundT_coinBody (r b : Fin k) (ℓ : Fin k → ℕ) :
    Prog.timeBoundT (Prog.coin b ⨾ Prog.push r b ⨾ Prog.clr b) ℓ ≤ 6 * supB ℓ + 30 := by
  have h1 := supB_update_le_add ℓ b 1
  have e : Prog.lenBoundT (Prog.push r b) (Function.update ℓ b 1) = Function.update ℓ b 1 := by
    funext t; simp [Prog.push, Prog.sin, Prog.lenBoundT, Prim.lenT]
  show (2 * supB ℓ + 4) + (Prog.timeBoundT (Prog.push r b) (Function.update ℓ b 1) +
    Prog.timeBoundT (Prog.clr b) (Prog.lenBoundT (Prog.push r b) (Function.update ℓ b 1))) ≤ _
  rw [e]
  have p1 := pad_le (Prim.carry (Prog.sinOp true) r r)
  have p2 := pad_le (Prim.carry (Prog.sinOp false) r r)
  have p3 := pad_le (Prim.clear b)
  simp only [Prog.push, Prog.sin, Prog.timeBoundT]
  omega

/-- The steps of `coinsAt` from tapes below `S`, with `m` coins. -/
def coinT (S m : ℕ) : ℕ := 2 * (2 * (S + 1) + 3) + (m * (8 * S + 34) + 2)

/-- **Drawing the coins**: the target `r` and the counter `c` get the length `m = β t` of the
template, every other tape keeps its bound. -/
theorem ph_coinsAt {r t c b : Fin k} (hrt : r ≠ t) (β : Fin k → ℕ) {S : ℕ} (hS : ∀ i, β i ≤ S) :
    Ph (.prog (Prog.coinsAt r t c b)) β (coinT S (β t))
      (Function.update (Function.update β r (β t)) c (β t)) := by
  set β1 := Function.update β r (β t) with hβ1
  set β2 := Function.update β1 c (β t) with hβ2
  have hS2 : ∀ i, β2 i ≤ S := fun i => by
    simp only [hβ2, hβ1, Function.update_apply]; split_ifs <;> exact hS _
  have hinv : Prog.loopStepT c (Prog.coin b ⨾ Prog.push r b ⨾ Prog.clr b) β2 ≤ β2 := by
    intro i
    simp only [Prog.loopStepT, Prog.lenBoundT, Prog.push, Prog.sin, Prim.lenT,
      tailB, Function.update_apply]
    split_ifs <;> simp_all
  intro ℓ hℓ
  have h1 : Prog.lenBoundT (Prog.cp r t) ℓ ≤ β1 := fun i => by
    simp only [Prog.lenBoundT, Prim.lenT, hβ1, Function.update_apply]
    split_ifs
    · exact hℓ t
    · exact hℓ i
  have h2 : Prog.lenBoundT (Prog.cp c t) (Prog.lenBoundT (Prog.cp r t) ℓ) ≤ β2 := fun i => by
    have := hℓ t; have := hℓ i
    simp only [Prog.lenBoundT, Prim.lenT, hβ2, hβ1, Function.update_apply]
    split_ifs <;> simp_all
  have hl := Prog.lenBoundT_loop_le_of_inv c _ h2 hinv
  have ht := Prog.timeBoundT_loop_le_of_inv c _ h2 hinv
  have hr := Prog.roundTimeT_le (Prog.coin b ⨾ Prog.push r b ⨾ Prog.clr b) c β2
  have hb := timeBoundT_coinBody r b β2
  have hs2 := supB_le_of hS2
  have hsl : supB ℓ ≤ S := supB_le_of fun i => (hℓ i).trans (hS i)
  have hs1 : supB (Prog.lenBoundT (Prog.cp r t) ℓ) ≤ S :=
    supB_le_of fun i => (h1 i).trans (by simp only [hβ1, Function.update_apply]; split_ifs <;> exact hS _)
  have hc : (Prog.lenBoundT (Prog.cp c t) (Prog.lenBoundT (Prog.cp r t) ℓ)) c ≤ β t :=
    (h2 c).trans (by simp [hβ2])
  refine ⟨?_, hl⟩
  have hround : Prog.roundTimeT (Prog.timeBoundT (Prog.coin b ⨾ Prog.push r b ⨾ Prog.clr b)) c β2 + 1 ≤
      8 * S + 34 := by omega
  have hm := Nat.mul_le_mul hc hround
  have e1 : Prog.timeBoundT (Prog.cp r t) ℓ = 2 * (supB ℓ + 0) + 3 := rfl
  have e2 : Prog.timeBoundT (Prog.cp c t) (Prog.lenBoundT (Prog.cp r t) ℓ) =
    2 * (supB (Prog.lenBoundT (Prog.cp r t) ℓ) + 0) + 3 := rfl
  show Prog.timeBoundT (Prog.cp r t) ℓ + (Prog.timeBoundT (Prog.cp c t) _ + Prog.timeBoundT
    (Prog.loop c _) _) ≤ _
  rw [e1, e2]
  unfold coinT
  omega

end Coins

/-! ### The certificate of the key try -/

namespace KeyV

open Sym

/-- The monomial `c · N^a K^b k^c d^e nT^f P^g B^h m^i` (variable `0` the top). -/
def mo (c : ℕ) (e : List ℕ) : Poly := [(0 :: e, c)]

def qN : Poly := mo 1 [1]
def qK : Poly := mo 1 [0, 1]
def qNK : Poly := mo 1 [1, 1]
def qm : Poly := mo 1 [0, 0, 0, 0, 0, 0, 0, 1]
def qP : Poly := mo 1 [0, 0, 0, 0, 0, 1]

/-- **The abstract store at the key try**: data at the top, templates at their lengths, the norm
word and `powW` at `K`, the coins and their counter at `m`, scratch blank. -/
def σKR : Asg :=
  [pTop, pTop, pTop, qm, qK, qK, qK, qN, qNK, mo 1 [0, 0, 0, 0, 0, 0, 1],
    pAdd (mo 1 [1, 0, 0, 1]) (mo 1 [1, 0, 0, 0, 1]), pAdd (mo 1 [1, 1, 0, 1]) (mo 1 [1, 1, 0, 0, 1]),
    mo 1 [0, 0, 1], mo 2 [0, 0, 1], pC 1, pC 1, mo 1 [0, 0, 0, 1], mo 1 [0, 0, 0, 0, 1],
    mo 1 [1, 1, 0, 1], mo 1 [1, 1, 0, 0, 1], mo 2 [1, 1, 1], mo 1 [1, 0, 0, 1], qP, qP,
    pAdd qP (pAdd (pAdd (mo 1 [1, 1, 0, 1]) (mo 1 [1, 1, 0, 0, 1])) (mo 2 [1, 1, 1])), qm] ++
  List.replicate 15 [] ++ [qm] ++ List.replicate 48 [] ++
  [pTop, pTop, mo 2 [1, 0, 1], mo 4 [1, 1, 2], [], [], [], [], [], [], mo 2 [0, 0, 1]]

/-- The store after the key try. -/
def oKR : Asg := ((absRun 8 (ProgKeyR.keyTryRP ⨾ Prog.clr 3) σKR).map (·.1)).getD []
/-- **The sweeps of the key try.** -/
def wKR : Poly := ((absRun 8 (ProgKeyR.keyTryRP ⨾ Prog.clr 3) σKR).map (·.2)).getD []

set_option maxRecDepth 100000 in
theorem absRun_keyTry : absRun 8 (ProgKeyR.keyTryRP ⨾ Prog.clr 3) σKR = some (oKR, wKR) := by
  decide +kernel

end KeyV

set_option maxRecDepth 100000 in
open KeyV in
/-- **The real key try, per tape**: from bounds `γ` below the top whose coins and counter, set to the
template `γ 25`, fit `σKR`. -/
theorem ph_keyTryR_v (ρ : List ℕ) (γ : Fin 101 → ℕ)
    (hin : Function.update (Function.update γ 3 (γ 25)) 41 (γ 25) ≤ Sym.bnd ρ σKR)
    (htop : ∀ j, γ j ≤ Sym.top ρ) :
    Ph (.prog ProgKeyR.keyTryRCoinsP) γ
      (coinT (Sym.top ρ) (γ 25) + (2 * Sym.top ρ + 3) * Sym.pEval ρ wKR) (capB ρ oKR) := by
  have h1 := ph_coinsAt (r := (3 : Fin 101)) (t := 25) (c := 41) (b := 42) (by decide +kernel) γ htop
  have htop' : ∀ j, Function.update (Function.update γ 3 (γ 25)) 41 (γ 25) j ≤ Sym.top ρ := by
    intro j; simp only [Function.update_apply]; split_ifs <;> exact htop _
  have h2 := ph_absRun absRun_keyTry ρ hin htop'
  exact fun ℓ hℓ => (h1.seq h2) ℓ hℓ

end AdvancedEncryption.RingBTVW.Prog
