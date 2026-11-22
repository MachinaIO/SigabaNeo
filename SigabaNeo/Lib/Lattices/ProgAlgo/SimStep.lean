import SigabaNeo.Lib.Lattices.ProgAlgo.SimJoint
import SigabaNeo.Lib.Lattices.ProgAlgo.Spec
import SigabaNeo.Lib.Machines.Prog.Split

/-!
# The step of the simulation on joint words as a gate program

`simStepP G : Prog 132` computes the step of the simulation `simStepJW N K k r d gad ginv` on joint
words (`run_simStepP`), for any program `G` of `G⁻¹` (`GinvSpec`): it splits the two inputs
(`splitP`), computes `G⁻¹(A_v)` with `G`, then

  `G − A_u G⁻¹(A_v)`, `−(W_u G⁻¹(A_v) + x_u W_v)`, `1 − x_u x_v`

with `matMulP`, `subRWP`, `addRWP`, `mulRWP` (the entrywise product `x_u W_v` is the product of a
`1 × 1` and a `1 × d 2k` matrix word, `matMulW_one_one`), and joins the three parts (`joinP`).
`stepSpec_simStepP`: it is a gate program (`StepSpec`) for `simStepJW`.

**Tapes.** `0` the value, `1` `2` the inputs; templates `3` … `17` of lengths `K`, `N`, `N K`, `r`,
`2k`, `2k`, `d 2k`, `1`, `1`, `d`, `La = r 2k N K`, `Lw = d 2k N K`, `La + Lw + N K`, `r 2k N`,
`d 2k N` (tape `18` unused); content templates `19` the gadget word `gad`, `20` `zeroW Lw`, `21`
`oneW N K`; registers `22 … 36` and scratch `37 … 85`, blank before and after; the tapes `86 … 131`
are the tapes `2 … 47` of `G` (its templates and scratch, `GPre`).
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices SigabaNeo.Lattices.Algo

namespace Prog

open scoped Prog

/-- **A program of `G⁻¹`** on words of `Lin` bits: tape `0` the value, `1` the input; the
precondition `GPre` only looks at the tapes `2 … 47`. -/
structure GinvSpec (G : Prog 48) (Lin Lout : ℕ) (ginv : List Bool → List Bool)
    (GPre : Store 48 → Prop) : Prop where
  noGrow : G.NoGrow
  wf : G.WF
  pre_congr : ∀ s s' : Store 48, (∀ i : Fin 48, 2 ≤ i.val → s i = s' i) → GPre s → GPre s'
  run_eq : ∀ s, GPre s → (s 1).length = Lin → run G s = Function.update s 0 (ginv (s 1))
  len : ∀ a, a.length = Lin → (ginv a).length = Lout

def sU : Fin 10 → Fin 132 := ![22, 23, 24, 1, 13, 14, 5, 37, 38, 39]
def sV : Fin 10 → Fin 132 := ![25, 26, 27, 2, 13, 14, 5, 37, 38, 39]
def vG : Fin 48 → Fin 132 := ![28, 25, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]
def mP1 : Fin 59 → Fin 132 := ![29, 22, 28, 3, 4, 5, 6, 7, 8, 13, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85]
def sO1 : Fin 28 → Fin 132 := ![30, 19, 29, 3, 16, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59]
def mP2 : Fin 59 → Fin 132 := ![31, 23, 28, 3, 4, 5, 12, 7, 8, 14, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85]
def mS : Fin 59 → Fin 132 := ![32, 24, 26, 3, 4, 5, 10, 11, 9, 14, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85]
def aSum : Fin 28 → Fin 132 := ![33, 31, 32, 3, 17, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59]
def sO2 : Fin 28 → Fin 132 := ![34, 20, 33, 3, 17, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59]
def mM3 : Fin 38 → Fin 132 := ![35, 24, 27, 3, 4, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69]
def sO3 : Fin 28 → Fin 132 := ![36, 21, 35, 3, 4, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59]
def jO : Fin 11 → Fin 132 := ![0, 30, 34, 36, 13, 14, 5, 15, 37, 38, 39]
theorem sU_inj : Function.Injective sU := by decide
theorem sV_inj : Function.Injective sV := by decide
theorem vG_inj : Function.Injective vG := by decide
theorem mP1_inj : Function.Injective mP1 := by decide
theorem sO1_inj : Function.Injective sO1 := by decide
theorem mP2_inj : Function.Injective mP2 := by decide
theorem mS_inj : Function.Injective mS := by decide
theorem aSum_inj : Function.Injective aSum := by decide
theorem sO2_inj : Function.Injective sO2 := by decide
theorem mM3_inj : Function.Injective mM3 := by decide
theorem sO3_inj : Function.Injective sO3 := by decide
theorem jO_inj : Function.Injective jO := by decide

/-- Split the two inputs into registers `22 … 27`. -/
def simPre : Prog 132 := map sU splitP ⨾ map sV splitP

/-- From `G⁻¹(A_v)` on `28`: the three parts on `30`, `34`, `36`, joined on `0`; registers cleared. -/
def simPost : Prog 132 :=
  map mP1 matMulP ⨾ map sO1 subRWP ⨾ map mP2 matMulP ⨾ map mS matMulP ⨾ map aSum addRWP ⨾
    map sO2 subRWP ⨾ map mM3 mulRWP ⨾ map sO3 subRWP ⨾ map jO joinP ⨾
    clr 22 ⨾ clr 23 ⨾ clr 24 ⨾ clr 25 ⨾ clr 26 ⨾ clr 27 ⨾ clr 28 ⨾ clr 29 ⨾ clr 30 ⨾ clr 31 ⨾
    clr 32 ⨾ clr 33 ⨾ clr 34 ⨾ clr 35 ⨾ clr 36

/-- **The step of the simulation on joint words**, with the program `G` of `G⁻¹`. -/
def simStepP (G : Prog 48) : Prog 132 := seq simPre (seq (map vG G) simPost)

theorem run_simPre (s : Store 132) (h37 : s 37 = []) (h38 : s 38 = []) (h39 : s 39 = [])
    {a b c : ℕ} (h13 : (s 13).length = a) (h14 : (s 14).length = b) (h5 : (s 5).length = c) :
    run simPre s = Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update s 22 (takeD a (s 1))) 23 (takeD b ((s 1).drop a))) 24
      (takeD c ((s 1).drop (a + b)))) 25 (takeD a (s 2))) 26 (takeD b ((s 2).drop a))) 27
      (takeD c ((s 2).drop (a + b))) := by
  simp only [simPre, run_seq]
  rw [run_splitP_map sU_inj _ (by simp [sU, h37]) (by simp [sU, h38]) (by simp [sU, h39]),
    run_splitP_map sV_inj _ (by simp [sU, sV, h37]) (by simp [sU, sV, h38])
      (by simp [sU, sV, h39])]
  simp [sU, sV, h13, h14, h5]

theorem run_addRWP_mat_map {u : Fin 28 → Fin k} (hu : Function.Injective u) {K N L : ℕ}
    (s : Store k) (hs : ∀ i : Fin 28, 5 ≤ i.val → s (u i) = []) (hK : (s (u 3)).length = K)
    (hLN : (s (u 4)).length = L * N) (hx : (s (u 1)).length = L * N * K)
    (hy : (s (u 2)).length = L * N * K) :
    run (map u addRWP) s = Function.update s (u 0) (matAddW N K L (s (u 1)) (s (u 2))) :=
  run_map_eq_update hu _ s 0 _ (run_addRWP_mat (s ∘ u) hs hK hLN hx hy)

theorem run_subRWP_map {u : Fin 28 → Fin k} (hu : Function.Injective u) {K N : ℕ}
    (s : Store k) (hs : ∀ i : Fin 28, 5 ≤ i.val → s (u i) = []) (hK : (s (u 3)).length = K)
    (hN : (s (u 4)).length = N) (hx : (s (u 1)).length = N * K)
    (hy : (s (u 2)).length = N * K) :
    run (map u subRWP) s = Function.update s (u 0) (subRW N K (s (u 1)) (s (u 2))) :=
  run_map_eq_update hu _ s 0 _ (run_subRWP (s ∘ u) hs hK hN hx hy)

theorem length_matAddW {N K L : ℕ} {x : List Bool} (hx : x.length = L * (N * K)) (y : List Bool) :
    (matAddW N K L x y).length = L * (N * K) :=
  length_concatN fun p hp => length_addRW N K (length_block hx hp) _

/-- The three parts of the step, from the registers. -/
def simParts (N K k r d : ℕ) (gad zw one au wu xu wv xv gi : List Bool) : List Bool :=
  jointW (matSubW N K (r * (2 * k)) gad (matMulW N K r (2 * k) (2 * k) au gi),
    matSubW N K (d * (2 * k)) zw (matAddW N K (d * (2 * k)) (matMulW N K d (2 * k) (2 * k) wu gi)
      (matMulW N K 1 1 (d * (2 * k)) xu wv)),
    subRW N K one (mulRW N K xu xv))

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
theorem run_simPost {N K k r d : ℕ} (t : Store 132)
    (hb : ∀ i : Fin 132, 29 ≤ i.val → i.val < 86 → t i = [])
    (h3 : (t 3).length = K) (h4 : (t 4).length = N) (h5 : (t 5).length = N * K)
    (h6 : (t 6).length = r) (h7 : (t 7).length = 2 * k) (h8 : (t 8).length = 2 * k)
    (h9 : (t 9).length = d * (2 * k)) (h10 : (t 10).length = 1) (h11 : (t 11).length = 1)
    (h12 : (t 12).length = d) (h13 : (t 13).length = lenA N K k r)
    (h14 : (t 14).length = lenA N K k d) (h15 : (t 15).length = lenA N K k r + lenA N K k d + N * K)
    (h16 : (t 16).length = r * (2 * k) * N) (h17 : (t 17).length = d * (2 * k) * N)
    (h19 : (t 19).length = lenA N K k r) (h20 : (t 20).length = lenA N K k d)
    (h21 : (t 21).length = N * K)
    (h22 : (t 22).length = lenA N K k r) (h23 : (t 23).length = lenA N K k d)
    (h24 : (t 24).length = N * K) (h26 : (t 26).length = lenA N K k d)
    (h27 : (t 27).length = N * K) (h28 : (t 28).length = 2 * k * (2 * k * (N * K))) :
    run simPost t = Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update t 22 []) 23 []) 24 [])
        25 []) 26 []) 27 []) 28 [])
      0 (simParts N K k r d (t 19) (t 20) (t 21) (t 22) (t 23) (t 24) (t 26) (t 27) (t 28)) := by
  have hbs : ∀ i : Fin 132, 29 ≤ i.val → i.val < 86 → t i = [] := hb
  simp only [simPost, run_seq, run_clear]
  rw [run_matMulP_map mP1_inj (K := K) (N := N) (m := r) (n := 2 * k) (l := 2 * k) _ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_,
    run_subRWP_mat_map sO1_inj (K := K) (N := N) (L := r * (2 * k)) _ ?_ ?_ ?_ ?_ ?_,
    run_matMulP_map mP2_inj (K := K) (N := N) (m := d) (n := 2 * k) (l := 2 * k) _ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_,
    run_matMulP_map mS_inj (K := K) (N := N) (m := 1) (n := 1) (l := d * (2 * k)) _ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_,
    run_addRWP_mat_map aSum_inj (K := K) (N := N) (L := d * (2 * k)) _ ?_ ?_ ?_ ?_ ?_,
    run_subRWP_mat_map sO2_inj (K := K) (N := N) (L := d * (2 * k)) _ ?_ ?_ ?_ ?_ ?_,
    run_mulRWP_map mM3_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_ ?_,
    run_subRWP_map sO3_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_ ?_,
    run_joinP_map jO_inj _ ?_ ?_ ?_ ?_]
  · have e1 : (matSubW N K (r * (2 * k)) (t 19) (matMulW N K r (2 * k) (2 * k) (t 22)
        (t 28))).length = lenA N K k r := length_matSubW h19 _
    have e2 : (matSubW N K (d * (2 * k)) (t 20) (matAddW N K (d * (2 * k))
        (matMulW N K d (2 * k) (2 * k) (t 23) (t 28)) (matMulW N K 1 1 (d * (2 * k)) (t 24)
          (t 26)))).length = lenA N K k d := length_matSubW h20 _
    have e3 : (subRW N K (t 21) (mulRW N K (t 24) (t 27))).length = N * K := length_subRW N K h21 _
    funext i
    fin_cases i <;> simp [mP1, sO1, mP2, mS, aSum, sO2, mM3, sO3, jO, hbs, h13, h14, h5,
      takeD_of_length' e1, takeD_of_length' e2, takeD_of_length' e3, simParts, jointW]
  all_goals first
    | (intro i hi; fin_cases i <;> simp [mP1, sO1, mP2, mS, aSum, sO2, mM3, sO3, jO, hbs] at hi ⊢)
    | (simp [mP1, sO1, mP2, mS, aSum, sO2, mM3, sO3, jO, hbs, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h19, h20, h21, h22, h23, h24, h26, h27, h28, length_matMulW,
        length_matSubW, length_mulRW, length_matAddW]; try ring)

end Prog

end SigabaNeo.Tape
