import PE.Impl.DualUse.Prog.TightApp
import PE.Impl.DualUse.Prog.C0
import SigabaNeo.Lib.Machines.Prog.XAbs

/-!
# Per-tape bounds of `c0P` (the row `c₀ = t a + e` of `Setup`)

`c0P 0 (2k NK) (2k) N K : XProg 82` builds twelve templates (`natP`), splits its input word, multiplies
(`matMulP`), adds (`addRWP`), copies the sum to tape `0` and clears its scratch. Its per-tape bounds
are certified on symbolic sizes (`SigabaNeo.Lib.Machines.Prog.XAbs`), with the variables

  `ρ = [0, G, N, K, k, x₀, x₄]`

(`0` unused): tape `0` holds at most `x₀` bits, tape `4` at most `x₄`, every other tape at most
`Tb = G + x₀ + x₄ + (2kNK + NK + N + K + 2k + 2kN + 1)` (the bulk `G` plus all template lengths).

* the templates: `vb_natP_bnd` (each `natP`, uniform bound `Tb`, the template set exactly);
* the rest (splits, product, sum, copy, clears): one certificate `xcheck_c0Rest` (`decide +kernel`);
* **`vb_c0P`**: afterwards tape `0` holds at most `2kNK` bits, tape `4` at most `x₄`, the cleared
  scratch nothing, every other tape at most `Tb`; the cost is `natC0 + pEval ρ cC0`, every loop
  charged its own template.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg SigabaNeo.Tape.Sym

namespace TightP

/-! ### Symbolic sizes: `ρ = [0, G, N, K, k, x₀, x₄]` -/

/-- The monomial `c · G^a N^b K^c k^d x₀^e x₄^f` (exponents `e`). -/
def mo (c : ℕ) (e : List ℕ) : Poly := [(0 :: e, c)]

def vG : Poly := mo 1 [1]
def pN : Poly := mo 1 [0, 1]
def pK : Poly := mo 1 [0, 0, 1]
def pk : Poly := mo 1 [0, 0, 0, 1]
def pNK : Poly := mo 1 [0, 1, 1]
def p2kNK : Poly := mo 2 [0, 1, 1, 1]
def p2k : Poly := mo 2 [0, 0, 0, 1]
def p2kN : Poly := mo 2 [0, 1, 0, 1]
def vx0 : Poly := mo 1 [0, 0, 0, 0, 1]
def vx4 : Poly := mo 1 [0, 0, 0, 0, 0, 1]

/-- The bound of every tape: the bulk, the two tracked tapes and all template lengths. -/
def Tb : Poly := [([0, 1], 1), ([0, 0, 0, 0, 0, 1], 1), ([0, 0, 0, 0, 0, 0, 1], 1),
  ([0, 0, 1, 1, 1], 2), ([0, 0, 1, 1], 1), ([0, 0, 0, 1], 1), ([0, 0, 1], 1), ([0, 0, 0, 0, 1], 2),
  ([0, 0, 1, 0, 1], 2), ([], 1)]

/-- The values of the variables. -/
def ρv (G N K k x0 x4 : ℕ) : List ℕ := [0, G, N, K, k, x0, x4]

/-- The value of `Tb`. -/
def tbv (G N K k x0 x4 : ℕ) : ℕ :=
  G + x0 + x4 + (2 * k * (N * K) + N * K + N + K + 2 * k + 2 * k * N + 1)

theorem pEval_Tb (G N K k x0 x4 : ℕ) : pEval (ρv G N K k x0 x4) Tb = tbv G N K k x0 x4 := by
  simp [Tb, pEval, mEval, ρv, tbv]; ring

/-- Clearing a list of tapes, annotated. -/
def clearA {H : List ℕ → Prop} {n : ℕ} [NeZero n] (T : Poly) : List (Fin n) → XAst H n
  | [] => .leaf (.prim (.copy 0 0)) T
  | t :: l => .seq (.leaf (.prim (.clear t)) T) (clearA T l)

theorem toX_clearA {H : List ℕ → Prop} {n : ℕ} [NeZero n] (T : Poly) :
    ∀ l : List (Fin n), (clearA (H := H) T l).toX = clearL l
  | [] => rfl
  | t :: l => by rw [clearA, XAst.toX, toX_clearA T l]; rfl

/-! ### Templates -/

/-- **A template on symbolic sizes**: `natP t c n` sets tape `t` to `n ≤ pEval p` bits; the scratch
`c` is at the uniform bound `T`. -/
theorem vb_natP_bnd {m : ℕ} {t c : Fin m} (hct : c ≠ t) (n : ℕ) (ρ : List ℕ) (σ : Asg)
    (p T : Poly) (hp : n ≤ pEval ρ p) (hall : allLe σ T m = true) (hc : aGet σ c.val = T)
    (hn : n ≤ pEval ρ T) :
    VB (natP t c n) (bnd ρ σ) ((2 * n + 1) * (4 * pEval ρ T + 12)) (bnd ρ (aSet σ t.val p)) := by
  refine (VB.natP hct n (M := pEval ρ T) (fun i => allLe_spec hall ρ i) hn).mono le_rfl le_rfl ?_
  intro i
  rw [bnd_aSet]
  simp only [natB, Function.update_apply]
  split_ifs with h1 h2
  · exact hp
  · subst h2; simp only [bnd, hc]; omega
  · exact le_rfl

end TightP

open TightP

/-! ### `c0P` -/

namespace TightC0

/-- The bounds at entry: `x₀` on tape `0`, `x₄` on tape `4`, `Tb` elsewhere. -/
def σ0 : Asg := (List.range 82).map fun j => if j = 0 then vx0 else if j = 4 then vx4 else Tb

def σ1 : Asg := aSet σ0 2 []
def σ2 : Asg := aSet σ1 3 p2kNK
def σ3 : Asg := aSet σ2 5 p2kNK
def σ4 : Asg := aSet σ3 6 pNK
def σ5 : Asg := aSet σ4 7 p2kNK
def σ6 : Asg := aSet σ5 8 pK
def σ7 : Asg := aSet σ6 9 pN
def σ8 : Asg := aSet σ7 11 (pC 1)
def σ9 : Asg := aSet σ8 12 (pC 1)
def σ10 : Asg := aSet σ9 13 p2k
def σ11 : Asg := aSet σ10 14 p2kNK
def σ12 : Asg := aSet σ11 15 p2kN

set_option maxRecDepth 100000 in
theorem all_ok : (allLe σ0 Tb 82 && allLe σ1 Tb 82 && allLe σ2 Tb 82 && allLe σ3 Tb 82 &&
    allLe σ4 Tb 82 && allLe σ5 Tb 82 && allLe σ6 Tb 82 && allLe σ7 Tb 82 && allLe σ8 Tb 82 &&
    allLe σ9 Tb 82 && allLe σ10 Tb 82 && allLe σ11 Tb 82) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c10_ok : aGet σ0 10 = Tb ∧ aGet σ1 10 = Tb ∧ aGet σ2 10 = Tb ∧ aGet σ3 10 = Tb ∧
    aGet σ4 10 = Tb ∧ aGet σ5 10 = Tb ∧ aGet σ6 10 = Tb ∧ aGet σ7 10 = Tb ∧ aGet σ8 10 = Tb ∧
    aGet σ9 10 = Tb ∧ aGet σ10 10 = Tb ∧ aGet σ11 10 = Tb := by decide +kernel

/-- Splits, product, sum, copy, clears. -/
def aRest : XAst (fun _ => True) 82 :=
  .seq (.frame eS1 (.leaf Prog.splitP Tb)) <| .seq (.frame eS2 (.leaf Prog.splitP Tb)) <|
  .seq (.frame eM (.leaf Prog.matMulP Tb)) <| .seq (.frame eA (.leaf Prog.addRWP Tb)) <|
  .seq (.leaf (.prim (.copy 0 75)) Tb) (clearA Tb c0Tapes)

/-- The claimed bounds afterwards: the row on tape `0`, `x₄` on tape `4`, the cleared scratch
blank, `Tb` elsewhere. -/
def claim : Asg := (List.range 82).map fun j =>
  if j = 0 then p2kNK else if j = 4 then vx4 else if j ∈ (c0Tapes.map Fin.val) then [] else Tb

/-- The steps of the rest, found by the interpreter. -/
def cRest : Poly := ((XAst.xabs 8 aRest σ12).map Prod.snd).getD []

set_option maxRecDepth 100000 in
theorem xcheck_rest : xcheck 8 aRest σ12 claim cRest = true := by decide +kernel

theorem claim_length : claim.length = 82 := by simp [claim]

end TightC0

open TightC0

/-- The cost of the templates of `c0P`, from tapes below `T`. -/
def natC0 (N K k T : ℕ) : ℕ :=
  (2 * 0 + 1) * (4 * T + 12) + (2 * (2 * k * (N * K)) + 1) * (4 * T + 12) +
  (2 * (2 * k * (N * K)) + 1) * (4 * T + 12) + (2 * (N * K) + 1) * (4 * T + 12) +
  (2 * (2 * k * (N * K)) + 1) * (4 * T + 12) + (2 * K + 1) * (4 * T + 12) +
  (2 * N + 1) * (4 * T + 12) + (2 * 1 + 1) * (4 * T + 12) + (2 * 1 + 1) * (4 * T + 12) +
  (2 * (2 * k) + 1) * (4 * T + 12) + (2 * (1 * (2 * k) * (N * K)) + 1) * (4 * T + 12) +
  (2 * (1 * (2 * k) * N) + 1) * (4 * T + 12)

set_option maxHeartbeats 4000000 in
/-- **The per-tape bounds of `c0P`.** -/
theorem vb_c0P (G N K k x0 x4 : ℕ) :
    VB (c0P 0 (2 * k * (N * K)) (2 * k) N K) (bnd (ρv G N K k x0 x4) σ0)
      (natC0 N K k (tbv G N K k x0 x4) + pEval (ρv G N K k x0 x4) cRest)
      (bnd (ρv G N K k x0 x4) claim) := by
  set ρ := ρv G N K k x0 x4 with hρ
  have hT := pEval_Tb G N K k x0 x4
  rw [← hρ] at hT
  have hall := all_ok
  simp only [Bool.and_eq_true] at hall
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a0, a1⟩, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩ := hall
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ := c10_ok
  have hrest : VB aRest.toX (bnd ρ σ12) (pEval ρ cRest) (bnd ρ claim) := fun ℓ hℓ => by
    have h := bounds_of_xcheck xcheck_rest ρ trivial hℓ
    refine ⟨h.2, fun t => ?_⟩
    exact h.1 t (by rw [claim_length]; exact t.isLt)
  have ev : ∀ p : Poly, pEval ρ p = pEval (ρv G N K k x0 x4) p := fun _ => rfl
  have e2kNK : pEval ρ p2kNK = 2 * k * (N * K) := by simp [hρ, ρv, p2kNK, mo, pEval, mEval]; ring
  have eNK : pEval ρ pNK = N * K := by simp [hρ, ρv, pNK, mo, pEval, mEval]
  have eK : pEval ρ pK = K := by simp [hρ, ρv, pK, mo, pEval, mEval]
  have eN : pEval ρ pN = N := by simp [hρ, ρv, pN, mo, pEval, mEval]
  have e2k : pEval ρ p2k = 2 * k := by simp [hρ, ρv, p2k, mo, pEval, mEval]
  have e2kN : pEval ρ p2kN = 2 * k * N := by simp [hρ, ρv, p2kN, mo, pEval, mEval]; ring
  have hle : ∀ x, x ≤ 2 * k * (N * K) + N * K + N + K + 2 * k + 2 * k * N + 1 →
      x ≤ pEval ρ Tb := fun x hx => by rw [hT]; unfold tbv; omega
  have s1 := vb_natP_bnd (t := 2) (c := 10) (by decide) 0 ρ σ0 [] Tb (by simp) a0 c0 (hle _ (by omega))
  have s2 := vb_natP_bnd (t := 3) (c := 10) (by decide) (2 * k * (N * K)) ρ σ1 p2kNK Tb
    e2kNK.ge a1 c1 (hle _ (by omega))
  have s3 := vb_natP_bnd (t := 5) (c := 10) (by decide) (2 * k * (N * K)) ρ σ2 p2kNK Tb
    e2kNK.ge a2 c2 (hle _ (by omega))
  have s4 := vb_natP_bnd (t := 6) (c := 10) (by decide) (N * K) ρ σ3 pNK Tb
    eNK.ge a3 c3 (hle _ (by omega))
  have s5 := vb_natP_bnd (t := 7) (c := 10) (by decide) (2 * k * (N * K)) ρ σ4 p2kNK Tb
    e2kNK.ge a4 c4 (hle _ (by omega))
  have s6 := vb_natP_bnd (t := 8) (c := 10) (by decide) K ρ σ5 pK Tb eK.ge a5 c5 (hle _ (by omega))
  have s7 := vb_natP_bnd (t := 9) (c := 10) (by decide) N ρ σ6 pN Tb eN.ge a6 c6 (hle _ (by omega))
  have s8 := vb_natP_bnd (t := 11) (c := 10) (by decide) 1 ρ σ7 (pC 1) Tb (by simp) a7 c7
    (hle _ (by omega))
  have s9 := vb_natP_bnd (t := 12) (c := 10) (by decide) 1 ρ σ8 (pC 1) Tb (by simp) a8 c8
    (hle _ (by omega))
  have s10 := vb_natP_bnd (t := 13) (c := 10) (by decide) (2 * k) ρ σ9 p2k Tb e2k.ge a9 c9
    (hle _ (by omega))
  have s11 := vb_natP_bnd (t := 14) (c := 10) (by decide) (1 * (2 * k) * (N * K)) ρ σ10 p2kNK Tb
    (by rw [e2kNK]; ring_nf; omega) a10 c10 (hle _ (by nlinarith))
  have s12 := vb_natP_bnd (t := 15) (c := 10) (by decide) (1 * (2 * k) * N) ρ σ11 p2kN Tb
    (by rw [e2kN]; ring_nf; omega) a11 c11 (hle _ (by nlinarith))
  have h := s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq
    (s11.seq (s12.seq hrest)))))))))))
  rw [hT] at h
  refine h.mono le_rfl (le_of_eq ?_) le_rfl
  unfold natC0
  ring

end AdvancedEncryption.DualUse.Prog
