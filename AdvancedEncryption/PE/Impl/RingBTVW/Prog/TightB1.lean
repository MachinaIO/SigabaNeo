import PE.Impl.RingBTVW.Prog.TightC0
import PE.Impl.RingBTVW.Prog.B1

/-!
# Per-tape bounds of `b1P` (the trapdoor row of `Setup`)

`b1P N K k : XProg 82` builds eight templates, splits its input word, builds the gadget row
(`gadP`), subtracts (`subRWP`), builds one more template, joins (`joinP`) and clears its scratch.
Variables `ρ = [0, G, N, K, k, x₀, x₄, x₉]`: tape `0` at most `x₀`, tape `4` at most `x₄`, tape `9`
at most `x₉` (the split counts along it), every other tape at most
`Tb1 = G + x₀ + x₄ + x₉ + (4kNK + NK + N + K + k + 2kN + 1)`.

**`vb_b1P`**: afterwards tape `0` holds at most `NK + 4kNK` bits (the joined row), tape `9` at most
`x₉`, the cleared scratch nothing, every other tape at most `Tb1`.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg SigabaNeo.Tape.Sym TightP

namespace TightB1

def vx9 : Poly := mo 1 [0, 0, 0, 0, 0, 0, 1]
def p4kNK1 : Poly := [([0, 0, 1, 1], 1), ([0, 0, 1, 1, 1], 4)]

/-- The bound of every tape of `b1P`. -/
def Tb1 : Poly := [([0, 1], 1), ([0, 0, 0, 0, 0, 1], 1), ([0, 0, 0, 0, 0, 0, 1], 1),
  ([0, 0, 0, 0, 0, 0, 0, 1], 1), ([0, 0, 1, 1, 1], 4), ([0, 0, 1, 1], 1), ([0, 0, 1], 1),
  ([0, 0, 0, 1], 1), ([0, 0, 0, 0, 1], 1), ([0, 0, 1, 0, 1], 2), ([], 1)]

def ρ1 (G N K k x0 x4 x9 : ℕ) : List ℕ := [0, G, N, K, k, x0, x4, x9]

def tb1v (G N K k x0 x4 x9 : ℕ) : ℕ :=
  G + x0 + x4 + x9 + (4 * k * (N * K) + N * K + N + K + k + 2 * k * N + 1)

theorem pEval_Tb1 (G N K k x0 x4 x9 : ℕ) :
    pEval (ρ1 G N K k x0 x4 x9) Tb1 = tb1v G N K k x0 x4 x9 := by
  simp [Tb1, pEval, mEval, ρ1, tb1v]; ring

def σ0 : Asg := (List.range 82).map fun j =>
  if j = 0 then vx0 else if j = 4 then vx4 else if j = 9 then vx9 else Tb1

def σ1 : Asg := aSet σ0 2 pK
def σ2 : Asg := aSet σ1 3 pN
def σ3 : Asg := aSet σ2 4 pNK
def σ4 : Asg := aSet σ3 5 pk
def σ5 : Asg := aSet σ4 6 p2kNK
def σ6 : Asg := aSet σ5 14 p2kNK
def σ7 : Asg := aSet σ6 7 p2kN
def σ8 : Asg := aSet σ7 8 p4kNK1

/-- Split, gadget row, subtraction. -/
def aRest1 : XAst (fun _ => True) 82 :=
  .seq (.frame eS (.leaf Prog.splitP Tb1)) <| .seq (.frame eG (.leaf Prog.gadP Tb1))
    (.frame eD (.leaf Prog.subRWP Tb1))

def claim1 : Asg := ((XAst.xabs 8 aRest1 σ8).map Prod.fst).getD []
def cRest1 : Poly := ((XAst.xabs 8 aRest1 σ8).map Prod.snd).getD []

def σ9 : Asg := aSet claim1 58 pNK

def pNK1 : Poly := [([0, 0, 1, 1], 1), ([], 1)]

/-- After the marker. -/
def σ10 : Asg := aSet σ9 58 pNK1

/-- The join, the clears. -/
def aRest2 : XAst (fun _ => True) 82 :=
  .seq (.frame eJ (.leaf Prog.joinP Tb1)) (clearA Tb1 b1Tapes)

def claim : Asg := (List.range 82).map fun j =>
  if j = 0 then p4kNK1 else if j = 9 then vx9 else if j ∈ (b1Tapes.map Fin.val) then [] else Tb1

def cRest2 : Poly := ((XAst.xabs 8 aRest2 σ10).map Prod.snd).getD []

set_option maxRecDepth 100000 in
theorem all_ok : (allLe σ0 Tb1 82 && allLe σ1 Tb1 82 && allLe σ2 Tb1 82 && allLe σ3 Tb1 82 &&
    allLe σ4 Tb1 82 && allLe σ5 Tb1 82 && allLe σ6 Tb1 82 && allLe σ7 Tb1 82 &&
    allLe claim1 Tb1 82 && allLe σ9 Tb1 82) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c10_ok : aGet σ0 10 = Tb1 ∧ aGet σ1 10 = Tb1 ∧ aGet σ2 10 = Tb1 ∧ aGet σ3 10 = Tb1 ∧
    aGet σ4 10 = Tb1 ∧ aGet σ5 10 = Tb1 ∧ aGet σ6 10 = Tb1 ∧ aGet σ7 10 = Tb1 ∧
    aGet claim1 10 = Tb1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem xcheck_rest1 : xcheck 8 aRest1 σ8 claim1 cRest1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem claim1_length : claim1.length = 82 := by decide +kernel

set_option maxRecDepth 100000 in
theorem xcheck_rest2 : xcheck 8 aRest2 σ10 claim cRest2 = true := by decide +kernel

theorem claim_length : claim.length = 82 := by simp [claim]

end TightB1

open TightB1

/-- `(eS; (eG; eD)); R` costs as `eS; (eG; (eD; R))`. -/
theorem VB.assoc3 {k : ℕ} {p q r R : XProg k} {a b : Fin k → ℕ} {T : ℕ}
    (h : VB (seq (seq p (seq q r)) R) a T b) : VB (seq p (seq q (seq r R))) a T b := by
  intro ℓ hℓ
  obtain ⟨h1, h2⟩ := h ℓ hℓ
  refine ⟨le_of_eq_of_le ?_ h1, h2⟩
  simp only [timeBoundT_seq, lenBoundT]
  ring

/-- The marker bit on tape `58`. -/
theorem vb_cons58 (σ : Asg) (ρ : List ℕ) (T q : Poly) (hall : allLe σ T 82 = true)
    (h58 : pEval ρ (aGet σ 58) + 1 ≤ pEval ρ q) :
    VB (prog (.prim (.cons (58 : Fin 82) true))) (bnd ρ σ) (2 * (pEval ρ T + 1) + 3)
      (bnd ρ (aSet σ 58 q)) := by
  refine (VB.prim (.cons (58 : Fin 82) true) (M := pEval ρ T) (fun i => allLe_spec hall ρ i)).mono
    le_rfl le_rfl ?_
  intro i
  simp only [Prim.lenT, Function.update_apply, bnd, aGet_aSet]
  by_cases h1 : i = 58
  · subst h1
    simp only [if_true, show ((58 : Fin 82) : ℕ) = 58 from rfl]
    exact h58
  · have h1' : (i : ℕ) ≠ 58 := fun h => h1 (Fin.ext h)
    simp only [h1, h1', if_false]
    exact le_rfl

/-- The cost of the templates of `b1P`, from tapes below `T`. -/
def natB1 (N K k T : ℕ) : ℕ :=
  (2 * K + 1) * (4 * T + 12) + (2 * N + 1) * (4 * T + 12) + (2 * (N * K) + 1) * (4 * T + 12) +
  (2 * k + 1) * (4 * T + 12) + (2 * (2 * k * (N * K)) + 1) * (4 * T + 12) +
  (2 * (2 * k * (N * K)) + 1) * (4 * T + 12) + (2 * (2 * k * N) + 1) * (4 * T + 12) +
  (2 * (N * K + 4 * k * (N * K)) + 1) * (4 * T + 12) + (2 * (N * K) + 1) * (4 * T + 12) +
  (2 * (T + 1) + 3)

set_option maxHeartbeats 4000000 in
/-- **The per-tape bounds of `b1P`.** -/
theorem vb_b1P (G N K k x0 x4 x9 : ℕ) :
    VB (b1P N K k) (bnd (ρ1 G N K k x0 x4 x9) σ0)
      (natB1 N K k (tb1v G N K k x0 x4 x9) + (pEval (ρ1 G N K k x0 x4 x9) cRest1 +
        pEval (ρ1 G N K k x0 x4 x9) cRest2))
      (bnd (ρ1 G N K k x0 x4 x9) claim) := by
  set ρ := ρ1 G N K k x0 x4 x9 with hρ
  have hT := pEval_Tb1 G N K k x0 x4 x9
  rw [← hρ] at hT
  have hall := all_ok
  simp only [Bool.and_eq_true] at hall
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨a0, a1⟩, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩ := hall
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := c10_ok
  have hrest1 : VB aRest1.toX (bnd ρ σ8) (pEval ρ cRest1) (bnd ρ claim1) := fun ℓ hℓ => by
    have h := bounds_of_xcheck xcheck_rest1 ρ trivial hℓ
    exact ⟨h.2, fun t => h.1 t (by rw [claim1_length]; exact t.isLt)⟩
  have hrest2 : VB aRest2.toX (bnd ρ σ10) (pEval ρ cRest2) (bnd ρ claim) := fun ℓ hℓ => by
    have h := bounds_of_xcheck xcheck_rest2 ρ trivial hℓ
    exact ⟨h.2, fun t => h.1 t (by rw [claim_length]; exact t.isLt)⟩
  have e2kNK : pEval ρ p2kNK = 2 * k * (N * K) := by simp [hρ, ρ1, p2kNK, mo, pEval, mEval]; ring
  have eNK : pEval ρ pNK = N * K := by simp [hρ, ρ1, pNK, mo, pEval, mEval]
  have eK : pEval ρ pK = K := by simp [hρ, ρ1, pK, mo, pEval, mEval]
  have eN : pEval ρ pN = N := by simp [hρ, ρ1, pN, mo, pEval, mEval]
  have ek : pEval ρ pk = k := by simp [hρ, ρ1, pk, mo, pEval, mEval]
  have e2kN : pEval ρ p2kN = 2 * k * N := by simp [hρ, ρ1, p2kN, mo, pEval, mEval]; ring
  have e4 : pEval ρ p4kNK1 = N * K + 4 * k * (N * K) := by
    simp [hρ, ρ1, p4kNK1, pEval, mEval]; ring
  have hle : ∀ x, x ≤ 4 * k * (N * K) + N * K + N + K + k + 2 * k * N + 1 →
      x ≤ pEval ρ Tb1 := fun x hx => by rw [hT]; unfold tb1v; omega
  have hrow : rowL N K k = 2 * k * (N * K) := by unfold rowL; ring
  have h2kN : 1 * (2 * k) * N = 2 * k * N := by ring
  have h1kNK : 1 * (2 * k) * (N * K) = 2 * k * (N * K) := by ring
  have h4 : 2 * k * (N * K) + 2 * k * (N * K) = 4 * k * (N * K) := by ring
  have s1 := vb_natP_bnd (t := 2) (c := 10) (by decide) K ρ σ0 pK Tb1 eK.ge a0 c0 (hle _ (by omega))
  have s2 := vb_natP_bnd (t := 3) (c := 10) (by decide) N ρ σ1 pN Tb1 eN.ge a1 c1 (hle _ (by omega))
  have s3 := vb_natP_bnd (t := 4) (c := 10) (by decide) (N * K) ρ σ2 pNK Tb1 eNK.ge a2 c2
    (hle _ (by omega))
  have s4 := vb_natP_bnd (t := 5) (c := 10) (by decide) k ρ σ3 pk Tb1 ek.ge a3 c3 (hle _ (by omega))
  have s5 := vb_natP_bnd (t := 6) (c := 10) (by decide) (rowL N K k) ρ σ4 p2kNK Tb1
    (by rw [hrow, e2kNK]) a4 c4 (hle _ (by rw [hrow]; omega))
  have s6 := vb_natP_bnd (t := 14) (c := 10) (by decide) (rowL N K k) ρ σ5 p2kNK Tb1
    (by rw [hrow, e2kNK]) a5 c5 (hle _ (by rw [hrow]; omega))
  have s7 := vb_natP_bnd (t := 7) (c := 10) (by decide) (1 * (2 * k) * N) ρ σ6 p2kN Tb1
    (by rw [e2kN, h2kN]) a6 c6 (hle _ (by rw [h2kN]; omega))
  have s8 := vb_natP_bnd (t := 8) (c := 10) (by decide) (N * K + rowL N K k + rowL N K k) ρ σ7
    p4kNK1 Tb1 (by rw [hrow, e4]; omega) a7 c7 (hle _ (by rw [hrow]; omega))
  have s9 := vb_natP_bnd (t := 58) (c := 10) (by decide) (N * K - 1) ρ claim1 pNK Tb1
    (by rw [eNK]; omega) a8 c8 (hle _ (by omega))
  have e1 : pEval ρ pNK1 = N * K + 1 := by simp [hρ, ρ1, pNK1, pEval, mEval]
  have e2 : aGet σ9 58 = pNK := by simp only [σ9, aGet_aSet, if_true]
  have hcons := vb_cons58 σ9 ρ Tb1 pNK1 a9 (by rw [e2, eNK, e1])
  have hR := VB.assoc3 (hrest1.seq (s9.seq (hcons.seq hrest2)))
  have h := s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq hR)))))))
  rw [hT] at h
  refine h.mono le_rfl ?_ le_rfl
  have hm : (2 * (N * K - 1) + 1) * (4 * tb1v G N K k x0 x4 x9 + 12) ≤
      (2 * (N * K) + 1) * (4 * tb1v G N K k x0 x4 x9 + 12) :=
    Nat.mul_le_mul_right _ (by omega)
  unfold natB1
  rw [hrow, h2kN]
  have e8 : N * K + 2 * k * (N * K) + 2 * k * (N * K) = N * K + 4 * k * (N * K) := by ring
  rw [e8]
  omega

end AdvancedEncryption.RingBTVW.Prog
