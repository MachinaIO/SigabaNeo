import PE.Impl.ExpLUT.Prog.KeyTimeLoad
/-! Binary ring operations and canonicalization with nonblank bounded scratch. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog
open SigabaNeo.Tape.Sym Prog.SpecT Prog.MersenneT

/-- First five operation tapes have structured bounds; scratch is bounded by M. -/
def ringArea {n : ℕ} (M N K out : ℕ) (j : Fin n) : ℕ :=
  if j.val = 0 then out else if j.val = 1 ∨ j.val = 2 then N * K
  else if j.val = 3 then K else if j.val = 4 then N else M

theorem check_add37 : check 8 Op.add.prog (σRing ++ List.replicate 32 pTop) σRing' wAddRM = true := by
  decide +kernel

theorem check_sub37 : check 8 Op.sub.prog (σRing ++ List.replicate 32 pTop) σRing' wAddRM = true := by
  decide +kernel

/-- A checked ring primitive on the full 37-tape operation layout. -/
theorem ring37_cert (p : Tape.Prog 37) (w : Poly)
    (hc : check 8 p (σRing ++ List.replicate 32 pTop) σRing' w = true)
    (M N K : ℕ) (a : Fin 37 → ℕ) (hM : ∀ j, a j ≤ M)
    (h1 : a 1 ≤ N * K) (h2 : a 2 ≤ N * K) (h3 : a 3 ≤ K) (h4 : a 4 ≤ N) :
    Cert (.prog p) a (ringArea M N K (N * K))
      ((2 * M + 3) * pEval [M, N, K] w) := by
  have hi : a ≤ bnd [M, N, K] (σRing ++ List.replicate 32 pTop) := by
    intro j
    fin_cases j <;> simp [bnd, aGet, σRing, pTop, pNK, pK, pN, mo, pEval, mEval,
      hM, h1, h2, h3, h4]
  have ho : ∀ j : Fin 37,
      (if j.val < σRing'.length then pEval [M, N, K] (aGet σRing' j.val)
        else top [M, N, K]) ≤ ringArea M N K (N * K) j := by
    intro j
    fin_cases j <;> simp [ringArea, σRing', aGet, pNK, pK, pN, mo, pEval, mEval, top]
  exact checked_local hc [M, N, K] a _ hi hM ho

/-- The canonicalizer uses 28 tapes with the same first-five template layout. -/
theorem canon28_cert (M N K : ℕ) (a : Fin 28 → ℕ) (hM : ∀ j, a j ≤ M)
    (h1 : a 1 ≤ N * K) (h2 : a 2 ≤ N * K) (h3 : a 3 ≤ K) (h4 : a 4 ≤ N) :
    Cert (.prog canonRP) a (ringArea M N K (N * K))
      ((2 * M + 3) * (7 + 44 * N + 40 * (N * K))) := by
  have hi : a ≤ bnd [M, N, K] (σRing ++ List.replicate 23 pTop) := by
    intro j
    fin_cases j <;> simp [bnd, aGet, σRing, pTop, pNK, pK, pN, mo, pEval, mEval,
      hM, h1, h2, h3, h4]
  have ho : ∀ j : Fin 28,
      (if j.val < σRing'.length then pEval [M, N, K] (aGet σRing' j.val)
        else top [M, N, K]) ≤ ringArea M N K (N * K) j := by
    intro j
    fin_cases j <;> simp [ringArea, σRing', aGet, pNK, pK, pN, mo, pEval, mEval, top]
  have h := checked_local RingVM.checkT_canonRP [M, N, K] a _ hi hM ho
  simpa [RingVM.wCanon, pEval, mEval, top, Nat.mul_assoc, Nat.add_assoc] using h

def binaryPoly (o : Op) : Poly := if o = .mul then wMulRM else wAddRM

/-- Binary arithmetic in the exact MVM operation frame. -/
theorem binaryOp_cert (o : Op) (ho : o = .add ∨ o = .sub ∨ o = .mul)
    (M N K : ℕ) (a : Fin 105 → ℕ) (hM : ∀ j, a j ≤ M)
    (h1 : a 33 ≤ N * K) (h2 : a 34 ≤ N * K) (h3 : a 35 ≤ K) (h4 : a 36 ≤ N) :
    let e := mkE (fOp 34) (fOp_inj 34 (Or.inl rfl))
    Cert (.frame e (.prog o.prog)) a (embedF e a (ringArea M N K (N * K)))
      ((2 * M + 3) * pEval [M, N, K] (binaryPoly o)) := by
  dsimp only
  let e := mkE (fOp 34) (fOp_inj 34 (Or.inl rfl))
  have hc : check 8 o.prog (σRing ++ List.replicate 32 pTop) σRing' (binaryPoly o) = true := by
    rcases ho with rfl | rfl | rfl
    · exact check_add37
    · exact check_sub37
    · exact RingVM.checkT_mulRMP
  exact (ring37_cert o.prog (binaryPoly o) hc M N K (a ∘ e)
    (fun j ↦ hM _) h1 h2 h3 h4).frame e

/-- Canonicalization swaps the operation words and reads the fixed all-ones template. -/
theorem canon_cert (M N K : ℕ) (a : Fin 105 → ℕ) (hM : ∀ j, a j ≤ M)
    (h1 : a 32 ≤ N * K) (h2 : a 38 ≤ N * K) (h3 : a 35 ≤ K) (h4 : a 36 ≤ N) :
    let e := mkE fCan fCan_inj
    Cert (.frame e (.prog canonRP)) a (embedF e a (ringArea M N K (N * K)))
      ((2 * M + 3) * (7 + 44 * N + 40 * (N * K))) := by
  dsimp only
  let e := mkE fCan fCan_inj
  exact (canon28_cert M N K (a ∘ e) (fun j ↦ hM _) h1 h2 h3 h4).frame e

end AdvancedEncryption.ExpLUT.Prog.KeyTime
