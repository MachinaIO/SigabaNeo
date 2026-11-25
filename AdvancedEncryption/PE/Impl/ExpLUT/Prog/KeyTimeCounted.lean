import PE.Impl.ExpLUT.Prog.KeyTimeInvariant
/-! Count-dependent arithmetic on the actual 37-tape MVM operation layout. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog
open SigabaNeo.Tape.Sym Prog.SpecT Prog.MersenneT

def countedPoly : Op → Poly
  | .neg => wNotM
  | .aut => wAut
  | .rho => wRhoJ
  | .rot => wRotB
  | .dig => RingVM.wDigitM
  | _ => []

theorem check_counted37 (o : Op) (ho : o.bin = false) :
    check 8 o.prog (σJ ++ List.replicate 32 pTop) σJ' (countedPoly o) = true := by
  cases o <;> first | contradiction | decide +kernel

def countedArea (M N K count : ℕ) (j : Fin 37) : ℕ :=
  if j.val = 0 ∨ j.val = 1 then N * K else if j.val = 2 then count
  else if j.val = 3 then K else if j.val = 4 then N else M

/-- The counter is preserved; its length is charged as a polynomial variable. -/
theorem counted37_cert (o : Op) (ho : o.bin = false) (M N K count : ℕ)
    (a : Fin 37 → ℕ) (hM : ∀ j, a j ≤ M) (h1 : a 1 ≤ N * K)
    (h2 : a 2 ≤ count) (h3 : a 3 ≤ K) (h4 : a 4 ≤ N) :
    Cert (.prog o.prog) a (countedArea M N K count)
      ((2 * M + 3) * pEval [M, N, K, count] (countedPoly o)) := by
  have hi : a ≤ bnd [M, N, K, count] (σJ ++ List.replicate 32 pTop) := by
    intro j
    fin_cases j <;> simp [bnd, aGet, σJ, pTop, pNK, pm, pK, pN, mo, pEval, mEval,
      hM, h1, h2, h3, h4]
  have hout : ∀ j : Fin 37,
      (if j.val < σJ'.length then pEval [M, N, K, count] (aGet σJ' j.val)
        else top [M, N, K, count]) ≤ countedArea M N K count j := by
    intro j
    fin_cases j <;> simp [countedArea, σJ', aGet, pNK, pm, pK, pN, mo, pEval, mEval, top]
  exact checked_local (check_counted37 o ho) [M, N, K, count] a _ hi hM hout

def countedFrame (c : Fin 64) : Fin 37 ↪ Fin 105 :=
  mkE (fOp (41 + c.val)) (fOp_inj _ (Or.inr ⟨by omega, by have := c.isLt; omega⟩))

/-- Counted arithmetic reads the register directly, rather than its NK-bit loaded copy. -/
theorem countedOp_cert (o : Op) (ho : o.bin = false) (c : Fin 64)
    (M N K count : ℕ) (a : Fin 105 → ℕ) (hM : ∀ j, a j ≤ M)
    (h1 : a 33 ≤ N * K) (h2 : a (tR c) ≤ count) (h3 : a 35 ≤ K) (h4 : a 36 ≤ N) :
    Cert (.frame (countedFrame c) (.prog o.prog)) a
      (embedF (countedFrame c) a (countedArea M N K count))
      ((2 * M + 3) * pEval [M, N, K, count] (countedPoly o)) := by
  have hc : countedFrame c 2 = tR c := by
    apply Fin.ext
    change (41 + c.val) % 105 = 41 + c.val
    apply Nat.mod_eq_of_lt
    have := c.isLt
    omega
  apply Cert.frame
  apply counted37_cert o ho M N K count (a ∘ countedFrame c) (fun j ↦ hM (countedFrame c j)) h1 _ h3 h4
  simpa only [Function.comp_apply, hc] using h2

def countedAfter (M N K count : ℕ) (c : Fin 64) (a : Fin 105 → ℕ) : Fin 105 → ℕ :=
  embedF (countedFrame c) a (countedArea M N K count)

theorem countedArea_bound (M N K count : ℕ) (hNK : N * K ≤ M) (hN : N ≤ M)
    (hK : K ≤ M) (hc : count ≤ M) : ∀ j, countedArea M N K count j ≤ M := by
  intro j
  simp only [countedArea]
  split_ifs <;> omega

theorem countedAfter_fields (M N K count : ℕ) (c : Fin 64) (a : Fin 105 → ℕ) :
    countedAfter M N K count c a 32 = N * K ∧ countedAfter M N K count c a 35 = K ∧
    countedAfter M N K count c a 36 = N ∧ countedAfter M N K count c a 38 = a 38 := by
  refine ⟨embedF_apply_self (countedFrame c) a (countedArea M N K count) 0,
    embedF_apply_self (countedFrame c) a (countedArea M N K count) 3,
    embedF_apply_self (countedFrame c) a (countedArea M N K count) 4, ?_⟩
  apply embed_outside
  intro j hj
  have he := congrArg Fin.val hj
  change (if j.val = 0 then 32 else if j.val = 1 then 33
    else if j.val = 2 then (41 + c.val) % 105 else if j.val = 3 then 35
    else if j.val = 4 then 36 else j.val - 5) = 38 at he
  have hc := c.isLt
  have hjlt := j.isLt
  rw [Nat.mod_eq_of_lt (by omega : 41 + c.val < 105)] at he
  split_ifs at he <;> omega

def countedResult (M N K count : ℕ) (d c : Fin 64) (a : Fin 105 → ℕ) : Fin 105 → ℕ :=
  embedF (mkE (fOut d) (fOut_inj d))
    (canonicalAfter M N K (countedAfter M N K count c
      (Function.update (Function.update a 33 (N * K)) 34 (N * K))))
    (fun j ↦ if j = 0 then N * K else 0)

def countedTime (M N K count : ℕ) (o : Op) : ℕ :=
  (2 * M + 3) * (2 * (30 + 10 * (N * K)) + pEval [M, N, K, count] (countedPoly o) +
    (7 + 44 * N + 40 * (N * K)) + 20)

/-- The complete actual counted instruction, charging its real counter length. -/
theorem compile_counted_cert (o : Op) (ho : o.bin = false)
    (d s c : Fin 64) (M N K : ℕ) (a : Fin 105 → ℕ)
    (hM : ∀ j, a j ≤ M) (hNK : N * K ≤ M) (hN : N ≤ M) (hK : K ≤ M)
    (hk : a 35 ≤ K) (hn : a 36 ≤ N) (hz : a 37 = N * K) (hones : a 38 ≤ N * K)
    (h32 : a 32 = 0) (h39 : a 39 = 0) (h40 : a 40 = 0) :
    Cert (MVM.compile (.op o d s c)) a (countedResult M N K (a (tR c)) d c a)
      (countedTime M N K (a (tR c)) o) := by
  let a1 := Function.update a (33 : Fin 105) (N * K)
  let a2 := Function.update a1 (34 : Fin 105) (N * K)
  have hM1 : ∀ j, a1 j ≤ M := by
    intro j
    simp only [a1, Function.update_apply]
    split_ifs <;> first | exact hNK | exact hM j
  have hM2 : ∀ j, a2 j ≤ M := by
    intro j
    simp only [a2, Function.update_apply]
    split_ifs <;> first | exact hNK | exact hM1 j
  have hload1 := load_cert N K M 33 (Or.inl rfl) s a hM hz h32 h39 h40
  have hload2 := load_cert N K M 34 (Or.inr rfl) c a1 hM1
    (by simpa [a1] using hz) (by simpa [a1] using h32)
    (by simpa [a1] using h39) (by simpa [a1] using h40)
  have hc33 : tR c ≠ 33 := by intro he; have hv := congrArg Fin.val he; simp only [tR_val] at hv; omega
  have hc34 : tR c ≠ 34 := by intro he; have hv := congrArg Fin.val he; simp only [tR_val] at hv; omega
  have hop := countedOp_cert o ho c M N K (a (tR c)) a2 hM2 (by simp [a2, a1])
    (by simp [a2, a1, hc33, hc34]) (by simpa [a2, a1] using hk) (by simpa [a2, a1] using hn)
  have hbM := embed_bound (countedFrame c) a2 (countedArea M N K (a (tR c))) M hM2
    (countedArea_bound M N K _ hNK hN hK (hM _))
  obtain ⟨hb0, hb3, hb4, hb38⟩ := countedAfter_fields M N K (a (tR c)) c a2
  have hcan := canon_cert M N K (countedAfter M N K (a (tR c)) c a2) hbM hb0.le
    (by rw [hb38]; simpa [a2, a1] using hones) hb3.le hb4.le
  have hcM := embed_bound canonicalFrame (countedAfter M N K (a (tR c)) c a2)
    (ringArea M N K (N * K)) M hbM (ringArea_bound M N K hNK hN hK)
  have hout := store_cert N K M d (canonicalAfter M N K (countedAfter M N K (a (tR c)) c a2)) hcM
    (canonicalAfter_result M N K _).le
  have h := hload1.seq (hload2.seq (hop.seq (hcan.seq hout)))
  have he : (2 * M + 3) * (30 + 10 * (N * K)) +
      ((2 * M + 3) * (30 + 10 * (N * K)) +
      ((2 * M + 3) * pEval [M, N, K, a (tR c)] (countedPoly o) +
      ((2 * M + 3) * (7 + 44 * N + 40 * (N * K)) + (2 * M + 3) * 20))) =
        countedTime M N K (a (tR c)) o := by unfold countedTime; ring
  rw [he] at h
  simpa only [MVM.compile, t2Of, ho, Bool.false_eq_true, ↓reduceIte, countedResult, a1, a2,
    countedAfter, canonicalAfter, countedFrame, canonicalFrame] using h

end AdvancedEncryption.ExpLUT.Prog.KeyTime
