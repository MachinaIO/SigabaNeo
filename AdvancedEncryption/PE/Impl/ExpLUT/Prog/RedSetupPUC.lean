import PE.Impl.ExpLUT.Prog.SetupConf

/-!
# The canonical uniform sampler appended to a non-blank output tape (package G2, `setupP`)

`vb_unifCanonP` (`Prog/SetupTime`) bounds `unifCanonP N K n` from a blank output tape. Inside the
reduction's setup component the sampler appends to the word already on tape `0`, so here the same
bound with tape `0` at most the scratch bound `S` (`check_ucTail'`: the certificate of the tail
with tape `0` at the top, a tape the tail never touches):

* **`vb_unifCanonP'`**: from tape `1` blank and every other tape at most `S`, the sampler costs
  `ucT' N K n S` and ends with tape `0` at most `S + n N K`, tape `1` blank, the others at most
  `S + K + n N K`.
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg SigabaNeo.Tape.Sym
open AdvancedEncryption.RingBTVW.Prog

/-- The tapes before the tail, tape `0` at the top. -/
def σuc' : Asg := [pTop, pLKv] ++ List.replicate 5 pTop ++ [pKv, pLv] ++ List.replicate 31 pTop

/-- The tapes after the tail, tape `0` at the top. -/
def claimUc' : Asg :=
  [pTop, [], pTop, pTop, pTop, pTop, pTop, [], [], [], [], [], pTop, pTop, pTop, pLv,
    pAdd pTop pKv] ++ List.replicate 16 pTop ++ [pLKv]

set_option maxRecDepth 100000 in
theorem check_ucTail' : check 8 ucTail σuc' claimUc' wUc = true := by decide +kernel

/-- Before the sampler: tape `1` blank, the others at most `S`. -/
def ucIn' (S : ℕ) : Fin 40 → ℕ := fun j => if j.val = 1 then 0 else S

/-- After the sampler. -/
def ucOut' (S K m : ℕ) : Fin 40 → ℕ :=
  fun j => if j.val = 0 then S + m else if j.val = 1 then 0 else S + K + m

/-- The time of `n` canonical uniform words appended to a tape of at most `S` bits. -/
def ucT' (N K n S : ℕ) : ℕ :=
  countT (n * (N * K)) 1 0 tCoin 0 S + ((2 * K + 1) * (4 * S + 12) +
    ((2 * (n * N) + 1) * (4 * S + 12) + ((2 * S + 3) * (12 + 19 * (n * N) + 18 * (n * N * K)) +
      appT' (S + K + n * (N * K)) (n * (N * K)))))

set_option maxHeartbeats 4000000 in
/-- **The canonical uniform sampler appended to a non-blank tape `0`.** -/
theorem vb_unifCanonP' (N K n S : ℕ) (hS : n * (N * K) ≤ S) (hK : K ≤ S) (hL : n * N ≤ S)
    (h1 : 1 ≤ S) :
    VB (unifCanonP N K n) (ucIn' S) (ucT' N K n S) (ucOut' S K (n * (N * K))) := by
  set m := n * (N * K) with hm
  set L := n * N with hLdef
  have hmL : m = L * K := by rw [hm, hLdef]; ring
  -- the fair bits
  let v1 : Fin 40 → ℕ := fun j => if j.val = 1 then m else S
  have s1 : VB (frame eU (coinsF m)) (ucIn' S) (countT m 1 0 tCoin 0 S) v1 := by
    refine vb_smp eU (atbb_coinsF m) (x := 0) (S := S) ?_ ?_ ?_ ?_ ?_ ?_
    · show ucIn' S 1 ≤ 0; simp [ucIn']
    · intro j _; simp only [ucIn']; split_ifs <;> omega
    · show max 1 m ≤ S; omega
    · show 0 + m * 1 ≤ v1 1; simp [v1]
    · intro j hj
      show S + m * 0 ≤ v1 (eU j)
      fin_cases j <;> simp_all [v1, eU]
    · intro t; simp only [ucIn', v1]; split_ifs <;> omega
  -- the templates
  have s2 := VB.natP (t := (7 : Fin 40)) (c := 34) (by decide) K (a := v1) (M := S)
    (fun i => by simp only [v1]; split_ifs <;> omega) hK
  have s3 := VB.natP (t := (8 : Fin 40)) (c := 34) (by decide) L (a := natB 7 34 K v1) (M := S)
    (fun i => by simp only [natB, v1]; split_ifs <;> omega) hL
  let v2 : Fin 40 → ℕ := fun j => if j.val = 1 then m else
    if j.val = 7 then K else if j.val = 8 then L else S
  have e23 : natB 8 34 L (natB 7 34 K v1) ≤ v2 := by
    intro j
    simp only [natB, v1, v2]
    split_ifs <;> simp_all <;> omega
  -- the tail
  let v3 : Fin 40 → ℕ := fun j => if j.val = 0 then S else if j.val = 1 then 0 else
    if j.val = 33 then m else S + K
  have s4 : VB (prog ucTail) v2 ((2 * S + 3) * (12 + 19 * L + 18 * (L * K))) v3 := by
    have h := VB.checkMap check_ucTail' (ucVars S L K) (u := id) Function.injective_id (a := v2)
      (b := v3) ?_ ?_ ?_ ?_ ?_
    · rw [Prog.map_id] at h
      refine h.mono le_rfl (le_of_eq ?_) le_rfl
      simp [wUc, ucVars, pEval, mEval, top]; ring
    · intro j
      fin_cases j <;> simp [v2, σuc', aGet, pEval, mEval, ucVars, pTop, pLv, pKv, pLKv, hmL]
    · intro t
      show v2 t ≤ S
      simp only [v2]; split_ifs <;> omega
    · intro j hj
      fin_cases j <;> simp_all [v3, claimUc', aGet, pEval, mEval, ucVars, pTop, pLv, pKv, pLKv] <;> omega
    · intro j hj
      have hl : claimUc'.length = 34 := rfl
      rw [hl] at hj
      show S ≤ v3 j
      simp only [v3]; split_ifs <;> omega
    · intro t ht; exact absurd rfl (ht t)
  -- the append
  have s5 := vb_appendTapeP (r := (0 : Fin 40)) (a := 33) (S := 35) (c := 36) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) v3 (M := S + K + m)
    (fun t => by simp only [v3]; split_ifs <;> omega) (by simp [v3])
  have e5 : appOut (0 : Fin 40) 33 35 36 v3 ≤ ucOut' S K m := by
    intro j
    simp only [appOut, Function.update_apply, ucOut', v3]
    split_ifs <;> simp_all
  have hv33 : v3 33 = m := by simp [v3]
  rw [hv33] at s5
  have := s1.seq (s2.seq ((s3.mono le_rfl le_rfl e23).seq (s4.seq (s5.mono le_rfl le_rfl e5))))
  refine this.mono le_rfl (le_of_eq ?_) le_rfl
  unfold ucT'
  rw [← hm, ← hLdef]

end AdvancedEncryption.ExpLUT.Prog
