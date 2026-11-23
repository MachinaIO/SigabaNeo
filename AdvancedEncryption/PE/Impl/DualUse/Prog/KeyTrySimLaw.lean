import PE.Impl.DualUse.Prog.KeyTrySim

/-!
# The law of the simulated key oracle, as a tape program

`keyTrySimCoinsP : Prog 90` draws `m` fair coins on tape `3` (`coinsAt`, template `25` of length
`m`), runs `keyTrySimP`, and blanks the coins.

* `law_keyTrySimCoinsP`: its law is the image of `uniformList m` under
  `l ↦ Function.update s 0 (keyTrySimW N K k d B sW pk W_f l)`.
* `law_keyTrySimCoinsP_KGsim`: on the words of a public key and of `W_f = simW sd C`, for a window
  predicate `C` of at most `c.L` bits, the law of the program is the image of the law of the
  simulated key oracle `KGsim sd C` under `w ↦ Function.update s 0 w`.
-/

namespace AdvancedEncryption.DualUse.ProgKey

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Lattices.Algo
  AdvancedEncryption.DualUse.Algo Cslib AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
  AdvancedEncryption.PE.Gates AdvancedEncryption.PE.Gates.BPWord
open scoped SigabaNeo.Tape.Prog

/-- **One try with the simulated trapdoor from fresh coins.** -/
def keyTrySimCoinsP : Prog 90 := coinsAt 3 25 41 42 ⨾ (keyTrySimP ⨾ clr 3)

theorem noGrow_keyTrySimP : keyTrySimP.NoGrow := by decide

theorem wf_keyTrySimP : keyTrySimP.WF := wf_of_wfB (by decide)

theorem wf_keyTrySimCoinsP : keyTrySimCoinsP.WF :=
  ⟨wf_coinsAt _ _ _ _ (by decide) (by decide), wf_keyTrySimP, trivial⟩

theorem law_keyTrySimCoinsP {N K k d B P m : ℕ} (hK0 : 0 < K) (s : Store 90)
    (hs : ∀ j : Fin 90, 26 ≤ j.val → s j = []) (h3 : s 3 = [])
    (hpk : (s 1).length = P) (hsz : d * (N * K) + nT k * (N * K) ≤ P)
    (hwf : (s 2).length = d * (2 * k) * (N * K)) (hS : (s 4).length = K)
    (hc : s 5 = powW K (B - 1)) (hK : (s 6).length = K) (hN : (s 7).length = N)
    (hNK : (s 8).length = N * K) (hB : (s 9).length = B) (hn : (s 10).length = (d + nT k) * N)
    (hnK : (s 11).length = (d + nT k) * N * K) (hk : (s 12).length = k)
    (h13 : (s 13).length = 2 * k) (h14 : (s 14).length = 1) (h15 : (s 15).length = 1)
    (h16 : (s 16).length = d) (h17 : (s 17).length = nT k) (h18 : (s 18).length = d * (N * K))
    (h19 : (s 19).length = nT k * (N * K)) (h20 : (s 20).length = 2 * k * (N * K))
    (h21 : (s 21).length = d * N) (h22 : (s 22).length = P - N * K) (h23 : (s 23).length = P)
    (h24 : (s 24).length = P + (d + nT k) * N * K + 2 * k * (N * K)) (h25 : (s 25).length = m) :
    law keyTrySimCoinsP s = (BitString.uniformList m).map
      (fun l => Function.update s 0 (keyTrySimW N K k d B (s 4) (s 1) (s 2) l)) := by
  rw [keyTrySimCoinsP, law_seq_noGrow _ _ (by decide) s,
    law_coinsAt (by decide) (by decide) (by decide) (by decide) (by decide) s (hs 41 (by decide))
      (hs 42 (by decide)), h25, PMF.map_comp]
  congr 1
  funext l
  simp only [Function.comp_apply, run_seq, run_clear]
  have hne : ∀ j : Fin 90, j ≠ 3 → Function.update s 3 l j = s j := fun j hj =>
    Function.update_of_ne hj _ _
  rw [run_keyTrySimP (N := N) (K := K) (k := k) (d := d) (B := B) (P := P) hK0 _
    (fun j hj => by rw [hne j (by rintro rfl; simp at hj)]; exact hs j hj)
    (by rw [hne 1 (by decide), hpk]) hsz (by rw [hne 2 (by decide), hwf])
    (by rw [hne 4 (by decide), hS]) (by rw [hne 5 (by decide), hc]) (by rw [hne 6 (by decide), hK])
    (by rw [hne 7 (by decide), hN]) (by rw [hne 8 (by decide), hNK]) (by rw [hne 9 (by decide), hB])
    (by rw [hne 10 (by decide), hn]) (by rw [hne 11 (by decide), hnK])
    (by rw [hne 12 (by decide), hk]) (by rw [hne 13 (by decide), h13])
    (by rw [hne 14 (by decide), h14]) (by rw [hne 15 (by decide), h15])
    (by rw [hne 16 (by decide), h16]) (by rw [hne 17 (by decide), h17])
    (by rw [hne 18 (by decide), h18]) (by rw [hne 19 (by decide), h19])
    (by rw [hne 20 (by decide), h20]) (by rw [hne 21 (by decide), h21])
    (by rw [hne 22 (by decide), h22]) (by rw [hne 23 (by decide), h23])
    (by rw [hne 24 (by decide), h24])]
  rw [hne 4 (by decide), hne 1 (by decide), hne 2 (by decide), Function.update_self]
  funext j
  simp only [Function.update_apply]
  by_cases hj3 : j = 3
  · subst hj3; simp [h3]
  · simp [hj3]

/-- **Time bound** of the whole program on words at most `L` long: the coin loop, then the
deterministic part on words at most `2L` long, with the syntactic constants `tbC`, `tbD` of
`keyTrySimP ⨾ clr 3` (`timeBound_le`). -/
theorem timeBound_keyTrySimCoinsP (L : ℕ) :
    timeBound keyTrySimCoinsP L ≤
      23 * (L + 1) ^ 2 + tbC (keyTrySimP ⨾ clr 3) * (2 * L + 1) ^ tbD (keyTrySimP ⨾ clr 3) := by
  have hng : (keyTrySimP ⨾ clr 3).NoGrow := by decide
  show timeBound (coinsAt 3 25 41 42) L +
      timeBound (keyTrySimP ⨾ clr 3) (lenBound (coinsAt 3 25 41 42) L) ≤ _
  have h1 := timeBound_coinsAt_le (3 : Fin 90) 25 41 42 L
  have h2 := timeBound_le _ hng (lenBound (coinsAt (3 : Fin 90) 25 41 42) L)
  have h3 : (lenBound (coinsAt (3 : Fin 90) 25 41 42) L + 1) ^ tbD (keyTrySimP ⨾ clr 3) ≤
      (2 * L + 1) ^ tbD (keyTrySimP ⨾ clr 3) :=
    Nat.pow_le_pow_left (by have := lenBound_coinsAt_le (3 : Fin 90) 25 41 42 L; omega) _
  have h4 := Nat.mul_le_mul_left (tbC (keyTrySimP ⨾ clr 3)) h3
  omega

/-- The length bound of the whole program: `2L` (the coins), then unchanged. -/
theorem lenBound_keyTrySimCoinsP_le (L : ℕ) : lenBound keyTrySimCoinsP L ≤ 2 * L := by
  have hng : (keyTrySimP ⨾ clr 3).NoGrow := by decide
  show lenBound (keyTrySimP ⨾ clr 3) (lenBound (coinsAt 3 25 41 42) L) ≤ _
  rw [lenBound_eq _ hng]
  exact lenBound_coinsAt_le _ _ _ _ L

/-- The first two blocks of a public key fit in its word. -/
theorem pk_size {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : DualUse.Conf N K k) (mpk : DualUse.PK hk c) :
    c.d * (N * K) + nT k * (N * K) ≤ ((DualUse.pkEnc hk c).enc mpk).length := by
  obtain ⟨_, g2, _⟩ := pkEnc_blocks hk c mpk
  have hv : (vecW N K (mpk.B₁ 0)).length = nT k * (N * K) := by rw [length_vecW, len_trapCol]
  have l1 := congrArg List.length g2
  rw [hv, List.length_take, List.length_drop] at l1
  generalize ((DualUse.pkEnc hk c).enc mpk).length = P at l1 ⊢
  have : 1 ≤ nT k := by simp [nT]
  rcases Nat.eq_zero_or_pos (N * K) with h | h
  · rw [h]; simp
  · have : N * K ≤ nT k * (N * K) := Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- **The program has the law of the simulated key oracle**: for a window predicate `C` of at most
`c.L` bits, on the word of the public key of `sd` (tape `1`) and the word of `W_f = simW sd C`
(tape `2`), the law of `keyTrySimCoinsP` is the image of `KGsim sd C` under the update of the
output tape. -/
theorem law_keyTrySimCoinsP_KGsim {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (h0 : 0 < k) (hK0 : 0 < K)
    {c : DualUse.Conf N K k} (B : ℕ) (hB : 2 ^ B ≤ 2 ^ K) (m : ℕ)
    (hm : nCoef c.d (DualUse.TrapCol k) N * B = m)
    (hBig : c.Big =
      Finset.univ.map (keyEmbE (d := c.d) (Wt := DualUse.TrapCol k) (N := N) B hB m hm))
    {S : ℕ} {sW : List Bool} (hsl : sW.length = K) (hSv : val sW = S)
    (hSmall : c.Small = DualUse.keyBall (2 ^ K) c.d (DualUse.TrapCol k) N S)
    (hdec : c.dec = decG hk h0) (sd : DualUse.SimData hk c) (C : List Bool) (hL : C.length ≤ c.L)
    (hC : ValidC C) {P : ℕ} (s : Store 90)
    (hs : ∀ j : Fin 90, 26 ≤ j.val → s j = []) (h3 : s 3 = [])
    (h1 : s 1 = (DualUse.pkEnc hk c).enc sd.mpk) (h2 : s 2 = colsW N K k c.d (DualUse.simW sd C))
    (h4 : s 4 = sW) (hpk : (s 1).length = P)
    (hc : s 5 = powW K (B - 1)) (hK : (s 6).length = K) (hN : (s 7).length = N)
    (hNK : (s 8).length = N * K) (hB' : (s 9).length = B) (hn : (s 10).length = (c.d + nT k) * N)
    (hnK : (s 11).length = (c.d + nT k) * N * K) (hk' : (s 12).length = k)
    (h13 : (s 13).length = 2 * k) (h14 : (s 14).length = 1) (h15 : (s 15).length = 1)
    (h16 : (s 16).length = c.d) (h17 : (s 17).length = nT k)
    (h18 : (s 18).length = c.d * (N * K)) (h19 : (s 19).length = nT k * (N * K))
    (h20 : (s 20).length = 2 * k * (N * K)) (h21 : (s 21).length = c.d * N)
    (h22 : (s 22).length = P - N * K) (h23 : (s 23).length = P)
    (h24 : (s 24).length = P + (c.d + nT k) * N * K + 2 * k * (N * K)) (h25 : (s 25).length = m) :
    law keyTrySimCoinsP s = (DualUse.KGsim sd C).map (fun w => Function.update s 0 w) := by
  have hsz : c.d * (N * K) + nT k * (N * K) ≤ P := by
    rw [← hpk, h1]; exact pk_size hk c sd.mpk
  have hwf : (s 2).length = c.d * (2 * k) * (N * K) := by rw [h2, colsW, length_matW]
  rw [law_keyTrySimCoinsP (N := N) (K := K) (k := k) (d := c.d) (B := B) (P := P) (m := m) hK0 s hs
    h3 hpk hsz hwf (by rw [h4, hsl]) hc hK hN hNK hB' hn hnK hk' h13 h14 h15 h16 h17 h18 h19 h20 h21
    h22 h23 h24 h25, KGsim_words hk h0 B hB m hm hBig hsl hSv hSmall hdec sd C hL hC, PMF.map_comp]
  congr 1
  funext l
  simp only [Function.comp_apply, h1, h2, h4]

end AdvancedEncryption.DualUse.ProgKey
