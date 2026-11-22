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
  AdvancedEncryption.DualUse.Algo Cslib AdvancedEncryption.PE.DateWindow
open scoped SigabaNeo.Tape.Prog

/-- **One try with the simulated trapdoor from fresh coins.** -/
def keyTrySimCoinsP : Prog 90 := coinsAt 3 25 41 42 ⨾ (keyTrySimP ⨾ clr 3)

theorem noGrow_keyTrySimP : keyTrySimP.NoGrow := by decide

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

end AdvancedEncryption.DualUse.ProgKey
