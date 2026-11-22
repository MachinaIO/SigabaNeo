import PE.Impl.DualUse.Prog.KeyTryReal
import PE.Impl.DualUse.Prog.KeyP

/-!
# The law of one try of `KeyGen` with the real trapdoor, as a tape program

`keyTryRCoinsP : Prog 101` draws `m` fair coins on tape `3` (template `25`), runs `keyTryRP`, and
blanks the coins.

* `law_keyTryRCoinsP`: its law is the image of `uniformList m` under
  `l ↦ Function.update s 0 (keyTryRW … l)`;
* `law_keyTryRCoinsP_keyM`: on the words of a master secret key (public key on `1`, `e` on `90`,
  `t` on `91`) and of the key row `B_f̂` of a window predicate `C` (tape `2`), for a configuration
  meeting `KeyCfg.Valid`, the law is the image of `keyM msk C` under the update of the output tape
  by the word of the key;
* `timeBound_keyTryRCoinsP`: `23 (L + 1)² + tbC · (2L + 1)^tbD` on words at most `L` long.
-/

namespace AdvancedEncryption.DualUse.ProgKeyR

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo AdvancedEncryption.DualUse.Algo AdvancedEncryption.DualUse.ProgKey Matrix
  Cslib AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
  AdvancedEncryption.PE.Gates.DateWindow
open scoped SigabaNeo.Tape.Prog

variable {N K k : ℕ}

/-- **One try with the real trapdoor from fresh coins.** -/
def keyTryRCoinsP : Prog 101 := coinsAt 3 25 41 42 ⨾ (keyTryRP ⨾ clr 3)

theorem noGrow_keyTryRP : keyTryRP.NoGrow := by decide

theorem wf_keyTryRP : keyTryRP.WF := wf_of_wfB (by decide)

theorem wf_keyTryRCoinsP : keyTryRCoinsP.WF :=
  ⟨wf_coinsAt _ _ _ _ (by decide) (by decide), wf_keyTryRP, trivial⟩

theorem law_keyTryRCoinsP {d B P m : ℕ} (hK0 : 0 < K) (s : Store 101)
    (hs : ∀ j : Fin 101, 26 ≤ j.val → j.val < 90 → s j = [])
    (hw : ∀ j : Fin 101, 94 ≤ j.val → j.val < 100 → s j = []) (h3 : s 3 = [])
    (hpk : (s 1).length = P) (hsz : d * (N * K) + nT k * (N * K) ≤ P)
    (hbf : (s 2).length = 2 * k * (N * K)) (hS : (s 4).length = K)
    (hc : s 5 = powW K (B - 1)) (hK : (s 6).length = K) (hN : (s 7).length = N)
    (hNK : (s 8).length = N * K) (hB : (s 9).length = B) (hn : (s 10).length = (d + nT k) * N)
    (hnK : (s 11).length = (d + nT k) * N * K) (hk : (s 12).length = k)
    (h13 : (s 13).length = 2 * k) (h14 : (s 14).length = 1) (h15 : (s 15).length = 1)
    (h16 : (s 16).length = d) (h17 : (s 17).length = nT k) (h18 : (s 18).length = d * (N * K))
    (h19 : (s 19).length = nT k * (N * K)) (h20 : (s 20).length = 2 * k * (N * K))
    (h21 : (s 21).length = d * N) (h22 : (s 22).length = P - N * K) (h23 : (s 23).length = P)
    (h24 : (s 24).length = P + (d + nT k) * N * K + 2 * k * (N * K)) (h25 : (s 25).length = m)
    (he : (s 90).length = 2 * k * (N * K)) (htt : (s 91).length = N * K)
    (h92 : (s 92).length = 2 * k * N) (h93 : (s 93).length = 2 * k * (2 * k * (N * K)))
    (h100 : (s 100).length = 2 * k) :
    law keyTryRCoinsP s = (BitString.uniformList m).map
      (fun l => Function.update s 0 (keyTryRW N K k d B (s 4) (s 1) (s 90) (s 91) (s 2) l)) := by
  rw [keyTryRCoinsP, law_seq_noGrow _ _ (by decide) s,
    law_coinsAt (by decide) (by decide) (by decide) (by decide) (by decide) s
      (hs 41 (by decide) (by decide)) (hs 42 (by decide) (by decide)), h25, PMF.map_comp]
  congr 1
  funext l
  simp only [Function.comp_apply, run_seq, run_clear]
  have hne : ∀ j : Fin 101, j ≠ 3 → Function.update s 3 l j = s j := fun j hj =>
    Function.update_of_ne hj _ _
  rw [run_keyTryRP (N := N) (K := K) (k := k) (d := d) (B := B) (P := P) hK0 _
    (fun j h1 h2 => by rw [hne j (by rintro rfl; simp at h1)]; exact hs j h1 h2)
    (fun j h1 h2 => by rw [hne j (by rintro rfl; simp at h1)]; exact hw j h1 h2)
    (by rw [hne 1 (by decide), hpk]) hsz (by rw [hne 2 (by decide), hbf])
    (by rw [hne 4 (by decide), hS]) (by rw [hne 5 (by decide), hc]) (by rw [hne 6 (by decide), hK])
    (by rw [hne 7 (by decide), hN]) (by rw [hne 8 (by decide), hNK]) (by rw [hne 9 (by decide), hB])
    (by rw [hne 10 (by decide), hn]) (by rw [hne 11 (by decide), hnK])
    (by rw [hne 12 (by decide), hk]) (by rw [hne 13 (by decide), h13])
    (by rw [hne 14 (by decide), h14]) (by rw [hne 15 (by decide), h15])
    (by rw [hne 16 (by decide), h16]) (by rw [hne 17 (by decide), h17])
    (by rw [hne 18 (by decide), h18]) (by rw [hne 19 (by decide), h19])
    (by rw [hne 20 (by decide), h20]) (by rw [hne 21 (by decide), h21])
    (by rw [hne 22 (by decide), h22]) (by rw [hne 23 (by decide), h23])
    (by rw [hne 24 (by decide), h24]) (by rw [hne 90 (by decide), he])
    (by rw [hne 91 (by decide), htt]) (by rw [hne 92 (by decide), h92])
    (by rw [hne 93 (by decide), h93]) (by rw [hne 100 (by decide), h100])]
  rw [hne 4 (by decide), hne 1 (by decide), hne 2 (by decide), hne 90 (by decide),
    hne 91 (by decide), Function.update_self]
  funext j
  simp only [Function.update_apply]
  by_cases hj3 : j = 3
  · subst hj3; simp [h3]
  · simp [hj3]

/-- **Time bound** of the whole program on words at most `L` long. -/
theorem timeBound_keyTryRCoinsP (L : ℕ) :
    timeBound keyTryRCoinsP L ≤
      23 * (L + 1) ^ 2 + tbC (keyTryRP ⨾ clr 3) * (2 * L + 1) ^ tbD (keyTryRP ⨾ clr 3) := by
  have hng : (keyTryRP ⨾ clr 3).NoGrow := by decide
  show timeBound (coinsAt 3 25 41 42) L +
      timeBound (keyTryRP ⨾ clr 3) (lenBound (coinsAt 3 25 41 42) L) ≤ _
  have h1 := timeBound_coinsAt_le (3 : Fin 101) 25 41 42 L
  have h2 := timeBound_le _ hng (lenBound (coinsAt (3 : Fin 101) 25 41 42) L)
  have h3 : (lenBound (coinsAt (3 : Fin 101) 25 41 42) L + 1) ^ tbD (keyTryRP ⨾ clr 3) ≤
      (2 * L + 1) ^ tbD (keyTryRP ⨾ clr 3) :=
    Nat.pow_le_pow_left (by have := lenBound_coinsAt_le (3 : Fin 101) 25 41 42 L; omega) _
  have h4 := Nat.mul_le_mul_left (tbC (keyTryRP ⨾ clr 3)) h3
  omega

theorem lenBound_keyTryRCoinsP_le (L : ℕ) : lenBound keyTryRCoinsP L ≤ 2 * L := by
  have hng : (keyTryRP ⨾ clr 3).NoGrow := by decide
  show lenBound (keyTryRP ⨾ clr 3) (lenBound (coinsAt 3 25 41 42) L) ≤ _
  rw [lenBound_eq _ hng]
  exact lenBound_coinsAt_le _ _ _ _ L

theorem tbC_keyTryR : tbC (keyTryRP ⨾ clr 3) = 11494 := by decide +kernel
theorem tbD_keyTryR : tbD (keyTryRP ⨾ clr 3) = 8 := by decide +kernel

/-! ### The law of `KeyGen` -/

open AdvancedEncryption.DualUse.Prog in
/-- **The program has the law of `KeyGen`**: on the words of the public key (tape `1`), of `e`
(`90`) and `t` (`91`) of a master secret key and of the key row `B_f̂` of a window predicate `C`
(tape `2`), the law of `keyTryRCoinsP` is the image of `keyM msk C` under the update of the output
tape by the word of the key. -/
theorem law_keyTryRCoinsP_keyM (hk : 2 ^ K < 2 ^ k) {c : DualUse.Conf N K k} (cf : KeyCfg)
    (hcf : cf.Valid hk c) (msk : DualUse.SKey hk c) (C : List Bool)
    (hC : ∃ w : Window, winWord w = C) (s : Store 101)
    (hs : ∀ j : Fin 101, 26 ≤ j.val → j.val < 90 → s j = [])
    (hw : ∀ j : Fin 101, 94 ≤ j.val → j.val < 100 → s j = []) (h3 : s 3 = [])
    (h1 : s 1 = (DualUse.pkEnc hk c).enc msk.1)
    (h2 : s 2 = rowW N K k (DualUse.keyMatrix msk.1 (DualUse.predC C)))
    (h4 : s 4 = cf.sW) (h90 : s 90 = rowW N K k msk.2.1) (h91 : s 91 = (ringEnc N K).enc msk.2.2)
    (hc : s 5 = powW K (cf.B - 1)) (hK : (s 6).length = K) (hN : (s 7).length = N)
    (hNK : (s 8).length = N * K) (hB : (s 9).length = cf.B)
    (hn : (s 10).length = (c.d + nT k) * N) (hnK : (s 11).length = (c.d + nT k) * N * K)
    (hk' : (s 12).length = k) (h13 : (s 13).length = 2 * k) (h14 : (s 14).length = 1)
    (h15 : (s 15).length = 1) (h16 : (s 16).length = c.d) (h17 : (s 17).length = nT k)
    (h18 : (s 18).length = c.d * (N * K)) (h19 : (s 19).length = nT k * (N * K))
    (h20 : (s 20).length = 2 * k * (N * K)) (h21 : (s 21).length = c.d * N)
    (h22 : (s 22).length = lenPK hk c - N * K) (h23 : (s 23).length = lenPK hk c)
    (h24 : (s 24).length = lenPK hk c + (c.d + nT k) * N * K + 2 * k * (N * K))
    (h25 : (s 25).length = cf.m)
    (h92 : (s 92).length = 2 * k * N) (h93 : (s 93).length = 2 * k * (2 * k * (N * K)))
    (h100 : (s 100).length = 2 * k) :
    law keyTryRCoinsP s =
      (DualUse.keyM hk c msk C).map (fun sk => Function.update s 0 ((DualUse.skEnc hk c).enc sk)) := by
  have hpk : (s 1).length = lenPK hk c := by rw [h1]; exact length_enc_fixLen _ _
  have hsz : c.d * (N * K) + nT k * (N * K) ≤ lenPK hk c := by
    rw [← hpk, h1]; exact pk_size hk c msk.1
  rw [law_keyTryRCoinsP (N := N) (K := K) (k := k) (d := c.d) (B := cf.B) (P := lenPK hk c)
    (m := cf.m) hcf.hK0 s hs hw h3 hpk hsz (by rw [h2]; exact Algo.length_rowW _)
    (by rw [h4, hcf.hsl]) hc hK hN hNK hB hn hnK hk' h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23
    h24 h25 (by rw [h90]; exact Algo.length_rowW _) (by rw [h91]; exact (ringEnc N K).length _)
    h92 h93 h100,
    keyM_coinsE hk c cf.B hcf.hB cf.m hcf.hm hcf.hBig msk C, PMF.map_comp]
  congr 1
  funext l
  simp only [Function.comp_apply]
  congr 1
  rw [keyTryRW_eq_core _ _ _ _ _ _ (by rw [h91]; exact (ringEnc N K).length _),
    ← keyTryMskW_eq hk hcf.h0 c cf.B hcf.hB cf.m hcf.hm hcf.hsl rfl hcf.hSmall hcf.hdec msk C true
      (by simp [hC]) _ h2 l]
  obtain ⟨e1, e2, e3⟩ := AdvancedEncryption.DualUse.Algo.split3 ((DualUse.pkEnc hk c).enc msk.1) (rowW N K k msk.2.1)
    ((ringEnc N K).enc msk.2.2) (Algo.length_rowW _) ((ringEnc N K).length _)
  unfold keyTryMskW
  rw [mskEnc_eq, e1, e2, e3, h1, h4, h90, h91, h2]

end AdvancedEncryption.DualUse.ProgKeyR
