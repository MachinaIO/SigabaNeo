import PE.Impl.RingBTVW.Prog.KeyTryRealLaw
import PE.Impl.RingBTVW.Algo.DecWords

/-!
# The end of decryption as a tape program

`decFP : Prog 101` computes `decFinW` (`PE.Impl.RingBTVW.Algo.DecWords`): tapes `30 … 35` hold the
words of `c₀`, `k₀`, `c₁`, `k₁`, `k₂`, `κ`, tape `2` the word of `c_f̂`; three dot products
(`matMulP`), two sums (`addRWP`), a difference (`subRWP`), and the centered-abs test of the
constant coefficient (`ballP` on one coefficient, radius on tape `4`) on tape `40` (`run_decFP`).
-/

namespace AdvancedEncryption.RingBTVW.ProgKeyR

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo AdvancedEncryption.RingBTVW.Algo
open scoped SigabaNeo.Tape.Prog

variable {N K k : ℕ}

theorem run_addR {o x y : Fin 101} (hu : Function.Injective (bzR o x y 6 7)) (t : Store 101)
    (ht : Scr t) {K N : ℕ} (hK : (t 6).length = K) (hN : (t 7).length = N)
    (hx : (t x).length = N * K) (hy : (t y).length = N * K) :
    run (map (bzR o x y 6 7) addRWP) t = Function.update t o (addRW N K (t x) (t y)) :=
  run_map_eq_update hu _ t 0 _ (run_addRWP (t ∘ bzR o x y 6 7)
    (fun i hi => plR_scratch ht (by norm_num) 5 le_rfl i hi) hK hN hx hy)

/-- **The end of decryption.** -/
def decFP : Prog 101 :=
  map (mmR 36 30 31 14 16 15 29) matMulP ⨾ map (mmR 37 32 33 14 17 15 29) matMulP ⨾
    map (mmR 38 2 34 14 13 15 29) matMulP ⨾ map (bzR 26 36 37 6 7) addRWP ⨾
    map (bzR 27 26 38 6 7) addRWP ⨾ map (bzR 39 35 27 6 7) subRWP

theorem noGrow_decFP : decFP.NoGrow := by decide

theorem wf_decFP : decFP.WF := wf_of_wfB (by decide)

theorem run_decFP {d : ℕ} (hK0 : 0 < K) (t : Store 101) (hs : Scr t)
    (hK : (t 6).length = K) (hN : (t 7).length = N) (hNK : (t 8).length = N * K)
    (h13 : (t 13).length = 2 * k) (h14 : (t 14).length = 1) (h15 : (t 15).length = 1)
    (h16 : (t 16).length = d) (h17 : (t 17).length = nT k) (h29 : (t 29).length = N * K)
    (h30 : (t 30).length = d * (N * K)) (h31 : (t 31).length = d * (N * K))
    (h32 : (t 32).length = nT k * (N * K)) (h33 : (t 33).length = nT k * (N * K))
    (h2 : (t 2).length = 2 * k * (N * K)) (h34 : (t 34).length = 2 * k * (N * K))
    (h35 : (t 35).length = N * K) :
    ∃ u : Store 101, run decFP t = u ∧
      u 39 = decValW N K d (nT k) k (t 30) (t 31) (t 32) (t 33) (t 2) (t 34) (t 35) ∧
      Scr u ∧ ∀ j : Fin 101, (j.val < 26 ∨ (39 < j.val)) → u j = t j := by
  set A := matMulW N K 1 d 1 (t 30) (t 31)
  set B := matMulW N K 1 (nT k) 1 (t 32) (t 33)
  set C := matMulW N K 1 (2 * k) 1 (t 2) (t 34)
  have hA : A.length = N * K := by simp [A, length_matMulW]
  have hB : B.length = N * K := by simp [B, length_matMulW]
  have hC : C.length = N * K := by simp [C, length_matMulW]
  have upd : ∀ (w : Store 101) (i : Fin 101) (v : List Bool) (j : Fin 101), j ≠ i →
      Function.update w i v j = w j := fun w i v j h => Function.update_of_ne h _ _
  set u1 := Function.update t 36 A with hu1
  have s1 : run (map (mmR 36 30 31 14 16 15 29) matMulP) t = u1 :=
    run_mmR (K := K) (N := N) (m' := 1) (n' := d) (l' := 1) (by decide) t hs hK hN hNK h14 h16 h15
      (by rw [h29]; ring) (by rw [h30]; ring) (by rw [h31]; ring)
  have hs1 : Scr u1 := hs.upd (by decide) _
  set u2 := Function.update u1 37 B with hu2
  have s2 : run (map (mmR 37 32 33 14 17 15 29) matMulP) u1 = u2 := by
    rw [run_mmR (K := K) (N := N) (m' := 1) (n' := nT k) (l' := 1) (by decide) u1 hs1
      (by simp [hu1, hK]) (by simp [hu1, hN]) (by simp [hu1, hNK]) (by simp [hu1, h14])
      (by simp [hu1, h17]) (by simp [hu1, h15]) (by simp [hu1, h29]) (by simp [hu1, h32])
      (by simp [hu1, h33])]
    simp [hu1, hu2, B]
  have hs2 : Scr u2 := hs1.upd (by decide) _
  set u3 := Function.update u2 38 C with hu3
  have s3 : run (map (mmR 38 2 34 14 13 15 29) matMulP) u2 = u3 := by
    rw [run_mmR (K := K) (N := N) (m' := 1) (n' := 2 * k) (l' := 1) (by decide) u2 hs2
      (by simp [hu2, hu1, hK]) (by simp [hu2, hu1, hN]) (by simp [hu2, hu1, hNK])
      (by simp [hu2, hu1, h14]) (by simp [hu2, hu1, h13]) (by simp [hu2, hu1, h15])
      (by simp [hu2, hu1, h29]) (by simp [hu2, hu1, h2]) (by simp [hu2, hu1, h34])]
    simp [hu1, hu2, hu3, C]
  have hs3 : Scr u3 := hs2.upd (by decide) _
  set u4 := Function.update u3 26 (addRW N K A B) with hu4
  have s4 : run (map (bzR 26 36 37 6 7) addRWP) u3 = u4 := by
    rw [run_addR (K := K) (N := N) (by decide) u3 hs3 (by simp [hu3, hu2, hu1, hK])
      (by simp [hu3, hu2, hu1, hN]) (by simp [hu3, hu2, hu1, hA]) (by simp [hu3, hu2, hB])]
    simp [hu1, hu2, hu3, hu4]
  have hs4 : Scr u4 := hs3.upd (by decide) _
  set u5 := Function.update u4 27 (addRW N K (addRW N K A B) C) with hu5
  have s5 : run (map (bzR 27 26 38 6 7) addRWP) u4 = u5 := by
    rw [run_addR (K := K) (N := N) (by decide) u4 hs4 (by simp [hu4, hu3, hu2, hu1, hK])
      (by simp [hu4, hu3, hu2, hu1, hN]) (by simp [hu4, length_addRW, hA]) (by simp [hu4, hu3, hC])]
    simp [hu1, hu2, hu3, hu4, hu5]
  have hs5 : Scr u5 := hs4.upd (by decide) _
  set V := decValW N K d (nT k) k (t 30) (t 31) (t 32) (t 33) (t 2) (t 34) (t 35) with hV
  have hVe : V = subRW N K (t 35) (addRW N K (addRW N K A B) C) := by
    rw [hV, decValW, ProgKey.dotW_eq_matMulW, ProgKey.dotW_eq_matMulW, ProgKey.dotW_eq_matMulW]
  set u6 := Function.update u5 39 V with hu6
  have s6 : run (map (bzR 39 35 27 6 7) subRWP) u5 = u6 := by
    rw [run_bzR (K := K) (N := N) (L := 1) (by decide) u5 hs5
      (by simp [hu5, hu4, hu3, hu2, hu1, hK]) (by simp [hu5, hu4, hu3, hu2, hu1, hN])
      (by simp [hu5, hu4, hu3, hu2, hu1, h35]) (by simp [hu5, length_addRW, hA])]
    simp only [hu6, hVe, matSubW_eq_subRW, Nat.one_mul]
    simp [hu1, hu2, hu3, hu4, hu5]
  have hs6 : Scr u6 := hs5.upd (by decide) _
  refine ⟨u6, ?_, by simp [hu6], hs6, fun j hj => ?_⟩
  · simp only [decFP, run_seq]; rw [s1, s2, s3, s4, s5, s6]
  · have ne : ∀ i : Fin 101, 26 ≤ i.val → i.val ≤ 39 → j ≠ i := fun i h1 h2 e => by
      rw [e] at hj; omega
    rw [hu6, upd _ _ _ _ (ne 39 (by decide) (by decide)), hu5, upd _ _ _ _ (ne 27 (by decide) (by decide)),
      hu4, upd _ _ _ _ (ne 26 (by decide) (by decide)), hu3, upd _ _ _ _ (ne 38 (by decide) (by decide)),
      hu2, upd _ _ _ _ (ne 37 (by decide) (by decide)), hu1, upd _ _ _ _ (ne 36 (by decide) (by decide))]

end AdvancedEncryption.RingBTVW.ProgKeyR
