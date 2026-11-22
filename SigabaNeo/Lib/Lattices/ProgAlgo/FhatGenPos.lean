import SigabaNeo.Lib.Lattices.ProgAlgo.FhatGenCompile
import SigabaNeo.Lib.Lattices.ProgAlgo.KeySum
import SigabaNeo.Lib.Lattices.ProgAlgo.MatAdd

/-!
# Generating gate tapes: the positions of the output wires

`posBody`: for the bit `(c, i, j)` (registers `47 48 49`), fetch the position of the wire of the
output representation (list `23`, index `(c N + j) k + i`), fix it against the threshold `58`
(positions not below it are read as `1`), append it to the list `19`. `iter_posBody`: the loop over
all `(c, i, j)` (odometer `odoC`) collects the positions in the order of `posW`.
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Lattices

namespace FhatGen

open SigabaNeo.Tape SigabaNeo.Tape.RegVM SLP Algo

variable {E : Env}

/-- One bit `(c, i, j)` of the output. -/
def posBody : Code :=
  .seq (.mov 50 47) (.seq (maddC 50 5 49 53) (.seq (maddC 50 2 48 53) (.seq (fetchC 51 23 50 20)
    (.seq (.ifLt 51 58 .skip (.mov 51 0)) (.lpush 19 51)))))

/-- The fixed position of the bit `(c, i, j)` of a list `R`. -/
def pfix (n thr : ℕ) (N k : ℕ) (R : List ℕ) (c i j : ℕ) : ℕ :=
  if R.getD ((c * N + j) * k + i) 0 < thr then R.getD ((c * N + j) * k + i) 0 else n

theorem exec_posBody {N k : ℕ} (hk : 0 < k) (hN : 0 < N) (σ : St) (c i j : ℕ) (R : List ℕ) (thr : ℕ) (h2 : σ.sc 2 = k)
    (h5 : σ.sc 5 = N) (h0 : σ.sc 0 = E.n) (h47 : σ.sc 47 = c) (h48 : σ.sc 48 = i)
    (h49 : σ.sc 49 = j) (h58 : σ.sc 58 = thr) (h23 : σ.ls 23 = R)
    (hM : (c * N + j) * k + i ≤ E.M) (hR : ∀ x ∈ R, x ≤ E.M) (hnM : E.n ≤ E.M)
    (hC : (σ.ls 19).length < E.C) :
    ∃ sc' ls', exec E posBody σ = setSL σ sc' ls' ∧
      ls' 19 = σ.ls 19 ++ [pfix E.n thr N k R c i j] ∧
      (∀ r : SR, r.val < 41 ∨ (41 < r.val ∧ r.val < 50) ∨ 53 < r.val → sc' r = σ.sc r) ∧
      ∀ l : LR, l ≠ 19 → l ≠ 20 → ls' l = σ.ls l := by
  have b1 : c * N + j ≤ (c * N + j) * k + i :=
    le_trans (Nat.le_mul_of_pos_right _ hk) (Nat.le_add_right _ _)
  have b0 : c ≤ c * N + j := le_trans (Nat.le_mul_of_pos_right _ hN) (Nat.le_add_right _ _)
  set s1 := setSL σ (Function.update σ.sc 50 c) σ.ls
  have e1 : exec E (.mov 50 47) σ = s1 := by simp [exec, s1, setSL, h47]
  have q2 := exec_maddC (E := E) 50 5 49 53 (by decide) (by decide) (by decide) (by decide)
    (by decide) s1 (by simp [s1, setSL, h5, h49]; nlinarith)
  set s2 := setSL s1 (Function.update (Function.update s1.sc 53 (s1.sc 50)) 50
    (s1.sc 50 * s1.sc 5 + s1.sc 49)) s1.ls
  have q3 := exec_maddC (E := E) 50 2 48 53 (by decide) (by decide) (by decide) (by decide)
    (by decide) s2 (by simp [s2, s1, setSL, h5, h49, h2, h48, Function.update_apply]; nlinarith)
  set s3 := setSL s2 (Function.update (Function.update s2.sc 53 (s2.sc 50)) 50
    (s2.sc 50 * s2.sc 2 + s2.sc 48)) s2.ls
  have h50 : s3.sc 50 = (c * N + j) * k + i := by
    simp [s3, s2, s1, setSL, h5, h49, h2, h48, Function.update_apply]
  have hs3 : ∀ r : SR, r ≠ 50 → r ≠ 53 → s3.sc r = σ.sc r := fun r a b => by
    simp [s3, s2, s1, setSL, Function.update_of_ne a, Function.update_of_ne b]
  have hl3 : s3.ls = σ.ls := rfl
  obtain ⟨sc4, e4, d4, f4⟩ := exec_fetchC (E := E) 51 23 50 20 s3
  set x := R.getD ((c * N + j) * k + i) 0
  have hx : sc4 51 = x := by rw [d4, hl3, h23, h50]
  set s4 := setSL s3 sc4 (Function.update s3.ls 20 (((s3.ls 23).drop (s3.sc 50)).tail))
  have hs4 : ∀ r : SR, r ≠ 41 → r ≠ 51 → sc4 r = s3.sc r := fun r a b =>
    f4 r (by simp [a, b])
  set s5 := setSL s4 (Function.update sc4 51 (pfix E.n thr N k R c i j)) s4.ls
  have e5 : exec E (.ifLt 51 58 .skip (.mov 51 0)) s4 = s5 := by
    have h58' : sc4 58 = thr := by
      rw [hs4 58 (by decide) (by decide), hs3 58 (by decide) (by decide), h58]
    have h0' : sc4 0 = E.n := by
      rw [hs4 0 (by decide) (by decide), hs3 0 (by decide) (by decide), h0]
    simp only [exec_ifLt, s4, setSL, hx, h58', s5, pfix]
    split_ifs with h
    · simp only [exec]; congr 1; funext r; by_cases hr : r = 51
      · subst hr; simp [hx, x, List.getD_eq_getElem?_getD]
      · simp [Function.update_of_ne hr]
    · simp [exec, h0']
  have hv : pfix E.n thr N k R c i j ≤ E.M := by
    unfold pfix; split_ifs
    · rcases Nat.lt_or_ge ((c * N + j) * k + i) R.length with h | h
      · exact hR _ (by rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h)
      · rw [List.getD_eq_default _ _ h]; omega
    · exact hnM
  have e6 := exec_lpush_lt s5 19 51 (by simp [s5, s4, s3, s2, s1, setSL]; exact hC)
    (by simp [s5, setSL]; exact hv)
  refine ⟨s5.sc, Function.update s5.ls 19 (s5.ls 19 ++ [s5.sc 51]), ?_, ?_, fun r hr => ?_,
    fun l a b => ?_⟩
  · rw [posBody, exec_seq, e1, exec_seq, q2, exec_seq, q3, exec_seq, e4, exec_seq, e5, e6]; rfl
  · simp [s5, s4, s3, s2, s1, setSL]
  · simp only [s5, setSL]
    rw [Function.update_of_ne (by rintro rfl; revert hr; decide),
      hs4 r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide),
      hs3 r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)]
  · simp [s5, s4, s3, s2, s1, setSL, Function.update_of_ne a, Function.update_of_ne b]

/-- The value at the index `x` of the loop. -/
def pAt (n thr N k : ℕ) (R : List ℕ) (x : ℕ) : ℕ := pfix n thr N k R (x / N / k) (x / N % k) (x % N)

theorem pAt_idx {n thr N k : ℕ} (R : List ℕ) {c i j : ℕ} (hi : i < k) (hj : j < N) :
    pAt n thr N k R ((c * k + i) * N + j) = pfix n thr N k R c i j := by
  have e1 : ((c * k + i) * N + j) / N = c * k + i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : ((c * k + i) * N + j) % N = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have e3 : (c * k + i) / k = c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi, Nat.zero_add]
  have e4 : (c * k + i) % k = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  simp only [pAt, e1, e2, e3, e4]

/-- The registers the position loop relies on. -/
def PQ (N k thr : ℕ) (R : List ℕ) (σ : St) : Prop :=
  σ.sc 2 = k ∧ σ.sc 5 = N ∧ σ.sc 0 = E.n ∧ σ.sc 58 = thr ∧ σ.ls 23 = R

theorem pos_bounds {N k : ℕ} (hk : 0 < k) (hN : 0 < N) :
    2 * k ≤ 4 * k * N * k ∧ N ≤ 4 * k * N * k ∧ 2 * k * k * N ≤ 4 * k * N * k := by
  have h1 : 1 ≤ N * k := Nat.mul_pos hN hk
  have h2 : 1 ≤ k * k := Nat.mul_pos hk hk
  refine ⟨?_, ?_, ?_⟩
  · have : 2 * k * 1 ≤ 2 * k * (N * k) := Nat.mul_le_mul_left _ h1
    have e : 4 * k * N * k = 2 * (2 * k * (N * k)) := by ring
    omega
  · have : N * 1 ≤ N * (k * k) := Nat.mul_le_mul_left _ h2
    have e : 4 * k * N * k = 4 * (N * (k * k)) := by ring
    omega
  · have e : 4 * k * N * k = 2 * (2 * k * k * N) := by ring
    omega

set_option maxHeartbeats 2000000 in
theorem iter_posBody {N k : ℕ} (hk : 0 < k) (hN : 0 < N) (thr : ℕ) (R : List ℕ)
    (hR : ∀ x ∈ R, x ≤ E.M) (hnM : E.n ≤ E.M) (hbM : 4 * k * N * k + 2 ≤ E.M) :
    ∀ (x : ℕ) (σ : St) (L0 : List ℕ) (c i j : ℕ), x ≤ 2 * k * k * N → PQ (E := E) N k thr R σ →
      σ.sc 47 = c → σ.sc 48 = i → σ.sc 49 = j → i < k → j < N → (c * k + i) * N + j = 0 →
      σ.ls 19 = L0 → L0.length + 2 * k * k * N ≤ E.C →
      PQ (E := E) N k thr R ((exec E (.seq posBody odoC))^[x] σ) ∧
        ((exec E (.seq posBody odoC))^[x] σ).ls 19 =
          L0 ++ (List.range x).map (pAt E.n thr N k R) ∧
        (∀ r : SR, r.val < 41 ∨ (49 < r.val ∧ r.val < 50) ∨ 53 < r.val →
          ((exec E (.seq posBody odoC))^[x] σ).sc r = σ.sc r) ∧
        (∀ l : LR, l ≠ 19 → l ≠ 20 → ((exec E (.seq posBody odoC))^[x] σ).ls l = σ.ls l) ∧
        ∃ c' i' j', ((exec E (.seq posBody odoC))^[x] σ).sc 47 = c' ∧
          ((exec E (.seq posBody odoC))^[x] σ).sc 48 = i' ∧
          ((exec E (.seq posBody odoC))^[x] σ).sc 49 = j' ∧ i' < k ∧ j' < N ∧
          (c' * k + i') * N + j' = x
  | 0, σ, L0, c, i, j, _, hq, h47, h48, h49, hi, hj, h0, hL, _ =>
    ⟨hq, by simp [hL], fun _ _ => rfl, fun _ _ _ => rfl, c, i, j, h47, h48, h49, hi, hj, h0⟩
  | x + 1, σ, L0, c, i, j, hx, hq, h47, h48, h49, hi, hj, h0, hL, hC => by
    obtain ⟨hq1, hl1, hf1, hg1, c1, i1, j1, d47, d48, d49, hi1, hj1, hidx⟩ :=
      iter_posBody hk hN thr R hR hnM hbM x σ L0 c i j (by omega) hq h47 h48 h49 hi hj h0 hL hC
    rw [Function.iterate_succ_apply']
    set τ := (exec E (.seq posBody odoC))^[x] σ
    have hc1 : c1 < 2 * k := by
      by_contra h
      have a1 : 2 * k * k ≤ c1 * k := Nat.mul_le_mul_right k (by omega)
      have a2 : 2 * k * k * N ≤ c1 * k * N := Nat.mul_le_mul_right N a1
      have a3 : c1 * k * N ≤ (c1 * k + i1) * N := Nat.mul_le_mul_right N (by omega)
      omega
    have hidx' : (c1 * N + j1) * k + i1 < 2 * k * k * N := by
      have a1 : (c1 * N + j1) * k + i1 < (c1 * N + j1 + 1) * k := by
        rw [Nat.add_mul (c1 * N + j1) 1 k]; omega
      have a2 : c1 * N + j1 + 1 ≤ 2 * k * N := by
        have : (c1 + 1) * N ≤ 2 * k * N := Nat.mul_le_mul_right N (by omega)
        rw [Nat.add_mul] at this; omega
      have a3 : (c1 * N + j1 + 1) * k ≤ 2 * k * N * k := Nat.mul_le_mul_right k a2
      have : 2 * k * N * k = 2 * k * k * N := by ring
      omega
    have hb := pos_bounds hk hN
    obtain ⟨sc2, ls2, e2, d2, f2, g2⟩ := exec_posBody (E := E) hk hN τ c1 i1 j1 R thr hq1.1
      hq1.2.1 hq1.2.2.1 d47 d48 d49 hq1.2.2.2.1 hq1.2.2.2.2 (by omega) hR hnM
      (by rw [hl1]; simp; omega)
    obtain ⟨c2, i2, j2, e3, hidx2, hi2, hj2⟩ := exec_odoC (E := E) (setSL τ sc2 ls2) c1 i1 j1
      (by simp [setSL]; rw [f2 2 (by decide), hq1.1]) (by simp [setSL]; rw [f2 5 (by decide), hq1.2.1])
      (by simp [setSL]; rw [f2 47 (by decide), d47]) (by simp [setSL]; rw [f2 48 (by decide), d48])
      (by simp [setSL]; rw [f2 49 (by decide), d49]) hi1 hj1 (by omega) (by omega)
      (by omega)
    rw [exec_seq, e2, e3]
    have hs : ∀ r : SR, r.val < 41 ∨ (49 < r.val ∧ r.val < 50) ∨ 53 < r.val →
        (setSL (setSL τ sc2 ls2) (Function.update (Function.update (Function.update
          (setSL τ sc2 ls2).sc 47 c2) 48 i2) 49 j2) (setSL τ sc2 ls2).ls).sc r = σ.sc r :=
      fun r hr => by
        simp only [setSL]
        rw [Function.update_of_ne (by rintro rfl; revert hr; decide),
          Function.update_of_ne (by rintro rfl; revert hr; decide),
          Function.update_of_ne (by rintro rfl; revert hr; decide), f2 r (by omega), hf1 r hr]
    refine ⟨⟨by rw [hs 2 (by decide), hq.1], by rw [hs 5 (by decide), hq.2.1],
        by rw [hs 0 (by decide), hq.2.2.1], by rw [hs 58 (by decide), hq.2.2.2.1],
        by simp only [setSL]; rw [g2 23 (by decide) (by decide), hq1.2.2.2.2]⟩,
      ?_, hs, fun l a b => by simp only [setSL]; rw [g2 l a b, hg1 l a b],
      c2, i2, j2, by simp [setSL], by simp [setSL, Function.update_apply],
      by simp [setSL, Function.update_apply], hi2, hj2, by omega⟩
    simp only [setSL]
    rw [d2, hl1, List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    congr 3
    rw [← hidx, pAt_idx R hi1 hj1]

/-- Emit two positions of the list `19` as one gate. -/
def pairE : Code := .seq (.lpop 55 19) (.seq (.lpop 56 19) (.nand 57 55 56))

theorem iter_pairE : ∀ (x : ℕ) (σ : St) (L : List ℕ), σ.ls 19 = L → 2 * x ≤ L.length →
    (∀ v ∈ L, v < min (E.n + 1 + σ.t) E.M) →
    ((exec E pairE)^[x] σ).out = σ.out ++ ((L.take (2 * x)).map (uw E.W)).flatten ∧
    ((exec E pairE)^[x] σ).t = σ.t + x ∧ ((exec E pairE)^[x] σ).ls 19 = L.drop (2 * x) ∧
    ((exec E pairE)^[x] σ).src = σ.src ∧
    (∀ r : SR, r ≠ 55 → r ≠ 56 → r ≠ 57 → ((exec E pairE)^[x] σ).sc r = σ.sc r) ∧
    (∀ l : LR, l ≠ 19 → ((exec E pairE)^[x] σ).ls l = σ.ls l)
  | 0, σ, L, hL, _, _ => by simp [hL]
  | x + 1, σ, L, hL, hlen, hv => by
    obtain ⟨a, b, L', rfl⟩ : ∃ a b L', L = a :: b :: L' := by
      match L, hlen with
      | a :: b :: L', _ => exact ⟨a, b, L', rfl⟩
    rw [Function.iterate_succ_apply]
    have ha := hv a (by simp)
    have hb := hv b (by simp)
    set τ := exec E pairE σ
    have hτ : τ.out = σ.out ++ uw E.W a ++ uw E.W b ∧ τ.t = σ.t + 1 ∧ τ.ls 19 = L' ∧
        τ.src = σ.src ∧ (∀ r : SR, r ≠ 55 → r ≠ 56 → r ≠ 57 → τ.sc r = σ.sc r) ∧
        (∀ l : LR, l ≠ 19 → τ.ls l = σ.ls l) := by
      have fa : fixv E σ.t a = a := by unfold fixv; simp only [show ¬ min (E.n + 1 + σ.t) E.M ≤ a by omega, ↓reduceIte]
      have fb : fixv E σ.t b = b := by unfold fixv; simp only [show ¬ min (E.n + 1 + σ.t) E.M ≤ b by omega, ↓reduceIte]
      simp only [τ, pairE, exec, hL, Function.update_apply, List.headD_cons, List.tail_cons,
        show (56 : SR) ≠ 55 by decide, show (55 : SR) ≠ 56 by decide]
      refine ⟨by simp [fa, fb], trivial, by simp, trivial, fun r h1 h2 h3 => by simp [h1, h2, h3],
        fun l h => by simp [h]⟩
    obtain ⟨o1, t1, l1, s1, f1, g1⟩ := hτ
    obtain ⟨o2, t2, l2, s2, f2, g2⟩ := iter_pairE x τ L' l1 (by simp at hlen; omega)
      (fun v hv' => by
        have := hv v (by simp [hv'])
        rw [t1]; omega)
    refine ⟨?_, by rw [t2, t1]; ring, by rw [l2]; simp [Nat.mul_succ], by rw [s2, s1],
      fun r h1 h2 h3 => by rw [f2 r h1 h2 h3, f1 r h1 h2 h3], fun l h => by rw [g2 l h, g1 l h]⟩
    rw [o2, o1, show 2 * (x + 1) = 2 * x + 2 by ring]
    simp [List.append_assoc]

/-! ### The position stream as `posW` -/

theorem flatten_range_map (f : ℕ → List Bool) : ∀ n : ℕ,
    ((List.range n).map f).flatten = concatN n f
  | 0 => rfl
  | n + 1 => by rw [List.range_succ, List.map_append, List.flatten_append, flatten_range_map f n]; simp [concatN]

theorem uw_eq_unaryW (W j : ℕ) : uw W j = Tape.Prog.unaryW W j := rfl

theorem posList_eq (W n thr N k : ℕ) (R : List ℕ) :
    (((List.range (2 * k * k * N)).map (pAt n thr N k R)).map (uw W)).flatten =
      Tape.Prog.posW W N k (fun c i j => pfix n thr N k R c i j) := by
  rw [List.map_map, flatten_range_map, concatN_mul, concatN_mul]
  unfold Tape.Prog.posW
  refine concatN_congr fun c _ => concatN_congr fun i hi => concatN_congr fun j hj => ?_
  simp only [Function.comp, uw_eq_unaryW, pAt_idx R hi hj]

theorem pfix_repList {ι : Type*} (ix : ι → ℕ) (hix : ∀ i, ix i < E.n) (t : ℕ)
    (rep : BI N k → Wire ι) {c i j : ℕ} (hc : c < 2 * k) (hi : i < k) (hj : j < N) :
    pfix E.n (E.n + 1 + t) N k (repList E ix rep) c i j =
      Tape.Prog.wireIx ix E.n t (rep (0, colE k ⟨c, hc⟩, ⟨i, hi⟩, ⟨j, hj⟩)) := by
  have ho : oIdx ((0, colE k ⟨c, hc⟩, ⟨j, hj⟩) : OI N k) = c * N + j := by
    simp only [oIdx, colE_apply]
    have := Nat.div_add_mod c k
    simp only [Fin.val_zero, zero_mul, zero_add]
    rw [Nat.mul_comm (c / k) k, this]
  have h := repList_getD E ix rep ((0, colE k ⟨c, hc⟩, ⟨j, hj⟩) : OI N k) ⟨i, hi⟩
  rw [ho] at h
  simp only at h
  unfold pfix
  cases hw : rep (0, colE k ⟨c, hc⟩, ⟨i, hi⟩, ⟨j, hj⟩) with
  | input a => have := hix a; simp only [h, hw, pos, Tape.Prog.wireIx]; split_ifs <;> omega
  | one => simp only [h, hw, pos, Tape.Prog.wireIx]; split_ifs <;> omega
  | gate m => simp only [h, hw, pos, Tape.Prog.wireIx]; split_ifs <;> omega

end FhatGen

end SigabaNeo.Lattices
