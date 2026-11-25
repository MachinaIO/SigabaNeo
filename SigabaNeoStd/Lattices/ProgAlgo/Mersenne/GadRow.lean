import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.Canon
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.Mul

/-!
# The gadget row minus a row of ring words, modulo `2^K − 1`

The TrapGen row `B⁽¹⁾ = [Ā | g − Ā T]` needs the gadget row `g = (1, 2, …, 2^{K−1})` minus the
row `Ā T`. `gadRowP : Prog 42` writes the canonical words of `g_c − P_c` for `c < K`
(`run_gadRowP`, `gadRowW`):

* tapes: `0` output register (any word of `K · N K` bits before), `1` the row `P` (`K` ring words),
  templates `2` (`K`), `3` (`N`), `4` (`N K`), `5` (`K − 1`), `6` the word `one` of `1`
  (`true` then `N K − 1` zeros); scratch `7 … 41`, blank before and after;
* per column: `a := P_c` (`mvP`), `d := g − a` (`subRMP`), `canonW d` (`canonRP`) shifted into the
  output, `g := 2 g` (`rotBP` by `K − 1`, i.e. `2^{1 − K} = 2`).

`decRM_gadRowW`: block `c` reads as `2^c − decRM P_c`, canonical.
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG

variable {k : ℕ}

/-- The abstract round: (stream of `P`, `g`, the register `a`, output). -/
def gstep (N K : ℕ) : List Bool × List Bool × List Bool × List Bool →
    List Bool × List Bool × List Bool × List Bool
  | (sv, g, a, out) => (sv.drop (N * K), rotBW N K (K - 1) g, takeD (N * K) sv,
      (out ++ canonW N K (subRMW N K g (takeD (N * K) sv))).drop (N * K))

/-- The gadget entries `2^c`, as `rotBW` iterates of `one`. -/
def gIt (N K : ℕ) (one : List Bool) (c : ℕ) : List Bool := (rotBW N K (K - 1))^[c] one

/-- **The words of `g_c − P_c`**, canonicalized. -/
def gadRowW (N K : ℕ) (one P : List Bool) : List Bool :=
  concatN K (fun c => canonW N K (subRMW N K (gIt N K one c) (takeD (N * K) (P.drop (c * (N * K))))))

theorem length_gIt {N K : ℕ} {one : List Bool} (h : one.length = N * K) (c : ℕ) :
    (gIt N K one c).length = N * K := by
  induction c with
  | zero => exact h
  | succ c ih =>
    rw [gIt, Function.iterate_succ_apply']
    exact length_rotBW N K _ ih

theorem gstep_iter {N K : ℕ} (one : List Bool) (hone : one.length = N * K) : ∀ (c : ℕ)
    (sv a out : List Bool),
    (gstep N K)^[c] (sv, one, a, out) =
      (sv.drop (c * (N * K)), gIt N K one c,
        if c = 0 then a else takeD (N * K) (sv.drop ((c - 1) * (N * K))),
        (out ++ concatN c (fun j => canonW N K (subRMW N K (gIt N K one j)
          (takeD (N * K) (sv.drop (j * (N * K))))))).drop (c * (N * K)))
  | 0, sv, a, out => by simp [concatN, gIt]
  | c + 1, sv, a, out => by
    rw [Function.iterate_succ_apply', gstep_iter one hone c sv a out]
    have hl : (concatN c (fun j => canonW N K (subRMW N K (gIt N K one j)
        (takeD (N * K) (sv.drop (j * (N * K))))))).length = c * (N * K) :=
      length_concatN fun j _ => length_canonW N K (length_subRMW N K (length_gIt hone j) _)
    have hd := drop_append_drop out (concatN c (fun j => canonW N K (subRMW N K (gIt N K one j)
      (takeD (N * K) (sv.drop (j * (N * K))))))) (canonW N K (subRMW N K (gIt N K one c)
        (takeD (N * K) (sv.drop (c * (N * K))))))
    rw [hl, length_canonW N K (length_subRMW N K (length_gIt hone c) _)] at hd
    simp only [gstep, Prod.mk.injEq, List.drop_drop]
    refine ⟨by congr 1; ring, ?_, ?_, ?_⟩
    · show rotBW N K (K - 1) (gIt N K one c) = gIt N K one (c + 1)
      rw [gIt, gIt, Function.iterate_succ_apply']
    · simp
    · first
        | exact hd
        | (rw [hd]; simp [concatN, List.append_assoc, Nat.add_comm, Nat.add_mul])
        | (simp only [concatN, List.append_assoc] at hd ⊢; rw [hd]; congr 1; ring)

namespace Prog

open scoped Prog

/-- `mvP` from the stream `10` into the register `9` (scratch `14`, counter `15`, length `4`). -/
def gMvA : Fin 5 → Fin 42 := ![10, 9, 14, 15, 4]
/-- `mvP` from `12` into the output `0`. -/
def gMvO : Fin 5 → Fin 42 := ![12, 0, 14, 15, 4]
/-- `subRMP`: `11 := 8 − 9`. -/
def gSub : Fin 28 → Fin 42 := ![11, 8, 9, 2, 3, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
  29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]
/-- `canonRP`: `12 := canonW 11` (dummy operand `4`). -/
def gCan : Fin 28 → Fin 42 := ![12, 11, 4, 2, 3, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
  29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]
/-- `rotBP`: `13 := rotBW (K − 1) 8`. -/
def gRot : Fin 30 → Fin 42 := ![13, 8, 5, 2, 3, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
  29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41]

theorem gMvA_inj : Function.Injective gMvA := by decide
theorem gMvO_inj : Function.Injective gMvO := by decide
theorem gSub_inj : Function.Injective gSub := by decide
theorem gCan_inj : Function.Injective gCan := by decide
theorem gRot_inj : Function.Injective gRot := by decide

/-- One column. -/
def gRBody : Prog 42 :=
  map gMvA mvP ⨾ map gSub subRMP ⨾ map gCan canonRP ⨾ map gMvO mvP ⨾ map gRot rotBP ⨾ cp 8 13 ⨾
    clr 11 ⨾ clr 12 ⨾ clr 13

/-- **The gadget row minus `P`.** -/
def gadRowP : Prog 42 := cp 10 1 ⨾ cp 8 6 ⨾ cp 9 4 ⨾ forN 7 2 gRBody ⨾ clr 8 ⨾ clr 9 ⨾ clr 10

def gRG (S : Store 42) : List Bool × List Bool × List Bool × List Bool → Store 42
  | (sv, g, a, out) =>
    Function.update (Function.update (Function.update (Function.update S 10 sv) 8 g) 9 a) 0 out

/-- The scratch of a round is blank. -/
def GRClean (S : Store 42) : Prop := ∀ i : Fin 42, 11 ≤ i.val → S i = []

set_option maxHeartbeats 4000000 in
theorem run_gRBody {K N : ℕ} (hK : 0 < K) (S : Store 42) (hS : GRClean S) (hK' : (S 2).length = K)
    (hN : (S 3).length = N) (hNK : (S 4).length = N * K) (hj : (S 5).length = K - 1) (a)
    (hg : a.2.1.length = N * K) (ha : a.2.2.1.length = N * K) (w : List Bool) :
    run gRBody (Function.update (gRG S a) 7 w) = Function.update (gRG S (gstep N K a)) 7 w := by
  obtain ⟨sv, g, a, out⟩ := a
  simp only at hg ha
  have hS : ∀ i : Fin 42, 11 ≤ i.val → S i = [] := hS
  have hta : (takeD (N * K) sv).length = N * K := length_takeD _ _
  have hsub : (subRMW N K g (takeD (N * K) sv)).length = N * K := length_subRMW N K hg _
  simp only [gRBody, run_seq, run_copy, run_clear]
  rw [run_mvP_map gMvA_inj _ (by simp [gMvA, gRG, hS]) (by simp [gMvA, gRG, hS])]
  rw [run_subRMP_map gSub_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [gSub, gMvA, gRG, hS] at hi ⊢
  · simp [gSub, gMvA, gRG, hK']
  · simp [gSub, gMvA, gRG, hN]
  · simp [gSub, gMvA, gRG, hg]
  · simp [gSub, gMvA, gRG, hNK, ha, drop_append_of_length, hta]
  rw [run_canonRP_map gCan_inj (K := K) (N := N) hK _ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [gCan, gSub, gMvA, gRG, hS] at hi ⊢
  · simp [gCan, gSub, gMvA, gRG, hK']
  · simp [gCan, gSub, gMvA, gRG, hN]
  · simp [gCan, gSub, gMvA, gRG, hNK, ha, drop_append_of_length, hta, hsub]
  · simp [gCan, gSub, gMvA, gRG, hNK]
  rw [run_mvP_map gMvO_inj _ (by simp [gMvO, gCan, gSub, gMvA, gRG, hS])
    (by simp [gMvO, gCan, gSub, gMvA, gRG, hS])]
  rw [run_rotBP_map gRot_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [gRot, gMvO, gCan, gSub, gMvA, gRG, hS] at hi ⊢
  · simp [gRot, gMvO, gCan, gSub, gMvA, gRG, hK']
  · simp [gRot, gMvO, gCan, gSub, gMvA, gRG, hN]
  · simp [gRot, gMvO, gCan, gSub, gMvA, gRG, hg]
  have hcw : (canonW N K (subRMW N K g (takeD (N * K) sv))).length = N * K :=
    length_canonW N K hsub
  funext t
  simp only [gRG, gstep]
  fin_cases t <;> simp [gRot, gMvO, gCan, gSub, gMvA, hS, hNK, hj, ha, hta, hcw,
    drop_append_of_length, List.drop_of_length_le, takeD_of_length' hcw]

/-- **The gadget row minus `P`**: `0 := gadRowW N K one P`. -/
theorem run_gadRowP {K N : ℕ} (hK : 0 < K) (s : Store 42) (hs : ∀ i : Fin 42, 7 ≤ i.val → s i = [])
    (hK' : (s 2).length = K) (hN : (s 3).length = N) (hNK : (s 4).length = N * K)
    (hj : (s 5).length = K - 1) (hone : (s 6).length = N * K) (hO : (s 0).length = K * (N * K)) :
    run gadRowP s = Function.update s 0 (gadRowW N K (s 6) (s 1)) := by
  set s1 := Function.update (Function.update (Function.update s 10 (s 1)) 8 (s 6)) 9 (s 4)
  have hloop := run_forN_inv 7 2 gRBody (gRG s1) (gstep N K)
    (fun a => a.2.1.length = N * K ∧ a.2.2.1.length = N * K)
    (fun a w ha => run_gRBody hK s1 (fun i hi => by
        fin_cases i <;> simp [s1, hs] at hi ⊢) (by simp [s1, hK']) (by simp [s1, hN])
        (by simp [s1, hNK]) (by simp [s1, hj]) a ha.1 ha.2 w)
    (fun a ha => by
      obtain ⟨sv, g, a, out⟩ := a
      exact ⟨length_rotBW N K _ ha.1, length_takeD _ _⟩)
    (s 1, s 6, s 4, s 0) ⟨hone, hNK⟩ s1 (by funext t; fin_cases t <;> simp [s1, gRG, hs])
  have hsplit : run gadRowP s = run (clr 8 ⨾ clr 9 ⨾ clr 10) (run (forN 7 2 gRBody) s1) := by
    simp only [gadRowP, run_seq, run_copy, s1]
    rfl
  rw [hsplit, hloop, gstep_iter _ hone, show s1 2 = s 2 by simp [s1], hK']
  simp only [run_seq, run_clear]
  rw [show K * (N * K) = (s 0).length from hO.symm, drop_append_of_length rfl]
  funext t
  fin_cases t <;> simp [gRG, s1, hs, gadRowW, hO]

theorem noGrow_gadRowP : gadRowP.NoGrow := rfl
theorem wf_gadRowP : gadRowP.WF := wf_of_wfB (by decide)

end Prog

/-! ### The ring elements -/

theorem decRM_one {N K : ℕ} (hK : 0 < K) (hN : 0 < N) :
    decRM N K (true :: List.replicate (N * K - 1) false) = 1 := by
  apply ext_coefG
  intro i hi
  rw [coefG_decRM _ hi]
  have hNK : 1 ≤ N * K := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · have hb : block K 0 (true :: List.replicate (N * K - 1) false) =
        true :: List.replicate (K - 1) false := by
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      simp only [block, zero_mul, List.drop_zero, List.take_succ_cons, List.take_replicate,
        Nat.add_sub_cancel]
      congr 2
      have : K' ≤ N * (K' + 1) - 1 := by
        have := Nat.le_mul_of_pos_left (K' + 1) hN; omega
      omega
    rw [hb, decM, show (1 : Cslib.Negacyclic (ZMod (2 ^ K - 1)) N) = algebraMap _ _ 1 from
      (map_one _).symm]
    have hz : val (List.replicate (K - 1) false) = 0 := val_zeroW (K - 1)
    simp [coefG, hN, val_cons, hz]
  · have hb : block K i (true :: List.replicate (N * K - 1) false) = List.replicate K false := by
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      simp only [block, List.drop_replicate, List.take_replicate]
      rw [show (i' + 1) * K = (i' * K + (K - 1)) + 1 by
        obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩; simp; ring, List.drop_succ_cons,
        List.drop_replicate, List.take_replicate]
      congr 1
      have : (i' + 1) * K + K ≤ N * K := by nlinarith
      have : (i' + 1) * K = i' * K + K := by ring
      omega
    rw [hb, show List.replicate K false = zeroW K from rfl, decM_zeroW]
    rw [show (1 : Cslib.Negacyclic (ZMod (2 ^ K - 1)) N) = algebraMap _ _ 1 from
      (map_one _).symm]
    simp [coefG, hi, hi0.ne']

end SigabaNeo.Tape
