import PE.Impl.ExpLUT.Prog.Words
import SigabaNeo.Lib.Lattices.ProgAlgo.MatAdd
import PE.Impl.DualUse.Prog.Lift
import PE.Impl.DualUse.Prog.Setup5
import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.Canon
import SigabaNeo.Lib.Machines.Prog.Pass
import SigabaNeo.Lib.Machines.Randomized

/-!
# Sampling canonical "uniform" ring words

`unifCanonP N K n : XProg 40` appends to tape `0` the canonical words of `n` independent ring
elements of `unifW` (`n N K` fair bits, then `canonRP`): **`appendLaw_unifCanonP`**, with the law
`catPow (υW N K) n`, `υW N K` the law of the canonical word of `N K` fair bits. Every other tape
is blank before and after (scratch `1 … 39`).

`υW_eq`: `υW` is the law of the word `rEnc.enc a`, `a ← unifW D`; the encodings of independent
families of such elements are `catPow (υW …)` (`lawVec`, `lawMat`, `lawFunMat`, `lawFunFunMat`).
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.XProg Matrix Cslib Cslib.Probability
open AdvancedEncryption.DualUse.Prog

/-! ### Laws of words -/

theorem pmf_bind_congr_support {α β : Type} (p : PMF α) {f g : α → PMF β}
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  simp only [PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [(PMF.apply_eq_zero_iff _ _).mpr ha]; simp

/-- The law of the canonical word of `N K` fair bits. -/
noncomputable def υW (N K : ℕ) : PMF (List Bool) :=
  (BitString.uniformList (N * K)).map (canonW N K)

theorem block_append_left {K i : ℕ} {u v : List Bool} (h : (i + 1) * K ≤ u.length) :
    block K i (u ++ v) = block K i u := by
  have h' : i * K + K ≤ u.length := by rw [show i * K + K = (i + 1) * K by ring]; exact h
  unfold block
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by
    rw [List.length_drop]; omega)]

theorem block_append_right {K i : ℕ} {u v : List Bool} (h : u.length = i * K) (j : ℕ) :
    block K (i + j) (u ++ v) = block K j v := by
  unfold block
  rw [show (i + j) * K = u.length + j * K by rw [h]; ring, ← List.drop_drop,
    List.drop_left]

theorem canonW_append {N K n : ℕ} {u v : List Bool} (hu : u.length = n * N * K)
    (hv : v.length = N * K) :
    canonW ((n + 1) * N) K (u ++ v) = canonW (n * N) K u ++ canonW N K v := by
  unfold canonW
  rw [show (n + 1) * N = n * N + N by ring, SigabaNeo.Tape.concatN_add]
  congr 1
  · apply concatN_congr
    intro i hi
    rw [block_append_left (by rw [hu]; nlinarith)]
  · apply concatN_congr
    intro j hj
    rw [block_append_right (by rw [hu])]

/-- **Canonicalized fair bits** are independent canonical words. -/
theorem canon_catPow (N K : ℕ) : ∀ n : ℕ,
    (BitString.uniformList (n * (N * K))).map (canonW (n * N) K) = catPow (υW N K) n
  | 0 => by simp [canonW, concatN]
  | n + 1 => by
    have e1 : BitString.uniformList ((n + 1) * (N * K)) =
        (BitString.uniformList (n * (N * K))).bind fun a =>
          (BitString.uniformList (N * K)).map (a ++ ·) := by
      rw [← catPow_uniformList (N * K) (n + 1), catPow_succ, catPow_uniformList]
    rw [e1, PMF.map_bind, catPow_succ, ← canon_catPow N K n, PMF.bind_map]
    refine pmf_bind_congr_support _ fun u hu => ?_
    have hul := BitString.length_of_mem_support_uniformList hu
    simp only [Function.comp_def, υW, PMF.map_comp]
    refine PMF.map_congr_support _ fun v hv => ?_
    exact canonW_append (by rw [hul]; ring) (BitString.length_of_mem_support_uniformList hv)

variable (D : Dims)

/-- **The canonical word of a `unifW` element.** -/
theorem υW_eq : (unifW D).map (rEnc D).enc = υW D.N D.K := by
  rw [unifW, PMF.map_comp, υW]
  refine PMF.map_congr_support _ fun v hv => ?_
  have hl := BitString.length_of_mem_support_uniformList hv
  rw [Function.comp_apply, rEnc_enc, canonW_eq D.K_pos hl]

variable {D}

theorem lawVec (υ : PMF (Rg D)) (α : Type) [Enum α] [Fintype α] [DecidableEq α] :
    (iidLaw υ α).map (vecE D α).enc = catPow (υ.map (rEnc D).enc) (Enum.list (α := α)).length :=
  fun_enc_pi (rEnc D) υ

theorem lawMat (υ : PMF (Rg D)) (r s : Type) [Enum r] [Fintype r] [DecidableEq r] [Enum s]
    [Fintype s] [DecidableEq s] :
    (iidFam υ r s).map (matE D r s).enc =
      catPow (υ.map (rEnc D).enc) ((Enum.list (α := r)).length * (Enum.list (α := s)).length) := by
  rw [iidFam, fun_enc_pi, lawVec, catPow_mul]

theorem lawFunMat (υ : PMF (Rg D)) (j r s : Type) [Enum j] [Fintype j] [DecidableEq j] [Enum r]
    [Fintype r] [DecidableEq r] [Enum s] [Fintype s] [DecidableEq s] :
    (Cslib.Probability.PMF.pi fun _ : j => iidFam υ r s).map
        (FixedEnc.fun (α := j) (matE D r s)).enc =
      catPow (υ.map (rEnc D).enc) ((Enum.list (α := j)).length *
        ((Enum.list (α := r)).length * (Enum.list (α := s)).length)) := by
  rw [fun_enc_pi, lawMat, catPow_mul]

theorem lawFunFunMat (υ : PMF (Rg D)) (i j r s : Type) [Enum i] [Fintype i] [DecidableEq i]
    [Enum j] [Fintype j] [DecidableEq j] [Enum r] [Fintype r] [DecidableEq r] [Enum s] [Fintype s]
    [DecidableEq s] :
    (Cslib.Probability.PMF.pi fun _ : i => Cslib.Probability.PMF.pi fun _ : j => iidFam υ r s).map
        (FixedEnc.fun (α := i) (FixedEnc.fun (α := j) (matE D r s))).enc =
      catPow (υ.map (rEnc D).enc) ((Enum.list (α := i)).length * ((Enum.list (α := j)).length *
        ((Enum.list (α := r)).length * (Enum.list (α := s)).length))) := by
  rw [fun_enc_pi, lawFunMat, catPow_mul]

/-! ### The sampler -/

/-- The fair bits land on tape `1` (scratch `2 … 6`). -/
def eU : Fin 7 ↪ Fin 40 := ⟨![1, 39, 2, 3, 4, 5, 6], by decide⟩

/-- `canonRP`: `33 := canonW (s 1)` (dummy operand `9`, templates `7`, `8`, scratch `10 … 32`). -/
def uCan : Fin 28 → Fin 40 := ![33, 1, 9, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
  23, 24, 25, 26, 27, 28, 29, 30, 31, 32]

theorem uCan_inj : Function.Injective uCan := by decide

/-- The deterministic tail: canonicalize tape `1` into `33`, append it to `0`, clear. -/
def ucTail : Prog 40 :=
  Prog.seq (.prim (.copy 9 1)) (Prog.seq (Prog.map uCan Prog.canonRP)
    (Prog.seq (.prim (.clear 1)) (Prog.seq (.prim (.clear 9)) (Prog.seq (.prim (.clear 7))
      (.prim (.clear 8))))))

/-- **`n` canonical "uniform" ring words appended to tape `0`.** -/
def unifCanonP (N K n : ℕ) : XProg 40 :=
  seq (frame eU (coinsF (n * (N * K)))) (seq (natP 7 34 K) (seq (natP 8 34 (n * N))
    (seq (prog ucTail) (appendTapeP 0 33 35 36))))

/-- The scratch tapes are blank. -/
def UCPre (s : Store 40) : Prop := ∀ j : Fin 40, 1 ≤ j.val → s j = []

theorem run_ucTail {N K n : ℕ} (hK : 0 < K) (s : Store 40) (hs : ∀ j : Fin 40, 9 ≤ j.val → s j = [])
    (h7 : s 7 = List.replicate K false) (h8 : s 8 = List.replicate (n * N) false)
    (h1 : (s 1).length = n * N * K) :
    Prog.run ucTail s = Function.update (Function.update (Function.update (Function.update
      (Function.update s 33 (canonW (n * N) K (s 1))) 1 []) 9 []) 7 []) 8 [] := by
  simp only [ucTail, Prog.run_seq, Prog.run_copy, Prog.run_clear]
  rw [Prog.run_canonRP_map uCan_inj (K := K) (N := n * N) hK _ ?_ ?_ ?_ ?_ ?_]
  · funext t
    simp only [Function.update_apply, uCan]
    split_ifs <;> simp_all
  · intro i hi; fin_cases i <;> simp [uCan, hs] at hi ⊢
  · simp [uCan, h7]
  · simp [uCan, h8]
  · simp [uCan, h1]
  · simp [uCan, h1]

theorem coinFree_ucTail : ucTail.CoinFree := rfl

/-- **The law of `unifCanonP`.** -/
theorem appendLaw_unifCanonP {N K : ℕ} (hK : 0 < K) (n : ℕ) :
    AppendLaw (unifCanonP N K n) 0 UCPre (catPow (υW N K) n) := by
  intro s hs
  have hs' : ∀ j : Fin 40, 1 ≤ j.val → s j = [] := hs
  have hc := appendLaw_frame eU (law_coinsF (n * (N * K)))
  rw [unifCanonP, law_seq, hc s (by
    refine ⟨?_, ?_, ?_⟩ <;> simp [eU, hs']), ← canon_catPow, PMF.map_comp, PMF.bind_map]
  refine pmf_bind_congr_support _ fun u hu => ?_
  have hul := BitString.length_of_mem_support_uniformList hu
  simp only [Function.comp_apply]
  set s1 := Function.update s (eU 0) (s (eU 0) ++ u)
  have e1 : s1 = Function.update s 1 u := by simp [s1, eU, hs']
  rw [e1, law_seq, law_natP (by decide) K _ (by simp [hs']), PMF.pure_bind, law_seq,
    law_natP (by decide) (n * N) _ (by simp [hs']), PMF.pure_bind, law_seq, law_prog,
    Prog.law_eq_run_of_coinFree _ coinFree_ucTail, PMF.pure_bind]
  rw [run_ucTail (N := N) (n := n) hK _ (fun j hj => by
      simp only [Function.update_apply]
      split_ifs <;> first | omega | (subst_vars; simp at hj) | exact hs' j (by omega))
    (by simp) (by simp) (by simp [hul]; ring)]
  rw [law_appendTapeP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) _
    (by simp [hs']) (by simp [hs'])]
  congr 1
  funext t
  simp only [Function.update_apply]
  split_ifs <;> (try subst_vars) <;> simp_all <;> exact (hs' t (by omega)).symm

theorem wf_ucTail : ucTail.WF := Prog.wf_of_wfB (by decide)

theorem wf_unifCanonP (N K n : ℕ) : (unifCanonP N K n).WF :=
  ⟨wf_coinsF _, wf_natP (by decide) _, wf_natP (by decide) _, wf_ucTail,
    wf_appendTapeP (by decide) (by decide)⟩

end AdvancedEncryption.ExpLUT.Prog
