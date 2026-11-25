import PE.Impl.ExpLUT.Prog.EncTailCodec
import SigabaNeo.Lib.Machines.Prog.Lookup

/-! # Executable outer loop for all encryption helper pairs -/

namespace AdvancedEncryption.ExpLUT.Prog.EncW

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.Prog Matrix

variable (D : Dims)

/-- Install the two exponent templates, execute a helper pair, then release the templates.
Literal template lengths are part of the program description and must be charged in its bound. -/
def helperRoundP (t : ℕ) : SigabaNeo.Tape.Prog 69 :=
  .seq (putW 5 (List.replicate (2 ^ t) false))
    (.seq (putW 6 (List.replicate (2 ^ D.b - 2 ^ t) false))
      (.seq hBlkP (.seq (clr 5) (clr 6))))

/-- Consecutive helper pairs, in the scheme's exponent order. -/
def helperPairsP (j : ℕ) : ℕ → SigabaNeo.Tape.Prog 69
  | 0 => cp 0 0
  | n + 1 => .seq (helperRoundP D j) (helperPairsP (j + 1) n)

theorem wf_helperRoundP (t : ℕ) : (helperRoundP D t).WF :=
  ⟨wf_putW _ _, wf_putW _ _, wf_hBlkP, trivial, trivial⟩

theorem wf_helperPairsP (j n : ℕ) : (helperPairsP D j n).WF := by
  induction n generalizing j with
  | zero => trivial
  | succ n ih => exact ⟨wf_helperRoundP D j, ih (j + 1)⟩

theorem coinFree_helperRoundP (t : ℕ) : (helperRoundP D t).CoinFree := by
  have hh : hBlkP.CoinFree := rfl
  simp only [helperRoundP, Prog.CoinFree, Prog.coinFreeB, Bool.and_eq_true]
  exact ⟨coinFree_putW _ _, coinFree_putW _ _, hh, trivial, trivial⟩

theorem coinFree_helperPairsP (j n : ℕ) : (helperPairsP D j n).CoinFree := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    simp only [helperPairsP, Prog.CoinFree, Prog.coinFreeB, Bool.and_eq_true]
    exact ⟨coinFree_helperRoundP D j, ih (j + 1)⟩

/-- The three mutable stream registers of the helper loop. -/
def helperState (S : Store 69) (o H E : List Bool) : Store 69 :=
  Function.update (Function.update (Function.update S 0 o) 2 H) 3 E

theorem helperState_idem (S : Store 69) (o H E o' H' E' : List Bool) :
    helperState (helperState S o H E) o' H' E' = helperState S o' H' E' := by
  funext i
  by_cases h0 : i = 0 <;> by_cases h2 : i = 2 <;> by_cases h3 : i = 3 <;>
    simp [helperState, h0, h2, h3]

theorem helperOK_state {S : Store 69} (h : HelperOK D S) (o H E : List Bool) :
    HelperOK D (helperState S o H E) := by
  constructor
  · intro i hi
    have h0 : i ≠ 0 := by intro he; subst he; simp at hi
    have h2 : i ≠ 2 := by intro he; subst he; simp at hi
    have h3 : i ≠ 3 := by intro he; subst he; simp at hi
    simp [helperState, h0, h2, h3, h.scratch i hi]
  all_goals simp [helperState, h.hK, h.hN, h.hNK, h.h11, h.h12, h.h13, h.h14, h.h15]

/-- The mathematical pair of helper rows in stream order. -/
noncomputable def helperPairWord (s : Rg D) (t : ℕ)
    (H : Fin 2 → Fin 2 → Col D.K → Rg D) (E : Fin 2 → Col D.K → Rg D) : List Bool :=
  (vecE D (Col D.K)).enc (helperRow D s (2 ^ t) (H 0) (E 0)) ++
    (vecE D (Col D.K)).enc (helperRow D s (2 ^ D.b - 2 ^ t) (H 1) (E 1))

theorem length_helperPairWord (s : Rg D) (t : ℕ)
    (H : Fin 2 → Fin 2 → Col D.K → Rg D) (E : Fin 2 → Col D.K → Rg D) :
    (helperPairWord D s t H E).length = 2 * ((D.K + D.K) * (D.N * D.K)) := by
  rw [helperPairWord, List.length_append, length_vecE', length_vecE', length_col]
  ring

set_option maxRecDepth 100000 in
/-- A concrete helper round consumes both inputs and restores its exponent-template scratch. -/
theorem run_helperRoundP (S : Store 69) (h : HelperOK D S) (s : Rg D) (t : ℕ)
    (H : Fin 2 → Fin 2 → Col D.K → Rg D) (E : Fin 2 → Col D.K → Rg D)
    (restH restE : List Bool) (hs : S 1 = wd D s) (h1 : S 7 = wd D 1)
    (hg : (S 4).length = gD D) (h5 : S 5 = []) (h6 : S 6 = [])
    (hH : S 2 = (matE D (Fin 2) (Col D.K)).enc (H 0) ++
      ((matE D (Fin 2) (Col D.K)).enc (H 1) ++ restH))
    (hE : S 3 = (vecE D (Col D.K)).enc (E 0) ++ ((vecE D (Col D.K)).enc (E 1) ++ restE))
    (hout : (D.K + D.K) * (D.N * D.K) ≤ (S 0).length) :
    (helperRoundP D t).run S = helperState S
      ((S 0 ++ helperPairWord D s t H E).drop (2 * ((D.K + D.K) * (D.N * D.K)))) restH restE := by
  let T := Function.update (Function.update S 5 (List.replicate (2 ^ t) false))
    6 (List.replicate (2 ^ D.b - 2 ^ t) false)
  have hT : HelperOK D T := by
    constructor
    · intro i hi
      have h5' : i ≠ 5 := by intro he; subst he; simp at hi
      have h6' : i ≠ 6 := by intro he; subst he; simp at hi
      simp [T, h5', h6', h.scratch i hi]
    all_goals simp [T, h.hK, h.hN, h.hNK, h.h11, h.h12, h.h13, h.h14, h.h15]
  have hr := run_hBlkP_scheme D T hT (H 0) (H 1) (E 0) (E 1) s
    (2 ^ t) (2 ^ D.b - 2 ^ t) restH restE
    (by simpa [T] using hs) (by simpa [T] using h1) (by simpa [T] using hg)
    (by simp [T]) (by simp [T]) (by simpa [T] using hH) (by simpa [T] using hE)
  have hrow (j : ℕ) (M : Fin 2 → Col D.K → Rg D) (e : Col D.K → Rg D) :
      ((vecE D (Col D.K)).enc (helperRow D s j M e)).length =
        (D.K + D.K) * (D.N * D.K) := by rw [length_vecE', length_col]
  have ho := shiftAppend_comp (S 0)
    ((vecE D (Col D.K)).enc (helperRow D s (2 ^ t) (H 0) (E 0)))
    ((vecE D (Col D.K)).enc (helperRow D s (2 ^ D.b - 2 ^ t) (H 1) (E 1)))
    (by rw [hrow]; exact hout)
  simp only [shiftAppend, List.length_append, hrow] at ho
  rw [show (D.K + D.K) * (D.N * D.K) + (D.K + D.K) * (D.N * D.K) =
    2 * ((D.K + D.K) * (D.N * D.K)) by ring] at ho
  simp only [helperRoundP, Prog.run_seq, run_putW, run_clear]
  change Function.update (Function.update (hBlkP.run T) 5 []) 6 [] = _
  rw [hr]
  change Function.update (Function.update (helperState T
    ((((S 0 ++ (vecE D (Col D.K)).enc (helperRow D s (2 ^ t) (H 0) (E 0))).drop
      ((D.K + D.K) * (D.N * D.K))) ++ (vecE D (Col D.K)).enc
        (helperRow D s (2 ^ D.b - 2 ^ t) (H 1) (E 1))).drop
          ((D.K + D.K) * (D.N * D.K))) restH restE) 5 []) 6 [] = _
  rw [ho]
  funext i
  fin_cases i <;> simp [helperState, T, h5, h6, helperPairWord]

/-- The complete concrete helper program consumes consecutive pairs and writes their row stream. -/
theorem run_helperPairsP (S : Store 69) (h : HelperOK D S) (s : Rg D)
    (H : ℕ → Fin 2 → Fin 2 → Col D.K → Rg D) (E : ℕ → Fin 2 → Col D.K → Rg D)
    (j n : ℕ) (restH restE : List Bool) (hs : S 1 = wd D s) (h1 : S 7 = wd D 1)
    (hg : (S 4).length = gD D) (h5 : S 5 = []) (h6 : S 6 = [])
    (hH : S 2 = blockStream (fun t ↦ (matE D (Fin 2) (Col D.K)).enc (H t 0) ++
      (matE D (Fin 2) (Col D.K)).enc (H t 1)) j n ++ restH)
    (hE : S 3 = blockStream (fun t ↦ (vecE D (Col D.K)).enc (E t 0) ++
      (vecE D (Col D.K)).enc (E t 1)) j n ++ restE)
    (hout : n * (2 * ((D.K + D.K) * (D.N * D.K))) ≤ (S 0).length) :
    (helperPairsP D j n).run S = helperState S
      ((S 0 ++ blockStream (fun t ↦ helperPairWord D s t (H t) (E t)) j n).drop
        (n * (2 * ((D.K + D.K) * (D.N * D.K))))) restH restE := by
  induction n generalizing S j with
  | zero =>
    simp only [blockStream_zero, List.nil_append] at hH hE
    simp [helperPairsP, run_copy, helperState, ← hH, ← hE]
  | succ n ih =>
    let rh := blockStream (fun t ↦ (matE D (Fin 2) (Col D.K)).enc (H t 0) ++
      (matE D (Fin 2) (Col D.K)).enc (H t 1)) (j + 1) n ++ restH
    let re := blockStream (fun t ↦ (vecE D (Col D.K)).enc (E t 0) ++
      (vecE D (Col D.K)).enc (E t 1)) (j + 1) n ++ restE
    let o := (S 0 ++ helperPairWord D s j (H j) (E j)).drop
      (2 * ((D.K + D.K) * (D.N * D.K)))
    let T := helperState S o rh re
    have hn : 2 * ((D.K + D.K) * (D.N * D.K)) ≤ (S 0).length := by
      rw [Nat.succ_mul] at hout; omega
    have hr : (helperRoundP D j).run S = T := run_helperRoundP D S h s j (H j) (E j)
      rh re hs h1 hg h5 h6
      (by simpa only [rh, blockStream_succ, List.append_assoc] using hH)
      (by simpa only [re, blockStream_succ, List.append_assoc] using hE) (by omega)
    have hlen : (T 0).length = (S 0).length := by
      simp only [T, helperState, Function.update_of_ne (by decide : (0 : Fin 69) ≠ 3),
        Function.update_of_ne (by decide : (0 : Fin 69) ≠ 2), Function.update_self, o,
        List.length_drop, List.length_append, length_helperPairWord]
      omega
    have ht := ih T (helperOK_state D h o rh re) (j + 1)
      (by simpa [T, helperState] using hs) (by simpa [T, helperState] using h1)
      (by simpa [T, helperState] using hg) (by simpa [T, helperState] using h5)
      (by simpa [T, helperState] using h6) (by simp [T, helperState, rh])
      (by simp [T, helperState, re]) (by rw [hlen]; rw [Nat.succ_mul] at hout; omega)
    rw [helperPairsP, Prog.run_seq, hr, ht]
    have ht0 : T 0 = o := by simp [T, helperState]
    rw [ht0, show T = helperState S o rh re from rfl, helperState_idem]
    apply congrArg (fun v : List Bool ↦ helperState S v restH restE)
    simp only [o, blockStream_succ]
    rw [List.drop_append_of_le_length hn, List.append_assoc]
    conv_rhs =>
      rw [Nat.succ_mul, Nat.add_comm (n * (2 * ((D.K + D.K) * (D.N * D.K))))
        (2 * ((D.K + D.K) * (D.N * D.K))), ← List.drop_drop,
        List.drop_append_of_le_length hn]

/-- Literal-word description size on the helper machine's tapes. -/
theorem size_putW_helper (i : Fin 69) (w : List Bool) :
    (putW i w).size = 36 + 60 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [putW, Prog.size, Prim.pad, ih]; omega

/-- Both unary exponent templates together have exactly `2^b` bits. -/
theorem size_helperRoundP (t : ℕ) (ht : t ≤ D.b) :
    (helperRoundP D t).size = hBlkP.size + 144 + 60 * 2 ^ D.b := by
  have hp : 2 ^ t ≤ 2 ^ D.b := Nat.pow_le_pow_right (by decide) ht
  simp only [helperRoundP, Prog.size, size_putW_helper, List.length_replicate]
  change (36 + 60 * 2 ^ t) + ((36 + 60 * (2 ^ D.b - 2 ^ t)) +
    (hBlkP.size + (36 + 36))) = _
  omega

/-- Description size of the complete unrolled helper program, including its literal templates. -/
theorem size_helperPairsP (j n : ℕ) (hjn : j + n ≤ D.b) :
    (helperPairsP D j n).size = 36 + n * (hBlkP.size + 144 + 60 * 2 ^ D.b) := by
  induction n generalizing j with
  | zero => simp [helperPairsP, Prog.size, Prim.pad]
  | succ n ih =>
    simp only [helperPairsP, Prog.size]
    rw [size_helperRoundP D j (by omega), ih (j + 1) (by omega)]
    ring

/-- Read an exponent index in the same order as the public helper family. -/
def helperIndex (hb : 0 < D.b) (t : ℕ) : Fin D.b :=
  (Enum.list (α := Fin D.b)).getD t ⟨0, hb⟩

theorem helperIndex_val (hb : 0 < D.b) (t : ℕ) (ht : t < D.b) :
    (helperIndex D hb t).val = t := by
  unfold helperIndex
  rw [List.getD_eq_getElem _ _ (by simpa only [len_fin] using ht), Enum.getElem_fin]

/-- Pair-by-pair traversal is exactly the helper-family codec order. -/
theorem helperBlocks_codec (hb : 0 < D.b) {α : Type} {n : ℕ} (e : FixedEnc α n) (F : Jh D → α) :
    blockStream (fun t ↦ e.enc (F (helperIndex D hb t, 0)) ++
      e.enc (F (helperIndex D hb t, 1))) 0 D.b = (FixedEnc.fun (α := Jh D) e).enc F := by
  have hp (t : ℕ) : e.enc (F (helperIndex D hb t, 0)) ++ e.enc (F (helperIndex D hb t, 1)) =
      (FixedEnc.fun (α := Fin 2) e).enc (fun u ↦ F (helperIndex D hb t, u)) :=
    (fun_fin2_enc e (fun u : Fin 2 ↦ F (helperIndex D hb t, u))).symm
  simp_rw [hp]
  have he := blockStream_enum (fun t : Fin D.b ↦
    (FixedEnc.fun (α := Fin 2) e).enc (fun u ↦ F (t, u))) ⟨0, hb⟩
  simp only [len_fin] at he
  rw [show blockStream (fun t ↦ (FixedEnc.fun (α := Fin 2) e).enc
    (fun u ↦ F (helperIndex D hb t, u))) 0 D.b = _ from he]
  simp [FixedEnc.fun, FixedEnc.encList, Jh, Enum.list, List.product,
    List.flatMap_map, List.flatMap_assoc]

/-- The complete helper output stream is the ciphertext's `h` field. -/
theorem helperPairs_codec (hb : 0 < D.b) (mpk : MPKt D)
    (x : PE.BranchingProgram.Attribute PE.BranchingProgram.w8) (μ : Bool)
    (r : EncCoins (setting D) (Wb D) (Jh D) Pos) :
    blockStream (fun t ↦ helperPairWord D r.s t
      (fun u ↦ mpk.H (helperIndex D hb t, u)) (fun u ↦ r.eh (helperIndex D hb t, u))) 0 D.b =
      (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc
        (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r).h := by
  rw [← helperBlocks_codec D hb (vecE D (Col D.K))
    (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r).h]
  unfold blockStream
  apply List.flatMap_congr
  intro t ht
  have ht' : t < D.b := by simpa using ht
  have hv := helperIndex_val D hb t ht'
  simp [helperPairWord, helperRow, encrypt, helpers, helperMap, je, hv]
  rfl

/-- The full executable helper phase writes the scheme's `h` field and consumes its input families. -/
theorem run_helperPairsP_ciphertext (S : Store 69) (h : HelperOK D S) (hb : 0 < D.b)
    (mpk : MPKt D) (x : PE.BranchingProgram.Attribute PE.BranchingProgram.w8) (μ : Bool)
    (r : EncCoins (setting D) (Wb D) (Jh D) Pos)
    (hs : S 1 = wd D r.s) (h1 : S 7 = wd D 1) (hg : (S 4).length = gD D)
    (h5 : S 5 = []) (h6 : S 6 = [])
    (hH : S 2 = (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc mpk.H)
    (hE : S 3 = (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc r.eh)
    (hout : D.b * (2 * ((D.K + D.K) * (D.N * D.K))) ≤ (S 0).length) :
    (helperPairsP D 0 D.b).run S = helperState S
      ((S 0 ++ (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc
        (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r).h).drop
          (D.b * (2 * ((D.K + D.K) * (D.N * D.K))))) [] [] := by
  have hr := run_helperPairsP D S h r.s
    (fun t u ↦ mpk.H (helperIndex D hb t, u)) (fun t u ↦ r.eh (helperIndex D hb t, u))
    0 D.b [] [] hs h1 hg h5 h6
    (by rw [helperBlocks_codec D hb (matE D (Fin 2) (Col D.K)) mpk.H, List.append_nil]; exact hH)
    (by rw [helperBlocks_codec D hb (vecE D (Col D.K)) r.eh, List.append_nil]; exact hE) hout
  rw [helperPairs_codec D hb mpk x μ r] at hr
  exact hr

end AdvancedEncryption.ExpLUT.Prog.EncW
