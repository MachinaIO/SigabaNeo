import PE.Impl.ExpLUT.Prog.EncHelpers

/-! # Executable automorphism rounds with explicit exponent templates -/
namespace AdvancedEncryption.ExpLUT.Prog.EncW

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.Prog Matrix

variable (D : Dims)

def autRoundP (t : ℕ) : SigabaNeo.Tape.Prog 85 :=
  .seq (putW 7 (List.replicate (2 ^ t) false))
    (.seq (putW 8 (List.replicate (2 ^ D.b - 2 ^ t) false))
      (.seq autBlkP (.seq (clr 7) (clr 8))))

def autBlocksP (j : ℕ) : ℕ → SigabaNeo.Tape.Prog 85
  | 0 => cp 0 0
  | n + 1 => .seq (autRoundP D j) (autBlocksP (j + 1) n)

theorem wf_autRoundP (t : ℕ) : (autRoundP D t).WF :=
  ⟨wf_putW _ _, wf_putW _ _, wf_autBlkP, trivial, trivial⟩

theorem wf_autBlocksP (j n : ℕ) : (autBlocksP D j n).WF := by
  induction n generalizing j with
  | zero => trivial
  | succ n ih => exact ⟨wf_autRoundP D j, ih (j + 1)⟩

theorem coinFree_autRoundP (t : ℕ) : (autRoundP D t).CoinFree := by
  have hh : autBlkP.CoinFree := rfl
  simp only [autRoundP, Prog.CoinFree, Prog.coinFreeB, Bool.and_eq_true]
  exact ⟨coinFree_putW _ _, coinFree_putW _ _, hh, trivial, trivial⟩

theorem coinFree_autBlocksP (j n : ℕ) : (autBlocksP D j n).CoinFree := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    simp only [autBlocksP, Prog.CoinFree, Prog.coinFreeB, Bool.and_eq_true]
    exact ⟨coinFree_autRoundP D j, ih (j + 1)⟩

def autState (S : Store 85) (o H Eh A E : List Bool) : Store 85 :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update S 0 o) 2 H) 3 Eh) 4 A) 5 E

theorem autState_idem (S : Store 85) (o H Eh A E o' H' Eh' A' E' : List Bool) :
    autState (autState S o H Eh A E) o' H' Eh' A' E' = autState S o' H' Eh' A' E' := by
  funext i
  by_cases h0 : i = 0 <;> by_cases h2 : i = 2 <;> by_cases h3 : i = 3 <;>
    by_cases h4 : i = 4 <;> by_cases h5 : i = 5 <;> simp [autState, h0, h2, h3, h4, h5]

theorem autBlockOK_state {S : Store 85} (h : AutBlockOK D S) (o H Eh A E : List Bool) :
    AutBlockOK D (autState S o H Eh A E) := by
  constructor
  · intro i hi
    have h0 : i ≠ 0 := by intro he; subst he; simp at hi
    have h2 : i ≠ 2 := by intro he; subst he; simp at hi
    have h3 : i ≠ 3 := by intro he; subst he; simp at hi
    have h4 : i ≠ 4 := by intro he; subst he; simp at hi
    have h5 : i ≠ 5 := by intro he; subst he; simp at hi
    simp [autState, h0, h2, h3, h4, h5, h.scratch i hi]
  all_goals simp [autState, h.hK, h.hN, h.hNK, h.h13, h.hK1, h.h15,
    h.h16, h.h17, h.h18, h.h19]

noncomputable def autBlockWord (s : Rg D) (t : ℕ)
    (H : Fin 2 → Fin 2 → Col D.K → Rg D) (Eh : Fin 2 → Col D.K → Rg D)
    (A : Dig D.K → Fin 2 → Col D.K → Rg D) (E : Dig D.K → Col D.K → Rg D) : List Bool :=
  (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc
    (digitRows D (autTW D.N D.K (gD D) (2 ^ t) (wd D s))
      (gcAut (setting D) ((setting D).idx (2 ^ t)) (H 1)
        (helperRow D s (2 ^ D.b - 2 ^ t) (H 1) (Eh 1))) A E)

set_option maxRecDepth 100000 in
/-- Install both templates, consume a full block, and restore the template registers. -/
theorem run_autRoundP (S : Store 85) (h : AutBlockOK D S) (s : Rg D) (t : ℕ)
    (H : Fin 2 → Fin 2 → Col D.K → Rg D) (Eh : Fin 2 → Col D.K → Rg D)
    (A : Dig D.K → Fin 2 → Col D.K → Rg D) (E : Dig D.K → Col D.K → Rg D)
    (restH restEh restA restE : List Bool)
    (hs : S 1 = wd D s) (h1 : S 9 = wd D 1) (hg : (S 6).length = gD D)
    (h7 : S 7 = []) (h8 : S 8 = [])
    (hH : S 2 = (matE D (Fin 2) (Col D.K)).enc (H 0) ++
      ((matE D (Fin 2) (Col D.K)).enc (H 1) ++ restH))
    (hEh : S 3 = (vecE D (Col D.K)).enc (Eh 0) ++ ((vecE D (Col D.K)).enc (Eh 1) ++ restEh))
    (hA : S 4 = (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K))).enc A ++ restA)
    (hE : S 5 = (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc E ++ restE)
    (hout : (D.K + D.K + (D.K + D.K)) *
      (D.K * ((D.K + D.K) * (D.N * D.K))) ≤ (S 0).length) :
    (autRoundP D t).run S = autState S
      ((S 0 ++ autBlockWord D s t H Eh A E).drop
        ((D.K + D.K + (D.K + D.K)) * (D.K * ((D.K + D.K) * (D.N * D.K)))))
      restH restEh restA restE := by
  let T := Function.update (Function.update S 7 (List.replicate (2 ^ t) false))
    8 (List.replicate (2 ^ D.b - 2 ^ t) false)
  have hT : AutBlockOK D T := by
    constructor
    · intro i hi
      have h7' : i ≠ 7 := by intro he; subst he; simp at hi
      have h8' : i ≠ 8 := by intro he; subst he; simp at hi
      simp [T, h7', h8', h.scratch i hi]
    all_goals simp [T, h.hK, h.hN, h.hNK, h.h13, h.hK1, h.h15,
      h.h16, h.h17, h.h18, h.h19]
  have hr := run_autBlkP_encoded D T hT s (2 ^ t) (2 ^ D.b - 2 ^ t)
    (H 0) (H 1) (Eh 0) (Eh 1) A E restH restEh restA restE
    (by simpa [T] using hs) (by simpa [T] using h1) (by simpa [T] using hg)
    (by simp [T]) (by simp [T]) (by simpa [T] using hH) (by simpa [T] using hEh)
    (by simpa [T] using hA) (by simpa [T] using hE) (by simpa [T] using hout)
  simp only [autRoundP, Prog.run_seq, run_putW, run_clear]
  change Function.update (Function.update (autBlkP.run T) 7 []) 8 [] = _
  rw [hr]
  funext i
  fin_cases i <;> simp [autState, T, h7, h8, autBlockWord]

theorem size_putW_aut (i : Fin 85) (w : List Bool) :
    (putW i w).size = 36 + 60 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [putW, Prog.size, Prim.pad, ih]; omega

/-- Both unary exponent templates together have exactly `2^b` bits. -/
theorem size_autRoundP (t : ℕ) (ht : t ≤ D.b) :
    (autRoundP D t).size = autBlkP.size + 144 + 60 * 2 ^ D.b := by
  have hp : 2 ^ t ≤ 2 ^ D.b := Nat.pow_le_pow_right (by decide) ht
  simp only [autRoundP, Prog.size, size_putW_aut, List.length_replicate]
  change (36 + 60 * 2 ^ t) + ((36 + 60 * (2 ^ D.b - 2 ^ t)) +
    (autBlkP.size + (36 + 36))) = _
  omega

/-- Description size of the complete unrolled automorphism program, including its literal templates. -/
theorem size_autBlocksP (j n : ℕ) (hjn : j + n ≤ D.b) :
    (autBlocksP D j n).size = 36 + n * (autBlkP.size + 144 + 60 * 2 ^ D.b) := by
  induction n generalizing j with
  | zero => simp [autBlocksP, Prog.size, Prim.pad]
  | succ n ih =>
    simp only [autBlocksP, Prog.size]
    rw [size_autRoundP D j (by omega), ih (j + 1) (by omega)]
    ring


theorem length_autBlockWord (s : Rg D) (t : ℕ)
    (H : Fin 2 → Fin 2 → Col D.K → Rg D) (Eh : Fin 2 → Col D.K → Rg D)
    (A : Dig D.K → Fin 2 → Col D.K → Rg D) (E : Dig D.K → Col D.K → Rg D) :
    (autBlockWord D s t H Eh A E).length =
      (D.K + D.K + (D.K + D.K)) * (D.K * ((D.K + D.K) * (D.N * D.K))) :=
  length_digitFamily D _

/-- All consecutive automorphism blocks consume their four streams in order. -/
theorem run_autBlocksP (S : Store 85) (h : AutBlockOK D S) (s : Rg D)
    (H : ℕ → Fin 2 → Fin 2 → Col D.K → Rg D) (Eh : ℕ → Fin 2 → Col D.K → Rg D)
    (A : ℕ → Dig D.K → Fin 2 → Col D.K → Rg D) (E : ℕ → Dig D.K → Col D.K → Rg D)
    (j n : ℕ) (restH restEh restA restE : List Bool)
    (hs : S 1 = wd D s) (h1 : S 9 = wd D 1) (hg : (S 6).length = gD D)
    (h7 : S 7 = []) (h8 : S 8 = [])
    (hH : S 2 = blockStream (fun t ↦ (matE D (Fin 2) (Col D.K)).enc (H t 0) ++
      (matE D (Fin 2) (Col D.K)).enc (H t 1)) j n ++ restH)
    (hEh : S 3 = blockStream (fun t ↦ (vecE D (Col D.K)).enc (Eh t 0) ++
      (vecE D (Col D.K)).enc (Eh t 1)) j n ++ restEh)
    (hA : S 4 = blockStream (fun t ↦
      (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K))).enc (A t)) j n ++ restA)
    (hE : S 5 = blockStream (fun t ↦
      (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc (E t)) j n ++ restE)
    (hout : n * ((D.K + D.K + (D.K + D.K)) *
      (D.K * ((D.K + D.K) * (D.N * D.K)))) ≤ (S 0).length) :
    (autBlocksP D j n).run S = autState S
      ((S 0 ++ blockStream (fun t ↦ autBlockWord D s t (H t) (Eh t) (A t) (E t)) j n).drop
        (n * ((D.K + D.K + (D.K + D.K)) * (D.K * ((D.K + D.K) * (D.N * D.K))))))
      restH restEh restA restE := by
  induction n generalizing S j with
  | zero =>
    simp only [blockStream_zero, List.nil_append] at hH hEh hA hE
    simp [autBlocksP, run_copy, autState, ← hH, ← hEh, ← hA, ← hE]
  | succ n ih =>
    let rh := blockStream (fun t ↦ (matE D (Fin 2) (Col D.K)).enc (H t 0) ++
      (matE D (Fin 2) (Col D.K)).enc (H t 1)) (j + 1) n ++ restH
    let reh := blockStream (fun t ↦ (vecE D (Col D.K)).enc (Eh t 0) ++
      (vecE D (Col D.K)).enc (Eh t 1)) (j + 1) n ++ restEh
    let ra := blockStream (fun t ↦
      (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K))).enc (A t)) (j + 1) n ++ restA
    let re := blockStream (fun t ↦
      (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc (E t)) (j + 1) n ++ restE
    let L := (D.K + D.K + (D.K + D.K)) * (D.K * ((D.K + D.K) * (D.N * D.K)))
    let o := (S 0 ++ autBlockWord D s j (H j) (Eh j) (A j) (E j)).drop L
    let T := autState S o rh reh ra re
    have hn : L ≤ (S 0).length := by
      change (n + 1) * L ≤ (S 0).length at hout
      rw [Nat.succ_mul] at hout; omega
    have hr : (autRoundP D j).run S = T := run_autRoundP D S h s j (H j) (Eh j) (A j) (E j)
      rh reh ra re hs h1 hg h7 h8
      (by simpa only [rh, blockStream_succ, List.append_assoc] using hH)
      (by simpa only [reh, blockStream_succ, List.append_assoc] using hEh)
      (by simpa only [ra, blockStream_succ, List.append_assoc] using hA)
      (by simpa only [re, blockStream_succ, List.append_assoc] using hE) hn
    have ht0 : T 0 = o := by simp [T, autState]
    have hlen : (T 0).length = (S 0).length := by
      rw [ht0]
      simp only [o, List.length_drop, List.length_append, length_autBlockWord]
      dsimp [L]
      omega
    have ht := ih T (autBlockOK_state D h o rh reh ra re) (j + 1)
      (by simpa [T, autState] using hs) (by simpa [T, autState] using h1)
      (by simpa [T, autState] using hg) (by simpa [T, autState] using h7)
      (by simpa [T, autState] using h8) (by simp [T, autState, rh])
      (by simp [T, autState, reh]) (by simp [T, autState, ra]) (by simp [T, autState, re])
      (by rw [hlen]; rw [Nat.succ_mul] at hout; omega)
    rw [autBlocksP, Prog.run_seq, hr, ht, ht0,
      show T = autState S o rh reh ra re from rfl, autState_idem]
    apply congrArg (fun v : List Bool ↦ autState S v restH restEh restA restE)
    change ((o ++ blockStream _ (j + 1) n).drop (n * L)) = _
    simp only [o, blockStream_succ]
    rw [List.drop_append_of_le_length hn, List.append_assoc]
    change _ = (S 0 ++ (_ ++ _)).drop ((n + 1) * L)
    conv_rhs =>
      rw [Nat.succ_mul, Nat.add_comm (n * L) L, ← List.drop_drop,
        List.drop_append_of_le_length hn]

/-- Natural-index traversal agrees with the codec of the automorphism family. -/
theorem autBlocks_codec (hb : 0 < D.b) {α : Type} {n : ℕ} (e : FixedEnc α n)
    (F : Fin D.b → α) :
    blockStream (fun t ↦ e.enc (F (helperIndex D hb t))) 0 D.b =
      (FixedEnc.fun (α := Fin D.b) e).enc F := by
  have he := blockStream_enum (fun t : Fin D.b ↦ e.enc (F t)) ⟨0, hb⟩
  simpa only [helperIndex, len_fin, FixedEnc.fun, FixedEnc.encList, List.flatMap_map] using he

/-- The output block stream is precisely the ciphertext's automorphism field. -/
theorem autOutput_codec (hb : 0 < D.b) (mpk : MPKt D)
    (x : PE.BranchingProgram.Attribute PE.BranchingProgram.w8) (μ : Bool)
    (r : EncCoins (setting D) (Wb D) (Jh D) Pos) :
    blockStream (fun t ↦ autBlockWord D r.s t
      (fun u ↦ mpk.H (helperIndex D hb t, u)) (fun u ↦ r.eh (helperIndex D hb t, u))
      (mpk.Aaut (helperIndex D hb t)) (r.eaut (helperIndex D hb t))) 0 D.b =
      (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc
        (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r).caut := by
  rw [← autBlocks_codec D hb (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))
    (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r).caut]
  unfold blockStream
  apply List.flatMap_congr
  intro t ht
  have ht' : t < D.b := by simpa using ht
  have hv := helperIndex_val D hb t ht'
  unfold autBlockWord
  rw [digitRows_autTW D r.s (2 ^ t)
    (gcAut (setting D) ((setting D).idx (2 ^ t)) (mpk.H (helperIndex D hb t, 1))
      (helperRow D r.s (2 ^ D.b - 2 ^ t) (mpk.H (helperIndex D hb t, 1))
        (r.eh (helperIndex D hb t, 1))))
    (mpk.Aaut (helperIndex D hb t)) (r.eaut (helperIndex D hb t))]
  simp [helperRow, encrypt, autGC, helpers, helperMap, je, hv]
  rfl

/-- The concrete automorphism phase writes `caut` and exhausts all four encoded families. -/
theorem run_autBlocksP_ciphertext (S : Store 85) (h : AutBlockOK D S) (hb : 0 < D.b)
    (mpk : MPKt D) (x : PE.BranchingProgram.Attribute PE.BranchingProgram.w8) (μ : Bool)
    (r : EncCoins (setting D) (Wb D) (Jh D) Pos)
    (hs : S 1 = wd D r.s) (h1 : S 9 = wd D 1) (hg : (S 6).length = gD D)
    (h7 : S 7 = []) (h8 : S 8 = [])
    (hH : S 2 = (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc mpk.H)
    (hEh : S 3 = (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc r.eh)
    (hA : S 4 = (FixedEnc.fun (α := Fin D.b)
      (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc mpk.Aaut)
    (hE : S 5 = (FixedEnc.fun (α := Fin D.b)
      (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc r.eaut)
    (hout : D.b * ((D.K + D.K + (D.K + D.K)) *
      (D.K * ((D.K + D.K) * (D.N * D.K)))) ≤ (S 0).length) :
    (autBlocksP D 0 D.b).run S = autState S
      ((S 0 ++ (FixedEnc.fun (α := Fin D.b)
        (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc
          (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r).caut).drop
            (D.b * ((D.K + D.K + (D.K + D.K)) * (D.K * ((D.K + D.K) * (D.N * D.K))))))
      [] [] [] [] := by
  have hr := run_autBlocksP D S h r.s
    (fun t u ↦ mpk.H (helperIndex D hb t, u)) (fun t u ↦ r.eh (helperIndex D hb t, u))
    (fun t ↦ mpk.Aaut (helperIndex D hb t)) (fun t ↦ r.eaut (helperIndex D hb t))
    0 D.b [] [] [] [] hs h1 hg h7 h8
    (by rw [helperBlocks_codec D hb (matE D (Fin 2) (Col D.K)) mpk.H, List.append_nil]; exact hH)
    (by rw [helperBlocks_codec D hb (vecE D (Col D.K)) r.eh, List.append_nil]; exact hEh)
    (by rw [autBlocks_codec D hb (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K))) mpk.Aaut, List.append_nil]; exact hA)
    (by rw [autBlocks_codec D hb (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))) r.eaut, List.append_nil]; exact hE) hout
  rw [autOutput_codec D hb mpk x μ r] at hr
  exact hr

end AdvancedEncryption.ExpLUT.Prog.EncW
