import PE.Impl.ExpLUT.Prog.EncCore

/-! # Fixed-field loading for the concrete encryption core -/
namespace AdvancedEncryption.ExpLUT.Prog.EncW

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.Prog Matrix

/-- Core tapes followed by the coin/public streams and three loader scratch tapes. -/
def coreTape (i : Fin 321) : Fin 326 := ⟨i.val, by omega⟩
def sourceTape (i : Fin 2) : Fin 326 := ⟨321 + i.val, by omega⟩
def readMap (src : Fin 2) (dst : Fin 321) : Fin 5 → Fin 326 :=
  ![sourceTape src, coreTape dst, 324, 325, 323]

theorem readMap_inj (src : Fin 2) (dst : Fin 321) : Function.Injective (readMap src dst) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [readMap, sourceTape, coreTape, Fin.ext_iff] at h ⊢ <;> omega

/-- Read a fixed-size field, overwriting its destination and clearing the length template. -/
def readFieldP (src : Fin 2) (dst : Fin 321) (n : ℕ) : SigabaNeo.Tape.Prog 326 :=
  .seq (putW 323 (List.replicate n false))
    (.seq (cp (coreTape dst) 323) (.seq (Prog.map (readMap src dst) mvP) (clr 323)))

theorem run_readFieldP (src : Fin 2) (dst : Fin 321) (n : ℕ) (S : Store 326)
    (h323 : S 323 = []) (h324 : S 324 = []) (h325 : S 325 = []) :
    (readFieldP src dst n).run S = Function.update
      (Function.update S (sourceTape src) ((S (sourceTape src)).drop n))
      (coreTape dst) (takeD n (S (sourceTape src))) := by
  have hd : coreTape dst ≠ (323 : Fin 326) := by simp [coreTape, Fin.ext_iff]; omega
  have hd4 : (324 : Fin 326) ≠ coreTape dst := by simp [coreTape, Fin.ext_iff]; omega
  have hd5 : (325 : Fin 326) ≠ coreTape dst := by simp [coreTape, Fin.ext_iff]; omega
  have hs : sourceTape src ≠ (323 : Fin 326) := by simp [sourceTape, Fin.ext_iff]; omega
  have hsd : sourceTape src ≠ coreTape dst := by simp [sourceTape, coreTape, Fin.ext_iff]; omega
  simp only [readFieldP, Prog.run_seq, run_putW, run_copy, run_clear]
  rw [run_mvP_map (readMap_inj src dst) _
    (by simp [readMap, hd4, h324]) (by simp [readMap, hd5, h325])]
  simp [readMap, hd.symm, hs, hsd]
  funext i
  by_cases hi : i = coreTape dst <;> by_cases hj : i = sourceTape src <;>
    by_cases hk : i = 323 <;> simp_all

theorem wf_readFieldP (src : Fin 2) (dst : Fin 321) (n : ℕ) : (readFieldP src dst n).WF :=
  ⟨wf_putW _ _, trivial, wf_mvP.map (readMap_inj src dst), trivial⟩

theorem coinFree_readFieldP (src : Fin 2) (dst : Fin 321) (n : ℕ) :
    (readFieldP src dst n).CoinFree := by
  have hm : mvP.CoinFree := rfl
  simp only [readFieldP, Prog.CoinFree, Prog.coinFreeB, Bool.and_eq_true]
  exact ⟨coinFree_putW _ _, trivial, coinFree_mapP _ hm, trivial⟩

/-- The loader instruction set contains only stream reads, copies, and literal words. -/
inductive InitOp where
  | read (src : Fin 2) (dst : Fin 321) (n : ℕ)
  | copy (dst src : Fin 321)
  | word (dst : Fin 321) (w : List Bool)

def InitOp.program : InitOp → SigabaNeo.Tape.Prog 326
  | .read src dst n => readFieldP src dst n
  | .copy dst src => cp (coreTape dst) (coreTape src)
  | .word dst w => putW (coreTape dst) w

def InitOp.eval : InitOp → Store 326 → Store 326
  | .read src dst n, S => Function.update
      (Function.update S (sourceTape src) ((S (sourceTape src)).drop n))
      (coreTape dst) (takeD n (S (sourceTape src)))
  | .copy dst src, S => Function.update S (coreTape dst) (S (coreTape src))
  | .word dst w, S => Function.update S (coreTape dst) w

def InitClean (S : Store 326) : Prop := S 323 = [] ∧ S 324 = [] ∧ S 325 = []

theorem InitOp.run (op : InitOp) (S : Store 326) (h : InitClean S) :
    op.program.run S = op.eval S := by
  cases op with
  | read src dst n => exact run_readFieldP src dst n S h.1 h.2.1 h.2.2
  | copy dst src => rfl
  | word dst w => exact run_putW _ _ _

theorem InitOp.clean (op : InitOp) (S : Store 326) (h : InitClean S) :
    InitClean (op.eval S) := by
  have hc (d : Fin 321) (i : Fin 326) (hi : 323 ≤ i.val) : i ≠ coreTape d := by
    simp [coreTape, Fin.ext_iff]; omega
  have hs (d : Fin 2) (i : Fin 326) (hi : 323 ≤ i.val) : i ≠ sourceTape d := by
    simp [sourceTape, Fin.ext_iff]; omega
  cases op <;> simp [InitOp.eval, InitClean, hc, hs] at h ⊢ <;> exact h

def initProgram : List InitOp → SigabaNeo.Tape.Prog 326
  | [] => cp 0 0
  | op :: ops => .seq op.program (initProgram ops)

def initEval (ops : List InitOp) (S : Store 326) : Store 326 :=
  ops.foldl (fun T op ↦ op.eval T) S

theorem run_initProgram (ops : List InitOp) (S : Store 326) (h : InitClean S) :
    (initProgram ops).run S = initEval ops S := by
  induction ops generalizing S with
  | nil => simp [initProgram, initEval, run_copy]
  | cons op ops ih =>
    rw [initProgram, Prog.run_seq, op.run S h, ih _ (op.clean S h)]
    rfl

theorem InitOp.wf (op : InitOp) : op.program.WF := by
  cases op with
  | read src dst n => exact wf_readFieldP src dst n
  | copy dst src => trivial
  | word dst w => exact wf_putW _ _

theorem InitOp.coinFree (op : InitOp) : op.program.CoinFree := by
  cases op with
  | read src dst n => exact coinFree_readFieldP src dst n
  | copy dst src => rfl
  | word dst w => exact coinFree_putW _ _

theorem wf_initProgram (ops : List InitOp) : (initProgram ops).WF := by
  induction ops with
  | nil => trivial
  | cons op ops ih => exact ⟨op.wf, ih⟩

theorem coinFree_initProgram (ops : List InitOp) : (initProgram ops).CoinFree := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    simp only [initProgram, Prog.CoinFree, Prog.coinFreeB, Bool.and_eq_true]
    exact ⟨op.coinFree, ih⟩

def fixedSize {α : Type} {n : ℕ} (_ : FixedEnc α n) : ℕ := n

variable (D : Dims)

/-- Public fields and the two trailing plaintext fields, in their wire order. -/
def publicInitOps : List InitOp :=
  [.read 1 (bSlot 4) (fixedSize (matE D (Fin 2) (BCol (Wb D) D.K))),
   .read 1 (helperSlot 2) (fixedSize (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K)))),
   .copy (autSlot 2) (helperSlot 2),
   .read 1 (tailSlot 4) (fixedSize (FixedEnc.fun (α := Pos) (vecE D (Col D.K)))),
   .copy (tailSlot 5) (tailSlot 4), .copy (tailSlot 6) (tailSlot 4),
   .read 1 (tailSlot 11) (fixedSize (matE D (Fin 2) (Col D.K))),
   .read 1 (tailSlot 9) (fixedSize (FixedEnc.fun (α := Pos)
     (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K))))),
   .read 1 (autSlot 4) (fixedSize (FixedEnc.fun (α := Fin D.b)
     (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K))))),
   .read 1 (tailSlot 13) (fixedSize (vecE D (Fin 2))),
   .read 1 (tailSlot 2) 128, .copy (tailSlot 3) (tailSlot 2), .read 1 (tailSlot 15) 1]

/-- Coin fields in sampler order, with the copies needed to recompute helper and input rows. -/
def coinInitOps : List InitOp :=
  [.read 0 (bSlot 1) (D.N * D.K),
   .copy (helperSlot 1) (bSlot 1), .copy (autSlot 1) (bSlot 1), .copy (tailSlot 1) (bSlot 1),
   .read 0 (bSlot 5) (fixedSize (vecE D (BCol (Wb D) D.K))),
   .read 0 (helperSlot 3) (fixedSize (FixedEnc.fun (α := Jh D) (vecE D (Col D.K)))),
   .copy (autSlot 3) (helperSlot 3),
   .read 0 (autSlot 5) (fixedSize (FixedEnc.fun (α := Fin D.b)
     (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))))),
   .read 0 (tailSlot 7) (fixedSize (FixedEnc.fun (α := Pos) (vecE D (Col D.K)))),
   .copy (tailSlot 8) (tailSlot 7),
   .read 0 (tailSlot 10) (fixedSize (FixedEnc.fun (α := Pos)
     (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))))),
   .read 0 (tailSlot 12) (fixedSize (vecE D (Col D.K))), .read 0 (tailSlot 14) (D.N * D.K)]

/-- A literal unary template, charged as part of the loader program. -/
def zeroInit (dst : Fin 321) (n : ℕ) : InitOp := .word dst (List.replicate n false)

/-- Keep the large subtraction symbolic while installing rotation templates. -/
def rotationLength (i : Fin 8) : ℕ :=
  if wSt * 2 ^ (7 - i.val) ≤ 2 * D.N then 2 * D.N - wSt * 2 ^ (7 - i.val) else 0

theorem rotationLength_eq (i : Fin 8) : rotationLength D i =
    2 * D.N - wSt * 2 ^ (7 - i.val) := by
  unfold rotationLength
  split_ifs with h
  · rfl
  · omega

/-- All lengths, ring constants, and output capacity used by the four phases. -/
noncomputable def templateInitOps : List InitOp :=
  let nk := D.N * D.K
  let row := (D.K + D.K) * nk
  let cols := (Enum.list (α := BCol (Wb D) D.K)).length
  [zeroInit 0 (fixedSize (ctEnc D)),
   zeroInit (bSlot 2) nk, zeroInit (bSlot 3) nk,
   zeroInit (bSlot 6) D.K, zeroInit (bSlot 7) D.N, zeroInit (bSlot 8) nk,
   zeroInit (bSlot 9) cols, zeroInit (bSlot 10) (D.K - 1),
   zeroInit (bSlot 11) row, zeroInit (bSlot 12) (cols * nk), zeroInit (bSlot 13) ((cols + cols) * nk),
   zeroInit (helperSlot 4) (gD D), .word (helperSlot 7) (wd D 1),
   zeroInit (helperSlot 8) D.K, zeroInit (helperSlot 9) D.N, zeroInit (helperSlot 10) nk,
   zeroInit (helperSlot 11) (D.K + D.K), zeroInit (helperSlot 12) (D.K - 1),
   zeroInit (helperSlot 13) row, zeroInit (helperSlot 14) row,
   zeroInit (helperSlot 15) ((D.K + D.K + (D.K + D.K)) * nk),
   zeroInit (autSlot 6) (gD D), .word (autSlot 9) (wd D 1),
   zeroInit (autSlot 10) D.K, zeroInit (autSlot 11) D.N, zeroInit (autSlot 12) nk,
   zeroInit (autSlot 13) (D.K + D.K), zeroInit (autSlot 14) (D.K - 1),
   zeroInit (autSlot 15) row, zeroInit (autSlot 16) row,
   zeroInit (autSlot 17) ((D.K + D.K + (D.K + D.K)) * nk),
   zeroInit (autSlot 18) 1, zeroInit (autSlot 19) (D.K + D.K + (D.K + D.K)),
   .word (tailSlot 16) (wd D 1)] ++
  (List.finRange 8).map (fun i ↦ zeroInit (tailSlot ⟨17 + i.val, by omega⟩)
    (rotationLength D i)) ++
  [zeroInit (tailSlot 25) D.K, zeroInit (tailSlot 26) D.N, zeroInit (tailSlot 27) nk,
   zeroInit (tailSlot 28) (D.K + D.K), zeroInit (tailSlot 29) (D.K - 1),
   zeroInit (tailSlot 30) row, zeroInit (tailSlot 31) row,
   zeroInit (tailSlot 32) ((D.K + D.K + (D.K + D.K)) * nk), zeroInit (tailSlot 33) 1,
   zeroInit (tailSlot 34) (D.K + D.K + (D.K + D.K)), zeroInit (tailSlot 35) 16,
   zeroInit (tailSlot 36) 1, zeroInit (tailSlot 37) nk, zeroInit (tailSlot 38) (2 * nk)]

noncomputable def encInitOps : List InitOp :=
  publicInitOps D ++ coinInitOps D ++ templateInitOps D

noncomputable def encInitP : SigabaNeo.Tape.Prog 326 := initProgram (encInitOps D)

theorem run_encInitP (S : Store 326) (h : InitClean S) :
    (encInitP D).run S = initEval (encInitOps D) S := run_initProgram _ _ h

theorem wf_encInitP : (encInitP D).WF := wf_initProgram _
theorem coinFree_encInitP : (encInitP D).CoinFree := coinFree_initProgram _

/-- An encoded field is copied exactly, leaving the following stream intact. -/
theorem run_readFieldP_encoded {α : Type} {n : ℕ} (e : FixedEnc α n) (a : α)
    (src : Fin 2) (dst : Fin 321) (rest : List Bool) (S : Store 326)
    (h : InitClean S) (hsrc : S (sourceTape src) = e.enc a ++ rest) :
    (readFieldP src dst n).run S =
      Function.update (Function.update S (sourceTape src) rest) (coreTape dst) (e.enc a) := by
  have ht : takeD n (e.enc a ++ rest) = e.enc a := by
    rw [takeD_eq_take (by simp [e.length])]
    simpa only [e.length a] using (@List.take_left Bool (e.enc a) rest)
  have hd : (e.enc a ++ rest).drop n = rest := by
    simpa only [e.length a] using (@List.drop_left Bool (e.enc a) rest)
  rw [run_readFieldP src dst n S h.1 h.2.1 h.2.2, hsrc, ht, hd]

theorem initEval_clean (ops : List InitOp) (S : Store 326) (h : InitClean S) :
    InitClean (initEval ops S) := by
  induction ops generalizing S with
  | nil => exact h
  | cons op ops ih => exact ih (op.eval S) (op.clean S h)

/-- Initialization followed by the concrete encryption core on the same machine. -/
noncomputable def initializedCoreP : SigabaNeo.Tape.Prog 326 :=
  .seq (encInitP D) (Prog.map coreTape (encCoreP D))

theorem coreTape_inj : Function.Injective coreTape := by
  intro i j h
  exact Fin.ext (congrArg (fun t : Fin 326 ↦ t.val) h)

theorem wf_initializedCoreP : (initializedCoreP D).WF :=
  ⟨wf_encInitP D, (wf_encCoreP D).map coreTape_inj⟩

theorem coinFree_initializedCoreP : (initializedCoreP D).CoinFree := by
  simp only [initializedCoreP, Prog.CoinFree, Prog.coinFreeB, Bool.and_eq_true]
  exact ⟨coinFree_encInitP D, coinFree_mapP coreTape (coinFree_encCoreP D)⟩

/-- The actual initialized core executes on exactly the loader's computed tape state. -/
theorem run_initializedCoreP (S : Store 326) (h : InitClean S) :
    (initializedCoreP D).run S 0 =
      (encCoreP D).run (initEval (encInitOps D) S ∘ coreTape) 0 := by
  rw [initializedCoreP, Prog.run_seq, run_encInitP D S h, run_map coreTape_inj]
  change Function.extend coreTape _ _ (coreTape 0) = _
  rw [coreTape_inj.extend_apply]

theorem size_putW_init (i : Fin 326) (w : List Bool) :
    (putW i w).size = 36 + 60 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [putW, Prog.size, Prim.pad, ih]; omega

def InitOp.cost : InitOp → ℕ
  | .read _ _ n => mvP.size + 108 + 60 * n
  | .copy _ _ => 36
  | .word _ w => 36 + 60 * w.length

theorem InitOp.size (op : InitOp) : op.program.size = op.cost := by
  cases op with
  | read src dst n =>
    simp only [InitOp.program, readFieldP, Prog.size, size_map, size_putW_init,
      List.length_replicate, InitOp.cost]
    change (36 + 60 * n) + (36 + (mvP.size + 36)) = _
    omega
  | copy dst src => rfl
  | word dst w => exact size_putW_init _ _

theorem size_initProgram (ops : List InitOp) :
    (initProgram ops).size = 36 + (ops.map InitOp.cost).sum := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    simp only [initProgram, Prog.size, op.size, ih, List.map_cons, List.sum_cons]
    omega

/-- Description size includes every loaded unary template and every literal constant. -/
theorem size_initializedCoreP : (initializedCoreP D).size =
    36 + ((encInitOps D).map InitOp.cost).sum + (encCoreP D).size := by
  simp only [initializedCoreP, Prog.size, encInitP, size_initProgram, size_map]

end AdvancedEncryption.ExpLUT.Prog.EncW
