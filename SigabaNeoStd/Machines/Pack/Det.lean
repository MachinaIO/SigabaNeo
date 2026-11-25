import SigabaNeoStd.Machines.Pack.States
import SigabaNeoStd.Machines.Prog.DetX

/-!
# Coin-free programs give deterministic packed machines

`CoinIndep` (`SigabaNeoStd.Machines.Prog.DetX`: the transitions ignore the coin) is preserved by
the plumbing of the segment phases (`outputToTape`, `inputFromTape`, hence `outputToWord`,
`inputFromWord`, `onWords`, `trPhase`), so the read and replace phases ignore the coin
(`coinIndep_getPh`, `coinIndep_putPh`). A program of `ZProg` whose framed leaves are coin-free and
whose phases ignore the coin (`ZProg.CI`) compiles to a machine ignoring the coin, so the packing
translation of a coin-free framed program does too, and

**`deterministic_packMachineT`**: `p.CoinFree → (packMachineT w D p i₀ o n).Deterministic`.
-/

namespace SigabaNeo.Tape

open Cslib Turing MultiTapeMachine MultiTapePTM Function

variable {k : ℕ}

/-! ### Plumbing -/

theorem CoinIndep.outputToTape {S : Type} {m : MultiTapePTM k Bool S Empty} (h : CoinIndep m) :
    CoinIndep (MultiTapeMachine.outputToTape m) := by
  intro q a w o
  show OutputToTape.instruction (m.tr q a (fun i => w i.castSucc) o true) =
    OutputToTape.instruction (m.tr q a (fun i => w i.castSucc) o false)
  rw [h]

theorem CoinIndep.inputFromTape {S : Type} {m : MultiTapePTM k Bool S Empty} (h : CoinIndep m) :
    CoinIndep (MultiTapeMachine.inputFromTape m) := by
  intro q a w o
  show InputFromTape.instruction (w (Fin.natAdd k 0)) (w (Fin.natAdd k 1))
      (m.tr q (w (Fin.natAdd k 0)) (fun i => w (i.castAdd 2)) o true) =
    InputFromTape.instruction (w (Fin.natAdd k 0)) (w (Fin.natAdd k 1))
      (m.tr q (w (Fin.natAdd k 0)) (fun i => w (i.castAdd 2)) o false)
  rw [h]

theorem CoinIndep.outputToWord {S : Type} {m : MultiTapePTM k Bool S Empty} (h : CoinIndep m) :
    CoinIndep (MultiTapePTM.outputToWord m) :=
  h.outputToTape.seq (coinIndep_ofDeterministic _)

theorem CoinIndep.inputFromWord {S : Type} {m : MultiTapePTM k Bool S Empty} (h : CoinIndep m)
    (mark : Bool) : CoinIndep (MultiTapePTM.inputFromWord m mark) :=
  (coinIndep_ofDeterministic _).seq (h.inputFromTape.seq (coinIndep_ofDeterministic _))

theorem CoinIndep.onWords {S : Type} {m : MultiTapePTM k Bool S Empty} (h : CoinIndep m)
    (mark : Bool) : CoinIndep (MultiTapePTM.onWords m mark) :=
  h.outputToWord.inputFromWord mark

theorem coinIndep_trPhase {Q : Type} [Finite Q] (τ : MultiTapeTM.Transducer Bool Q)
    (e : Fin 3 ↪ Fin k) : CoinIndep (trPhase τ e) :=
  ((coinIndep_ofDeterministic _).onWords true).extendTapes e

/-! ### Framed programs with native phases -/

namespace ZProg

/-- The framed leaves are coin-free and the phases ignore the coin. -/
def CI : ZProg k → Prop
  | xp p => p.CoinFree
  | ph P => CoinIndep P.machine
  | seq p q => CI p ∧ CI q
  | ifBlank _ p q => CI p ∧ CI q
  | ifBit _ p q => CI p ∧ CI q
  | loop _ b => CI b

theorem coinIndep_compile : ∀ p : ZProg k, p.CI → CoinIndep p.compile
  | xp p, h => XProg.coinIndep_compile p h
  | ph _, h => h
  | seq p q, h => (coinIndep_compile p h.1).seq (coinIndep_compile q h.2)
  | ifBlank i p q, h => CoinIndep.branch i (coinIndep_compile q h.2) (coinIndep_compile p h.1)
  | ifBit i p q, h => CoinIndep.branchBit i (coinIndep_compile p h.1) (coinIndep_compile q h.2)
  | loop i b, h => CoinIndep.branch i (CoinIndep.repeatUntilBlank i
      ((coinIndep_ofDeterministic _).seq (coinIndep_compile b h))) (coinIndep_ofDeterministic _)

/-- **A program with coin-free leaves and coin-ignoring phases gives a deterministic machine.** -/
theorem deterministic_toMachineZ (p : ZProg k) (h : p.CI) (i₀ o : Fin k) (n t lo : ℕ) :
    (p.toMachineZ i₀ o n t lo).Deterministic :=
  deterministic_ofPTM (((coinIndep_ofDeterministic _).seq (coinIndep_compile p h)).seq
    (coinIndep_ofDeterministic _)) _

end ZProg

namespace Pack

/-! ### The segment phases -/

theorem coinIndep_getPh (j : ℕ) (t st fl : Fin k) : CoinIndep (getPh j t st fl).machine := by
  unfold getPh
  by_cases h : t ≠ st ∧ t ≠ fl ∧ st ≠ fl
  · rw [dif_pos h]; exact coinIndep_trPhase _ _
  · rw [dif_neg h]; exact coinIndep_ofDeterministic _

theorem coinIndep_emitTr {Q : Type} [Finite Q] (τ : MultiTapeTM.Transducer Bool Q)
    (e : Fin 2 ↪ Fin k) : CoinIndep (emitTr τ e) :=
  ((coinIndep_ofDeterministic _).inputFromWord true).extendTapes e

theorem coinIndep_putLocal (j : ℕ) : CoinIndep (putLocal j) :=
  ((coinIndep_emitTr _ _).seq ((coinIndep_emitTr _ _).seq (coinIndep_emitTr _ _))).outputToWord.seq
    (Prog.coinIndep_compile _ coinFree_putTail)

theorem coinIndep_putPh (j : ℕ) (t st fl B : Fin k) : CoinIndep (putPh j t st fl B).machine := by
  unfold putPh
  by_cases h : [st, t, fl, B].Nodup
  · rw [dif_pos h]; exact (coinIndep_putLocal j).extendTapes _
  · rw [dif_neg h]; exact coinIndep_ofDeterministic _

/-! ### The translation -/

variable {K c w D : ℕ} (lay : Layout c w D) (kit : Kit K c lay.st)

/-- The segment phases of a kit ignore the coin. -/
def KitCI : Prop := ∀ (j : Fin K) (t : Fin c), CoinIndep (kit.get j t).machine ∧
  CoinIndep (kit.put j t).machine

variable {lay kit}

theorem ci_seqL_ph (Ps : List (Phase c)) (hP : ∀ P ∈ Ps, CoinIndep P.machine) {q : ZProg c}
    (hq : q.CI) : (seqL (Ps.map ZProg.ph) q).CI := by
  induction Ps with
  | nil => exact hq
  | cons P Ps ih =>
    exact ⟨hP P (by simp), ih (fun P' hP' => hP P' (by simp [hP']))⟩

theorem ci_skipZ : (skipZ (lay := lay)).CI := rfl

theorem ci_leaf (hk : KitCI lay kit) {m : ℕ} (σ : Fin m ↪ Fin K) (h : m ≤ w) {p : XProg m}
    (hp : p.CoinFree) : (leaf lay kit σ h p).CI := by
  unfold leaf
  have e1 : ((List.finRange m).map fun j => ZProg.ph (kit.get (σ j) (wsE lay h j))) =
      ((List.finRange m).map fun j => kit.get (σ j) (wsE lay h j)).map ZProg.ph := by
    simp [List.map_map]
  have e2 : ((List.finRange m).map fun j => ZProg.ph (kit.put (σ j) (wsE lay h j))) =
      ((List.finRange m).map fun j => kit.put (σ j) (wsE lay h j)).map ZProg.ph := by
    simp [List.map_map]
  rw [e1, e2]
  refine ci_seqL_ph _ (fun P hP => ?_) ⟨hp, ci_seqL_ph _ (fun P hP => ?_) ci_skipZ⟩
  · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hP; exact (hk _ _).1
  · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hP; exact (hk _ _).2

theorem ci_orNarrow (hk : KitCI lay kit) {k : ℕ} (σ : Fin k ↪ Fin K) {q : Prog k}
    (hq : q.CoinFree) {alt : ZProg c} (halt : alt.CI) : (orNarrow lay kit σ q alt).CI := by
  unfold orNarrow
  split_ifs with h
  · exact ci_leaf hk _ _ (XProg.coinFree_prog (Prog.coinFree_mapP _ hq))
  · exact halt

theorem ci_orLeaf (hk : KitCI lay kit) {k : ℕ} (σ : Fin k ↪ Fin K) {p : XProg k}
    (hp : p.CoinFree) {alt : ZProg c} (halt : alt.CI) : (orLeaf lay kit σ p alt).CI := by
  unfold orLeaf
  split_ifs with h
  · exact ci_leaf hk _ _ hp
  · exact halt

theorem ci_testZ (hk : KitCI lay kit) (j : Fin K) (bit : Bool) {p q : ZProg c} (hp : p.CI)
    (hq : q.CI) : (testZ lay kit j bit p q).CI := by
  unfold testZ
  refine ⟨(hk _ _).1, ?_⟩
  cases bit
  · exact ⟨⟨rfl, hp⟩, ⟨rfl, hq⟩⟩
  · exact ⟨⟨rfl, hp⟩, ⟨rfl, hq⟩⟩

theorem ci_tailZ (hk : KitCI lay kit) (j : Fin K) : (tailZ lay kit j).CI :=
  ⟨(hk _ _).1, rfl, (hk _ _).2⟩

theorem ci_loopAt (hk : KitCI lay kit) (j : Fin K) (d : ℕ) {b : ZProg c} (hb : b.CI) :
    (loopAt lay kit j d b).CI := by
  unfold loopAt
  split_ifs with hd
  · exact ⟨(hk _ _).1, ci_tailZ hk j, hb⟩
  · exact ci_skipZ

theorem coinFreeB_seq {k : ℕ} {p q : Prog k} (h : (Prog.seq p q).CoinFree) :
    p.CoinFree ∧ q.CoinFree := by
  simp only [Prog.CoinFree, Prog.coinFreeB, Bool.and_eq_true] at h; exact h

theorem ci_trP (hk : KitCI lay kit) {k : ℕ} (σ : Fin k ↪ Fin K) :
    ∀ (d : ℕ) (q : Prog k), q.CoinFree → (trP lay kit σ d q).CI
  | _, .prim _, h => ci_orNarrow hk σ h ci_skipZ
  | _, .coin _, h => ci_orNarrow hk σ h ci_skipZ
  | d, .seq p q, h => by
    have h' : p.CoinFree ∧ q.CoinFree := by
      simp only [Prog.CoinFree, Prog.coinFreeB, Bool.and_eq_true] at h; exact h
    exact ci_orNarrow hk σ h ⟨ci_trP hk σ d p h'.1, ci_trP hk σ d q h'.2⟩
  | d, .ifBlank i p q, h => by
    have h' : p.CoinFree ∧ q.CoinFree := by
      simp only [Prog.CoinFree, Prog.coinFreeB, Bool.and_eq_true] at h; exact h
    exact ci_orNarrow hk σ h (ci_testZ hk _ _ (ci_trP hk σ d p h'.1) (ci_trP hk σ d q h'.2))
  | d, .ifBit i p q, h => by
    have h' : p.CoinFree ∧ q.CoinFree := by
      simp only [Prog.CoinFree, Prog.coinFreeB, Bool.and_eq_true] at h; exact h
    exact ci_orNarrow hk σ h (ci_testZ hk _ _ (ci_trP hk σ d p h'.1) (ci_trP hk σ d q h'.2))
  | d, .loop i b, h => ci_orNarrow hk σ h (ci_loopAt hk _ _ (ci_trP hk σ (d + 1) b h))

theorem ci_tr (hk : KitCI lay kit) : ∀ {k : ℕ} (σ : Fin k ↪ Fin K) (d : ℕ) (p : XProg k),
    p.CoinFree → (tr lay kit σ d p).CI
  | _, σ, d, .prog q, h => ci_orLeaf hk σ h (ci_trP hk σ d q h)
  | _, σ, d, .frame e q, h => ci_orLeaf hk σ h (ci_tr hk (e.trans σ) d q h)
  | _, σ, d, .seq p q, h => by
    have h' : p.CoinFree ∧ q.CoinFree := by
      simp only [XProg.CoinFree, XProg.coinFreeB, Bool.and_eq_true] at h; exact h
    exact ci_orLeaf hk σ h ⟨ci_tr hk σ d p h'.1, ci_tr hk σ d q h'.2⟩
  | _, σ, d, .ifBlank i p q, h => by
    have h' : p.CoinFree ∧ q.CoinFree := by
      simp only [XProg.CoinFree, XProg.coinFreeB, Bool.and_eq_true] at h; exact h
    exact ci_orLeaf hk σ h (ci_testZ hk _ _ (ci_tr hk σ d p h'.1) (ci_tr hk σ d q h'.2))
  | _, σ, d, .ifBit i p q, h => by
    have h' : p.CoinFree ∧ q.CoinFree := by
      simp only [XProg.CoinFree, XProg.coinFreeB, Bool.and_eq_true] at h; exact h
    exact ci_orLeaf hk σ h (ci_testZ hk _ _ (ci_tr hk σ d p h'.1) (ci_tr hk σ d q h'.2))
  | _, σ, d, .loop i b, h => ci_orLeaf hk σ h (ci_loopAt hk _ _ (ci_tr hk σ (d + 1) b h))

theorem kitCI_packKit : KitCI (packLayout w D) (packKit K w D) := fun j t =>
  ⟨coinIndep_getPh _ _ _ _, coinIndep_putPh _ _ _ _ _⟩

/-- **The packed machine of a coin-free program is deterministic.** -/
theorem deterministic_packMachineT (p : XProg K) (hp : p.CoinFree) (i₀ o : Fin K) (n : ℕ) :
    (packMachineT w D p i₀ o n).Deterministic :=
  ZProg.deterministic_toMachineZ _ (by
    unfold topZ
    exact ⟨XProg.coinFree_prog (Prog.coinFree_snocN _ _ _), coinIndep_putPh _ _ _ _ _,
      ci_tr kitCI_packKit _ 0 p hp, coinIndep_getPh _ _ _ _⟩) _ _ _ _ _

end Pack

end SigabaNeo.Tape
