import PE.Impl.ExpLUT.Prog.KeyTimeInvalid
import PE.Impl.ExpLUT.Prog.KeySizeConf
import PE.Impl.ExpLUT.Prog.EncTimeConf
import PE.Impl.ExpLUT.AH.Games
import SigabaNeo.Lib.Machines.Prog.LoadB
import SigabaNeo.Lib.Machines.Prog.AppendWCost

/-!
# The guarded KeyGen machine: specification, long predicates, clock and cost

`keyGuardP` runs a length guard on the loaded input before the KeyGen program: inputs longer than
the framed bound `keyInputBound D L` produce the empty output. `keyMB` is the machine of this
program with the bounded loader (`toMachineB`), so it satisfies both `KeySpec` and
`KeyLongSpec`. The clock is bounded through the actual compiler bounds of the parser, the length
check, both key branches and the output frame.
-/

set_option exponentiation.threshold 2000

namespace AdvancedEncryption.ExpLUT.Prog.KeyCore
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.Prog Cslib Cslib.Probability
open AdvancedEncryption.ExpLUT.Params
open AdvancedEncryption.ExpLUT.Prog.EncW (XBound)

/-! ### The length guard on 105 tapes -/

/-- `103 := [true]` if `|s 0| ≤ n`, `[]` otherwise; tape `104` is scratch. -/
def guardP (n : ℕ) : SigabaNeo.Tape.Prog 105 :=
  prim (.clear 103) ⨾ prim (.copy 104 0) ⨾ tailsP 104 n ⨾
    ifBlank 104 (prim (.snoc 103 true)) (prim (.copy 103 103)) ⨾ prim (.clear 104)

theorem run_guardP (n : ℕ) (s : Store 105) :
    run (guardP n) s = Function.update (Function.update s 103
      (if (s 0).length ≤ n then [true] else [])) 104 [] := by
  simp only [guardP, run_seq, run_prim, Prim.apply, run_tailsP, run_ifBlank]
  by_cases h : (s 0).length ≤ n
  · have hd : (s 0).drop n = [] := List.drop_eq_nil_of_le (by omega)
    simp [hd, h, Function.update_comm (show (103 : Fin 105) ≠ 104 by decide)]
  · have hd : (s 0).drop n ≠ [] := by
      intro e; have := congrArg List.length e; simp at this; omega
    simp [hd, h, Function.update_comm (show (103 : Fin 105) ≠ 104 by decide)]

theorem coinFree_guardP (n : ℕ) : (guardP n).CoinFree := by
  have := coinFree_tailsP (104 : Fin 105) n
  simp only [CoinFree] at this
  simp [CoinFree, guardP, coinFreeB, this]

theorem wf_guardP (n : ℕ) : (guardP n).WF :=
  ⟨trivial, trivial, wf_tailsP 104 n, ⟨trivial, trivial⟩, trivial⟩

theorem ubp_guardP (n M : ℕ) : UBP (guardP n) M (leT n M) (M + 1) := by
  have h := (ubp_prim0 (k := 105) (.clear 103) rfl M).seq ((ubp_prim0 (.copy 104 0) rfl M).seq
    ((ubp_tailsP 104 n M).seq ((ubp_ifBlank (i := 104) (ubp_prim (.snoc 103 true) M)
      (ubp_prim0 (.copy 103 103) rfl M)).seq (ubp_prim0 (.clear 104) rfl _))))
  refine h.mono ?_ (by simp only [max_def]; split_ifs <;> omega)
  simp only [leT, max_def]
  split_ifs <;> nlinarith

theorem size_tailsP_le {k : ℕ} (i : Fin k) : ∀ n, (tailsP i n).size ≤ 60 * (n + 1)
  | 0 => size_prim_le' _
  | n + 1 => by
    have h1 := size_prim_le' (Prim.tail i)
    have h2 := size_tailsP_le i n
    show (prim (Prim.tail i)).size + (tailsP i n).size ≤ _
    omega

theorem size_guardP_le (n : ℕ) : (guardP n).size ≤ 60 * (n + 10) := by
  have h := size_tailsP_le (104 : Fin 105) n
  have a1 := size_prim_le' (k := 105) (.clear 103)
  have a2 := size_prim_le' (k := 105) (.copy 104 0)
  have a3 := size_prim_le' (k := 105) (.snoc 103 true)
  have a4 := size_prim_le' (k := 105) (.copy 103 103)
  have a5 := size_prim_le' (k := 105) (.clear 104)
  show (prim (.clear 103)).size + ((prim (.copy 104 0)).size + ((tailsP 104 n).size +
    (((prim (.snoc 103 true)).size + (prim (.copy 103 103)).size + 1) +
      (prim (.clear 104)).size))) ≤ _
  omega

/-! ### The guarded program -/

/-- Guard the input length, then run KeyGen; overlong inputs give the empty output. -/
noncomputable def keyGuardP (D : Dims) (B r n : ℕ) : XProg 105 :=
  .seq (.prog (guardP n))
    (.ifBit 103 (.seq (.prog (clr 103)) (keyProgram D B r)) (.prog (clr 0)))

theorem wf_keyGuardP (D : Dims) (B r n : ℕ) : (keyGuardP D B r n).WF :=
  ⟨wf_guardP n, ⟨trivial, wf_keyProgram D B r⟩, trivial⟩

theorem law_ifBit {k : ℕ} (i : Fin k) (p q : XProg k) (s : Store k) :
    (XProg.ifBit i p q).law s = if (s i).head? = some true then p.law s else q.law s := by
  change (if (s i).head? = some true then p.denote s else q.denote s).eval = _
  split_ifs <;> rfl

theorem law_keyGuardP_short (D : Dims) (B r n : ℕ) (x : List Bool) (hx : x.length ≤ n) :
    (keyGuardP D B r n).law (inputStore 0 x) = (keyProgram D B r).law (inputStore 0 x) := by
  rw [keyGuardP, XProg.law_seq, XProg.law_prog,
    Prog.law_eq_run_of_coinFree _ (coinFree_guardP n), run_guardP, PMF.pure_bind, law_ifBit]
  have h0 : inputStore (0 : Fin 105) x 0 = x := by simp [inputStore]
  simp only [h0, hx, ite_true, Function.update_of_ne (show (103 : Fin 105) ≠ 104 by decide),
    Function.update_self, List.head?_cons]
  rw [XProg.law_seq, XProg.law_prog, Prog.law_eq_run_of_coinFree _ (by rfl), run_clear,
    PMF.pure_bind]
  congr 1
  funext t
  by_cases h3 : t = 103
  · subst h3; simp [inputStore]
  · by_cases h4 : t = 104
    · subst h4; simp [inputStore]
    · simp [Function.update_of_ne h3, Function.update_of_ne h4]

theorem law_keyGuardP_long (D : Dims) (B r n : ℕ) (x : List Bool) (hx : n < x.length) :
    ((keyGuardP D B r n).law (inputStore 0 x)).map (fun s ↦ s 0) = PMF.pure [] := by
  rw [keyGuardP, XProg.law_seq, XProg.law_prog,
    Prog.law_eq_run_of_coinFree _ (coinFree_guardP n), run_guardP, PMF.pure_bind, law_ifBit]
  have h0 : inputStore (0 : Fin 105) x 0 = x := by simp [inputStore]
  have hn : ¬ x.length ≤ n := by omega
  simp only [h0, hn, ite_false, Function.update_of_ne (show (103 : Fin 105) ≠ 104 by decide),
    Function.update_self, List.head?_nil, reduceCtorEq, ite_false]
  rw [XProg.law_prog, Prog.law_eq_run_of_coinFree _ (by rfl), run_clear, PMF.pure_map]
  simp

/-! ### The machine -/

/-- **The guarded KeyGen machine**: the bounded loader reads at most `keyInputBound D L + 1`
bits. -/
noncomputable def keyMB (D : Dims) (B r L : ℕ) : Machine :=
  (keyGuardP D B r (keyInputBound D L)).toMachineB 0 0 (keyInputBound D L)

theorem length_keyInput (D : Dims) (msk : MSKt D) (C : List Bool) :
    (encodeTuple [pwW, (mskEnc D).enc msk, C]).length =
      (2 * pwW.length + 1) + (2 * codecSize (mskEnc D) + 1) + (2 * C.length + 1) := by
  have hm : ((mskEnc D).enc msk).length = codecSize (mskEnc D) := (mskEnc D).length msk
  simp only [encodeTuple_cons, encodeTuple_nil, List.length_append, length_frame,
    List.length_nil, hm]
  omega

theorem run_keyMB_short (D : Dims) (B r L : ℕ) (x : List Bool) (hx : x.length ≤ keyInputBound D L) :
    (keyMB D B r L).run x = (keyMP D B r L).run x := by
  rw [keyMB, keyMP, XProg.run_toMachineB _ (wf_keyGuardP D B r _),
    XProg.run_toMachineT _ (wf_keyProgram D B r) 0 0 _ x hx,
    List.take_of_length_le (by omega), law_keyGuardP_short D B r _ x hx]

theorem keySpec_keyMB_Dc (L : ℕ) : KeySpec Dc kbDc L (keyMB Dc Bk rSmall L) := by
  intro msk C hC
  rw [run_keyMB_short _ _ _ _ _ (length_keyInput_le Dc L msk C hC)]
  exact keySpec_keyMP_Dc L msk C hC

theorem keyLongSpec_keyMB (D : Dims) (B r L : ℕ) : KeyLongSpec D L (keyMB D B r L) := by
  intro msk C hC
  rw [keyMB, XProg.run_toMachineB _ (wf_keyGuardP D B r _)]
  have hl := length_keyInput D msk C
  apply law_keyGuardP_long
  rw [List.length_take, hl, keyInputBound]
  omega

/-! ### Compiler bounds of the pieces -/

theorem xbound_ifBit {k : ℕ} {i : Fin k} {p q : XProg k} {M T U M' : ℕ}
    (hp : XBound p M T M') (hq : XBound q M U M') : XBound (.ifBit i p q) M (max T U + 1) M' :=
  fun ℓ hℓ => ⟨by
    show max _ _ + 1 ≤ _
    have := (hp ℓ hℓ).1; have := (hq ℓ hℓ).1; omega,
    fun t => by show max _ _ ≤ _; exact max_le ((hp ℓ hℓ).2 t) ((hq ℓ hℓ).2 t)⟩

theorem xbound_prog {k : ℕ} {p : SigabaNeo.Tape.Prog k} {M T M' : ℕ} (h : UBP p M T M') :
    XBound (.prog p) M T M' := fun ℓ hℓ => h ℓ hℓ

theorem bounds_keyParse : UBP parse (2 ^ 105) (2 ^ 230) (2 ^ 108) := by
  have h1 := EncW.ubp_unfr_mapped (EncIO.parseMap 4) (2 ^ 105)
  have h2 := EncW.ubp_unfr_mapped (EncIO.parseMap 1) (2 * 2 ^ 105)
  have h3 := EncW.ubp_unfr_mapped (EncIO.parseMap 5) (2 * (2 * 2 ^ 105))
  have h4 := ubp_prim0 (.copy (0 : Fin 105) 1) rfl (2 * (2 * (2 * 2 ^ 105)))
  have h5 := ubp_prim0 (.copy (1 : Fin 105) 5) rfl (2 * (2 * (2 * 2 ^ 105)))
  have h6 := ubp_prim0 (.clear (4 : Fin 105)) rfl (2 * (2 * (2 * 2 ^ 105)))
  have h7 := ubp_prim0 (.clear (5 : Fin 105)) rfl (2 * (2 * (2 * 2 ^ 105)))
  exact (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7)))))).mono
    (by norm_num [unfrT]) (by norm_num)

theorem checkP_eq : checkP = natU 3 5 6 predLen ⨾ cp 4 1 ⨾ dropT 4 3 5 ⨾
    ifBlank 4 (dropT 3 1 5 ⨾ ifBlank 3 (setB 2 true) (setB 2 false)) (setB 2 false) ⨾
      clr 3 ⨾ clr 4 :=
  map_lenEqP checkMap predLen

theorem bounds_checkP {S : ℕ} (hn : predLen ≤ S) (h1 : 1 ≤ S) :
    UBP checkP S ((12 * predLen + 6 * S + 120) * (2 * S + 5)) S := by
  rw [checkP_eq]
  let U : SigabaNeo.Tape.Prog 105 → ℕ → Prop := fun p m =>
    ∀ ℓ : Fin 105 → ℕ, (∀ t, ℓ t ≤ S) → timeBoundT p ℓ ≤ m * (2 * S + 5) ∧
      ∀ t, lenBoundT p ℓ t ≤ S
  have seqU : ∀ {p q m m'}, U p m → U q m' → U (p ⨾ q) (m + m') := fun hp hq ℓ hℓ => by
    have a := hp ℓ hℓ; have b := hq _ a.2
    exact ⟨by rw [timeBoundT_seq, Nat.add_mul]; omega, b.2⟩
  have primU : ∀ q : Prim 105, q.grow = 0 → U (prim q) 1 := fun q hq ℓ hℓ => by
    refine ⟨?_, fun t => ?_⟩
    · show 2 * (supB ℓ + q.pad) + 3 ≤ _
      have := supB_le_of hℓ; have : q.pad ≤ 1 := by cases q <;> simp [Prim.pad]
      omega
    · exact ((Prim.lenT_mono q (fun u => hℓ u)) t).trans
        ((Prim.lenT_const_le q S t).trans (show S + q.grow ≤ S by omega))
  have setU : ∀ (f : Fin 105) (b : Bool), U (setB f b) 2 := fun f b ℓ hℓ => by
    refine ⟨?_, fun t => ?_⟩
    · show 2 * (supB ℓ + 0) + 3 + (2 * (supB (Prim.lenT (.clear f) ℓ) + 1) + 3) ≤ _
      have := supB_le_of hℓ
      have : supB (Prim.lenT (.clear f) ℓ) ≤ S := supB_le_of fun u => by
        simp only [Prim.lenT, Function.update_apply]; split_ifs
        · exact Nat.zero_le _
        · exact hℓ u
      omega
    · show Prim.lenT (.snoc f b) (Prim.lenT (.clear f) ℓ) t ≤ _
      simp only [Prim.lenT, Function.update_apply]; split_ifs <;> first | omega | exact hℓ t
  have dropU : ∀ t x a : Fin 105, t ≠ a → x ≠ a → U (dropT t x a) (3 * S + 3) :=
    fun t x a hta hxa ℓ hℓ => by
      have h := dropT_bounds hta hxa ℓ hℓ
      refine ⟨h.1.trans (Nat.mul_le_mul_right (2 * S + 5)
        (show 3 * ℓ x + 3 ≤ 3 * S + 3 by have := hℓ x; omega)), fun u => (h.2 u).trans ?_⟩
      simp only [Function.update_apply]; split_ifs
      · exact hℓ x
      · exact hℓ u
  have natUU : U (natU 3 5 6 predLen) (12 * predLen + 100) := fun ℓ hℓ => by
    have h := natU_bounds (o := (3 : Fin 105)) (a := 5) (b := 6) (by decide) (by decide)
      (by decide) predLen ℓ hℓ hn
    refine ⟨h.1, fun u => (h.2 u).trans ?_⟩
    split_ifs
    · exact hn
    · exact max_le (hℓ u) hn
    · exact hℓ u
  have ifU : ∀ (i : Fin 105) {p q m}, U p m → U q m → U (ifBlank i p q) (m + 1) :=
    fun i p q m hp hq ℓ hℓ => by
      have a := hp ℓ hℓ; have b := hq ℓ hℓ
      refine ⟨?_, fun t => max_le (a.2 t) (b.2 t)⟩
      show max _ _ + 1 ≤ _; rw [Nat.add_mul, Nat.one_mul]; have := max_le a.1 b.1; omega
  have monoU : ∀ {p m m'}, U p m → m ≤ m' → U p m' := fun hp hm ℓ hℓ =>
    ⟨(hp ℓ hℓ).1.trans (Nat.mul_le_mul_right _ hm), (hp ℓ hℓ).2⟩
  have hB : U (dropT 3 1 5 ⨾ ifBlank 3 (setB 2 true) (setB 2 false)) (3 * S + 3 + 3) :=
    seqU (dropU 3 1 5 (by decide) (by decide)) (ifU 3 (setU 2 true) (setU 2 false))
  have h := seqU natUU (seqU (primU (.copy 4 1) rfl) (seqU (dropU 4 3 5 (by decide) (by decide))
    (seqU (ifU 4 hB (monoU (setU 2 false) (by omega)))
      (seqU (primU (.clear 3) rfl) (primU (.clear 4) rfl)))))
  exact fun ℓ hℓ => monoU h (by omega) ℓ hℓ

/-- The emitter of `frameKeyP` as a deterministic program. -/
def outFrameBody105 : SigabaNeo.Tape.Prog 105 :=
  .seq (.prim (.snoc 0 true)) (.seq (.prim (.snocHead 0 2)) (.prim (.tail 2)))

def outFrameP105 : SigabaNeo.Tape.Prog 105 :=
  .seq (.seq (cp 1 0) (clr 0))
    (.seq (.seq (cp 2 1) (.seq (forN 3 1 outFrameBody105)
      (.seq (.prim (.snoc 0 false)) (clr 2)))) (clr 1))

theorem bounds_frameKeyP : XBound frameKeyP (2 ^ 121) (2 ^ 250) (2 ^ 123) := by
  have hp := (ubp_prim0 (.copy (1 : Fin 105) 0) rfl (2 ^ 121)).seq
    (ubp_prim0 (.clear 0) rfl (2 ^ 121))
  have hc := ubp_prim0 (.copy (2 : Fin 105) 1) rfl (2 ^ 121)
  have hcounter := ubp_prim0 (.copy (3 : Fin 105) 1) rfl (2 ^ 121)
  have hb : ∀ M, UBP outFrameBody105 M (10 * (M + 3)) (M + 2) := fun M => by
    have h := (ubp_prim (.snoc (0 : Fin 105) true) M).seq
      ((ubp_prim (.snocHead 0 2) (M + 1)).seq (ubp_prim0 (.tail 2) rfl (M + 1 + 1)))
    exact h.mono (by omega) (by omega)
  have hl := ubp_loop (3 : Fin 105) outFrameBody105 2 _ hb (2 ^ 121)
  have he := (ubp_prim (.snoc (0 : Fin 105) false) (2 ^ 121 + 2 * 2 ^ 121)).seq
    (ubp_prim0 (.clear 2) rfl (2 ^ 121 + 2 * 2 ^ 121 + 1))
  have hlast := ubp_prim0 (.clear (1 : Fin 105)) rfl (2 ^ 121 + 2 * 2 ^ 121 + 1)
  have h := hp.seq ((hc.seq ((hcounter.seq hl).seq he)).seq hlast)
  have hb' := h.mono (by norm_num : _ ≤ 2 ^ 250) (by norm_num : _ ≤ 2 ^ 123)
  intro ℓ hℓ
  have e1 : XProg.timeBoundT frameKeyP ℓ = timeBoundT outFrameP105 ℓ := rfl
  have e2 : XProg.lenBoundT frameKeyP ℓ = lenBoundT outFrameP105 ℓ := rfl
  rw [e1, e2]
  exact hb' ℓ hℓ

theorem bounds_branches (r : ℕ) :
    XBound (.ifBit 2 (validP Dc Bk r) (invalidP Dc)) (2 ^ 120) (2 ^ 505) (2 ^ 121) := by
  have hv : XBound (validP Dc Bk r) (2 ^ 120) (2 ^ 504) (2 ^ 121) := fun ℓ hℓ => by
    have c := KeyTime.cert_validP_uniform r ℓ hℓ
    refine ⟨c.time, fun t => (c.len t).trans ?_⟩
    simp only [KeyTime.outputBounds]; split_ifs <;> norm_num
  have hi : XBound (invalidP Dc) (2 ^ 120) (2 ^ 254) (2 ^ 121) := fun ℓ hℓ => by
    have c := KeyTime.cert_invalidP_Dc ℓ hℓ
    refine ⟨c.time, fun t => (c.len t).trans ?_⟩
    simp only [KeyTime.outputBounds]; split_ifs <;> norm_num
  exact (xbound_ifBit hv hi).mono (by norm_num) le_rfl

theorem bounds_keyProgram (r : ℕ) :
    XBound (keyProgram Dc Bk r) (2 ^ 105) (2 ^ 506) (2 ^ 123) := by
  have hp : XBound (.prog parse) (2 ^ 105) (2 ^ 230) (2 ^ 120) :=
    (xbound_prog bounds_keyParse).mono le_rfl (by norm_num)
  have hc : XBound (.prog checkP) (2 ^ 120) (2 ^ 250) (2 ^ 120) :=
    (xbound_prog (bounds_checkP (by norm_num [predLen]) (by norm_num))).mono
      (by norm_num [predLen]) le_rfl
  have h := hp.seq ((hc.seq (bounds_branches r)).seq bounds_frameKeyP)
  exact h.mono (by norm_num) le_rfl

theorem bounds_keyGuardP (r n : ℕ) :
    XBound (keyGuardP Dc Bk r n) (2 ^ 104) (leT n (2 ^ 104) + (2 ^ 507)) (2 ^ 123) := by
  have hg : XBound (.prog (guardP n)) (2 ^ 104) (leT n (2 ^ 104)) (2 ^ 105) :=
    (xbound_prog (ubp_guardP n (2 ^ 104))).mono le_rfl (by norm_num)
  have hk : XBound (.seq (.prog (clr 103)) (keyProgram Dc Bk r)) (2 ^ 105)
      (2 * (2 ^ 105 + 1) + 3 + 2 ^ 506) (2 ^ 123) :=
    (xbound_prog (ubp_prim0 (.clear (103 : Fin 105)) rfl (2 ^ 105))).seq (bounds_keyProgram r)
  have hz : XBound (.prog (clr (0 : Fin 105))) (2 ^ 105) (2 * (2 ^ 105 + 1) + 3) (2 ^ 123) :=
    (xbound_prog (ubp_prim0 (.clear (0 : Fin 105)) rfl (2 ^ 105))).mono le_rfl (by norm_num)
  exact (hg.seq (xbound_ifBit hk hz)).mono (by
    have : max (2 * (2 ^ 105 + 1) + 3 + 2 ^ 506) (2 * (2 ^ 105 + 1) + 3) + 1 ≤ 2 ^ 507 := by
      norm_num
    omega) le_rfl

/-! ### The concrete machine: clock and description -/

theorem time_toMachineB_eq {k : ℕ} (p : XProg k) (i o : Fin k) (n : ℕ) :
    (p.toMachineB i o n).time = XProg.totalTimeT p i o (n + 1) := rfl

theorem descLen_toMachineB105 (p : XProg 105) (n : ℕ) :
    (p.toMachineB 0 0 n).descLen =
      6 * (p.size + (n + 3) + 2) * 3 ^ 105 * 3 ^ 0 *
        Machine.entryBits 105 (p.size + (n + 3) + 2) 0 := by
  rw [Machine.descLen, XProg.states_toMachineB, XProg.card_state]
  rfl

theorem size_keyGuardP (D : Dims) (B r n : ℕ) :
    (keyGuardP D B r n).size = (guardP n).size + ((prim (.clear 103) : SigabaNeo.Tape.Prog 105).size +
      (keyProgram D B r).size + (prim (.clear 0) : SigabaNeo.Tape.Prog 105).size + 1) := rfl

theorem codecSize_mskEnc (D : Dims) :
    codecSize (mskEnc D) = codecSize (mpkEnc D) + codecSize (matE D (Wb D) (Fin D.K)) := rfl

theorem codecSize_mskEnc_Dc : codecSize (mskEnc Dc) ≤ 2 ^ 101 := by
  rw [codecSize_mskEnc]
  obtain ⟨hp, ht⟩ := keyCodec_lengths Dc
  rw [hp, ht]
  norm_num [Dc, Kc, mbar, PE.BranchingProgram.w8, PE.BranchingProgram.Width.len]

theorem keyInputBound_Dc : keyInputBound Dc predLen ≤ 2 ^ 103 := by
  have hm := codecSize_mskEnc_Dc
  have hw := EncConf.pwW_length_le
  simp only [keyInputBound]
  have : predLen ≤ 2 ^ 30 := by norm_num [predLen]
  omega

/-- The configured KeyGen machine, predicates of at most `predLen` bits. -/
noncomputable def keyMachine : Machine := keyMB Dc Bk rSmall predLen

theorem keySpec_keyMachine : KeySpec Dc kbDc predLen keyMachine := keySpec_keyMB_Dc predLen

theorem keyLongSpec_keyMachine : KeyLongSpec Dc predLen keyMachine :=
  keyLongSpec_keyMB Dc Bk rSmall predLen

theorem time_keyGuard_le (n : ℕ) (hn : n ≤ 2 ^ 103) :
    XProg.totalTimeT (keyGuardP Dc Bk rSmall n) 0 0 (n + 1) ≤ 2 ^ 508 := by
  have h := (bounds_keyGuardP rSmall n).total (0 : Fin 105) 0 (n := n + 1) (by omega)
  have hl : leT n (2 ^ 104) ≤ 2 ^ 300 := by
    simp only [leT]
    have : n + 5 ≤ 2 ^ 104 := by omega
    calc (n + 5) * (2 * (2 ^ 104 + 2) + 3) + 1
        ≤ 2 ^ 104 * (2 * (2 ^ 104 + 2) + 3) + 1 := by gcongr
      _ ≤ 2 ^ 300 := by norm_num
  refine h.trans ?_
  have : (2 * 2 ^ 104 + 2) + (2 ^ 300 + 2 ^ 507) + (2 * 2 ^ 123 + 2) ≤ (2 : ℕ) ^ 508 := by
    norm_num
  refine le_trans ?_ this
  gcongr

theorem size_keyGuard_le (n : ℕ) (hn : n ≤ 2 ^ 103) :
    (keyGuardP Dc Bk rSmall n).size + (n + 3) + 2 ≤ 2 ^ 221 := by
  have hg := size_guardP_le n
  have hk := size_keyProgram_Dc_pow
  have h1 := size_prim_le' (k := 105) (.clear 103)
  have h0 := size_prim_le' (k := 105) (.clear 0)
  have e := size_keyGuardP Dc Bk rSmall n
  have : (2 : ℕ) ^ 221 = 2 ^ 220 + 2 ^ 220 := by norm_num
  have : 60 * (2 ^ 103 + 10) + 2 ^ 103 + 200 ≤ (2 : ℕ) ^ 220 := by norm_num
  omega

theorem descLen_keyGuard_le (n : ℕ) (hn : n ≤ 2 ^ 103) :
    ((keyGuardP Dc Bk rSmall n).toMachineB 0 0 n).descLen ≤ 2 ^ 620 := by
  rw [descLen_toMachineB105]
  exact (AdvancedEncryption.DualUse.Prog.descLen_arithA (size_keyGuard_le n hn)).trans
    (by norm_num)

theorem keyMachine_eq : keyMachine =
    (keyGuardP Dc Bk rSmall (keyInputBound Dc predLen)).toMachineB 0 0
      (keyInputBound Dc predLen) := rfl

theorem time_keyMachine : keyMachine.time ≤ 2 ^ 508 := by
  rw [keyMachine_eq, time_toMachineB_eq]
  exact time_keyGuard_le _ keyInputBound_Dc

theorem descLen_keyMachine : keyMachine.descLen ≤ 2 ^ 620 := by
  rw [keyMachine_eq]
  exact descLen_keyGuard_le _ keyInputBound_Dc

theorem cost_keyMachine_lt : keyMachine.cost < 2 ^ 818 :=
  EncConf.machine_cost_lt keyMachine time_keyMachine descLen_keyMachine (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.KeyCore
