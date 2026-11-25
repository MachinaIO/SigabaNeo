import PE.Impl.ExpLUT.Prog.RedChalLaw
import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.VMSize

/-!
# The clock of the challenge component (package G2, `chalP`)

* **`vmTime_le`**: the clock of a code from a bound `I` on its instructions and `Bc` on its loop
  counters: `vmCount c · Bc^{depth c} · (A + I) · (depth c + 1)`, with `A` the per-round overhead;
* **`instrTime_le`**: every instruction but `mul` and `digit` costs at most
  `4 (2M + 3)(30 + 10M) + 1000 (Mo + 1)^4` when its templates fit the operation area.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedChal

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Tape.Prog.MersenneT
  SigabaNeo.Tape.Prog.SpecT SigabaNeo.Tape.Sym

/-! ### A structural clock -/

/-- The loop depth of a code. -/
def vmDepth : Code → ℕ
  | .rep _ b => vmDepth b + 1
  | .seq p q => max (vmDepth p) (vmDepth q)
  | .ifb _ p q => max (vmDepth p) (vmDepth q)
  | _ => 0

section Clock

variable (Mo N K : ℕ) (B : Fin 200 → ℕ)

/-- Every instruction costs at most `I`. -/
def LeafLe (I : ℕ) : Code → Prop
  | .rep _ b => LeafLe I b
  | .seq p q => LeafLe I p ∧ LeafLe I q
  | .ifb _ p q => LeafLe I p ∧ LeafLe I q
  | c => instrTime Mo N K B c ≤ I

/-- Every loop counter is bounded by `Bc`. -/
def RepLe (Bc : ℕ) : Code → Prop
  | .rep t b => B t ≤ Bc ∧ RepLe Bc b
  | .seq p q => RepLe Bc p ∧ RepLe Bc q
  | .ifb _ p q => RepLe Bc p ∧ RepLe Bc q
  | _ => True

theorem one_le_vmCount : ∀ c : Code, 1 ≤ vmCount c
  | .rep _ b => by simp [vmCount]
  | .seq p q => by have := one_le_vmCount p; simp only [vmCount]; omega
  | .ifb _ p q => by simp [vmCount]
  | .add .. | .sub .. | .mul .. | .canon .. | .neg .. | .digit .. | .rotB .. | .aut .. | .rhoJ ..
  | .mv .. | .cp .. | .drop .. | .clr _ | .tl _ | .nop => by simp [vmCount]

theorem X_mono {Bc A I d d' : ℕ} (hBc : 1 ≤ Bc) (h : d ≤ d') :
    Bc ^ d * (A + I) * (d + 1) ≤ Bc ^ d' * (A + I) * (d' + 1) :=
  Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hBc h)) (by omega)

/-- **The structural clock.** -/
theorem vmTime_le (A I Bc : ℕ) (hA : 2 * supB (encB Mo N K B) + 4 ≤ A) (h4 : 4 ≤ A)
    (hBc : 1 ≤ Bc) : ∀ c : Code, LeafLe Mo N K B I c → RepLe B Bc c →
      vmTime Mo N K B (instrTime Mo N K B) c ≤
        vmCount c * (Bc ^ vmDepth c * (A + I) * (vmDepth c + 1))
  | .rep t b, hl, hr => by
    have ih := vmTime_le A I Bc hA h4 hBc b hl hr.2
    simp only [vmTime, vmCount, vmDepth]
    set X := Bc ^ vmDepth b * (A + I) * (vmDepth b + 1)
    have hX : Bc * X ≤ Bc ^ (vmDepth b + 1) * (A + I) * (vmDepth b + 1 + 1) := by
      rw [pow_succ]
      calc Bc * X = Bc ^ vmDepth b * Bc * (A + I) * (vmDepth b + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
    have hP : 1 ≤ Bc ^ vmDepth b := Nat.one_le_pow _ _ hBc
    have hY : Bc * A + 2 ≤ Bc ^ (vmDepth b + 1) * (A + I) * (vmDepth b + 1 + 1) := by
      rw [pow_succ]
      have h1 : Bc * A ≤ Bc ^ vmDepth b * Bc * (A + I) :=
        calc Bc * A = 1 * Bc * A := by ring
          _ ≤ Bc ^ vmDepth b * Bc * (A + I) :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ hP) (by omega)
      have h2 : 4 ≤ Bc ^ vmDepth b * Bc * (A + I) :=
        calc 4 ≤ 1 * 1 * A := by omega
          _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul hP hBc) (by omega)
      nlinarith
    calc B t * (2 * supB (encB Mo N K B) + 3 + vmTime Mo N K B (instrTime Mo N K B) b + 1) + 2
        ≤ Bc * (A + vmCount b * X) + 2 :=
          Nat.add_le_add_right (Nat.mul_le_mul hr.1 (by omega)) 2
      _ = vmCount b * (Bc * X) + (Bc * A + 2) := by ring
      _ ≤ vmCount b * (Bc ^ (vmDepth b + 1) * (A + I) * (vmDepth b + 1 + 1)) +
          Bc ^ (vmDepth b + 1) * (A + I) * (vmDepth b + 1 + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hX) hY
      _ = _ := by ring
  | .seq p q, hl, hr => by
    have ihp := vmTime_le A I Bc hA h4 hBc p hl.1 hr.1
    have ihq := vmTime_le A I Bc hA h4 hBc q hl.2 hr.2
    simp only [vmTime, vmCount, vmDepth]
    have mp := X_mono (A := A) (I := I) hBc (le_max_left (vmDepth p) (vmDepth q))
    have mq := X_mono (A := A) (I := I) hBc (le_max_right (vmDepth p) (vmDepth q))
    calc _ ≤ _ := Nat.add_le_add ihp ihq
      _ ≤ vmCount p * (Bc ^ max (vmDepth p) (vmDepth q) * (A + I) * (max (vmDepth p) (vmDepth q) + 1)) +
          vmCount q * (Bc ^ max (vmDepth p) (vmDepth q) * (A + I) * (max (vmDepth p) (vmDepth q) + 1)) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ mp) (Nat.mul_le_mul_left _ mq)
      _ = _ := by ring
  | .ifb t p q, hl, hr => by
    have ihp := vmTime_le A I Bc hA h4 hBc p hl.1 hr.1
    have ihq := vmTime_le A I Bc hA h4 hBc q hl.2 hr.2
    simp only [vmTime, vmCount, vmDepth]
    have mp := X_mono (A := A) (I := I) hBc (le_max_left (vmDepth p) (vmDepth q))
    have mq := X_mono (A := A) (I := I) hBc (le_max_right (vmDepth p) (vmDepth q))
    set d := max (vmDepth p) (vmDepth q)
    have h1 : 1 ≤ Bc ^ d * (A + I) * (d + 1) := by
      have : 1 ≤ Bc ^ d := Nat.one_le_pow _ _ hBc
      have : 1 ≤ A + I := by omega
      calc 1 = 1 * 1 * 1 := rfl
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul ‹_› ‹_›) (by omega)
    have e1 := (Nat.mul_le_mul_left (vmCount p) mp)
    have e2 := (Nat.mul_le_mul_left (vmCount q) mq)
    calc max (vmTime Mo N K B (instrTime Mo N K B) p) (vmTime Mo N K B (instrTime Mo N K B) q) + 1
        ≤ (vmCount p * (Bc ^ d * (A + I) * (d + 1)) + vmCount q * (Bc ^ d * (A + I) * (d + 1))) +
          Bc ^ d * (A + I) * (d + 1) := by
          have := max_le (ihp.trans (e1.trans (Nat.le_add_right _ _)))
            (ihq.trans (e2.trans (Nat.le_add_left _ _)))
          omega
      _ = _ := by ring
  | .add .., hl, _ | .sub .., hl, _ | .mul .., hl, _ | .canon .., hl, _ | .neg .., hl, _
  | .digit .., hl, _ | .rotB .., hl, _ | .aut .., hl, _ | .rhoJ .., hl, _ | .mv .., hl, _
  | .cp .., hl, _ | .drop .., hl, _ | .clr _, hl, _ | .tl _, hl, _ | .nop, hl, _ => by
    simp only [vmTime, vmCount, vmDepth, pow_zero, one_mul, zero_add, mul_one]
    exact hl.trans (by omega)

end Clock

/-! ### The instructions -/

section Instr

variable {Mo N K M : ℕ} {B : Fin 200 → ℕ}

/-- The uniform bound on an instruction. -/
def IB (M Mo : ℕ) : ℕ := 4 * ((2 * M + 3) * (30 + 10 * M)) + 1000 * (Mo + 1) ^ 4

/-- The instructions allowed (no `mul`, `digit`, `neg`), templates in the operation area. -/
def TmOK (Mo : ℕ) (B : Fin 200 → ℕ) : Code → Prop
  | .rotB _ _ t => B t ≤ Mo
  | .aut _ _ t => B t ≤ Mo
  | .rhoJ _ _ t => B t ≤ Mo
  | .mul .. => False
  | .digit .. => False
  | .neg .. => False
  | .rep _ b => TmOK Mo B b
  | .seq p q => TmOK Mo B p ∧ TmOK Mo B q
  | .ifb _ p q => TmOK Mo B p ∧ TmOK Mo B q
  | _ => True

theorem poly_le {Mo N K m : ℕ} (hN : N ≤ Mo) (hK : K ≤ Mo) (hm : m ≤ Mo) (hNK : N * K ≤ Mo)
    (c0 c1 c2 c3 c4 c5 : ℕ) (hc : c0 + c1 + c2 + c3 + c4 + c5 ≤ 200) :
    c0 + c1 * N + c2 * (N * K) + c3 * m + c4 * (N * m) + c5 * (N * K * m) ≤ 200 * (Mo + 1) ^ 3 := by
  set Y := (Mo + 1) ^ 3 with hY
  have hA : Mo ≤ Y := by
    have := Nat.le_self_pow (n := 3) (by norm_num) (Mo + 1); rw [hY]; omega
  have hB : Mo * Mo ≤ Y := by
    rw [hY]
    calc Mo * Mo ≤ (Mo + 1) * (Mo + 1) * (Mo + 1) := by nlinarith
      _ = (Mo + 1) ^ 3 := by ring
  have h1 : N ≤ Y := hN.trans hA
  have h2 : N * K ≤ Y := hNK.trans hA
  have h3 : m ≤ Y := hm.trans hA
  have h4 : N * m ≤ Y := (Nat.mul_le_mul hN hm).trans hB
  have h5 : N * K * m ≤ Y := (Nat.mul_le_mul hNK hm).trans hB
  have h0 : 1 ≤ Y := Nat.one_le_pow _ _ (by omega)
  calc c0 + c1 * N + c2 * (N * K) + c3 * m + c4 * (N * m) + c5 * (N * K * m)
      ≤ c0 * Y + c1 * Y + c2 * Y + c3 * Y + c4 * Y + c5 * Y := by
        have := Nat.mul_le_mul_left c0 h0
        have := Nat.mul_le_mul_left c1 h1
        have := Nat.mul_le_mul_left c2 h2
        have := Nat.mul_le_mul_left c3 h3
        have := Nat.mul_le_mul_left c4 h4
        have := Nat.mul_le_mul_left c5 h5
        omega
    _ = (c0 + c1 + c2 + c3 + c4 + c5) * Y := by ring
    _ ≤ 200 * Y := Nat.mul_le_mul_right _ hc

theorem pEval_le_aut {m : ℕ} (hN : N ≤ Mo) (hK : K ≤ Mo) (hm : m ≤ Mo) (hNK : N * K ≤ Mo) :
    pEval (ρLd Mo N K m) wAut ≤ 200 * (Mo + 1) ^ 3 := by
  simp only [pEval, mEval, ρLd, wAut, List.foldr, List.headD_cons, List.tail_cons, pow_zero,
    pow_one, one_mul, mul_one]
  have := poly_le hN hK hm hNK 10 55 40 0 8 14 (by norm_num)
  nlinarith

theorem pEval_le_rotB {m : ℕ} (hN : N ≤ Mo) (hK : K ≤ Mo) (hm : m ≤ Mo) (hNK : N * K ≤ Mo) :
    pEval (ρLd Mo N K m) wRotB ≤ 200 * (Mo + 1) ^ 3 := by
  simp only [pEval, mEval, ρLd, wRotB, List.foldr, List.headD_cons, List.tail_cons, pow_zero,
    pow_one, one_mul, mul_one]
  have := poly_le hN hK hm hNK 3 0 0 11 19 18 (by norm_num)
  nlinarith

theorem pEval_le_rhoJ {m : ℕ} (hN : N ≤ Mo) (hK : K ≤ Mo) (hm : m ≤ Mo) (hNK : N * K ≤ Mo) :
    pEval (ρLd Mo N K m) wRhoJ ≤ 200 * (Mo + 1) ^ 3 := by
  simp only [pEval, mEval, ρLd, wRhoJ, List.foldr, List.headD_cons, List.tail_cons, pow_zero,
    pow_one, one_mul, mul_one]
  have := poly_le (N := K) (K := 0) hK (Nat.zero_le _) hm (by simp) 3 0 0 4 7 0 (by norm_num)
  nlinarith

theorem pEval_le_canon (hN : N ≤ Mo) (hK : K ≤ Mo) (hNK : N * K ≤ Mo) :
    pEval (ρLd Mo N K 0) wCanon ≤ 200 * (Mo + 1) ^ 3 := by
  simp only [pEval, mEval, ρLd, wCanon, List.foldr, List.headD_cons, List.tail_cons, pow_zero,
    pow_one, one_mul, mul_one]
  have := poly_le hN hK (Nat.zero_le Mo) hNK 7 44 40 0 0 0 (by norm_num)
  nlinarith


theorem leafLe_of (hNK : N * K ≤ Mo) (hK : K ≤ Mo) (hN : N ≤ Mo) (hMo : Mo ≤ M)
    (hB : ∀ r, B r ≤ M) : ∀ c, TmOK Mo B c → LeafLe Mo N K B (IB M Mo) c := by
  have hm : ∀ r, max Mo (B r) ≤ M := fun r => max_le hMo (hB r)
  have hX : ∀ a b : ℕ, a ≤ M → b ≤ M → (2 * a + 3) * (30 + 10 * b) ≤ (2 * M + 3) * (30 + 10 * M) :=
    fun a b ha hb => Nat.mul_le_mul (by omega) (by omega)
  have hP : ∀ W : ℕ, W ≤ 200 * (Mo + 1) ^ 3 → (2 * Mo + 3) * W ≤ 1000 * (Mo + 1) ^ 4 := by
    intro W hW
    calc (2 * Mo + 3) * W ≤ (3 * (Mo + 1)) * (200 * (Mo + 1) ^ 3) :=
          Nat.mul_le_mul (by omega) hW
      _ = 600 * (Mo + 1) ^ 4 := by ring
      _ ≤ _ := by omega
  have hY : 1 ≤ (2 * M + 3) * (30 + 10 * M) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  set X := (2 * M + 3) * (30 + 10 * M)
  intro c hc
  induction c with
  | rep t b ih => exact ih hc
  | seq p q ihp ihq => exact ⟨ihp hc.1, ihq hc.2⟩
  | ifb t p q ihp ihq => exact ⟨ihp hc.1, ihq hc.2⟩
  | add d a b | sub d a b =>
    show binTime Mo N K B _ d a b ≤ IB M Mo
    unfold binTime IB
    have h1 := hX _ _ (hm a) (hNK.trans hMo)
    have h2 := hX _ _ (hm b) (hNK.trans hMo)
    have h3 := hP (40 * (N * K) + 44 * N + 7) (by
      have : 1 ≤ (Mo + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
      have : Mo ≤ (Mo + 1) ^ 3 := by
        have := Nat.le_self_pow (n := 3) (by norm_num) (Mo + 1); omega
      omega)
    have h4 : (2 * max Mo (B d) + 3) * 10 ≤ X := (Nat.mul_le_mul (by have := hm d; omega)
      (by omega : 10 ≤ 30 + 10 * M))
    omega
  | mul => exact hc.elim
  | digit => exact hc.elim
  | neg => exact hc.elim
  | canon d a =>
    show unTime Mo N K B _ d a ≤ IB M Mo
    unfold unTime IB
    have h1 := hX _ _ (hm a) (hNK.trans hMo)
    have h3 := hP _ (pEval_le_canon hN hK hNK)
    have h4 : (2 * max Mo (B d) + 3) * 10 ≤ X := (Nat.mul_le_mul (by have := hm d; omega)
      (by omega : 10 ≤ 30 + 10 * M))
    omega
  | rotB d a t =>
    show tmTime Mo N K B (pEval (ρLd Mo N K (B t)) wRotB) d a t ≤ IB M Mo
    unfold tmTime IB
    have h1 := hX _ _ (hm a) (hNK.trans hMo)
    have h3 := hP _ (pEval_le_rotB hN hK hc hNK)
    have h4 : (2 * max Mo (B d) + 3) * 10 ≤ X := (Nat.mul_le_mul (by have := hm d; omega)
      (by omega : 10 ≤ 30 + 10 * M))
    have h5 : 2 * max Mo (B t) + 3 ≤ X := by
      have := hm t
      calc 2 * max Mo (B t) + 3 ≤ (2 * M + 3) * 1 := by omega
        _ ≤ X := Nat.mul_le_mul_left _ (by omega)
    omega
  | aut d a t =>
    show tmTime Mo N K B (pEval (ρLd Mo N K (B t)) wAut) d a t ≤ IB M Mo
    unfold tmTime IB
    have h1 := hX _ _ (hm a) (hNK.trans hMo)
    have h3 := hP _ (pEval_le_aut hN hK hc hNK)
    have h4 : (2 * max Mo (B d) + 3) * 10 ≤ X := (Nat.mul_le_mul (by have := hm d; omega)
      (by omega : 10 ≤ 30 + 10 * M))
    have h5 : 2 * max Mo (B t) + 3 ≤ X := by
      have := hm t
      calc 2 * max Mo (B t) + 3 ≤ (2 * M + 3) * 1 := by omega
        _ ≤ X := Nat.mul_le_mul_left _ (by omega)
    omega
  | rhoJ d a t =>
    show tmTime Mo N K B (pEval (ρLd Mo N K (B t)) wRhoJ) d a t ≤ IB M Mo
    unfold tmTime IB
    have h1 := hX _ _ (hm a) (hNK.trans hMo)
    have h3 := hP _ (pEval_le_rhoJ hN hK hc hNK)
    have h4 : (2 * max Mo (B d) + 3) * 10 ≤ X := (Nat.mul_le_mul (by have := hm d; omega)
      (by omega : 10 ≤ 30 + 10 * M))
    have h5 : 2 * max Mo (B t) + 3 ≤ X := by
      have := hm t
      calc 2 * max Mo (B t) + 3 ≤ (2 * M + 3) * 1 := by omega
        _ ≤ X := Nat.mul_le_mul_left _ (by omega)
    omega
  | mv d s c =>
    show (2 * max (B s) (max (B d) (B c)) + 3) * (20 + 10 * B c) + 3 ≤ IB M Mo
    unfold IB
    have : (2 * max (B s) (max (B d) (B c)) + 3) * (20 + 10 * B c) ≤ X :=
      Nat.mul_le_mul (by have := hB s; have := hB d; have := hB c; omega)
        (by have := hB c; omega)
    omega
  | drop t c =>
    show (2 * max (B t) (B c) + 3) * (20 + 10 * B c) + 3 ≤ IB M Mo
    unfold IB
    have : (2 * max (B t) (B c) + 3) * (20 + 10 * B c) ≤ X :=
      Nat.mul_le_mul (by have := hB t; have := hB c; omega) (by have := hB c; omega)
    omega
  | cp d s =>
    show 2 * max (B d) (B s) + 3 ≤ IB M Mo
    unfold IB
    have := hB d; have := hB s
    have : 2 * max (B d) (B s) + 3 ≤ X :=
      calc _ ≤ (2 * M + 3) * 1 := by omega
        _ ≤ X := Nat.mul_le_mul_left _ (by omega)
    omega
  | clr t | tl t =>
    show 2 * B t + 3 ≤ IB M Mo
    unfold IB
    have := hB t
    have : 2 * B t + 3 ≤ X :=
      calc _ ≤ (2 * M + 3) * 1 := by omega
        _ ≤ X := Nat.mul_le_mul_left _ (by omega)
    omega
  | nop =>
    show 3 ≤ IB M Mo
    unfold IB; omega

end Instr

end AdvancedEncryption.ExpLUT.Prog.RedChal
