import PE.Impl.ExpLUT.Prog.AuthW
import PE.Impl.RingBTVW.Prog.BpCompCost

/-!
# The cost of the authorization program for ExpLUT's predicate words (package G2)

As for `RingBTVW.BpComp.authBP` (`BpCompCost`): cost triples `TA S p n` (from the per-tape bounds
`βA S` to `βA S` in `n` sweeps of `2 S + 5` steps).

* `ta_offW`: the offset of `a ‖ z` (two moves into `K`, the doubling `ta_dbl`);
* `ta_stepW`: a step (the reversed move of the entry has the bounds of the plain move:
  `consHead` and `snocHead` have the same `lenT` and `pad`);
* **`bounds_authW8`**: on predicate words of at most `L ≤ S` bits (`S ≥ 2^49`), at most
  `authNW S · (2 S + 5)` steps, every tape at most `S` bits; **`bounds_authW8_49`**: at most
  `2^108` steps for `L ≤ 2^49`; **`size_authW8`**: at most `2^17` states.
-/

namespace AdvancedEncryption.ExpLUT.AuthW

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog
open AdvancedEncryption.RingBTVW.BpComp
open scoped Prog

variable {S : ℕ}

/-! ### Reversed moves -/

theorem lenT_consHead (i j : Fin 16) : Prim.lenT (.consHead i j) = Prim.lenT (.snocHead i j) := rfl

theorem bounds_iter_cons (z src d t : Fin 16) : ∀ (n : ℕ) (ℓ : Fin 16 → ℕ),
    timeBoundT (iter z (pp src t ⨾ prim (.consHead d t) ⨾ clr t) n) ℓ =
        timeBoundT (iter z (pp src t ⨾ prim (.snocHead d t) ⨾ clr t) n) ℓ ∧
      lenBoundT (iter z (pp src t ⨾ prim (.consHead d t) ⨾ clr t) n) ℓ =
        lenBoundT (iter z (pp src t ⨾ prim (.snocHead d t) ⨾ clr t) n) ℓ
  | 0, ℓ => ⟨rfl, rfl⟩
  | n + 1, ℓ => by
    have hb : lenBoundT (pp src t ⨾ prim (.consHead d t) ⨾ clr t) ℓ =
        lenBoundT (pp src t ⨾ prim (.snocHead d t) ⨾ clr t) ℓ := rfl
    have hbt : timeBoundT (pp src t ⨾ prim (.consHead d t) ⨾ clr t) ℓ =
        timeBoundT (pp src t ⨾ prim (.snocHead d t) ⨾ clr t) ℓ := rfl
    have ih := bounds_iter_cons z src d t n (lenBoundT (pp src t ⨾ prim (.snocHead d t) ⨾ clr t) ℓ)
    refine ⟨?_, ?_⟩
    · show timeBoundT (pp src t ⨾ prim (.consHead d t) ⨾ clr t) ℓ +
          timeBoundT (iter z (pp src t ⨾ prim (.consHead d t) ⨾ clr t) n)
            (lenBoundT (pp src t ⨾ prim (.consHead d t) ⨾ clr t) ℓ) =
        timeBoundT (pp src t ⨾ prim (.snocHead d t) ⨾ clr t) ℓ +
          timeBoundT (iter z (pp src t ⨾ prim (.snocHead d t) ⨾ clr t) n)
            (lenBoundT (pp src t ⨾ prim (.snocHead d t) ⨾ clr t) ℓ)
      rw [hbt, hb, ih.1]
    · show lenBoundT (iter z (pp src t ⨾ prim (.consHead d t) ⨾ clr t) n)
            (lenBoundT (pp src t ⨾ prim (.consHead d t) ⨾ clr t) ℓ) =
        lenBoundT (iter z (pp src t ⨾ prim (.snocHead d t) ⨾ clr t) n)
            (lenBoundT (pp src t ⨾ prim (.snocHead d t) ⨾ clr t) ℓ)
      rw [hb, ih.2]

theorem ta_mvRev32 (hS : 2 ^ 49 ≤ S) {rest : Prog 16} {m : ℕ} (hr : TA S rest m) :
    TA S (clr tZB ⨾ iter tT2 (pp tT2 tBit ⨾ prim (.consHead tZB tBit) ⨾ clr tBit) 14 ⨾ rest)
      (1 + (3 * 14 + 1 + m)) := fun ℓ hℓ => by
  have h := ta_mv32 hS hr ℓ hℓ
  have e := bounds_iter_cons tT2 tT2 tZB tBit 14 (lenBoundT (clr tZB) ℓ)
  refine ⟨?_, ?_⟩
  · show timeBoundT (clr tZB) ℓ + (timeBoundT (iter tT2 (pp tT2 tBit ⨾ prim (.consHead tZB tBit) ⨾
        clr tBit) 14) (lenBoundT (clr tZB) ℓ) + timeBoundT rest (lenBoundT (iter tT2
          (pp tT2 tBit ⨾ prim (.consHead tZB tBit) ⨾ clr tBit) 14) (lenBoundT (clr tZB) ℓ))) ≤ _
    rw [e.1, e.2]; exact h.1
  · show lenBoundT rest (lenBoundT (iter tT2 (pp tT2 tBit ⨾ prim (.consHead tZB tBit) ⨾
        clr tBit) 14) (lenBoundT (clr tZB) ℓ)) ≤ _
    rw [e.2]; exact h.2

/-! ### The offset -/

/-- Units of the offset computation. -/
abbrev offNW : ℕ := 1 + (3 * 8 + 1 + (1 + (3 * 14 + 1 + (1 + (22 * (4 * 2 ^ 26 + 152) + 45)))))

theorem ta_offW (hS : 2 ^ 49 ≤ S) : TA S offW offNW := fun ℓ hℓ => by
  have hS1 : 1 ≤ S := le_trans Nat.one_le_two_pow hS
  -- after the second move, from a store with `K ≤ 8`
  have hm2 : ∀ ℓ' : Fin 16 → ℕ, ℓ' ≤ βA S → ℓ' tK ≤ 8 →
      timeBoundT (cp tT2 tZB ⨾ iter tK (pp tT2 tBit ⨾ prim (.snocHead tK tBit) ⨾ clr tBit) 14 ⨾
          clr tT2 ⨾ clr tU ⨾ forN tKC tK (pp tK tBit ⨾ appT tU tU tA2 tB2 ⨾
            ifBit tBit (appT tU tE tA2 tB2) (nop tU) ⨾ clr tBit)) ℓ' ≤
        (1 + (3 * 14 + 1 + (1 + (22 * (4 * 2 ^ 26 + 152) + 45)))) * (2 * S + 5) ∧
      lenBoundT (cp tT2 tZB ⨾ iter tK (pp tT2 tBit ⨾ prim (.snocHead tK tBit) ⨾ clr tBit) 14 ⨾
          clr tT2 ⨾ clr tU ⨾ forN tKC tK (pp tK tBit ⨾ appT tU tU tA2 tB2 ⨾
            ifBit tBit (appT tU tE tA2 tB2) (nop tU) ⨾ clr tBit)) ℓ' ≤ βA S := by
    intro ℓ' hℓ' hK
    let ℓ2 : Fin 16 → ℕ := Function.update ℓ' tT2 (ℓ' tZB)
    have hZ : ℓ' tZB ≤ 14 := by have := hℓ' tZB; simpa +decide [βA] using this
    have h2 : ℓ2 ≤ βA S := fun t => by
      have := hℓ' t; simp only [ℓ2, Function.update_apply]; split_ifs with h
      · subst h; simp +decide [βA]; omega
      · exact this
    have hm := ta_mv hS (src := tT2) (dst := tK) (t := tBit) (z := tK) (by decide) (by decide)
      (by decide) 14 (by simp +decide [βA]) ((ta_prim hS (.clear tT2) (by βA_tac)).seq (ta_dbl hS))
      ℓ2 h2 (by simp only [ℓ2, Function.update_of_ne (show tK ≠ tT2 by decide)]; simp +decide [βA]; omega)
    have t0 : timeBoundT (prim (.copy tT2 tZB)) ℓ' ≤ 2 * S + 5 := by
      show 2 * (supB ℓ' + 0) + 3 ≤ _; have := supB_βA hS hℓ'; omega
    refine ⟨?_, hm.2⟩
    show timeBoundT (prim (.copy tT2 tZB)) ℓ' + timeBoundT _ ℓ2 ≤ _
    nlinarith [hm.1]
  -- the first move
  let ℓ1 : Fin 16 → ℕ := Function.update ℓ tK 0
  have h1 : ℓ1 ≤ βA S := fun t => by
    have := hℓ t; simp only [ℓ1, Function.update_apply]; split_ifs
    · exact Nat.zero_le _
    · exact this
  have hi := iter_mv_bounds tK (src := tX) (dst := tK) (t := tBit) (by decide) (by decide)
    (by decide) 8 ℓ1 (S := S) (fun u => (h1 u).trans (βA_le hS u))
    (by simp only [ℓ1, Function.update_self]; omega) hS1
  set ℓ3 := lenBoundT (iter tK (pp tX tBit ⨾ prim (.snocHead tK tBit) ⨾ clr tBit) 8) ℓ1
  have h3 : ℓ3 ≤ βA S := fun u => by
    refine (hi.2 u).trans ?_
    have hu : ℓ1 u ≤ βA S u := h1 u
    split_ifs with ha hb
    · subst ha; simp only [ℓ1, Function.update_self]; simp +decide [βA]
    · subst hb; have : βA S tBit = S := by simp +decide [βA]
      rw [this]; exact max_le (hu.trans (βA_le hS _)) hS1
    · exact hu
  have h3K : ℓ3 tK ≤ 8 := by
    have := hi.2 tK; simp only [↓reduceIte] at this
    simp only [ℓ1, Function.update_self] at this; omega
  have hr := hm2 ℓ3 h3 h3K
  have t0 : timeBoundT (prim (.clear tK)) ℓ ≤ 2 * S + 5 := by
    show 2 * (supB ℓ + 0) + 3 ≤ _; have := supB_βA hS hℓ; omega
  refine ⟨?_, hr.2⟩
  show timeBoundT (prim (.clear tK)) ℓ + (timeBoundT (iter tK (pp tX tBit ⨾ prim (.snocHead tK tBit) ⨾
    clr tBit) 8) ℓ1 + timeBoundT _ ℓ3) ≤ _
  nlinarith [hi.1, hr.1]

/-! ### The steps and the program -/

/-- Units of a step. -/
abbrev stepNW : ℕ := offNW + (1 + ((3 * 2 ^ 26 + 3) + (1 + (3 * 14 + 1 + (1 + ((3 * 2 ^ 26 + 3) + 1))))))

theorem ta_stepW (hS : 2 ^ 49 ≤ S) : TA S stepW stepNW := by
  have hU : βA S tU = 2 ^ 26 := by simp +decide [βA]
  have hTB : βA S tTB = 2 ^ 26 := by simp +decide [βA]
  have := (ta_offW hS).seq <| (ta_prim hS (.copy tT2 tCU) (by βA_tac)).seq <|
    ((ta_dropT hS (t := tT2) (x := tU) (by decide) (by decide)).seq <| ta_mvRev32 hS <|
      (ta_prim hS (.clear tT2) (by βA_tac)).seq <|
      (ta_dropT hS (t := tCU) (x := tTB) (by decide) (by decide)).seq
        (ta_prim hS (.clear tU) (by βA_tac)))
  rw [hU, hTB] at this
  exact this

theorem ta_lastW (hS : 2 ^ 49 ≤ S) :
    TA S lastW (2 + (offNW + (1 + ((3 * 2 ^ 26 + 3) + 1)))) := by
  have hU : βA S tU = 2 ^ 26 := by simp +decide [βA]
  have := ta_clrSnoc hS true (c := tE) (by simp +decide [βA]) <|
    (ta_offW hS).seq <| (ta_prim hS (.copy tT2 tCU) (by βA_tac)).seq <|
      (ta_dropT hS (t := tT2) (x := tU) (by decide) (by decide)).seq
        (ta_prim hS (.pop tT2 tBit) (by βA_tac))
  rw [hU] at this
  exact this

/-- Units of the authorization program for tapes of at most `S` bits. -/
def authNW (S : ℕ) : ℕ :=
  ((12 * bpLenA + 100) + (1 + ((3 * S + 3) + (((3 * S + 3) + (2 + 1) + 1) + (1 + 1))))) +
    (((12 * tblW + 100) + ((12 * 14 + 100) + (1 + (1 + (14 + 1 + (12 * 15 + 100)))))) +
      ((15 * (stepNW + 2) + 1) + ((2 + (offNW + (1 + ((3 * 2 ^ 26 + 3) + 1)))) +
        ((1 + (2 + 1 + 1)) + 10))))

theorem ta_authW8 (hS : 2 ^ 49 ≤ S) : TA S authW8 (authNW S) := by
  have hS2 : βA S tS2 = 15 := by simp +decide [βA]
  have hl := ta_loop hS tS2 (ta_stepW hS)
  rw [hS2] at hl
  exact (ta_lenA hS).seq <| (ta_initA hS).seq <| hl.seq <| (ta_lastW hS).seq <|
    (ta_outA hS).seq (ta_clrA hS)

/-- **The bounds of the authorization program** for predicate words of at most `L ≤ S` bits. -/
theorem bounds_authW8 (hS : 2 ^ 49 ≤ S) {L : ℕ} (hL : L ≤ S) :
    timeBoundT authW8 (inBA L) ≤ authNW S * (2 * S + 5) ∧ ∀ t, lenBoundT authW8 (inBA L) t ≤ S := by
  have h := ta_authW8 hS (inBA L) fun t => by
    simp only [inBA, Function.update_apply]
    split_ifs with h1 h2
    · subst h1; simp +decide [βA]; omega
    · subst h2; simp +decide [βA]; omega
    · exact Nat.zero_le _
  exact ⟨h.1, fun t => (h.2 t).trans (βA_le hS t)⟩

theorem authNW_le : authNW (2 ^ 49) * (2 * 2 ^ 49 + 5) ≤ 2 ^ 108 := by decide +kernel

/-- **The authorization program** on predicate words of at most `2^49` bits: at most `2^108`
steps, every tape at most `2^49` bits. -/
theorem bounds_authW8_49 {L : ℕ} (hL : L ≤ 2 ^ 49) :
    timeBoundT authW8 (inBA L) ≤ 2 ^ 108 ∧ ∀ t, lenBoundT authW8 (inBA L) t ≤ 2 ^ 49 := by
  obtain ⟨h1, h2⟩ := bounds_authW8 (S := 2 ^ 49) le_rfl hL
  exact ⟨h1.trans authNW_le, h2⟩

/-! ### The size -/

theorem size_offW : size offW ≤ 6000 := by
  have hmv : ∀ src : Fin 16, size (pp src tBit ⨾ prim (.snocHead tK tBit) ⨾ clr tBit) ≤ 180 := by
    intro src
    have : size (pp src tBit) ≤ 60 := size_prim16 _
    have : size (prim (.snocHead tK tBit)) ≤ 60 := size_prim16 _
    have : size (clr tBit) ≤ 60 := size_prim16 _
    show size _ + (size _ + size _) ≤ _; omega
  have hi := size_iter16 tK (pp tX tBit ⨾ prim (.snocHead tK tBit) ⨾ clr tBit) 8
  have hi2 := size_iter16 tK (pp tT2 tBit ⨾ prim (.snocHead tK tBit) ⨾ clr tBit) 14
  have := hmv tX; have := hmv tT2
  have a1 := size_appT_le tU tU tA2 tB2; have a2 := size_appT_le tU tE tA2 tB2
  have : size (clr tK) ≤ 60 := size_prim16 _
  have : size (cp tT2 tZB) ≤ 60 := size_prim16 _
  have : size (clr tT2) ≤ 60 := size_prim16 _
  have : size (clr tU) ≤ 60 := size_prim16 _
  have : size (cp tKC tK) ≤ 60 := size_prim16 _
  have : size (pp tK tBit) ≤ 60 := size_prim16 _
  have : size (nop tU) ≤ 60 := size_prim16 _
  have : size (clr tBit) ≤ 60 := size_prim16 _
  show size (clr tK) + (size (iter tK (pp tX tBit ⨾ prim (.snocHead tK tBit) ⨾ clr tBit) 8) +
    (size (cp tT2 tZB) + (size (iter tK (pp tT2 tBit ⨾ prim (.snocHead tK tBit) ⨾ clr tBit) 14) +
    (size (clr tT2) + (size (clr tU) + (size (cp tKC tK) + (size (pp tK tBit) +
      (size (appT tU tU tA2 tB2) + ((size (appT tU tE tA2 tB2) + size (nop tU) + 1) +
        size (clr tBit))) + 39))))))) ≤ _
  omega

theorem size_stepW : size stepW ≤ 12000 := by
  have := size_offW
  have hmv : size (pp tT2 tBit ⨾ prim (.consHead tZB tBit) ⨾ clr tBit) ≤ 180 := by
    have : size (pp tT2 tBit) ≤ 60 := size_prim16 _
    have : size (prim (.consHead tZB tBit)) ≤ 60 := size_prim16 _
    have : size (clr tBit) ≤ 60 := size_prim16 _
    show size _ + (size _ + size _) ≤ _; omega
  have hi := size_iter16 tT2 (pp tT2 tBit ⨾ prim (.consHead tZB tBit) ⨾ clr tBit) 14
  have := size_dropT16 tT2 tU tA2; have := size_dropT16 tCU tTB tA2
  have : size (cp tT2 tCU) ≤ 60 := size_prim16 _
  have : size (clr tZB) ≤ 60 := size_prim16 _
  have : size (clr tT2) ≤ 60 := size_prim16 _
  have : size (clr tU) ≤ 60 := size_prim16 _
  show size offW + (size (cp tT2 tCU) + (size (dropT tT2 tU tA2) + (size (clr tZB) +
    (size (iter tT2 (pp tT2 tBit ⨾ prim (.consHead tZB tBit) ⨾ clr tBit) 14) + (size (clr tT2) +
      (size (dropT tCU tTB tA2) + size (clr tU))))))) ≤ _
  omega

/-- **The size of the authorization program**: at most `2^17` states. -/
theorem size_authW8 : size authW8 ≤ 2 ^ 17 := by
  have hl : size (Prog.map uL (lenEqP bpLenA)) ≤ 500 * 49 + 2000 := by
    rw [size_map]
    have := size_lenEqP bpLenA
    have : Nat.log2 bpLenA ≤ 49 := log2_lt_of (by simp only [bpLenA]; norm_num)
    omega
  have hTB : Nat.log2 tblW ≤ 46 := log2_lt_of (by simp only [tblW]; norm_num)
  have h1 := size_natU tTB tA2 tB2 tblW; have h2 := size_natU tE tA2 tB2 14
  have h3 := size_natU tS2 tA2 tB2 15
  have h32 : Nat.log2 14 ≤ 6 := log2_lt_of (by norm_num)
  have h15 : Nat.log2 15 ≤ 4 := log2_lt_of (by norm_num)
  have hz := size_snocN16 tZB false 14
  have hs := size_stepW; have ho := size_offW
  have hd := size_dropT16 tT2 tU tA2
  have hsB : ∀ b, size (setB tC b) ≤ 120 := fun b => by
    have := size_prim16 (.clear tC); have := size_prim16 (.snoc tC b)
    show size (prim _) + size (prim _) ≤ _; omega
  have := hsB true; have := hsB false
  have : size (cp tCU tC) ≤ 60 := size_prim16 _
  have : size (clr tZB) ≤ 60 := size_prim16 _
  have : size (clr tE) ≤ 60 := size_prim16 _
  have : size (prim (.snoc tE true)) ≤ 60 := size_prim16 _
  have : size (cp tT2 tCU) ≤ 60 := size_prim16 _
  have : size (pp tT2 tBit) ≤ 60 := size_prim16 _
  have : size (clr tC) ≤ 60 := size_prim16 _
  have hc : size clrA ≤ 600 := by
    have hcl : ∀ t : Fin 16, size (clr t) ≤ 60 := fun t => size_prim16 _
    have := hcl tX; have := hcl tCU; have := hcl tZB; have := hcl tK; have := hcl tU
    have := hcl tE; have := hcl tT2; have := hcl tTB; have := hcl tBit; have := hcl tF
    show size (clr tX) + (size (clr tCU) + (size (clr tZB) + (size (clr tK) + (size (clr tU) +
      (size (clr tE) + (size (clr tT2) + (size (clr tTB) + (size (clr tBit) + size (clr tF))))))))) ≤ _
    omega
  have g1 : ∀ p q : Prog 16, size (p ⨾ q) = size p + size q := fun _ _ => rfl
  have g2 : ∀ (c : Fin 16) (p : Prog 16), size (loop c p) = size p + 39 := fun _ _ => rfl
  have g3 : ∀ (c : Fin 16) (p q : Prog 16), size (ifBit c p q) = size p + size q + 1 :=
    fun _ _ _ => rfl
  simp only [authW8, initA, lastW, outA', g1, g2, g3]
  omega

end AdvancedEncryption.ExpLUT.AuthW
