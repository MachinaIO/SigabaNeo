import PE.Impl.ExpLUT.Prog.RedKeyMidRing
import PE.Impl.ExpLUT.Prog.RedKeyC1Un
import PE.Impl.ExpLUT.Prog.KeyTimeBasic

/-!
# Cost certificate of `mid`, phase M1 (generic): the bounds of the stash handler `ringIOS`

**`c1_bounds_ringIOS`**: from the input bound `c1St (io2 La Lb 0) v₁ v₂ v₃` (the stash bounds on
the register tapes `tWd 197 … 199`), for register bounds `B` closed under the code
(`RingVM.Closed`) with `vᵢ ≤ B sRᵢ`, the output bound is `c1St (io2 (B ro) 0 0) v₁ v₂ v₃` — the
stash keeps its **exact** input bounds — and the time is
`(M + 1) · 210 (2M+1)(4M+12) + vmTime … c + 300 (2M+3)` (the factor `M + 1` pays for the parked
stash while `preP` builds the templates, `c1X_time`).

Steps: `parkP` (`c1_park_len`), `preP` with the parked tapes (`c1Av_preP`, `c1X_len`,
`c1X_time`), the bit of `1`, `unparkP` (`c1_unpark_len`), the code at the register bounds
`B` updated on the stash (`c1_closed_update`: a code that never mentions a register is closed
for any bound on it), the exit `postS`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyC

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.RingVM
open AdvancedEncryption.ExpLUT.Prog.RedIO AdvancedEncryption.ExpLUT.Prog.RedKeyMid
open AdvancedEncryption.ExpLUT.Prog.KeyTime (Cert)
open scoped SigabaNeo.Tape.Prog

/-! ### Straight-line copies and clears -/

/-- A straight-line program of copies and clears. -/
def c1CC {k : ℕ} : Tape.Prog k → Prop
  | .prim (.copy _ _) => True
  | .prim (.clear _) => True
  | .seq p q => c1CC p ∧ c1CC q
  | _ => False

/-- Its number of primitives. -/
def c1Cnt {k : ℕ} : Tape.Prog k → ℕ
  | .seq p q => c1Cnt p + c1Cnt q
  | _ => 1

theorem c1CC_bounds {k : ℕ} (M : ℕ) : ∀ p : Tape.Prog k, c1CC p → ∀ ℓ : Fin k → ℕ, (∀ t, ℓ t ≤ M) →
    (∀ t, p.lenBoundT ℓ t ≤ M) ∧ p.timeBoundT ℓ ≤ c1Cnt p * (2 * M + 3) := by
  intro p
  induction p with
  | prim p =>
    intro hp ℓ hℓ
    have hs := XProg.supB_le_of hℓ
    cases p with
    | copy i j =>
      refine ⟨fun t => ?_, ?_⟩
      · show Function.update ℓ i (ℓ j) t ≤ M
        rw [Function.update_apply]; split_ifs <;> exact hℓ _
      · show 2 * (supB ℓ + 0) + 3 ≤ 1 * (2 * M + 3); omega
    | clear i =>
      refine ⟨fun t => ?_, ?_⟩
      · show Function.update ℓ i 0 t ≤ M
        rw [Function.update_apply]; split_ifs
        · exact Nat.zero_le _
        · exact hℓ _
      · show 2 * (supB ℓ + 0) + 3 ≤ 1 * (2 * M + 3); omega
    | _ => exact absurd hp id
  | seq p q ihp ihq =>
    intro hp ℓ hℓ
    obtain ⟨h1, h2⟩ := ihp hp.1 ℓ hℓ
    obtain ⟨h3, h4⟩ := ihq hp.2 _ h1
    refine ⟨h3, ?_⟩
    show p.timeBoundT ℓ + q.timeBoundT (p.lenBoundT ℓ) ≤ (c1Cnt p + c1Cnt q) * (2 * M + 3)
    rw [Nat.add_mul]; omega
  | _ => intro hp; exact absurd hp id

/-! ### The parking tapes and the stash -/

/-- The parking tapes `10, 11, 12`. -/
def c1Pk (t : Fin 247) : Prop := t = pk1 ∨ t = pk2 ∨ t = pk3

instance : DecidablePred c1Pk := fun t => by unfold c1Pk; infer_instance

/-- Bounds with the stash bounds on the stash register tapes. -/
def c1St (s : Fin 247 → ℕ) (v1 v2 v3 : ℕ) : Fin 247 → ℕ :=
  Function.update (Function.update (Function.update s (tWd sR1) v1) (tWd sR2) v2) (tWd sR3) v3

/-- The stash bounds on the parking tapes. -/
def c1Pg (v1 v2 v3 : ℕ) : Fin 247 → ℕ := fun t => if t = pk1 then v1 else if t = pk2 then v2 else v3

/-- The register bounds with the stash bounds. -/
def c1BS (B : Fin 200 → ℕ) (v1 v2 v3 : ℕ) : Fin 200 → ℕ :=
  Function.update (Function.update (Function.update B sR1 v1) sR2 v2) sR3 v3

theorem c1Mix_mono {S : Fin 247 → Prop} [DecidablePred S] {a b : Fin 247 → ℕ} (h : a ≤ b)
    (g : Fin 247 → ℕ) : c1Mix S a g ≤ c1Mix S b g := fun t => by
  by_cases hs : S t <;> simp [c1Mix, hs, h t]

theorem c1_io2_pk (La Lb : ℕ) (t : Fin 247) (ht : c1Pk t) : io2 (R := 245) La Lb 0 t = 0 := by
  rcases ht with rfl | rfl | rfl <;> rfl

theorem c1_io2_tWd (La Lb : ℕ) (x : Fin 200) : io2 (R := 245) La Lb 0 (tWd x) = 0 := by
  have h0 : (tWd x).val ≠ 0 := by simp [tWd]
  have h1 : (tWd x).val ≠ 1 := by simp [tWd]; omega
  simp [io2, h0, h1]

theorem c1_park_len (La Lb v1 v2 v3 : ℕ) :
    Prog.lenBoundT parkP (c1St (io2 (R := 245) La Lb 0) v1 v2 v3) ≤
      c1Mix c1Pk (io2 (R := 245) La Lb 0) (c1Pg v1 v2 v3) := by
  intro t
  have e1 := c1_io2_tWd La Lb sR1
  have e2 := c1_io2_tWd La Lb sR2
  have e3 := c1_io2_tWd La Lb sR3
  simp only [parkP, Prog.lenBoundT, Prim.lenT, c1St, c1Mix, c1Pg, c1Pk]
  by_cases a1 : t = tWd sR1 <;> by_cases a2 : t = tWd sR2 <;> by_cases a3 : t = tWd sR3 <;>
    by_cases b1 : t = pk1 <;> by_cases b2 : t = pk2 <;> by_cases b3 : t = pk3 <;>
    simp_all [Function.update_apply, sR1, sR2, sR3, pk1, pk2, pk3, tWd]

theorem c1_park_time (La Lb v1 v2 v3 M : ℕ) (ha : La ≤ M) (hb : Lb ≤ M) (h1 : v1 ≤ M)
    (h2 : v2 ≤ M) (h3 : v3 ≤ M) :
    Prog.timeBoundT parkP (c1St (io2 (R := 245) La Lb 0) v1 v2 v3) ≤ 6 * (2 * M + 3) := by
  have hc : c1CC parkP := by simp [parkP, c1CC]
  have hl : ∀ t, c1St (io2 (R := 245) La Lb 0) v1 v2 v3 t ≤ M := by
    intro t
    simp only [c1St, Function.update_apply, io2]
    split_ifs <;> omega
  exact (c1CC_bounds M parkP hc _ hl).2

theorem c1_unpark_len (Mo N K : ℕ) (B : Fin 200 → ℕ) (v1 v2 v3 : ℕ) :
    Prog.lenBoundT unparkP (c1Mix c1Pk (encB Mo N K B) (c1Pg v1 v2 v3)) ≤
      encB Mo N K (c1BS B v1 v2 v3) := by
  intro t
  have hpk : ∀ t : Fin 247, c1Pk t → encB Mo N K (c1BS B v1 v2 v3) t = Mo := by
    intro t ht
    rcases ht with rfl | rfl | rfl <;> simp [encB, pk1, pk2, pk3]
  have hw : ∀ x : Fin 200, encB Mo N K (c1BS B v1 v2 v3) (tWd x) = c1BS B v1 v2 v3 x :=
    encB_tWd Mo N K _
  have hw' : ∀ x : Fin 200, encB Mo N K B (tWd x) = B x := encB_tWd Mo N K _
  simp only [unparkP, Prog.lenBoundT, Prim.lenT]
  by_cases a1 : t = tWd sR1
  · subst a1; rw [hw]; simp [Function.update_apply, c1Mix, c1Pg, c1Pk, c1BS, sR1, sR2, sR3, pk1,
      pk2, pk3, tWd]
  by_cases a2 : t = tWd sR2
  · subst a2; rw [hw]; simp [Function.update_apply, c1Mix, c1Pg, c1Pk, c1BS, sR1, sR2, sR3, pk1,
      pk2, pk3, tWd]
  by_cases a3 : t = tWd sR3
  · subst a3; rw [hw]; simp [Function.update_apply, c1Mix, c1Pg, c1Pk, c1BS, sR1, sR2, sR3, pk1,
      pk2, pk3, tWd]
  by_cases hp : c1Pk t
  · rw [hpk t hp]
    rcases hp with rfl | rfl | rfl <;> simp [Function.update_apply, pk1, pk2, pk3, sR1, sR2, sR3,
      tWd]
  · have e : encB Mo N K (c1BS B v1 v2 v3) t = encB Mo N K B t := by
      by_cases hge : 47 ≤ t.val
      · obtain ⟨x, rfl⟩ : ∃ x : Fin 200, t = tWd x :=
          ⟨⟨t.val - 47, by have := t.isLt; omega⟩, Fin.ext (by simp [tWd]; omega)⟩
        rw [hw, hw']
        have n1 : x ≠ sR1 := fun h => a1 (by rw [h])
        have n2 : x ≠ sR2 := fun h => a2 (by rw [h])
        have n3 : x ≠ sR3 := fun h => a3 (by rw [h])
        simp [c1BS, Function.update_of_ne n1, Function.update_of_ne n2, Function.update_of_ne n3]
      · simp only [encB, hge, ↓reduceDIte]
    rw [e]
    have hp' : ¬ (t = pk1 ∨ t = pk2 ∨ t = pk3) := hp
    push Not at hp'
    simp [Function.update_apply, a1, a2, a3, hp'.1, hp'.2.1, hp'.2.2, c1Mix, c1Pk]

theorem c1_encB_mono (Mo N K : ℕ) {B B' : Fin 200 → ℕ} (h : B ≤ B') :
    encB Mo N K B ≤ encB Mo N K B' := by
  intro t
  unfold encB
  split_ifs <;> first | exact le_rfl | exact h _

/-- **A code that never mentions `r` is closed for any bound on `r`.** -/
theorem c1_closed_update (Mo N K : ℕ) (B : Fin 200 → ℕ) (r : Fin 200) (v : ℕ) :
    ∀ c : Code, usesR r c = false → Closed Mo N K B c → Closed Mo N K (Function.update B r v) c := by
  intro c
  induction c with
  | rep t b ih =>
    intro hu hc
    simp only [usesR, Bool.or_eq_false_iff] at hu
    exact ih hu.2 hc
  | seq p q ihp ihq =>
    intro hu hc
    simp only [usesR, Bool.or_eq_false_iff] at hu
    exact ⟨ihp hu.1 hc.1, ihq hu.2 hc.2⟩
  | ifb t p q ihp ihq =>
    intro hu hc
    simp only [usesR, Bool.or_eq_false_iff] at hu
    exact ⟨ihp hu.1.2 hc.1, ihq hu.2 hc.2⟩
  | _ =>
    intro hu hc
    simp only [usesR, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hu
    simp_all [Closed, Function.update_apply]

theorem c1_closed_BS (Mo N K : ℕ) (B : Fin 200 → ℕ) (v1 v2 v3 : ℕ) (c : Code)
    (h1 : usesR sR1 c = false) (h2 : usesR sR2 c = false) (h3 : usesR sR3 c = false)
    (hc : Closed Mo N K B c) : Closed Mo N K (c1BS B v1 v2 v3) c :=
  c1_closed_update _ _ _ _ _ _ c h3 (c1_closed_update _ _ _ _ _ _ c h2
    (c1_closed_update _ _ _ _ _ _ c h1 hc))

theorem c1BS_le (B : Fin 200 → ℕ) (v1 v2 v3 : ℕ) (h1 : v1 ≤ B sR1) (h2 : v2 ≤ B sR2)
    (h3 : v3 ≤ B sR3) : c1BS B v1 v2 v3 ≤ B := by
  intro r
  simp only [c1BS, Function.update_apply]
  split_ifs with a b c
  · subst a; exact h3
  · subst b; exact h2
  · subst c; exact h1
  · exact le_rfl

/-! ### `preP` avoids the parking tapes -/

theorem c1Av_natP (t c : Fin 247) (ht : ¬ c1Pk t) (hc : ¬ c1Pk c) :
    ∀ n, c1XAv c1Pk (XProg.natP t c n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hd : c1XAv c1Pk (XProg.dblP t c) := ⟨⟨hc, ht⟩, hc, ht⟩
    rcases n with _ | n
    · rw [XProg.natP]; exact ht
    · rw [XProg.natP]
      split_ifs
      · exact ⟨ih _ (by omega), hd⟩
      · exact ⟨⟨ih _ (by omega), hd⟩, ht⟩

theorem c1Av_tmplsP (c : Fin 247) (hc : ¬ c1Pk c) :
    ∀ l : List (Fin 247 × ℕ), (∀ p ∈ l, ¬ c1Pk p.1) → c1XAv c1Pk (tmplsP c l) := by
  intro l
  induction l with
  | nil => intro _; exact ⟨hc, hc⟩
  | cons p l ih =>
    intro hl
    exact ⟨c1Av_natP p.1 c (hl p (by simp)) hc p.2, ih fun q hq => hl q (by simp [hq])⟩

theorem c1_not_pk_tWd (x : Fin 200) : ¬ c1Pk (tWd x) := by
  intro h
  rcases h with h | h | h <;> have := congrArg Fin.val h <;> simp [tWd, pk1, pk2, pk3] at this <;>
    omega

theorem c1_not_pk_of (t : Fin 247) (h : t.val ≠ 10 ∧ t.val ≠ 11 ∧ t.val ≠ 12) : ¬ c1Pk t := by
  rintro (e | e | e) <;> subst e <;> simp [pk1, pk2, pk3] at h

theorem c1Av_preP (N K : ℕ) (ra rb : Fin 200) (tm : Fin 200 → ℕ) :
    c1XAv c1Pk (preP N K ra rb tm) := by
  have hl : ∀ p ∈ tList N K ra rb tm, ¬ c1Pk p.1 := by
    intro p hp
    rcases mem_tList.mp hp with rfl | rfl | rfl | ⟨r', -, -, rfl⟩
    · exact c1_not_pk_of tK (by decide)
    · exact c1_not_pk_of tN (by decide)
    · exact c1_not_pk_of tNK (by decide)
    · exact c1_not_pk_tWd r'
  have h0 : ¬ c1Pk 0 := c1_not_pk_of 0 (by decide)
  have h1 : ¬ c1Pk 1 := c1_not_pk_of 1 (by decide)
  have hc : ¬ c1Pk cT := c1_not_pk_of cT (by decide)
  have ho : ¬ c1Pk tOn := c1_not_pk_of tOn (by decide)
  have hn : ¬ c1Pk tNK := c1_not_pk_of tNK (by decide)
  refine ⟨?_, c1Av_tmplsP cT hc _ hl, ?_⟩
  · simp only [inP, c1XAv, c1ProgAv, c1PrimAv]
    exact ⟨⟨c1_not_pk_tWd ra, h0⟩, h0, ⟨c1_not_pk_tWd rb, h1⟩, h1⟩
  · simp only [onesP, Prog.forN, c1XAv, c1ProgAv, c1PrimAv]
    exact ⟨⟨⟨hc, hn⟩, hc, ho⟩, hc⟩

/-! ### The handler -/

theorem c1_pre_le (N K M : ℕ) (hNK : N * K ≤ M) :
    4 * (2 * M + 3) + (203 * ((2 * M + 1) * (4 * M + 12)) + (2 * M + 3)) +
      (2 * (2 * M + 3) + (N * K * (4 * M + 9) + 2)) ≤ 210 * ((2 * M + 1) * (4 * M + 12)) := by
  have : N * K * (4 * M + 9) ≤ M * (4 * M + 9) := Nat.mul_le_mul_right _ hNK
  nlinarith

/-- **The bounds of the stash handler.** -/
theorem c1_bounds_ringIOS {N K Mo : ℕ} (hNK : N * K ≤ Mo) (hK : K ≤ Mo) (hN : N ≤ Mo)
    {ra rb : Fin 200} (hab : ra ≠ rb) (ro r1 : Fin 200) (h1a : r1 ≠ ra) (h1b : r1 ≠ rb)
    (tm : Fin 200 → ℕ) (c : Code)
    (B : Fin 200 → ℕ) (hc : Closed Mo N K B c) (La Lb M : ℕ) (hLa : La ≤ B ra) (hLb : Lb ≤ B rb)
    (htm : ∀ r, r ≠ ra → r ≠ rb → r ≠ r1 → tm r ≤ B r) (h1 : tm r1 + 1 ≤ B r1) (hMo : Mo ≤ M)
    (hB : ∀ r, B r ≤ M) (v1 v2 v3 : ℕ) (hv1 : v1 ≤ B sR1) (hv2 : v2 ≤ B sR2) (hv3 : v3 ≤ B sR3)
    (hu1 : usesR sR1 c = false) (hu2 : usesR sR2 c = false) (hu3 : usesR sR3 c = false)
    (hro1 : ro ≠ sR1) (hro2 : ro ≠ sR2) (hro3 : ro ≠ sR3) :
    Cert (ringIOS N K ra rb ro r1 tm c) (c1St (io2 (R := 245) La Lb 0) v1 v2 v3)
      (c1St (io2 (R := 245) (B ro) 0 0) v1 v2 v3)
      ((M + 1) * (210 * ((2 * M + 1) * (4 * M + 12))) + vmTime Mo N K B (instrTime Mo N K B) c +
        300 * (2 * M + 3)) := by
  have hE := encB_le Mo N K B M hMo hK hN hNK hB
  have hv1M := hv1.trans (hB _)
  have hv2M := hv2.trans (hB _)
  have hv3M := hv3.trans (hB _)
  have hg : ∀ t, c1Pk t → c1Pg v1 v2 v3 t ≤ M := by
    intro t _; simp only [c1Pg]; split_ifs <;> omega
  -- park
  have cP : Cert (.prog parkP) (c1St (io2 (R := 245) La Lb 0) v1 v2 v3)
      (c1Mix c1Pk (io2 (R := 245) La Lb 0) (c1Pg v1 v2 v3)) (6 * (2 * M + 3)) :=
    ⟨c1_park_len La Lb v1 v2 v3, c1_park_time La Lb v1 v2 v3 M (hLa.trans (hB _))
      (hLb.trans (hB _)) hv1M hv2M hv3M⟩
  -- the templates
  set B0 := Function.update B r1 (tm r1)
  have hB0 : ∀ r, B0 r ≤ M := fun r => by
    simp only [B0, Function.update_apply]; split_ifs
    · subst r; exact (by omega : tm r1 ≤ B r1).trans (hB r1)
    · exact hB r
  have hB0B : B0 ≤ B := fun r => by
    simp only [B0, Function.update_apply]; split_ifs
    · subst r; omega
    · exact le_rfl
  obtain ⟨hpre, hTpre⟩ := pre_bounds hNK hK hN hab tm B0 La Lb M
    (by simp [B0, Function.update_of_ne h1a.symm, hLa])
    (by simp [B0, Function.update_of_ne h1b.symm, hLb])
    (fun r ha hb => by
      simp only [B0, Function.update_apply]; split_ifs
      · subst r; exact le_rfl
      · exact htm r ha hb (by assumption))
    hMo hB0
  have hav := c1Av_preP N K ra rb tm
  have cPre : Cert (preP N K ra rb tm) (c1Mix c1Pk (io2 (R := 245) La Lb 0) (c1Pg v1 v2 v3))
      (c1Mix c1Pk (encB Mo N K B0) (c1Pg v1 v2 v3))
      ((M + 1) * (210 * ((2 * M + 1) * (4 * M + 12)))) := by
    refine ⟨?_, ?_⟩
    · rw [c1X_len c1Pk _ hav]; exact c1Mix_mono hpre _
    · refine (c1X_time c1Pk M _ hav _ _ hg).trans (Nat.mul_le_mul_left _ ?_)
      exact hTpre.trans (c1_pre_le N K M (hNK.trans hMo))
  -- the bit of `1`
  have hE0 := encB_le Mo N K B0 M hMo hK hN hNK hB0
  have hmix0 : ∀ t, c1Mix c1Pk (encB Mo N K B0) (c1Pg v1 v2 v3) t ≤ M := by
    intro t; by_cases ht : c1Pk t
    · rw [c1Mix_of _ _ _ ht]; exact hg t ht
    · rw [c1Mix_off _ _ _ ht]; exact hE0 t
  have cCons : Cert (.prog (.prim (.cons (tWd r1) true)))
      (c1Mix c1Pk (encB Mo N K B0) (c1Pg v1 v2 v3)) (c1Mix c1Pk (encB Mo N K B) (c1Pg v1 v2 v3))
      (2 * (M + 1) + 3) := by
    refine ⟨fun t => ?_, ?_⟩
    · show Prim.lenT (.cons (tWd r1) true) (c1Mix c1Pk (encB Mo N K B0) (c1Pg v1 v2 v3)) t ≤ _
      simp only [Prim.lenT]
      rw [Function.update_apply]
      split_ifs with ht
      · subst ht
        rw [c1Mix_off _ _ _ (c1_not_pk_tWd r1), c1Mix_off _ _ _ (c1_not_pk_tWd r1), encB_tWd,
          encB_tWd]
        simp only [B0, Function.update_self]; omega
      · exact c1Mix_mono (c1_encB_mono Mo N K hB0B) _ t
    · show 2 * (supB _ + 1) + 3 ≤ _
      have := XProg.supB_le_of hmix0
      omega
  -- unpark
  set B2 := c1BS B v1 v2 v3
  have hB2B : B2 ≤ B := c1BS_le B v1 v2 v3 hv1 hv2 hv3
  have hB2 : ∀ r, B2 r ≤ M := fun r => (hB2B r).trans (hB r)
  have hmix : ∀ t, c1Mix c1Pk (encB Mo N K B) (c1Pg v1 v2 v3) t ≤ M := by
    intro t; by_cases ht : c1Pk t
    · rw [c1Mix_of _ _ _ ht]; exact hg t ht
    · rw [c1Mix_off _ _ _ ht]; exact hE t
  have cUn : Cert (.prog unparkP) (c1Mix c1Pk (encB Mo N K B) (c1Pg v1 v2 v3)) (encB Mo N K B2)
      (6 * (2 * M + 3)) :=
    ⟨c1_unpark_len Mo N K B v1 v2 v3,
      (c1CC_bounds M unparkP (by simp [unparkP, c1CC]) _ hmix).2⟩
  -- the code
  have hcl2 := c1_closed_BS Mo N K B v1 v2 v3 c hu1 hu2 hu3 hc
  obtain ⟨-, hL2⟩ := compile_time Mo N K B2 hNK hK hN c hcl2
  obtain ⟨hT, -⟩ := compile_time Mo N K B hNK hK hN c hc
  have cC : Cert (compile c) (encB Mo N K B2) (encB Mo N K B2)
      (vmTime Mo N K B (instrTime Mo N K B) c) :=
    ⟨hL2, ((XProg.timeBoundT_mono _) (c1_encB_mono Mo N K hB2B)).trans hT⟩
  -- the exit
  have hE2 := encB_le Mo N K B2 M hMo hK hN hNK hB2
  have cPost : Cert (.prog (postS ro)) (encB Mo N K B2) (c1St (io2 (R := 245) (B ro) 0 0) v1 v2 v3)
      (249 * (2 * M + 3)) := by
    set ℓc := encB Mo N K B2
    obtain ⟨hpl, hpt⟩ := clrL_bounds postTapesS (Function.update ℓc 0 (ℓc (tWd ro))) M
      (fun i => by
        simp only [Function.update_apply]
        split_ifs <;> exact hE2 _)
    have hlen : postTapesS.length ≤ 247 := (List.length_filter_le _ _).trans (by simp)
    have e : Prog.lenBoundT (postS ro) ℓc =
        Prog.lenBoundT (clrL postTapesS) (Function.update ℓc 0 (ℓc (tWd ro))) := by
      rw [postS]; simp only [Prog.lenBoundT, Prim.lenT]
    have et : Prog.timeBoundT (postS ro) ℓc = 2 * (supB ℓc + 0) + 3 +
        Prog.timeBoundT (clrL postTapesS) (Function.update ℓc 0 (ℓc (tWd ro))) := by
      rw [postS]; simp only [Prog.timeBoundT, Prog.lenBoundT, Prim.lenT, Prim.pad]
    refine ⟨?_, ?_⟩
    · change Prog.lenBoundT (postS ro) ℓc ≤ _
      rw [e, hpl]
      intro t
      show (if t ∈ postTapesS then 0 else Function.update ℓc 0 (ℓc (tWd ro)) t) ≤ _
      have ero : ℓc (tWd ro) = B ro := by
        simp only [ℓc, encB_tWd, B2, c1BS, Function.update_of_ne hro1, Function.update_of_ne hro2,
          Function.update_of_ne hro3]
      by_cases h0 : t = 0
      · subst h0
        have hm : (0 : Fin 247) ∉ postTapesS := by simp [postTapesS]
        rw [ite_cond_eq_false _ _ (eq_false hm), Function.update_self, ero]
        simp [c1St, io2, Function.update_apply, sR1, sR2, sR3, tWd]
      by_cases s3 : t = tWd sR3
      · subst s3
        have hm : tWd sR3 ∉ postTapesS := by simp [postTapesS]
        rw [ite_cond_eq_false _ _ (eq_false hm), Function.update_of_ne h0]
        simp [ℓc, c1St, encB_tWd, B2, c1BS]
      by_cases s2 : t = tWd sR2
      · subst s2
        have hm : tWd sR2 ∉ postTapesS := by simp [postTapesS]
        rw [ite_cond_eq_false _ _ (eq_false hm), Function.update_of_ne h0]
        simp only [ℓc, encB_tWd, B2, c1BS, c1St]
        rw [Function.update_of_ne (by decide), Function.update_self,
          Function.update_of_ne (by decide), Function.update_self]
      by_cases s1 : t = tWd sR1
      · subst s1
        have hm : tWd sR1 ∉ postTapesS := by simp [postTapesS]
        rw [ite_cond_eq_false _ _ (eq_false hm), Function.update_of_ne h0]
        simp only [ℓc, encB_tWd, B2, c1BS, c1St]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_self, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_self]
      · have hm : t ∈ postTapesS := by simp [postTapesS, h0, s1, s2, s3]
        rw [ite_cond_eq_true _ _ (eq_true hm)]; exact Nat.zero_le _
    · change Prog.timeBoundT (postS ro) ℓc ≤ _
      rw [et]
      have hs := XProg.supB_le_of hE2
      have := Nat.mul_le_mul_right (2 * M + 3) (Nat.add_le_add_right hlen 1)
      omega
  have all := cP.seq (cPre.seq (cCons.seq (cUn.seq (cC.seq cPost))))
  exact all.mono le_rfl le_rfl (by omega)

end AdvancedEncryption.ExpLUT.Prog.RedKeyC
