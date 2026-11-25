import PE.Impl.ExpLUT.Prog.RedKeyC1Ring
import PE.Impl.ExpLUT.Prog.RedKeyMidPub
import PE.Impl.ExpLUT.Prog.RedChalDc
import PE.Impl.ExpLUT.Prog.RedKeyTTop

/-!
# Cost certificate of `mid`, phase M1: `m1P` from the input `rkIn`

**`c1_cert_m1P : Cert m1P rkIn c1Out (2 ^ 437)`**, with the output envelope (the storage tapes of
`RedKeyMidPub`)

| tape | word | bound |
|---|---|---|
| `tCt = 243` | `ctW σ` | `2 ^ 110` |
| `tMpk = 244` | `mpkW σ` | `2 ^ 102` |
| `tSig = 245` | `rawEnc σ` | `2 ^ 101` |
| `tC = 246` | `C` | `predLen` |
| all others | | `0` |

* `pubC` in `ringIOS` (`c1_cert_pub`): `pBf (2^41) (2^42) (2^102)` as in `RedPubP.bounds_pubP_Dc`,
  time `≤ 2^436` (the evaluated `vmTime` bound, `≈ 2^435.4`, plus `2^318` for the parked stash);
* `chalC` in `ringIOS` (`c1_cert_chal`): `Bf (2^40) (2^56) (2^110)` as in
  `RedChal.bounds_chalP_Dc`, time `≤ 2^351`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyC

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.RingVM
open AdvancedEncryption.ExpLUT.Prog.RedIO AdvancedEncryption.ExpLUT.Prog.RedKeyMid
open AdvancedEncryption.ExpLUT.Prog.KeyTime (Cert)
open scoped SigabaNeo.Tape.Prog

/-! ### The public key -/

set_option exponentiation.threshold 2000 in
theorem c1_cert_pub (La v1 v2 v3 : ℕ) (hLa : La ≤ 2 ^ 102) (hv1 : v1 ≤ 2 ^ 102)
    (hv2 : v2 ≤ 2 ^ 102) (hv3 : v3 ≤ 2 ^ 102) :
    Cert (ringIOS Dc.N Dc.K RedPubP.ra RedPubP.rb RedPubP.rOut RedPubP.r1 (RedPubP.tm Dc)
      (RedPubP.pubC Dc)) (c1St (io2 (R := 245) La 0 0) v1 v2 v3)
      (c1St (io2 (R := 245) (2 ^ 102) 0 0) v1 v2 v3) (2 ^ 436) := by
  have hNK : Dc.N * Dc.K = 2 ^ 40 := by rw [RedPubP.pDc_N, RedPubP.pDc_K]; norm_num
  have hK : Dc.K ≤ 2 ^ 41 := by rw [RedPubP.pDc_K]; norm_num
  have hN : Dc.N ≤ 2 ^ 41 := by rw [RedPubP.pDc_N]; norm_num
  have hNK' : Dc.N * Dc.K ≤ 2 ^ 41 := by rw [hNK]; norm_num
  have h1 : (2 : ℕ) ^ 41 ≤ 2 ^ 42 := by norm_num
  have h2 : (2 : ℕ) ^ 42 ≤ 2 ^ 102 := by norm_num
  obtain ⟨hC, hT, hR⟩ := RedPubP.pokB_spec hNK' h1 h2 (RedPubP.pubC Dc) (RedPubP.pokB_pubC Dc)
  have hBf : ∀ r, RedPubP.pBf (2 ^ 41) (2 ^ 42) (2 ^ 102) r ≤ 2 ^ 102 := RedPubP.pBf_le h1 h2
  have hS : ∀ r : Fin 200, r = sR1 ∨ r = sR2 ∨ r = sR3 →
      RedPubP.pBf (2 ^ 41) (2 ^ 42) (2 ^ 102) r = 2 ^ 102 := by
    rintro r (rfl | rfl | rfl) <;> rfl
  have c := c1_bounds_ringIOS hNK' hK hN (ra := RedPubP.ra) (rb := RedPubP.rb) (by decide)
    RedPubP.rOut RedPubP.r1 (by decide) (by decide) (RedPubP.tm Dc) (RedPubP.pubC Dc)
    (RedPubP.pBf (2 ^ 41) (2 ^ 42) (2 ^ 102)) hC La 0 (2 ^ 102) (by rw [show
      RedPubP.pBf (2 ^ 41) (2 ^ 42) (2 ^ 102) RedPubP.ra = 2 ^ 102 from rfl]; exact hLa)
    (Nat.zero_le _) (fun r _ _ _ => RedPubP.tm_le_Dc r)
    (by rw [show RedPubP.pBf (2 ^ 41) (2 ^ 42) (2 ^ 102) RedPubP.r1 = 2 ^ 102 from rfl];
        show Dc.N * Dc.K - 1 + 1 ≤ 2 ^ 102; rw [hNK]; norm_num)
    (h1.trans h2) hBf v1 v2 v3 (by rw [hS sR1 (Or.inl rfl)]; exact hv1)
    (by rw [hS sR2 (Or.inr (Or.inl rfl))]; exact hv2) (by rw [hS sR3 (Or.inr (Or.inr rfl))]; exact hv3)
    pub_uses1 pub_uses2 pub_uses3 (by decide) (by decide) (by decide)
  rw [show RedPubP.pBf (2 ^ 41) (2 ^ 42) (2 ^ 102) RedPubP.rOut = 2 ^ 102 from rfl] at c
  refine c.mono le_rfl le_rfl ?_
  have hsup : supB (encB (2 ^ 41) Dc.N Dc.K (RedPubP.pBf (2 ^ 41) (2 ^ 42) (2 ^ 102))) ≤ 2 ^ 102 :=
    XProg.supB_le_of (RedIO.encB_le (2 ^ 41) Dc.N Dc.K _ (2 ^ 102) (h1.trans h2) hK hN hNK' hBf)
  have hv := RedPubP.pvmTime_le (2 ^ 41) Dc.N Dc.K (RedPubP.pBf (2 ^ 41) (2 ^ 42) (2 ^ 102))
    (2 * 2 ^ 102 + 4) (RedPubP.pIB (2 ^ 102) (2 ^ 41)) (2 ^ 42) (by omega) (by omega)
    (by norm_num) (RedPubP.pubC Dc)
    (RedPubP.pleafLe_of hNK' hK hN (h1.trans h2) hBf (RedPubP.pubC Dc) hT) hR
  rw [RedPubP.vmCount_pubC] at hv
  have hd := RedPubP.pvmDepth_pubC Dc
  have hX : (2 ^ 42) ^ RedPubP.pvmDepth (RedPubP.pubC Dc) *
      (2 * 2 ^ 102 + 4 + RedPubP.pIB (2 ^ 102) (2 ^ 41)) * (RedPubP.pvmDepth (RedPubP.pubC Dc) + 1) ≤
      (2 ^ 42) ^ 5 * (2 * 2 ^ 102 + 4 + RedPubP.pIB (2 ^ 102) (2 ^ 41)) * 6 :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hd)) (by omega)
  have hv' := hv.trans (Nat.mul_le_mul_left _ hX)
  rw [show Dc.b = 22 from rfl] at hv'
  unfold RedPubP.pIB at hv'
  have hnum : ((2 : ℕ) ^ 102 + 1) * (210 * ((2 * 2 ^ 102 + 1) * (4 * 2 ^ 102 + 12))) +
      (478 + 241 * 22) * ((2 ^ 42) ^ 5 * (2 * 2 ^ 102 + 4 + (4 * ((2 * 2 ^ 102 + 3) *
        (30 + 10 * 2 ^ 102)) + 1000 * (2 ^ 41 + 1) ^ 4)) * 6) + 300 * (2 * 2 ^ 102 + 3) ≤ 2 ^ 436 := by
    norm_num
  exact (Nat.add_le_add_right (Nat.add_le_add_left hv' _) _).trans hnum

/-! ### The challenge -/

set_option exponentiation.threshold 2000 in
theorem c1_cert_chal (La Lb v1 v2 v3 : ℕ) (hLa : La ≤ 2 ^ 110) (hLb : Lb ≤ 2 ^ 110)
    (hv1 : v1 ≤ 2 ^ 110) (hv2 : v2 ≤ 2 ^ 110) (hv3 : v3 ≤ 2 ^ 110) :
    Cert (ringIOS Dc.N Dc.K RedChal.ra RedChal.rb RedVM.xOut RedChal.r1 (RedChal.tm Dc)
      (RedChal.chalC Dc)) (c1St (io2 (R := 245) La Lb 0) v1 v2 v3)
      (c1St (io2 (R := 245) (2 ^ 110) 0 0) v1 v2 v3) (2 ^ 351) := by
  have hNK : Dc.N * Dc.K = 2 ^ 40 := by rw [RedChal.Dc_N, RedChal.Dc_K]; norm_num
  have hK : Dc.K ≤ 2 ^ 40 := by rw [RedChal.Dc_K]; norm_num
  have hN : Dc.N ≤ 2 ^ 40 := by rw [RedChal.Dc_N]; norm_num
  have h1 : (2 : ℕ) ^ 40 ≤ 2 ^ 56 := by norm_num
  have h2 : (2 : ℕ) ^ 56 ≤ 2 ^ 110 := by norm_num
  obtain ⟨hC, hT, hR⟩ := RedChal.okB_spec hNK.le h1 h2 (RedChal.chalC Dc) (RedChal.okB_chalC Dc)
  have hBf : ∀ r, RedChal.Bf (2 ^ 40) (2 ^ 56) (2 ^ 110) r ≤ 2 ^ 110 := RedChal.Bf_le h1 h2
  have hS : ∀ r : Fin 200, r = sR1 ∨ r = sR2 ∨ r = sR3 →
      RedChal.Bf (2 ^ 40) (2 ^ 56) (2 ^ 110) r = 2 ^ 110 := by
    rintro r (rfl | rfl | rfl) <;> rfl
  have htm := RedChal.tm_le_Bf Dc (Mo := 2 ^ 40) (Bc := 2 ^ 56) (Mb := 2 ^ 110)
    (by rw [RedChal.Dc_N]; norm_num) (by norm_num) RedChal.ctr_Dc RedChal.tmBase_Dc_le
  have c := c1_bounds_ringIOS hNK.le hK hN (ra := RedChal.ra) (rb := RedChal.rb) (by decide)
    RedVM.xOut RedChal.r1 (by decide) (by decide) (RedChal.tm Dc) (RedChal.chalC Dc)
    (RedChal.Bf (2 ^ 40) (2 ^ 56) (2 ^ 110)) hC La Lb (2 ^ 110)
    (by rw [show RedChal.Bf (2 ^ 40) (2 ^ 56) (2 ^ 110) RedChal.ra = 2 ^ 110 from rfl]; exact hLa)
    (by rw [show RedChal.Bf (2 ^ 40) (2 ^ 56) (2 ^ 110) RedChal.rb = 2 ^ 110 from rfl]; exact hLb)
    (fun r _ _ _ => htm r)
    (by rw [show RedChal.Bf (2 ^ 40) (2 ^ 56) (2 ^ 110) RedChal.r1 = 2 ^ 110 from rfl];
        show Dc.N * Dc.K - 1 + 1 ≤ 2 ^ 110; rw [hNK]; norm_num)
    (h1.trans h2) hBf v1 v2 v3 (by rw [hS sR1 (Or.inl rfl)]; exact hv1)
    (by rw [hS sR2 (Or.inr (Or.inl rfl))]; exact hv2) (by rw [hS sR3 (Or.inr (Or.inr rfl))]; exact hv3)
    chal_uses1 chal_uses2 chal_uses3 (by decide) (by decide) (by decide)
  rw [show RedChal.Bf (2 ^ 40) (2 ^ 56) (2 ^ 110) RedVM.xOut = 2 ^ 110 from rfl] at c
  refine c.mono le_rfl le_rfl ?_
  have hsup : supB (encB (2 ^ 40) Dc.N Dc.K (RedChal.Bf (2 ^ 40) (2 ^ 56) (2 ^ 110))) ≤ 2 ^ 110 :=
    XProg.supB_le_of (RedIO.encB_le (2 ^ 40) Dc.N Dc.K _ (2 ^ 110) (h1.trans h2) hK hN hNK.le hBf)
  have hv := RedChal.vmTime_le (2 ^ 40) Dc.N Dc.K (RedChal.Bf (2 ^ 40) (2 ^ 56) (2 ^ 110))
    (2 * 2 ^ 110 + 4) (RedChal.IB (2 ^ 110) (2 ^ 40)) (2 ^ 56) (by omega) (by omega)
    (by norm_num) (RedChal.chalC Dc)
    (RedChal.leafLe_of hNK.le hK hN (h1.trans h2) hBf (RedChal.chalC Dc) hT) hR
  rw [RedChal.vmCount_chalC] at hv
  have hd := RedChal.vmDepth_chalC Dc
  have hX : (2 ^ 56) ^ RedChal.vmDepth (RedChal.chalC Dc) *
      (2 * 2 ^ 110 + 4 + RedChal.IB (2 ^ 110) (2 ^ 40)) * (RedChal.vmDepth (RedChal.chalC Dc) + 1) ≤
      (2 ^ 56) ^ 2 * (2 * 2 ^ 110 + 4 + RedChal.IB (2 ^ 110) (2 ^ 40)) * 3 :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hd)) (by omega)
  have hv' := hv.trans (Nat.mul_le_mul_left _ hX)
  rw [show Dc.b = 22 from rfl] at hv'
  unfold RedChal.IB at hv'
  have hnum : ((2 : ℕ) ^ 110 + 1) * (210 * ((2 * 2 ^ 110 + 1) * (4 * 2 ^ 110 + 12))) +
      (1205 + 16 * 22) * ((2 ^ 56) ^ 2 * (2 * 2 ^ 110 + 4 + (4 * ((2 * 2 ^ 110 + 3) *
        (30 + 10 * 2 ^ 110)) + 1000 * (2 ^ 40 + 1) ^ 4)) * 3) + 300 * (2 * 2 ^ 110 + 3) ≤
      2 ^ 351 := by
    norm_num
  exact (Nat.add_le_add_right (Nat.add_le_add_left hv' _) _).trans hnum


/-! ### Straight-line programs with bits -/

/-- A straight-line program of copies, clears and pushed bits. -/
def c1CX {k : ℕ} : Tape.Prog k → Prop
  | .prim (.copy _ _) => True
  | .prim (.clear _) => True
  | .prim (.cons _ _) => True
  | .seq p q => c1CX p ∧ c1CX q
  | _ => False

theorem c1CX_bounds {k : ℕ} : ∀ p : Tape.Prog k, c1CX p → ∀ (M : ℕ) (ℓ : Fin k → ℕ),
    (∀ t, ℓ t ≤ M) → (∀ t, p.lenBoundT ℓ t ≤ M + c1Cnt p) ∧
      p.timeBoundT ℓ ≤ c1Cnt p * (2 * (M + c1Cnt p) + 5) := by
  intro p
  induction p with
  | prim p =>
    intro hp M ℓ hℓ
    have hs := XProg.supB_le_of hℓ
    cases p with
    | copy i j =>
      refine ⟨fun t => ?_, ?_⟩
      · show Function.update ℓ i (ℓ j) t ≤ M + 1
        rw [Function.update_apply]; split_ifs <;> exact (hℓ _).trans (by omega)
      · show 2 * (supB ℓ + 0) + 3 ≤ 1 * (2 * (M + 1) + 5); omega
    | clear i =>
      refine ⟨fun t => ?_, ?_⟩
      · show Function.update ℓ i 0 t ≤ M + 1
        rw [Function.update_apply]; split_ifs
        · exact Nat.zero_le _
        · exact (hℓ _).trans (by omega)
      · show 2 * (supB ℓ + 0) + 3 ≤ 1 * (2 * (M + 1) + 5); omega
    | cons i b =>
      refine ⟨fun t => ?_, ?_⟩
      · show Function.update ℓ i (ℓ i + 1) t ≤ M + 1
        rw [Function.update_apply]; split_ifs
        · have := hℓ i; omega
        · exact (hℓ _).trans (by omega)
      · show 2 * (supB ℓ + 1) + 3 ≤ 1 * (2 * (M + 1) + 5); omega
    | _ => exact absurd hp id
  | seq p q ihp ihq =>
    intro hp M ℓ hℓ
    obtain ⟨h1, h2⟩ := ihp hp.1 M ℓ hℓ
    obtain ⟨h3, h4⟩ := ihq hp.2 (M + c1Cnt p) _ h1
    refine ⟨fun t => (h3 t).trans (by show _ ≤ M + (c1Cnt p + c1Cnt q); omega), ?_⟩
    show p.timeBoundT ℓ + q.timeBoundT (p.lenBoundT ℓ) ≤
      (c1Cnt p + c1Cnt q) * (2 * (M + (c1Cnt p + c1Cnt q)) + 5)
    have e1 : c1Cnt p * (2 * (M + c1Cnt p) + 5) ≤
        c1Cnt p * (2 * (M + (c1Cnt p + c1Cnt q)) + 5) := Nat.mul_le_mul_left _ (by omega)
    have e2 : c1Cnt q * (2 * (M + c1Cnt p + c1Cnt q) + 5) ≤
        c1Cnt q * (2 * (M + (c1Cnt p + c1Cnt q)) + 5) := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.add_mul]; omega
  | _ => intro hp; exact absurd hp id

/-! ### Phase M1 -/

/-- **The output envelope of M1** (the storage tapes of `RedKeyMidPub`). -/
def c1Out : Fin 247 → ℕ := fun t =>
  if t = tCt then 2 ^ 110 else if t = tMpk then 2 ^ 102 else if t = tSig then 2 ^ 101
  else if t = tC then predLen else 0

theorem c1_io2_0 (a b d : ℕ) : io2 (R := 245) a b d 0 = a := rfl
theorem c1_io2_1 (a b d : ℕ) : io2 (R := 245) a b d 1 = b := rfl
theorem c1_io2_o (a b d : ℕ) (t : Fin 247) (h0 : ¬ t = 0) (h1 : ¬ t = 1) :
    io2 (R := 245) a b d t = d := by
  have e0 : t.val ≠ 0 := fun h => h0 (Fin.ext h)
  have e1 : t.val ≠ 1 := fun h => h1 (Fin.ext h)
  simp [io2, e0, e1]

theorem c1_predLen : predLen ≤ 2 ^ 101 := by norm_num [predLen]

theorem c1_cert_in :
    Cert (.prog m1InP) RedKeyT.rkIn (c1St (io2 (R := 245) (2 ^ 101) 0 0) 0 (2 ^ 101) predLen)
      (3 * (2 * (2 ^ 101 + 3) + 5)) := by
  have hl : ∀ t, RedKeyT.rkIn t ≤ 2 ^ 101 := by
    intro t; simp only [RedKeyT.rkIn, io2]; have := c1_predLen; split_ifs <;> omega
  refine ⟨fun t => ?_, (c1CX_bounds m1InP (by simp [m1InP, c1CX]) _ _ hl).2⟩
  simp only [m1InP, XProg.lenBoundT, Prog.lenBoundT, Prim.lenT, c1St, RedKeyT.rkIn]
  by_cases a1 : t = tWd sR1 <;> by_cases a2 : t = tWd sR2 <;> by_cases a3 : t = tWd sR3 <;>
    by_cases b0 : t = 0 <;> by_cases b1 : t = 1 <;>
    simp_all [Function.update_apply, c1_io2_0, c1_io2_1, c1_io2_o, sR1, sR2, sR3, tWd, tC, tSig]

theorem c1_cert_mid :
    Cert (.prog m1MidP) (c1St (io2 (R := 245) (2 ^ 102) 0 0) 0 (2 ^ 101) predLen)
      (c1St (io2 (R := 245) (2 ^ 101) 1 0) (2 ^ 102) (2 ^ 101) predLen)
      (3 * (2 * (2 ^ 102 + 3) + 5)) := by
  have hl : ∀ t, c1St (io2 (R := 245) (2 ^ 102) 0 0) 0 (2 ^ 101) predLen t ≤ 2 ^ 102 := by
    intro t; simp only [c1St, Function.update_apply, io2]; have := c1_predLen
    split_ifs <;> omega
  refine ⟨fun t => ?_, (c1CX_bounds m1MidP (by simp [m1MidP, c1CX]) _ _ hl).2⟩
  simp only [m1MidP, XProg.lenBoundT, Prog.lenBoundT, Prim.lenT, c1St]
  by_cases a1 : t = tWd sR1 <;> by_cases a2 : t = tWd sR2 <;> by_cases a3 : t = tWd sR3 <;>
    by_cases b0 : t = 0 <;> by_cases b1 : t = 1 <;>
    simp_all [Function.update_apply, c1_io2_0, c1_io2_1, c1_io2_o, sR1, sR2, sR3, tWd, tMpk, tSig]

theorem c1_cert_out :
    Cert (.prog m1OutP) (c1St (io2 (R := 245) (2 ^ 110) 0 0) (2 ^ 102) (2 ^ 101) predLen) c1Out
      (2 * (2 * (2 ^ 110 + 2) + 5)) := by
  have hl : ∀ t, c1St (io2 (R := 245) (2 ^ 110) 0 0) (2 ^ 102) (2 ^ 101) predLen t ≤ 2 ^ 110 := by
    intro t; simp only [c1St, Function.update_apply, io2]; have := c1_predLen
    split_ifs <;> omega
  refine ⟨fun t => ?_, (c1CX_bounds m1OutP (by simp [m1OutP, c1CX]) _ _ hl).2⟩
  simp only [m1OutP, XProg.lenBoundT, Prog.lenBoundT, Prim.lenT, c1St, c1Out]
  by_cases a1 : t = tWd sR1 <;> by_cases a2 : t = tWd sR2 <;> by_cases a3 : t = tWd sR3 <;>
    by_cases b0 : t = 0 <;> by_cases b1 : t = 1 <;> by_cases b4 : t = tCt <;>
    simp_all [Function.update_apply, c1_io2_0, c1_io2_1, c1_io2_o, sR1, sR2, sR3, tWd, tMpk, tSig, tCt, tC]

set_option exponentiation.threshold 2000 in
/-- **The certificate of phase M1.** -/
theorem c1_cert_m1P : Cert m1P RedKeyT.rkIn c1Out (2 ^ 437) := by
  have hp := c1_predLen
  have p0 := c1_cert_in
  have p1 := c1_cert_pub (2 ^ 101) 0 (2 ^ 101) predLen (by norm_num) (by norm_num) (by norm_num)
    (hp.trans (by norm_num))
  have p2 := c1_cert_mid
  have p3 := c1_cert_chal (2 ^ 101) 1 (2 ^ 102) (2 ^ 101) predLen (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (hp.trans (by norm_num))
  have p4 := c1_cert_out
  exact (p0.seq (p1.seq (p2.seq (p3.seq p4)))).mono le_rfl le_rfl (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.RedKeyC
