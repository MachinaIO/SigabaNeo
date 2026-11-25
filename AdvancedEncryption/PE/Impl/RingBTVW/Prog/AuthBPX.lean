import PE.Impl.RingBTVW.Prog.Comps
import PE.Impl.RingBTVW.Prog.BpCompCost
import PE.Impl.RingBTVW.Prog.Lift
import PE.Impl.RingBTVW.Prog.KeyFront

/-!
# The authorization component of the reductions for branching programs

`AuthSpec hk c authP Lq Ta Sa`: the interface of the authorization component at the handlers'
width (the law of `Comps.law_auth`, the bit `authI hk c C x`; from a query of at most `Lq` bits and
an attribute of at most `nA` bits, at most `2^Ta` steps, the output one bit, at most `2^Sa`
states). Here it is met by **`authBPX`**: WS7's `authBPC` (16 tapes) followed by `authFix` (the
work tapes cleared and the output bit rewritten, so that the static output bound is one bit),
lifted to the handlers' width.

**`authSpec_authBPX`**: `AuthSpec hk c authBPX (2^49) 109 18` (queries of at most `2^49` bits;
the class has `bpLen = 481 · 2^40` bits; longer queries are cut by the handlers).
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.PE
open AdvancedEncryption.PE.BranchingProgram (encAttr)
open AdvancedEncryption.RingBTVW.BpComp (authBPC inA outA law_authBPC good_authBP bounds_authBPC
  inBA)

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- **The specification of an authorization component** at the handlers' width. -/
structure AuthSpec (authP : XProg 256) (Lq Ta Sa : ℕ) : Prop where
  wf : authP.WF
  law : ∀ (C : List Bool) (x : PUniv.Attr), authP.law (io2 (R := 254) C (PUniv.encAttr x) []) =
    PMF.pure (io2 (R := 254) [authI hk c C x] [] [])
  time : ∀ {a b : ℕ}, a ≤ Lq → b ≤ nA → XProg.timeBoundT authP (io2 (R := 254) a b 0) ≤ 2 ^ Ta
  len : ∀ {a b : ℕ}, a ≤ Lq → b ≤ nA → XProg.lenBoundT authP (io2 (R := 254) a b 0) ≤ io2 1 0 0
  size : authP.size ≤ 2 ^ Sa

/-- The output normalized: the work tapes cleared, the bit of tape `0` rewritten. -/
def authFix : Prog 16 :=
  .seq (.prim (.clear 1)) <| .seq (.prim (.clear 2)) <| .seq (.prim (.clear 3)) <|
  .seq (.prim (.clear 4)) <| .seq (.prim (.clear 5)) <| .seq (.prim (.clear 6)) <|
  .seq (.prim (.clear 7)) <| .seq (.prim (.clear 8)) <| .seq (.prim (.clear 9)) <|
  .seq (.prim (.clear 10)) <| .seq (.prim (.clear 11)) <| .seq (.prim (.clear 12)) <|
  .seq (.prim (.clear 13)) <| .seq (.prim (.clear 14)) <| .seq (.prim (.clear 15)) <|
  .ifBit 0 (.seq (.prim (.clear 0)) (.prim (.cons 0 true)))
    (.seq (.prim (.clear 0)) (.prim (.cons 0 false)))

/-- The authorization program with its output normalized. -/
def authBPN : Prog 16 := .seq authBPC authFix

theorem l14 : (14 : ℕ) ≤ 254 := by norm_num

/-- **The authorization component**: `authBPN` at the handlers' width. -/
def authBPX : XProg 256 := liftP l14 (Prog.toX authBPN)

theorem coinFree_authFix : authFix.CoinFree := by
  simp [authFix, Prog.CoinFree, Prog.coinFreeB]

theorem wf_authFix : authFix.WF := by
  simp [authFix, Prog.WF]

theorem run_authFix (b : Bool) : Prog.run authFix (outA b) = ioS (R := 14) [b] [] [] := by
  funext t
  cases b <;> fin_cases t <;> rfl

theorem ioS_inA (C xs : List Bool) : (ioS (R := 14) C xs [] : Store 16) = inA C xs := by
  funext t
  fin_cases t <;> rfl

theorem run_authBPC (C : List Bool) (x : PUniv.Attr) :
    Prog.run authBPC (inA C (encAttr x)) =
      outA (decide (C.length = bpLen) && !output (tablesOf C) x) := by
  have h := law_authBPC C x
  rw [Prog.law_eq_run_of_coinFree authBPC good_authBP.1] at h
  have : _ ∈ (PMF.pure _).support := h ▸ (PMF.mem_support_pure_iff _ _).mpr rfl
  simpa using this

theorem law_authBPX (C : List Bool) (x : PUniv.Attr) :
    authBPX.law (io2 (R := 254) C (PUniv.encAttr x) []) =
      PMF.pure (io2 (R := 254) [authI hk c C x] [] []) := by
  have hcf : authBPN.CoinFree := by
    have h1 : authBPC.coinFreeB = true := good_authBP.1
    have h2 : authFix.coinFreeB = true := coinFree_authFix
    show (Prog.seq authBPC authFix).coinFreeB = true
    simp [Prog.coinFreeB, h1, h2]
  have hp : (Prog.toX authBPN).law (ioS (R := 14) C (encAttr x) []) =
      PMF.pure (ioS (R := 14) [authI hk c C x] [] []) := by
    rw [Prog.law_toX, Prog.law_eq_run_of_coinFree _ hcf, ioS_inA, authBPN, Prog.run_seq,
      run_authBPC, run_authFix, authI_eq]
  exact law_liftP_pure l14 hp

theorem wf_authBPX : authBPX.WF := Prog.wf_toX _ ⟨good_authBP.2, wf_authFix⟩

theorem io2_le_inBA {a b : ℕ} (ha : a ≤ 2 ^ 49) (hb : b ≤ nA) :
    (io2 (R := 14) a b 0 : Fin 16 → ℕ) ≤ inBA (2 ^ 49) := fun t => by
  simp only [io2, inBA, Function.update_apply]
  fin_cases t <;> simp <;> omega

theorem lenBoundT_authFix (ℓ : Fin 16 → ℕ) :
    Prog.lenBoundT authFix ℓ ≤ io2 (R := 14) 1 0 0 := fun t => by
  fin_cases t <;> simp [authFix, Prog.lenBoundT, Prim.lenT, Function.update_apply, io2]

theorem time_authFix {ℓ : Fin 16 → ℕ} (h : ∀ t, ℓ t ≤ 2 ^ 49) :
    Prog.timeBoundT authFix ℓ ≤ 2 ^ 60 := by
  have h1 := (Prog.ubp_global authFix (2 ^ 49)) ℓ h
  have h2 : Prog.timeBound authFix (2 ^ 49) ≤ 2 ^ 60 := by
    simp [authFix, Prog.timeBound, Prog.lenBound, Prim.pad, Prim.grow]
  exact h1.1.trans h2

/-- **The authorization component meets the interface**: queries of at most `2^49` bits,
at most `2^109` steps, one output bit, at most `2^18` states. -/
theorem authSpec_authBPX : AuthSpec hk c authBPX (2 ^ 49) 109 18 where
  wf := wf_authBPX
  law := law_authBPX hk c
  time {a b} ha hb := by
    rw [authBPX, timeBoundT_liftP, Prog.timeBoundT_toX, authBPN]
    obtain ⟨t1, l1⟩ := bounds_authBPC (L := 2 ^ 49) le_rfl
    have m1 := Prog.timeBoundT_mono authBPC (io2_le_inBA ha hb)
    have m2 : ∀ t, Prog.lenBoundT authBPC (io2 (R := 14) a b 0) t ≤ 2 ^ 49 := fun t =>
      (Prog.lenBoundT_mono authBPC (io2_le_inBA ha hb) t).trans (l1 t)
    show Prog.timeBoundT authBPC _ + Prog.timeBoundT authFix _ ≤ _
    have := time_authFix m2
    have : (2 : ℕ) ^ 108 + 2 ^ 60 ≤ 2 ^ 109 := by norm_num
    omega
  len {a b} _ _ := by
    refine lenBoundT_liftP_le l14 _ ?_
    rw [Prog.lenBoundT_toX, authBPN]
    exact lenBoundT_authFix _
  size := by
    rw [authBPX, liftP, XProg.size_frame, Prog.size_toX, authBPN]
    have h1 := BpComp.size_authBPC
    have h2 : Prog.size authFix ≤ 2 ^ 12 := by decide +kernel
    have e : Prog.size (Prog.seq authBPC authFix) = Prog.size authBPC + Prog.size authFix :=
      Prog.size.eq_3 _ _
    rw [e]
    have : (2 : ℕ) ^ 17 + 2 ^ 12 ≤ 2 ^ 18 := by norm_num
    omega

end AdvancedEncryption.RingBTVW.Prog
