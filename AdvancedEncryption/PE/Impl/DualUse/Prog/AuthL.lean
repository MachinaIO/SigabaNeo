import PE.Impl.Gates.AuthProg
import PE.Impl.DualUse.Prog.Auth
import PE.Impl.DualUse.Prog.Comps
import SigabaNeo.Lib.Machines.Prog.NumBound
import SigabaNeo.Lib.Machines.Prog.VecBound
import SigabaNeo.Lib.Machines.Prog.FrameSize

/-!
# The authorization component at the handlers' width

`authL : XProg 256` is the tape program `authMain` (`PE.Impl.Gates.AuthProg`: a search over the
valid dates `a ≤ b`, writing each window predicate `pairWord (a, b)` with a gate generator and
comparing it with the query) as a framed program (`Prog.toX`), lifted to the handlers' width.

* `law_authL`: in the form of `Comps.law_auth`, when `dateBound ≤ c.L` (`authI_eq_winAuth`, and
  `outerV_validL`: the program's search is `winAuth`);
* `time_authL`, `len_authL`: from a query of at most `2^240` bits and a date of at most `10`,
  at most `2^275` steps, and the output `io2 1 0 0` — a certificate of the numeric interpreter
  (`NB.check`, `check_authMain`, checked by `decide +kernel`);
* `size_authL`: at most `2^19` states; `wf_authL`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow
open AdvancedEncryption.PE.Gates AdvancedEncryption.PE.Gates.DateWindow

/-- **The program's search is the window search.** -/
theorem outerV_validL (C : List Bool) (x : Date) : outerV C x validL = winAuth C x := by
  rw [Bool.eq_iff_iff, outerV_iff C x _ validL_sorted, winAuth, List.any_eq_true]
  constructor
  · rintro ⟨a, ha, b, hb, hab, h1, hx, hax, hxb⟩
    refine ⟨(a, b), List.pair_mem_product.mpr ⟨mem_allDates _, mem_allDates _⟩, ?_⟩
    rw [mem_validL] at ha hb hx
    simp only [isWindow, acceptsP, Bool.and_eq_true, decide_eq_true_iff, dateLe_dkey]
    exact ⟨⟨⟨⟨ha, hb⟩, hab⟩, h1⟩, ⟨hx, hax⟩, hxb⟩
  · rintro ⟨⟨a, b⟩, -, h⟩
    simp only [isWindow, acceptsP, Bool.and_eq_true, decide_eq_true_iff, dateLe_dkey] at h
    obtain ⟨⟨⟨⟨ha, hb⟩, hab⟩, h1⟩, ⟨hx, hax⟩, hxb⟩ := h
    exact ⟨a, (mem_validL a).mpr ha, b, (mem_validL b).mpr hb, hab, h1, (mem_validL x).mpr hx,
      hax, hxb⟩

theorem coinFree_authMain : authMain.CoinFree := by
  unfold Prog.CoinFree; decide +kernel

theorem wf_authMain : authMain.WF := Prog.wf_of_wfB (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **The certificate of the bounds**: from a query of at most `2^240` bits and a date of at most
`10` bits, the output is one bit, every other tape blank, in at most `2^275` steps. -/
theorem check_authMain : NB.check 3 authMain [2 ^ 240, 10] [1] (2 ^ 275) = true := by
  decide +kernel

theorem size_authMain : authMain.size ≤ 2 ^ 19 := by decide +kernel

theorem one_le_254 : (38 : ℕ) ≤ 254 := by norm_num

/-- **The authorization component.** -/
def authL : XProg 256 := liftP one_le_254 (Prog.toX authMain)

theorem wf_authL : authL.WF := Prog.wf_toX _ wf_authMain

theorem ioS_eq_inStore (C : List Bool) (x : Date) :
    (ioS (R := 38) C (encDate x) [] : Store 40) = inStore C x := by
  funext t
  simp only [ioS, inStore, Fin.ext_iff]
  rfl

theorem ioS_out (b : Bool) :
    (fun t : Fin 40 => if t = 0 then [b] else []) = (ioS (R := 38) [b] [] [] : Store 40) := by
  funext t
  simp only [ioS, Fin.ext_iff]
  split_ifs <;> simp_all

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- **The law of the authorization component**, in the form of `Comps.law_auth`. -/
theorem law_authL (hL : dateBound ≤ c.L) (C : List Bool) (x : Date) :
    authL.law (io2 (R := 254) C (dateUniverse.encAttr x) []) =
      PMF.pure (io2 (R := 254) [authI hk c C x] [] []) := by
  have hp : (Prog.toX authMain).law (ioS (R := 38) C (encDate x) []) =
      PMF.pure (ioS (R := 38) [authI hk c C x] [] []) := by
    rw [Prog.law_toX, ioS_eq_inStore, Prog.law_eq_run_of_coinFree _ coinFree_authMain,
      run_authMain, outerV_validL, ← authI_eq_winAuth hk c hL, ioS_out]
  exact law_liftP_pure one_le_254 hp

theorem vg_io2_le {a b : ℕ} (ha : a ≤ 2 ^ 240) (hb : b ≤ 10) :
    (io2 (R := 38) a b 0 : Fin 40 → ℕ) ≤ NB.vg [2 ^ 240, 10] := fun t => by
  simp only [io2, NB.vg]
  rcases t with ⟨t, ht⟩
  rcases t with _ | _ | t
  · simpa using ha
  · simpa using hb
  · simp

/-- **The time of the authorization component.** -/
theorem time_authL {a b : ℕ} (ha : a ≤ 2 ^ 240) (hb : b ≤ 10) :
    XProg.timeBoundT authL (io2 (R := 254) a b 0) ≤ 2 ^ 275 := by
  rw [authL, timeBoundT_liftP, Prog.timeBoundT_toX]
  exact (NB.bounds_of_check check_authMain (vg_io2_le ha hb)).2

/-- **The output of the authorization component**: one bit. -/
theorem len_authL {a b : ℕ} (ha : a ≤ 2 ^ 240) (hb : b ≤ 10) :
    XProg.lenBoundT authL (io2 (R := 254) a b 0) ≤ io2 1 0 0 := by
  refine lenBoundT_liftP_le one_le_254 _ ?_
  rw [Prog.lenBoundT_toX]
  refine (NB.bounds_of_check check_authMain (vg_io2_le ha hb)).1.trans fun t => ?_
  simp only [io2, NB.vg]
  rcases t with ⟨t, ht⟩
  rcases t with _ | t <;> simp

/-- **The size of the authorization component.** -/
theorem size_authL : authL.size ≤ 2 ^ 19 := by
  rw [authL, liftP, XProg.size_frame, Prog.size_toX]; exact size_authMain

/-! ### The interface of the authorization component -/

/-- **The specification of an authorization component** at the handlers' width (`R = 254`): the
law of `Comps.law_auth` (the bit `authI hk c C x`), and, from a query of at most `Lq` bits and an
attribute of at most `nA` bits, at most `2 ^ Ta` steps, the output one bit, at most `2 ^ Sa`
states. The reductions use the authorization component only through this interface: `authL`
(date windows, `authSpec_authL`) now, the framed `authBPC` (branching programs, WS7) after the
switch. -/
structure AuthSpec (authP : XProg 256) (Lq Ta Sa : ℕ) : Prop where
  wf : authP.WF
  law : ∀ (C : List Bool) (x : PUniv.Attr), authP.law (io2 (R := 254) C (PUniv.encAttr x) []) =
    PMF.pure (io2 (R := 254) [authI hk c C x] [] [])
  time : ∀ {a b : ℕ}, a ≤ Lq → b ≤ nA → XProg.timeBoundT authP (io2 (R := 254) a b 0) ≤ 2 ^ Ta
  len : ∀ {a b : ℕ}, a ≤ Lq → b ≤ nA → XProg.lenBoundT authP (io2 (R := 254) a b 0) ≤ io2 1 0 0
  size : authP.size ≤ 2 ^ Sa

/-- **`authL` meets the interface**: queries of at most `2^240` bits, `2^275` steps, `2^19`
states. -/
theorem authSpec_authL (hL : dateBound ≤ c.L) : AuthSpec hk c authL (2 ^ 240) 275 19 where
  wf := wf_authL
  law := law_authL hk c hL
  time ha hb := time_authL ha hb
  len ha hb := len_authL ha hb
  size := size_authL

end AdvancedEncryption.DualUse.Prog
