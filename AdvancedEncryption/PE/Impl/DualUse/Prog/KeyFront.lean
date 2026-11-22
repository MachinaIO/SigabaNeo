import PE.Impl.DualUse.SimKeyGame
import PE.Impl.Gates.ProgWindow

/-!
# The front end of the simulated key query and the authorization test

* **`authI_eq`**: the authorization flag of the experiment, classically `decide (Authorized …)`,
  is the explicit test `authN (nAuth c.L) C x` (`PE.Gates.DateWindow.authN`: `|C| ≤ nAuth c.L`,
  `C` in the window class, and the gate list of `C` false on the date bits). Here
  `nAuth L = (L - (2 |pw| + 23)) / 2`, the longest query whose input word `(pw, C, x)` of `Eval`
  has at most `L` bits.
* **`law_authPI`**: the component `authP (nAuth c.L)` computes `[authI hk c C x]` from `C` and
  `encDate x` (the form of `Comps.law_auth`), in `20 |C|` steps plus a constant
  (`PE.Gates.DateWindow.timeBoundT_authP`).
* **`KGsim_eq_front`**: the simulated key oracle depends on the query only through the output
  `frontV c.L W C` of the front-end component `frontP c.L W` (`law_frontP`) and, for a window
  predicate, through its gate list `parse C` (`predC C = predOf 10 (parse C)`), which that output
  carries in the layout `gsW W` of the `f̂` generator.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib
  Cslib.Probability SigabaNeo.Tape SigabaNeo.Tape.Prog
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}
variable {ms : Machines hk c}

/-- The longest query authorized under the input bound `L` of `Eval`. -/
def nAuth (L : ℕ) : ℕ := (L - (2 * (paramsWord dateUniverse params).length + 23)) / 2

theorem length_encodeTuple3 (a C x : List Bool) :
    (encodeTuple [a, C, x]).length = 2 * a.length + 2 * C.length + 2 * x.length + 3 := by
  rw [encodeTuple, Turing.MultiTapeTM.length_encList]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  show 2 * a.length + 1 + (2 * C.length + 1 + (2 * x.length + 1 + 0)) = _
  omega

variable (hk c) in
/-- **The authorization flag is the explicit test.** -/
theorem authI_eq (C : List Bool) (x : Date) : authI hk c C x = authN (nAuth c.L) C x := by
  classical
  unfold authI authN
  rw [Bool.eq_iff_iff, decide_eq_true_iff, win_authorized_iff (impl hk c) rfl,
    length_encodeTuple3, length_encDate]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  rw [← inClassW_iff]
  constructor
  · rintro ⟨hl, hc, he⟩
    exact ⟨⟨by unfold nAuth; omega, hc⟩, he⟩
  · rintro ⟨⟨hl, hc⟩, he⟩
    have hne : C ≠ [] := by rintro rfl; rw [not_inClassW_nil] at hc; cases hc
    have h1 : 1 ≤ C.length := List.length_pos_iff.mpr hne
    unfold nAuth at hl
    exact ⟨by omega, hc, he⟩

variable (hk c) in
/-- **The authorization component** computes the flag of the experiment. -/
theorem law_authPI (C : List Bool) (x : Date) :
    (authP (nAuth c.L)).law (io2 (R := 6) C (dateUniverse.encAttr x) []) =
      PMF.pure (io2 (R := 6) [authI hk c C x] [] []) := by
  rw [authI_eq hk c]
  exact law_authP _ C x

open Classical in
/-- The simulated key oracle from the output of the front end. -/
noncomputable def kgOfFront (d : SimData hk c) (C : List Bool) : List Bool → PMF (List Bool)
  | [] => PMF.pure []
  | false :: _ => PMF.pure ((skEnc hk c).enc (d.mpk, dummyKey c))
  | true :: _ => (keyLaw c.Big c.Small c.hBig c.dec d.mpk (simTrap (Wt := TrapCol k) (simW d C))).map
      fun o => (skEnc hk c).enc (d.mpk, keyOfOutput o)

/-- **`KGsim` through the front end.** -/
theorem KGsim_eq_front (W : ℕ) (d : SimData hk c) (C : List Bool) :
    KGsim d C = kgOfFront d C (frontV c.L W C) := by
  unfold KGsim
  by_cases hl : C.length ≤ c.L
  · by_cases hw : ∃ w : Window, winWord w = C
    · rw [frontV_win hl hw, if_pos hl, if_pos hw]; rfl
    · rw [frontV_short_not hl hw, if_pos hl, if_neg hw]; rfl
  · rw [frontV_long hl, if_neg hl]; rfl

/-- The simulated trapdoor reads the query through its gate list. -/
theorem simW_parse (d : SimData hk c) (C : List Bool) :
    simW d C = simKeyMat (S := Sdw (N := N) hk) d.Rm (bitsOf d.x) d.W d.Ψ d.mpk.Bj
      (predOf 10 (parse C)) := rfl

end AdvancedEncryption.DualUse
