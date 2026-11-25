import PE.Impl.RingBTVW.Prog.KeyP

/-!
# The time and length bounds of the key component

* the SimData block and the front end are bounded per tape: `sdP` on `io2 Ls 0 0` (its bounds
  `Ts`, `io2 Lsd 0 0` are hypotheses), the front end on `io2 K₀ 0 0` (`timeBoundT_frontP`,
  `lenBoundT_frontP`);
* the branches by uniform bounds (`UB`) from `M = max (max Lsd LF) (tmplMax …)`, the `W_f` block by
  a uniform-bound hypothesis `∀ M, UB wfB M (Twf M) (Gwf M)`;
* the final clearing makes the length bound `io2 L 0 0`.

**`time_keyP`**: `timeBoundT keyP (io2 Ls K₀ 0) ≤ Ts + frontT c.L W K₀ + branchT … M + clrT …` and
`lenBoundT keyP (io2 Ls K₀ 0) ≤ io2 (branchL … M) 0 0` (the `len_key` field of `CompBoundsP`).
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.XProg Matrix AdvancedEncryption.RingBTVW.Fresh Cslib Cslib.Probability
  AdvancedEncryption.RingBTVW.Algo
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord
open scoped SigabaNeo.Tape.Prog

/-! ### Uniform bounds of the helpers -/

section UBs

variable {n m : ℕ}

theorem ub_ifBit {i : Fin n} {p q : XProg n} {M T M' U M'' : ℕ} (hp : UB p M T M')
    (hq : UB q M U M'') : UB (ifBit i p q) M (max T U + 1) (max M' M'') := fun ℓ hℓ =>
  ⟨by show max _ _ + 1 ≤ _; have := (hp ℓ hℓ).1; have := (hq ℓ hℓ).1; omega,
    fun t => by show max _ _ ≤ _; exact max_le_max ((hp ℓ hℓ).2 t) ((hq ℓ hℓ).2 t)⟩

theorem ub_ifBlank {i : Fin n} {p q : XProg n} {M T M' U M'' : ℕ} (hp : UB p M T M')
    (hq : UB q M U M'') : UB (ifBlank i p q) M (max T U + 1) (max M' M'') := fun ℓ hℓ =>
  ⟨by show max _ _ + 1 ≤ _; have := (hp ℓ hℓ).1; have := (hq ℓ hℓ).1; omega,
    fun t => by show max _ _ ≤ _; exact max_le_max ((hp ℓ hℓ).2 t) ((hq ℓ hℓ).2 t)⟩

/-- A plain program from its global bounds. -/
theorem ub_prog (p : Prog n) (M : ℕ) : UB (prog p) M (Prog.timeBound p M) (Prog.lenBound p M) := by
  intro ℓ hℓ
  have hc : ℓ ≤ fun _ => M := hℓ
  exact ⟨(Prog.timeBoundT_mono p hc).trans (Prog.timeBoundT_const_le p M),
    fun i => ((Prog.lenBoundT_mono p hc).trans (Prog.lenBoundT_const_le p M)) i⟩

/-- A framed plain program from its global bounds. -/
theorem ub_frameP (e : Fin m ↪ Fin n) (p : Prog m) (M : ℕ) :
    UB (frame e (prog p)) M (Prog.timeBound p M) (max M (Prog.lenBound p M)) := by
  intro ℓ hℓ
  have hc : (fun j => ℓ (e j)) ≤ fun _ => M := fun j => hℓ (e j)
  refine ⟨?_, fun i => ?_⟩
  · rw [timeBoundT_frame, timeBoundT_prog]
    exact (Prog.timeBoundT_mono p hc).trans (Prog.timeBoundT_const_le p M)
  · show embedF e ℓ (Prog.lenBoundT p fun j => ℓ (e j)) i ≤ _
    rcases embedF_cases e ℓ (Prog.lenBoundT p fun j => ℓ (e j)) i with ⟨-, h⟩ | ⟨j, rfl, h⟩
    · rw [h]; exact (hℓ i).trans (le_max_left _ _)
    · rw [h]
      exact (((Prog.lenBoundT_mono p hc).trans (Prog.lenBoundT_const_le p M)) j).trans
        (le_max_right _ _)

theorem ub_copySelf (t : Fin n) (M : ℕ) : UB (prog (.prim (.copy t t))) M (2 * (M + 1) + 3) M := by
  intro ℓ hℓ
  refine ⟨((ub_prim _ M) ℓ hℓ).1, fun i => ?_⟩
  rw [lenBoundT_prim]
  simp only [Prim.lenT, Function.update_apply]
  split_ifs
  · exact hℓ _
  · exact hℓ i

/-- The time of `putW` of a word of `n` bits. -/
def putT (n M : ℕ) : ℕ := (n + 1) * (2 * (M + n + 1) + 3)

theorem ub_putW (t : Fin n) : ∀ (w : List Bool) (M : ℕ),
    UB (putW t w) M (putT w.length M) (M + w.length + 1)
  | [], M => (ub_copySelf t M).mono (by simp [putT]) (by omega)
  | b :: w, M => by
    refine ((ub_prim (.snoc t b) M).seq (ub_putW t w (M + 1))).mono ?_ (by simp; omega)
    simp only [putT, List.length_cons]
    nlinarith

/-- The time of `prefP P`. -/
def prefT (P M : ℕ) : ℕ :=
  (2 * (M + 1) + 3) + (P * (6 * (M + 1 + P) + 13) + 2 * (M + 1 + P) + 3) + (2 * (M + 1 + P + 1) + 3)

theorem ub_prefP (P : ℕ) (src dst a b : Fin n) (M : ℕ) :
    UB (prefP P src dst a b) M (prefT P M) (M + 1 + P) := by
  have u := (ub_prim (.copy a src) M).seq <|
    ((ub_prog (Prog.moveFront P a dst b) (M + 1)).mono (Prog.timeBound_moveFront_le P (M + 1))
      (Prog.lenBound_moveFront_le P (M + 1))).seq (ub_clear a (M + 1 + P))
  exact u.mono (by simp only [prefT]; omega) le_rfl

/-- The time of the templates. -/
def tmplT : List (Fin n × ℕ) → ℕ → ℕ
  | [], M => 2 * (M + 1) + 3
  | x :: l, M => (2 * x.2 + 1) * (4 * M + 12) + tmplT l M

/-- The largest template. -/
def tmplMax : List (Fin n × ℕ) → ℕ
  | [] => 0
  | x :: l => max x.2 (tmplMax l)

theorem le_tmplMax : ∀ (l : List (Fin n × ℕ)), ∀ x ∈ l, x.2 ≤ tmplMax l
  | [], _, h => by simp at h
  | y :: l, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (le_tmplMax l x h).trans (le_max_right _ _)

theorem ub_tmplP (c : Fin n) : ∀ (l : List (Fin n × ℕ)) (M : ℕ), (∀ x ∈ l, x.2 ≤ M) →
    (∀ x ∈ l, x.1 ≠ c) → UB (tmplP c l) M (tmplT l M) M
  | [], M, _, _ => ub_copySelf c M
  | x :: l, M, hM, hc => (ub_natP (Ne.symm (hc x (by simp))) (hM x (by simp))).seq
      (ub_tmplP c l M (fun y hy => hM y (by simp [hy])) (fun y hy => hc y (by simp [hy])))

/-- The per-tape length bound of a clearing. -/
theorem lenBoundT_clearL_le [NeZero n] : ∀ (l : List (Fin n)) (ℓ : Fin n → ℕ) (t : Fin n),
    lenBoundT (clearL l) ℓ t ≤ if t ∈ l then 0 else ℓ t
  | [], ℓ, t => by
    show (Prim.copy 0 0).lenT ℓ t ≤ _
    simp only [Prim.lenT, Function.update_apply, List.not_mem_nil, if_false]
    split_ifs with h
    · subst h; exact le_rfl
    · exact le_rfl
  | u :: l, ℓ, t => by
    show lenBoundT (clearL l) ((Prim.clear u).lenT ℓ) t ≤ _
    refine (lenBoundT_clearL_le l _ t).trans ?_
    simp only [Prim.lenT, Function.update_apply, List.mem_cons]
    split_ifs <;> simp_all

end UBs

/-! ### The branches -/

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

/-- The time of the key try (`timeBound_keyTrySimCoinsP`). -/
def keyTryT (M : ℕ) : ℕ :=
  23 * (M + 1) ^ 2 + SigabaNeo.Tape.Prog.tbC (ProgKey.keyTrySimP ⨾ SigabaNeo.Tape.Prog.clr 3) *
    (2 * M + 1) ^ SigabaNeo.Tape.Prog.tbD (ProgKey.keyTrySimP ⨾ SigabaNeo.Tape.Prog.clr 3)

theorem ub_keyTry (M : ℕ) : UB (frame eKT (prog ProgKey.keyTrySimCoinsP)) M (keyTryT M) (2 * M) :=
  (ub_frameP eKT _ M).mono (ProgKey.timeBound_keyTrySimCoinsP M)
    (max_le (by omega) (ProgKey.lenBound_keyTrySimCoinsP_le M))

variable (hk c) in
/-- The bound after the `W_f` block and the public key in the window branch. -/
def winB1 (Gwf : ℕ → ℕ) (M : ℕ) : ℕ := max (Gwf (M + 1)) M + 1 + lenPK hk c

variable (hk c) in
/-- The bound before the templates in the window branch. -/
def winB3 (Gwf : ℕ → ℕ) (cf : KeyCfg) (M : ℕ) : ℕ :=
  winB1 hk c Gwf M + cf.sW.length + 1 + (powW K (cf.B - 1)).length + 1

variable (hk c) in
/-- **The time of the window branch** from tapes below `M`. -/
def winT (Twf Gwf : ℕ → ℕ) (cf : KeyCfg) (M : ℕ) : ℕ :=
  (2 * (M + 1) + 3) + Twf (M + 1) + prefT (lenPK hk c) (max (Gwf (M + 1)) M) +
    putT cf.sW.length (winB1 hk c Gwf M) +
    putT (powW K (cf.B - 1)).length (winB1 hk c Gwf M + cf.sW.length + 1) +
    tmplT (keyTmpl hk c cf) (winB3 hk c Gwf cf M) + keyTryT (winB3 hk c Gwf cf M) +
    (keyClr.length * (2 * (2 * winB3 hk c Gwf cf M + 1) + 3) +
      (2 * (2 * winB3 hk c Gwf cf M + 1) + 3))

variable (hk c) in
theorem ub_winB {wfB : XProg 256} {Twf Gwf : ℕ → ℕ} (hU : ∀ M, UB wfB M (Twf M) (Gwf M))
    (cf : KeyCfg) {M : ℕ} (hM : tmplMax (keyTmpl hk c cf) ≤ M) :
    UB (winB hk c wfB cf) M (winT hk c Twf Gwf cf M) (2 * winB3 hk c Gwf cf M) := by
  have hT : ∀ x ∈ keyTmpl hk c cf, x.2 ≤ winB3 hk c Gwf cf M := fun x hx =>
    (le_tmplMax _ x hx).trans (hM.trans (by simp only [winB3, winB1]; omega))
  have u := (ub_prim (Prim.tail (1 : Fin 256)) M).seq <| ((hU (M + 1)).mono le_rfl (le_max_left _ M)).seq <|
    (ub_prefP (lenPK hk c) 0 1 100 101 _).seq <| (ub_putW 4 cf.sW _).seq <|
    (ub_putW 5 (powW K (cf.B - 1)) _).seq <|
    (ub_tmplP 120 (keyTmpl hk c cf) (winB3 hk c Gwf cf M) hT
      (keyTmpl_ne (Or.inr (Or.inr rfl)))).seq <|
    (ub_keyTry _).seq (ub_clearL _ keyClr)
  refine u.mono (le_of_eq ?_) le_rfl
  simp only [winT, winB1, Nat.add_assoc]

variable (hk c) in
/-- The bound after the prefix in the dummy branch. -/
def dumD (M : ℕ) : ℕ := M + 1 + lenPK hk c + ((keyEnc (N := N) (K := K) c).enc (dummyKey c)).length + 1

variable (hk c) in
/-- **The time of the dummy branch.** -/
def dumT (M : ℕ) : ℕ :=
  (2 * (M + 1) + 3) + prefT (lenPK hk c) M +
    putT ((keyEnc (N := N) (K := K) c).enc (dummyKey c)).length (M + 1 + lenPK hk c) +
    (2 * (dumD hk c M + 1) + 3) + (2 * (dumD hk c M + 1 + 1) + 3)

variable (hk c) in
theorem ub_dumB (M : ℕ) : UB (dumB hk c) M (dumT hk c M) (dumD hk c M + 1) := by
  have u := (ub_clear 1 M).seq <| (ub_prefP (lenPK hk c) 0 2 100 101 M).seq <|
    (ub_putW 2 ((keyEnc (N := N) (K := K) c).enc (dummyKey c)) _).seq <|
    (ub_prim (Prim.copy (0 : Fin 256) 2) _).seq (ub_clear 2 _)
  refine u.mono (le_of_eq ?_) (le_of_eq ?_)
  · simp only [dumT, dumD, Nat.add_assoc]
  · simp only [dumD, Nat.add_assoc]

/-- The time of the long branch. -/
def longT (M : ℕ) : ℕ := 1 * (2 * (M + 1) + 3) + (2 * (M + 1) + 3)

theorem ub_longB (M : ℕ) : UB longB M (longT M) M := ub_clearL M [0]

variable (hk c) in
/-- **The time of the branches.** -/
def branchT (Twf Gwf : ℕ → ℕ) (cf : KeyCfg) (M : ℕ) : ℕ :=
  max (winT hk c Twf Gwf cf M) (max (longT M) (dumT hk c M) + 1) + 1

variable (hk c) in
/-- **The length bound after the branches.** -/
def branchL (Gwf : ℕ → ℕ) (cf : KeyCfg) (M : ℕ) : ℕ :=
  max (2 * winB3 hk c Gwf cf M) (max M (dumD hk c M + 1))

variable (hk c) in
theorem ub_branchB {wfB : XProg 256} {Twf Gwf : ℕ → ℕ} (hU : ∀ M, UB wfB M (Twf M) (Gwf M))
    (cf : KeyCfg) {M : ℕ} (hM : tmplMax (keyTmpl hk c cf) ≤ M) :
    UB (branchB hk c wfB cf) M (branchT hk c Twf Gwf cf M) (branchL hk c Gwf cf M) :=
  ub_ifBit (ub_winB hk c hU cf hM) (ub_ifBlank (ub_longB M) (ub_dumB hk c M))

/-! ### The key component -/

/-- The time of the final clearing. -/
def clrT (M : ℕ) : ℕ := 256 * (2 * (M + 1) + 3) + (2 * (M + 1) + 3)

variable (hk c) in
/-- The uniform bound at the branches for a front end with output bound `LF`. -/
def keyMF (Lsd LF : ℕ) (cf : KeyCfg) : ℕ := max (max Lsd LF) (tmplMax (keyTmpl hk c cf))


variable (hk c) in
/-- **The time and length bounds of the key component for any front end** (`keyPF`), from the
phase bounds `FT`, `FL` of the front end (the `ph` field of `FrontSpec`): as `time_keyP` with
`FT K₀` for `frontT c.L W K₀` and `FL K₀` for `frontL c.L W`. -/
theorem time_keyPF {sdP : XProg 82} {Ls Ts Lsd : ℕ}
    (hsT : timeBoundT sdP (io2 (R := 80) Ls 0 0) ≤ Ts)
    (hsL : lenBoundT sdP (io2 (R := 80) Ls 0 0) ≤ io2 Lsd 0 0)
    {R : ℕ} {e : Fin (R + 2) ↪ Fin 256} (he : FrEmb e) {fr : XProg (R + 2)} {FT FL : ℕ → ℕ}
    (hfr : ∀ T, Ph fr (io2 (R := R) T 0 0) (FT T) (io2 (R := R) (FL T) 0 0))
    {wfB : XProg 256} {Twf Gwf : ℕ → ℕ} (hU : ∀ M, UB wfB M (Twf M) (Gwf M))
    (cf : KeyCfg) (K₀ : ℕ) :
    timeBoundT (keyPF hk c sdP e fr wfB cf) (io2 (R := 254) Ls K₀ 0) ≤
        Ts + FT K₀ + branchT hk c Twf Gwf cf (keyMF hk c Lsd (FL K₀) cf) +
          clrT (branchL hk c Gwf cf (keyMF hk c Lsd (FL K₀) cf)) ∧
      lenBoundT (keyPF hk c sdP e fr wfB cf) (io2 (R := 254) Ls K₀ 0) ≤
        io2 (branchL hk c Gwf cf (keyMF hk c Lsd (FL K₀) cf)) 0 0 := by
  set M := keyMF hk c Lsd (FL K₀) cf with hMdef
  have e1 : (fun j => io2 (R := 254) Ls K₀ 0 (eSd j)) = io2 (R := 80) Ls 0 0 := io2_eSd Ls K₀ 0
  have l1 : lenBoundT (frame eSd sdP) (io2 (R := 254) Ls K₀ 0) ≤ io2 (R := 254) Lsd K₀ 0 := by
    show embedF eSd _ (lenBoundT sdP fun j => io2 (R := 254) Ls K₀ 0 (eSd j)) ≤ _
    rw [e1, ← embedF_eSd Ls K₀ Lsd 0]
    exact embedF_mono _ le_rfl hsL
  have t1 : timeBoundT (frame eSd sdP) (io2 (R := 254) Ls K₀ 0) ≤ Ts := by
    rw [timeBoundT_frame, e1]; exact hsT
  set ℓ1 := lenBoundT (frame eSd sdP) (io2 (R := 254) Ls K₀ 0) with hℓ1
  have v1 : (fun j => ℓ1 (e j)) ≤ io2 (R := R) K₀ 0 0 := by
    rw [← io2_frEmb he Lsd K₀ 0]; exact fun j => l1 (e j)
  have pf := hfr K₀ _ v1
  have t2 : timeBoundT (frame e fr) ℓ1 ≤ FT K₀ := by rw [timeBoundT_frame]; exact pf.1
  have l2 : lenBoundT (frame e fr) ℓ1 ≤ io2 (R := 254) Lsd (FL K₀) 0 := by
    show embedF e ℓ1 (lenBoundT fr fun j => ℓ1 (e j)) ≤ _
    rw [← embedF_frEmb he Lsd K₀ (FL K₀) 0]
    exact embedF_mono _ l1 pf.2
  set ℓ2 := lenBoundT (frame e fr) ℓ1 with hℓ2
  have hℓ2M : ∀ t, ℓ2 t ≤ M := fun t => (l2 t).trans (by
    simp only [io2, hMdef, keyMF]; split_ifs <;> omega)
  have ub := ub_branchB hk c hU cf (M := M) (le_max_right _ _) ℓ2 hℓ2M
  have hc := ub_clearL (branchL hk c Gwf cf M) clrAll _ ub.2
  have hlen : clrAll.length * (2 * (branchL hk c Gwf cf M + 1) + 3) ≤
      256 * (2 * (branchL hk c Gwf cf M + 1) + 3) := Nat.mul_le_mul_right _ length_clrAll_le
  refine ⟨?_, fun t => ?_⟩
  · show timeBoundT (frame eSd sdP) _ + (timeBoundT (frame e fr) ℓ1 +
      (timeBoundT (branchB hk c wfB cf) ℓ2 +
        timeBoundT (clearL clrAll) (lenBoundT (branchB hk c wfB cf) ℓ2))) ≤ _
    have := ub.1
    have := hc.1
    simp only [clrT]
    omega
  · show lenBoundT (clearL clrAll) (lenBoundT (branchB hk c wfB cf) ℓ2) t ≤ _
    refine (lenBoundT_clearL_le clrAll _ t).trans ?_
    simp only [mem_clrAll]
    by_cases h : t = 0
    · subst h; simp [io2, ub.2 0]
    · have : t.val ≠ 0 := fun e => h (Fin.ext e)
      simp [h, io2, this]

end AdvancedEncryption.RingBTVW.Prog
