import PE.Impl.RingBTVW.Prog.KeyPTime
import SigabaNeo.Lib.Machines.Prog.MacroSize
import SigabaNeo.Lib.Machines.Prog.VecBound

/-!
# The key component with a per-tape bound of the `W_f` block

`time_keyP` bounds the `W_f` block by a uniform bound `∀ M, UB wfB M (Twf M) (Gwf M)`: every tape
charged as the longest. **`time_keyPT`** asks instead for the bounds of `wfB` at the one input it
gets inside the key component: the word of the simulation data on tape `0` (at most `Lsd` bits),
the gate list of the query on tape `1` (at most `frontL c.L W` bits), every other tape blank
(`wfIn`). With `timeBoundT wfB (wfIn …) ≤ Tw` and every tape after `wfB` at most `Gw ≥ keyM …`,
the rest of the window branch is bounded uniformly from `Gw` (`ub_winRest`), the other branches
as before.

Also: the constants of the key try (`tbD_keyTrySim = 8`, `tbC_keyTrySim_le`) and the states of the
key component (`size_keyP_le`).
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.XProg Matrix AdvancedEncryption.RingBTVW.Fresh Cslib Cslib.Probability
  AdvancedEncryption.RingBTVW.Algo
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord
open scoped SigabaNeo.Tape.Prog

/-! ### The constants of the key try -/

section KeyTry

open SigabaNeo.Tape.Prog AdvancedEncryption.RingBTVW.ProgKey

theorem tbD_keyTrySim : tbD (keyTrySimP ⨾ clr 3) = 8 := by
  have h1 : mvP.tbD = 2 := by decide +kernel
  have h2 : dropP.tbD = 2 := by decide +kernel
  have h3 : embP.tbD = 3 := by decide +kernel
  have h4 : matMulP.tbD = 8 := by decide +kernel
  have h5 : addRWP.tbD = 3 := by decide +kernel
  have h6 : subRWP.tbD = 3 := by decide +kernel
  have h7 : decP.tbD = 4 := by decide +kernel
  have h8 : ballP.tbD = 3 := by decide +kernel
  have h9 : (nop 0 : Prog 90).tbD = 1 := by decide +kernel
  simp only [keyTrySimP, ph1, ph2, ph3, ph4, clrWork, tbD, tbD_map, h1, h2, h3, h4, h5, h6, h7, h8,
    h9]
  rfl

theorem tbC_keyTrySim_le : tbC (keyTrySimP ⨾ clr 3) ≤ 20000 := by
  have h1 : mvP.tbC = 20 := by decide +kernel
  have h2 : dropP.tbC = 10 := by decide +kernel
  have h3 : embP.tbC = 204 := by decide +kernel
  have h4 : matMulP.tbC = 1716 := by decide +kernel
  have h5 : addRWP.tbC = 210 := by decide +kernel
  have h6 : subRWP.tbC = 210 := by decide +kernel
  have h7 : decP.tbC = 385 := by decide +kernel
  have h8 : ballP.tbC = 419 := by decide +kernel
  have h9 : (nop 0 : Prog 90).tbC = 3 := by decide +kernel
  simp only [keyTrySimP, ph1, ph2, ph3, ph4, clrWork, tbC, tbC_map, h1, h2, h3, h4, h5, h6, h7, h8,
    h9]
  norm_num

set_option maxRecDepth 100000 in
theorem size_keyTrySimCoinsP_le : keyTrySimCoinsP.size ≤ 2 ^ 17 := by
  have h0 : (coinsAt (3 : Fin 90) 25 41 42).size = 257 := by decide +kernel
  have h1 : mvP.size = 220 := by decide +kernel
  have h2 : dropP.size = 111 := by decide +kernel
  have h3 : embP.size = 2293 := by decide +kernel
  have h4 : matMulP.size = 19366 := by decide +kernel
  have h5 : addRWP.size = 2365 := by decide +kernel
  have h6 : subRWP.size = 2365 := by decide +kernel
  have h7 : decP.size = 4338 := by decide +kernel
  have h8 : ballP.size = 4719 := by decide +kernel
  have h9 : (nop 0 : Prog 90).size = 36 := by decide +kernel
  simp only [keyTrySimCoinsP, keyTrySimP, ph1, ph2, ph3, ph4, clrWork, Prog.size, size_map, h0, h1,
    h2, h3, h4, h5, h6, h7, h8, h9, Prim.pad]
  norm_num

end KeyTry

/-- The time of the key try, with its constants. -/
theorem keyTryT_le (M : ℕ) : keyTryT M ≤ 23 * (M + 1) ^ 2 + 20000 * (2 * M + 1) ^ 8 := by
  unfold keyTryT
  rw [tbD_keyTrySim]
  have := Nat.mul_le_mul_right ((2 * M + 1) ^ 8) tbC_keyTrySim_le
  omega

/-! ### The window branch after the `W_f` block -/

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

variable (hk c) in
/-- The bound after the prefix of the public key, from `G`. -/
def winR1 (G : ℕ) : ℕ := G + 1 + lenPK hk c

variable (hk c) in
/-- The bound before the templates, from `G`. -/
def winR3 (G : ℕ) (cf : KeyCfg) : ℕ :=
  winR1 hk c G + cf.sW.length + 1 + (powW K (cf.B - 1)).length + 1

variable (hk c) in
/-- **The time of the window branch after the `W_f` block**, from tapes below `G`. -/
def winRT (G : ℕ) (cf : KeyCfg) : ℕ :=
  prefT (lenPK hk c) G + putT cf.sW.length (winR1 hk c G) +
    putT (powW K (cf.B - 1)).length (winR1 hk c G + cf.sW.length + 1) +
    tmplT (keyTmpl hk c cf) (winR3 hk c G cf) + keyTryT (winR3 hk c G cf) +
    (keyClr.length * (2 * (2 * winR3 hk c G cf + 1) + 3) + (2 * (2 * winR3 hk c G cf + 1) + 3))

variable (hk c) in
/-- The window branch after the `W_f` block. -/
noncomputable def winRest (cf : KeyCfg) : XProg 256 :=
  seq (prefP (lenPK hk c) 0 1 100 101) <| seq (putW 4 cf.sW) <| seq (putW 5 (powW K (cf.B - 1))) <|
  seq (tmplP 120 (keyTmpl hk c cf)) <| seq (frame eKT (prog ProgKey.keyTrySimCoinsP)) (clearL keyClr)

theorem winB_eq (wfB : XProg 256) (cf : KeyCfg) :
    winB hk c wfB cf = seq (prog (.prim (.tail 1))) (seq wfB (winRest hk c cf)) := rfl

variable (hk c) in
theorem ub_winRest (cf : KeyCfg) {G : ℕ} (hG : tmplMax (keyTmpl hk c cf) ≤ G) :
    UB (winRest hk c cf) G (winRT hk c G cf) (2 * winR3 hk c G cf) := by
  have hT : ∀ x ∈ keyTmpl hk c cf, x.2 ≤ winR3 hk c G cf := fun x hx =>
    (le_tmplMax _ x hx).trans (hG.trans (by simp only [winR3, winR1]; omega))
  have u := (ub_prefP (lenPK hk c) 0 1 100 101 G).seq <| (ub_putW 4 cf.sW _).seq <|
    (ub_putW 5 (powW K (cf.B - 1)) _).seq <|
    (ub_tmplP 120 (keyTmpl hk c cf) (winR3 hk c G cf) hT
      (keyTmpl_ne (Or.inr (Or.inr rfl)))).seq <|
    (ub_keyTry _).seq (ub_clearL _ keyClr)
  refine u.mono (le_of_eq ?_) le_rfl
  simp only [winRT, winR1, Nat.add_assoc]

variable (hk c) in
/-- **The window branch with a per-tape bound of the `W_f` block** at the input bound `ι`. -/
theorem tt_winB {wfB : XProg 256} {Tw Gw : ℕ} (cf : KeyCfg) {ℓ ι : Fin 256 → ℕ} {M : ℕ}
    (hℓι : ℓ ≤ ι) (hℓM : ∀ t, ℓ t ≤ M) (hwT : timeBoundT wfB ι ≤ Tw)
    (hwL : ∀ i, lenBoundT wfB ι i ≤ Gw) (hG : tmplMax (keyTmpl hk c cf) ≤ Gw) :
    timeBoundT (winB hk c wfB cf) ℓ ≤ (2 * (M + 1) + 3) + Tw + winRT hk c Gw cf ∧
      ∀ i, lenBoundT (winB hk c wfB cf) ℓ i ≤ 2 * winR3 hk c Gw cf := by
  set ℓ1 := lenBoundT (prog (.prim (.tail (1 : Fin 256)))) ℓ with hℓ1
  have h1 : ℓ1 ≤ ι := fun t => le_trans (by
    show Function.update ℓ 1 (ℓ 1 - 1) t ≤ ℓ t
    rw [Function.update_apply]; split_ifs with h
    · subst h; omega
    · exact le_rfl) (hℓι t)
  have t1 := (ub_prim (Prim.tail (1 : Fin 256)) M ℓ hℓM).1
  have t2 := (timeBoundT_mono wfB h1).trans hwT
  have l2 : ∀ i, lenBoundT wfB ℓ1 i ≤ Gw := fun i => (lenBoundT_mono wfB h1 i).trans (hwL i)
  have r := ub_winRest hk c cf hG (lenBoundT wfB ℓ1) l2
  refine ⟨?_, r.2⟩
  rw [winB_eq]
  show timeBoundT (prog _) ℓ + (timeBoundT wfB ℓ1 + timeBoundT (winRest hk c cf) (lenBoundT wfB ℓ1)) ≤ _
  have := r.1
  omega

variable (hk c) in
/-- **The time of the branches** with the per-tape bound of the `W_f` block. -/
def branchTT (Tw Gw : ℕ) (cf : KeyCfg) (M : ℕ) : ℕ :=
  max ((2 * (M + 1) + 3) + Tw + winRT hk c Gw cf) (max (longT M) (dumT hk c M) + 1) + 1

variable (hk c) in
/-- **The length bound after the branches** with the per-tape bound of the `W_f` block. -/
def branchLT (Gw : ℕ) (cf : KeyCfg) (M : ℕ) : ℕ :=
  max (2 * winR3 hk c Gw cf) (max M (dumD hk c M + 1))

variable (hk c) in
theorem tt_branchB {wfB : XProg 256} {Tw Gw : ℕ} (cf : KeyCfg) {ℓ ι : Fin 256 → ℕ} {M : ℕ}
    (hℓι : ℓ ≤ ι) (hℓM : ∀ t, ℓ t ≤ M) (hwT : timeBoundT wfB ι ≤ Tw)
    (hwL : ∀ i, lenBoundT wfB ι i ≤ Gw) (hG : tmplMax (keyTmpl hk c cf) ≤ Gw) :
    timeBoundT (branchB hk c wfB cf) ℓ ≤ branchTT hk c Tw Gw cf M ∧
      ∀ i, lenBoundT (branchB hk c wfB cf) ℓ i ≤ branchLT hk c Gw cf M := by
  have w := tt_winB hk c cf hℓι hℓM hwT hwL hG
  have u := ub_ifBlank (i := (1 : Fin 256)) (ub_longB M) (ub_dumB hk c M) ℓ hℓM
  refine ⟨?_, fun t => ?_⟩
  · show max _ _ + 1 ≤ _
    unfold branchTT
    have := w.1; have := u.1
    omega
  · show max _ _ ≤ _
    exact max_le_max (w.2 t) (u.2 t)

/-! ### The key component -/

/-- **The input bound of the `W_f` block** inside the key component: the word of the simulation
data (at most `Lsd` bits) on tape `0`, the gate list of the query (at most `LF` bits) on tape `1`. -/
abbrev wfIn (Lsd LF : ℕ) : Fin 256 → ℕ := io2 (R := 254) Lsd LF 0

/-! ### The states of the key component -/

section Size

variable {n : ℕ}

theorem size_putWX (t : Fin n) : ∀ w : List Bool, (putW t w).size ≤ 60 * (w.length + 1)
  | [] => by simp [putW, Prim.pad]
  | b :: w => by
    have := size_putWX t w
    simp only [putW, size_seq, size_prog, Prog.size_prim, Prim.pad, List.length_cons]
    omega

theorem size_prefP (P : ℕ) (src dst a b : Fin n) : (prefP P src dst a b).size ≤ 132 * P + 108 := by
  simp [prefP, Prim.pad]; omega

theorem size_clearL_le [NeZero n] : ∀ l : List (Fin n), (clearL l).size ≤ 36 * (l.length + 1)
  | [] => by simp [clearL, Prim.pad]
  | t :: l => by
    have := size_clearL_le l
    simp only [clearL, size_seq, size_prog, Prog.size_prim, Prim.pad, List.length_cons]
    omega

theorem size_tmplP_le (c : Fin n) (m : ℕ) : ∀ l : List (Fin n × ℕ), (∀ x ∈ l, x.2 < 2 ^ m) →
    (tmplP c l).size ≤ l.length * (195 * m + 36) + 36
  | [], _ => by simp [tmplP, Prim.pad]
  | x :: l, h => by
    have h1 := size_natP_le x.1 c x.2 m (h x (by simp))
    have h2 := size_tmplP_le c m l (fun y hy => h y (by simp [hy]))
    simp only [tmplP, size_seq, List.length_cons]
    rw [Nat.succ_mul]
    omega

end Size

end AdvancedEncryption.RingBTVW.Prog
