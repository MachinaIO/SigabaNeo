import PE.Impl.DualUse.Prog.KeyTrySimV
import PE.Impl.DualUse.Prog.KeyTightBfX

/-!
# The key component of the reductions, per tape

`time_keyPT` (`PE.Impl.DualUse.Prog.KeyPTimeT`) bounds the window branch after the `W_f` block
(`winRest`: the public key, the norm word, `powW`, the templates, the simulated key try, the
clearing) uniformly from the longest tape `Gw`; its key try is charged `tbC · (2M + 1)^tbD`. Here:

* `tt_winB_ph`, `tt_branchB_ph`, **`time_keyPV`**: the key component with the `W_f` block bounded
  per tape on its input (`lenBoundT wfB (wfIn …) ≤ βw`) and **any phase bound of `winRest` from
  `βw`** (`Ph (winRest …) βw TR (fun _ => GR)`): at most
  `Ts + frontT + branchTV Tw TR GR M + clrT (branchLV GR M)` steps (generic: no parameter of
  `confP`, no shape of `W_f`);
* **`ph_winRest_v`**: the phase bound of `winRest` when only tapes `0`, `2` are nonblank after the
  `W_f` block (`v02 G`, as for `wfB2`): every loop of the simulated key try charged its own counter
  (`ph_keyTrySim_v`), at most `winRV G` steps, every tape at most `simTop G = G + 1 + P` bits.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.XProg Matrix AdvancedEncryption.RingBTVW Cslib Cslib.Probability
  AdvancedEncryption.DualUse.Algo
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow
open scoped SigabaNeo.Tape.Prog

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-! ### The key component from a phase bound of `winRest` -/

/-- **The window branch** from the per-tape bound `βw` of the `W_f` block and a phase bound of
`winRest` from `βw`. -/
theorem tt_winB_ph {wfB : XProg 256} {Tw TR GR : ℕ} (cf : KeyCfg) {ℓ ι βw : Fin 256 → ℕ} {M : ℕ}
    (hℓι : ℓ ≤ ι) (hℓM : ∀ t, ℓ t ≤ M) (hwT : timeBoundT wfB ι ≤ Tw)
    (hwL : lenBoundT wfB ι ≤ βw) (hR : Ph (winRest hk c cf) βw TR (fun _ => GR)) :
    timeBoundT (winB hk c wfB cf) ℓ ≤ (2 * (M + 1) + 3) + Tw + TR ∧
      ∀ i, lenBoundT (winB hk c wfB cf) ℓ i ≤ GR := by
  set ℓ1 := lenBoundT (prog (.prim (.tail (1 : Fin 256)))) ℓ with hℓ1
  have h1 : ℓ1 ≤ ι := fun t => le_trans (by
    show Function.update ℓ 1 (ℓ 1 - 1) t ≤ ℓ t
    rw [Function.update_apply]; split_ifs with h
    · subst h; omega
    · exact le_rfl) (hℓι t)
  have t1 := (ub_prim (Prim.tail (1 : Fin 256)) M ℓ hℓM).1
  have t2 := (timeBoundT_mono wfB h1).trans hwT
  have r := hR (lenBoundT wfB ℓ1) ((lenBoundT_mono wfB h1).trans hwL)
  refine ⟨?_, fun i => r.2 i⟩
  rw [winB_eq]
  show timeBoundT (prog _) ℓ + (timeBoundT wfB ℓ1 + timeBoundT (winRest hk c cf) (lenBoundT wfB ℓ1)) ≤ _
  have := r.1
  omega

/-- The time of the branches with a phase bound of `winRest`. -/
def branchTV (Tw TR : ℕ) (M : ℕ) : ℕ :=
  max ((2 * (M + 1) + 3) + Tw + TR) (max (longT M) (dumT hk c M) + 1) + 1

/-- The length bound after the branches with a phase bound of `winRest`. -/
def branchLV (GR M : ℕ) : ℕ := max GR (max M (dumD hk c M + 1))

theorem tt_branchB_ph {wfB : XProg 256} {Tw TR GR : ℕ} (cf : KeyCfg) {ℓ ι βw : Fin 256 → ℕ}
    {M : ℕ} (hℓι : ℓ ≤ ι) (hℓM : ∀ t, ℓ t ≤ M) (hwT : timeBoundT wfB ι ≤ Tw)
    (hwL : lenBoundT wfB ι ≤ βw) (hR : Ph (winRest hk c cf) βw TR (fun _ => GR)) :
    timeBoundT (branchB hk c wfB cf) ℓ ≤ branchTV hk c Tw TR M ∧
      ∀ i, lenBoundT (branchB hk c wfB cf) ℓ i ≤ branchLV hk c GR M := by
  have w := tt_winB_ph hk c cf hℓι hℓM hwT hwL hR
  have u := ub_ifBlank (i := (1 : Fin 256)) (ub_longB M) (ub_dumB hk c M) ℓ hℓM
  refine ⟨?_, fun t => ?_⟩
  · show max _ _ + 1 ≤ _
    unfold branchTV
    have := w.1; have := u.1
    omega
  · show max _ _ ≤ _
    exact max_le_max (w.2 t) (u.2 t)

/-- **The time and length bounds of the key component with a phase bound of `winRest`**: as
`time_keyPT`, the window branch after the `W_f` block charged `TR` (from the per-tape bound `βw`
of the block's output) instead of the uniform `winRT`. -/
theorem time_keyPV {sdP : XProg 82} {Ls Ts Lsd : ℕ}
    (hsT : timeBoundT sdP (io2 (R := 80) Ls 0 0) ≤ Ts)
    (hsL : lenBoundT sdP (io2 (R := 80) Ls 0 0) ≤ io2 Lsd 0 0)
    {wfB : XProg 256} {Tw TR GR : ℕ} {βw : Fin 256 → ℕ} (W : ℕ) (cf : KeyCfg) (K₀ : ℕ)
    (hwT : timeBoundT wfB (wfIn Lsd (frontL c.L W)) ≤ Tw)
    (hwL : lenBoundT wfB (wfIn Lsd (frontL c.L W)) ≤ βw)
    (hR : Ph (winRest hk c cf) βw TR (fun _ => GR)) :
    timeBoundT (keyP hk c sdP wfB W cf) (io2 (R := 254) Ls K₀ 0) ≤
        Ts + frontT c.L W K₀ + branchTV hk c Tw TR (keyM hk c Lsd W cf) +
          clrT (branchLV hk c GR (keyM hk c Lsd W cf)) ∧
      lenBoundT (keyP hk c sdP wfB W cf) (io2 (R := 254) Ls K₀ 0) ≤
        io2 (branchLV hk c GR (keyM hk c Lsd W cf)) 0 0 := by
  set M := keyM hk c Lsd W cf with hMdef
  have e1 : (fun j => io2 (R := 254) Ls K₀ 0 (eSd j)) = io2 (R := 80) Ls 0 0 := io2_eSd Ls K₀ 0
  have l1 : lenBoundT (frame eSd sdP) (io2 (R := 254) Ls K₀ 0) ≤ io2 (R := 254) Lsd K₀ 0 := by
    show embedF eSd _ (lenBoundT sdP fun j => io2 (R := 254) Ls K₀ 0 (eSd j)) ≤ _
    rw [e1, ← embedF_eSd Ls K₀ Lsd 0]
    exact embedF_mono _ le_rfl hsL
  have t1 : timeBoundT (frame eSd sdP) (io2 (R := 254) Ls K₀ 0) ≤ Ts := by
    rw [timeBoundT_frame, e1]; exact hsT
  set ℓ1 := lenBoundT (frame eSd sdP) (io2 (R := 254) Ls K₀ 0) with hℓ1
  have v1 : (fun j => ℓ1 (eFr j)) ≤ io2 (R := 6) K₀ 0 0 := by
    rw [← io2_eFr Lsd K₀ 0]; exact fun j => l1 (eFr j)
  have t2 : timeBoundT (frame eFr (frontP c.L W)) ℓ1 ≤ frontT c.L W K₀ := by
    rw [timeBoundT_frame]
    exact (timeBoundT_mono _ v1).trans (timeBoundT_frontP c.L W K₀)
  have l2 : lenBoundT (frame eFr (frontP c.L W)) ℓ1 ≤ io2 (R := 254) Lsd (frontL c.L W) 0 := by
    show embedF eFr ℓ1 (lenBoundT (frontP c.L W) fun j => ℓ1 (eFr j)) ≤ _
    rw [← embedF_eFr Lsd K₀ (frontL c.L W) 0]
    exact embedF_mono _ l1 ((lenBoundT_mono _ v1).trans (lenBoundT_frontP c.L W K₀))
  set ℓ2 := lenBoundT (frame eFr (frontP c.L W)) ℓ1 with hℓ2
  have hℓ2M : ∀ t, ℓ2 t ≤ M := fun t => (l2 t).trans (by
    simp only [io2, hMdef, keyM]; split_ifs <;> omega)
  have ub := tt_branchB_ph hk c cf l2 hℓ2M hwT hwL hR
  have hc := ub_clearL (branchLV hk c GR M) clrAll _ ub.2
  have hlen : clrAll.length * (2 * (branchLV hk c GR M + 1) + 3) ≤
      256 * (2 * (branchLV hk c GR M + 1) + 3) := Nat.mul_le_mul_right _ length_clrAll_le
  refine ⟨?_, fun t => ?_⟩
  · show timeBoundT (frame eSd sdP) _ + (timeBoundT (frame eFr (frontP c.L W)) ℓ1 +
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

/-! ### `winRest` per tape -/

/-- The top of the simulated key try: `G`, then the public key copied from tape `0`. -/
def simTop (G : ℕ) : ℕ := G + 1 + lenPK hk c

/-- The values of the variables of `σKS`: the top, `N, K, k, d, nT, P, B, m`. -/
def ρS (G : ℕ) (cf : KeyCfg) : List ℕ :=
  [simTop hk c G, N, K, k, c.d, AdvancedEncryption.DualUse.Algo.nT k, lenPK hk c, cf.B, cf.m]

theorem keyTmpl_keys (cf : KeyCfg) : (keyTmpl hk c cf).map (fun x => x.1.val) =
    [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25] := rfl

/-- The templates of the simulated key try fit `σKS`. -/
theorem keyTmpl_fitS (G : ℕ) (cf : KeyCfg) : ∀ x ∈ keyTmpl hk c cf,
    x.2 ≤ Sym.pEval (ρS hk c G cf) (Sym.aGet KeySV.σKS x.1.val) := by
  intro x hx
  have hlt : x.1.val < 90 := by
    have := List.mem_map_of_mem (f := fun x : Fin 256 × ℕ => x.1.val) hx
    rw [keyTmpl_keys] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    omega
  rw [KeySV.aGet_σKS hlt]
  simp only [keyTmpl, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp [KeyV.σKR, KeyV.mo, KeyV.qK, KeyV.qN, KeyV.qNK, KeyV.qP, KeyV.qm, Sym.aGet, Sym.pEval,
      Sym.mEval, ρS] <;> ring_nf <;> omega

theorem keyTmpl_ne120 (cf : KeyCfg) : ∀ x ∈ keyTmpl hk c cf, x.1 ≠ (120 : Fin 256) :=
  keyTmpl_ne (Or.inr (Or.inr rfl))

theorem keyTmpl_nodup (cf : KeyCfg) : ((keyTmpl hk c cf).map Prod.fst).Nodup := by
  have : ((keyTmpl hk c cf).map Prod.fst).map Fin.val = [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
      17, 18, 19, 20, 21, 22, 23, 24, 25] := by rw [List.map_map]; exact keyTmpl_keys hk c cf
  exact List.Nodup.of_map _ (by rw [this]; decide)

theorem mem_keysS_iff (cf : KeyCfg) (t : Fin 256) : t ∈ (keyTmpl hk c cf).map Prod.fst ↔
    t.val ∈ [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25] := by
  have e : ((keyTmpl hk c cf).map Prod.fst).map Fin.val = [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
      17, 18, 19, 20, 21, 22, 23, 24, 25] := by
    rw [List.map_map]; exact keyTmpl_keys hk c cf
  constructor
  · intro h; rw [← e]; exact List.mem_map_of_mem h
  · intro h
    rw [← e] at h
    obtain ⟨u, hu, e'⟩ := List.mem_map.mp h
    rwa [Fin.ext e'] at hu

set_option maxRecDepth 100000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 100000 in
theorem σKS_classes : ∀ j : Fin 90,
    j.val ∉ [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25] →
    j.val ∉ [3, 41] →
    (j.val ∈ [0, 1, 2] ∧ Sym.aGet KeySV.σKS j.val = Sym.pTop) ∨
    (j.val ∈ [4, 5] ∧ Sym.aGet KeySV.σKS j.val = KeyV.qK) ∨
    (j.val ∉ [0, 1, 2, 4, 5] ∧ Sym.aGet KeySV.σKS j.val = ([] : Sym.Poly)) := by
  decide +kernel

/-- The time of `winRest` per tape, from `v02 G`, the sweeps of the key try bounded by `Wk`. -/
def winRV (G : ℕ) (cf : KeyCfg) (Wk : ℕ) : ℕ :=
  prefT (lenPK hk c) G +
    (cf.sW.length + 1) * (2 * (simTop hk c G + cf.sW.length + 1) + 3) +
    ((powW K (cf.B - 1)).length + 1) * (2 * (simTop hk c G + (powW K (cf.B - 1)).length + 1) + 3) +
    21 * ((2 * simTop hk c G + 1) * (4 * simTop hk c G + 12)) +
    (coinT (simTop hk c G) cf.m + (2 * simTop hk c G + 3) * Wk) +
    (25 * (2 * (simTop hk c G + 1) + 3) + (2 * (simTop hk c G + 1) + 3))


/-- `winRV` from bounds on its ingredients. -/
theorem winRV_le (G : ℕ) (cf : KeyCfg) (Wk : ℕ) {P T m s p : ℕ} (hP : lenPK hk c ≤ P)
    (hT : simTop hk c G ≤ T) (hs : cf.sW.length ≤ s) (hp : (powW K (cf.B - 1)).length ≤ p)
    (hm : cf.m ≤ m) :
    winRV hk c G cf Wk ≤ prefT P G + (s + 1) * (2 * (T + s + 1) + 3) +
      (p + 1) * (2 * (T + p + 1) + 3) + 21 * ((2 * T + 1) * (4 * T + 12)) +
      (coinT T m + (2 * T + 3) * Wk) + (25 * (2 * (T + 1) + 3) + (2 * (T + 1) + 3)) := by
  unfold winRV prefT coinT
  gcongr


/-- `dumT` from bounds on the public key and the dummy key. -/
theorem dumT_le (M : ℕ) {L D : ℕ} (hL : lenPK hk c ≤ L)
    (hD : ((keyEnc (N := N) (K := K) c).enc (dummyKey c)).length ≤ D) :
    dumT hk c M ≤ (2 * (M + 1) + 3) + prefT L M + putT D (M + 1 + L) +
      (2 * (M + 1 + L + D + 1 + 1) + 3) + (2 * (M + 1 + L + D + 1 + 1 + 1) + 3) := by
  unfold dumT dumD prefT putT
  gcongr

set_option maxHeartbeats 1000000 in
/-- **`winRest` per tape**: from tapes `0`, `2` below `G` and the others blank, at most `winRV G`
steps, every tape at most `simTop G` bits; the simulated key try charged per tape, its sweeps
`wKS` at the variables `ρS G cf` bounded by `Wk`. -/
theorem ph_winRest_v (G : ℕ) (cf : KeyCfg) {Wk : ℕ}
    (hWk : Sym.pEval (ρS hk c G cf) KeySV.wKS ≤ Wk) (hsW : cf.sW.length ≤ K)
    (hpw : (powW K (cf.B - 1)).length ≤ K) (hKT : K ≤ simTop hk c G)
    (hTm : ∀ x ∈ keyTmpl hk c cf, x.2 ≤ simTop hk c G) :
    Ph (winRest hk c cf) (v02 G) (winRV hk c G cf Wk) (fun _ => simTop hk c G) := by
  set T := simTop hk c G with hT
  set P := lenPK hk c with hP
  have hGT : G + 1 + P = T := rfl
  -- the public key
  set β1 : Fin 256 → ℕ := fun i => if i ∈ [1, 100, 101] then G + 1 + P else v02 G i with hβ1
  have q1 : Ph (prefP P 0 1 100 101) (v02 G) (prefT P G) β1 :=
    ph_of_ub_ws [1, 100, 101] (fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      exact preserves_prefP (Ne.symm hi.2.1) (Ne.symm hi.1) (Ne.symm hi.2.2))
      (ub_prefP P 0 1 100 101 G) (fun i => by simp only [v02]; split_ifs <;> omega)
  have hβ1T : ∀ i, β1 i ≤ T := fun i => by simp only [hβ1, v02]; split_ifs <;> omega
  have hβ14 : β1 4 = 0 := by simp [hβ1, v02]
  have hβ15 : β1 5 = 0 := by simp [hβ1, v02]
  -- the norm word and `powW`
  set β3 := Function.update β1 4 (β1 4 + cf.sW.length) with hβ3
  have q3 := ph_putW (4 : Fin 256) cf.sW β1
  have hβ3T : ∀ i, β3 i ≤ T := fun i => by
    simp only [hβ3, Function.update_apply]; split_ifs
    · rw [hβ14]; omega
    · exact hβ1T i
  set β4 := Function.update β3 5 (β3 5 + (powW K (cf.B - 1)).length) with hβ4
  have q4 := ph_putW (5 : Fin 256) (powW K (cf.B - 1)) β3
  have hβ35 : β3 5 = 0 := by simp [hβ3, hβ15]
  have hβ4T : ∀ i, β4 i ≤ T := fun i => by
    simp only [hβ4, Function.update_apply]; split_ifs
    · rw [hβ35]; omega
    · exact hβ3T i
  -- the templates
  set β5 := tmplB 120 (keyTmpl hk c cf) β4 with hβ5
  have q5 := ph_tmplP (120 : Fin 256) (keyTmpl hk c cf) β4 (keyTmpl_ne120 hk c cf)
  have hβ5T : ∀ i, β5 i ≤ T := tmplB_le 120 T _ β4 hβ4T hTm
  have hcount := tmplTT_le (120 : Fin 256) T (keyTmpl hk c cf) β4 hβ4T hTm
  have hlen : (keyTmpl hk c cf).length = 20 := rfl
  rw [hlen] at hcount
  -- the key try
  have h25 : β5 25 = cf.m := tmplB_key 120 _ β4 (keyTmpl_nodup hk c cf) (keyTmpl_ne120 hk c cf)
    (25, cf.m) (by simp [keyTmpl])
  have hfit : ∀ j : Fin 90, j.val ∉ [3, 41] →
      β5 (eKT j) ≤ Sym.pEval (ρS hk c G cf) (Sym.aGet KeySV.σKS j.val) := by
    intro j h341
    by_cases hkey : eKT j ∈ (keyTmpl hk c cf).map Prod.fst
    · obtain ⟨x, hx, hxj⟩ := List.mem_map.mp hkey
      rw [← hxj, hβ5, tmplB_key 120 _ β4 (keyTmpl_nodup hk c cf) (keyTmpl_ne120 hk c cf) x hx]
      have := keyTmpl_fitS hk c G cf x hx
      rwa [hxj, eKT_val] at this
    · have hne : eKT j ≠ 120 := fun e => by
        have := congrArg Fin.val e; rw [eKT_val] at this; have := j.isLt; simp at this; omega
      rw [hβ5, tmplB_of_not_mem 120 _ β4 _ hne hkey]
      rw [mem_keysS_iff hk c cf, eKT_val] at hkey
      rcases σKS_classes j hkey h341 with ⟨hm, hs⟩ | ⟨hm, hs⟩ | ⟨hm, hs⟩
      · rw [hs]
        have : Sym.pEval (ρS hk c G cf) Sym.pTop = T := by
          simp [Sym.pTop, Sym.pEval, Sym.mEval, ρS, hT]
        rw [this]; exact hβ4T _
      · rw [hs]
        have : Sym.pEval (ρS hk c G cf) KeyV.qK = K := by
          simp [KeyV.qK, KeyV.mo, Sym.pEval, Sym.mEval, ρS]
        rw [this]
        have hv : (eKT j).val = 4 ∨ (eKT j).val = 5 := by rw [eKT_val]; simpa using hm
        simp only [hβ4, hβ3, Function.update_apply]
        rcases hv with h | h
        · have e4 : eKT j = 4 := Fin.ext h
          simp [e4, hβ14, hsW]
        · have e5 : eKT j = 5 := Fin.ext h
          simp [e5, hβ15, hpw]
      · rw [hs]
        have hv := hm
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
        have hk' := hkey
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk'
        have h341' := h341
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h341'
        simp only [hβ4, hβ3, hβ1, v02, Function.update_apply, Fin.ext_iff, eKT_val,
          List.mem_cons, List.not_mem_nil, or_false]
        have := j.isLt
        split_ifs <;> simp_all <;> omega
  have hin : Function.update (Function.update (fun j => β5 (eKT j)) 3 (β5 (eKT 25))) 41
      (β5 (eKT 25)) ≤ Sym.bnd (ρS hk c G cf) KeySV.σKS := by
    intro j
    simp only [Function.update_apply]
    have h25' : β5 (eKT 25) = cf.m := h25
    split_ifs with h1 h2
    · subst h1
      rw [h25']
      simp [Sym.bnd, KeySV.σKS, KeyV.σKR, KeyV.qm, KeyV.mo, Sym.aGet, Sym.pEval, Sym.mEval, ρS]
    · subst h2
      rw [h25']
      simp [Sym.bnd, KeySV.σKS, KeyV.σKR, KeyV.qm, KeyV.mo, Sym.aGet, Sym.pEval, Sym.mEval, ρS]
    · refine hfit j ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun e => h2 (Fin.ext e), fun e => h1 (Fin.ext e)⟩
  have htop : ∀ j : Fin 90, β5 (eKT j) ≤ Sym.top (ρS hk c G cf) := fun j => hβ5T _
  have q6 := ph_frame eKT (ph_keyTrySim_v (ρS hk c G cf) (fun j => β5 (eKT j)) hin htop)
  have hβ6T : ∀ t, embedF eKT β5 (capB (ρS hk c G cf) KeySV.oKS) t ≤ T := by
    intro t
    rcases embedF_cases eKT β5 (capB (ρS hk c G cf) KeySV.oKS) t with ⟨-, e⟩ | ⟨j, -, e⟩
    · rw [e]; exact hβ5T t
    · rw [e]; exact capB_le_top _ _ _
  have q8 := ph_of_ub hβ6T (ub_clearL T keyClr)
  have hcl : keyClr.length = 25 := rfl
  rw [hcl] at q8
  have q6' : Ph (XProg.frame eKT (XProg.prog ProgKey.keyTrySimCoinsP)) β5
      (coinT T cf.m + (2 * T + 3) * Sym.pEval (ρS hk c G cf) KeySV.wKS)
      (embedF eKT β5 (capB (ρS hk c G cf) KeySV.oKS)) :=
    q6.mono le_rfl (le_of_eq (by
      have e1 : Sym.top (ρS hk c G cf) = T := rfl
      have e2 : β5 (eKT 25) = cf.m := h25
      rw [e1, e2])) le_rfl
  refine (q1.seq (q3.seq (q4.seq (q5.seq (q6'.seq q8))))).mono le_rfl ?_ le_rfl
  have s1 := supB_le_of hβ1T
  have s3 := supB_le_of hβ3T
  have m3 : (cf.sW.length + 1) * (2 * (supB β1 + cf.sW.length + 1) + 3) ≤
      (cf.sW.length + 1) * (2 * (T + cf.sW.length + 1) + 3) := Nat.mul_le_mul_left _ (by omega)
  have m4 : ((powW K (cf.B - 1)).length + 1) * (2 * (supB β3 + (powW K (cf.B - 1)).length + 1) + 3) ≤
      ((powW K (cf.B - 1)).length + 1) * (2 * (T + (powW K (cf.B - 1)).length + 1) + 3) :=
    Nat.mul_le_mul_left _ (by omega)
  have mW := Nat.mul_le_mul_left (2 * T + 3) hWk
  simp only [winRV, ← hT, ← hP]
  omega

end AdvancedEncryption.DualUse.Prog
