import PE.Impl.DualUse.Prog.WfB2Size
import SigabaNeo.Lib.Machines.GatesSLPBound
import PE.Impl.DualUse.Prog.FhatGen
import PE.Impl.DualUse.Params.Conf

/-!
# The block-structured `W_f` block at `confP`

The hypotheses of `wfSpec_wfB2`, `time_wfB2_conf`, `size_wfB2_conf` and `time_keyP_wfB2` at the
parameters `confP`:
* the windows (`hP_win`): a window predicate parses to its gate list, nonempty, of at most
  `375` gates, every wire index at most `385` (`gates_facts`, through `bnd_predGates`);
* `treeHeight Np kp = 61 ≤ 64` (`treeHeight_conf`);
* the stream offsets and `|sdEnc|` below `2^238 ≤ Lb = 2^240` (`offs_conf`, closed forms of the encodings);
* `bpLen ≤ 2^20` and the front end's output `frontL bpLen 512 ≤ 2^64` (`frontL_le`).

**`wfB2_confP`**: at `confP` the block meets its specification `WfSpec`, has at most `2^25`
states and runs in at most `2^556` steps; **`time_keyP_confP`**: the key component with it.
-/

namespace AdvancedEncryption.DualUse.Prog

namespace WB2

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.ValVM SigabaNeo.Tape.Prog
  SigabaNeo.Lattices SigabaNeo.Lattices.SLP AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
  AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord AdvancedEncryption.DualUse.Params

set_option maxRecDepth 100000

/-! ### The windows -/

/-- **The gate list of the window predicate of two dates**: nonempty, at most `375` gates, wire
indices at most `385`. -/
theorem gates_facts (a b : PUniv.Attr) :
    predGates (compile [] (winExp a b)).1 (compile [] (winExp a b)).2 ≠ [] ∧
      (predGates (compile [] (winExp a b)).1 (compile [] (winExp a b)).2).length ≤ 375 ∧
      ∀ x ∈ predGates (compile [] (winExp a b)).1 (compile [] (winExp a b)).2,
        x.1 ≤ 385 ∧ x.2 ≤ 385 := by
  have hg := good_compile (winExp a b) (closed_nil (ι := Fin 10))
  have hl : (compile ([] : SLP (Fin 10)) (winExp a b)).1.length ≤ 374 := by
    have := SLP.length_compile (winExp a b) []
    rw [size_winExp] at this
    simpa using this
  have hlen := length_predGates (compile ([] : SLP (Fin 10)) (winExp a b)).1
    (compile [] (winExp a b)).2
  have hb := bnd_predGates hg.1 hg.2.1
  refine ⟨fun h => by rw [h] at hlen; simp at hlen, by omega, fun x hx => ?_⟩
  have := hb x hx
  omega

theorem parse_pairWord (p : PUniv.Attr × PUniv.Attr) :
    parse (pairWord p) = predGates (compile [] (winExp p.1 p.2)).1 (compile [] (winExp p.1 p.2)).2 := by
  rw [pairWord, parse_unparse]

/-- **The windows' gate lists fit `W = 512`.** -/
theorem hP_win (L : ℕ) : ∀ C : List Bool, C.length ≤ L → (∃ w : Window, winWord w = C) →
    parse C ≠ [] ∧ (parse C).length + 10 ≤ Wc ∧ BndG Wc (parse C) := by
  rintro C - ⟨w, rfl⟩
  rw [winWord_eq_pairWord, parse_pairWord]
  obtain ⟨h1, h2, h3⟩ := gates_facts w.1.1 w.1.2
  exact ⟨h1, by simp only [Wc]; omega, fun x hx => by have := h3 x hx; simp only [Wc]; omega⟩

/-- **The block meets its specification** at `W = 512`. -/
theorem wfSpec_wfB2_conf {N K : ℕ} (hk : 2 ^ K < 2 ^ (K + 1)) (c : Conf N K (K + 1)) (hN : 0 < N)
    (hK : 0 < K) : WfSpec hk c (wfB2 hk c Wc) Wc :=
  wfSpec_wfB2 hk c Wc hN hK (hP_win c.L)

/-! ### The tree height and the stream offsets -/

theorem treeHeight_conf : treeHeight Nc (Kc + 1) ≤ 64 := by
  unfold treeHeight
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
  exact Nat.clog_le_of_le_pow (by simp only [Nc, Kc]; norm_num)

theorem lenAI {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) :
    (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).length =
      10 * (4 * k * N * k) :=
  nT_eq (N := N) (K := K) hk

/-- **The stream offsets and the SimData word at `confP`** are below `2^240`. -/
theorem offs_conf {N K : ℕ} (hk : 2 ^ K < 2 ^ (K + 1)) (c : Conf N K (K + 1)) (hN : N = Nc)
    (hK : K = Kc) (hd : c.d = dc) :
    offB c ≤ Lb ∧ offW hk c ≤ Lb ∧ offPsi hk c ≤ Lb ∧ offR hk c ≤ Lb ∧
      offPsi hk c + 10 * lenPsi N K (K + 1) ≤ Lb ∧ fixLen (sdEnc hk c) ≤ Lb := by
  simp only [offB, offW, offR, offPsi, lenPsi, fixLen, Algo.len_fin, Algo.len_col,
    Algo.len_trapCol, lenAI, hd]
  subst hN hK
  decide +kernel

/-! ### The front end -/

theorem length_winWord (w : Window) : (winWord w).length ≤ 375 * 772 := by
  rw [winWord_eq_pairWord, pairWord, length_unparse]
  obtain ⟨-, h2, h3⟩ := gates_facts w.1.1 w.1.2
  have := List.sum_le_length_nsmul
    ((predGates (compile [] (winExp w.1.1 w.1.2)).1 (compile [] (winExp w.1.1 w.1.2)).2).map
      fun g => g.1 + g.2 + 2) 772 (by
        intro y hy
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hy
        have := h3 g hg
        omega)
  rw [List.length_map, smul_eq_mul] at this
  exact this.trans (Nat.mul_le_mul_right _ h2)

/-- **The longest input word of `Eval` on a window predicate** has at most `2^20` bits. -/
theorem bpLen_le : bpLen ≤ 2 ^ 20 := by
  rw [bpLen]
  apply Finset.sup_le
  rintro ⟨w, x⟩ -
  rw [length_encodeTuple3]
  have hp : (paramsWord PUniv params).length = 515 := by
    rw [paramsWord, length_encodeTuple3]
    simp [params, PUniv]
  have hx : (PUniv.encAttr x).length = 10 := length_encAttr x
  have hw := length_winWord w
  simp only at hp hx hw ⊢
  omega

theorem length_windows : windows.length ≤ 2 ^ 20 := by
  have ha : allDates.length = 2 ^ 10 := by
    rw [allDates, List.length_product, List.length_finRange]; norm_num
  have h := List.length_filter_le isWindow (allDates ×ˢ allDates)
  rw [List.length_product, ha] at h
  rw [windows]
  exact h

theorem length_frontTbl (n W : ℕ) : (frontTbl n W).length ≤ 2 ^ 20 := by
  rw [frontTbl, List.length_map, winsN]
  exact (List.length_filter_le _ _).trans length_windows

theorem entry_frontTbl {n : ℕ} (hn : n ≤ 2 ^ 20) :
    ∀ e ∈ frontTbl n Wc, e.1.length + e.2.length ≤ 2 ^ 20 + 1 + (1 + 375 * 1024) := by
  intro e he
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp he
  simp only [length_padW, List.length_cons]
  rw [parse_pairWord]
  obtain ⟨-, h2, h3⟩ := gates_facts p.1 p.2
  rw [length_gsW (fun g hg => by have := h3 g hg; simp only [Wc]; omega)]
  have : (predGates (compile [] (winExp p.1 p.2)).1 (compile [] (winExp p.1 p.2)).2).length *
      (2 * Wc) ≤ 375 * 1024 := by simp only [Wc]; omega
  omega

/-- The front end's output on inputs of at most `n ≤ 2^20` bits has at most `2^64` bits. -/
theorem frontL_le' {n : ℕ} (hn : n ≤ 2 ^ 20) : frontL n Wc ≤ Lgc := by
  unfold frontL
  have ht := length_frontTbl n Wc
  have he := entry_frontTbl hn
  have hl := lookCount_le _ [false] he
  have hm := Nat.mul_le_mul_right (2 ^ 20 + 1 + (1 + 375 * 1024) + 4) ht
  simp only [List.length_singleton] at hl
  generalize lookCount (frontTbl n Wc) [false] = x at hl ⊢
  generalize (frontTbl n Wc).length = y at hl hm
  have e : Lgc = 2 ^ 64 := rfl
  rw [e]
  norm_num at hm hl hn ⊢
  omega

/-- **The front end's output at `confP`** has at most `2^64` bits. -/
theorem frontL_le : frontL bpLen Wc ≤ Lgc := frontL_le' bpLen_le

/-! ### At `confP` -/

theorem hN_conf : Np = Nc := by rw [Np_def]; rfl
theorem hK_conf : Kp = Kc := by rw [Kp_def]; rfl
theorem hd_conf : confP.d = dc := by show dp = dc; rw [dp_def]; rfl

/-- **The block at `confP`**: its specification, at most `2^25` states, at most `2^556` steps on
SimData words of at most `2^240` bits and gate lists of at most `2^64` bits, every tape below
`2^250` afterwards. -/
theorem wfB2_confP :
    WfSpec hkp confP (wfB2 hkp confP Wc) Wc ∧ (wfB2 hkp confP Wc).size ≤ 2 ^ 25 ∧
      ∀ Lsd Lg : ℕ, Lsd ≤ Lb → Lg ≤ Lgc →
        XProg.timeBoundT (wfB2 hkp confP Wc) (io2 (R := 254) Lsd Lg 0) ≤ 2 ^ 556 ∧
        ∀ t, XProg.lenBoundT (wfB2 hkp confP Wc) (io2 (R := 254) Lsd Lg 0) t ≤ Mall := by
  have hth : treeHeight Np (Kp + 1) ≤ 64 := by rw [hN_conf, hK_conf]; exact treeHeight_conf
  obtain ⟨hoB, hoW, hoP, hoR, hoX, -⟩ := offs_conf hkp confP hN_conf hK_conf hd_conf
  refine ⟨wfSpec_wfB2_conf hkp confP Np_pos (by rw [Kp_def]; norm_num),
    size_wfB2_conf hkp confP hN_conf hK_conf hd_conf hth hoB hoW hoP hoR hoX,
    fun Lsd Lg hLsd hLg => time_wfB2_conf hkp confP hN_conf hK_conf hd_conf hth hoB hoW hoP hoR hoX
      Lsd Lg hLsd hLg⟩

/-- **The key component with the block at `confP`**: `time_keyP_wfB2` with every hypothesis on the
block discharged; what remains is the SimData program `sdP` (its time and its output below
`2^240` bits, e.g. `Lsd = fixLen (sdEnc hkp confP)`, `offs_conf`). -/
theorem time_keyP_confP {sdP : XProg 82} {Ls Ts Lsd : ℕ}
    (hsT : XProg.timeBoundT sdP (io2 (R := 80) Ls 0 0) ≤ Ts)
    (hsL : XProg.lenBoundT sdP (io2 (R := 80) Ls 0 0) ≤ io2 Lsd 0 0) (hLsd : Lsd ≤ Lb)
    (cf : KeyCfg) (K₀ : ℕ) :
    XProg.timeBoundT (keyP hkp confP sdP (wfB2 hkp confP Wc) Wc cf) (io2 (R := 254) Ls K₀ 0) ≤
        Ts + frontT confP.L Wc K₀ + branchT hkp confP (fun _ => 2 ^ 556) (fun _ => Mall) cf
          (keyM hkp confP Lsd Wc cf) +
          clrT (branchL hkp confP (fun _ => Mall) cf (keyM hkp confP Lsd Wc cf)) ∧
      XProg.lenBoundT (keyP hkp confP sdP (wfB2 hkp confP Wc) Wc cf) (io2 (R := 254) Ls K₀ 0) ≤
        io2 (branchL hkp confP (fun _ => Mall) cf (keyM hkp confP Lsd Wc cf)) 0 0 := by
  have hth : treeHeight Np (Kp + 1) ≤ 64 := by rw [hN_conf, hK_conf]; exact treeHeight_conf
  obtain ⟨hoB, hoW, hoP, hoR, hoX, -⟩ := offs_conf hkp confP hN_conf hK_conf hd_conf
  exact time_keyP_wfB2 hkp confP hN_conf hK_conf hd_conf hth hoB hoW hoP hoR hoX hsT hsL hLsd
    (by rw [confP_L]; exact frontL_le) cf K₀

end WB2

end AdvancedEncryption.DualUse.Prog
