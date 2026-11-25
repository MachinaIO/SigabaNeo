import PE.Impl.RingBTVW.Prog.SetupCostP
import SigabaNeo.Lib.Machines.Prog.FrameIO
import PE.Impl.RingBTVW.Prog.KeyPTime

/-!
# The time of the compiled `Enc`

`ub_encP`: from tapes below `M` (above the samplers' thresholds and the parse and template sizes),
`encP` takes at most `encT …` steps and leaves every tape below `encG …`: the parser (`dropChunk`,
`ufChunk`), the framed samplers, the templates, the core (`tbC · (M + 1)^tbD`), the output frame.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg

theorem ub_tailX {k : ℕ} (S : Fin k) (X : ℕ) : UB (prog (.prim (.tail S))) X (2 * (X + 1) + 3) X :=
  fun ℓ hℓ => SigabaNeo.Tape.Prog.ubp_prim0 (.tail S) rfl X ℓ hℓ

/-- The time of `dropChunk n` from tapes below `M`. -/
def dropCT (n M : ℕ) : ℕ :=
  (2 * n + 1) * (4 * M + 12) + (forT (fun X => 2 * (X + 1) + 3) 0 M + (2 * (M + M * 0 + 1) + 3))

theorem ub_dropChunk (n M : ℕ) (hn : n ≤ M) : UB (dropChunk n) M (dropCT n M) (M + M * 0) :=
  (ub_natP (by decide) hn).seq ((ub_forN (fun X => ub_tailX (120 : Fin 124) X |>.mono le_rfl
    (by omega)) M).seq (ub_clear 121 _))

/-- The time of `ufChunk` from tapes below `M`. -/
def ufCT (n M : ℕ) : ℕ :=
  (2 * n + 1) * (4 * M + 12) + (forT (fun X => (2 * (X + 1) + 3) + ((2 * (X + 1) + 3) +
    (2 * (X + 1 + 1) + 3))) 1 M + (2 * (M + M * 1 + 1) + 3))

theorem ub_ufChunk (D : Fin 124) (n M : ℕ) (hn : n ≤ M) : UB (ufChunk D n) M (ufCT n M) (M + M * 1) :=
  (ub_natP (by decide) hn).seq ((ub_forN (fun X => ((ub_tailX 120 X).seq ((ub_prim (.snocHead D 120) X).seq
    (ub_tailX 120 (X + 1))))) M).seq (ub_clear 121 _))

/-- The time of the templates `natL l` from tapes below `M`. -/
def natLT : List (Fin 124 × ℕ) → ℕ → ℕ
  | [], M => 2 * (M + 1) + 3
  | p :: l, M => (2 * p.2 + 1) * (4 * M + 12) + natLT l M

theorem ub_natL : ∀ (l : List (Fin 124 × ℕ)) (M : ℕ), (∀ p ∈ l, p.2 ≤ M) → (∀ p ∈ l, p.1 ≠ 123) →
    UB (natL l) M (natLT l M) M
  | [], M, _, _ => ub_copySelf 123 M
  | p :: l, M, hM, hc => (ub_natP (Ne.symm (hc p (by simp))) (hM p (by simp))).seq
      (ub_natL l M (fun q hq => hM q (by simp [hq])) (fun q hq => hc q (by simp [hq])))

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The bound after the parser of `Enc`. -/
def parseEG (M : ℕ) : ℕ :=
  let P0 := M + M * 0
  let P1 := P0 + P0 * 1
  let P2 := P1 + P1 * 1
  let P3 := P2 + P2 * 1
  let P4 := P3 + P3 * 1
  let P5 := P4 + P4 * 1
  P5 + P5 * 1

/-- The time of the parser of `Enc`. -/
def parseET (M : ℕ) : ℕ :=
  let P0 := M + M * 0
  let P1 := P0 + P0 * 1
  let P2 := P1 + P1 * 1
  let P3 := P2 + P2 * 1
  let P4 := P3 + P3 * 1
  let P5 := P4 + P4 * 1
  dropCT (2 * RingBTVW.pw.length + 1) M +
    (ufCT ((Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K))) P0 +
    (ufCT ((Enum.list (α := Fin 1)).length * ((Enum.list (α := TrapCol k)).length * (N * K))) P1 +
    (ufCT ((Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).length *
      ((Enum.list (α := Fin 1)).length * ((Enum.list (α := RingBTVW.Fresh.Col k)).length * (N * K)))) P2 +
    (ufCT (N * K) P3 + ((2 * (P4 + 1) + 3) + (ufCT nA P4 + ((2 * (P5 + 1) + 3) + ufCT 1 P5)))))))

set_option maxRecDepth 100000 in
theorem ub_encParseP (M : ℕ)
    (h0 : 2 * RingBTVW.pw.length + 1 ≤ M)
    (h1 : (Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K)) ≤ M)
    (h2 : (Enum.list (α := Fin 1)).length * ((Enum.list (α := TrapCol k)).length * (N * K)) ≤ M)
    (h3 : (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).length *
      ((Enum.list (α := Fin 1)).length * ((Enum.list (α := RingBTVW.Fresh.Col k)).length * (N * K))) ≤ M)
    (h4 : N * K ≤ M) (h5 : nA ≤ M) :
    UB (encParseP hk c) M (parseET hk c M) (parseEG M) := by
  rw [encParseP]
  refine ((ub_dropChunk _ M h0).seq <| (ub_ufChunk 1 _ _ (by omega)).seq <|
    (ub_ufChunk 2 _ _ (by omega)).seq <| (ub_ufChunk 3 _ _ (by omega)).seq <|
    (ub_ufChunk 4 _ _ (by omega)).seq <| (ub_tailX 120 _).seq <| (ub_ufChunk 5 _ _ (by omega)).seq <|
    (ub_tailX 120 _).seq (ub_ufChunk 6 _ _ (by omega))).mono (le_of_eq rfl) (le_of_eq rfl)

/-- The bound after the samplers of `Enc`. -/
def encS (Bχ : Bnd) (M : ℕ) : ℕ :=
  let S1 := M + (bCoins (N * K)).a + (bCoins (N * K)).s
  let S2 := S1 + (Bχ.count ((Enum.list (α := Fin c.d)).length * N)).a +
    (Bχ.count ((Enum.list (α := Fin c.d)).length * N)).s
  let S3 := S2 + (Bχ.count N).a + (Bχ.count N).s
  let S4 := S3 + (Bχ.count ((Enum.list (α := RingBTVW.Fresh.Col k)).length * N)).a +
    (Bχ.count ((Enum.list (α := RingBTVW.Fresh.Col k)).length * N)).s
  let S5 := S4 + (Bχ.count ((Enum.list (α := RingBTVW.Fresh.Col k)).length * N)).a +
    (Bχ.count ((Enum.list (α := RingBTVW.Fresh.Col k)).length * N)).s
  let S6 := S5 + ((bEntB N K).count (nR hk c)).a + ((bEntB N K).count (nR hk c)).s
  let S7 := S6 + ((bEntF K c.w).count (nE (N := N) hk)).a + ((bEntF K c.w).count (nE (N := N) hk)).s
  S7 + (Bχ.count N).a + (Bχ.count N).s

/-- The time of the samplers of `Enc`. -/
def encST (Bχ : Bnd) (M : ℕ) : ℕ :=
  let S1 := M + (bCoins (N * K)).a + (bCoins (N * K)).s
  let S2 := S1 + (Bχ.count ((Enum.list (α := Fin c.d)).length * N)).a +
    (Bχ.count ((Enum.list (α := Fin c.d)).length * N)).s
  let S3 := S2 + (Bχ.count N).a + (Bχ.count N).s
  let S4 := S3 + (Bχ.count ((Enum.list (α := RingBTVW.Fresh.Col k)).length * N)).a +
    (Bχ.count ((Enum.list (α := RingBTVW.Fresh.Col k)).length * N)).s
  let S5 := S4 + (Bχ.count ((Enum.list (α := RingBTVW.Fresh.Col k)).length * N)).a +
    (Bχ.count ((Enum.list (α := RingBTVW.Fresh.Col k)).length * N)).s
  let S6 := S5 + ((bEntB N K).count (nR hk c)).a + ((bEntB N K).count (nR hk c)).s
  let S7 := S6 + ((bEntF K c.w).count (nE (N := N) hk)).a + ((bEntF K c.w).count (nE (N := N) hk)).s
  (bCoins (N * K)).T M M + ((Bχ.count ((Enum.list (α := Fin c.d)).length * N)).T S1 S1 +
    ((Bχ.count N).T S2 S2 + ((Bχ.count ((Enum.list (α := RingBTVW.Fresh.Col k)).length * N)).T S3 S3 +
    ((Bχ.count ((Enum.list (α := RingBTVW.Fresh.Col k)).length * N)).T S4 S4 +
    (((bEntB N K).count (nR hk c)).T S5 S5 + (((bEntF K c.w).count (nE (N := N) hk)).T S6 S6 +
    (Bχ.count N).T S7 S7))))))

/-- The time of the tail of `Enc` from tapes below `M`. -/
def encTT (M : ℕ) : ℕ :=
  natLT (tmplList hk c) M + (SigabaNeo.Tape.Prog.timeBound encCoreP M + appT M)

/-- **The uniform bound of `encP`.** -/
theorem ub_encP {X : ChiSampler c} (M : ℕ) (hpres : X.P.Preserves 6)
    (h0 : 2 * RingBTVW.pw.length + 1 ≤ M)
    (h1 : (Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K)) ≤ M)
    (h2 : (Enum.list (α := Fin 1)).length * ((Enum.list (α := TrapCol k)).length * (N * K)) ≤ M)
    (h3 : (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).length *
      ((Enum.list (α := Fin 1)).length * ((Enum.list (α := RingBTVW.Fresh.Col k)).length * (N * K))) ≤ M)
    (h4 : N * K ≤ M) (h5 : nA ≤ M)
    (s1 : (bCoins (N * K)).S₀ ≤ parseEG M)
    (s2 : (X.B.count ((Enum.list (α := Fin c.d)).length * N)).S₀ ≤ parseEG M)
    (s3 : (X.B.count N).S₀ ≤ parseEG M)
    (s4 : (X.B.count ((Enum.list (α := RingBTVW.Fresh.Col k)).length * N)).S₀ ≤ parseEG M)
    (s6 : ((bEntB N K).count (nR hk c)).S₀ ≤ parseEG M)
    (s7 : ((bEntF K c.w).count (nE (N := N) hk)).S₀ ≤ parseEG M)
    (ht : ∀ p ∈ tmplList hk c, p.2 ≤ encS hk c X.B (parseEG M)) :
    UB (encP hk c X) M (parseET hk c M + (encST hk c X.B (parseEG M) +
      encTT hk c (encS hk c X.B (parseEG M)))) (4 * encS hk c X.B (parseEG M) + 1) := by
  rw [encP]
  refine ((ub_encParseP hk c M h0 h1 h2 h3 h4 h5).seq <|
    (ub_of_atb e7 (atbb_coinsF _) s1).seq <|
    (ub_of_atb e8 (atbb_repF X.atb hpres _) (by omega)).seq <|
    (ub_of_atb e9 (atbb_repF X.atb hpres _) (by omega)).seq <|
    (ub_of_atb e9 (atbb_repF X.atb hpres _) (by omega)).seq <|
    (ub_of_atb e9 (atbb_repF X.atb hpres _) (by omega)).seq <|
    (ub_of_atb e10 (atbb_repF (atbb_entB N K) (preserves6_entB N K) _) (by omega)).seq <|
    (ub_of_atb e11 (atbb_repF (atbb_entF K c.w) (preserves6_entF K c.w) _) (by omega)).seq <|
    (ub_of_atb e12 (atbb_repF X.atb hpres _) (by omega)).seq <|
    (ub_natL _ _ ht (fun p hp => tmpl_lt hk c p hp 123 (by decide))).seq <|
    (ub_frame e120 encCoreP noGrow_encCoreP _).seq (ub_frameApP 122 0 123 121 _)).mono
    (le_of_eq ?_) (le_of_eq rfl)
  simp only [encST, encS, encTT, Nat.add_assoc]

end AdvancedEncryption.RingBTVW.Prog
