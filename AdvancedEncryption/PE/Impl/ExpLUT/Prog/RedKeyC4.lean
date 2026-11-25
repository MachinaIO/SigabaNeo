import PE.Impl.ExpLUT.Prog.RedKeyC4H
import PE.Impl.ExpLUT.Prog.RedKeyTIn
import PE.Impl.ExpLUT.Prog.KeyPrepareSize

/-!
# Cost certificate of `mid`, phase M4: `simKeyC ; midLd14 ; setXC ; simXC ; midFin`

`mid pk = m1P ; midEnter ; midLdM2 ; onM m2C ; midStA ; midEnter ; midLdPk ; onM pk ; m4P`
(**`mid_m4P`**, `rfl`), with the M4 tail

    m4P = onM (simKeyC Dc) ; midLd14 ; onM (setXC Dc) ; onM simXC ; midFin.

**`c4_cert_m4`**: for register bounds `x ≤ bx c4In` (the M4 input envelope, `RedKeyC4H`) and
storage bounds `g` with `C4Store g`,

    Cert m4P (embedF rkE g (layout (2^150) (2^24) (2^16) x)) (rkLiftB c4Out) (2 ^ 412),

and **`c4_tailIn : RkTailIn c4Out`** (every MVM tape `≤ 2^150`, templates exact, register `14`
`≤ 2^102`; tapes `105 … 246` end at `0`).

The MVM phases come from the verified analyzer (`RedKeyC4A.c4Ok_cert`) and the four kernel checks
of `RedKeyC4H`; `midLd14`/`midFin` are tape-level copies/clears (`XProg.VB.prim`).

### The input envelope M1–M3 must deliver (after `onM (pkOf pkt)`)

* registers: `x ≤ bx c4In`, i.e. `rAinS (0) ≤ 2^142`, `rCs (3) ≤ 2^73`, `seLoopC (28) ≤ 2^42`,
  `rKc (31) ≤ 16`, `rBit1 (21) ≤ 1`, the `SeConst`/`MulTmpl` templates at their exact sizes
  (see `RedKeyC4H`), every other register `≤ 2^141`; the tape cap `M = 2^150` on the scratch
  tapes `0 … 40` and exact templates `35 … 38` (the `layout`);
* storage (`C4Store g`): every tape `≤ 2^150`, `tMpk ≤ 2^102`, all tapes `≥ 105` other than
  `tAF tCt tMpk tSig tC` at `0`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyC4

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM
open AdvancedEncryption.ExpLUT.Prog AdvancedEncryption.ExpLUT.Prog.KeyTime
open AdvancedEncryption.ExpLUT.Prog.RedKeyMid AdvancedEncryption.ExpLUT.Prog.RedKeyM
open AdvancedEncryption.ExpLUT.Prog.RedKeyT
open AdvancedEncryption.ExpLUT.Params
open scoped SigabaNeo.Tape.Prog

/-! ### Constants -/

/-- The tape cap of M4. -/
abbrev c4M : ℕ := 2 ^ 150

theorem c4_mb : Dc.mb = 3 * 2 ^ 40 + 408 := by
  show mbar = _; rw [mbar_def, Kc_def]; norm_num

theorem c4_codec : codecSize (mpkEnc Dc) ≤ 2 ^ 98 := by
  obtain ⟨hp, -⟩ := keyCodec_lengths Dc
  exact hp.le.trans (by norm_num [Dc, Kc, mbar, AdvancedEncryption.PE.BranchingProgram.w8,
    AdvancedEncryption.PE.BranchingProgram.Width.len])

theorem c4_nBH : RedKeyMid.nB Dc ≤ 2 ^ 98 ∧ RedKeyMid.nH Dc ≤ 2 ^ 98 := by
  have h := publicFieldLengths_sum Dc
  have hc := c4_codec
  simp only [publicFieldLengths, List.sum_cons, List.sum_nil] at h
  unfold RedKeyMid.nB RedKeyMid.nH
  constructor <;> omega

/-! ### The codes as `AC` -/

theorem c4_er1 : AC.Er (.c seLoopKC) seLoopKC := .c _

theorem c4_er2 : AC.Er c4AcP (.seq (natC seMb rBit1 Dc.mb) sePostC) :=
  .s (.nat _ _ _ _ c4_mb.le) (.c _)

theorem c4_er3 : AC.Er c4AcX (setXC Dc) := by
  have h3 : 2 ^ Dc.b * Dc.mb ≤ 2 ^ 22 * (3 * 2 ^ 40 + 408) := by rw [hb_Dc, c4_mb]
  unfold setXC readFieldC c4AcX
  exact .s (.c _) (.s (.c _) (.s (.c _) (.s (.c _) (.s (.c _) (.s (.c _) (.s (.s (.c _)
    (.s (.nat _ _ _ _ c4_nBH.1) (.s (.c _) (.s (.nat _ _ _ _ c4_nBH.2) (.c _)))))
    (.nat _ _ _ _ h3)))))))

/-! ### The MVM phases -/

/-- The register envelope `layout (2^150) (2^24) (2^16)`. -/
abbrev c4L (x : Fin 64 → ℕ) : Fin 105 → ℕ := layout c4M (2 ^ 24) (2 ^ 16) x

theorem c4_cert_simKey (x : Fin 64 → ℕ) (hx : x ≤ bx c4In) :
    Cert (compile (simKeyC Dc)) (c4L x) (c4L (bx c4E2)) (2 ^ 411 + 2 ^ 298) := by
  have h1 := c4Ok_cert (by norm_num) (by norm_num) (by norm_num) (by norm_num) c4_er1 c4_ok1 x hx
  have h2 := c4Ok_cert (by norm_num) (by norm_num) (by norm_num) (by norm_num) c4_er2 c4_ok2
    (bx c4E1) le_rfl
  exact h1.seq h2

theorem c4_E3 : c4E3 = c4E2.set 14 (2 ^ 102) := by decide +kernel

theorem c4_cert_setX (x : Fin 64 → ℕ) (hx : x ≤ bx c4E3) :
    Cert (compile (setXC Dc)) (c4L x) (c4L (bx c4E4)) (2 ^ 256) :=
  c4Ok_cert (by norm_num) (by norm_num) (by norm_num) (by norm_num) c4_er3 c4_ok3 x hx

theorem c4_cert_simX :
    Cert (compile simXC) (c4L (bx c4E4)) (c4L (bx c4E5)) (2 ^ 407) :=
  c4Ok_cert (by norm_num) (by norm_num) (by norm_num) (by norm_num) (.c _) c4_ok4 _ le_rfl

/-! ### The `247`-tape envelopes -/

/-- Registers `x` on the MVM tapes, storage `g` on the others. -/
def c4Env (x : Fin 64 → ℕ) (g : Fin 247 → ℕ) : Fin 247 → ℕ := embedF rkE g (c4L x)

theorem c4Env_rkE (x : Fin 64 → ℕ) (g : Fin 247 → ℕ) (j : Fin 105) : c4Env x g (rkE j) = c4L x j := by
  simp [c4Env]

theorem c4Env_hi (x : Fin 64 → ℕ) (g : Fin 247 → ℕ) (t : Fin 247) (ht : 105 ≤ t.val) :
    c4Env x g t = g t := by
  rcases embedF_cases rkE g (c4L x) t with ⟨-, h⟩ | ⟨j, hj, -⟩
  · exact h
  · have := j.isLt; rw [← hj, rkE_val] at ht; omega

theorem c4_embed_embed (a : Fin 247 → ℕ) (b c : Fin 105 → ℕ) :
    embedF rkE (embedF rkE a b) c = embedF rkE a c := by
  funext t
  rcases embedF_cases rkE (embedF rkE a b) c t with ⟨h1, h2⟩ | ⟨j, rfl, h2⟩
  · rw [h2]
    rcases embedF_cases rkE a b t with ⟨-, h3⟩ | ⟨j, rfl, -⟩
    · rw [h3]
      rcases embedF_cases rkE a c t with ⟨-, h4⟩ | ⟨j, rfl, -⟩
      · rw [h4]
      · rw [partialInv_self] at h1; cases h1
    · rw [partialInv_self] at h1; cases h1
  · rw [h2, embedF_apply_self]

theorem c4Env_le (x : Fin 64 → ℕ) (g : Fin 247 → ℕ) (hx : ∀ r, x r ≤ c4M) (hg : ∀ t, g t ≤ c4M) :
    ∀ t, c4Env x g t ≤ c4M := by
  intro t
  rcases embedF_cases rkE g (c4L x) t with ⟨-, h⟩ | ⟨j, -, h⟩
  · rw [c4Env, h]; exact hg t
  · rw [c4Env, h]; exact layout_top _ _ _ x hx (by norm_num) (by norm_num) (by norm_num) j

/-- An MVM phase, framed. -/
theorem c4_onM {c : Code} {x y : Fin 64 → ℕ} {T : ℕ} (g : Fin 247 → ℕ)
    (h : Cert (compile c) (c4L x) (c4L y) T) : Cert (onM c) (c4Env x g) (c4Env y g) T := by
  have he : (c4Env x g) ∘ rkE = c4L x := by funext j; exact c4Env_rkE x g j
  have := Cert.frame rkE (a := c4Env x g) (by rw [he]; exact h)
  rwa [c4Env, c4_embed_embed] at this

/-- A tape primitive. -/
theorem c4_prim (p : Prim 247) (a : Fin 247 → ℕ) (h : ∀ i, a i ≤ c4M) :
    Cert (.prog (.prim p)) a (p.lenT a) (2 * (c4M + 1) + 3) :=
  Cert.ofVB (XProg.VB.prim p h)

/-- A sequence of tape programs. -/
theorem c4_pseq {p q : Tape.Prog 247} {a b c : Fin 247 → ℕ} {T U : ℕ}
    (hp : Cert (.prog p) a b T) (hq : Cert (.prog q) b c U) : Cert (.prog (p ⨾ q)) a c (T + U) :=
  have h := hp.seq hq
  ⟨h.len, h.time⟩

theorem c4_upd_le {a : Fin 247 → ℕ} (h : ∀ i, a i ≤ c4M) (t : Fin 247) {v : ℕ} (hv : v ≤ c4M) :
    ∀ i, Function.update a t v i ≤ c4M := by
  intro i; by_cases hi : i = t
  · subst hi; simpa using hv
  · rw [Function.update_of_ne hi]; exact h i

/-! ### The storage -/

/-- **The storage envelope at the start of M4.** -/
structure C4Store (g : Fin 247 → ℕ) : Prop where
  top : ∀ t, g t ≤ 2 ^ 150
  mpk : g tMpk ≤ 2 ^ 102
  zero : ∀ t : Fin 247, 105 ≤ t.val → t ≠ tAF → t ≠ tCt → t ≠ tMpk → t ≠ tSig → t ≠ tC → g t = 0

/-- `midLd14`. -/
theorem c4_cert_ld14 (x : Fin 64 → ℕ) (g : Fin 247 → ℕ) (hx : ∀ r, x r ≤ c4M)
    (hg : ∀ t, g t ≤ c4M) :
    Cert (.prog midLd14) (c4Env x g) (c4Env (Function.update x 14 (g tMpk)) g)
      (2 * (c4M + 1) + 3) := by
  have h := c4_prim (.copy (tRg 14) tMpk) _ (c4Env_le x g hx hg)
  have e : (Prim.copy (tRg 14) tMpk).lenT (c4Env x g) = c4Env (Function.update x 14 (g tMpk)) g := by
    simp only [Prim.lenT]
    rw [c4Env_hi x g tMpk (by decide), c4Env, c4Env, c4L, c4L, layout_update, embed_update]
    rfl
  rw [e] at h
  exact h

/-! ### The output envelope -/

/-- The register bounds at the end of `mid`: `c4E5`, register `8 := tAF` (`≤ 2^150`),
`14 := tMpk` (`≤ 2^102`). -/
def c4OutB : Fin 64 → ℕ := Function.update (Function.update (bx c4E5) 8 (2 ^ 150)) 14 (2 ^ 102)

/-- **The output envelope of `mid`** on the MVM tapes. -/
def c4Out : Fin 105 → ℕ := c4L c4OutB

theorem c4_tailIn : RkTailIn c4Out := by
  have hN : Dc.N = 2 ^ 24 := rfl
  have hK : Dc.K = 2 ^ 16 := by show Kc = _; rw [Kc_def]
  have h5 := topL_sound c4_top.2.2.2.2
  refine ⟨fun t => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine layout_top _ _ _ _ (fun r => ?_) (by norm_num) (by norm_num) (by norm_num) t
    simp only [c4OutB, Function.update_apply]
    split_ifs
    · norm_num
    · norm_num
    · exact h5 r
  · simp [c4Out, c4L, layout, hK]
  · simp [c4Out, c4L, layout, hN]
  · simp [c4Out, c4L, layout, hN, hK]
  · simp [c4Out, c4L, layout, hN, hK]
  · simp [c4Out, c4L, c4OutB]

/-- `midFin` (`8 := tAF`, `14 := tMpk`, storage cleared). -/
theorem c4_cert_fin (x : Fin 64 → ℕ) (hx : x ≤ bx c4E5) (g : Fin 247 → ℕ) (hg : C4Store g) :
    Cert (.prog midFin) (c4Env x g) (rkLiftB c4Out) (7 * (2 * (c4M + 1) + 3)) := by
  have hx' : ∀ r, x r ≤ c4M := fun r => (hx r).trans (topL_sound c4_top.2.2.2.2 r)
  have h0 := c4Env_le x g hx' hg.top
  have p1 := c4_prim (.copy (tRg 8) tAF) _ h0
  have q1 := c4_upd_le h0 (tRg 8) (h0 tAF)
  set a1 := (Prim.copy (tRg 8) tAF).lenT (c4Env x g)
  have p2 := c4_prim (.copy (tRg 14) tMpk) a1 q1
  have q2 := c4_upd_le q1 (tRg 14) (q1 tMpk)
  set a2 := (Prim.copy (tRg 14) tMpk).lenT a1
  have p3 := c4_prim (.clear tAF) a2 q2
  have q3 := c4_upd_le q2 tAF (Nat.zero_le _)
  set a3 := (Prim.clear tAF).lenT a2
  have p4 := c4_prim (.clear tCt) a3 q3
  have q4 := c4_upd_le q3 tCt (Nat.zero_le _)
  set a4 := (Prim.clear tCt).lenT a3
  have p5 := c4_prim (.clear tMpk) a4 q4
  have q5 := c4_upd_le q4 tMpk (Nat.zero_le _)
  set a5 := (Prim.clear tMpk).lenT a4
  have p6 := c4_prim (.clear tSig) a5 q5
  have q6 := c4_upd_le q5 tSig (Nat.zero_le _)
  set a6 := (Prim.clear tSig).lenT a5
  have p7 := c4_prim (.clear tC) a6 q6
  have hc := c4_pseq p1 (c4_pseq p2 (c4_pseq p3 (c4_pseq p4 (c4_pseq p5 (c4_pseq p6 p7)))))
  refine hc.mono le_rfl ?_ (by omega)
  -- the final bound
  have hxo : x ≤ c4OutB := by
    have h14 : c4E5.getD 14 0 ≤ 2 ^ 102 := by decide +kernel
    intro r
    simp only [c4OutB, Function.update_apply]
    split_ifs with h1 h2
    · subst h1; exact (hx _).trans h14
    · exact hx' r
    · exact hx r
  have hlo : ∀ j : Fin 105, c4Env x g (rkE j) ≤ rkLiftB c4Out (rkE j) := by
    intro j
    rw [c4Env_rkE, rkLiftB, embedF_apply_self, c4Out]
    exact layout_mono _ _ _ hxo j
  have hAF : c4Env x g tAF = g tAF := c4Env_hi x g tAF (by decide)
  have hMpk : c4Env x g tMpk = g tMpk := c4Env_hi x g tMpk (by decide)
  have hM8 : tMpk ≠ tRg 8 := by decide
  intro t
  simp only [a6, a5, a4, a3, a2, a1, Prim.lenT, Function.update_apply, hM8, ite_false]
  split_ifs with e1 e2 e3 e4 e5 e6 e7
  all_goals try exact Nat.zero_le _
  · subst e6
    rw [hMpk, tRg, rkLiftB, embedF_apply_self, c4Out, c4OutB, c4L, layout_update]
    simpa using hg.mpk
  · subst e7
    rw [hAF, tRg, rkLiftB, embedF_apply_self, c4Out, c4OutB, c4L, layout_update, layout_update,
      Function.update_of_ne (by decide), Function.update_self]
    exact hg.top _
  · by_cases ht : t.val < 105
    · obtain ⟨j, rfl⟩ : ∃ j : Fin 105, rkE j = t := ⟨⟨t.val, ht⟩, Fin.ext rfl⟩
      exact hlo j
    · have ht' : 105 ≤ t.val := by omega
      rw [c4Env_hi x g t ht', hg.zero t ht' e5 e4 e3 e2 e1]
      exact Nat.zero_le _

/-! ### Phase M4 -/

/-- **The M4 tail of `mid`.** -/
noncomputable def m4P : XProg 247 :=
  .seq (onM (simKeyC Dc)) <| .seq (.prog midLd14) <| .seq (onM (setXC Dc)) <|
  .seq (onM simXC) <| .prog midFin

theorem mid_m4P (pk : Code) :
    mid pk = .seq m1P (.seq midEnter (.seq (.prog midLdM2) (.seq (onM m2C) (.seq (.prog midStA)
      (.seq midEnter (.seq (.prog midLdPk) (.seq (onM pk) m4P))))))) := rfl

set_option exponentiation.threshold 2000 in
/-- **The cost certificate of phase M4.** -/
theorem c4_cert_m4 (x : Fin 64 → ℕ) (hx : x ≤ bx c4In) (g : Fin 247 → ℕ) (hg : C4Store g) :
    Cert m4P (c4Env x g) (rkLiftB c4Out) (2 ^ 412) := by
  have hg' : ∀ t, g t ≤ c4M := hg.top
  have hE2 : ∀ r, bx c4E2 r ≤ c4M := topL_sound c4_top.2.1
  have p1 := c4_onM g (c4_cert_simKey x hx)
  have p2 := c4_cert_ld14 (bx c4E2) g hE2 hg'
  have hx3 : Function.update (bx c4E2) 14 (g tMpk) ≤ bx c4E3 := by
    rw [c4_E3, show (14 : ℕ) = (14 : Fin 64).val from rfl, bx_set _ (by decide +kernel)]
    intro r; by_cases hr : r = 14
    · subst hr; simpa using hg.mpk
    · simp [Function.update_of_ne hr]
  have p3 := c4_onM g (c4_cert_setX _ hx3)
  have p4 := c4_onM g c4_cert_simX
  have p5 := c4_cert_fin (bx c4E5) le_rfl g hg
  exact (p1.seq (p2.seq (p3.seq (p4.seq p5)))).mono le_rfl le_rfl (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.RedKeyC4
