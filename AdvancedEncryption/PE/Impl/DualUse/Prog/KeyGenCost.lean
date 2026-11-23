import PE.Impl.DualUse.Prog.KeyGenP
import PE.Impl.DualUse.Prog.CostTools
import PE.Impl.DualUse.Prog.KeyPTimeT

/-!
# The time of the compiled `KeyGen`

`ph_keyGenP`: from the input bound of the machine (`nKG + 1` bits on tape `255`), with the key-row
block bounded by a phase (`Tb` steps, every tape below `Gb`) on stores whose tape `0` is below
`8 (nKG + 2)` and tape `1` below the front end's output bound, the program `keyGenP` takes at most
`keyGT …` steps and leaves at most `keyGL …` bits on tape `0`, the other tapes blank.

The guard and the parser are bounded uniformly on the tapes they write, the other tapes keep their
bound `0` (`ph_of_ub_ws`), so the front end gets blank scratch (`timeBoundT_frontP`); after the
block every tape is bounded uniformly.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg
open SigabaNeo.Tape.Prog (leP unfrP frP leT unfrT frT tailsP ubp_tailsP ubp_prim0)
open AdvancedEncryption.PE.Gates.DateWindow
open SigabaNeo.Lattices.Algo
open scoped SigabaNeo.Tape.Prog

/-! ### Relabelled programs keep the other tapes -/

theorem writes_map {n m : ℕ} (u : Fin n → Fin m) (q : Prim n) :
    (q.map u).writes = q.writes.map u := by cases q <;> rfl

theorem preserves_map {n m : ℕ} (u : Fin n → Fin m) (t : Fin m) :
    ∀ p : Prog n, (∀ j, u j = t → p.Preserves j) → (Prog.map u p).Preserves t
  | .prim q, h => by
    show t ∉ (q.map u).writes
    rw [writes_map]
    intro ht
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
    exact h j rfl hj
  | .coin i, h => by
    show u i ≠ t
    intro e
    exact (h i e) rfl
  | .seq p q, h => ⟨preserves_map u t p (fun j hj => (h j hj).1),
      preserves_map u t q (fun j hj => (h j hj).2)⟩
  | .ifBlank _ p q, h => ⟨preserves_map u t p (fun j hj => (h j hj).1),
      preserves_map u t q (fun j hj => (h j hj).2)⟩
  | .ifBit _ p q, h => ⟨preserves_map u t p (fun j hj => (h j hj).1),
      preserves_map u t q (fun j hj => (h j hj).2)⟩
  | .loop i b, h => by
    refine ⟨fun e => ?_, preserves_map u t b (fun j hj => (h j hj).2)⟩
    exact (h i e).1 rfl

/-! ### The guard and the parser -/

theorem ph_guard (n M : ℕ) {β : Fin 256 → ℕ} (hβ : ∀ i, β i ≤ M) :
    Ph (prog (Prog.map uL (leP n))) β (leT n M) (fun i => if i ∈ [254, 253] then M + 1 else β i) := by
  refine ph_of_ub_ws _ (fun i hi => ?_) (fun ℓ hℓ => ubp_leP_map uL n M ℓ hℓ) hβ
  refine preserves_map uL i _ (fun j hj => ?_)
  fin_cases j
  · refine ⟨by simp [Prog.Preserves, Prim.writes], by simp [Prog.Preserves, Prim.writes],
      preserves_tailsP (by decide) n, ⟨by simp [Prog.Preserves, Prim.writes],
        by simp [Prog.Preserves, Prim.writes]⟩, by simp [Prog.Preserves, Prim.writes]⟩
  · exact absurd hj (fun e => hi (by simp [← e, uL]))
  · exact absurd hj (fun e => hi (by simp [← e, uL]))

/-- The time of the parser from tapes below `M`. -/
def parseT (M : ℕ) : ℕ :=
  (2 * (M + 1) + 3) + (unfrT M + (unfrT (2 * M) + (unfrT (2 * (2 * M)) +
    ((2 * (2 * (2 * (2 * M)) + 1) + 3) + (2 * (2 * (2 * (2 * M)) + 1) + 3)))))

theorem ph_parse (M : ℕ) {β : Fin 256 → ℕ} (hβ : ∀ i, β i ≤ M) :
    Ph (prog parseP) β (parseT M)
      (fun i => if i ∈ [254, 253, 0, 1, 251, 252, 255] then 2 * (2 * (2 * M)) else β i) := by
  refine ph_of_ub_ws _ (fun i hi => ?_) (fun ℓ hℓ => ?_) hβ
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hi
    have hu : ∀ d : Fin 256, (d = 253 ∨ d = 0 ∨ d = 1) → (Prog.map (uU d) unfrP).Preserves i :=
      fun d hd => preserves_map _ i _ (fun j hj => by
        exfalso; fin_cases j <;> simp [uU] at hj <;> rcases hd with rfl | rfl | rfl <;> simp_all)
    exact ⟨by simp [Prog.Preserves, Prim.writes, n1], hu 253 (Or.inl rfl), hu 0 (by simp),
      hu 1 (by simp), by simp [Prog.Preserves, Prim.writes, n2],
      by simp [Prog.Preserves, Prim.writes, n7]⟩
  · exact ((ubp_prim0 (.clear 254) rfl M).seq ((ubp_unfrP_map _ M).seq ((ubp_unfrP_map _ _).seq
      ((ubp_unfrP_map _ _).seq ((ubp_prim0 (.clear 253) rfl _).seq (ubp_prim0 (.clear 255) rfl _))))))
      ℓ hℓ

/-! ### The front end -/

theorem ph_front (n W T : ℕ) {β : Fin 256 → ℕ} (hβ : (fun j => β (eFr j)) ≤ io2 (R := 6) T 0 0) :
    Ph (frame eFr (frontP n W)) β (frontT n W T) (embedF eFr β (io2 (R := 6) (frontL n W) 0 0)) :=
  ph_frame eFr (fun ℓ hℓ => ⟨(timeBoundT_mono _ (hℓ.trans hβ)).trans (timeBoundT_frontP n W T),
    (lenBoundT_mono _ (hℓ.trans hβ)).trans (lenBoundT_frontP n W T)⟩)

/-! ### The tail of the window branch -/

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

/-- The time of the real key try (`timeBound_keyTryRCoinsP`). -/
def keyTryRT (M : ℕ) : ℕ :=
  23 * (M + 1) ^ 2 + SigabaNeo.Tape.Prog.tbC (ProgKeyR.keyTryRP ⨾ SigabaNeo.Tape.Prog.clr 3) *
    (2 * M + 1) ^ SigabaNeo.Tape.Prog.tbD (ProgKeyR.keyTryRP ⨾ SigabaNeo.Tape.Prog.clr 3)

theorem ub_keyTryR (M : ℕ) : UB (frame eKR (prog ProgKeyR.keyTryRCoinsP)) M (keyTryRT M) (2 * M) :=
  (ub_frameP eKR _ M).mono (ProgKeyR.timeBound_keyTryRCoinsP M)
    (max_le (by omega) (ProgKeyR.lenBound_keyTryRCoinsP_le M))

/-- The time of `etP` from tapes below `M`. -/
def etT (X Y P M : ℕ) : ℕ :=
  ((2 * (M + 1) + 3) + ((X + 1) * (2 * (M + 1) + 3) + ((2 * (M + 1) + 3) +
    (Y + 1) * (2 * (M + 1) + 3)))) + (prefT P M + (2 * (M + 1 + P + 1) + 3))

variable (hk c) in
theorem ub_etP (M : ℕ) : UB (etP hk c) M (etT (lenPK hk c + 2 * k * (N * K)) (lenPK hk c)
    (2 * k * (N * K)) M) (M + 1 + 2 * k * (N * K)) := by
  have h1 : UB (prog (SigabaNeo.Tape.Prog.cp 91 0 ⨾ tailsP 91 (lenPK hk c + 2 * k * (N * K)) ⨾
      SigabaNeo.Tape.Prog.cp 102 0 ⨾ tailsP (102 : Fin 256) (lenPK hk c))) M
      ((2 * (M + 1) + 3) + ((lenPK hk c + 2 * k * (N * K) + 1) * (2 * (M + 1) + 3) +
        ((2 * (M + 1) + 3) + (lenPK hk c + 1) * (2 * (M + 1) + 3)))) M := fun ℓ hℓ =>
    ((ubp_prim0 (.copy 91 0) rfl M).seq ((ubp_tailsP 91 _ M).seq ((ubp_prim0 (.copy 102 0) rfl M).seq
      (ubp_tailsP 102 _ M)))) ℓ hℓ
  exact h1.seq ((ub_prefP _ 102 90 103 104 M).seq (ub_clear 102 _))

variable (hk c) in
/-- The bound after the window branch's tail from tapes below `M`. -/
def winG (cf : KeyCfg) (M : ℕ) : ℕ :=
  3 * (2 * (M + 1 + lenPK hk c + 1 + 2 * k * (N * K) + cf.sW.length + 1 +
    (powW K (cf.B - 1)).length + 1)) + 1

variable (hk c) in
/-- The time of the window branch's tail from tapes below `M`. -/
def winT2 (cf : KeyCfg) (M : ℕ) : ℕ :=
  let M1 := M + 1 + lenPK hk c
  let M2 := M1 + 1 + 2 * k * (N * K)
  let M3 := M2 + cf.sW.length + 1
  let M4 := M3 + (powW K (cf.B - 1)).length + 1
  prefT (lenPK hk c) M + etT (lenPK hk c + 2 * k * (N * K)) (lenPK hk c) (2 * k * (N * K)) M1 +
    putT cf.sW.length M2 + putT (powW K (cf.B - 1)).length M3 + tmplT (keyTmplR hk c cf) M4 +
    keyTryRT M4 + frT (2 * M4) + (keyClrR.length * (2 * (3 * (2 * M4) + 1 + 1) + 3) +
      (2 * (3 * (2 * M4) + 1 + 1) + 3))

variable (hk c) in
theorem ub_winTail (cf : KeyCfg) {M : ℕ} (hM : tmplMax (keyTmplR hk c cf) ≤ M) :
    UB (XProg.seq (prefP (lenPK hk c) 0 1 100 101) <| XProg.seq (etP hk c) <|
      XProg.seq (putW 4 cf.sW) <| XProg.seq (putW 5 (powW K (cf.B - 1))) <|
      XProg.seq (tmplP 120 (keyTmplR hk c cf)) <|
      XProg.seq (XProg.frame eKR (XProg.prog ProgKeyR.keyTryRCoinsP)) <|
      XProg.seq (XProg.prog (Prog.map uF frP)) (clearL keyClrR)) M (winT2 hk c cf M) (winG hk c cf M) := by
  have hT : ∀ x ∈ keyTmplR hk c cf, x.2 ≤ M + 1 + lenPK hk c + 1 + 2 * k * (N * K) +
      cf.sW.length + 1 + (powW K (cf.B - 1)).length + 1 := fun x hx =>
    (le_tmplMax _ x hx).trans (hM.trans (by omega))
  have hk1 : ∀ x ∈ keyTmplR hk c cf, x.1 ≠ (120 : Fin 256) := fun x hx e => by
    have := List.mem_map_of_mem (f := fun x : Fin 256 × ℕ => x.1.val) hx
    rw [keyTmplR_keys, e] at this; simp at this
  refine ((ub_prefP _ 0 1 100 101 M).seq <| (ub_etP hk c _).seq <| (ub_putW 4 cf.sW _).seq <|
    (ub_putW 5 (powW K (cf.B - 1)) _).seq <| (ub_tmplP 120 _ _ hT hk1).seq <|
    (ub_keyTryR _).seq <| (show UB (prog (Prog.map uF frP)) _ _ _ from
      fun ℓ hℓ => ubp_frP_map uF _ ℓ hℓ).seq (ub_clearL _ keyClrR)).mono
    (le_of_eq ?_) (le_of_eq ?_)
  · simp only [winT2]; ring
  · simp only [winG]

/-! ### The program -/

variable (hk c) in
/-- The time of the branches of `KeyGen` from the front end's bounds. -/
def keyBT (W : ℕ) (cf : KeyCfg) (Tb Gb : ℕ) : ℕ :=
  let Mβ := max (8 * (nKG hk c + 2)) (frontL c.L W)
  max ((2 * (Mβ + 1) + 3) + (Tb + winT2 hk c cf Gb))
    (max (longT Mβ) (dumT hk c Mβ + frT (dumD hk c Mβ + 1)) + 1) + 1

variable (hk c) in
/-- The bound of tape `0` after the branches of `KeyGen`. -/
def keyBL (W : ℕ) (cf : KeyCfg) (Gb : ℕ) : ℕ :=
  let Mβ := max (8 * (nKG hk c + 2)) (frontL c.L W)
  max (winG hk c cf Gb) (max Mβ (3 * (dumD hk c Mβ + 1) + 1))

variable (hk c) in
/-- **The time of `KeyGen`'s program** from its input bound. -/
def keyGT (W : ℕ) (cf : KeyCfg) (Tb Gb : ℕ) : ℕ :=
  leT (nKG hk c) (nKG hk c + 1) + (max (2 * (nKG hk c + 2 + 1) + 3)
    (parseT (nKG hk c + 2) + (frontT c.L W (8 * (nKG hk c + 2)) + (keyBT hk c W cf Tb Gb +
      (256 * (2 * (keyBL hk c W cf Gb + 1) + 3) + (2 * (keyBL hk c W cf Gb + 1) + 3))))) + 1)

variable (hk c) in
/-- The time of the branches of `KeyGen` from the front end's bounds. -/
def keyBTF (LF : ℕ) (cf : KeyCfg) (Tb Gb : ℕ) : ℕ :=
  let Mβ := max (8 * (nKG hk c + 2)) LF
  max ((2 * (Mβ + 1) + 3) + (Tb + winT2 hk c cf Gb))
    (max (longT Mβ) (dumT hk c Mβ + frT (dumD hk c Mβ + 1)) + 1) + 1

variable (hk c) in
/-- The bound of tape `0` after the branches of `KeyGen`. -/
def keyBLF (LF : ℕ) (cf : KeyCfg) (Gb : ℕ) : ℕ :=
  let Mβ := max (8 * (nKG hk c + 2)) LF
  max (winG hk c cf Gb) (max Mβ (3 * (dumD hk c Mβ + 1) + 1))

variable (hk c) in
/-- **The time of `KeyGen`'s program** from its input bound. -/
def keyGTF (FT LF : ℕ) (cf : KeyCfg) (Tb Gb : ℕ) : ℕ :=
  leT (nKG hk c) (nKG hk c + 1) + (max (2 * (nKG hk c + 2 + 1) + 3)
    (parseT (nKG hk c + 2) + (FT + (keyBTF hk c LF cf Tb Gb +
      (256 * (2 * (keyBLF hk c LF cf Gb + 1) + 3) + (2 * (keyBLF hk c LF cf Gb + 1) + 3))))) + 1)

/-- **The time and the output bound of `KeyGen`'s program.** -/
theorem ph_keyGenF {R : ℕ} {e : Fin (R + 2) ↪ Fin 256} (he : FrEmb e) (hR : R ≤ 166)
    {fr : XProg (R + 2)} {FT FL : ℕ → ℕ}
    (hfr : ∀ T, Ph fr (io2 (R := R) T 0 0) (FT T) (io2 (R := R) (FL T) 0 0))
    (bfX : XProg 256) (W : ℕ) (cf : KeyCfg) {Tb Gb : ℕ}
    (hbf : ∀ β : Fin 256 → ℕ, β 0 ≤ 8 * (nKG hk c + 2) → β 1 ≤ FL (8 * (nKG hk c + 2)) →
      (∀ i, β i ≤ max (8 * (nKG hk c + 2)) (FL (8 * (nKG hk c + 2)))) → Ph bfX β Tb (fun _ => Gb))
    (hT : tmplMax (keyTmplR hk c cf) ≤ Gb) :
    timeBoundT (keyGenF hk c e fr bfX W cf) (Prog.inputBound (255 : Fin 256) (nKG hk c + 1)) ≤
        keyGTF hk c (FT (8 * (nKG hk c + 2))) (FL (8 * (nKG hk c + 2))) cf Tb Gb ∧
      lenBoundT (keyGenF hk c e fr bfX W cf) (Prog.inputBound (255 : Fin 256) (nKG hk c + 1)) 0 ≤
        keyBLF hk c (FL (8 * (nKG hk c + 2))) cf Gb := by
  set n := nKG hk c with hn
  set a := 8 * (n + 2) with ha
  set FL := FL a with hFL
  set Mβ := max a FL with hMβ
  have h0 : ∀ i, Prog.inputBound (255 : Fin 256) (n + 1) i ≤ n + 1 := fun i => by
    simp only [Prog.inputBound, Function.update_apply]; split_ifs <;> omega
  have p1 := ph_guard n (n + 1) h0
  set β1 := fun i => if i ∈ [(254 : Fin 256), 253] then n + 1 + 1 else Prog.inputBound (255 : Fin 256) (n + 1) i
    with hβ1
  have hβ1M : ∀ i, β1 i ≤ n + 2 := fun i => by
    simp only [hβ1]; split_ifs
    · omega
    · have := h0 i; omega
  -- the short branch
  have pA := (ph_prim (Prim.clear (255 : Fin 256)) β1).mono le_rfl
    (show 2 * (supB β1 + 1) + 3 ≤ 2 * (n + 2 + 1) + 3 by have := supB_le_of hβ1M; omega) le_rfl
  -- parsing
  have p3 := ph_parse (n + 2) hβ1M
  set β3 := fun i => if i ∈ [(254 : Fin 256), 253, 0, 1, 251, 252, 255] then 2 * (2 * (2 * (n + 2)))
    else β1 i with hβ3
  have hβ3e : ∀ j, (fun j => β3 (e j)) j ≤ io2 (R := R) a 0 0 j := by
    intro j
    simp only [hβ3, hβ1, Prog.inputBound, Function.update_apply, io2]
    by_cases hj : j.val = 0
    · have : e j = 1 := Fin.ext (by rw [he]; simp [hj])
      simp [this, hj, ha]; omega
    · have hv : (e j).val = j.val + 82 := by rw [he]; simp [hj]
      have hne : ∀ t : Fin 256, t.val ≤ 82 ∨ t.val ≥ 250 → e j ≠ t := fun t ht e' => by
        rw [← e', hv] at ht; have := j.isLt; omega
      have h1 : e j ≠ 254 := hne 254 (by simp)
      have h2 : e j ≠ 253 := hne 253 (by simp)
      have h3 : e j ≠ 0 := hne 0 (by simp)
      have h4 : e j ≠ 1 := hne 1 (by simp)
      have h5 : e j ≠ 251 := hne 251 (by simp)
      have h6 : e j ≠ 252 := hne 252 (by simp)
      have h7 : e j ≠ 255 := hne 255 (by simp)
      simp [h1, h2, h3, h4, h5, h6, h7, hj]
  have p4 := ph_frame e (p := fr) (β := β3) (hfr a |>.mono (fun j => hβ3e j) le_rfl le_rfl)
  set β4 := embedF e β3 (io2 (R := R) FL 0 0) with hβ4
  have hb40 : β4 0 = a := by
    rw [hβ4]
    rcases embedF_cases e β3 (io2 (R := R) FL 0 0) 0 with ⟨-, h⟩ | ⟨j, hj, -⟩
    · rw [h]; simp [hβ3]; omega
    · exact absurd hj (he.ne_zero j)
  have hb41 : β4 1 ≤ FL := by
    rw [hβ4, ← he.zero, embedF_apply_self]
    simp [io2]
  have hb4M : ∀ i, β4 i ≤ Mβ := by
    intro i
    rw [hβ4]
    rcases embedF_cases e β3 (io2 (R := R) FL 0 0) i with ⟨-, h⟩ | ⟨j, -, h⟩
    · rw [h]; simp only [hβ3, hβ1, Prog.inputBound, Function.update_apply]
      split_ifs <;> omega
    · rw [h]; simp only [io2]; split_ifs <;> omega
  -- the branches
  have pwin := ((ph_prim (Prim.tail (1 : Fin 256)) β4).seq ((hbf _ (by simp [Prim.lenT, hb40])
    (by simp only [Prim.lenT, Function.update_apply]; split_ifs <;> omega)
    (fun i => by simp only [Prim.lenT, Function.update_apply]; split_ifs <;> have := hb4M i <;> omega)).seq
    (ph_of_ub (β := fun _ => Gb) (fun _ => le_rfl) (ub_winTail hk c cf hT)))).mono le_rfl
    (show _ ≤ (2 * (Mβ + 1) + 3) + (Tb + winT2 hk c cf Gb) by
      have := supB_le_of hb4M; omega) le_rfl
  have plong := ph_of_ub hb4M (ub_longB Mβ)
  have pdum := ph_of_ub hb4M ((ub_dumB hk c Mβ).seq (show UB (prog (Prog.map uF frP)) _ _ _ from
    fun ℓ hℓ => ubp_frP_map uF _ ℓ hℓ))
  have p5 := ph_ifBit' (1 : Fin 256) pwin (ph_ifBlank' (1 : Fin 256) plong pdum)
  have p5' := p5.mono le_rfl (le_of_eq rfl) (show _ ≤ fun _ => keyBLF hk c FL cf Gb from
    fun t => le_of_eq rfl)
  have p6 := ph_clearL clrAll (fun _ => keyBLF hk c FL cf Gb)
  have pB := p3.seq (p4.seq (p5'.seq p6))
  have pall := p1.seq (ph_ifBlank' (254 : Fin 256) pA pB)
  have h := pall (Prog.inputBound (255 : Fin 256) (n + 1)) le_rfl
  refine ⟨h.1.trans ?_, (h.2 0).trans ?_⟩
  · have hs := supB_const_le (k := 256) (keyBLF hk c FL cf Gb)
    have hl := length_clrAll_le
    have := Nat.mul_le_mul_right (2 * (supB (fun _ : Fin 256 => keyBLF hk c FL cf Gb) + 1) + 3) hl
    have e : clrAll.length * (2 * (supB (fun _ : Fin 256 => keyBLF hk c FL cf Gb) + 1) + 3) +
        (2 * (supB (fun _ : Fin 256 => keyBLF hk c FL cf Gb) + 1) + 3) ≤
        256 * (2 * (keyBLF hk c FL cf Gb + 1) + 3) + (2 * (keyBLF hk c FL cf Gb + 1) + 3) := by
      have h2 : 2 * (supB (fun _ : Fin 256 => keyBLF hk c FL cf Gb) + 1) + 3 ≤
          2 * (keyBLF hk c FL cf Gb + 1) + 3 := by omega
      exact Nat.add_le_add (Nat.mul_le_mul hl h2) h2
    show _ ≤ leT n (n + 1) + (max (2 * (n + 2 + 1) + 3) (parseT (n + 2) + (FT a +
      (keyBTF hk c FL cf Tb Gb + (256 * (2 * (keyBLF hk c FL cf Gb + 1) + 3) +
        (2 * (keyBLF hk c FL cf Gb + 1) + 3))))) + 1)
    gcongr
    exact Nat.le_of_eq rfl
  · simp [mem_clrAll, Prim.lenT, hβ1, Prog.inputBound]

/-- **The time and the output bound of `KeyGen`'s program** (date-window front end). -/
theorem ph_keyGenP (bfX : XProg 256) (W : ℕ) (cf : KeyCfg) {Tb Gb : ℕ}
    (hbf : ∀ β : Fin 256 → ℕ, β 0 ≤ 8 * (nKG hk c + 2) → β 1 ≤ frontL c.L W →
      (∀ i, β i ≤ max (8 * (nKG hk c + 2)) (frontL c.L W)) → Ph bfX β Tb (fun _ => Gb))
    (hT : tmplMax (keyTmplR hk c cf) ≤ Gb) :
    timeBoundT (keyGenP hk c bfX W cf) (Prog.inputBound (255 : Fin 256) (nKG hk c + 1)) ≤ keyGT hk c W cf Tb Gb ∧
      lenBoundT (keyGenP hk c bfX W cf) (Prog.inputBound (255 : Fin 256) (nKG hk c + 1)) 0 ≤ keyBL hk c W cf Gb :=
  ph_keyGenF frEmb_eFr (by norm_num) (frontSpec_frontP c.L W).ph bfX W cf hbf hT

theorem eFr_ne_zero (j : Fin 8) : eFr j ≠ 0 := frEmb_eFr.ne_zero j

end AdvancedEncryption.DualUse.Prog
