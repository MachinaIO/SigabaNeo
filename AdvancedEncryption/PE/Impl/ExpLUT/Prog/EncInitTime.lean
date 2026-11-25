import PE.Impl.ExpLUT.Prog.EncCoreTime

/-! # Time and length bounds for the actual encryption initializer -/
namespace AdvancedEncryption.ExpLUT.Prog.EncW
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog
open AdvancedEncryption.ExpLUT.Params

set_option exponentiation.threshold 2000 in
theorem phase_readField (src : Fin 2) (dst : Fin 321) (n : ℕ) (hn : n ≤ 2 ^ 99) :
    PhaseBound (readFieldP src dst n) (2 ^ 311) := by
  have h1 := phase_putW (323 : Fin 326) (List.replicate n false) (by simpa using hn)
  have h2 := phase_prim (.copy (coreTape dst) (323 : Fin 326)) rfl
  have h3 : PhaseBound (map (readMap src dst) mvP) (2 ^ 310) :=
    mapped_poly mvP (by rfl) (by decide +kernel) 326 _
  have h4 := phase_prim (.clear (323 : Fin 326)) rfl
  exact (h1.seq (h2.seq (h3.seq h4))).mono (by norm_num)

set_option exponentiation.threshold 2000 in
theorem phase_initOp (op : InitOp) (hc : op.cost ≤ 60 * 2 ^ 99) :
    PhaseBound op.program (2 ^ 311) := by
  cases op with
  | read src dst n =>
    exact phase_readField src dst n (by simp only [InitOp.cost] at hc; omega)
  | copy dst src =>
    exact (phase_prim (.copy (coreTape dst) (coreTape src)) rfl).mono (by norm_num)
  | word dst w =>
    exact (phase_putW (coreTape dst) w (by simp only [InitOp.cost] at hc; omega)).mono (by norm_num)

set_option exponentiation.threshold 2000 in
theorem phase_initProgram (ops : List InitOp) (hc : ∀ op ∈ ops, op.cost ≤ 60 * 2 ^ 99) :
    PhaseBound (initProgram ops) (ops.length * 2 ^ 311 + 2 ^ 102) := by
  induction ops with
  | nil => simpa [initProgram] using phase_prim (.copy (0 : Fin 326) 0) rfl
  | cons op ops ih =>
    exact ((phase_initOp op (hc op (by simp))).seq
      (ih (fun a ha => hc a (by simp [ha])))).mono (by simp only [List.length_cons]; omega)

theorem initOp_cost_le_sum (op : InitOp) : ∀ ops : List InitOp,
    op ∈ ops → op.cost ≤ (ops.map InitOp.cost).sum
  | [], h => by simp at h
  | a :: ops, h => by
    simp only [List.mem_cons] at h
    simp only [List.map_cons, List.sum_cons]
    rcases h with rfl | h
    · omega
    · exact (initOp_cost_le_sum op ops h).trans (Nat.le_add_left _ _)

set_option exponentiation.threshold 2000 in
theorem encInitOps_cost_tight : ((encInitOps Dc).map InitOp.cost).sum ≤ 60 * 2 ^ 99 := by
  simp only [encInitOps, List.map_append, List.sum_append]
  exact (Nat.add_le_add (Nat.add_le_add EncConf.cost_public_tight EncConf.cost_coins_tight)
    EncConf.cost_templates_tight).trans (by norm_num)

theorem length_encInitOps (D : Dims) : (encInitOps D).length = 82 := by
  simp [encInitOps, publicInitOps, coinInitOps, templateInitOps]

set_option exponentiation.threshold 2000 in
/-- The initializer preserves the common tape bound and takes at most `2^318` steps. -/
theorem phase_encInitP : PhaseBound (encInitP Dc) (2 ^ 318) := by
  have h := phase_initProgram (encInitOps Dc) (fun op hop =>
    (initOp_cost_le_sum op _ hop).trans encInitOps_cost_tight)
  rw [length_encInitOps] at h
  exact h.mono (by norm_num)

theorem lenBoundT_copy_self {k : ℕ} (i : Fin k) (ℓ : Fin k → ℕ) :
    lenBoundT (cp i i) ℓ = ℓ := by
  simp [lenBoundT, Prim.lenT]

/-- Splitting a list of initialization operations also splits the compiler's length transformer. -/
theorem lenBoundT_initProgram_append (as bs : List InitOp) (ℓ : Fin 326 → ℕ) :
    lenBoundT (initProgram (as ++ bs)) ℓ =
      lenBoundT (initProgram bs) (lenBoundT (initProgram as) ℓ) := by
  induction as generalizing ℓ with
  | nil => simp only [List.nil_append, initProgram, lenBoundT_copy_self]
  | cons op as ih =>
    simp only [List.cons_append, initProgram, lenBoundT, ih]

/-- Only three fixed fields follow the sixteen-position counter. -/
theorem encInitOps_drop78 (D : Dims) : (encInitOps D).drop 78 =
    [.word (tailSlot 35) (List.replicate 16 false),
     .word (tailSlot 36) (List.replicate 1 false),
     .word (tailSlot 37) (List.replicate (D.N * D.K) false),
     .word (tailSlot 38) (List.replicate (2 * (D.N * D.K)) false)] := by
  simp only [encInitOps, publicInitOps, coinInitOps, templateInitOps, finRange8, zeroInit]
  rfl

theorem lenBoundT_seq_enc {k : ℕ} (p q : SigabaNeo.Tape.Prog k) (ℓ : Fin k → ℕ) :
    lenBoundT (.seq p q) ℓ = lenBoundT q (lenBoundT p ℓ) := rfl

/-- The count is set at the level of compiler bounds, not only actual execution. -/
theorem lenBoundT_encInitP_count (D : Dims) (ℓ : Fin 326 → ℕ) :
    lenBoundT (encInitP D) ℓ (coreTape (tailSlot 35)) = 16 := by
  unfold encInitP
  rw [← List.take_append_drop 78 (encInitOps D), lenBoundT_initProgram_append,
    encInitOps_drop78]
  generalize lenBoundT (initProgram ((encInitOps D).take 78)) ℓ = a
  simp only [initProgram, InitOp.program, lenBoundT_seq_enc, lenBoundT_putW,
    List.length_replicate, lenBoundT_copy_self]
  norm_num [coreTape, tailSlot, phaseSlot, Function.update]

theorem phase_seq_count {k : ℕ} {p q : SigabaNeo.Tape.Prog k} {T U : ℕ} (c : Fin k)
    (hp : PhaseBound p T) (hc : ∀ ℓ, lenBoundT p ℓ c ≤ 16)
    (hq : ∀ ℓ, (∀ i, ℓ i ≤ 2 ^ 99) → ℓ c ≤ 16 →
      timeBoundT q ℓ ≤ U ∧ ∀ i, lenBoundT q ℓ i ≤ 2 ^ 99) :
    PhaseBound (.seq p q) (T + U) := by
  intro ℓ hℓ
  have h1 := hp ℓ hℓ
  have h2 := hq _ h1.2 (hc ℓ)
  exact ⟨Nat.add_le_add h1.1 h2.1, h2.2⟩

/-- The concrete initializer establishes both premises of the core clock bound. -/
theorem phase_initializedCoreP : PhaseBound (initializedCoreP Dc) (2 ^ 318 + 2 ^ 814) :=
  phase_seq_count (coreTape (tailSlot 35)) phase_encInitP
    (fun ℓ => (lenBoundT_encInitP_count Dc ℓ).le)
    (fun _ hℓ hn => time_core_mapped coreTape coreTape_inj hℓ hn)

set_option exponentiation.threshold 2000 in
theorem phase_eraseP (is : List (Fin 326)) :
    PhaseBound (eraseP is) ((is.length + 1) * 2 ^ 102) := by
  induction is with
  | nil => simpa [eraseP] using phase_prim (.copy (0 : Fin 326) 0) rfl
  | cons i is ih =>
    exact ((phase_prim (.clear i) rfl).seq ih).mono (by simp only [List.length_cons]; omega)

set_option exponentiation.threshold 2000 in
theorem phase_cleanCoreP : PhaseBound (cleanCoreP Dc) (2 ^ 815) := by
  have h := phase_initializedCoreP.seq (phase_eraseP ((List.finRange 325).map Fin.succ))
  exact h.mono (by simp only [List.length_map, List.length_finRange]; norm_num)

set_option exponentiation.threshold 2000 in
theorem phase_relocateP : PhaseBound relocateP (4 * 2 ^ 102) := by
  exact ((phase_prim (.copy (321 : Fin 326) 0) rfl).seq
    ((phase_prim (.copy 322 1) rfl).seq
      ((phase_prim (.clear 0) rfl).seq (phase_prim (.clear 1) rfl)))).mono (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.EncW
