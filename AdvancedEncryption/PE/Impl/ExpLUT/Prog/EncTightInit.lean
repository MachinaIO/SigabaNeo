import PE.Impl.ExpLUT.Prog.EncTightBase
/-!
# Per-tape bounds of the encryption loader (tight encryption clock, part 2)

The loader `encInitP` (`initProgram (encInitOps D)`) writes each core tape with a field read
from a stream (`readFieldP`, length `n`), a copy, or a literal word. `initB ops b` is the
resulting per-tape bound of the core tapes (`initB_spec`), and a read of `n` bits costs
`O(n · 2^99)` steps: the moving loop `mvP` is charged its actual counter `n` (`check_mvP_enc`),
not the common cap.
-/

namespace AdvancedEncryption.ExpLUT.Prog.EncTight

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Tape.Sym SigabaNeo.Tape.Prog.SpecT
open AdvancedEncryption.ExpLUT.Prog.EncW

/-- The inputs of `mvP`: the source stream, the destination and the counter template (`n`). -/
def σMvE : Asg := [pTop, pN, pTop, pTop, pN]

def wMvE : Poly := [([], 2), ([0, 1], 6)]

/-- **The certificate of `mvP`**: `2 + 6 n` sweeps, the destination stays at `n` bits. -/
theorem check_mvP_enc : check 8 mvP σMvE [pTop, pN] wMvE = true := by decide +kernel

/-- The per-tape bound of the core tapes after a list of loader operations. -/
def initB : List InitOp → (Fin 321 → ℕ) → (Fin 321 → ℕ)
  | [], b => b
  | .read _ dst n :: ops, b => initB ops (Function.update b dst n)
  | .copy dst src :: ops, b => initB ops (Function.update b dst (b src))
  | .word dst w :: ops, b => initB ops (Function.update b dst w.length)

theorem coreTape_ne_323 (i : Fin 321) : coreTape i ≠ (323 : Fin 326) := by
  simp [coreTape, Fin.ext_iff]; omega

theorem readMap_ne_core (src : Fin 2) (dst i : Fin 321) (hi : i ≠ dst) (j : Fin 5) :
    readMap src dst j ≠ coreTape i := by
  have hi' : i.val ≠ dst.val := fun h => hi (Fin.ext h)
  fin_cases j <;> simp [readMap, sourceTape, coreTape, Fin.ext_iff] <;> omega

theorem bnd_mvE (X n : ℕ) (j : Fin 5) :
    bnd [X, n] σMvE j = if j.val = 1 ∨ j.val = 4 then n else X := by
  fin_cases j <;> simp [bnd, σMvE, aGet, pEval, mEval, pTop, pN, mo]

/-- **A read of `n` bits**: the destination ends at `n` bits, the other core tapes keep their
bounds, and it costs at most `(n + 1) (32 X + 32)` steps, `X` the common cap. -/
theorem read_bounds (X : ℕ) (src : Fin 2) (dst : Fin 321) (n : ℕ) (hn : n ≤ X)
    (ℓ : Fin 326 → ℕ) (hM : ∀ t, ℓ t ≤ X) :
    lenBoundT (readFieldP src dst n) ℓ (coreTape dst) ≤ n ∧
      (∀ i, i ≠ dst → lenBoundT (readFieldP src dst n) ℓ (coreTape i) ≤ ℓ (coreTape i)) ∧
      (∀ t, lenBoundT (readFieldP src dst n) ℓ t ≤ X) ∧
      timeBoundT (readFieldP src dst n) ℓ ≤ (n + 1) * (32 * X + 32) := by
  have hc : ∀ i, coreTape i ≠ (323 : Fin 326) := coreTape_ne_323
  have h₁ : lenBoundT (putW (323 : Fin 326) (List.replicate n false)) ℓ =
      Function.update ℓ 323 n := by
    rw [lenBoundT_putW, List.length_replicate]
  have h₂ : lenBoundT (cp (coreTape dst) 323) (Function.update ℓ 323 n) =
      Function.update (Function.update ℓ 323 n) (coreTape dst) n := by
    show Function.update (Function.update ℓ 323 n) (coreTape dst) (Function.update ℓ 323 n 323) = _
    rw [Function.update_self]
  have hM₁ : ∀ t, Function.update ℓ 323 n t ≤ X := by
    intro t; rw [Function.update_apply]; split_ifs
    · exact hn
    · exact hM t
  have hM₂ : ∀ t, Function.update (Function.update ℓ 323 n) (coreTape dst) n t ≤ X := by
    intro t; rw [Function.update_apply]; split_ifs
    · exact hn
    · exact hM₁ t
  obtain ⟨a₃, b₃, c₃⟩ := TB.of_check check_mvP_enc [X, n] 326 (readMap src dst)
    (readMap_inj src dst) _
    (by
      intro j
      rw [bnd_mvE]
      fin_cases j
      · exact hM₂ _
      · show Function.update (Function.update ℓ 323 n) (coreTape dst) n (coreTape dst) ≤ _
        simp
      · exact hM₂ _
      · exact hM₂ _
      · show Function.update (Function.update ℓ 323 n) (coreTape dst) n 323 ≤ _
        rw [Function.update_of_ne (hc dst).symm]; simp)
    hM₂
  have hlen : lenBoundT (readFieldP src dst n) ℓ =
      Function.update (lenBoundT (map (readMap src dst) mvP)
        (Function.update (Function.update ℓ 323 n) (coreTape dst) n)) 323 0 := by
    show lenBoundT (clr 323) (lenBoundT (map (readMap src dst) mvP)
      (lenBoundT (cp (coreTape dst) 323)
        (lenBoundT (putW (323 : Fin 326) (List.replicate n false)) ℓ))) = _
    rw [h₁, h₂]; rfl
  refine ⟨?_, fun i hi => ?_, fun t => ?_, ?_⟩
  · rw [hlen, Function.update_of_ne (hc dst)]
    have := a₃ 1
    have e : readMap src dst 1 = coreTape dst := rfl
    rw [e] at this
    simpa [bnd, aGet, pN, mo, pEval, mEval] using this
  · rw [hlen, Function.update_of_ne (hc i),
      lenBoundT_map_off _ _ (readMap_ne_core src dst i hi),
      Function.update_of_ne (fun h => hi (coreTape_inj h)), Function.update_of_ne (hc i)]
  · rw [hlen, Function.update_apply]; split_ifs
    · exact Nat.zero_le _
    · exact b₃ t
  · have tp : timeBoundT (putW (323 : Fin 326) (List.replicate n false)) ℓ ≤
        (n + 1) * (2 * (X + (n + 1)) + 5) := by
      have h := timeBoundT_le_pcount _ (loopFree_putW (323 : Fin 326) (List.replicate n false)) ℓ hM
      rwa [pcount_putW, List.length_replicate] at h
    have tc : timeBoundT (cp (coreTape dst) (323 : Fin 326)) (Function.update ℓ 323 n) ≤
        2 * X + 3 := by
      show 2 * (supB _ + 0) + 3 ≤ _
      have := Sym.supB_le_const hM₁; omega
    have tl : ∀ ℓ' : Fin 326 → ℕ, (∀ t, ℓ' t ≤ X) → timeBoundT (clr (323 : Fin 326)) ℓ' ≤ 2 * X + 3 := by
      intro ℓ' h'
      show 2 * (supB ℓ' + 0) + 3 ≤ _
      have := Sym.supB_le_const h'; omega
    have tm : timeBoundT (map (readMap src dst) mvP)
        (Function.update (Function.update ℓ 323 n) (coreTape dst) n) ≤ (2 * X + 3) * (2 + 6 * n) := by
      refine c₃.trans (le_of_eq ?_)
      simp [top, wMvE, pEval, mEval]
    have ht : timeBoundT (readFieldP src dst n) ℓ =
        timeBoundT (putW (323 : Fin 326) (List.replicate n false)) ℓ +
          (timeBoundT (cp (coreTape dst) (323 : Fin 326))
              (lenBoundT (putW (323 : Fin 326) (List.replicate n false)) ℓ) +
            (timeBoundT (map (readMap src dst) mvP) (lenBoundT (cp (coreTape dst) (323 : Fin 326))
              (lenBoundT (putW (323 : Fin 326) (List.replicate n false)) ℓ)) +
              timeBoundT (clr (323 : Fin 326)) (lenBoundT (map (readMap src dst) mvP)
                (lenBoundT (cp (coreTape dst) (323 : Fin 326))
                  (lenBoundT (putW (323 : Fin 326) (List.replicate n false)) ℓ))))) := rfl
    rw [h₁, h₂] at ht
    rw [ht]
    have t4 := tl _ b₃
    nlinarith [tp, tc, t4, tm]

/-- A literal word. -/
theorem word_bounds (X : ℕ) (dst : Fin 321) (w : List Bool) (hw : w.length ≤ X)
    (ℓ : Fin 326 → ℕ) (hM : ∀ t, ℓ t ≤ X) :
    lenBoundT (putW (coreTape dst) w) ℓ = Function.update ℓ (coreTape dst) w.length ∧
      (∀ t, lenBoundT (putW (coreTape dst) w) ℓ t ≤ X) ∧
      timeBoundT (putW (coreTape dst) w) ℓ ≤ (w.length + 1) * (32 * X + 32) := by
  refine ⟨lenBoundT_putW _ _ _, fun t => ?_, ?_⟩
  · rw [lenBoundT_putW, Function.update_apply]; split_ifs
    · exact hw
    · exact hM t
  · have h := timeBoundT_le_pcount _ (loopFree_putW (coreTape dst) w) ℓ hM
    rw [pcount_putW] at h
    refine h.trans (Nat.mul_le_mul_left _ ?_)
    omega

/-- The length a loader operation writes. -/
def opLen : InitOp → ℕ
  | .read _ _ n => n
  | .copy _ _ => 0
  | .word _ w => w.length

theorem opLen_le_cost (op : InitOp) : opLen op ≤ op.cost := by
  cases op <;> simp [opLen, InitOp.cost] <;> omega

/-- **The loader's per-tape bounds and clock**, from a common cap `X` on every tape. -/
theorem initB_spec (X : ℕ) : ∀ (ops : List InitOp), (∀ op ∈ ops, op.cost ≤ 60 * X) →
    ∀ (ℓ : Fin 326 → ℕ) (b : Fin 321 → ℕ), (∀ t, ℓ t ≤ X) →
      (∀ i, ℓ (coreTape i) ≤ b i) →
      (∀ i, lenBoundT (initProgram ops) ℓ (coreTape i) ≤ initB ops b i) ∧
        (∀ t, lenBoundT (initProgram ops) ℓ t ≤ X) ∧
        timeBoundT (initProgram ops) ℓ ≤
          ((ops.map InitOp.cost).sum + ops.length + 1) * (32 * X + 32)
  | [], _, ℓ, b, hM, hb => by
    refine ⟨fun i => ?_, fun t => ?_, ?_⟩
    · show Function.update ℓ 0 (ℓ 0) (coreTape i) ≤ b i
      simpa using hb i
    · show Function.update ℓ 0 (ℓ 0) t ≤ _
      simpa using hM t
    · show 2 * (supB ℓ + 0) + 3 ≤ _
      have := Sym.supB_le_const hM; simp; omega
  | op :: ops, hc, ℓ, b, hM, hb => by
    have hc₀ := hc op (by simp)
    have hcs : ∀ o ∈ ops, o.cost ≤ 60 * X := fun o ho => hc o (by simp [ho])
    have hge := opLen_le_cost op
    have step : ∃ b' : Fin 321 → ℕ, initB (op :: ops) b = initB ops b' ∧
        (∀ i, lenBoundT op.program ℓ (coreTape i) ≤ b' i) ∧
        (∀ t, lenBoundT op.program ℓ t ≤ X) ∧
        timeBoundT op.program ℓ ≤ (op.cost + 1) * (32 * X + 32) := by
      cases op with
      | read src dst n =>
        simp only [opLen] at hge
        obtain ⟨r1, r2, r3, r4⟩ := read_bounds X src dst n (by simp only [InitOp.cost] at hc₀; omega) ℓ hM
        refine ⟨Function.update b dst n, rfl, fun i => ?_, r3, r4.trans ?_⟩
        · by_cases hi : i = dst
          · subst hi; simpa [InitOp.program] using r1
          · rw [Function.update_of_ne hi]; exact (r2 i hi).trans (hb i)
        · exact Nat.mul_le_mul_right _ (by omega)
      | copy dst src =>
        refine ⟨Function.update b dst (b src), rfl, fun i => ?_, fun t => ?_, ?_⟩
        · show Function.update ℓ (coreTape dst) (ℓ (coreTape src)) (coreTape i) ≤ _
          by_cases hi : i = dst
          · subst hi; simpa using hb src
          · rw [Function.update_of_ne (fun h => hi (coreTape_inj h)), Function.update_of_ne hi]
            exact hb i
        · show Function.update ℓ (coreTape dst) (ℓ (coreTape src)) t ≤ _
          rw [Function.update_apply]; split_ifs
          · exact hM _
          · exact hM t
        · show 2 * (supB ℓ + 0) + 3 ≤ _
          have := Sym.supB_le_const hM
          have : 32 * X + 32 ≤ (InitOp.cost (.copy dst src) + 1) * (32 * X + 32) :=
            Nat.le_mul_of_pos_left _ (by omega)
          omega
      | word dst w =>
        simp only [opLen] at hge
        obtain ⟨r1, r2, r3⟩ := word_bounds X dst w (by simp only [InitOp.cost] at hc₀; omega) ℓ hM
        refine ⟨Function.update b dst w.length, rfl, fun i => ?_, r2, r3.trans ?_⟩
        · show lenBoundT (putW (coreTape dst) w) ℓ (coreTape i) ≤ _
          rw [r1]
          by_cases hi : i = dst
          · subst hi; simp
          · rw [Function.update_of_ne (fun h => hi (coreTape_inj h)), Function.update_of_ne hi]
            exact hb i
        · exact Nat.mul_le_mul_right _ (by omega)
    obtain ⟨b', eb, s1, s2, s3⟩ := step
    obtain ⟨t1, t2, t3⟩ := initB_spec X ops hcs _ b' s2 s1
    refine ⟨fun i => eb ▸ t1 i, t2, ?_⟩
    show timeBoundT op.program ℓ + timeBoundT (initProgram ops) (lenBoundT op.program ℓ) ≤ _
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith [s3, t3]

/-- A loader operation writes at most `B dst` bits (a copy from a tape bounded below `B dst`). -/
def opOK (B : Fin 321 → ℕ) : InitOp → Prop
  | .read _ dst n => n ≤ B dst
  | .copy dst src => B src ≤ B dst
  | .word dst w => w.length ≤ B dst

/-- **An invariant bound of the loader**: if every operation respects `B`, so does the result. -/
theorem initB_le (B : Fin 321 → ℕ) : ∀ (ops : List InitOp) (b : Fin 321 → ℕ), b ≤ B →
    (∀ op ∈ ops, opOK B op) → initB ops b ≤ B
  | [], b, hb, _ => hb
  | op :: ops, b, hb, hops => by
    have h₀ := hops op (by simp)
    have hr : ∀ o ∈ ops, opOK B o := fun o ho => hops o (by simp [ho])
    cases op with
    | read src dst n =>
      refine initB_le B ops _ (fun i => ?_) hr
      rw [Function.update_apply]; split_ifs with h
      · subst h; exact h₀
      · exact hb i
    | copy dst src =>
      refine initB_le B ops _ (fun i => ?_) hr
      rw [Function.update_apply]; split_ifs with h
      · subst h; exact (hb src).trans h₀
      · exact hb i
    | word dst w =>
      refine initB_le B ops _ (fun i => ?_) hr
      rw [Function.update_apply]; split_ifs with h
      · subst h; exact h₀
      · exact hb i

end AdvancedEncryption.ExpLUT.Prog.EncTight
