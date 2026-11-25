import PE.Impl.ExpLUT.Prog.EncNormalizeTime
import PE.Impl.ExpLUT.Prog.EncSamplerTimeConf
/-! # Parser and sampler clock bounds before normalization -/
namespace AdvancedEncryption.ExpLUT.Prog.EncW
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.Prog
open AdvancedEncryption.ExpLUT.Params

/-- The frame parser's coarse bounds are independent of its tape placement. -/
theorem ubp_unfrBody_mapped {k : ℕ} (u : Fin 4 → Fin k) (M : ℕ) :
    UBP (map u unfrBody) M (4 * (2 * (M + 2) + 3) + 2) (M + 1) := by
  have h1 := (ubp_prim0 (.tail (u 0)) rfl M).seq ((ubp_prim (.snocHead (u 1) (u 0)) M).seq
    (ubp_prim0 (.tail (u 0)) rfl (M + 1)))
  have h2 := (ubp_prim0 (.tail (u 0)) rfl M).seq (ubp_prim (.snoc (u 3) true) M)
  have h3 := ubp_prim0 (.copy (u 3) (u 3)) rfl M
  refine (ubp_ifBlank (i := u 3) (ubp_ifBit (i := u 0) h1 h2) h3).mono ?_ ?_
  · simp only [max_def]; split_ifs <;> omega
  · simp only [max_def]; split_ifs <;> omega

theorem ubp_unfr_mapped {k : ℕ} (u : Fin 4 → Fin k) (M : ℕ) :
    UBP (map u unfrP) M (unfrT M) (2 * M) := by
  have h := (ubp_prim0 (.copy (u 2) (u 0)) rfl M).seq
    ((ubp_loop (u 2) (map u unfrBody) 1 _ (ubp_unfrBody_mapped u) M).seq
      (ubp_prim0 (.clear (u 3)) rfl _))
  refine h.mono (le_of_eq ?_) (by omega)
  simp only [unfrT, Nat.add_assoc]

set_option exponentiation.threshold 2000 in
theorem bounds_parse : UBP EncIO.parse (2 ^ 100) (2 ^ 214) (2 ^ 104) := by
  have h1 := ubp_unfr_mapped (EncIO.parseMap 4) (2 ^ 100)
  have h2 := ubp_unfr_mapped (EncIO.parseMap 1) (2 * 2 ^ 100)
  have h3 := ubp_unfr_mapped (EncIO.parseMap 1) (2 * (2 * 2 ^ 100))
  have h4 := ubp_unfr_mapped (EncIO.parseMap 1) (2 * (2 * (2 * 2 ^ 100)))
  have h5 := ubp_prim0 (.clear (4 : Fin 105)) rfl (2 * (2 * (2 * (2 * 2 ^ 100))))
  exact (h1.seq (h2.seq (h3.seq (h4.seq h5)))).mono (by norm_num [unfrT]) (by norm_num)

theorem embedF_bound {m k : ℕ} (e : Fin m ↪ Fin k) {a : Fin k → ℕ} {b : Fin m → ℕ}
    {M : ℕ} (ha : ∀ i, a i ≤ M) (hb : ∀ j, b j ≤ M) : ∀ i, embedF e a b i ≤ M := by
  intro i
  rcases embedF_cases e a b i with ⟨_, h⟩ | ⟨j, _, h⟩
  · rw [h]; exact ha i
  · rw [h]; exact hb j

/-- Uniform compiler bounds for a program with probabilistic and framed subprograms. -/
def XBound {k : ℕ} (p : XProg k) (M T M' : ℕ) : Prop :=
  ∀ ℓ, (∀ i, ℓ i ≤ M) → XProg.timeBoundT p ℓ ≤ T ∧ ∀ i, XProg.lenBoundT p ℓ i ≤ M'

theorem XBound.seq {k : ℕ} {p q : XProg k} {M T M' U M'' : ℕ}
    (hp : XBound p M T M') (hq : XBound q M' U M'') : XBound (.seq p q) M (T + U) M'' :=
  fun ℓ hℓ => ⟨Nat.add_le_add (hp ℓ hℓ).1 (hq _ (hp ℓ hℓ).2).1, (hq _ (hp ℓ hℓ).2).2⟩

theorem XBound.mono {k : ℕ} {p : XProg k} {M T M' U M'' : ℕ}
    (h : XBound p M T M') (hT : T ≤ U) (hM : M' ≤ M'') : XBound p M U M'' :=
  fun ℓ hℓ => ⟨(h ℓ hℓ).1.trans hT, fun i => ((h ℓ hℓ).2 i).trans hM⟩

theorem XBound.frame {m k : ℕ} (e : Fin m ↪ Fin k) {p : XProg m} {M T M' : ℕ}
    (h : XBound p M T M') (hM : M ≤ M') : XBound (.frame e p) M T M' := by
  intro ℓ hℓ
  have hb := h (ℓ ∘ e) (fun j => hℓ (e j))
  exact ⟨hb.1, embedF_bound e (fun i => (hℓ i).trans hM) hb.2⟩

set_option exponentiation.threshold 2000 in
theorem bounds_prepare : XBound (EncIO.prepare Dc 16 6 eFl) (2 ^ 100) (2 ^ 301) (2 ^ 105) := by
  have h1 : XBound (.prog EncIO.parse) (2 ^ 100) (2 ^ 214) (2 ^ 104) := bounds_parse
  have h2 : XBound (encCoinsP Dc 16 6 eFl) (2 ^ 104) (2 ^ 300) (2 ^ 105) :=
    fun _ hℓ => EncConf.encCoins_bounds_loose hℓ
  exact (h1.seq (h2.frame EncIO.sampleFrame (by norm_num))).mono (by norm_num) le_rfl

set_option exponentiation.threshold 2000 in
theorem bounds_widePrepare : XBound (widePrepare Dc 16 6 eFl) (2 ^ 100) (2 ^ 301) (2 ^ 110) :=
  ((bounds_prepare.frame prepareFrame (by norm_num))).mono le_rfl (by norm_num)

theorem XBound.total {k : ℕ} {p : XProg k} {M T M' n : ℕ}
    (h : XBound p M T M') (i o : Fin k) (hn : n ≤ M) :
    XProg.totalTimeT p i o n ≤ (2 * M + 2) + T + (2 * M' + 2) := by
  have hi : ∀ j, inputBound i n j ≤ M := by
    intro j
    simp only [inputBound, Function.update_apply]
    split_ifs
    · exact hn
    · exact Nat.zero_le _
  have hb := h _ hi
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hn) 2) hb.1)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hb.2 o)) 2)

end AdvancedEncryption.ExpLUT.Prog.EncW
