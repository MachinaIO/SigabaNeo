import PE.Impl.RingBTVW.Prog.EncCoreCert
import PE.Impl.RingBTVW.Prog.EncCostP

/-!
# The time of the compiled `Enc` with a per-tape bound of the core

`ub_encP` charges the core `encCoreP` its uniform bound `tbC · (M + 1) ^ tbD`: every loop, at
every nesting level, is charged the longest tape `M`. Here the core is bounded per tape, from the
certificate `check_encCoreP` of the abstract interpreter: after the templates (`natL`, built from
a uniform bound `G`), the template tapes hold exactly their lengths (`natL_tmpl`), so every loop
of the core is charged the length of its own counter, and each of its `pEval ρ wE` sweeps costs
`2 G + 3` steps (`core_boundT`). `ub_encTailT` is the uniform bound of the tail of `Enc`
(templates, core, output frame) that results, and `ub_encPT` the bound of `encP`, with the parser
bounded additively (`ub_encParsePT`).
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg SigabaNeo.Tape.Sym

/-! ### Templates -/

theorem preserves_natL : ∀ (l : List (Fin 124 × ℕ)) (i : Fin 124), i ≠ 123 → (∀ p ∈ l, p.1 ≠ i) →
    (natL l).Preserves i
  | [], i, h, _ => by
    show Prog.Preserves i (.prim (.copy 123 123))
    simp [Prog.Preserves, Prim.writes]
    exact h
  | p :: l, i, h, hl => ⟨preserves_natP (hl p (by simp)) (Ne.symm h) _,
      preserves_natL l i h fun q hq => hl q (by simp [hq])⟩

/-- **After the templates, each template tape is at most its length.** -/
theorem natL_tmpl : ∀ (l : List (Fin 124 × ℕ)) (G : ℕ) (ℓ : Fin 124 → ℕ), (∀ i, ℓ i ≤ G) →
    (∀ p ∈ l, p.2 ≤ G) → (∀ p ∈ l, p.1 ≠ 123) → (l.map Prod.fst).Nodup →
    ∀ p ∈ l, lenBoundT (natL l) ℓ p.1 ≤ p.2
  | [], _, _, _, _, _, _, p, hp => by simp at hp
  | q :: l, G, ℓ, hℓ, hG, hc, hnd, p, hp => by
    have hq123 : q.1 ≠ 123 := hc q (by simp)
    obtain ⟨h1, -⟩ := natP_bounds (Ne.symm hq123) q.2 ℓ G hℓ (hG q (by simp))
    have hℓ1 : ∀ i, lenBoundT (natP q.1 123 q.2) ℓ i ≤ G := fun i => (h1 i).trans (by
      simp only [natB]
      split_ifs
      · exact hG q (by simp)
      · exact max_le (hℓ _) (hG q (by simp))
      · exact hℓ i)
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    show lenBoundT (natL l) (lenBoundT (natP q.1 123 q.2) ℓ) p.1 ≤ p.2
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [lenBoundT_of_preserves (natL l) p.1 (preserves_natL l p.1 hq123
        fun r hr h => hnd.1 ⟨r, hr, h⟩)]
      exact (h1 p.1).trans (by simp [natB])
    · exact natL_tmpl l G _ hℓ1 (fun r hr => hG r (by simp [hr]))
        (fun r hr => hc r (by simp [hr])) hnd.2 p hp

/-! ### The core -/

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The values of the variables of `σE`: the top size `G`, then `N`, `K`, `k`, `d`, the number of
trapdoor columns, the number of encodings, the number of attribute bits, `k − K`, `N K − K`. -/
def ρE (G : ℕ) : List ℕ := [G, N, K, k, c.d, nTrap k, nJenc (N := N) hk, nA, k - K, N * K - K]

theorem tmplList_nodup : ((tmplList hk c).map Prod.fst).Nodup := by
  simp only [tmplList, List.map_cons, List.map_nil]
  decide

theorem aGet_σE_top (v : ℕ) (h : v < 13 ∨ 39 ≤ v) (hv : v < 120) : aGet σE v = pTop := by
  rcases h with h | h <;> interval_cases v <;> rfl

theorem pEval_mE (ρ : List ℕ) (c : ℕ) (e : List ℕ) : pEval ρ (mE c e) = c * mEval ρ (0 :: e) := by
  simp [mE, pEval]

set_option maxHeartbeats 4000000 in
/-- The templates fit the abstract store `σE`. -/
theorem le_bnd_σE (G : ℕ) (ℓ : Fin 120 → ℕ) (hG : ∀ j, ℓ j ≤ G)
    (htm : ∀ p ∈ tmplList hk c, ∀ j : Fin 120, e120 j = p.1 → ℓ j ≤ p.2) :
    ℓ ≤ bnd (ρE hk c G) σE := by
  intro ⟨v, hv⟩
  show ℓ ⟨v, hv⟩ ≤ pEval (ρE hk c G) (aGet σE v)
  by_cases h : v < 13 ∨ 39 ≤ v
  · rw [aGet_σE_top v h hv, pEval_of_isTop rfl]
    exact hG _
  push Not at h
  obtain ⟨h1, h2⟩ := h
  simp only [tmplList, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at htm
  obtain ⟨-, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38⟩ := htm
  interval_cases v <;>
    (first
      | refine (h13 _ rfl).trans (le_of_eq ?_)
      | refine (h14 _ rfl).trans (le_of_eq ?_)
      | refine (h15 _ rfl).trans (le_of_eq ?_)
      | refine (h16 _ rfl).trans (le_of_eq ?_)
      | refine (h17 _ rfl).trans (le_of_eq ?_)
      | refine (h18 _ rfl).trans (le_of_eq ?_)
      | refine (h19 _ rfl).trans (le_of_eq ?_)
      | refine (h20 _ rfl).trans (le_of_eq ?_)
      | refine (h21 _ rfl).trans (le_of_eq ?_)
      | refine (h22 _ rfl).trans (le_of_eq ?_)
      | refine (h23 _ rfl).trans (le_of_eq ?_)
      | refine (h24 _ rfl).trans (le_of_eq ?_)
      | refine (h25 _ rfl).trans (le_of_eq ?_)
      | refine (h26 _ rfl).trans (le_of_eq ?_)
      | refine (h27 _ rfl).trans (le_of_eq ?_)
      | refine (h28 _ rfl).trans (le_of_eq ?_)
      | refine (h29 _ rfl).trans (le_of_eq ?_)
      | refine (h30 _ rfl).trans (le_of_eq ?_)
      | refine (h31 _ rfl).trans (le_of_eq ?_)
      | refine (h32 _ rfl).trans (le_of_eq ?_)
      | refine (h33 _ rfl).trans (le_of_eq ?_)
      | refine (h34 _ rfl).trans (le_of_eq ?_)
      | refine (h35 _ rfl).trans (le_of_eq ?_)
      | refine (h36 _ rfl).trans (le_of_eq ?_)
      | refine (h37 _ rfl).trans (le_of_eq ?_)
      | refine (h38 _ rfl).trans (le_of_eq ?_)) <;>
    simp [aGet, σE, tmplE, mE, pEval, mEval, ρE] <;> ring

/-- **The core from the templates**: framed on the tapes `0 … 119`, from tapes at most `G` with
the templates at their lengths, the core takes at most `(2 G + 3) · pEval (ρE G) wE` steps and
leaves every tape at most `G`. -/
theorem core_boundT (G : ℕ) (ℓ : Fin 124 → ℕ) (hG : ∀ i, ℓ i ≤ G)
    (htm : ∀ p ∈ tmplList hk c, ℓ p.1 ≤ p.2) :
    timeBoundT (frame e120 (prog encCoreP)) ℓ ≤ (2 * G + 3) * pEval (ρE hk c G) wE ∧
      ∀ i, lenBoundT (frame e120 (prog encCoreP)) ℓ i ≤ G := by
  have hb := le_bnd_σE hk c G (fun j => ℓ (e120 j)) (fun j => hG _)
    (fun p hp j hj => by rw [hj]; exact htm p hp)
  obtain ⟨-, h2, h3⟩ := bounds_of_check check_encCoreP (ρE hk c G) hb (fun j => hG _)
  refine ⟨h3, fun i => ?_⟩
  show embedF e120 ℓ (Prog.lenBoundT encCoreP fun j => ℓ (e120 j)) i ≤ G
  rcases embedF_cases e120 ℓ (Prog.lenBoundT encCoreP fun j => ℓ (e120 j)) i with
    ⟨-, h⟩ | ⟨j, -, h⟩
  · rw [h]; exact hG i
  · rw [h]; exact h2 j

/-- **The tail of `Enc`** (templates, core, output frame) from tapes at most `G`. -/
theorem ub_encTailT (G : ℕ) (hT : ∀ p ∈ tmplList hk c, p.2 ≤ G) :
    UB (encTail hk c) G (natLT (tmplList hk c) G + ((2 * G + 3) * pEval (ρE hk c G) wE + appT G))
      (4 * G + 1) := by
  intro ℓ hℓ
  have u1 := ub_natL (tmplList hk c) G hT (fun p hp => tmpl_lt hk c p hp 123 (by decide)) ℓ hℓ
  have htm := natL_tmpl (tmplList hk c) G ℓ hℓ hT (tmplList_ne hk c) (tmplList_nodup hk c)
  have hc := core_boundT hk c G _ u1.2 htm
  have u3 := ub_frameApP (k := 124) 122 0 123 121 G _ hc.2
  refine ⟨?_, u3.2⟩
  show timeBoundT (natL (tmplList hk c)) ℓ + (timeBoundT (frame e120 (prog encCoreP)) _ +
    timeBoundT (frameApP 122 0 123 121) _) ≤ _
  exact Nat.add_le_add u1.1 (Nat.add_le_add hc.1 u3.1)

/-! ### The parser, additively

`ub_ufChunk` lets a chunk of `n` bits double the uniform bound (its loop is charged the uniform
bound `M` of rounds). Its counter has `n` bits, so the chunk adds at most `n` to the bound
(`ub_ufChunkT`), and the parser at most the sum of its chunks (`ub_encParsePT`). -/

/-- The time of a round of `unframeP`. -/
def ufTb (X : ℕ) : ℕ := (2 * (X + 1) + 3) + ((2 * (X + 1) + 3) + (2 * (X + 1 + 1) + 3))

/-- The time of `ufChunk D n` from tapes below `M`. -/
def ufCTT (n M : ℕ) : ℕ :=
  (2 * n + 1) * (4 * M + 12) + ((2 * (M + 1) + 3 + loopT ufTb 1 M n) + (2 * (M + n * 1 + 1) + 3))

theorem ub_ufChunkT (D : Fin 124) (n M : ℕ) (hn : n ≤ M) :
    UB (ufChunk D n) M (ufCTT n M) (M + n) := by
  intro ℓ hℓ
  have h1 := ub_natP (k := 124) (t := 121) (c := 123) (by decide) hn ℓ hℓ
  have h1' := (natP_bounds (t := (121 : Fin 124)) (c := 123) (by decide) n ℓ M hℓ hn).1 121
  have h2 := ub_copyS (k := 124) 123 121 M _ h1.2
  have hc : lenBoundT (prog (.prim (.copy 123 121))) (lenBoundT (natP 121 123 n) ℓ) 123 ≤ n := by
    show (Prim.copy (123 : Fin 124) 121).lenT _ 123 ≤ n
    simp only [Prim.lenT, Function.update_self]
    exact h1'.trans (by simp [natB])
  have hb : ∀ X, UB (seq (prog (.prim (.tail 120))) (seq (prog (.prim (.snocHead D 120)))
      (prog (.prim (.tail 120))))) X (ufTb X) (X + 1) := fun X =>
    (ub_tailX 120 X).seq ((ub_prim (.snocHead D 120) X).seq (ub_tailX 120 (X + 1)))
  have h3 := ub_loop (i := 123) hb _ h2.2 hc
  have h4 := ub_clear (k := 124) 121 (M + n * 1) _ h3.2
  refine ⟨?_, fun i => (h4.2 i).trans (by omega)⟩
  exact Nat.add_le_add h1.1 (Nat.add_le_add (Nat.add_le_add h2.1 h3.1) h4.1)

/-- The time of the parser of `Enc` (counts as variables). -/
def parseETv (p n1 n2 n3 n4 M : ℕ) : ℕ :=
  dropCT p M + (ufCTT n1 M + (ufCTT n2 (M + n1) + (ufCTT n3 (M + n1 + n2) +
    (ufCTT n4 (M + n1 + n2 + n3) + ((2 * (M + n1 + n2 + n3 + n4 + 1) + 3) +
    (ufCTT nA (M + n1 + n2 + n3 + n4) + ((2 * (M + n1 + n2 + n3 + n4 + nA + 1) + 3) +
      ufCTT 1 (M + n1 + n2 + n3 + n4 + nA))))))))

/-- The bound after the parser of `Enc` (counts as variables). -/
def parseEGv (n1 n2 n3 n4 M : ℕ) : ℕ := M + n1 + n2 + n3 + n4 + nA + 1

set_option maxRecDepth 100000 in
/-- **The parser of `Enc`, additively.** -/
theorem ub_encParsePT (M : ℕ)
    (h0 : 2 * RingBTVW.pw.length + 1 ≤ M)
    (h1 : (Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K)) ≤ M)
    (h2 : (Enum.list (α := Fin 1)).length * ((Enum.list (α := TrapCol k)).length * (N * K)) ≤ M)
    (h3 : (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).length *
      ((Enum.list (α := Fin 1)).length * ((Enum.list (α := RingBTVW.Fresh.Col k)).length * (N * K))) ≤ M)
    (h4 : N * K ≤ M) (h5 : nA ≤ M) :
    UB (encParseP hk c) M
      (parseETv (2 * RingBTVW.pw.length + 1)
        ((Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K)))
        ((Enum.list (α := Fin 1)).length * ((Enum.list (α := TrapCol k)).length * (N * K)))
        ((Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).length *
          ((Enum.list (α := Fin 1)).length * ((Enum.list (α := RingBTVW.Fresh.Col k)).length * (N * K))))
        (N * K) M)
      (parseEGv
        ((Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K)))
        ((Enum.list (α := Fin 1)).length * ((Enum.list (α := TrapCol k)).length * (N * K)))
        ((Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).length *
          ((Enum.list (α := Fin 1)).length * ((Enum.list (α := RingBTVW.Fresh.Col k)).length * (N * K))))
        (N * K) M) := by
  rw [encParseP]
  refine (((ub_dropChunk _ M h0).mono le_rfl (show M + M * 0 ≤ M by omega)).seq <|
    (ub_ufChunkT 1 _ _ h1).seq <| (ub_ufChunkT 2 _ _ (by omega)).seq <|
    (ub_ufChunkT 3 _ _ (by omega)).seq <| (ub_ufChunkT 4 _ _ (by omega)).seq <|
    (ub_tailX 120 _).seq <| (ub_ufChunkT 5 _ _ (by omega)).seq <|
    (ub_tailX 120 _).seq (ub_ufChunkT 6 _ _ (by omega))).mono (le_of_eq rfl) (le_of_eq rfl)

/-- **The uniform bound of `encP`** with the additive parser and the per-tape bound of the core
(`P`: the bound after the parser, `G`: after the samplers). -/
theorem ub_encPT {X : ChiSampler c} (M : ℕ) (hpres : X.P.Preserves 6)
    (h0 : 2 * RingBTVW.pw.length + 1 ≤ M)
    (h1 : (Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K)) ≤ M)
    (h2 : (Enum.list (α := Fin 1)).length * ((Enum.list (α := TrapCol k)).length * (N * K)) ≤ M)
    (h3 : (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).length *
      ((Enum.list (α := Fin 1)).length * ((Enum.list (α := RingBTVW.Fresh.Col k)).length * (N * K))) ≤ M)
    (h4 : N * K ≤ M) (h5 : nA ≤ M) {P T : ℕ}
    (hP : parseEGv
        ((Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K)))
        ((Enum.list (α := Fin 1)).length * ((Enum.list (α := TrapCol k)).length * (N * K)))
        ((Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).length *
          ((Enum.list (α := Fin 1)).length * ((Enum.list (α := RingBTVW.Fresh.Col k)).length * (N * K))))
        (N * K) M = P)
    (hT : parseETv (2 * RingBTVW.pw.length + 1)
        ((Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K)))
        ((Enum.list (α := Fin 1)).length * ((Enum.list (α := TrapCol k)).length * (N * K)))
        ((Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).length *
          ((Enum.list (α := Fin 1)).length * ((Enum.list (α := RingBTVW.Fresh.Col k)).length * (N * K))))
        (N * K) M = T)
    (s1 : (bCoins (N * K)).S₀ ≤ P)
    (s2 : (X.B.count ((Enum.list (α := Fin c.d)).length * N)).S₀ ≤ P)
    (s3 : (X.B.count N).S₀ ≤ P)
    (s4 : (X.B.count ((Enum.list (α := RingBTVW.Fresh.Col k)).length * N)).S₀ ≤ P)
    (s6 : ((bEntB N K).count (nR hk c)).S₀ ≤ P)
    (s7 : ((bEntF K c.w).count (nE (N := N) hk)).S₀ ≤ P)
    (ht : ∀ p ∈ tmplList hk c, p.2 ≤ encS hk c X.B P) :
    UB (encP hk c X) M (T + (encST hk c X.B P +
      (natLT (tmplList hk c) (encS hk c X.B P) +
        ((2 * encS hk c X.B P + 3) * pEval (ρE hk c (encS hk c X.B P)) wE +
          appT (encS hk c X.B P)))))
      (4 * encS hk c X.B P + 1) := by
  subst hP hT
  rw [encP]
  refine ((ub_encParsePT hk c M h0 h1 h2 h3 h4 h5).seq <|
    (ub_of_atb e7 (atbb_coinsF _) s1).seq <|
    (ub_of_atb e8 (atbb_repF X.atb hpres _) (by omega)).seq <|
    (ub_of_atb e9 (atbb_repF X.atb hpres _) (by omega)).seq <|
    (ub_of_atb e9 (atbb_repF X.atb hpres _) (by omega)).seq <|
    (ub_of_atb e9 (atbb_repF X.atb hpres _) (by omega)).seq <|
    (ub_of_atb e10 (atbb_repF (atbb_entB N K) (preserves6_entB N K) _) (by omega)).seq <|
    (ub_of_atb e11 (atbb_repF (atbb_entF K c.w) (preserves6_entF K c.w) _) (by omega)).seq <|
    (ub_of_atb e12 (atbb_repF X.atb hpres _) (by omega)).seq <|
    ub_encTailT hk c _ ht).mono (le_of_eq ?_) (le_of_eq rfl)
  simp only [encST, encS, Nat.add_assoc]

end AdvancedEncryption.RingBTVW.Prog
