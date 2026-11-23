import PE.Impl.DualUse.Prog.SetupI
import PE.Impl.DualUse.Params.Conf

/-!
# The χ coefficient sampler of the concrete configuration

The setup programs of hybrid 3 and of the ideal side (`law_setup3P`, `law_setupIP`) take a χ
coefficient sampler `Pχ : XProg 7` with `AppendLaw Pχ 0 P3 (μχ c)`: it appends the word
`zmodEnc K` of a χ sample to tape `0`, with its scratch among the tapes `2, 3, 4` (blank before and
after), changing nothing else.

For the centered binomial law of width `η` (`ModuleLWE.coeffLaw (2^K) (.cbd η)`), `cbdP η L K`:

1. appends `2η` fair bits to tape `2` (coin tape `4`), unrolled;
2. writes `η + a − b` in unary on tape `3` (`a`, `b` the numbers of ones among the first and the
   last `η` coins): `η` ones, then one more per one of the first half and one fewer per one of the
   second half, consuming tape `2`;
3. reads the unary value `j` by a chain of `2η + 1` tests (`chainP`) and, at the leaf `j`, appends
   the constant word of `v = j − η`: its `L` low bits (`zmodEnc L`), then `K − L` copies of the sign
   (counter on the tapes `3`, `4`). For `|v| < 2^{L−1} ≤ 2^{K−1}` this is `zmodEnc K` of `v`
   (`zmodEnc_small`).

**`law_cbdP`**: `AppendLaw (cbdP η L K) 0 P3 ((coeffLaw (2^K) (.cbd η)).map (zmodEnc K).enc)`.
**`law_chiP`**: for `confP` (`η = 16`, `L = 6`), `AppendLaw chiP 0 P3 (μχ confP)`, the hypothesis
of `law_setup3P` / `law_setupIP`; `wf_chiP`, `preserves_chiP` (tapes `1`, `5`, `6`).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.XProg Cslib
  Cslib.Probability

/-! ### Small residues -/

/-- **A small residue mod `2^K`**: its `L` low bits, then the sign. -/
theorem zmodEnc_small {K L : ℕ} (hL : 1 ≤ L) (hLK : L ≤ K) (v : ℤ) (h1 : -(2 : ℤ) ^ (L - 1) ≤ v)
    (h2 : v < 2 ^ (L - 1)) :
    (zmodEnc K).enc (v : ZMod (2 ^ K)) =
      (zmodEnc L).enc (v : ZMod (2 ^ L)) ++ List.replicate (K - L) (decide (v < 0)) := by
  have hpL : (2 : ℕ) ^ L = 2 * 2 ^ (L - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hLK' : (2 : ℕ) ^ L ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hLK
  -- the value of the residue as a natural number, below `2^L` or above `2^K − 2^L`
  obtain ⟨a, b, hab, hb, hvK, hvL⟩ : ∃ a b : ℕ, a = (if v < 0 then 2 ^ (K - L) - 1 else 0) ∧
      b < 2 ^ L ∧ (v : ZMod (2 ^ K)).val = 2 ^ L * a + b ∧ (v : ZMod (2 ^ L)).val = b := by
    rcases lt_or_ge v 0 with hv | hv
    · -- `v = −m`
      obtain ⟨m, rfl⟩ : ∃ m : ℕ, v = -(m : ℤ) := ⟨(-v).toNat, by omega⟩
      have hm1 : 1 ≤ m := by omega
      have hm2 : (m : ℤ) ≤ 2 ^ (L - 1) := by omega
      have hm2' : m ≤ 2 ^ (L - 1) := by exact_mod_cast hm2
      have hmL : m < 2 ^ L := by omega
      have hmK : m < 2 ^ K := lt_of_lt_of_le hmL hLK'
      refine ⟨2 ^ (K - L) - 1, 2 ^ L - m, by rw [if_pos hv], by omega, ?_, ?_⟩
      · have : NeZero (2 ^ K) := ⟨by positivity⟩
        rw [Int.cast_neg, Int.cast_natCast, ZMod.neg_val, if_neg, ZMod.val_natCast,
          Nat.mod_eq_of_lt hmK]
        · have hK : 2 ^ K = 2 ^ L * 2 ^ (K - L) := by rw [← pow_add]; congr 1; omega
          have h1' : 1 ≤ 2 ^ (K - L) := Nat.one_le_two_pow
          rw [hK, Nat.mul_sub_one]
          have : 2 ^ L ≤ 2 ^ L * 2 ^ (K - L) := Nat.le_mul_of_pos_right _ h1'
          omega
        · rw [ZMod.natCast_eq_zero_iff]
          exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
      · have : NeZero (2 ^ L) := ⟨by positivity⟩
        rw [Int.cast_neg, Int.cast_natCast, ZMod.neg_val, if_neg, ZMod.val_natCast,
          Nat.mod_eq_of_lt hmL]
        rw [ZMod.natCast_eq_zero_iff]
        exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
    · obtain ⟨t, rfl⟩ : ∃ t : ℕ, v = (t : ℤ) := ⟨v.toNat, by omega⟩
      have ht : t < 2 ^ L := by
        have : (t : ℤ) < 2 ^ (L - 1) := h2
        have : t < 2 ^ (L - 1) := by exact_mod_cast this
        omega
      refine ⟨0, t, by simp, ht, ?_, ?_⟩
      · rw [Int.cast_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (lt_of_lt_of_le ht hLK')]
        simp
      · rw [Int.cast_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ht]
  have hlen : ((zmodEnc K).enc (v : ZMod (2 ^ K))).length =
      ((zmodEnc L).enc (v : ZMod (2 ^ L)) ++ List.replicate (K - L) (decide (v < 0))).length := by
    rw [(zmodEnc K).length, List.length_append, (zmodEnc L).length, List.length_replicate]; omega
  apply List.ext_getElem hlen
  intro i h1i h2i
  have hiK : i < K := by rwa [(zmodEnc K).length] at h1i
  simp only [zmodEnc, List.getElem_map, List.getElem_finRange, Fin.val_cast, hvK]
  rw [Nat.testBit_two_pow_mul_add a hb]
  by_cases hi : i < L
  · rw [if_pos hi, List.getElem_append_left (by simpa using hi)]
    simp [hvL]
  · rw [if_neg hi, List.getElem_append_right (by simp; omega)]
    simp only [List.getElem_replicate, hab]
    split_ifs with hv
    · rw [Nat.testBit_two_pow_sub_one]; simp [hv]; omega
    · simp [hv]

/-! ### The law of each construct -/

theorem law_ifBit {k : ℕ} (i : Fin k) (p q : XProg k) (s : Store k) :
    (ifBit i p q).law s = if (s i).head? = some true then p.law s else q.law s := by
  simp only [law, denote]; split_ifs <;> rfl

theorem law_ifBlank {k : ℕ} (i : Fin k) (p q : XProg k) (s : Store k) :
    (ifBlank i p q).law s = if s i = [] then p.law s else q.law s := by
  simp only [law, denote]; split_ifs <;> rfl

/-! ### Pieces -/

/-- Do nothing. -/
def nopX : XProg 7 := prog (.prim (.copy 2 2))

theorem law_nopX (s : Store 7) : nopX.law s = PMF.pure s := by
  rw [nopX, law_prim]; simp [Prim.apply]

/-- `n` copies of `p`, unrolled. -/
def repX (p : XProg 7) : ℕ → XProg 7
  | 0 => nopX
  | n + 1 => seq p (repX p n)

theorem AppendLaw.repX {p : XProg 7} {r : Fin 7} {P : Store 7 → Prop} {μ : PMF (List Bool)}
    (hp : AppendLaw p r P μ) (hP : ∀ s w, P s → P (Function.update s r w)) :
    ∀ n, AppendLaw (Prog.repX p n) r P (catPow μ n)
  | 0 => fun s _ => by
    rw [Prog.repX, law_nopX, catPow_zero, PMF.pure_map, List.append_nil, Function.update_eq_self]
  | n + 1 => by
    have h := AppendLaw.seq hp (AppendLaw.repX hp hP n) hP
    refine h.mono (fun _ h => h) ?_
    rw [catPow_succ', cat]

/-- Append a fixed word. -/
def wordAp (r : Fin 7) : List Bool → XProg 7
  | [] => nopX
  | b :: w => seq (bitAp r b) (wordAp r w)

theorem law_wordAp (r : Fin 7) : ∀ (w : List Bool) (s : Store 7),
    (wordAp r w).law s = PMF.pure (Function.update s r (s r ++ w))
  | [], s => by rw [wordAp, law_nopX, List.append_nil, Function.update_eq_self]
  | b :: w, s => by
    rw [wordAp, law_seq, bitAp, law_prim, PMF.pure_bind, law_wordAp r w]
    simp [Prim.apply]

/-- One coin of the first half: one more on the unary tape `3` if it is `1`. -/
def upStep : XProg 7 := seq (ifBit 2 (bitAp 3 true) nopX) (prog (.prim (.tail 2)))

/-- One coin of the second half: one fewer on the unary tape `3` if it is `1`. -/
def downStep : XProg 7 := seq (ifBit 2 (prog (.prim (.tail 3))) nopX) (prog (.prim (.tail 2)))

theorem law_upStep (s : Store 7) :
    upStep.law s = PMF.pure (Function.update (Function.update s 3
      (if (s 2).head? = some true then s 3 ++ [true] else s 3)) 2 (s 2).tail) := by
  rw [upStep, law_seq, law_ifBit]
  split_ifs with h
  · rw [bitAp, law_prim, PMF.pure_bind, law_prim]
    congr 1
  · rw [law_nopX, PMF.pure_bind, law_prim]
    congr 1
    simp [Prim.apply]

theorem law_downStep (s : Store 7) :
    downStep.law s = PMF.pure (Function.update (Function.update s 3
      (if (s 2).head? = some true then (s 3).tail else s 3)) 2 (s 2).tail) := by
  rw [downStep, law_seq, law_ifBit]
  split_ifs with h
  · rw [law_prim, PMF.pure_bind, law_prim]
    congr 1
  · rw [law_nopX, PMF.pure_bind, law_prim]
    congr 1
    simp [Prim.apply]

theorem law_repX_step {p : XProg 7} (F : Store 7 → Store 7)
    (hp : ∀ s, p.law s = PMF.pure (F s)) : ∀ (n : ℕ) (s : Store 7),
    (repX p n).law s = PMF.pure (F^[n] s)
  | 0, s => by rw [repX, law_nopX]; rfl
  | n + 1, s => by
    rw [repX, law_seq, hp, PMF.pure_bind, law_repX_step F hp n, Function.iterate_succ_apply]

theorem upStep_iter : ∀ (n : ℕ) (l : List Bool) (m : ℕ) (s : Store 7), s 2 = l →
    s 3 = List.replicate m true →
    (fun s : Store 7 => Function.update (Function.update s 3
      (if (s 2).head? = some true then s 3 ++ [true] else s 3)) 2 (s 2).tail)^[n] s =
      Function.update (Function.update s 2 (l.drop n)) 3
        (List.replicate (m + (l.take n).count true) true)
  | 0, l, m, s, h2, h3 => by
    funext t
    by_cases t2 : t = 2
    · subst t2; simp [h2]
    · by_cases t3 : t = 3
      · subst t3; simp [h3]
      · simp [t2, t3]
  | n + 1, l, m, s, h2, h3 => by
    rw [Function.iterate_succ_apply]
    rcases l with _ | ⟨b, l⟩
    · rw [upStep_iter n [] m _ (by simp [h2]) (by simp [h2, h3])]
      funext t
      by_cases t2 : t = 2
      · subst t2; simp
      · by_cases t3 : t = 3
        · subst t3; simp
        · simp [t2, t3]
    · rw [upStep_iter n l (m + if b then 1 else 0) _ (by simp [h2])
        (by cases b <;> simp [h2, h3, List.replicate_succ'])]
      funext t
      by_cases t2 : t = 2
      · subst t2; simp
      · by_cases t3 : t = 3
        · subst t3; cases b <;> simp [List.count_cons] <;> omega
        · simp [t2, t3]

theorem downStep_iter : ∀ (n : ℕ) (l : List Bool) (m : ℕ) (s : Store 7), s 2 = l →
    s 3 = List.replicate m true →
    (fun s : Store 7 => Function.update (Function.update s 3
      (if (s 2).head? = some true then (s 3).tail else s 3)) 2 (s 2).tail)^[n] s =
      Function.update (Function.update s 2 (l.drop n)) 3
        (List.replicate (m - (l.take n).count true) true)
  | 0, l, m, s, h2, h3 => by
    funext t
    by_cases t2 : t = 2
    · subst t2; simp [h2]
    · by_cases t3 : t = 3
      · subst t3; simp [h3]
      · simp [t2, t3]
  | n + 1, l, m, s, h2, h3 => by
    rw [Function.iterate_succ_apply]
    rcases l with _ | ⟨b, l⟩
    · rw [downStep_iter n [] m _ (by simp [h2]) (by simp [h2, h3])]
      funext t
      by_cases t2 : t = 2
      · subst t2; simp
      · by_cases t3 : t = 3
        · subst t3; simp
        · simp [t2, t3]
    · rw [downStep_iter n l (m - if b then 1 else 0) _ (by simp [h2])
        (by cases b <;> simp [h2, h3, List.tail_replicate])]
      funext t
      by_cases t2 : t = 2
      · subst t2; simp
      · by_cases t3 : t = 3
        · subst t3; cases b <;> simp [List.count_cons] <;> omega
        · simp [t2, t3]

theorem law_upSteps (n : ℕ) (l : List Bool) (m : ℕ) (s : Store 7) (h2 : s 2 = l)
    (h3 : s 3 = List.replicate m true) :
    (repX upStep n).law s = PMF.pure (Function.update (Function.update s 2 (l.drop n)) 3
      (List.replicate (m + (l.take n).count true) true)) := by
  rw [law_repX_step _ law_upStep, upStep_iter n l m s h2 h3]

theorem law_downSteps (n : ℕ) (l : List Bool) (m : ℕ) (s : Store 7) (h2 : s 2 = l)
    (h3 : s 3 = List.replicate m true) :
    (repX downStep n).law s = PMF.pure (Function.update (Function.update s 2 (l.drop n)) 3
      (List.replicate (m - (l.take n).count true) true)) := by
  rw [law_repX_step _ law_downStep, downStep_iter n l m s h2 h3]

/-- The leaf `v`: append the `L` low bits of `v`, then `K − L` copies of its sign. -/
def leafP (K L : ℕ) (v : ℤ) : XProg 7 :=
  seq (prog (.prim (.clear 3))) (seq (wordAp 0 ((zmodEnc L).enc (v : ZMod (2 ^ L))))
    (withCount 3 4 (K - L) (forN 4 3 (bitAp 0 (decide (v < 0))))))

/-- The word appended at the leaf `v`. -/
def leafW (K L : ℕ) (v : ℤ) : List Bool :=
  (zmodEnc L).enc (v : ZMod (2 ^ L)) ++ List.replicate (K - L) (decide (v < 0))

theorem law_leafP (K L : ℕ) (v : ℤ) (s : Store 7) (h4 : s 4 = []) :
    (leafP K L v).law s =
      PMF.pure (Function.update (Function.update s 3 []) 0 (s 0 ++ leafW K L v)) := by
  have hb := AppendLaw.withCount (k := 7) (r := 0) (t := 3) (c := 4) (P := fun _ => True)
    (n := K - L)
    (appendLaw_bits (k := 7) (r := 0) (c := 4) (t := 3) (by decide) (decide (v < 0)) (K - L)
      (fun _ => True) (fun _ _ _ => trivial) (fun _ _ _ => trivial))
    (fun _ _ _ => trivial) (by decide) (by decide)
  rw [leafP, law_seq, law_prim, PMF.pure_bind, law_seq, law_wordAp, PMF.pure_bind]
  rw [hb _ ⟨trivial, by simp [Prim.apply], by simp [Prim.apply, h4]⟩, PMF.pure_map]
  congr 1
  funext t
  by_cases t0 : t = 0
  · subst t0; simp [Prim.apply, leafW, List.append_assoc]
  · by_cases t3 : t = 3
    · subst t3; simp [Prim.apply]
    · simp [Prim.apply, t0, t3]

/-- The chain of tests reading the unary value `j` on tape `3` (with `f` tests left). -/
def chainP (K L η : ℕ) : ℕ → ℕ → XProg 7
  | 0, j => leafP K L ((j : ℤ) - η)
  | f + 1, j => ifBlank 3 (leafP K L ((j : ℤ) - η)) (seq (prog (.prim (.tail 3))) (chainP K L η f (j + 1)))

theorem law_chainP (K L η : ℕ) : ∀ (f j m : ℕ) (s : Store 7), m ≤ f → s 3 = List.replicate m true →
    s 4 = [] → (chainP K L η f j).law s =
      PMF.pure (Function.update (Function.update s 3 []) 0 (s 0 ++ leafW K L ((j + m : ℕ) - η)))
  | 0, j, m, s, hm, h3, h4 => by
    obtain rfl : m = 0 := by omega
    rw [chainP, law_leafP K L _ s h4]; simp
  | f + 1, j, m, s, hm, h3, h4 => by
    rw [chainP, law_ifBlank]
    rcases m with _ | m
    · rw [if_pos (by simp [h3]), law_leafP K L _ s h4]; simp
    · rw [if_neg (by simp [h3]), law_seq, law_prim, PMF.pure_bind,
        law_chainP K L η f (j + 1) m _ (by omega) (by simp [Prim.apply, h3])
          (by simp [Prim.apply, h4])]
      congr 1
      funext t
      by_cases t0 : t = 0
      · subst t0; simp [Prim.apply, Nat.add_right_comm j 1 m, Nat.add_assoc]
      · by_cases t3 : t = 3
        · subst t3; simp [Prim.apply]
        · simp [Prim.apply, t0, t3]

/-! ### The sampler -/

/-- **The centered binomial sampler** of width `η`, the low part on `L` bits. -/
def cbdP (η L K : ℕ) : XProg 7 :=
  seq (repX (coinAp 2 4) (η + η)) (seq (repX (bitAp 3 true) η) (seq (repX upStep η)
    (seq (repX downStep η) (chainP K L η (η + η) 0))))

/-- The word appended for the coins `l`. -/
def cbdW (η L K : ℕ) (l : List Bool) : List Bool :=
  leafW K L (((η + (l.take η).count true - (l.drop η).count true : ℕ) : ℤ) - η)

theorem law_cbdP_det (η L K : ℕ) (s : Store 7) (l : List Bool) (hl : l.length = η + η)
    (h2 : s 2 = l) (h3 : s 3 = []) (h4 : s 4 = []) :
    (seq (repX (bitAp 3 true) η) (seq (repX upStep η)
      (seq (repX downStep η) (chainP K L η (η + η) 0)))).law s =
      PMF.pure (Function.update (Function.update s 2 []) 0 (s 0 ++ cbdW η L K l)) := by
  have hb := AppendLaw.repX (appendLaw_bitAp (k := 7) 3 true (fun _ => True)) (fun _ _ _ => trivial) η
  have hcat : catPow (PMF.pure [true]) η = PMF.pure (List.replicate η true) := by
    clear hb hl; induction η with
    | zero => rfl
    | succ m ih => rw [catPow_succ, ih, PMF.pure_bind, PMF.pure_map, List.replicate_succ']
  rw [law_seq, hb s trivial, hcat, PMF.pure_map, PMF.pure_bind, law_seq,
    law_upSteps η l η _ (by simp [h2]) (by simp [h3]), PMF.pure_bind, law_seq,
    law_downSteps η (l.drop η) (η + (l.take η).count true) _ (by simp) (by simp), PMF.pure_bind]
  have hb2 : (l.drop η).take η = l.drop η := List.take_of_length_le (by simp [hl])
  have hdd : (l.drop η).drop η = [] := List.drop_eq_nil_of_le (by simp [hl])
  have hc : ((l.drop η).count true) ≤ η := by
    have := List.count_le_length (a := true) (l := l.drop η); simp [hl] at this; omega
  have ha : ((l.take η).count true) ≤ η := by
    have := List.count_le_length (a := true) (l := l.take η); simp [hl] at this; omega
  rw [law_chainP K L η (η + η) 0 (η + (l.take η).count true - (l.drop η).count true) _
    (by omega) (by simp [hb2]) (by simp [h4])]
  congr 1
  funext t
  by_cases t0 : t = 0
  · subst t0; simp [cbdW, hb2]
  · by_cases t2 : t = 2
    · subst t2; simp [hdd]
    · by_cases t3 : t = 3
      · subst t3; simp [h3]
      · simp [t0, t2, t3]

/-- The coins of the sampler give the centered binomial residue. -/
theorem uniformList_cbd (η K : ℕ) :
    (BitString.uniformList (η + η)).map (fun l =>
      ((((η + (l.take η).count true - (l.drop η).count true : ℕ) : ℤ) - η : ℤ) : ZMod (2 ^ K))) =
      ModuleLWE.coeffLaw (2 ^ K) (.cbd η) := by
  let e : (Fin (η + η) → Bool) ≃ (Fin η → Bool) × (Fin η → Bool) :=
    (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
      (Equiv.sumArrowEquivProdArrow _ _ _)
  rw [ModuleLWE.coeffLaw, ← Cslib.Probability.PMF.uniformOfFintype_map_equiv e, PMF.map_comp,
    BitString.uniformList, PMF.map_comp]
  congr 1
  funext f
  have hcount : ∀ {n : ℕ} (g : Fin n → Bool),
      (List.ofFn g).count true = (Finset.univ.filter fun i => g i = true).card := by
    intro n g
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.ofFn_succ, List.count_cons, ih, Finset.card_filter, Finset.card_filter,
        Fin.sum_univ_succ]
      cases g 0 <;> simp [Nat.add_comm]
  have hsplit := List.ofFn_add (f := f)
  have hlen1 : (List.ofFn fun i : Fin η => f (Fin.castAdd η i)).length = η := List.length_ofFn
  have htake : (List.ofFn f).take η = List.ofFn fun i : Fin η => f (Fin.castAdd η i) := by
    rw [hsplit]; exact List.take_left' hlen1
  have hdrop : (List.ofFn f).drop η = List.ofFn fun i : Fin η => f (Fin.natAdd η i) := by
    rw [hsplit]; exact List.drop_left' hlen1
  have hc2 : ((List.ofFn f).drop η).count true ≤ η := by
    have := List.count_le_length (a := true) (l := (List.ofFn f).drop η); simpa using this
  simp only [Function.comp_apply]
  rw [Nat.cast_sub (by omega), Nat.cast_add, htake, hdrop, hcount, hcount]
  simp only [e, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.sumArrowEquivProdArrow_apply_fst,
    Equiv.sumArrowEquivProdArrow_apply_snd, Function.comp_apply, Equiv.refl_apply,
    Equiv.symm_symm, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  push_cast
  ring

theorem cbdW_eq (η L K : ℕ) (hL : 1 ≤ L) (hLK : L ≤ K) (hη : η < 2 ^ (L - 1)) (l : List Bool) :
    cbdW η L K l = (zmodEnc K).enc
      ((((η + (l.take η).count true - (l.drop η).count true : ℕ) : ℤ) - η : ℤ) : ZMod (2 ^ K)) := by
  have ha : (l.take η).count true ≤ η :=
    (List.count_le_length (a := true) (l := l.take η)).trans (by simp)
  have hη' : (η : ℤ) < 2 ^ (L - 1) := by exact_mod_cast hη
  rw [cbdW, leafW, zmodEnc_small hL hLK]
  · push_cast; omega
  · omega

/-- **The law of the centered binomial sampler.** -/
theorem law_cbdP (η L K : ℕ) (hL : 1 ≤ L) (hLK : L ≤ K) (hη : η < 2 ^ (L - 1)) :
    AppendLaw (cbdP η L K) 0 P3 ((ModuleLWE.coeffLaw (2 ^ K) (.cbd η)).map (zmodEnc K).enc) := by
  rintro s ⟨h2, h3, h4⟩
  have hc := AppendLaw.repX (appendLaw_coinAp (k := 7) (r := 2) (b := 4) (by decide))
    (fun s w hs => by rwa [Function.update_of_ne (by decide)]) (η + η)
  rw [catPow_uniformList, Nat.mul_one] at hc
  rw [cbdP, law_seq, hc s h4, PMF.bind_map]
  have hdet : ∀ u ∈ (BitString.uniformList (η + η)).support,
      ((seq (repX (bitAp 3 true) η) (seq (repX upStep η)
        (seq (repX downStep η) (chainP K L η (η + η) 0)))).law ∘
        fun u => Function.update s 2 (s 2 ++ u)) u =
      PMF.pure (Function.update s 0 (s 0 ++ cbdW η L K u)) := by
    intro u hu
    simp only [Function.comp_apply]
    rw [law_cbdP_det η L K _ u (BitString.length_of_mem_support_uniformList hu) (by simp [h2])
      (by simp [h3]) (by simp [h4])]
    congr 1
    funext t
    by_cases t0 : t = 0
    · subst t0; simp
    · by_cases t2 : t = 2
      · subst t2; simp [h2]
      · simp [t0, t2]
  rw [PMF.bind_congr_on_support _ _ _ hdet,
    show ((BitString.uniformList (η + η)).bind fun a =>
        PMF.pure (Function.update s 0 (s 0 ++ cbdW η L K a))) =
      (BitString.uniformList (η + η)).map (fun a => Function.update s 0 (s 0 ++ cbdW η L K a))
      from PMF.bind_pure_comp _ _, ← uniformList_cbd η K, PMF.map_comp, PMF.map_comp]
  congr 1
  funext u
  simp only [Function.comp_apply]
  rw [cbdW_eq η L K hL hLK hη u]

/-! ### Well-formedness and frame -/

theorem wf_nopX : nopX.WF := trivial

theorem preserves_prim {p : Prim 7} {i : Fin 7} (h : i ∉ p.writes) : (prog (.prim p)).Preserves i := h

theorem preserves_nopX (i : Fin 7) (h : i ≠ 2) : nopX.Preserves i :=
  preserves_prim (by simp [Prim.writes, h])

theorem wf_repX {p : XProg 7} (hp : p.WF) : ∀ n, (repX p n).WF
  | 0 => wf_nopX
  | n + 1 => ⟨hp, wf_repX hp n⟩

theorem preserves_repX {p : XProg 7} {i : Fin 7} (hi : i ≠ 2) (hp : p.Preserves i) :
    ∀ n, (repX p n).Preserves i
  | 0 => preserves_nopX i hi
  | n + 1 => ⟨hp, preserves_repX hi hp n⟩

theorem wf_wordAp (r : Fin 7) : ∀ w, (wordAp r w).WF
  | [] => wf_nopX
  | b :: w => ⟨wf_bitAp r b, wf_wordAp r w⟩

theorem preserves_wordAp {r i : Fin 7} (hr : r ≠ i) (hi : i ≠ 2) : ∀ w, (wordAp r w).Preserves i
  | [] => preserves_nopX i hi
  | b :: w => ⟨preserves_bitAp b hr, preserves_wordAp hr hi w⟩

theorem wf_leafP (K L : ℕ) (v : ℤ) : (leafP K L v).WF :=
  ⟨trivial, wf_wordAp 0 _, wf_withCount (by decide) (wf_forN (wf_bitAp _ _)
    (preserves_bitAp _ (by decide)))⟩

/-- The tapes outside `0, 2, 3, 4`. -/
def Outside (i : Fin 7) : Prop := i ≠ 0 ∧ i ≠ 2 ∧ i ≠ 3 ∧ i ≠ 4

theorem preserves_leafP (K L : ℕ) (v : ℤ) {i : Fin 7} (hi : Outside i) :
    (leafP K L v).Preserves i := by
  obtain ⟨h0, h2, h3, h4⟩ := hi
  exact ⟨preserves_prim (by simp [Prim.writes, h3]),
    preserves_wordAp (Ne.symm h0) h2 _,
    preserves_withCount (Ne.symm h3) (Ne.symm h4) ⟨preserves_prim (by simp [Prim.writes, h4]),
      Ne.symm h4, preserves_bitAp _ (Ne.symm h0)⟩⟩

theorem wf_chainP (K L η : ℕ) : ∀ f j, (chainP K L η f j).WF
  | 0, j => wf_leafP K L _
  | f + 1, j => ⟨wf_leafP K L _, trivial, wf_chainP K L η f (j + 1)⟩

theorem preserves_chainP (K L η : ℕ) {i : Fin 7} (hi : Outside i) : ∀ f j, (chainP K L η f j).Preserves i
  | 0, j => preserves_leafP K L _ hi
  | f + 1, j => ⟨preserves_leafP K L _ hi, preserves_prim (by simp [Prim.writes, hi.2.2.1]),
    preserves_chainP K L η hi f (j + 1)⟩

theorem wf_upStep : upStep.WF := ⟨⟨wf_bitAp 3 true, wf_nopX⟩, trivial⟩

theorem wf_downStep : downStep.WF := ⟨⟨trivial, wf_nopX⟩, trivial⟩

theorem wf_cbdP (η L K : ℕ) : (cbdP η L K).WF :=
  ⟨wf_repX (wf_coinAp 2 4) _, wf_repX (wf_bitAp 3 true) _, wf_repX wf_upStep _,
    wf_repX wf_downStep _, wf_chainP K L η _ _⟩

/-- **The sampler writes only the tapes `0, 2, 3, 4`.** -/
theorem preserves_cbdP (η L K : ℕ) {i : Fin 7} (hi : Outside i) : (cbdP η L K).Preserves i := by
  obtain ⟨h0, h2, h3, h4⟩ := hi
  have tl : ∀ j : Fin 7, i ≠ j → (prog (.prim (.tail j)) : XProg 7).Preserves i := fun j hj =>
    preserves_prim (by simp [Prim.writes, hj])
  have hu : upStep.Preserves i :=
    ⟨⟨preserves_bitAp _ (Ne.symm h3), preserves_nopX i h2⟩, tl 2 h2⟩
  have hd : downStep.Preserves i := ⟨⟨tl 3 h3, preserves_nopX i h2⟩, tl 2 h2⟩
  exact ⟨preserves_repX h2 (preserves_coinAp (Ne.symm h2) (Ne.symm h4)) _,
    preserves_repX h2 (preserves_bitAp _ (Ne.symm h3)) _,
    preserves_repX h2 hu _, preserves_repX h2 hd _,
    preserves_chainP K L η ⟨h0, h2, h3, h4⟩ _ _⟩

/-! ### The concrete configuration -/

/-- **The χ sampler of `confP`**: centered binomial of width `16`, low part on `6` bits. -/
def chiP : XProg 7 := cbdP 16 6 Params.Kp

theorem six_le_Kp : 6 ≤ Params.Kp := by rw [Params.Kp_def]; norm_num

/-- **The χ sampler of `confP` has the law of `law_setup3P` / `law_setupIP`.** -/
theorem law_chiP : AppendLaw chiP 0 P3 (μχ Params.confP) :=
  law_cbdP 16 6 Params.Kp (by norm_num) six_le_Kp (by norm_num)

theorem wf_chiP : chiP.WF := wf_cbdP _ _ _

theorem preserves_chiP {i : Fin 7} (hi : Outside i) : chiP.Preserves i := preserves_cbdP _ _ _ hi

theorem preserves6_chiP : chiP.Preserves 6 :=
  preserves_chiP ⟨by decide, by decide, by decide, by decide⟩

theorem dp_ne : NeZero Params.confP.d := ⟨by show Params.dp ≠ 0; rw [Params.dp_def]; positivity⟩

theorem Kp_pos : 0 < Params.Kp := by rw [Params.Kp_def]; positivity

/-- **The setup of hybrid 3 for `confP`**, with the sampler `chiP`. -/
theorem law_setup3P_conf (ab : Inst3T Params.Np Params.Kp Params.kp) (x : PUniv.Attr) :
    (setup3P Params.hkp Params.confP chiP).law (ioS (R := 5)
      ((inst3Enc (N := Params.Np) (K := Params.Kp) (k := Params.kp)).enc ab) (AdvancedEncryption.PE.BranchingProgram.encAttr x) []) =
      (setup3 Params.hkp Params.confP x).map fun σ => ioS (R := 5)
        (((inst3Enc (N := Params.Np) (K := Params.Kp) (k := Params.kp)).prod
          (sec3Enc Params.hkp Params.confP)).enc (ab, σ)) [] [] :=
  haveI := dp_ne
  law_setup3P Params.hkp Params.confP chiP law_chiP Params.Np_pos Kp_pos ab x

/-- **The setup of the ideal side for `confP`**, with the sampler `chiP`. -/
theorem law_setupIP_conf (ab : Inst3T Params.Np Params.Kp Params.kp) (x : PUniv.Attr) :
    (setupIP Params.hkp Params.confP chiP).law (ioS (R := 5)
      ((inst3Enc (N := Params.Np) (K := Params.Kp) (k := Params.kp)).enc ab) (AdvancedEncryption.PE.BranchingProgram.encAttr x) []) =
      (setupI Params.hkp Params.confP x).map fun σ => ioS (R := 5)
        (((inst3Enc (N := Params.Np) (K := Params.Kp) (k := Params.kp)).prod
          (secIEnc Params.hkp Params.confP)).enc (ab, σ)) [] [] :=
  haveI := dp_ne
  law_setupIP Params.hkp Params.confP chiP law_chiP Params.Np_pos Kp_pos ab x

theorem wf_setup3P_conf : (setup3P Params.hkp Params.confP chiP).WF :=
  wf_setup3P Params.hkp Params.confP chiP wf_chiP preserves6_chiP

theorem wf_setupIP_conf : (setupIP Params.hkp Params.confP chiP).WF :=
  wf_setupIP Params.hkp Params.confP chiP wf_chiP preserves6_chiP

end AdvancedEncryption.DualUse.Prog
