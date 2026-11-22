import PE.Impl.DualUse.Prog.Chi

/-!
# The challenge component of the reduction of the ideal side

On the ideal side the challenge `ct` is part of the secret (`SecI`, the simulator's uniform
ciphertext, last field of `secIEnc`), so the challenge component only has to

1. drop the prefix of the packed secret `(ab, σ)` before the word of `ct` (`dropF`);
2. for the message `μ = true`, add `half = 2^{K−1}` to `κ`. In the codec (`ringEnc`, least
   significant bit first) this flips one bit: the top bit `K − 1` of the constant coefficient of
   `κ` (`zmodEnc_add_half`, `ringEnc_add_half`), at the offset `Pκ + K − 1` of the word of `ct`
   (`ctEnc_shift`). The flip moves the first `P` bits to a scratch tape, flips the head, and moves
   them back (`flipP`).

**`law_chalIP`**: on `((inst3Enc).prod (secIEnc)).enc (ab, σ)` and `encMsg μ`, the output is
`(ctEnc hk c).enc (shiftCT hk c μ (viewI hk c ab σ).2)` alone on tape `0` (the `law_chal` field of
the handlers' components for the packed secret). `wf_chalIP`.

Tapes (`XProg 7`): `0` the word, `1` the message, `2` the moved prefix, `3`, `4` a counter and its
scratch.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.XProg Matrix
  AdvancedEncryption.RingBTVW Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow

/-! ### Flipping one bit of a word -/

/-- Flip the bit at position `P`. -/
def flipAt (P : ℕ) (w : List Bool) : List Bool := w.mapIdx fun i b => if i = P then !b else b

theorem length_flipAt (P : ℕ) (w : List Bool) : (flipAt P w).length = w.length := by
  simp [flipAt]

theorem flipAt_append_left {P : ℕ} {u : List Bool} (v : List Bool) (h : P < u.length) :
    flipAt P (u ++ v) = flipAt P u ++ v := by
  unfold flipAt
  rw [List.mapIdx_append]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_mapIdx]
  rw [if_neg (by omega)]

theorem flipAt_append_right (u v : List Bool) (P : ℕ) :
    flipAt (u.length + P) (u ++ v) = u ++ flipAt P v := by
  unfold flipAt
  rw [List.mapIdx_append]
  congr 1
  · apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_mapIdx]
    rw [if_neg (by simp at h1; omega)]
  · apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_mapIdx]
    congr 1
    simp only [eq_iff_iff]
    omega

theorem flipAt_zero_cons (b : Bool) (w : List Bool) : flipAt 0 (b :: w) = (!b) :: w := by
  have := flipAt_append_left (P := 0) (u := [b]) w (by simp)
  rw [List.singleton_append] at this
  rw [this]; simp [flipAt]

/-! ### Adding `half` flips a bit -/

/-- `2^{K−1}` added mod `2^K` flips the top bit. -/
theorem zmodEnc_add_half {K : ℕ} (hK : 1 ≤ K) (a : ZMod (2 ^ K)) :
    (zmodEnc K).enc (a + ((2 ^ K / 2 : ℕ) : ZMod (2 ^ K))) = flipAt (K - 1) ((zmodEnc K).enc a) := by
  have hpow : 2 ^ K / 2 = 2 ^ (K - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
    simp [pow_succ]
  have hlt : 2 ^ (K - 1) < 2 ^ K := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hval : (a + ((2 ^ K / 2 : ℕ) : ZMod (2 ^ K))).val = (2 ^ (K - 1) + a.val) % 2 ^ K := by
    rw [ZMod.val_add, ZMod.val_natCast, hpow, Nat.mod_eq_of_lt hlt, Nat.add_comm]
  apply List.ext_getElem (by simp [length_flipAt, (zmodEnc K).length])
  intro i h1 h2
  have hi : i < K := by simpa [(zmodEnc K).length] using h1
  simp only [flipAt, zmodEnc, List.getElem_mapIdx, List.getElem_map, List.getElem_finRange,
    Fin.val_cast, hval, Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]
  rcases lt_or_eq_of_le (show i ≤ K - 1 by omega) with h | h
  · rw [if_neg (by omega), Nat.testBit_two_pow_add_gt h]
  · subst h
    rw [if_pos rfl, Nat.testBit_two_pow_add_eq]

theorem half_eq {N K : ℕ} (hk : 2 ^ K < 2 ^ k) :
    (Sdw (N := N) hk).half = algebraMap (ZMod (2 ^ K)) _ ((2 ^ K / 2 : ℕ) : ZMod (2 ^ K)) := by
  show algebraMap _ _ (encodeBit (2 ^ K) true) = _
  rfl

/-- **Adding `half` to a ring element flips the top bit of its constant coefficient.** -/
theorem ringEnc_add_half {N K : ℕ} (hk : 2 ^ K < 2 ^ k) (hN : 0 < N) (hK : 1 ≤ K)
    (r : Rg N K) :
    (ringEnc N K).enc (r + (Sdw (N := N) hk).half) = flipAt (K - 1) ((ringEnc N K).enc r) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [ringEnc_flatMap', ringEnc_flatMap', half_eq, List.finRange_succ, List.map_cons,
    List.map_cons, List.flatMap_cons, List.flatMap_cons,
    flipAt_append_left _ (by rw [(zmodEnc K).length]; omega)]
  congr 1
  · simp only [Cslib.Negacyclic.coeffs_add, Pi.add_apply, Cslib.Negacyclic.coeffs_algebraMap,
      Fin.val_zero, if_true]
    exact zmodEnc_add_half hK _
  · congr 1
    simp only [List.map_map]
    congr 1
    funext i
    simp [Cslib.Negacyclic.coeffs_add, Cslib.Negacyclic.coeffs_algebraMap]

/-! ### Shifted challenges -/

/-- The length of an encoding. -/
def encLen {α : Type} {n : ℕ} (_ : FixedEnc α n) : ℕ := n

theorem length_enc {α : Type} {n : ℕ} (e : FixedEnc α n) (a : α) : (e.enc a).length = encLen e :=
  e.length a

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The offset of `κ` in the word of a ciphertext. -/
def offK : ℕ :=
  encLen (FixedEnc.fun (α := (Sdw (N := N) hk).Attr) (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))) +
    (encLen (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)) + (encLen (matEnc (N := N) (K := K) (Fin 1)
      (TrapCol k)) + encLen (FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
        (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)))))

/-- **The challenge for `μ`** is the challenge for `0` with one bit flipped if `μ = true`. -/
theorem ctEnc_shift (hN : 0 < N) (hK : 1 ≤ K) (μ : Bool) (ct : CT hk c) :
    (ctEnc hk c).enc (shiftCT hk c μ ct) =
      if μ then flipAt (offK hk c + (K - 1)) ((ctEnc hk c).enc ct) else (ctEnc hk c).enc ct := by
  cases μ
  · simp [shiftCT]
  · simp only [if_true]
    show _ ++ (_ ++ (_ ++ (_ ++ (ringEnc N K).enc (ct.κ + (Sdw (N := N) hk).half)))) =
      flipAt _ ((FixedEnc.fun (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).enc ct.Ψ ++
        ((matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc ct.c₀ ++
        ((matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc ct.c₁ ++
        ((FixedEnc.fun (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k))).enc ct.cj ++
          (ringEnc N K).enc ct.κ))))
    rw [ringEnc_add_half hk hN hK, offK, ← length_enc _ ct.Ψ, ← length_enc _ ct.c₀,
      ← length_enc _ ct.c₁, ← length_enc _ ct.cj, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc,
      flipAt_append_right, flipAt_append_right, flipAt_append_right, flipAt_append_right]
    rfl

/-! ### Deterministic loops -/

theorem law_forN_det {σ : Type} {c t : Fin 7} (body : XProg 7) (G : σ → Store 7) (f : σ → σ)
    (hG : ∀ a, G a c = [])
    (hb : ∀ a w, body.law (Function.update (G a) c w) = PMF.pure (Function.update (G (f a)) c w))
    (a : σ) : (forN c t body).law (G a) = PMF.pure (G (f^[(G a t).length] a)) := by
  rw [forN, law_seq, law_prim, PMF.pure_bind]
  simp only [Prim.apply]
  rw [law_loop_iter c body G (fun a => PMF.pure (f a)) (fun a w => by rw [hb, PMF.pure_map]) a,
    kIter_pure, PMF.pure_map, Function.update_eq_self_iff.mpr (hG _).symm]

theorem tail_iterate : ∀ (n : ℕ) (w : List Bool), List.tail^[n] w = w.drop n
  | 0, w => rfl
  | n + 1, w => by rw [Function.iterate_succ_apply, tail_iterate n, List.drop_tail]

theorem mvStepA_iterate : ∀ (n : ℕ) (o sv : List Bool),
    mvStepA^[n] (o, sv) = (o ++ sv.take n, sv.drop n)
  | 0, o, sv => by simp
  | n + 1, o, sv => by
    rw [Function.iterate_succ_apply]
    cases sv <;> simp [mvStepA, mvStepA_iterate n]

/-! ### The pieces -/

/-- Drop the first `D` bits of tape `0`. -/
def dropF (D : ℕ) : XProg 7 := withCount 3 4 D (forN 4 3 (prog (.prim (.tail 0))))

theorem law_dropF (D : ℕ) (s : Store 7) (h3 : s 3 = []) (h4 : s 4 = []) :
    (dropF D).law s = PMF.pure (Function.update s 0 ((s 0).drop D)) := by
  rw [dropF, withCount, law_seq, law_natP (by decide) D s h4, PMF.pure_bind, law_seq]
  set s1 := Function.update s 3 (List.replicate D false)
  have h := law_forN_det (c := 4) (t := 3) (prog (.prim (.tail 0)))
    (fun a => Function.update s1 0 a) List.tail (fun a => by simp [s1, h4])
    (fun a w => by
      rw [law_prim]; congr 1
      simp only [Prim.apply, Function.update_of_ne (show (0 : Fin 7) ≠ 4 by decide),
        Function.update_self]
      rw [Function.update_comm (show (4 : Fin 7) ≠ 0 by decide), Function.update_idem])
    (s 0)
  have he : Function.update s1 0 (s 0) = s1 := by
    rw [show s 0 = s1 0 by simp [s1]]; exact Function.update_eq_self _ _
  simp only [he] at h
  rw [h, PMF.pure_bind, law_prim]
  congr 1
  simp only [Prim.apply, s1, tail_iterate]
  funext t
  by_cases t0 : t = 0
  · subst t0; simp
  · by_cases t3 : t = 3
    · subst t3; simp [h3]
    · simp [t0, t3]

/-- Flip the head of tape `0`. -/
def flipHead : XProg 7 :=
  ifBit 0 (seq (prog (.prim (.tail 0))) (prog (.prim (.cons 0 false))))
    (seq (prog (.prim (.tail 0))) (prog (.prim (.cons 0 true))))

theorem law_flipHead (s : Store 7) (b : Bool) (w : List Bool) (h0 : s 0 = b :: w) :
    flipHead.law s = PMF.pure (Function.update s 0 ((!b) :: w)) := by
  rw [flipHead, law_ifBit, h0]
  cases b <;> simp [law_seq, law_prim, Prim.apply, h0]

/-- Flip the bit `P` of tape `0` (scratch `2`, `3`, `4`). -/
def flipP (P : ℕ) : XProg 7 :=
  seq (withCount 3 4 P (forN 4 3 (seq (prog (.prim (.snocHead 2 0))) (prog (.prim (.tail 0))))))
    (seq flipHead (seq (appendTapeP 2 0 3 4) (seq (prog (.prim (.copy 0 2)))
      (prog (.prim (.clear 2))))))

theorem law_flipP (P : ℕ) (s : Store 7) (h2 : s 2 = []) (h3 : s 3 = []) (h4 : s 4 = [])
    (hP : P < (s 0).length) :
    (flipP P).law s = PMF.pure (Function.update s 0 (flipAt P (s 0))) := by
  rw [flipP, withCount, law_seq, law_seq, law_natP (by decide) P s h4, PMF.pure_bind, law_seq]
  set s1 := Function.update s 3 (List.replicate P false)
  have h := law_forN_det (c := 4) (t := 3) (seq (prog (.prim (.snocHead 2 0))) (prog (.prim (.tail 0))))
    (fun a => Function.update (Function.update s1 2 a.1) 0 a.2) mvStepA (fun a => by simp [s1, h4])
    (fun a w => by
      rw [law_seq, law_prim, PMF.pure_bind, law_prim]; congr 1
      obtain ⟨x, y⟩ := a
      funext t
      simp only [Prim.apply, mvStepA, Function.update_apply]
      by_cases t0 : t = 0 <;> by_cases t2 : t = 2 <;> by_cases t4 : t = 4 <;> simp_all)
    ([], s 0)
  simp only at h
  have he : Function.update (Function.update s1 2 []) 0 (s 0) = s1 := by
    funext t
    by_cases t0 : t = 0
    · subst t0; simp [s1]
    · by_cases t2 : t = 2
      · subst t2; simp [s1, h2]
      · simp [t0, t2]
  rw [he] at h
  rw [h, PMF.pure_bind, law_prim, PMF.pure_bind]
  simp only [s1, Function.update_self, List.length_replicate, mvStepA_iterate, List.nil_append]
  obtain ⟨b, rest, hbr⟩ : ∃ b rest, (s 0).drop P = b :: rest := by
    cases h' : (s 0).drop P with
    | nil => simp at h'; omega
    | cons b rest => exact ⟨b, rest, rfl⟩
  rw [law_seq, law_flipHead _ b rest (by simp [Prim.apply, hbr]), PMF.pure_bind, law_seq,
    law_appendTapeP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) _
      (by simp [Prim.apply]) (by simp [Prim.apply, h4]),
    PMF.pure_bind, law_seq, law_prim, PMF.pure_bind, law_prim]
  congr 1
  have hfl : flipAt P (s 0) = (s 0).take P ++ (!b) :: rest := by
    have h1 := flipAt_append_right ((s 0).take P) ((s 0).drop P) 0
    rw [List.take_append_drop, Nat.add_zero, List.length_take, min_eq_left hP.le, hbr,
      flipAt_zero_cons] at h1
    exact h1
  funext t
  by_cases t0 : t = 0
  · subst t0; simp [Prim.apply, hfl]
  · by_cases t2 : t = 2
    · subst t2; simp [Prim.apply, h2]
    · by_cases t3 : t = 3
      · subst t3; simp [Prim.apply, h3]
      · simp [Prim.apply, t0, t2, t3]

/-- **The challenge from the packed secret** (`D` the prefix before the challenge, `P` the bit
of `half`). -/
def chalBodyP (D P : ℕ) : XProg 7 :=
  seq (dropF D) (seq (ifBit 1 (flipP P) nopX) (prog (.prim (.clear 1))))

theorem law_chalBodyP (D P : ℕ) (pre w : List Bool) (hpre : pre.length = D) (hP : P < w.length)
    (μ : Bool) :
    (chalBodyP D P).law (ioS (R := 5) (pre ++ w) (encMsg μ) []) =
      PMF.pure (ioS (R := 5) (if μ then flipAt P w else w) [] []) := by
  rw [chalBodyP, law_seq, law_dropF D _ rfl rfl, PMF.pure_bind, law_seq, law_ifBit]
  have hw : (ioS (R := 5) (pre ++ w) (encMsg μ) [] 0).drop D = w := by
    simp [ioS, ← hpre]
  have hd : (pre ++ w).drop D = w := by rw [← hpre, List.drop_left]
  have hm : ∀ b, encMsg b = [b] := fun _ => rfl
  cases μ
  · rw [if_neg (by simp [ioS, hm]), law_nopX, PMF.pure_bind, law_prim]
    congr 1
    funext t
    fin_cases t <;> simp [ioS, Prim.apply, hd]
  · rw [if_pos (by simp [ioS, hm]), law_flipP P _ (by simp [ioS]) (by simp [ioS])
      (by simp [ioS]) (by simp [hw, hP]), PMF.pure_bind, law_prim]
    congr 1
    funext t
    fin_cases t <;> simp [ioS, Prim.apply, hd]

theorem wf_chalBodyP (D P : ℕ) : (chalBodyP D P).WF := by
  refine ⟨wf_withCount (by decide) (wf_forN trivial (preserves_prim (by simp [Prim.writes]))),
    ⟨⟨wf_withCount (by decide) (wf_forN ⟨trivial, trivial⟩
      ⟨preserves_prim (by simp [Prim.writes]), preserves_prim (by simp [Prim.writes])⟩),
      ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩, wf_appendTapeP (by decide) (by decide),
      trivial, trivial⟩, wf_nopX⟩, trivial⟩

/-! ### The component of the ideal side -/

/-- The prefix of the packed secret of the ideal side before the challenge. -/
def preI : ℕ :=
  encLen (inst3Enc (N := N) (K := K) (k := k)) + (10 + (encLen (matEnc (N := N) (K := K) (Fin 1)
    (Fin c.d)) + (encLen (wEnc hk c) + (N * K + encLen (coinsEnc hk c)))))

/-- **The challenge component of the ideal side.** -/
def chalIP : XProg 7 := chalBodyP (preI hk c) (offK hk c + (K - 1))

/-- **The law of the challenge component of the ideal side.** -/
theorem law_chalIP (hN : 0 < N) (hK : 1 ≤ K) (ab : Inst3T N K k) (σ : SecI hk c) (μ : Bool) :
    (chalIP hk c).law (ioS (R := 5)
      (((inst3Enc (N := N) (K := K) (k := k)).prod (secIEnc hk c)).enc (ab, σ)) (encMsg μ) []) =
      PMF.pure (ioS (R := 5) ((ctEnc hk c).enc (shiftCT hk c μ (viewI hk c ab σ).2)) [] []) := by
  have hw : ((inst3Enc (N := N) (K := K) (k := k)).prod (secIEnc hk c)).enc (ab, σ) =
      ((inst3Enc (N := N) (K := K) (k := k)).enc ab ++ (dateEnc.enc σ.1 ++
        ((matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc σ.2.1 ++ ((wEnc hk c).enc σ.2.2.1 ++
          ((ringEnc N K).enc σ.2.2.2.1 ++ (coinsEnc hk c).enc σ.2.2.2.2.1))))) ++
        (ctEnc hk c).enc σ.2.2.2.2.2 := by
    simp only [FixedEnc.prod, secIEnc, List.append_assoc]
  have hP : offK hk c + (K - 1) < ((ctEnc hk c).enc σ.2.2.2.2.2).length := by
    rw [(ctEnc hk c).length, offK]
    simp only [encLen]
    have : K - 1 < N * K := by
      have := Nat.mul_le_mul_right K (show 1 ≤ N from hN); omega
    omega
  rw [chalIP, hw, law_chalBodyP _ _ _ _ (by simp [preI, length_enc, (dateEnc).length, (ringEnc N K).length]) hP,
    ctEnc_shift hk c hN hK]
  rfl

theorem wf_chalIP : (chalIP hk c).WF := wf_chalBodyP _ _

end AdvancedEncryption.DualUse.Prog
