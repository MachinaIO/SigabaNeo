import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.VM
import SigabaNeo.Lib.Lattices.Homomorphic.BinaryDigits
import SigabaNeo.Lib.Lattices.Automorphism.Instance

/-!
# The Mersenne VM on canonical ring words

Reasoning tools for `MVM.Code` programs whose registers hold canonical words of ring elements of
`Rq N K = ℤ_{2^K − 1}[X]/(X^N + 1)`:

* **queues**: `encL l`, the concatenated canonical words of a list `l`; `mvR d s` moves the head of
  the queue `s` to the tail of the queue `d` (dropping the head of `d`): `shiftIn_encRM`,
  `takeD_encRM_append`, `drop_encRM_append`;
* **the operations on canonical words are the ring operations** (`canonW_add`, `canonW_sub`,
  `canonW_mul`, `canonW_neg`, `canonW_aut` (`σ_k = aut N k`), `canonW_rho` (`X^{−j}`),
  `canonW_rot` (`2^{K−j}`), `canonW_dig` (`binaryDigit`));
* **footprints**: `exec_writes`: a code leaves every register it does not write alone;
* **loops**: `exec_rep_inv`, a `rep` loop by an invariant indexed by the round.
-/

/-- The simp set of the register names of VM routines. -/
register_simp_attr vmreg

namespace SigabaNeo.Tape

namespace MVM

open SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG Prog Cslib

/-- The ring `ℤ_{2^K − 1}[X]/(X^N + 1)`. -/
abbrev Rq (N K : ℕ) := Negacyclic (ZMod (2 ^ K - 1)) N

variable {N K : ℕ}

/-! ### Queues of ring elements -/

/-- The concatenated canonical words of a list of ring elements. -/
def encL (N K : ℕ) (l : List (Rq N K)) : List Bool := l.flatMap (encRM N K)

@[simp] theorem encL_nil : encL N K [] = [] := rfl
@[simp] theorem encL_cons (x : Rq N K) (l : List (Rq N K)) :
    encL N K (x :: l) = encRM N K x ++ encL N K l := rfl
@[simp] theorem encL_append (l l' : List (Rq N K)) :
    encL N K (l ++ l') = encL N K l ++ encL N K l' := List.flatMap_append

theorem encL_singleton (x : Rq N K) : encL N K [x] = encRM N K x := by simp

@[simp] theorem length_encL (l : List (Rq N K)) : (encL N K l).length = l.length * (N * K) := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [encL_cons, List.length_append, ih, length_encRM, List.length_cons]; ring

@[simp] theorem takeD_encRM (x : Rq N K) : takeD (N * K) (encRM N K x) = encRM N K x :=
  takeD_of_length' (length_encRM N K x)

theorem takeD_append_of_length : ∀ {n : ℕ} {w : List Bool} (u : List Bool), w.length = n →
    takeD n (w ++ u) = w
  | 0, [], _, _ => rfl
  | n + 1, b :: w, u, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [takeD, List.cons_append, List.tail_cons]
    rw [takeD_append_of_length u h]; rfl

@[simp] theorem takeD_encRM_append (x : Rq N K) (u : List Bool) :
    takeD (N * K) (encRM N K x ++ u) = encRM N K x :=
  takeD_append_of_length u (length_encRM N K x)

@[simp] theorem drop_encRM_append (x : Rq N K) (u : List Bool) :
    (encRM N K x ++ u).drop (N * K) = u := by
  rw [List.drop_append_of_le_length (by rw [length_encRM]), List.drop_of_length_le
    (by rw [length_encRM])]
  simp [length_encRM]

@[simp] theorem drop_encRM (x : Rq N K) : (encRM N K x).drop (N * K) = [] :=
  List.drop_of_length_le (by rw [length_encRM])

/-- Shifting a word into a queue whose head is a ring word. -/
@[simp] theorem shiftIn_encRM (y : Rq N K) (u s : List Bool) :
    ValVM.shiftIn (N * K) (encRM N K y ++ u) s = u ++ takeD (N * K) s := by
  unfold ValVM.shiftIn
  rw [List.append_assoc, drop_encRM_append]

@[simp] theorem shiftIn_encRM' (y : Rq N K) (s : List Bool) :
    ValVM.shiftIn (N * K) (encRM N K y) s = takeD (N * K) s := by
  simpa using shiftIn_encRM y [] s

theorem toBits_zero : ∀ K : ℕ, toBits K 0 = List.replicate K false
  | 0 => rfl
  | K + 1 => by simp [toBits, toBits_zero K, List.replicate_succ]

theorem encRM_zero (N K : ℕ) : encRM N K (0 : Rq N K) = List.replicate (N * K) false := by
  have h : ∀ n, concatN n (fun i => encM K (coefG (0 : Rq N K) i)) =
      List.replicate (n * K) false := by
    intro n
    induction n with
    | zero => simp [concatN]
    | succ n ih =>
      rw [concatN, ih, coefG_zero, encM, ZMod.val_zero, toBits_zero, Nat.succ_mul,
        List.replicate_add]
  exact h N

theorem encL_replicate_zero (N K m : ℕ) :
    encL N K (List.replicate m (0 : Rq N K)) = List.replicate (m * (N * K)) false := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, encL_cons, ih, encRM_zero, Nat.succ_mul, Nat.add_comm,
      List.replicate_add]

/-! ### The operations on canonical words -/

section Ops

variable (hK : 0 < K)
include hK

theorem canonW_add (a b : Rq N K) :
    canonW N K (addRMW N K (encRM N K a) (encRM N K b)) = encRM N K (a + b) := by
  rw [canonW_eq hK (length_addRMW _ _ (length_encRM _ _ _) _),
    decRM_addRMW (length_encRM _ _ _) (length_encRM _ _ _), decRM_encRM hK, decRM_encRM hK]

theorem canonW_sub (a b : Rq N K) :
    canonW N K (subRMW N K (encRM N K a) (encRM N K b)) = encRM N K (a - b) := by
  rw [canonW_eq hK (length_subRMW _ _ (length_encRM _ _ _) _),
    decRM_subRMW (length_encRM _ _ _) (length_encRM _ _ _), decRM_encRM hK, decRM_encRM hK]

theorem canonW_mul (a b : Rq N K) :
    canonW N K (mulRMW N K (encRM N K a) (encRM N K b)) = encRM N K (a * b) := by
  rw [canonW_eq hK (length_mulRMW _ _ _ _),
    decRM_mulRMW (length_encRM _ _ _) (length_encRM _ _ _), decRM_encRM hK, decRM_encRM hK]

theorem canonW_neg (a : Rq N K) : canonW N K (notW (encRM N K a)) = encRM N K (-a) := by
  rw [canonW_eq hK (by rw [length_notW, length_encRM]), decRM_notW (length_encRM _ _ _),
    decRM_encRM hK]

theorem canonW_aut (hN : 0 < N) {k : ℕ} (hk : 0 < k) (a : Rq N K) :
    canonW N K (autMW N K k (encRM N K a)) = encRM N K (aut N k a) := by
  rw [canonW_eq hK (length_autMW _ _ _ _ hN), decRM_autMW hk (length_encRM _ _ _), decRM_encRM hK]

theorem canonW_rho (hN : 0 < N) (j : ℕ) (a : Rq N K) :
    canonW N K ((rhoMW K)^[j] (encRM N K a)) = encRM N K (xInvG (ZMod (2 ^ K - 1)) N ^ j * a) := by
  rw [canonW_eq hK (by rw [length_rhoMW_iter, length_encRM]),
    decRM_rhoMW_iter_mul hN (length_encRM _ _ _), decRM_encRM hK]

theorem canonW_rot {j : ℕ} (hj : j ≤ K) (a : Rq N K) :
    canonW N K (rotBW N K j (encRM N K a)) = encRM N K ((2 : ZMod (2 ^ K - 1)) ^ (K - j) • a) := by
  have e : j = K - (K - j) := by omega
  rw [canonW_eq hK (length_rotBW _ _ _ (length_encRM _ _ _)), e,
    decRM_rotBW (length_encRM _ _ _) (Nat.sub_le _ _), decRM_encRM hK, ← e]

omit hK in
theorem getD_toBits : ∀ (K n i : ℕ), (toBits K n).getD i false = (decide (i < K) && n.testBit i)
  | 0, n, i => by simp [toBits]
  | K + 1, n, 0 => by simp [toBits, Nat.testBit_zero]
  | K + 1, n, i + 1 => by
    simp only [toBits, List.getD_cons_succ, getD_toBits K (n / 2) i, Nat.testBit_succ]
    simp

theorem canonW_dig (i : ℕ) (a : Rq N K) :
    canonW N K (digitRW N K i (encRM N K a)) = encRM N K (binaryDigit a i) := by
  rw [canonW_eq hK (by unfold digitRW; exact length_concatN fun _ _ => length_bitW _ _),
    decRM_digitRW hK]
  congr 1
  unfold binaryDigit
  congr 1
  funext t
  have hb : block K t.val (encRM N K a) = encM K (a.coeffs t) := by
    rw [encRM, block_concatN (fun _ _ => length_encM _ _), if_pos t.isLt]
    simp [coefG, t.isLt]
  rw [hb, encM, getD_toBits]
  haveI : NeZero (2 ^ K - 1) := ⟨by have := Nat.one_lt_two_pow (n := K) (by omega); omega⟩
  have hlt : (a.coeffs t).val < 2 ^ K := (ZMod.val_lt _).trans_le (Nat.sub_le _ _)
  by_cases hi : i < K
  · simp [hi]
  · have : (a.coeffs t).val.testBit i = false :=
      Nat.testBit_eq_false_of_lt (hlt.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hi, this]

end Ops

/-! ### The instructions, one at a time -/

section Exec

variable (N K)

theorem exec_seq (p q : Code) (w : St) : exec N K (.seq p q) w = exec N K q (exec N K p w) :=
  rfl
@[simp] theorem exec_nop (w : St) : exec N K .nop w = w := rfl
@[simp] theorem exec_cp (d s : Fin 64) (w : St) :
    exec N K (.cp d s) w = Function.update w d (w s) := rfl
@[simp] theorem exec_clr (t : Fin 64) (w : St) : exec N K (.clr t) w = Function.update w t [] := rfl
@[simp] theorem exec_tl (t : Fin 64) (w : St) :
    exec N K (.tl t) w = Function.update w t (w t).tail := rfl
@[simp] theorem exec_app (d s : Fin 64) (w : St) :
    exec N K (.app d s) w = Function.update w d (w d ++ w s) := rfl
@[simp] theorem exec_eqb (f a b : Fin 64) (w : St) : exec N K (.eqb f a b) w =
    if f = a ∨ f = b ∨ a = b then w else Function.update w f [decide (w a = w b)] := rfl
@[simp] theorem exec_drop (t c : Fin 64) (w : St) : exec N K (.drop t c) w =
    if t = c then w else Function.update w t ((w t).drop (w c).length) := rfl
@[simp] theorem exec_mv (d s c : Fin 64) (w : St) : exec N K (.mv d s c) w =
    if d = s ∨ d = c ∨ s = c then w else
      Function.update (Function.update w s ((w s).drop (w c).length)) d
        (ValVM.shiftIn (w c).length (w d) (w s)) := rfl
@[simp] theorem exec_mvR (d s : Fin 64) (w : St) : exec N K (.mvR d s) w =
    if d = s then w else
      Function.update (Function.update w s ((w s).drop (N * K))) d
        (ValVM.shiftIn (N * K) (w d) (w s)) := rfl
@[simp] theorem exec_ifb (t : Fin 64) (p q : Code) (w : St) : exec N K (.ifb t p q) w =
    if hd (w t) = true then exec N K p w else exec N K q w := rfl
@[simp] theorem exec_add (d a b : Fin 64) (w : St) : exec N K (.op .add d a b) w =
    Function.update w d (canonW N K (addRMW N K (takeD (N * K) (w a)) (takeD (N * K) (w b)))) := rfl
@[simp] theorem exec_sub (d a b : Fin 64) (w : St) : exec N K (.op .sub d a b) w =
    Function.update w d (canonW N K (subRMW N K (takeD (N * K) (w a)) (takeD (N * K) (w b)))) := rfl
@[simp] theorem exec_mul (d a b : Fin 64) (w : St) : exec N K (.op .mul d a b) w =
    Function.update w d (canonW N K (mulRMW N K (takeD (N * K) (w a)) (takeD (N * K) (w b)))) := rfl
@[simp] theorem exec_neg (d a b : Fin 64) (w : St) : exec N K (.op .neg d a b) w =
    Function.update w d (canonW N K (notW (takeD (N * K) (w a)))) := rfl
@[simp] theorem exec_aut (d a b : Fin 64) (w : St) : exec N K (.op .aut d a b) w =
    Function.update w d (canonW N K (autMW N K (w b).length (takeD (N * K) (w a)))) := rfl
@[simp] theorem exec_rho (d a b : Fin 64) (w : St) : exec N K (.op .rho d a b) w =
    Function.update w d (canonW N K ((rhoMW K)^[(w b).length] (takeD (N * K) (w a)))) := rfl
@[simp] theorem exec_rot (d a b : Fin 64) (w : St) : exec N K (.op .rot d a b) w =
    Function.update w d (canonW N K (rotBW N K (w b).length (takeD (N * K) (w a)))) := rfl
@[simp] theorem exec_dig (d a b : Fin 64) (w : St) : exec N K (.op .dig d a b) w =
    Function.update w d (canonW N K (digitRW N K (w b).length (takeD (N * K) (w a)))) := rfl

end Exec

/-! ### Footprints -/

theorem exec_writes : ∀ (c : Code) (w : St) (r : Fin 64), c.writes r = false →
    exec N K c w r = w r
  | .op o d a b, w, r, h => by
    simp only [Code.writes, beq_eq_false_iff_ne] at h
    simp [exec, Function.update_of_ne (Ne.symm h)]
  | .mv d s c, w, r, h => by
    simp only [Code.writes, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
    simp only [exec]; split_ifs
    · rfl
    · rw [Function.update_of_ne (Ne.symm h.1), Function.update_of_ne (Ne.symm h.2)]
  | .mvR d s, w, r, h => by
    simp only [Code.writes, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
    simp only [exec]; split_ifs
    · rfl
    · rw [Function.update_of_ne (Ne.symm h.1), Function.update_of_ne (Ne.symm h.2)]
  | .cp d s, w, r, h => by
    simp only [Code.writes, beq_eq_false_iff_ne] at h
    simp [exec, Function.update_of_ne (Ne.symm h)]
  | .drop t c, w, r, h => by
    simp only [Code.writes, beq_eq_false_iff_ne] at h
    simp only [exec]; split_ifs
    · rfl
    · rw [Function.update_of_ne (Ne.symm h)]
  | .clr t, w, r, h => by
    simp only [Code.writes, beq_eq_false_iff_ne] at h
    simp [exec, Function.update_of_ne (Ne.symm h)]
  | .tl t, w, r, h => by
    simp only [Code.writes, beq_eq_false_iff_ne] at h
    simp [exec, Function.update_of_ne (Ne.symm h)]
  | .app d s, w, r, h => by
    simp only [Code.writes, beq_eq_false_iff_ne] at h
    simp [exec, Function.update_of_ne (Ne.symm h)]
  | .eqb f a b, w, r, h => by
    simp only [Code.writes, beq_eq_false_iff_ne] at h
    simp only [exec]; split_ifs
    · rfl
    · rw [Function.update_of_ne (Ne.symm h)]
  | .rep c body, w, r, h => by
    simp only [Code.writes, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
    simp only [exec]
    generalize (w c).length = n
    induction n generalizing w with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply, ih, exec_writes body _ r h.2,
        Function.update_of_ne (Ne.symm h.1)]
  | .seq p q, w, r, h => by
    simp only [Code.writes, Bool.or_eq_false_iff] at h
    simp only [exec]; rw [exec_writes q _ r h.2, exec_writes p _ r h.1]
  | .ifb t p q, w, r, h => by
    simp only [Code.writes, Bool.or_eq_false_iff] at h
    simp only [exec]; split_ifs
    · exact exec_writes p _ r h.1
    · exact exec_writes q _ r h.2
  | .nop, _, _, _ => rfl

/-! ### Loops -/

/-- **A `rep` loop by an invariant**: if every round keeps `P` (indexed by the round), the loop
ends in `P` at the number of rounds. The counter is the `m`-th tail of its word in round `m`. -/
theorem exec_rep_inv (c : Fin 64) (body : Code) (hb : body.writes c = false) (P : ℕ → St → Prop)
    (w : St) (h0 : P 0 w)
    (hs : ∀ m w', m < (w c).length → P m w' → w' c = (w c).drop m →
      P (m + 1) (exec N K body (Function.update w' c (w' c).tail))) :
    P (w c).length (exec N K (.rep c body) w) := by
  simp only [exec]
  have key : ∀ m ≤ (w c).length,
      P m ((fun w' => exec N K body (Function.update w' c (w' c).tail))^[m] w) ∧
      ((fun w' => exec N K body (Function.update w' c (w' c).tail))^[m] w) c = (w c).drop m := by
    intro m
    induction m with
    | zero => intro _; exact ⟨h0, rfl⟩
    | succ m ih =>
      intro hm
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [Function.iterate_succ_apply']
      refine ⟨hs m _ (by omega) h1 h2, ?_⟩
      rw [exec_writes body _ c hb, Function.update_self, h2, List.tail_drop]
  exact (key _ le_rfl).1

end MVM

end SigabaNeo.Tape
