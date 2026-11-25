import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMMat

/-!
# Utilities of the Mersenne VM: templates, constants, fields

Generic VM code (`SigabaNeo.Tape.MVM`) for programs that build everything they need from their
input words:

* `bitsC`: the one-bit words `[true]`, `[false]` from two blank registers (`exec_bitsC`);
* `natC r u n`: the unary template `r := replicate n false` by binary doubling from a register
  `u = [false]` (`exec_natC`; `O(log n)` instructions);
* `takeC d s c`: the first `|c|` bits of the stream `s` into `d` (`exec_takeC`);
* `repAppC c d s`: `d := d ++ s^{|c|}` (`exec_repAppC`);
* the canonical words of the constants `1` (`encRM_one`) and of the elements with every
  coefficient `c` (`encRM_ofCoeffs_const`).
-/

namespace SigabaNeo.Tape

namespace MVM

open SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG Prog Cslib

variable {N K : ℕ}

/-! ### One-bit words -/

/-- `t := [true]`, `f := [false]` (`a` blank, pairwise distinct registers). -/
def bitsC (t f a : Fin 64) : Code := .seq (.clr t) <| .seq (.clr f) <| .seq (.eqb t f a) (.eqb f t a)

theorem exec_bitsC (t f a : Fin 64) (h1 : t ≠ f) (h2 : t ≠ a) (h3 : f ≠ a) (w : St)
    (ha : w a = []) :
    exec N K (bitsC t f a) w = Function.update (Function.update w t [true]) f [false] := by
  simp only [bitsC, exec_seq, exec_clr, exec_eqb]
  rw [if_neg (by tauto), if_neg (by tauto)]
  funext x
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-! ### Unary templates -/

/-- **`r := replicate n false`** by doubling along the bits of `n`, from `u = [false]`. -/
def natC (r u : Fin 64) : ℕ → Code
  | 0 => .clr r
  | n + 1 => .seq (.seq (natC r u ((n + 1) / 2)) (.app r r))
      (if (n + 1) % 2 = 0 then .nop else .app r u)
  decreasing_by omega

theorem natC_writes (r u : Fin 64) : ∀ n (t : Fin 64), t ≠ r → (natC r u n).writes t = false
  | 0, t, h => by simp [natC, Code.writes, Ne.symm h]
  | n + 1, t, h => by
    rw [natC]
    have ih := natC_writes r u ((n + 1) / 2) t h
    split_ifs <;> simp [Code.writes, ih, Ne.symm h]

theorem natC_wfc (r u : Fin 64) : ∀ n, (natC r u n).WFc
  | 0 => by simp [natC, Code.WFc]
  | n + 1 => by
    rw [natC]
    have ih := natC_wfc r u ((n + 1) / 2)
    split_ifs <;> exact ⟨⟨ih, trivial⟩, trivial⟩

theorem exec_natC (r u : Fin 64) (hru : r ≠ u) :
    ∀ n (w : St), w u = [false] → exec N K (natC r u n) w = Function.update w r (List.replicate n false)
  | 0, w, _ => by simp [natC]
  | n + 1, w, hu => by
    have ih := exec_natC r u hru ((n + 1) / 2) w hu
    rw [natC]
    split_ifs with h
    · simp only [exec_seq, ih, exec_app, exec_nop, Function.update_self, Function.update_idem,
        ← List.replicate_add]
      congr 2; omega
    · simp only [exec_seq, ih, exec_app, Function.update_self, Function.update_idem,
        Function.update_of_ne hru.symm, hu, ← List.replicate_add, ← List.replicate_succ']
      congr 2; omega

/-! ### Fields of a stream -/

/-- **The first `|c|` bits of the stream `s` into `d`** (`s` loses them). -/
def takeC (d s c : Fin 64) : Code := .seq (.cp d c) (.mv d s c)

theorem exec_takeC (d s c : Fin 64) (h : ¬(d = s ∨ d = c ∨ s = c)) (w : St) (n : ℕ)
    (hc : w c = List.replicate n false) :
    exec N K (takeC d s c) w =
      Function.update (Function.update w s ((w s).drop n)) d (takeD n (w s)) := by
  have hds : d ≠ s := fun e => h (Or.inl e)
  have hdc : d ≠ c := fun e => h (Or.inr (Or.inl e))
  have hsc : s ≠ c := fun e => h (Or.inr (Or.inr e))
  simp only [takeC, exec_seq, exec_cp, exec_mv, if_neg h]
  simp only [Function.update_self, Function.update_of_ne hdc.symm, Function.update_of_ne hds.symm,
    hc, List.length_replicate, Function.update_idem]
  rw [show ValVM.shiftIn n (List.replicate n false) (w s) = takeD n (w s) by
    unfold ValVM.shiftIn; rw [List.drop_left' (by simp)]]
  funext x
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-! ### Repeated appends -/

/-- **`d := d ++ s^{|c|}`**. -/
def repAppC (c d s : Fin 64) : Code := .rep c (.app d s)

theorem exec_repAppC (c d s : Fin 64) (hcd : c ≠ d) (hcs : c ≠ s) (hds : d ≠ s) (w : St) :
    exec N K (repAppC c d s) w d = w d ++ (List.replicate (w c).length (w s)).flatten := by
  unfold repAppC
  have key := exec_rep_inv (N := N) (K := K) c (.app d s)
    (by simp [Code.writes, Ne.symm hcd] ) (fun m w' => w' d =
      w d ++ (List.replicate m (w s)).flatten ∧ w' s = w s) w (by simp) ?_
  · exact key.1
  · intro m w' _ hP _
    obtain ⟨h1, h2⟩ := hP
    simp only [exec_app, Function.update_self, Function.update_of_ne hcd.symm,
      Function.update_of_ne hcs.symm, Function.update_of_ne (Ne.symm hds), h1, h2]
    refine ⟨?_, trivial⟩
    rw [List.replicate_succ', List.flatten_append, List.flatten_singleton, List.append_assoc]

/-! ### Constant words -/

theorem encRM_eq_concatN (a : Rq N K) :
    encRM N K a = concatN N fun i => encM K (coefG a i) := rfl

/-- The word of the element with every coefficient `c`. -/
theorem encRM_ofCoeffs_const (c : ZMod (2 ^ K - 1)) :
    encRM N K (Negacyclic.ofCoeffs fun _ => c : Rq N K) = (List.replicate N (encM K c)).flatten := by
  rw [encRM]
  have : ∀ n ≤ N, concatN n (fun i => encM K (coefG (Negacyclic.ofCoeffs fun _ => c : Rq N K) i)) =
      (List.replicate n (encM K c)).flatten := by
    intro n
    induction n with
    | zero => intro; rfl
    | succ n ih =>
      intro hn
      rw [concatN, ih (by omega), coefG_ofCoeffs _ (by omega), List.replicate_succ',
        List.flatten_append, List.flatten_singleton]
  exact this N le_rfl

theorem val_one_mersenne (hK : 2 ≤ K) : (1 : ZMod (2 ^ K - 1)).val = 1 := by
  have : 4 ≤ 2 ^ K := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK
  haveI : Fact (1 < 2 ^ K - 1) := ⟨by omega⟩
  exact ZMod.val_one _

theorem toBits_one (K : ℕ) (hK : 0 < K) : toBits K 1 = true :: List.replicate (K - 1) false := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  simp [toBits, toBits_zero]

/-- **The word of `1`**: `1` in the first block, then zeros. -/
theorem encRM_one (hN : 0 < N) (hK : 2 ≤ K) :
    encRM N K (1 : Rq N K) = (true :: List.replicate (K - 1) false) ++
      List.replicate ((N - 1) * K) false := by
  rw [encRM]
  have h1 : ∀ n, 1 ≤ n → n ≤ N → concatN n (fun i => encM K (coefG (1 : Rq N K) i)) =
      (true :: List.replicate (K - 1) false) ++ List.replicate ((n - 1) * K) false := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ n ih =>
      intro _ hn
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp only [concatN, List.nil_append, zero_add, Nat.sub_self, zero_mul, List.replicate_zero,
          List.append_nil]
        rw [encM, coefG, dif_pos hN]
        simp only [Negacyclic.coeffs_one]
        simp [val_one_mersenne hK, toBits_one K (by omega)]
      · rw [concatN, ih hpos (by omega), encM, coefG, dif_pos (by omega)]
        simp only [Negacyclic.coeffs_one]
        rw [if_neg (by omega), ZMod.val_zero,
          toBits_zero, List.append_assoc, ← List.replicate_add]
        congr 2
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        simp; ring
  exact h1 N hN le_rfl

end MVM

end SigabaNeo.Tape
