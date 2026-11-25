import SigabaNeoStd.Lattices.ProgAlgo.Nand
import SigabaNeoStd.Lattices.ProgAlgo.SLPTape
import SigabaNeoStd.Lattices.Algo.SimWords

/-!
# The simulation on joint words

A state `(A, W, x)` of the simulation (`simStepW`, `slpSimRunW`) is held on one tape as the *joint
word* `A ++ W ++ x` (`jointW`), `A` of `La = r · 2k · N K` bits, `W` of `Lw = d · 2k · N K` bits,
`x` of `N K` bits; `splitJ La Lw` cuts it back (`jointW_splitJ`, `splitJ_jointW`). The step on joint
words is `simStepJW`, and **the store of the evaluator holds the joint words of `slpSimRunW`**
(`simValues_block`).

Word identities used by the programs:

* `matMulW_one_one`: the entrywise product with a ring word `smulMatW` is the `1 × 1 · 1 × L`
  product;
* `ginvGswW_eq`: `G⁻¹` of the Ring-GSW gadget is the top halves of `G̲⁻¹` of the two rows;
* `gswGadW_eq`: the Ring-GSW gadget word is `gadW`, then `k` zero entries, then the top half of
  `gadW`.
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices SigabaNeo.Lattices.Algo Prog

/-! ### Joint words -/

/-- The joint word of a state of the simulation. -/
def jointW (t : List Bool × List Bool × List Bool) : List Bool := t.1 ++ t.2.1 ++ t.2.2

/-- Cut a joint word into parts of `a` and `b` bits and the rest. -/
def splitJ (a b : ℕ) (u : List Bool) : List Bool × List Bool × List Bool :=
  (u.take a, (u.drop a).take b, u.drop (a + b))

theorem jointW_splitJ (a b : ℕ) (u : List Bool) : jointW (splitJ a b u) = u := by
  simp only [jointW, splitJ, List.append_assoc]
  rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]

theorem splitJ_jointW {a b : ℕ} {t : List Bool × List Bool × List Bool} (ha : t.1.length = a)
    (hb : t.2.1.length = b) : splitJ a b (jointW t) = t := by
  obtain ⟨A, W, x⟩ := t
  simp only at ha hb
  subst ha hb
  simp [splitJ, jointW, List.take_append_of_le_length, List.drop_append]

theorem length_jointW (t : List Bool × List Bool × List Bool) :
    (jointW t).length = t.1.length + t.2.1.length + t.2.2.length := by
  simp [jointW]; omega

variable {N K k : ℕ}

/-- The lengths of the parts: public-key matrix of `r` rows, short matrix of `d` rows. -/
abbrev lenA (N K k r : ℕ) : ℕ := r * (2 * k) * (N * K)

/-- **The step of the simulation on joint words.** -/
def simStepJW (N K k r d : ℕ) (gad : List Bool) (ginv : List Bool → List Bool) (u v : List Bool) :
    List Bool :=
  jointW (simStepW N K k r d gad ginv (splitJ (lenA N K k r) (lenA N K k d) u)
    (splitJ (lenA N K k r) (lenA N K k d) v))

theorem length_matSubW {L : ℕ} {x : List Bool} (hx : x.length = L * (N * K)) (y : List Bool) :
    (matSubW N K L x y).length = L * (N * K) :=
  length_concatN fun p hp => length_subRW N K (length_block hx hp) _

theorem length_simStepW {r d : ℕ} {gad : List Bool} (hg : gad.length = lenA N K k r)
    (ginv : List Bool → List Bool) (u v : List Bool × List Bool × List Bool) :
    (simStepW N K k r d gad ginv u v).1.length = lenA N K k r ∧
      (simStepW N K k r d gad ginv u v).2.1.length = lenA N K k d ∧
      (simStepW N K k r d gad ginv u v).2.2.length = N * K := by
  refine ⟨length_matSubW hg _, length_matSubW (by simp) _, length_subRW N K ?_ _⟩
  exact length_constW (length_bitW K true)

theorem length_simStepJW {r d : ℕ} {gad : List Bool} (hg : gad.length = lenA N K k r)
    (ginv : List Bool → List Bool) (u v : List Bool) :
    (simStepJW N K k r d gad ginv u v).length = lenA N K k r + lenA N K k d + N * K := by
  obtain ⟨h1, h2, h3⟩ := length_simStepW (d := d) hg ginv
    (splitJ (lenA N K k r) (lenA N K k d) u) (splitJ (lenA N K k r) (lenA N K k d) v)
  rw [simStepJW, length_jointW, h1, h2, h3]

theorem splitJ_simStepJW {r d : ℕ} {gad : List Bool} (hg : gad.length = lenA N K k r)
    (ginv : List Bool → List Bool) (u v : List Bool) :
    splitJ (lenA N K k r) (lenA N K k d) (simStepJW N K k r d gad ginv u v) =
      simStepW N K k r d gad ginv (splitJ (lenA N K k r) (lenA N K k d) u)
        (splitJ (lenA N K k r) (lenA N K k d) v) := by
  obtain ⟨h1, h2, -⟩ := length_simStepW (d := d) hg ginv
    (splitJ (lenA N K k r) (lenA N K k d) u) (splitJ (lenA N K k r) (lenA N K k d) v)
  exact splitJ_jointW h1 h2

/-- The joint word of the value `1` of the simulation: `(G, 0, 1)`. -/
def simOneW (N K k d : ℕ) (gad : List Bool) : List Bool :=
  jointW (gad, zeroW (lenA N K k d), oneW N K)

/-- **The joint run is the run on joint words.** -/
theorem simValueOf_joint {ι : Type*} {r d : ℕ} {gad : List Bool} (hg : gad.length = lenA N K k r)
    (ginv : List Bool → List Bool) (aW wW xW : ι → List Bool)
    (ha : ∀ i, (aW i).length = lenA N K k r) (hw : ∀ i, (wW i).length = lenA N K k d)
    (p : SLP ι) (w : Wire ι) :
    SLP.valueOf (fun i => jointW (aW i, wW i, xW i)) (simOneW N K k d gad)
        (simStepJW N K k r d gad ginv) p w =
      jointW (slpSimRunW N K k r d gad ginv aW wW xW p w) := by
  have h := SLP.valueOf_map (fun i => jointW (aW i, wW i, xW i)) (simOneW N K k d gad)
    (simStepJW N K k r d gad ginv) (fun i => (aW i, wW i, xW i))
    (gad, zeroW (lenA N K k d), oneW N K) (simStepW N K k r d gad ginv)
    (splitJ (lenA N K k r) (lenA N K k d)) (fun i => splitJ_jointW (ha i) (hw i))
    (splitJ_jointW hg (by simp)) (fun u v => splitJ_simStepJW hg ginv u v) p w
  rw [slpSimRunW, ← h, jointW_splitJ]

/-- **The joint word of a wire in the store of the evaluator** (`run_slpEvalP` with the step
`simStepJW`): the entry at the final position of the wire `w` is the joint word of
`slpSimRunW … w`. -/
theorem simValues_block {ι : Type*} {r d : ℕ} {gad : List Bool} (hg : gad.length = lenA N K k r)
    (ginv : List Bool → List Bool) (aW wW xW : ι → List Bool)
    (ha : ∀ i, (aW i).length = lenA N K k r) (hw : ∀ i, (wW i).length = lenA N K k d)
    {ins : List (List Bool)} {n : ℕ} (hn : ins.length = n) {ix : ι → ℕ} (hix : ∀ i, ix i < n)
    (hins : ∀ i, ins.getD (ix i) [] = jointW (aW i, wW i, xW i)) (p : SLP ι) (w : Wire ι) :
    ∃ h : wireIx ix n p.length w <
        (ins ++ [simOneW N K k d gad] ++ SLP.values (fun i => ins.getD (ix i) [])
          (simOneW N K k d gad) (simStepJW N K k r d gad ginv) p).length,
      (ins ++ [simOneW N K k d gad] ++ SLP.values (fun i => ins.getD (ix i) [])
          (simOneW N K k d gad) (simStepJW N K k r d gad ginv) p)[wireIx ix n p.length w] =
        jointW (slpSimRunW N K k r d gad ginv aW wW xW p w) := by
  have hlen : (SLP.values (fun i => ins.getD (ix i) []) (simOneW N K k d gad)
      (simStepJW N K k r d gad ginv) p).length = p.length := by
    rw [SLP.values, length_slpRun]; simp
  obtain ⟨h1, h2⟩ := getElem_wireIx ix ins hn hix (simOneW N K k d gad)
    (SLP.values (fun i => ins.getD (ix i) []) (simOneW N K k d gad)
      (simStepJW N K k r d gad ginv) p) w
  simp only [hlen] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  have e : (fun i => ins.getD (ix i) []) = fun i => jointW (aW i, wW i, xW i) := funext hins
  rw [← simValueOf_joint hg ginv aW wW xW ha hw p w, e]
  rfl

/-- **The short matrix of a wire** read from the store entry. -/
theorem simValues_short {ι : Type*} {r d : ℕ} {gad : List Bool} (hg : gad.length = lenA N K k r)
    (ginv : List Bool → List Bool) (aW wW xW : ι → List Bool)
    (ha : ∀ i, (aW i).length = lenA N K k r) (hw : ∀ i, (wW i).length = lenA N K k d)
    {ins : List (List Bool)} {n : ℕ} (hn : ins.length = n) {ix : ι → ℕ} (hix : ∀ i, ix i < n)
    (hins : ∀ i, ins.getD (ix i) [] = jointW (aW i, wW i, xW i)) (p : SLP ι) (w : Wire ι) :
    ∃ h : wireIx ix n p.length w <
        (ins ++ [simOneW N K k d gad] ++ SLP.values (fun i => ins.getD (ix i) [])
          (simOneW N K k d gad) (simStepJW N K k r d gad ginv) p).length,
      (splitJ (lenA N K k r) (lenA N K k d) (ins ++ [simOneW N K k d gad] ++
          SLP.values (fun i => ins.getD (ix i) []) (simOneW N K k d gad)
            (simStepJW N K k r d gad ginv) p)[wireIx ix n p.length w]).2.1 =
        (slpSimRunW N K k r d gad ginv aW wW xW p w).2.1 := by
  obtain ⟨h, e⟩ := simValues_block hg ginv aW wW xW ha hw hn hix hins p w
  refine ⟨h, ?_⟩
  rw [e]
  have hl := SLP.valueOf_invariant (fun i => (aW i, wW i, xW i))
    (gad, zeroW (lenA N K k d), oneW N K) (simStepW N K k r d gad ginv)
    (fun t => t.1.length = lenA N K k r ∧ t.2.1.length = lenA N K k d)
    (fun i => ⟨ha i, hw i⟩) ⟨hg, by simp⟩
    (fun a b _ _ => ⟨(length_simStepW hg ginv a b).1, (length_simStepW hg ginv a b).2.1⟩) p w
  exact congrArg (fun t => t.2.1) (splitJ_jointW hl.1 hl.2)

/-! ### Word identities for the programs -/

theorem addRW_zeroW {z : List Bool} (hz : z.length = N * K) : addRW N K (zeroW (N * K)) z = z := by
  rw [← enc_zeroR N K, ← enc_decR hz, addRW_enc, zero_add]

/-- **The entrywise product with a ring word** is the product of a `1 × 1` and a `1 × L` matrix
word. -/
theorem matMulW_one_one (L : ℕ) {x : List Bool} (hx : x.length = N * K) (y : List Bool) :
    matMulW N K 1 1 L x y = smulMatW N K L x y := by
  rw [matMulW, smulMatW, Nat.one_mul]
  apply concatN_congr
  intro p hp
  rw [sumLoop, sumLoop, Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp, zero_mul, zero_add, zero_mul,
    zero_add, addRW_zeroW (length_mulRW N K _ _)]
  congr 1
  rw [rget, block, zero_mul, List.drop_zero, List.take_of_length_le (by omega)]

theorem take_concatN {n m c : ℕ} {f : ℕ → List Bool} (h : ∀ i < n + m, (f i).length = c) :
    (concatN (n + m) f).take (n * c) = concatN n f := by
  rw [concatN_add, List.take_left' (length_concatN fun i hi => h i (by omega))]

theorem take_ginvW (N K k : ℕ) (b : List Bool) :
    (ginvW N K k b).take (k * (2 * k * (N * K))) = concatN k (fun r => digitRW (2 * k * N) K r b) := by
  rw [ginvW_eq, List.take_left' (length_concatN fun i _ => by rw [length_digitRW]; ring)]

theorem block_take {c j M : ℕ} (a : List Bool) (h : (j + 1) * c ≤ M) :
    block c j (a.take M) = block c j a := by
  simp only [block, List.drop_take, List.take_take]
  congr 1
  rw [Nat.add_mul, Nat.one_mul] at h
  omega

theorem block_drop {c j M : ℕ} (a : List Bool) (hM : M = m * c) :
    block c j (a.drop M) = block c (m + j) a := by
  simp only [block, List.drop_drop, hM, Nat.add_mul]

/-- **`G⁻¹` of the Ring-GSW gadget**: the top halves (`k` rows each) of `G̲⁻¹` of the two rows. -/
theorem ginvGswW_eq (N K k : ℕ) (a : List Bool) :
    ginvGswW N K k a =
      (ginvW N K k (a.take (2 * k * (N * K)))).take (k * (2 * k * (N * K))) ++
        (ginvW N K k (a.drop (2 * k * (N * K)))).take (k * (2 * k * (N * K))) := by
  rw [take_ginvW, take_ginvW, ginvGswW, concatN_mul, concatN_two_mul]
  congr 1
  · apply concatN_congr
    intro r hr
    rw [← digitRW_entries]
    apply concatN_congr
    intro c hc
    have hdiv : (r * (2 * k) + c) / (2 * k) = r := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, zero_add]
    have hmod : (r * (2 * k) + c) % (2 * k) = c := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
    rw [hdiv, hmod, Nat.div_eq_of_lt hr, Nat.mod_eq_of_lt hr, zero_mul, zero_add, rget,
      block_take a (Nat.mul_le_mul_right _ (by omega : c + 1 ≤ 2 * k))]
  · apply concatN_congr
    intro r hr
    rw [← digitRW_entries]
    apply concatN_congr
    intro c hc
    have hdiv : ((k + r) * (2 * k) + c) / (2 * k) = k + r := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, zero_add]
    have hmod : ((k + r) * (2 * k) + c) % (2 * k) = c := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
    have hk : (k + r) / k = 1 := by
      rw [Nat.add_comm, Nat.add_div_right _ (by omega), Nat.div_eq_of_lt hr]
    have hk' : (k + r) % k = r := by
      rw [Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt hr]
    simp only [rget]
    rw [hdiv, hmod, hk, hk', one_mul, block_drop a (m := 2 * k) rfl]

theorem concatN_zeroW' (n c : ℕ) : concatN n (fun _ => zeroW c) = zeroW (n * c) := by
  induction n with
  | zero => simp [concatN, zeroW]
  | succ n ih => rw [concatN, ih, Nat.succ_mul]; simp only [zeroW, List.replicate_append_replicate]

/-- **The Ring-GSW gadget word**: the top-row gadget, then `k` zero entries and the first `k`
entries of the top-row gadget. -/
theorem gswGadW_eq (N K k : ℕ) :
    gswGadW N K k = gadW N K k ++ (zeroW (k * (N * K)) ++ (gadW N K k).take (k * (N * K))) := by
  rw [gadW_eq, List.take_left' (length_concatN fun p _ => length_constW (length_powW K p)),
    gswGadW, show 2 * (2 * k) = 2 * k + 2 * k by ring, concatN_add, concatN_two_mul,
    concatN_two_mul, ← concatN_zeroW' k (N * K),
    show List.replicate (k * (N * K)) false = zeroW _ from rfl, ← concatN_zeroW' k (N * K)]
  have hk0 : ∀ {p : ℕ}, p < k → 0 < k := fun h => by omega
  have hd : ∀ q, q < 2 * k → (2 * k + q) / (2 * k) = 1 ∧ (2 * k + q) % (2 * k) = q := by
    intro q hq
    constructor
    · rw [Nat.add_comm, Nat.add_div_right _ (by omega), Nat.div_eq_of_lt hq]
    · rw [Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt hq]
  have hkr : ∀ r, r < k → (k + r) / k = 1 ∧ (k + r) % k = r := by
    intro r hr
    constructor
    · rw [Nat.add_comm, Nat.add_div_right _ (hk0 hr), Nat.div_eq_of_lt hr]
    · rw [Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt hr]
  congr 1
  · congr 1
    · apply concatN_congr
      intro p hp
      have h2 : p < 2 * k := by omega
      rw [Nat.div_eq_of_lt h2, Nat.mod_eq_of_lt h2, Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp]
      simp
    · apply concatN_congr
      intro r hr
      have h2 : k + r < 2 * k := by omega
      rw [Nat.div_eq_of_lt h2, Nat.mod_eq_of_lt h2, (hkr r hr).1]
      simp
  · congr 1
    · apply concatN_congr
      intro r hr
      obtain ⟨h1, h2⟩ := hd r (by omega)
      rw [h1, h2, Nat.div_eq_of_lt hr]
      simp
    · apply concatN_congr
      intro r hr
      obtain ⟨h1, h2⟩ := hd (k + r) (by omega)
      rw [h1, h2, (hkr r hr).1, (hkr r hr).2]
      simp

end SigabaNeo.Tape
