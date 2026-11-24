import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.VMRing

/-!
# The digit dot product on the ring-word machine

The kernel of `Mul`, `SMul` and `Aut` (ePrint 2026/2539 §4.2) over `ℤ_{2^K − 1}[X]/(X^N + 1)` with
the binary gadget: for a vector `v` of `2K` ring elements (a stream of `2K` words, register `80`)
and two ring words `m₀`, `m₁` (registers `81`, `82`),

  `ddot = Σ_{i<K} v_i · d_i(m₀) + Σ_{i<K} v_{K+i} · d_i(m₁)`,

`d_i` the binary gadget digit (`binaryDigit`), into register `83` (`ddotC`, **`exec_ddotC`**).
Each `m_r` is canonicalized once, then its digits are read off by rotating every coefficient by
one bit per round (`digitRW_zero_rotBW`). Scratch: `84 … 89`.

The constants every block reads (`Consts`): register `0` blank, `1` one bit, `2` the zero word of
`N K` bits, `4` a word of `K` bits.
-/

namespace SigabaNeo.Tape

namespace RingVM

open SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG

variable {N K : ℕ}

/-- The ring. -/
abbrev RM (N K : ℕ) := Cslib.Negacyclic (ZMod (2 ^ K - 1)) N

/-- The constants every block reads. -/
structure Consts (N K : ℕ) (w : St) : Prop where
  z : w 0 = []
  one : w 1 = [false]
  zero : w 2 = List.replicate (N * K) false
  k : w 4 = List.replicate K false

theorem decRM_replicate (N K : ℕ) : decRM N K (List.replicate (N * K) false) = 0 := by
  apply ext_coefG
  intro i hi
  rw [coefG_decRM _ hi, coefG_zero]
  have : block K i (List.replicate (N * K) false) = zeroW K := by
    simp only [block, List.drop_replicate, List.take_replicate, zeroW]
    congr 1
    have : i * K + K ≤ N * K := by nlinarith
    omega
  rw [this, decM_zeroW]

theorem rotBW_one_rotBW {x : List Bool} (hx : x.length = N * K) (i : ℕ) :
    rotBW N K 1 (rotBW N K i x) = rotBW N K (i + 1) x := by
  rw [← rotBW_succ hx]
  rfl

/-! ### The code -/

/-- One digit: pop `v_i`, multiply by the digit `0` of the rotated word, accumulate, rotate. -/
def dBody : Code :=
  ofList [.mv 85 84 2, .digit 87 86 0, .mul 88 85 87, .add 83 83 88, .rotB 86 86 1]

/-- One row: canonicalize `m_r`, then `K` digits. -/
def dRow (src : Fin 200) : Code := ofList [.canon 86 src, .cp 89 4, .rep 89 dBody]

/-- **The digit dot product.** -/
def ddotC : Code := ofList [.cp 84 80, .cp 83 2, .cp 85 2, dRow 81, dRow 82]

theorem wr_dBody : wr dBody = [85, 84, 87, 88, 83, 86] := rfl

/-! ### Semantics -/

variable [NeZero (2 ^ K - 1)]

/-- The partial sums of one row. -/
noncomputable def dotRow (vs : List (List Bool)) (base : ℕ) (x : List Bool) (n : ℕ) : RM N K :=
  ∑ i ∈ Finset.range n, decRM N K (vs.getD (base + i) []) * binaryDigit (decRM N K x) i

theorem exec_dBody (hK : 0 < K) (w : St) (hc : Consts N K w) {v L : List Bool}
    (hv : v.length = N * K) (h84 : w 84 = v ++ L) (h85 : (w 85).length = N * K) {x : List Bool}
    (hx : x.length = N * K) {i : ℕ} (hi : i < K) (h86 : w 86 = rotBW N K i (canonW N K x))
    (h83 : (w 83).length = N * K) :
    (exec N K dBody w) 84 = L ∧ ((exec N K dBody w) 85).length = N * K ∧
      (exec N K dBody w) 86 = rotBW N K (i + 1) (canonW N K x) ∧
      ((exec N K dBody w) 83).length = N * K ∧
      decRM N K ((exec N K dBody w) 83) =
        decRM N K (w 83) + decRM N K v * binaryDigit (decRM N K x) i ∧
      ∀ j, j ∉ wr dBody → (exec N K dBody w) j = w j := by
  have hcx : (canonW N K x).length = N * K := length_canonW N K hx
  have hr : (rotBW N K i (canonW N K x)).length = N * K := length_rotBW N K i hcx
  have hpr := length_mulRMW N K v (digitRW N K 0 (rotBW N K i (canonW N K x)))
  have e : exec N K dBody w = Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update w 84 L) 85 v) 87
        (digitRW N K 0 (rotBW N K i (canonW N K x)))) 88
        (mulRMW N K v (digitRW N K 0 (rotBW N K i (canonW N K x))))) 83
        (addRMW N K (w 83) (mulRMW N K v (digitRW N K 0 (rotBW N K i (canonW N K x)))))) 86
        (rotBW N K 1 (rotBW N K i (canonW N K x))) := by
    simp only [dBody, exec_ofList_cons, exec_ofList_nil]
    rw [exec_mv_pop (by decide) (by rw [h85, hc.zero, List.length_replicate])
      (by rw [hv, hc.zero, List.length_replicate]) h84]
    simp only [exec, Function.update_apply, Fin.reduceEq, ↓reduceIte, hc.z, hc.one, h86,
      opd_eq hr, opd_eq hv, opd_eq h83, opd_mulRMW, opd_digitRW, List.length_nil,
      List.length_singleton]
  have hac : (addRMW N K (w 83) (mulRMW N K v (digitRW N K 0 (rotBW N K i (canonW N K x))))).length
      = N * K := length_addRMW N K h83 _
  refine ⟨?_, ?_, ?_, ?_, ?_, fun j hj => exec_not_mem _ _ j hj⟩
  · rw [e]; simp [Function.update_apply]
  · rw [e]; simp [Function.update_apply, hv]
  · rw [e]; simp [Function.update_apply, rotBW_one_rotBW hcx]
  · rw [e]; simp [Function.update_apply, hac]
  · rw [e]
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]
    rw [decRM_addRMW h83 hpr, decRM_mulRMW hv (length_digitRW' _ _ _ _),
      digitRW_zero_rotBW hcx hi, decRM_digitRW_canon hK hx]

theorem consts_update {w : St} (hc : Consts N K w) (j : Fin 200) (hj : 4 < j.val) (v : List Bool) :
    Consts N K (Function.update w j v) where
  z := by rw [Function.update_of_ne (by intro e; subst e; simp at hj)]; exact hc.z
  one := by rw [Function.update_of_ne (by intro e; subst e; simp at hj)]; exact hc.one
  zero := by rw [Function.update_of_ne (by intro e; subst e; simp at hj)]; exact hc.zero
  k := by rw [Function.update_of_ne (by intro e; subst e; simp at hj)]; exact hc.k

theorem consts_of_agree {w w' : St} (hc : Consts N K w) (h : ∀ j : Fin 200, j.val ≤ 4 → w' j = w j) :
    Consts N K w' where
  z := by rw [h 0 (by decide)]; exact hc.z
  one := by rw [h 1 (by decide)]; exact hc.one
  zero := by rw [h 2 (by decide)]; exact hc.zero
  k := by rw [h 4 (by decide)]; exact hc.k

/-- A code writing only registers above `4` keeps the constants. -/
theorem consts_exec {w : St} (hc : Consts N K w) (c : Code)
    (hwr : (wr c).all (fun x => decide (4 < x.val)) = true) :
    Consts N K (exec N K c w) :=
  consts_of_agree hc fun j hj => exec_not_mem c w j fun hm => by
    have := List.all_eq_true.mp hwr j hm; simp at this; omega

theorem flatten_drop_succ {vs : List (List Bool)} {i : ℕ} (hi : i < vs.length) :
    (vs.drop i).flatten = vs.getD i [] ++ (vs.drop (i + 1)).flatten := by
  rw [List.drop_eq_getElem_cons hi, List.flatten_cons, List.getD_eq_getElem _ _ hi]

theorem wr_dRow (src : Fin 200) : wr (dRow src) = [86, 89, 89, 85, 84, 87, 88, 83, 86] := rfl

/-- **One row of the dot product.** -/
theorem exec_dRow (hK : 0 < K) (w : St) (hc : Consts N K w) (src : Fin 200)
    {vs : List (List Bool)} (hvs : ∀ x ∈ vs, x.length = N * K) {base : ℕ}
    (hb : base + K ≤ vs.length) (h84 : w 84 = (vs.drop base).flatten) (h85 : (w 85).length = N * K)
    (h83 : (w 83).length = N * K) :
    (exec N K (dRow src) w) 84 = (vs.drop (base + K)).flatten ∧
      ((exec N K (dRow src) w) 85).length = N * K ∧
      ((exec N K (dRow src) w) 83).length = N * K ∧
      decRM N K ((exec N K (dRow src) w) 83) =
        decRM N K (w 83) + dotRow vs base (opd N K (w src)) K ∧
      ∀ j, j ∉ wr (dRow src) → (exec N K (dRow src) w) j = w j := by
  set x := opd N K (w src) with hxd
  have hx : x.length = N * K := length_takeD _ _
  set w1 := Function.update (Function.update w 86 (canonW N K x)) 89 (List.replicate K false)
    with hw1
  have hc1 : Consts N K w1 := consts_update (consts_update hc 86 (by decide) _) 89 (by decide) _
  have e1 : exec N K (dRow src) w = exec N K (.rep 89 dBody) w1 := by
    simp only [dRow, exec_ofList_cons, exec_ofList_nil, exec,
      Function.update_of_ne (show (4 : Fin 200) ≠ 86 by decide), hc.k]
    rfl
  have h89 : (w1 89).length = K := by simp [hw1]
  let P : ℕ → St → Prop := fun i w' =>
    Consts N K w' ∧ w' 84 = (vs.drop (base + i)).flatten ∧ (w' 85).length = N * K ∧
      w' 86 = rotBW N K i (canonW N K x) ∧ (w' 83).length = N * K ∧
      decRM N K (w' 83) = decRM N K (w 83) + dotRow vs base x i ∧
      ∀ j, j ∉ wr (dRow src) → w' j = w j
  have hP := exec_rep_inv (N := N) (K := K) 89 dBody (by decide) P w1
    ⟨hc1, by simp [hw1, h84], by simp [hw1, h85],
      by simp [hw1, rotBW, concatN_block (length_canonW N K hx)], by simp [hw1, h83],
      by simp [hw1, dotRow],
      fun j hj => by
        simp only [hw1]
        rw [Function.update_of_ne (fun e => hj (by subst e; rw [wr_dRow]; decide)),
          Function.update_of_ne (fun e => hj (by subst e; rw [wr_dRow]; decide))]⟩
    (fun i hi w' hw' _ => by
      obtain ⟨hc', h84', h85', h86', h83', hd', hf'⟩ := hw'
      rw [h89] at hi
      set w'' := Function.update w' 89 (w' 89).tail
      have hc'' : Consts N K w'' := consts_update hc' 89 (by decide) _
      have hiv : base + i < vs.length := by omega
      have hb := exec_dBody hK w'' hc'' (v := vs.getD (base + i) []) (hvs _ (by rw [List.getD_eq_getElem _ _ hiv]; exact List.getElem_mem hiv)) (by
          simp only [w'', Function.update_of_ne (show (84 : Fin 200) ≠ 89 by decide), h84']
          exact flatten_drop_succ hiv)
        (by simp only [w'', Function.update_of_ne (show (85 : Fin 200) ≠ 89 by decide)]; exact h85')
        hx hi (by simp only [w'', Function.update_of_ne (show (86 : Fin 200) ≠ 89 by decide)]; exact h86')
        (by simp only [w'', Function.update_of_ne (show (83 : Fin 200) ≠ 89 by decide)]; exact h83')
      obtain ⟨b84, b85, b86, b83, bd, bf⟩ := hb
      refine ⟨consts_exec hc'' _ rfl, by rw [b84, Nat.add_assoc], b85, b86, b83, ?_, fun j hj => ?_⟩
      · rw [bd]
        simp only [w'', Function.update_of_ne (show (83 : Fin 200) ≠ 89 by decide), hd', dotRow,
          Finset.sum_range_succ, add_assoc]
      · rw [bf j (fun hm => hj (mem_of_all rfl hm))]
        simp only [w'']
        rw [Function.update_of_ne (fun e => hj (by subst e; rw [wr_dRow]; decide))]
        exact hf' j hj)
  rw [h89] at hP
  obtain ⟨_, p84, p85, _, p83, pd, pf⟩ := hP
  exact ⟨e1 ▸ p84, e1 ▸ p85, e1 ▸ p83, e1 ▸ pd, fun j hj => e1 ▸ pf j hj⟩

theorem wr_ddotC : wr ddotC = [84, 83, 85, 86, 89, 89, 85, 84, 87, 88, 83, 86, 86, 89, 89, 85, 84,
    87, 88, 83, 86] := rfl

/-- **The digit dot product**: `Σ_{i<K} v_i d_i(m₀) + Σ_{i<K} v_{K+i} d_i(m₁)` for the stream
`v` of `2K` words on register `80` and the words `m₀`, `m₁` on `81`, `82`. -/
theorem exec_ddotC (hK : 0 < K) (w : St) (hc : Consts N K w) {vs : List (List Bool)}
    (hvs : ∀ x ∈ vs, x.length = N * K) (hl : vs.length = 2 * K) (h80 : w 80 = vs.flatten) :
    ((exec N K ddotC w) 83).length = N * K ∧
      decRM N K ((exec N K ddotC w) 83) =
        dotRow vs 0 (opd N K (w 81)) K + dotRow vs K (opd N K (w 82)) K ∧
      ∀ j, j ∉ wr ddotC → (exec N K ddotC w) j = w j := by
  set w1 := Function.update (Function.update (Function.update w 84 (w 80)) 83
    (List.replicate (N * K) false)) 85 (List.replicate (N * K) false) with hw1
  have e : exec N K ddotC w = exec N K (dRow 82) (exec N K (dRow 81) w1) := by
    simp only [ddotC, exec_ofList_cons, exec_ofList_nil, exec, hw1,
      Function.update_of_ne (show (2 : Fin 200) ≠ 84 by decide),
      Function.update_of_ne (show (2 : Fin 200) ≠ 83 by decide), hc.zero]
  have hc1 : Consts N K w1 :=
    consts_update (consts_update (consts_update hc 84 (by decide) _) 83 (by decide) _) 85
      (by decide) _
  obtain ⟨a84, a85, a83, ad, af⟩ := exec_dRow hK w1 hc1 81 hvs (base := 0) (by omega)
    (by simp [hw1, h80]) (by simp [hw1]) (by simp [hw1])
  have hc2 : Consts N K (exec N K (dRow 81) w1) := consts_exec hc1 _ rfl
  obtain ⟨b84, b85, b83, bd, bf⟩ := exec_dRow hK _ hc2 82 hvs (base := K) (by omega)
    (by rw [a84, zero_add]) a85 a83
  have h81 : w1 81 = w 81 := by simp [hw1]
  have h82 : exec N K (dRow 81) w1 82 = w 82 := by
    rw [af 82 (by rw [wr_dRow]; simp)]; simp [hw1]
  have h83 : w1 83 = List.replicate (N * K) false := by simp [hw1]
  refine ⟨?_, ?_, fun j hj => ?_⟩
  · rw [e]; exact b83
  · rw [e, bd, ad, h82, h81, h83, decRM_replicate, zero_add]
  · have hj1 : j ∉ wr (dRow 81) := fun hm => hj (mem_of_all rfl hm)
    have hj2 : j ∉ wr (dRow 82) := fun hm => hj (mem_of_all rfl hm)
    rw [e, bf j hj2, af j hj1]
    have h84 : j ≠ 84 := fun h => hj (by rw [h, wr_ddotC]; simp)
    have h83' : j ≠ 83 := fun h => hj (by rw [h, wr_ddotC]; simp)
    have h85 : j ≠ 85 := fun h => hj (by rw [h, wr_ddotC]; simp)
    rw [hw1, Function.update_of_ne h85, Function.update_of_ne h83', Function.update_of_ne h84]

end RingVM

end SigabaNeo.Tape
