import PE.Impl.DualUse.Prog.KeyTightLib
import PE.Impl.DualUse.Prog.PostCost

/-!
# Reading the key row back, with the gadget and the ring addition charged per tape

`ub_postCoreB` (`PE.Impl.DualUse.Prog.PostCost`) bounds the gadget row (`gadP`) and the ring
addition (`addRWP`) of `postCoreB` uniformly, every loop charged the uniform bound `M` (about
`375 M⁴` steps). Here the templates written by `tmplP` keep their own lengths (`tmplB`), and the two
programs are certified by the abstract interpreter (`absRun_gadB`, `absRun_addB`): each loop is
charged its own counter (`N`, `K`, `k`, …), every primitive the top `T` of the tapes.

**`ph_postCoreB_v`**: from tapes below `G`, `postCoreB` takes at most `postTV …` steps and leaves its
tapes `0`, `1` below `T = G + 1 + L + 1 + LT + 1 + L + 1 + LT`, the others blank.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

namespace PostV

open Sym

/-- The monomial `c · N^a K^b k^c` (exponents `e`; variable `0` the top). -/
def mo (c : ℕ) (e : List ℕ) : Poly := [(0 :: e, c)]

/-- The abstract store before the gadget: the templates of `postTmpl`, the top elsewhere. -/
def σP : Asg := List.replicate 8 pTop ++ [mo 1 [0, 1], mo 1 [1], mo 1 [1, 1], mo 1 [0, 0, 1],
  mo 2 [1, 1, 1]] ++ List.replicate 16 pTop ++ [mo 2 [1, 0, 1]] ++ List.replicate 24 pTop

/-- The abstract store after the gadget. -/
def oG : Asg := ((absRun 8 (Prog.map uG Prog.gadP) σP).map (·.1)).getD []
/-- The sweeps of the gadget. -/
def wG : Poly := ((absRun 8 (Prog.map uG Prog.gadP) σP).map (·.2)).getD []
/-- The abstract store after the ring addition. -/
def oA : Asg := ((absRun 8 (Prog.map uA Prog.addRWP) oG).map (·.1)).getD []
/-- The sweeps of the ring addition. -/
def wA : Poly := ((absRun 8 (Prog.map uA Prog.addRWP) oG).map (·.2)).getD []

set_option maxRecDepth 100000 in
theorem absRun_gadB : absRun 8 (Prog.map uG Prog.gadP) σP = some (oG, wG) := by decide +kernel

set_option maxRecDepth 100000 in
theorem absRun_addB : absRun 8 (Prog.map uA Prog.addRWP) oG = some (oA, wA) := by decide +kernel

theorem σP_top (j : Fin 54) (hj : j.val ∉ [8, 9, 10, 11, 12, 29]) : aGet σP j.val = pTop := by
  revert j; decide

end PostV

open PostV

/-- The values `T, N, K, k` of the variables. -/
def ρP (T N K k : ℕ) : List ℕ := [T, N, K, k]

/-- The uniform bound of `postCoreB` after its reading part, from `G`. -/
def postMd (L LT G : ℕ) : ℕ := G + 1 + L + 1 + LT + 1 + L + 1 + LT

/-- The time of `postCoreB` with the gadget and the addition charged per tape. -/
def postTV (L LT oW Zr N K k G : ℕ) : ℕ :=
  getT 0 L G + getT oW LT (G + 1 + L) + (2 * (G + 1 + L + 1 + LT + 1) + 3) +
    prefT L (G + 1 + L + 1 + LT) + prefT LT (G + 1 + L + 1 + LT + 1 + L) +
    (Zr + 1) * (2 * (postMd L LT G + 1) + 3) +
    tmplTT 53 (postTmpl N K k) (fun _ => postMd L LT G) +
    ((2 * postMd L LT G + 3) * Sym.pEval (ρP (postMd L LT G) N K k) wG +
      (2 * postMd L LT G + 3) * Sym.pEval (ρP (postMd L LT G) N K k) wA) +
    (2 * (postMd L LT G + 1) + 3) + (52 * (2 * (postMd L LT G + 1) + 3) + (2 * (postMd L LT G + 1) + 3))

theorem postTmpl_keys (N K k : ℕ) : ((postTmpl N K k).map Prod.fst).Nodup := by
  simp [postTmpl]

theorem postTmpl_ne (N K k : ℕ) : ∀ x ∈ postTmpl N K k, x.1 ≠ (53 : Fin 54) := by
  simp [postTmpl]

/-- The templates fit the abstract store `σP`. -/
theorem tmplB_postTmpl_le (N K k Md : ℕ) (hT : ∀ x ∈ postTmpl N K k, x.2 ≤ Md) :
    tmplB 53 (postTmpl N K k) (fun _ => Md) ≤ Sym.bnd (ρP Md N K k) σP := by
  intro j
  by_cases hj : j ∈ (postTmpl N K k).map Prod.fst
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hj
    rw [tmplB_key 53 _ _ (postTmpl_keys N K k) (postTmpl_ne N K k) x hx]
    simp only [postTmpl, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Sym.bnd, Sym.aGet, σP, mo, Sym.pEval, Sym.mEval, ρP] <;> ring_nf <;> exact le_rfl
  · have hv : j.val ∉ [8, 9, 10, 11, 12, 29] := by
      intro h; apply hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [postTmpl, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
      rcases h with h | h | h | h | h | h <;> [left; (right; left); (right; right; left);
        (right; right; right; left); (right; right; right; right; left);
        (right; right; right; right; right)] <;> exact Fin.ext h
    have htop : Sym.bnd (ρP Md N K k) σP j = Md := by
      simp only [Sym.bnd]; rw [σP_top j hv]; simp [Sym.pTop, Sym.pEval, Sym.mEval, ρP]
    rw [htop]
    by_cases hc : j = 53
    · subst hc
      exact tmplB_counter_le 53 _ _ le_rfl hT (postTmpl_ne N K k)
    · rw [tmplB_of_not_mem 53 _ _ j hc hj]

theorem tmplB_postTmpl_top (N K k Md : ℕ) (hT : ∀ x ∈ postTmpl N K k, x.2 ≤ Md) (j : Fin 54) :
    tmplB 53 (postTmpl N K k) (fun _ => Md) j ≤ Md :=
  tmplB_le 53 Md _ _ (fun _ => le_rfl) hT j

/-- **The per-tape bound of `postCoreB`.** -/
theorem ph_postCoreB_v (L LT oW Zr N K k G : ℕ)
    (hT : ∀ x ∈ postTmpl N K k, x.2 ≤ postMd L LT G) :
    Ph (postCoreB L LT oW Zr N K k) (fun _ => G) (postTV L LT oW Zr N K k G)
      (fun j => if j.val ≤ 1 then postMd L LT G else 0) := by
  set Md := postMd L LT G with hMd
  have p1 := ph_of_ub (β := fun _ => G) (fun _ => le_rfl) (ub_getAt (k := 54) 0 L 0 2 4 5 6 G)
  have p2 := ph_of_ub (β := fun _ => G + 1 + L) (fun _ => le_rfl) (ub_getAt (k := 54) oW LT 0 3 4 5 6 _)
  have p3 := ph_of_ub (β := fun _ => G + 1 + L + 1 + LT) (fun _ => le_rfl) (ub_clear (0 : Fin 54) _)
  have p4 := ph_of_ub (β := fun _ => G + 1 + L + 1 + LT) (fun _ => le_rfl) (ub_prefP L (2 : Fin 54) 0 4 5 _)
  have p5 := ph_of_ub (β := fun _ => G + 1 + L + 1 + LT + 1 + L) (fun _ => le_rfl)
    (ub_prefP LT (3 : Fin 54) 0 4 5 _)
  have p6 := ph_of_ub (β := fun _ => Md) (fun _ => le_rfl) (ub_tailsX (1 : Fin 54) Zr _)
  have p7 := ph_tmplP (53 : Fin 54) (postTmpl N K k) (fun _ => Md) (postTmpl_ne N K k)
  have p8 := ph_absRun absRun_gadB (ρP Md N K k) (tmplB_postTmpl_le N K k Md hT)
    (tmplB_postTmpl_top N K k Md hT)
  have p9 := ph_absRun absRun_addB (ρP Md N K k) (capB_le_bnd _ _) (capB_le_top _ _)
  have p10 := ph_prim (Prim.copy (1 : Fin 54) 28) (capB (ρP Md N K k) oA)
  have p11 := ph_clearL ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
    23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46,
    47, 48, 49, 50, 51, 52, 53] : List (Fin 54)) ((Prim.copy (1 : Fin 54) 28).lenT (capB (ρP Md N K k) oA))
  have hs : supB ((Prim.copy (1 : Fin 54) 28).lenT (capB (ρP Md N K k) oA)) ≤ Md := by
    refine supB_le_of fun t => ?_
    simp only [Prim.lenT, Function.update_apply]
    split_ifs
    · exact capB_le_top _ _ _
    · exact capB_le_top _ _ _
  have hs' : supB (capB (ρP Md N K k) oA : Fin 54 → ℕ) ≤ Md := supB_le_of fun t => capB_le_top _ _ _
  rw [postCoreB]
  refine (p1.seq (p2.seq (p3.seq (p4.seq (p5.seq (p6.seq (p7.seq (p8.seq (p9.seq
    (p10.seq p11)))))))))).mono le_rfl ?_ ?_
  · have hl : ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
        26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50,
        51, 52, 53] : List (Fin 54)).length = 52 := rfl
    rw [hl]
    have ht : Sym.top (ρP Md N K k) = Md := rfl
    rw [ht]
    have e3 := Nat.mul_le_mul_left 52 (show 2 * (supB ((Prim.copy (1 : Fin 54) 28).lenT
      (capB (ρP Md N K k) oA)) + 1) + 3 ≤ 2 * (Md + 1) + 3 by omega)
    simp only [postTV, ← hMd]
    omega
  · intro j
    by_cases hj : j.val ≤ 1
    · simp only [hj, ↓reduceIte]
      split_ifs
      · exact Nat.zero_le _
      · simp only [Prim.lenT, Function.update_apply]
        split_ifs <;> exact capB_le_top _ _ _
    · have hm : j ∈ ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
          25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
          49, 50, 51, 52, 53] : List (Fin 54)) := by revert j; decide
      simp [hm, hj]

end AdvancedEncryption.DualUse.Prog
