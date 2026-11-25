import PE.Impl.RingBTVW.Prog.KeyTightTry
import PE.Impl.RingBTVW.Prog.KeyTightBfX
import PE.Impl.RingBTVW.Prog.KeyGenCost

/-!
# The tail of the window branch of `KeyGen`, per tape

After the key-row block only tapes `0` and `2` are nonblank (`v02 Gb`, `ph_bfX_v`). The tail of the
window branch writes the public key (tape `1`), `e`, `t` (`90`, `91`), the norm word and `powW`
(tapes `4`, `5`, `K` bits each), the templates of the key try (`tmplB`, at their lengths), runs the
key try (`ph_keyTryR_v`: each loop charged its own counter), frames the output and clears.

**`ph_winTail_v`**: from `v02 Gb`, the tail takes at most `winTV …` steps and leaves every tape below
`3 T + 1`, `T = Gb + 1 + P + 1 + 2k N K` the top of the key try.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg
open scoped SigabaNeo.Tape.Prog
open SigabaNeo.Tape.Prog (frP frT)
open SigabaNeo.Lattices.Algo

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The top of the key try: `Gb`, then the public key and the words `e`, `t` read from tape `0`. -/
def winTop (Gb : ℕ) : ℕ := Gb + 1 + lenPK hk c + 1 + 2 * k * (N * K)

/-- The values of the variables of `σKR`: the top, `N, K, k, d, nT, P, B, m`. -/
def ρK (Gb : ℕ) (cf : KeyCfg) : List ℕ :=
  [winTop hk c Gb, N, K, k, c.d, AdvancedEncryption.RingBTVW.Algo.nT k, lenPK hk c, cf.B, cf.m]

/-- The templates of the key try fit `σKR`. -/
theorem keyTmplR_fit (Gb : ℕ) (cf : KeyCfg) : ∀ x ∈ keyTmplR hk c cf,
    x.2 ≤ Sym.pEval (ρK hk c Gb cf) (Sym.aGet KeyV.σKR x.1.val) := by
  intro x hx
  simp only [keyTmplR, keyTmpl, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl | rfl <;>
    simp [KeyV.σKR, KeyV.mo, KeyV.qK, KeyV.qN, KeyV.qNK, KeyV.qP, KeyV.qm, Sym.aGet, Sym.pEval,
      Sym.mEval, ρK] <;> ring_nf <;> omega

theorem keyTmplR_ne120 (cf : KeyCfg) : ∀ x ∈ keyTmplR hk c cf, x.1 ≠ (120 : Fin 256) := fun x hx e => by
  have := List.mem_map_of_mem (f := fun x : Fin 256 × ℕ => x.1.val) hx
  rw [keyTmplR_keys, e] at this; simp at this

theorem keyTmplR_nodup (cf : KeyCfg) : ((keyTmplR hk c cf).map Prod.fst).Nodup := by
  have h := keyTmplR_keys (hk := hk) (c := c) cf
  have : ((keyTmplR hk c cf).map Prod.fst).map Fin.val = [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17,
      18, 19, 20, 21, 22, 23, 24, 25, 92, 93, 100] := by rw [List.map_map]; exact h
  exact List.Nodup.of_map _ (by rw [this]; decide)

theorem mem_keys_iff (cf : KeyCfg) (t : Fin 256) : t ∈ (keyTmplR hk c cf).map Prod.fst ↔
    t.val ∈ [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 92, 93, 100] := by
  have e : ((keyTmplR hk c cf).map Prod.fst).map Fin.val = [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
      17, 18, 19, 20, 21, 22, 23, 24, 25, 92, 93, 100] := by
    rw [List.map_map]; exact keyTmplR_keys cf
  constructor
  · intro h; rw [← e]; exact List.mem_map_of_mem h
  · intro h
    rw [← e] at h
    obtain ⟨u, hu, e'⟩ := List.mem_map.mp h
    rwa [Fin.ext e'] at hu

set_option maxRecDepth 100000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 100000 in
theorem σKR_classes : ∀ j : Fin 101,
    j.val ∉ [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 92, 93, 100] →
    j.val ∉ [3, 41] →
    (j.val ∈ [0, 1, 2, 90, 91] ∧ Sym.aGet KeyV.σKR j.val = Sym.pTop) ∨
    (j.val ∈ [4, 5] ∧ Sym.aGet KeyV.σKR j.val = KeyV.qK) ∨
    (j.val ∉ [0, 1, 2, 90, 91, 4, 5] ∧ Sym.aGet KeyV.σKR j.val = ([] : Sym.Poly)) := by
  decide +kernel

/-- The tail of the window branch, after the key-row block. -/
noncomputable def winTail (cf : KeyCfg) : XProg 256 :=
  XProg.seq (prefP (lenPK hk c) 0 1 100 101) <| XProg.seq (etP hk c) <|
  XProg.seq (putW 4 cf.sW) <| XProg.seq (putW 5 (powW K (cf.B - 1))) <|
  XProg.seq (tmplP 120 (keyTmplR hk c cf)) <|
  XProg.seq (XProg.frame eKR (XProg.prog ProgKeyR.keyTryRCoinsP)) <|
  XProg.seq (XProg.prog (Prog.map uF frP)) (clearL keyClrR)

theorem winR_eq (bfX : XProg 256) (W : ℕ) (cf : KeyCfg) :
    winR hk c bfX W cf = XProg.seq (XProg.prog (.prim (.tail 1))) (XProg.seq bfX (winTail hk c cf)) :=
  rfl

theorem preserves_etP (t : Fin 256) (h : t ∉ [91, 102, 90, 103, 104]) : (etP hk c).Preserves t := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨⟨by simp [Prog.Preserves, Prim.writes, h1], preserves_tailsP (Ne.symm h1) _,
    by simp [Prog.Preserves, Prim.writes, h2], preserves_tailsP (Ne.symm h2) _⟩,
    preserves_prefP (Ne.symm h4) (Ne.symm h3) (Ne.symm h5), ?_⟩
  simp [XProg.Preserves, Prog.Preserves, Prim.writes, h2]

/-- The time of the tail of the window branch. -/
def winTV (Gb : ℕ) (cf : KeyCfg) : ℕ :=
  prefT (lenPK hk c) Gb + etT (lenPK hk c + 2 * k * (N * K)) (lenPK hk c) (2 * k * (N * K))
      (Gb + 1 + lenPK hk c) +
    (cf.sW.length + 1) * (2 * (winTop hk c Gb + cf.sW.length + 1) + 3) +
    ((powW K (cf.B - 1)).length + 1) * (2 * (winTop hk c Gb + (powW K (cf.B - 1)).length + 1) + 3) +
    24 * ((2 * winTop hk c Gb + 1) * (4 * winTop hk c Gb + 12)) +
    (coinT (winTop hk c Gb) cf.m + (2 * winTop hk c Gb + 3) * Sym.pEval (ρK hk c Gb cf) KeyV.wKR) +
    frT (winTop hk c Gb) +
    (31 * (2 * (3 * winTop hk c Gb + 1 + 1) + 3) + (2 * (3 * winTop hk c Gb + 1 + 1) + 3))

set_option maxHeartbeats 1000000 in
/-- **The tail of the window branch, per tape.** -/
theorem ph_winTail_v (Gb : ℕ) (cf : KeyCfg) (hsW : cf.sW.length ≤ K)
    (hpw : (powW K (cf.B - 1)).length ≤ K) (hKT : K ≤ winTop hk c Gb)
    (hTm : ∀ x ∈ keyTmplR hk c cf, x.2 ≤ winTop hk c Gb) :
    Ph (winTail hk c cf) (v02 Gb) (winTV hk c Gb cf) (fun _ => 3 * winTop hk c Gb + 1) := by
  set T := winTop hk c Gb with hT
  set P := lenPK hk c with hP
  set E := 2 * k * (N * K) with hE
  have hTP : Gb + 1 + P ≤ T := by simp only [hT, winTop]; omega
  have hGT : Gb ≤ T := by omega
  -- the public key
  set β1 : Fin 256 → ℕ := fun i => if i ∈ [1, 100, 101] then Gb + 1 + P else v02 Gb i with hβ1
  have q1 : Ph (prefP P 0 1 100 101) (v02 Gb) (prefT P Gb) β1 :=
    ph_of_ub_ws [1, 100, 101] (fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      exact preserves_prefP (Ne.symm hi.2.1) (Ne.symm hi.1) (Ne.symm hi.2.2))
      (ub_prefP P 0 1 100 101 Gb) (fun i => by simp only [v02]; split_ifs <;> omega)
  -- `e`, `t`
  set β2 : Fin 256 → ℕ := fun i => if i ∈ [91, 102, 90, 103, 104] then T else β1 i with hβ2
  have q2 : Ph (etP hk c) β1 (etT (P + E) P E (Gb + 1 + P)) β2 :=
    ph_of_ub_ws [91, 102, 90, 103, 104] (fun i hi => preserves_etP hk c i hi)
      (ub_etP hk c (Gb + 1 + P)) (fun i => by
        simp only [hβ1, v02]; split_ifs <;> omega)
  have hβ2T : ∀ i, β2 i ≤ T := fun i => by simp only [hβ2, hβ1, v02]; split_ifs <;> omega
  have hβ24 : β2 4 = 0 := by simp [hβ2, hβ1, v02]
  have hβ25 : β2 5 = 0 := by simp [hβ2, hβ1, v02]
  -- the norm word and `powW`
  set β3 := Function.update β2 4 (β2 4 + cf.sW.length) with hβ3
  have q3 := ph_putW (4 : Fin 256) cf.sW β2
  have hβ3T : ∀ i, β3 i ≤ T := fun i => by
    simp only [hβ3, Function.update_apply]; split_ifs
    · rw [hβ24]; omega
    · exact hβ2T i
  set β4 := Function.update β3 5 (β3 5 + (powW K (cf.B - 1)).length) with hβ4
  have q4 := ph_putW (5 : Fin 256) (powW K (cf.B - 1)) β3
  have hβ35 : β3 5 = 0 := by simp [hβ3, hβ25]
  have hβ4T : ∀ i, β4 i ≤ T := fun i => by
    simp only [hβ4, Function.update_apply]; split_ifs
    · rw [hβ35]; omega
    · exact hβ3T i
  -- the templates
  set β5 := tmplB 120 (keyTmplR hk c cf) β4 with hβ5
  have q5 := ph_tmplP (120 : Fin 256) (keyTmplR hk c cf) β4 (keyTmplR_ne120 hk c cf)
  have hβ5T : ∀ i, β5 i ≤ T := tmplB_le 120 T _ β4 hβ4T hTm
  have hcount := tmplTT_le (120 : Fin 256) T (keyTmplR hk c cf) β4 hβ4T hTm
  have hlen : (keyTmplR hk c cf).length = 23 := rfl
  rw [hlen] at hcount
  -- the key try
  have h25 : β5 25 = cf.m := tmplB_key 120 _ β4 (keyTmplR_nodup hk c cf) (keyTmplR_ne120 hk c cf)
    (25, cf.m) (by simp [keyTmplR, keyTmpl])
  have hfit : ∀ j : Fin 101, β5 (eKR j) ≤ Sym.pEval (ρK hk c Gb cf) (Sym.aGet KeyV.σKR j.val) := by
    intro j
    by_cases hkey : eKR j ∈ (keyTmplR hk c cf).map Prod.fst
    · obtain ⟨x, hx, hxj⟩ := List.mem_map.mp hkey
      rw [← hxj, hβ5, tmplB_key 120 _ β4 (keyTmplR_nodup hk c cf) (keyTmplR_ne120 hk c cf) x hx]
      have := keyTmplR_fit hk c Gb cf x hx
      rwa [hxj, eKR_val] at this
    · have hne : eKR j ≠ 120 := fun e => by
        have := congrArg Fin.val e; rw [eKR_val] at this; have := j.isLt; simp at this; omega
      rw [hβ5, tmplB_of_not_mem 120 _ β4 _ hne hkey]
      rw [mem_keys_iff hk c cf, eKR_val] at hkey
      by_cases h341 : j.val ∈ [3, 41]
      · have hv : j.val = 3 ∨ j.val = 41 := by simpa using h341
        have hs : Sym.aGet KeyV.σKR j.val = KeyV.qm := by rcases hv with h | h <;> rw [h] <;> rfl
        have hb : β4 (eKR j) = 0 := by
          have hv' : (eKR j).val = 3 ∨ (eKR j).val = 41 := by rw [eKR_val]; exact hv
          simp only [hβ4, hβ3, hβ2, hβ1, v02, Function.update_apply]
          rcases hv' with h | h <;> simp [Fin.ext_iff, h]
        rw [hb]; exact Nat.zero_le _
      · rcases σKR_classes j hkey h341 with ⟨hm, hs⟩ | ⟨hm, hs⟩ | ⟨hm, hs⟩
        · rw [hs]
          have : Sym.pEval (ρK hk c Gb cf) Sym.pTop = T := by
            simp [Sym.pTop, Sym.pEval, Sym.mEval, ρK]; omega
          rw [this]; exact hβ4T _
        · rw [hs]
          have : Sym.pEval (ρK hk c Gb cf) KeyV.qK = K := by
            simp [KeyV.qK, KeyV.mo, Sym.pEval, Sym.mEval, ρK]
          rw [this]
          have hv : (eKR j).val = 4 ∨ (eKR j).val = 5 := by rw [eKR_val]; simpa using hm
          simp only [hβ4, hβ3, Function.update_apply]
          rcases hv with h | h
          · have e4 : eKR j = 4 := Fin.ext h
            simp [e4, hβ24, hsW]
          · have e5 : eKR j = 5 := Fin.ext h
            simp [e5, hβ25, hpw]
        · rw [hs]
          have hv := hm
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
          have hk' := hkey
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk'
          have h341' := h341
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h341'
          simp only [hβ4, hβ3, hβ2, hβ1, v02, Function.update_apply, Fin.ext_iff, eKR_val,
            List.mem_cons, List.not_mem_nil, or_false]
          have := j.isLt
          split_ifs <;> simp_all <;> omega
  have hin : Function.update (Function.update (fun j => β5 (eKR j)) 3 (β5 (eKR 25))) 41
      (β5 (eKR 25)) ≤ Sym.bnd (ρK hk c Gb cf) KeyV.σKR := by
    intro j
    simp only [Function.update_apply]
    have h25' : β5 (eKR 25) = cf.m := h25
    split_ifs with h1 h2
    · subst h1
      rw [h25']; simp [Sym.bnd, KeyV.σKR, KeyV.qm, KeyV.mo, Sym.aGet, Sym.pEval, Sym.mEval, ρK]
    · subst h2
      rw [h25']; simp [Sym.bnd, KeyV.σKR, KeyV.qm, KeyV.mo, Sym.aGet, Sym.pEval, Sym.mEval, ρK]
    · exact hfit j
  have htop : ∀ j : Fin 101, β5 (eKR j) ≤ Sym.top (ρK hk c Gb cf) := fun j => hβ5T _
  have q6 := ph_frame eKR (ph_keyTryR_v (ρK hk c Gb cf) (fun j => β5 (eKR j)) hin htop)
  have hβ6T : ∀ t, embedF eKR β5 (capB (ρK hk c Gb cf) KeyV.oKR) t ≤ T := by
    intro t
    rcases embedF_cases eKR β5 (capB (ρK hk c Gb cf) KeyV.oKR) t with ⟨-, e⟩ | ⟨j, -, e⟩
    · rw [e]; exact hβ5T t
    · rw [e]; exact capB_le_top _ _ _
  have q7 := ph_of_ub hβ6T (show UB (XProg.prog (Prog.map uF frP)) T (frT T) (3 * T + 1) from
    fun ℓ hℓ => ubp_frP_map uF T ℓ hℓ)
  have q8 := ph_of_ub (β := fun _ : Fin 256 => 3 * T + 1) (fun _ => le_rfl) (ub_clearL (3 * T + 1) keyClrR)
  have hcl : keyClrR.length = 31 := rfl
  rw [hcl] at q8
  have q6' : Ph (XProg.frame eKR (XProg.prog ProgKeyR.keyTryRCoinsP)) β5
      (coinT T cf.m + (2 * T + 3) * Sym.pEval (ρK hk c Gb cf) KeyV.wKR)
      (embedF eKR β5 (capB (ρK hk c Gb cf) KeyV.oKR)) :=
    q6.mono le_rfl (le_of_eq (by
      have e1 : Sym.top (ρK hk c Gb cf) = T := rfl
      have e2 : β5 (eKR 25) = cf.m := h25
      rw [e1, e2])) le_rfl
  refine (q1.seq (q2.seq (q3.seq (q4.seq (q5.seq (q6'.seq (q7.seq q8))))))).mono le_rfl ?_ le_rfl
  have s2 := supB_le_of hβ2T
  have s3 := supB_le_of hβ3T
  have m3 : (cf.sW.length + 1) * (2 * (supB β2 + cf.sW.length + 1) + 3) ≤
      (cf.sW.length + 1) * (2 * (T + cf.sW.length + 1) + 3) := Nat.mul_le_mul_left _ (by omega)
  have m4 : ((powW K (cf.B - 1)).length + 1) * (2 * (supB β3 + (powW K (cf.B - 1)).length + 1) + 3) ≤
      ((powW K (cf.B - 1)).length + 1) * (2 * (T + (powW K (cf.B - 1)).length + 1) + 3) :=
    Nat.mul_le_mul_left _ (by omega)
  simp only [winTV, ← hT, ← hP, ← hE]
  omega

end AdvancedEncryption.RingBTVW.Prog
