import PE.Impl.DualUse.Prog.CompCost
import PE.Impl.DualUse.Prog.SetupCost

/-!
# The setup components at the handlers' width

The state word of the handlers is `true :: inst.enc i` (the decoder's marker bit). The setup
component drops the marker (`dropHead`: one `tail` of tape `0`) and runs the setup program of
the reduction (`setup3P`, `setup5P`, `setupIP`, with the χ sampler `chiP` of `confP`), lifted to
`XProg 256` (`liftP`).

* `law_setup3D`, `law_setup5D`, `law_setupID`: on `true :: inst.enc i` and the date, the law of the
  packed secret (`(inst ⊗ sec).enc (i, σ)`, `σ ← setup x`);
* `time_setup3D` …: the time bound of the setup program plus one sweep;
* at `confP`, inputs of at most `2^180` bits: **`time_setup3D_conf`**, `time_setup5D_conf`,
  `time_setupID_conf` (`≤ 2^380`), and the output bounds `len_setup*D_conf` (`≤ 2^181`).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.XProg Matrix
  AdvancedEncryption.RingBTVW Cslib Cslib.Probability AdvancedEncryption.DualUse.Params
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow

/-- Drop the first bit of tape `0`, run `p`, clear every tape but `0`. -/
def dropHead (p : XProg 7) : XProg 7 := seq (prog (.prim (.tail 0))) (seq p clrS)

theorem law_dropHead (p : XProg 7) (w x : List Bool) {β : Type} {μ : PMF β}
    {f : β → List Bool} (hp : p.law (ioS (R := 5) w x []) = μ.map fun v => ioS (R := 5) (f v) [] []) :
    (dropHead p).law (ioS (R := 5) (true :: w) x []) = μ.map fun v => ioS (R := 5) (f v) [] [] := by
  rw [dropHead, law_seq, law_prim, PMF.pure_bind, law_seq]
  have e : Function.update (ioS (R := 5) (true :: w) x []) 0
      ((ioS (R := 5) (true :: w) x [] 0).tail) = ioS (R := 5) w x [] := by
    funext t; fin_cases t <;> simp [ioS]
  simp only [Prim.apply]
  rw [e, hp, PMF.bind_map]
  simp only [Function.comp_def, law_clrS]
  rw [show ∀ g : β → Store 7, (μ.bind fun v => PMF.pure (g v)) = μ.map g from
    fun g => PMF.bind_pure_comp g μ]
  congr 1
  funext v
  funext t
  fin_cases t <;> simp [ioS]

theorem wf_dropHead {p : XProg 7} (hp : p.WF) : (dropHead p).WF := ⟨trivial, hp, wf_clrS⟩

/-- Clearing from bounds below `M`. -/
theorem clrS_bounds' {ℓ : Fin 7 → ℕ} {M : ℕ} (hℓ : ∀ i, ℓ i ≤ M) :
    timeBoundT clrS ℓ ≤ 6 * (2 * (M + 1) + 3) ∧
      lenBoundT clrS ℓ = fun t => if t = 0 then ℓ 0 else 0 := by
  have h := (VB.prim (.clear (1 : Fin 7)) hℓ).seq ((VB.prim (M := M) (.clear (2 : Fin 7))
    (a := (Prim.clear (1 : Fin 7)).lenT ℓ) ?_).seq ((VB.prim (M := M) (.clear (3 : Fin 7)) ?_).seq
    ((VB.prim (M := M) (.clear (4 : Fin 7)) ?_).seq ((VB.prim (M := M) (.clear (5 : Fin 7)) ?_).seq
    (VB.prim (M := M) (.clear (6 : Fin 7)) ?_)))))
  · refine ⟨((h ℓ le_rfl).1).trans (le_of_eq (by ring)), ?_⟩
    funext t; fin_cases t <;> rfl
  all_goals intro i; simp only [Prim.lenT, Function.update_apply]; split_ifs <;> first
    | exact Nat.zero_le _ | exact hℓ i

theorem time_dropHead (p : XProg 7) (a b M : ℕ)
    (hM : ∀ i, lenBoundT p (io2 (R := 5) a b 0) i ≤ M) :
    timeBoundT (dropHead p) (io2 (R := 5) a b 0) ≤
      (2 * (a + b + 1) + 3) + (timeBoundT p (io2 (R := 5) a b 0) + 6 * (2 * (M + 1) + 3)) := by
  have hl : (Prim.tail (0 : Fin 7)).lenT (io2 (R := 5) a b 0) ≤ io2 a b 0 := fun i => by
    simp only [Prim.lenT, Function.update_apply]; split_ifs with h
    · subst h; omega
    · exact le_rfl
  refine Nat.add_le_add ?_ (Nat.add_le_add (timeBoundT_mono p hl)
    (clrS_bounds' fun i => ((lenBoundT_mono p hl) i).trans (hM i)).1)
  show 2 * (supB _ + (Prim.tail (0 : Fin 7)).pad) + 3 ≤ _
  have := supB_le_of (ℓ := io2 (R := 5) a b 0) (M := a + b) fun i => by
    simp only [io2]; split_ifs <;> omega
  simp only [Prim.pad]; omega

theorem len_clrS (ℓ : Fin 7 → ℕ) : lenBoundT clrS ℓ = fun t => if t = 0 then ℓ 0 else 0 := by
  funext t; fin_cases t <;> rfl

theorem len_dropHead (p : XProg 7) (a b L : ℕ) (hL : lenBoundT p (io2 (R := 5) a b 0) 0 ≤ L) :
    lenBoundT (dropHead p) (io2 (R := 5) a b 0) ≤ io2 (R := 5) L 0 0 := by
  have hl : (Prim.tail (0 : Fin 7)).lenT (io2 (R := 5) a b 0) ≤ io2 a b 0 := fun i => by
    simp only [Prim.lenT, Function.update_apply]; split_ifs with h
    · subst h; omega
    · exact le_rfl
  show lenBoundT clrS (lenBoundT p ((Prim.tail (0 : Fin 7)).lenT (io2 (R := 5) a b 0))) ≤ _
  rw [len_clrS]
  have h0 := (lenBoundT_mono p hl) 0
  intro t
  simp only [io2]
  split_ifs <;> simp_all <;> omega

/-- The length bound of an appended tail. -/
theorem len_appendTail {tl : XProg 7} {B : Bnd} (h : ATBb tl B) (a b : ℕ) :
    lenBoundT (XProg.seq (appendTapeP 0 1 3 4) tl) (io2 (R := 5) a b 0) ≤
      shp 0 (a + b + B.a) (max b B.S₀ + B.s) := by
  set S := max b B.S₀
  have hℓ : io2 (R := 5) a b 0 ≤ shp (0 : Fin 7) a S := fun i => by
    simp only [io2, shp]; split_ifs <;> simp_all <;> omega
  obtain ⟨-, h2⟩ := appendTape_bounds (le_max_left b _) hℓ (by simp [io2])
  exact (lenBoundT_mono tl h2).trans (h (a + b) S (le_max_right _ _)).2

theorem two54 : (5 : ℕ) ≤ 254 := by norm_num

/-! ### The components -/

/-- **The setup component of hybrid 3.** -/
noncomputable def setup3D : XProg 256 := liftP two54 (dropHead (setup3P hkp confP chiP))
/-- **The setup component of hybrid 5.** -/
noncomputable def setup5D : XProg 256 := liftP two54 (dropHead (setup5P hkp confP))
/-- **The setup component of the ideal side.** -/
noncomputable def setupID : XProg 256 := liftP two54 (dropHead (setupIP hkp confP chiP))

theorem wf_setup3D : setup3D.WF := wf_dropHead wf_setup3P_conf
theorem wf_setup5D : setup5D.WF := wf_dropHead (wf_setup5P hkp confP)
theorem wf_setupID : setupID.WF := wf_dropHead wf_setupIP_conf

theorem law_setup3D (ab : Inst3T Np Kp kp) (x : Date) :
    setup3D.law (io2 (R := 254) (true :: (inst3Enc (N := Np) (K := Kp) (k := kp)).enc ab)
      (encDate x) []) =
      (setup3 hkp confP x).map fun σ => io2 (R := 254)
        (((inst3Enc (N := Np) (K := Kp) (k := kp)).prod (sec3Enc hkp confP)).enc (ab, σ)) [] [] :=
  law_liftP_map _ (law_dropHead _ _ _ (law_setup3P_conf ab x))

theorem law_setupID (ab : Inst3T Np Kp kp) (x : Date) :
    setupID.law (io2 (R := 254) (true :: (inst3Enc (N := Np) (K := Kp) (k := kp)).enc ab)
      (encDate x) []) =
      (setupI hkp confP x).map fun σ => io2 (R := 254)
        (((inst3Enc (N := Np) (K := Kp) (k := kp)).prod (secIEnc hkp confP)).enc (ab, σ)) [] [] :=
  law_liftP_map _ (law_dropHead _ _ _ (law_setupIP_conf ab x))

theorem law_setup5D (i : Pub (Fin confP.d) (Rg Np Kp) kp × Pub (Fin confP.d) (Rg Np Kp) kp)
    (x : Date) :
    setup5D.law (io2 (R := 254) (true :: (inst5Enc (N := Np) (K := Kp) (k := kp) confP.d).enc i)
      (encDate x) []) =
      (setup5 hkp confP x).map fun σ => io2 (R := 254)
        (((inst5Enc (N := Np) (K := Kp) (k := kp) confP.d).prod (sec5Enc hkp confP)).enc (i, σ))
          [] [] :=
  haveI := dp_ne
  law_liftP_map _ (law_dropHead _ _ _ (law_setup5P hkp confP Np_pos Kp_pos i x))

end AdvancedEncryption.DualUse.Prog

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.DualUse.Params
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow

open SigabaNeo.Encode in
theorem confP_w : confP.w = 512 := rfl

open SigabaNeo.Encode

/-! ### The counts as arithmetic -/

section Counts

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

theorem nW_eq : nW hk c = nA * (2 * (2 * k * (k * N))) * (2 * k) * c.d := by
  simp [nW, len_JC, len_fin]

theorem nR_eq : nR hk c = nA * (2 * k) * c.d := by
  show (Enum.list (α := Fin nA × RingBTVW.Col k)).length * (List.finRange c.d).length = _
  simp [Enum.length_prod, len_fin, len_col]

theorem nE_eq : nE (N := N) hk = nA * (2 * (2 * k * (k * N))) * (2 * k) * N := by
  simp only [nE, Enum.length_prod, len_Attr, len_Index, len_col, len_fin]

theorem nPsi_eq : nPsi (N := N) hk = nA * (2 * (2 * k * (N * K))) := by
  show (Enum.list (α := Fin nA)).length * ((Enum.list (α := Fin 2)).length *
    ((Enum.list (α := RingBTVW.Col k)).length * (N * K))) = _
  simp only [len_fin, len_col]

theorem nC0_eq : nC0 (N := N) (K := K) c = c.d * (N * K) := by simp [nC0, len_fin]

theorem nC1_eq : nC1 (N := N) (K := K) (k := k) = (1 + (2 * k + 2 * k)) * (N * K) := by
  simp [nC1, len_fin, len_trap]

theorem nCj_eq : nCj (N := N) hk = nA * (2 * (2 * k * (k * N))) * (2 * k * (N * K)) := by
  simp only [nCj, len_AI, len_fin, len_col]; ring

theorem lenFin (n : ℕ) : (Enum.list (α := Fin n)).length = n := len_fin n

end Counts


section Eval

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000

theorem lbTail3_num {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (hN : N = 2 ^ 34)
    (hK : K = 2 ^ 25) (hk' : k = 2 ^ 25 + 1) (hd : c.d = 2 ^ 61) (hw : c.w = 512) {A : ℕ}
    (hA : A = 2 ^ 25) :
    (lbTail3 hk c (Bnd.prim A 64) ⟨2 ^ 40, 2 ^ 40⟩).w ≤ 2 ^ 200 ∧
      (lbTail3 hk c (Bnd.prim A 64) ⟨2 ^ 40, 2 ^ 40⟩).E ≤ 2 ^ 200 := by
  simp only [lbTail3, lbRest, LB.seq, LB.cnt, lbCoins, lbZeros, lbEntB, lbEntF, LB.coin, LB.prim,
    bRest, bCoins, bZeros, bCoin, bEntB, bEntF, Bnd.seq, Bnd.count, Bnd.prim, nW_eq, nR_eq, nE_eq,
    lenFin, len_col, hd, hw]
  subst hN hK hk' hA
  norm_num

theorem lbTailI_num {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (hN : N = 2 ^ 34)
    (hK : K = 2 ^ 25) (hk' : k = 2 ^ 25 + 1) (hd : c.d = 2 ^ 61) (hw : c.w = 512) {A : ℕ}
    (hA : A = 2 ^ 25) :
    (lbTailI hk c (Bnd.prim A 64) ⟨2 ^ 40, 2 ^ 40⟩).w ≤ 2 ^ 200 ∧
      (lbTailI hk c (Bnd.prim A 64) ⟨2 ^ 40, 2 ^ 40⟩).E ≤ 2 ^ 200 := by
  simp only [lbTailI, lbEncCoins, lbCt, LB.seq, LB.cnt, lbCoins, lbZeros, lbEntB, lbEntF, LB.coin,
    LB.prim, bEncCoins, bCt, bCoins, bZeros, bCoin, bEntB, bEntF, Bnd.seq, Bnd.count, Bnd.prim,
    nW_eq, nR_eq, nE_eq, nPsi_eq, nC0_eq, nC1_eq, nCj_eq, lenFin, len_col, len_trap, hd, hw]
  subst hN hK hk' hA
  norm_num

theorem kp_eq : kp = 2 ^ 25 + 1 := by rw [kp, Kp_def]

theorem lbTail3_conf : (lbTail3 hkp confP bChi ⟨2 ^ 40, 2 ^ 40⟩).w ≤ 2 ^ 200 ∧
    (lbTail3 hkp confP bChi ⟨2 ^ 40, 2 ^ 40⟩).E ≤ 2 ^ 200 := by
  rw [lbTail3_congr hkp confP _ bChi_a bChi_s]
  exact lbTail3_num hkp confP Np_def Kp_def kp_eq confP_d confP_w Kp_def

theorem lbTailI_conf : (lbTailI hkp confP bChi ⟨2 ^ 40, 2 ^ 40⟩).w ≤ 2 ^ 200 ∧
    (lbTailI hkp confP bChi ⟨2 ^ 40, 2 ^ 40⟩).E ≤ 2 ^ 200 := by
  rw [lbTailI_congr hkp confP _ bChi_a bChi_s]
  exact lbTailI_num hkp confP Np_def Kp_def kp_eq confP_d confP_w Kp_def

theorem tail5_conf : wTail5 hkp confP ≤ 2 ^ 200 ∧ eTail5 hkp confP ≤ 2 ^ 200 ∧
    s5 hkp confP ≤ 2 ^ 181 := by
  simp only [wTail5, eTail5, s5, nW_eq, nR_eq, nE_eq, lenFin, len_col]
  simp only [confP_d, confP_w, kp, Kp_def, Np_def]
  norm_num

theorem cntSum_conf : 10 + Kp + cntSum hkp confP ≤ 2 ^ 181 := by
  simp only [cntSum, nW_eq, nR_eq, nE_eq, nPsi_eq, nC0_eq, nC1_eq, nCj_eq, lenFin, len_col]
  simp only [confP_d, confP_w, kp, Kp_def, Np_def]
  norm_num

theorem bTail3_as {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (Bχ : Bnd) :
    (bTail3 hk c Bχ).a = (bTail3 hk c (Bnd.prim Bχ.a Bχ.s)).a ∧
      (bTail3 hk c Bχ).s = (bTail3 hk c (Bnd.prim Bχ.a Bχ.s)).s := by
  simp only [bTail3, bRest, Bnd.seq, Bnd.count, Bnd.prim, bCoins, bZeros, bEntB, bEntF, bCoin]
  exact ⟨trivial, trivial⟩

theorem bTailI_as {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (Bχ : Bnd) :
    (bTailI hk c Bχ).a = (bTailI hk c (Bnd.prim Bχ.a Bχ.s)).a ∧
      (bTailI hk c Bχ).s = (bTailI hk c (Bnd.prim Bχ.a Bχ.s)).s := by
  simp only [bTailI, bEncCoins, bCt, Bnd.seq, Bnd.count, Bnd.prim, bCoins, bZeros, bEntB, bEntF,
    bCoin]
  exact ⟨trivial, trivial⟩

theorem bTail3_as_num {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (hN : N = 2 ^ 34)
    (hK : K = 2 ^ 25) (hk' : k = 2 ^ 25 + 1) (hd : c.d = 2 ^ 61) (hw : c.w = 512) {A : ℕ}
    (hA : A = 2 ^ 25) :
    (bTail3 hk c (Bnd.prim A 64)).a ≤ 2 ^ 181 ∧ (bTail3 hk c (Bnd.prim A 64)).s ≤ 2 ^ 181 := by
  simp only [bTail3, bRest, Bnd.seq, Bnd.count, Bnd.prim, bCoins, bZeros, bEntB, bEntF, bCoin,
    nW_eq, nR_eq, nE_eq, lenFin, len_col, hd, hw]
  subst hN hK hk' hA
  norm_num

theorem bTailI_as_num {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (hN : N = 2 ^ 34)
    (hK : K = 2 ^ 25) (hk' : k = 2 ^ 25 + 1) (hd : c.d = 2 ^ 61) (hw : c.w = 512) {A : ℕ}
    (hA : A = 2 ^ 25) :
    (bTailI hk c (Bnd.prim A 64)).a ≤ 2 ^ 181 ∧ (bTailI hk c (Bnd.prim A 64)).s ≤ 2 ^ 181 := by
  simp only [bTailI, bEncCoins, bCt, Bnd.seq, Bnd.count, Bnd.prim, bCoins, bZeros, bEntB, bEntF,
    bCoin, nW_eq, nR_eq, nE_eq, nPsi_eq, nC0_eq, nC1_eq, nCj_eq, lenFin, len_col, len_trap, hd, hw]
  subst hN hK hk' hA
  norm_num

theorem bTail3_as_conf : (bTail3 hkp confP bChi).a ≤ 2 ^ 181 ∧ (bTail3 hkp confP bChi).s ≤ 2 ^ 181 := by
  rw [(bTail3_as hkp confP bChi).1, (bTail3_as hkp confP bChi).2, bChi_a, bChi_s]
  exact bTail3_as_num hkp confP Np_def Kp_def kp_eq confP_d confP_w Kp_def

theorem bTailI_as_conf : (bTailI hkp confP bChi).a ≤ 2 ^ 181 ∧ (bTailI hkp confP bChi).s ≤ 2 ^ 181 := by
  rw [(bTailI_as hkp confP bChi).1, (bTailI_as hkp confP bChi).2, bChi_a, bChi_s]
  exact bTailI_as_num hkp confP Np_def Kp_def kp_eq confP_d confP_w Kp_def

theorem tail5_as_conf : Np * Kp + (nW hkp confP + (nR hkp confP * (1 + (Np * Kp - 1)) +
    nE (N := Np) hkp * (min confP.w Kp + (Kp - confP.w)))) ≤ 2 ^ 181 := by
  simp only [nW_eq, nR_eq, nE_eq]
  simp only [confP_d, confP_w, kp, Kp_def, Np_def]
  norm_num

/-- The arithmetic of the setup bounds. -/
theorem setup_arith {s w E M : ℕ} (hs : s ≤ 2 ^ 181) (hw : w ≤ 2 ^ 200) (hE : E ≤ 2 ^ 200)
    (hM : M ≤ 2 ^ 182) :
    (2 * (2 ^ 180 + 10 + 1) + 3) + ((tApp (2 ^ 180) s 10 + w * (2 ^ 180 + 10 + s + E)) +
      6 * (2 * (M + 1) + 3)) ≤ 2 ^ 403 := by
  have h := Nat.mul_le_mul hw (show 2 ^ 180 + 10 + s + E ≤ 2 ^ 180 + 10 + 2 ^ 181 + 2 ^ 200 by omega)
  unfold tApp tBit
  norm_num at h hM ⊢
  omega

end Eval

/-! ### The bounds at `confP` -/

section Time

variable {a b : ℕ}

set_option maxRecDepth 100000
set_option exponentiation.threshold 1000

theorem bounds_setup3D :
    timeBoundT (dropHead (setup3P hkp confP chiP)) (io2 (R := 5) (2 ^ 180) 10 0) ≤ 2 ^ 403 ∧
      lenBoundT (dropHead (setup3P hkp confP chiP)) (io2 (R := 5) (2 ^ 180) 10 0) ≤
        io2 (2 ^ 182) 0 0 := by
  have hL := len_appendTail (atbb_tail3P hkp confP bChi atbb_chiP preserves6_chiP) (2 ^ 180) 10
  have hS := bTail3_S₀ hkp confP bChi
  have hs : max 10 (bTail3 hkp confP bChi).S₀ ≤ 2 ^ 181 := by
    have := cntSum_conf; have := bChi_S₀; omega
  obtain ⟨ha3, hs3⟩ := bTail3_as_conf
  have hM : ∀ i, lenBoundT (setup3P hkp confP chiP) (io2 (R := 5) (2 ^ 180) 10 0) i ≤ 2 ^ 182 :=
    fun i => (hL i).trans (by
      simp only [shp]; split_ifs
      · have : (2 : ℕ) ^ 182 = 2 ^ 181 + 2 ^ 181 := by norm_num
        have : (2 : ℕ) ^ 180 + 10 ≤ 2 ^ 181 := by norm_num
        omega
      · have : (2 : ℕ) ^ 182 = 2 ^ 181 + 2 ^ 181 := by norm_num
        omega)
  refine ⟨(time_dropHead _ _ _ _ hM).trans ?_, len_dropHead _ _ _ _ (hM 0)⟩
  have h3 := time_setup3P_conf (2 ^ 180) 10
  unfold time3 at h3
  have hT := hasLB_tail3 hkp confP bChi ⟨2 ^ 40, 2 ^ 40⟩ lin_bChi (2 ^ 180 + 10)
    (max 10 (bTail3 hkp confP bChi).S₀)
  obtain ⟨hw, hE⟩ := lbTail3_conf
  exact le_trans (Nat.add_le_add_left (Nat.add_le_add_right (h3.trans (Nat.add_le_add_left hT _)) _) _)
    (setup_arith hs hw hE (le_refl (2 ^ 182)))

theorem bounds_setupID :
    timeBoundT (dropHead (setupIP hkp confP chiP)) (io2 (R := 5) (2 ^ 180) 10 0) ≤ 2 ^ 403 ∧
      lenBoundT (dropHead (setupIP hkp confP chiP)) (io2 (R := 5) (2 ^ 180) 10 0) ≤
        io2 (2 ^ 182) 0 0 := by
  have hL := len_appendTail (atbb_tailIP hkp confP bChi atbb_chiP preserves6_chiP) (2 ^ 180) 10
  have hS := bTailI_S₀ hkp confP bChi
  have hs : max 10 (bTailI hkp confP bChi).S₀ ≤ 2 ^ 181 := by
    have := cntSum_conf; have := bChi_S₀; omega
  obtain ⟨ha3, hs3⟩ := bTailI_as_conf
  have hM : ∀ i, lenBoundT (setupIP hkp confP chiP) (io2 (R := 5) (2 ^ 180) 10 0) i ≤ 2 ^ 182 :=
    fun i => (hL i).trans (by
      simp only [shp]; split_ifs
      · have : (2 : ℕ) ^ 182 = 2 ^ 181 + 2 ^ 181 := by norm_num
        have : (2 : ℕ) ^ 180 + 10 ≤ 2 ^ 181 := by norm_num
        omega
      · have : (2 : ℕ) ^ 182 = 2 ^ 181 + 2 ^ 181 := by norm_num
        omega)
  refine ⟨(time_dropHead _ _ _ _ hM).trans ?_, len_dropHead _ _ _ _ (hM 0)⟩
  have h3 := time_setupIP_conf (2 ^ 180) 10
  unfold timeI at h3
  have hT := hasLB_tailI hkp confP bChi ⟨2 ^ 40, 2 ^ 40⟩ lin_bChi (2 ^ 180 + 10)
    (max 10 (bTailI hkp confP bChi).S₀)
  obtain ⟨hw, hE⟩ := lbTailI_conf
  exact le_trans (Nat.add_le_add_left (Nat.add_le_add_right (h3.trans (Nat.add_le_add_left hT _)) _) _)
    (setup_arith hs hw hE (le_refl (2 ^ 182)))

theorem bounds_setup5D :
    timeBoundT (dropHead (setup5P hkp confP)) (io2 (R := 5) (2 ^ 180) 10 0) ≤ 2 ^ 403 ∧
      lenBoundT (dropHead (setup5P hkp confP)) (io2 (R := 5) (2 ^ 180) 10 0) ≤
        io2 (2 ^ 182) 0 0 := by
  obtain ⟨hw, hE, hs5⟩ := tail5_conf
  have hs : max 10 (s5 hkp confP) ≤ 2 ^ 181 := by
    have : (10 : ℕ) ≤ 2 ^ 181 := by norm_num
    omega
  have hℓ : io2 (R := 5) (2 ^ 180) 10 0 ≤ shp (0 : Fin 7) (2 ^ 180) (max 10 (s5 hkp confP)) :=
    fun i => by simp only [io2, shp]; split_ifs <;> simp_all <;> omega
  obtain ⟨-, h2⟩ := appendTape_bounds (le_max_left 10 _) hℓ (by simp [io2])
  have hL : lenBoundT (setup5P hkp confP) (io2 (R := 5) (2 ^ 180) 10 0) ≤ _ :=
    (lenBoundT_mono _ h2).trans ((atb_tail5P hkp confP) _ _ (le_max_right _ _)).2
  have ha5 := tail5_as_conf
  have hM : ∀ i, lenBoundT (setup5P hkp confP) (io2 (R := 5) (2 ^ 180) 10 0) i ≤ 2 ^ 182 :=
    fun i => (hL i).trans (by
      simp only [shp]; split_ifs
      · have : (2 : ℕ) ^ 182 = 2 ^ 181 + 2 ^ 181 := by norm_num
        have : (2 : ℕ) ^ 180 + 10 ≤ 2 ^ 181 := by norm_num
        omega
      · have : (2 : ℕ) ^ 182 = 2 ^ 181 + 2 ^ 181 := by norm_num
        simp only [Nat.add_zero, Nat.mul_zero]
        omega)
  refine ⟨(time_dropHead _ _ _ _ hM).trans ?_, len_dropHead _ _ _ _ (hM 0)⟩
  have h5 := time_setup5P hkp confP (2 ^ 180) 10
  unfold time5 at h5
  have hT := lin_tTail5 hkp confP (2 ^ 180 + 10) (max 10 (s5 hkp confP))
  exact le_trans (Nat.add_le_add_left (Nat.add_le_add_right (h5.trans (Nat.add_le_add_left hT _)) _) _)
    (setup_arith hs hw hE (le_refl (2 ^ 182)))

theorem time_setup3D_conf (ha : a ≤ 2 ^ 180) (hb : b ≤ 10) :
    timeBoundT setup3D (io2 a b 0) ≤ 2 ^ 403 :=
  (timeBoundT_mono _ (io2_mono ha hb)).trans (by rw [setup3D, timeBoundT_liftP]; exact bounds_setup3D.1)

theorem len_setup3D_conf (ha : a ≤ 2 ^ 180) (hb : b ≤ 10) :
    lenBoundT setup3D (io2 a b 0) ≤ io2 (2 ^ 182) 0 0 :=
  (lenBoundT_mono _ (io2_mono ha hb)).trans (lenBoundT_liftP_le _ _ bounds_setup3D.2)

theorem time_setupID_conf (ha : a ≤ 2 ^ 180) (hb : b ≤ 10) :
    timeBoundT setupID (io2 a b 0) ≤ 2 ^ 403 :=
  (timeBoundT_mono _ (io2_mono ha hb)).trans (by rw [setupID, timeBoundT_liftP]; exact bounds_setupID.1)

theorem len_setupID_conf (ha : a ≤ 2 ^ 180) (hb : b ≤ 10) :
    lenBoundT setupID (io2 a b 0) ≤ io2 (2 ^ 182) 0 0 :=
  (lenBoundT_mono _ (io2_mono ha hb)).trans (lenBoundT_liftP_le _ _ bounds_setupID.2)

theorem time_setup5D_conf (ha : a ≤ 2 ^ 180) (hb : b ≤ 10) :
    timeBoundT setup5D (io2 a b 0) ≤ 2 ^ 403 :=
  (timeBoundT_mono _ (io2_mono ha hb)).trans (by rw [setup5D, timeBoundT_liftP]; exact bounds_setup5D.1)

theorem len_setup5D_conf (ha : a ≤ 2 ^ 180) (hb : b ≤ 10) :
    lenBoundT setup5D (io2 a b 0) ≤ io2 (2 ^ 182) 0 0 :=
  (lenBoundT_mono _ (io2_mono ha hb)).trans (lenBoundT_liftP_le _ _ bounds_setup5D.2)

end Time

end AdvancedEncryption.DualUse.Prog

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode AdvancedEncryption.DualUse.Params

/-! ### The secret words fit the input bound -/

section Words

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000

theorem nS3_conf :
    fencLen ((inst3Enc (N := Np) (K := Kp) (k := kp)).prod (sec3Enc hkp confP)) + 14 ≤ 2 ^ 180 := by
  simp only [fencLen, inst3Enc, sec3Enc, restEnc]
  comp_unfold
  norm_num

theorem nSI_conf :
    fencLen ((inst3Enc (N := Np) (K := Kp) (k := kp)).prod (secIEnc hkp confP)) + 14 ≤ 2 ^ 180 := by
  simp only [fencLen, inst3Enc, secIEnc, coinsEnc, ctEnc]
  comp_unfold
  norm_num

theorem nS5_conf :
    fencLen ((inst5Enc (N := Np) (K := Kp) (k := kp) confP.d).prod (sec5Enc hkp confP)) + 14 ≤
      2 ^ 180 := by
  simp only [fencLen, inst5Enc, pubEnc, sec5Enc]
  comp_unfold
  norm_num

end Words

end AdvancedEncryption.DualUse.Prog

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.DualUse.Params
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow

/-! ### State counts of the setups -/

section SetupSizes

variable {M : ℕ}

theorem sz_withCount {t c : Fin 7} {n : ℕ} (hn : n ≤ M) (hB : M < 2 ^ 240) {body : XProg 7}
    {a : ℕ} (hb : SZ body a) : SZ (withCount t c n body) (46836 + (a + 60)) :=
  (sz_natP hn hB).seq (hb.seq (sz_prim _))

theorem sz_forN {c t : Fin 7} {body : XProg 7} {a : ℕ} (hb : SZ body a) :
    SZ (forN c t body) (60 + (a + 39)) :=
  (sz_prim _).seq (show (body.size + 39) ≤ a + 39 by have := hb; unfold SZ at this; omega)

theorem sz_coinAp (r b : Fin 7) : SZ (coinAp r b) 200 := by
  show (prog (.coin b)).size + (prog (.seq (.prim (.snocHead r b)) (.prim (.clear b)))).size ≤ 200
  simp [Prog.size, Prim.pad]

theorem sz_bitAp (r : Fin 7) (b : Bool) : SZ (bitAp r b) 60 := sz_prim _

theorem sz_nopX : SZ nopX 60 := sz_prim _

theorem sz_coinsF {n : ℕ} (hn : n ≤ M) (hB : M < 2 ^ 240) :
    SZ (coinsF n) (46836 + ((60 + (200 + 39)) + 60)) :=
  sz_withCount hn hB (sz_forN (sz_coinAp 0 2))

theorem sz_zerosF {n : ℕ} (hn : n ≤ M) (hB : M < 2 ^ 240) :
    SZ (zerosF n) (46836 + ((60 + (60 + 39)) + 60)) :=
  sz_withCount hn hB (sz_forN (sz_bitAp 0 false))

theorem sz_repF {n : ℕ} (hn : n ≤ M) (hB : M < 2 ^ 240) {body : XProg 7} {a : ℕ}
    (hb : SZ body a) : SZ (repF n body) (46836 + ((60 + (a + 39)) + 60)) :=
  sz_withCount hn hB (sz_forN hb)

theorem sz_repX {p : XProg 7} {a : ℕ} (hp : SZ p a) : ∀ n, SZ (repX p n) (n * a + 60)
  | 0 => by show SZ nopX (0 * a + 60); simpa using sz_nopX
  | n + 1 => ((hp.seq (sz_repX hp n))).mono (by ring_nf; omega)

theorem sz_wordAp (r : Fin 7) : ∀ w : List Bool, SZ (wordAp r w) (60 * (w.length + 1))
  | [] => sz_nopX.mono (by simp)
  | b :: w => ((sz_bitAp r b).seq (sz_wordAp r w)).mono (by simp; ring_nf; omega)

theorem sz_leafP {K L : ℕ} (v : ℤ) (hK : K ≤ M) (hB : M < 2 ^ 240) :
    SZ (leafP K L v) (60 + (60 * (L + 1) + (46836 + ((60 + (60 + 39)) + 60)))) := by
  have hw := sz_wordAp 0 ((zmodEnc L).enc (v : ZMod (2 ^ L)))
  rw [(zmodEnc L).length] at hw
  exact (sz_prim _).seq (hw.seq (sz_withCount (by omega) hB (sz_forN (sz_bitAp _ _))))

theorem sz_chainP {K L η : ℕ} (hK : K ≤ M) (hB : M < 2 ^ 240) :
    ∀ f j, SZ (chainP K L η f j) ((f + 1) * (60 * L + 47300))
  | 0, j => (sz_leafP _ hK hB).mono (by ring_nf; omega)
  | f + 1, j => by
    have h1 := sz_leafP (L := L) ((j : ℤ) - η) hK hB
    have h2 := sz_chainP (L := L) (η := η) hK hB f (j + 1)
    show (leafP K L _).size + ((prog (.prim (.tail 3))).size + (chainP K L η f (j + 1)).size) + 1 ≤ _
    have h3 := sz_prim (k := 7) (.tail 3)
    unfold SZ at h1 h2 h3
    nlinarith

theorem sz_upStep : SZ upStep 300 := by
  unfold SZ upStep bitAp nopX; simp [Prog.size, Prim.pad]

theorem sz_downStep : SZ downStep 300 := by
  unfold SZ downStep nopX; simp [Prog.size, Prim.pad]

theorem sz_chiP : SZ chiP (2 ^ 21) := by
  have hK : Kp ≤ 2 ^ 25 := by rw [Kp_def]
  have hB : (2 : ℕ) ^ 25 < 2 ^ 240 := by norm_num
  unfold chiP cbdP
  exact ((sz_repX (sz_coinAp 2 4) (16 + 16)).seq ((sz_repX (sz_bitAp 3 true) 16).seq
    ((sz_repX sz_upStep 16).seq ((sz_repX sz_downStep 16).seq
      (sz_chainP (η := 16) (L := 6) hK hB (16 + 16) 0))))).mono (by norm_num)

theorem sz_appendTapeP : SZ (appendTapeP (k := 7) 0 1 3 4) 1000 := by
  unfold SZ appendTapeP XProg.forN; simp [Prog.size, Prim.pad]

theorem sz_entB {N K : ℕ} (h : N * K ≤ M) (hB : M < 2 ^ 240) :
    SZ (entB N K) (200 + (46836 + ((60 + (60 + 39)) + 60))) :=
  (sz_coinAp 0 2).seq (sz_zerosF (by omega) hB)

theorem sz_entF {K w : ℕ} (h : K + w ≤ M) (hB : M < 2 ^ 240) :
    SZ (entF K w) (46836 + ((60 + (200 + 39)) + 60) + (46836 + ((60 + (60 + 39)) + 60))) :=
  (sz_coinsF (by omega) hB).seq (sz_zerosF (by omega) hB)

theorem sz_clrS : SZ clrS 360 := by
  unfold SZ clrS; simp [Prog.size, Prim.pad]

theorem counts_le : (Encode.Enum.list (α := Fin 1)).length *
      ((Encode.Enum.list (α := Fin confP.d)).length * (Np * Kp)) ≤ 2 ^ 181 ∧
    nW hkp confP ≤ 2 ^ 181 ∧ Np * Kp ≤ 2 ^ 181 ∧
    (Encode.Enum.list (α := Fin confP.d)).length * Np ≤ 2 ^ 181 ∧ Np ≤ 2 ^ 181 ∧
    (Encode.Enum.list (α := RingBTVW.Col kp)).length * Np ≤ 2 ^ 181 ∧ nR hkp confP ≤ 2 ^ 181 ∧
    nE (N := Np) hkp ≤ 2 ^ 181 ∧ Kp + confP.w ≤ 2 ^ 181 ∧ nPsi (N := Np) hkp ≤ 2 ^ 181 ∧
    nC0 (N := Np) (K := Kp) confP ≤ 2 ^ 181 ∧ nC1 (N := Np) (K := Kp) (k := kp) ≤ 2 ^ 181 ∧
    nCj (N := Np) hkp ≤ 2 ^ 181 := by
  have h := cntSum_conf
  simp only [cntSum] at h
  omega

theorem size_setup3D_conf : setup3D.size ≤ 2 ^ 25 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -, -, -⟩ := counts_le
  have hB : (2 : ℕ) ^ 181 < 2 ^ 240 := by norm_num
  have hR : SZ (restP hkp confP chiP) _ :=
    (sz_coinsF h3 hB).seq ((sz_repF h4 hB sz_chiP).seq
      (((sz_repF h5 hB sz_chiP).seq ((sz_repF h6 hB sz_chiP).seq (sz_repF h6 hB sz_chiP))).seq
        ((sz_repF h7 hB (sz_entB h3 hB)).seq (sz_repF h5 hB sz_chiP))))
  have hT : SZ (tail3P hkp confP chiP) _ :=
    (sz_coinsF h1 hB).seq ((sz_coinsF h2 hB).seq ((sz_coinsF h3 hB).seq
      (hR.seq (sz_repF h8 hB (sz_entF h9 hB)))))
  rw [setup3D, liftP, size_frame]
  exact ((sz_prim _).seq ((sz_appendTapeP.seq hT).seq sz_clrS)).mono (by norm_num)

theorem size_setupID_conf : setupID.size ≤ 2 ^ 25 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := counts_le
  have hB : (2 : ℕ) ^ 181 < 2 ^ 240 := by norm_num
  have hE : SZ (encCoinsP hkp confP chiP) _ :=
    (sz_coinsF h3 hB).seq ((sz_repF h4 hB sz_chiP).seq
      (((sz_repF h5 hB sz_chiP).seq ((sz_repF h6 hB sz_chiP).seq (sz_repF h6 hB sz_chiP))).seq
        ((sz_repF h7 hB (sz_entB h3 hB)).seq ((sz_repF h8 hB (sz_entF h9 hB)).seq
          (sz_repF h5 hB sz_chiP)))))
  have hC : SZ (ctP hkp confP) _ :=
    (sz_coinsF h10 hB).seq ((sz_coinsF h11 hB).seq ((sz_coinsF h12 hB).seq
      ((sz_coinsF h13 hB).seq (sz_coinsF h3 hB))))
  have hT : SZ (tailIP hkp confP chiP) _ :=
    (sz_coinsF h1 hB).seq ((sz_coinsF h2 hB).seq ((sz_coinsF h3 hB).seq (hE.seq hC)))
  rw [setupID, liftP, size_frame]
  exact ((sz_prim _).seq ((sz_appendTapeP.seq hT).seq sz_clrS)).mono (by norm_num)

theorem size_setup5D_conf : setup5D.size ≤ 2 ^ 25 := by
  obtain ⟨-, h2, h3, -, -, -, h7, h8, h9, -, -, -, -⟩ := counts_le
  have hB : (2 : ℕ) ^ 181 < 2 ^ 240 := by norm_num
  have hT : SZ (tail5P hkp confP) _ :=
    (sz_coinsF h3 hB).seq ((sz_coinsF h2 hB).seq
      ((sz_repF h7 hB (sz_entB h3 hB)).seq (sz_repF h8 hB (sz_entF h9 hB))))
  rw [setup5D, liftP, size_frame]
  exact ((sz_prim _).seq ((sz_appendTapeP.seq hT).seq sz_clrS)).mono (by norm_num)

end SetupSizes

end AdvancedEncryption.DualUse.Prog
