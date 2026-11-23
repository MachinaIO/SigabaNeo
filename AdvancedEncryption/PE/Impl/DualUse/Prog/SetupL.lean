import PE.Impl.DualUse.Prog.CompLib
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
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

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

theorem law_setup3D (ab : Inst3T Np Kp kp) (x : PUniv.Attr) :
    setup3D.law (io2 (R := 254) (true :: (inst3Enc (N := Np) (K := Kp) (k := kp)).enc ab)
      (encAttr x) []) =
      (setup3 hkp confP x).map fun σ => io2 (R := 254)
        (((inst3Enc (N := Np) (K := Kp) (k := kp)).prod (sec3Enc hkp confP)).enc (ab, σ)) [] [] :=
  law_liftP_map _ (law_dropHead _ _ _ (law_setup3P_conf ab x))

theorem law_setupID (ab : Inst3T Np Kp kp) (x : PUniv.Attr) :
    setupID.law (io2 (R := 254) (true :: (inst3Enc (N := Np) (K := Kp) (k := kp)).enc ab)
      (encAttr x) []) =
      (setupI hkp confP x).map fun σ => io2 (R := 254)
        (((inst3Enc (N := Np) (K := Kp) (k := kp)).prod (secIEnc hkp confP)).enc (ab, σ)) [] [] :=
  law_liftP_map _ (law_dropHead _ _ _ (law_setupIP_conf ab x))

theorem law_setup5D (i : Pub (Fin confP.d) (Rg Np Kp) kp × Pub (Fin confP.d) (Rg Np Kp) kp)
    (x : PUniv.Attr) :
    setup5D.law (io2 (R := 254) (true :: (inst5Enc (N := Np) (K := Kp) (k := kp) confP.d).enc i)
      (encAttr x) []) =
      (setup5 hkp confP x).map fun σ => io2 (R := 254)
        (((inst5Enc (N := Np) (K := Kp) (k := kp) confP.d).prod (sec5Enc hkp confP)).enc (i, σ))
          [] [] :=
  haveI := dp_ne
  law_liftP_map _ (law_dropHead _ _ _ (law_setup5P hkp confP Np_pos Kp_pos i x))

end AdvancedEncryption.DualUse.Prog

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.DualUse.Params
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

open SigabaNeo.Encode in
theorem confP_w : confP.w = 768 := rfl

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

end Eval

end AdvancedEncryption.DualUse.Prog

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.DualUse.Params
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

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

end SetupSizes


theorem kp_eq : kp = 2 ^ 27 + 1 := by rw [kp, Kp_def]

theorem sz_chiP : SZ chiP (2 ^ 21) := by
  have hK : Kp ≤ 2 ^ 27 := by rw [Kp_def]
  have hB : (2 : ℕ) ^ 27 < 2 ^ 240 := by norm_num
  unfold chiP cbdP
  exact ((sz_repX (sz_coinAp 2 4) (16 + 16)).seq ((sz_repX (sz_bitAp 3 true) 16).seq
    ((sz_repX sz_upStep 16).seq ((sz_repX sz_downStep 16).seq
      (sz_chainP (η := 16) (L := 6) hK hB (16 + 16) 0))))).mono (by norm_num)

end AdvancedEncryption.DualUse.Prog
