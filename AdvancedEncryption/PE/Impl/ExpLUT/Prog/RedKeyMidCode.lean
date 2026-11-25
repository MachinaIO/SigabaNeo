import PE.Impl.ExpLUT.Prog.RedKeyMidPub
import PE.Impl.ExpLUT.Prog.RedKeySimE
import PE.Impl.ExpLUT.Prog.RedKeyMTail
import PE.Impl.ExpLUT.Prog.KeyMachine

/-!
# `mid` of the key component: the MVM phases M2, M3 (contract), M4

The MVM codes of the middle phases and their register-level specifications (the tape-level glue is
`RedKeyMidM`). Every phase starts from a **fresh** register file (all registers blank, the
storage tapes of `RedKeyMidPub` reloaded into a few registers):

* **M2** `m2C` (input `m2Init σ C`: `2` = `mpkW σ`, `rCs` = `C`, `rB1 = [false]`): the msk word
  `mpkW σ ++ 0^{|T|}` (an msk with the zero trapdoor, `mskZ`) into `0`, then F3's `keyPrepareC`:
  `8` = `matL A_F`, `14` = `mpkW σ` (**`exec_m2C`**).
* **M3** (`pk`, **the remaining obligation**, contract **`PkOk pk`**): from `pkInit σ C`
  (`0` = `rawEnc σ`, `1` = `ctW σ`, `2` = `mpkW σ`, `rCs` = `C`, all else blank) establish
  `simKeyC`'s input contract `SimKeyIn` (constants, slab packets with BP states, padded copies of
  `C`, slab counter).
* **M4**: `simKeyC` (`exec_simKeyC`), then — with `14 := mpkW σ` reloaded — **`setXC`** (module 5's
  inputs from `SimKeyIn`'s surviving constants and the `H` field of the public key,
  **`setXOk_setXC`**), then `simXC` (`exec_simXC`) → `16`; finally `8`, `14` reloaded.

**`ready_of_pk`**: under `PkOk pk`, the final register file satisfies `RkMidReady` (the input
contract of the back end `rkTailP`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyMid

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

/-! ### Facts at `Dc` -/

theorem hb_Dc : Dc.b = 22 := rfl

theorem hn_Dc : 2 ^ Dc.b ≤ Dc.q :=
  calc 2 ^ Dc.b ≤ 2 ^ Params.Bk := Nat.pow_le_pow_right (by decide) (by rw [hb_Dc, Params.Bk_def]; omega)
    _ ≤ Dc.q := hBk_Dc

theorem hbK_Dc : Dc.b < Dc.K := by rw [RedPubP.pDc_K, hb_Dc]; norm_num

/-! ### The blank register file -/

/-- All registers blank. -/
def wB : St := fun _ => []

/-! ### M2: `A_F` by F3's preparation, from an msk with the zero trapdoor -/

/-- The msk with the public key of `σ` and the zero trapdoor. -/
noncomputable def mskZ (σ : RawSec Dc) : MSKt Dc := ⟨(redView Dc (rawF Dc σ)).1, 0⟩

/-- The length of the trapdoor's word. -/
noncomputable def nT : ℕ := codecSize (matE Dc (Wb Dc) (Fin Dc.K))

theorem matE_enc_zero_gen (D : Dims) : (matE D (Wb D) (Fin D.K)).enc 0 =
    List.replicate (codecSize (matE D (Wb D) (Fin D.K))) false := by
  rw [List.eq_replicate_iff]
  refine ⟨(matE D (Wb D) (Fin D.K)).length 0, ?_⟩
  rw [matE_enc_product D (0 : Wb D → Fin D.K → Rg D)]
  intro b hb
  simp only [encL, List.mem_flatMap, List.mem_map] at hb
  obtain ⟨_, ⟨_, _, rfl⟩, hb⟩ := hb
  simp only [Pi.zero_apply, encRM_zero, List.mem_replicate] at hb
  exact hb.2

theorem matE_enc_zero : (matE Dc (Wb Dc) (Fin Dc.K)).enc 0 = List.replicate nT false :=
  matE_enc_zero_gen Dc

/-- **M2**: the msk word into `0`, then `keyPrepareC`. -/
noncomputable def m2C : Code :=
  .seq (natC 6 rB1 nT) (.seq (.cp 0 2) (.seq (.app 0 6) (keyPrepareC Dc)))

theorem wf_m2C : m2C.WFc := ⟨natC_wfc _ _ _, trivial, trivial, wf_keyPrepareC Dc⟩

/-- The input of M2. -/
noncomputable def m2Init (σ : RawSec Dc) (C : List Bool) : St :=
  Function.update (Function.update (Function.update wB 2 (mpkW σ)) rCs C) rB1 [false]

/-- **M2**: `14` = the public-key word, `8` = `matL A_F`. -/
theorem exec_m2C (σ : RawSec Dc) (C : List Bool) :
    exec Dc.N Dc.K m2C (m2Init σ C) 14 = mpkW σ ∧
    exec Dc.N Dc.K m2C (m2Init σ C) 8 = encL Dc.N Dc.K
      (matL (keyPK (helperMap Dc) (redView Dc (rawF Dc σ)).1 (bpOf (progOf C)))) := by
  have hb : m2Init σ C rB1 = [false] := by simp [m2Init]
  have h1 : exec Dc.N Dc.K (natC 6 rB1 nT) (m2Init σ C) =
      Function.update (m2Init σ C) 6 (List.replicate nT false) :=
    exec_natC 6 rB1 (by decide) nT _ hb
  rw [m2C, exec_seq, exec_seq, exec_seq, h1]
  have h0 : exec Dc.N Dc.K (.app 0 6) (exec Dc.N Dc.K (.cp 0 2)
      (Function.update (m2Init σ C) 6 (List.replicate nT false))) 0 = (mskEnc Dc).enc (mskZ σ) := by
    rw [mskEnc_append]
    simp only [exec_app, exec_cp, Function.update_apply]
    simp only [mskZ]
    simp [m2Init, mpkW]
    exact matE_enc_zero.symm
  have hC : exec Dc.N Dc.K (.app 0 6) (exec Dc.N Dc.K (.cp 0 2)
      (Function.update (m2Init σ C) 6 (List.replicate nT false))) rCs = C := by
    simp only [exec_app, exec_cp, Function.update_apply]
    simp [m2Init]
  obtain ⟨h14, h8, -⟩ := exec_keyPrepareC Dc hb_Dc hn_Dc (mskZ σ) C _ h0 hC
  exact ⟨h14, h8⟩

/-! ### M3: the contract of the packet code -/

/-- The input of M3: `0` = the raw secret's word, `1` = `ctW`, `2` = `mpkW`, `rCs` = `C`. -/
noncomputable def pkInit (σ : RawSec Dc) (C : List Bool) : St :=
  Function.update (Function.update (Function.update (Function.update wB 0 ((rawEnc Dc).enc σ))
    1 (ctW σ)) 2 (mpkW σ)) rCs C

/-- **The contract of the packet code** (phase M3): from `pkInit σ C`, it establishes the input
contract `SimKeyIn` of `simKeyC` for `mpk`, `ct` of `redView (rawF σ)`, `x = attrN`, the
programming `progOf zr`. -/
def PkOk (pk : Code) : Prop :=
  ∀ (σ : RawSec Dc) (C : List Bool), ValidC C →
    ∃ Cf, SimKeyIn Dc (redView Dc (rawF Dc σ)).1 C (redView Dc (rawF Dc σ)).2 (rawF Dc σ).1
      (ExpLUT.progOf (rawF Dc σ).2.2.1) Cf (exec Dc.N Dc.K pk (pkInit σ C))

/-! ### M4: module 5's inputs -/

/-- The length of the `B` field of the public-key word. -/
noncomputable abbrev nB (D : Dims) : ℕ := codecSize (matE D (Fin 2) (BCol (Wb D) D.K))

/-- The length of the `H` field of the public-key word. -/
noncomputable abbrev nH (D : Dims) : ℕ := codecSize (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K)))

/-- **The set-up code of `simXC`** (public-key word in `14`, `simKeyC`'s constants). -/
noncomputable def setXC (D : Dims) : Code :=
  .seq (.cp rxW rTW) <| .seq (.cp rxTb rTb) <| .seq (.cp rxOne rOne) <|
  .seq (.eqb rxTru rxW rTW) <| .seq (.eqb rxFal rxTb rxW) <| .seq (.eqb rB1 rxTb rxW) <|
  .seq (readFieldC 14 rxH (nB D) (nH D)) (natC rxTs rB1 (2 ^ D.b * D.mb))

theorem wf_setXC (D : Dims) : (setXC D).WFc :=
  ⟨trivial, trivial, trivial, trivial, trivial, trivial, wf_readFieldC _ _ _ _, natC_wfc _ _ _⟩

theorem hEnc_flat (D : Dims) (mpk : MPKt D) :
    (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc mpk.H =
      encL D.N D.K ((Enum.list (α := Jh D)).flatMap fun k => matL (fun a c => mpk.H k a c)) := by
  show ((Enum.list (α := Jh D)).map mpk.H).flatMap (matE D (Fin 2) (Col D.K)).enc = _
  refine (List.flatMap_map _ _ _).trans ?_
  unfold encL
  rw [List.flatMap_assoc]
  congr 1
  funext k
  exact matE_enc D (mpk.H k)

/-- The `H` field of the public-key word is the helper queue of module 5. -/
theorem mpkEnc_H (D : Dims) (mpk : MPKt D) :
    ∃ tail, (mpkEnc D).enc mpk = (matE D (Fin 2) (BCol (Wb D) D.K)).enc mpk.B ++
      encL D.N D.K (xHL (xHs D mpk) (xHi D mpk) (List.range D.b)) ++ tail := by
  rw [xHL_eq, ← hEnc_flat]
  simp only [mpkEnc, FixedEnc.comap, FixedEnc.prod]
  exact ⟨_, (List.append_assoc _ _ _).symm⟩

theorem length_xHL (D : Dims) (mpk : MPKt D) :
    (encL D.N D.K (xHL (xHs D mpk) (xHi D mpk) (List.range D.b))).length = nH D := by
  rw [xHL_eq, ← hEnc_flat]
  exact (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).length mpk.H

theorem rep_ne_pow (b : ℕ) : List.replicate b false ≠ List.replicate (2 ^ b) false := fun h => by
  have := congrArg List.length h
  simp only [List.length_replicate] at this
  exact absurd this (Nat.lt_two_pow_self).ne

/-- **`setXC` establishes module 5's inputs.** -/
theorem setXOk_setXC (D : Dims) (mpk : MPKt D) (w : St) (hM : w 14 = (mpkEnc D).enc mpk)
    (hW : w rTW = List.replicate (2 ^ D.b) false) (hb : w rTb = List.replicate D.b false)
    (h1 : w rOne = encRM D.N D.K 1) (hk : (w rKc).length = gD D) (hT : MulTmpl D.N D.K w) :
    SetXOk D (setXC D) mpk w := by
  obtain ⟨tail, hsplit⟩ := mpkEnc_H D mpk
  have hne := rep_ne_pow D.b
  set u : St := exec D.N D.K (.eqb rB1 rxTb rxW) (exec D.N D.K (.eqb rxFal rxTb rxW)
    (exec D.N D.K (.eqb rxTru rxW rTW) (exec D.N D.K (.cp rxOne rOne)
    (exec D.N D.K (.cp rxTb rTb) (exec D.N D.K (.cp rxW rTW) w))))) with hu
  have u14 : u 14 = (matE D (Fin 2) (BCol (Wb D) D.K)).enc mpk.B ++
      encL D.N D.K (xHL (xHs D mpk) (xHi D mpk) (List.range D.b)) ++ tail := by
    rw [← hsplit, ← hM]; simp [u, Function.update_apply]
  have uB1 : u rB1 = [false] := by simp [u, Function.update_apply, hW, hb, hne]
  have uTb : u rxTb = List.replicate D.b false := by simp [u, Function.update_apply, hb]
  have uTru : u rxTru = [true] := by simp [u, Function.update_apply]
  have uFal : u rxFal = [false] := by simp [u, Function.update_apply, hW, hb, hne]
  have uW : u rxW = List.replicate (2 ^ D.b) false := by simp [u, Function.update_apply, hW]
  have uOne : u rxOne = encRM D.N D.K 1 := by simp [u, Function.update_apply, h1]
  have uK : u rKc = w rKc := by simp [u, Function.update_apply]
  have uRh : u rxRh = w rxRh := by simp [u, Function.update_apply]
  have uHi : ∀ r : Fin 64, 57 ≤ r.val → u r = w r := by
    intro r hr
    have : r ≠ rB1 ∧ r ≠ rxFal ∧ r ≠ rxTru ∧ r ≠ rxOne ∧ r ≠ rxTb ∧ r ≠ rxW := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> subst h <;> simp at hr
    simp [u, Function.update_apply, this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1,
      this.2.2.2.2.2]
  set v := exec D.N D.K (readFieldC 14 rxH (nB D) (nH D)) u with hv
  have vH : v rxH = encL D.N D.K (xHL (xHs D mpk) (xHi D mpk) (List.range D.b)) := by
    have e := exec_readFieldC (N := D.N) (K := D.K) 14 rxH (by decide) (by decide) _ _ tail u u14 uB1
    rw [(matE D (Fin 2) (BCol (Wb D) D.K)).length mpk.B, length_xHL] at e
    exact e
  have vkeep : ∀ r : Fin 64, r ≠ 29 → r ≠ 30 → r ≠ rxH → v r = u r := fun r h29 h30 hH =>
    exec_writes _ _ _ (readFieldC_frame _ _ _ _ r h29 h30 hH)
  have hz : exec D.N D.K (setXC D) w = Function.update v rxTs
      (List.replicate (2 ^ D.b * D.mb) false) := by
    rw [setXC]
    simp only [exec_seq]
    exact exec_natC rxTs rB1 (by decide) _ v ((vkeep rB1 (by decide) (by decide) (by decide)).trans uB1)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hz, Function.update_of_ne (by decide)]; exact vH
  · rw [hz, Function.update_of_ne (by decide), vkeep _ (by decide) (by decide) (by decide)]; exact uTb
  · rw [hz, Function.update_of_ne (by decide), vkeep _ (by decide) (by decide) (by decide)]; exact uTru
  · rw [hz, Function.update_of_ne (by decide), vkeep _ (by decide) (by decide) (by decide)]; exact uFal
  · rw [hz, Function.update_of_ne (by decide), vkeep _ (by decide) (by decide) (by decide), uK]
    exact hk
  · rw [hz, Function.update_of_ne (by decide), vkeep _ (by decide) (by decide) (by decide), uW]
    simp
  · refine hT.of_writes fun q hq => ?_
    have h1 : q ≠ rxTs := by intro h; subst h; simp at hq
    have h2 : q ≠ 29 := by intro h; subst h; simp at hq
    have h3 : q ≠ 30 := by intro h; subst h; simp at hq
    have h4 : q ≠ rxH := by intro h; subst h; simp at hq
    rw [hz, Function.update_of_ne h1, vkeep _ h2 h3 h4, uHi q hq]
  · rw [hz, Function.update_of_ne (by decide), vkeep _ (by decide) (by decide) (by decide)]
    exact uRh
  · rw [hz, Function.update_self]; simp
  · rw [hz, Function.update_of_ne (by decide), vkeep _ (by decide) (by decide) (by decide)]
    exact uOne

/-! ### The chain M3 → M4 -/

/-- `simKeyC` keeps the constants `setXC` reads. -/
theorem simKeyC_keeps : ∀ r : Fin 64, (r = rTW ∨ r = rTb ∨ r = rOne ∨ r = rKc ∨ 57 ≤ r.val) →
    (simKeyC Dc).writes r = false := by
  have h1 : ∀ r : Fin 64, (r = rTW ∨ r = rTb ∨ r = rOne ∨ r = rKc ∨ 57 ≤ r.val) →
      seLoopKC.writes r = false ∧ sePostC.writes r = false := by
    unfold seLoopKC sePostC seSlabC seLoadC seEvalC2 sePopsC sePopC seSplitC seRtC seNBC transC
    decide
  intro r hr
  have h13 : r ≠ seMb := by
    rcases hr with rfl | rfl | rfl | rfl | h <;> first | decide | (intro e; subst e; simp at h)
  simp [simKeyC, Code.writes, (h1 r hr).1, sePostMC_writes _ r h13, (h1 r hr).2]

/-- The state after M3 and `simKeyC`. -/
noncomputable def w4Of (pk : Code) (σ : RawSec Dc) (C : List Bool) : St :=
  exec Dc.N Dc.K (simKeyC Dc) (exec Dc.N Dc.K pk (pkInit σ C))

/-- The state after `14 := mpkW`, `setXC`, `simXC`. -/
noncomputable def w6Of (pk : Code) (σ : RawSec Dc) (C : List Bool) : St :=
  exec Dc.N Dc.K simXC (exec Dc.N Dc.K (setXC Dc) (Function.update (w4Of pk σ C) 14 (mpkW σ)))

/-- **The final register file**: `w6Of` with `8 := A`, `14 := mpkW`. -/
noncomputable def wFin (pk : Code) (σ : RawSec Dc) (C A : List Bool) : St :=
  Function.update (Function.update (w6Of pk σ C) 8 A) 14 (mpkW σ)

/-- **The middle phases end ready for the back end** (register level). -/
theorem ready_of_pk {pk : Code} (hpk : PkOk pk) (σ : RawSec Dc) (C : List Bool) (hC : ValidC C) :
    RkMidReady (redView Dc (rawF Dc σ)).1 (bpOf (progOf C))
      (simKey (helperMap Dc) (redView Dc (rawF Dc σ)).1 (bpOf (progOf C)) (redView Dc (rawF Dc σ)).2
        (rawF Dc σ).1 (ExpLUT.progOf (rawF Dc σ).2.2.1))
      (wFin pk σ C (encL Dc.N Dc.K
        (matL (keyPK (helperMap Dc) (redView Dc (rawF Dc σ)).1 (bpOf (progOf C)))))) := by
  obtain ⟨Cf, hin⟩ := hpk σ C hC
  set mpk := (redView Dc (rawF Dc σ)).1
  set w3 := exec Dc.N Dc.K pk (pkInit σ C)
  have hR := exec_simKeyC Dc hb_Dc hbK_Dc mpk C _ _ _ Cf w3 hin
  have keep : ∀ r : Fin 64, (r = rTW ∨ r = rTb ∨ r = rOne ∨ r = rKc ∨ 57 ≤ r.val) →
      Function.update (w4Of pk σ C) 14 (mpkW σ) r = w3 r := by
    intro r hr
    have h14 : r ≠ 14 := by
      rcases hr with rfl | rfl | rfl | rfl | h <;> first | decide | (intro e; subst e; simp at h)
    rw [Function.update_of_ne h14, w4Of]
    exact exec_writes _ _ _ (simKeyC_keeps r hr)
  have hX := setXOk_setXC Dc mpk (Function.update (w4Of pk σ C) 14 (mpkW σ)) (by simp [mpkW, mpk])
    ((keep rTW (by decide)).trans hin.cst.tw) ((keep rTb (by decide)).trans hin.cst.tb)
    ((keep rOne (by decide)).trans hin.cst.one)
    (by rw [keep rKc (by decide)]; exact hin.cst.kc)
    (hin.cst.tm.of_writes fun q hq => keep q (Or.inr (Or.inr (Or.inr (Or.inr hq)))))
  have hS := exec_simXC Dc mpk (keyPK (helperMap Dc) mpk (bpOf (progOf C))) _ _ hX.xin
    (by rw [hX.rh, Function.update_of_ne (by decide)]; exact hR) hX.ts hX.one
  refine ⟨?_, ?_, ?_⟩
  · simp [wFin, mpkW, mpk]
  · simp [wFin]
  · rw [wFin, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    exact hS.1

end AdvancedEncryption.ExpLUT.Prog.RedKeyMid
