import PE.Impl.ExpLUT.Prog.KeyAccept
import PE.Impl.ExpLUT.Prog.KeySample

/-! Distributional specification of the executable deterministic KeyGen attempt. -/
-- Permit the definitionally equal concrete and setting-indexed coordinate types at PMF boundaries.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)
open Cslib.Probability Cslib.BitString

open Classical in
/-- The scheme's output for a fixed sampled candidate, including the abort-to-zero convention. -/
noncomputable def attemptOutput (D : Dims) (kb : KeyBoxes D) (msk : MSKt D) (F : BP Pos)
    (p : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D) : Keyt D :=
  let z := gadDec (S := setting D) (keyTarget msk.mpk - pubShort (helperMap D) msk.mpk F p)
  let x := p - realTrap (S := setting D) (J := Jh D) msk.T z
  keyOfOutput (S := setting D) (if x ∈ kb.Small then some (x, z) else none)

/-- One uniform proposal followed by the deterministic attempt is exactly keyGenLaw. -/
theorem map_uniform_attemptOutput (D : Dims) (kb : KeyBoxes D) (msk : MSKt D) (F : BP Pos) :
    (PMF.uniformOfFinset kb.Big kb.hBig).map (attemptOutput D kb msk F) =
      keyGenLaw (S := setting D) kb.Big kb.Small kb.hBig gadDec (helperMap D) msk F := by
  classical
  simp only [keyGenLaw, keyLaw, boxSample, PMF.map_comp]
  congr 1

/-- Exact output-word semantics for each candidate, in the distributional specification's notation. -/
theorem exec_tryKeyC_output (D : Dims) (hK : 2 ≤ D.K) (B r : ℕ) (hB : 2 ^ B ≤ D.q)
    (hBK : B ≤ D.K) (hr : 2 * r < 2 ^ B) (hq : 2 ^ (B + 1) ≤ D.q)
    (hcount : 2 * (D.K - B) < D.q) (msk : MSKt D) (F : BP Pos)
    (p : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D) (w : St)
    (hM : w 14 = (mpkEnc D).enc msk.mpk)
    (hA : w 8 = encL D.N D.K (matL (keyPK (helperMap D) msk.mpk F)))
    (hT : w 16 = (matE D (Wb D) (Fin D.K)).enc msk.T)
    (hP : w 9 = encL D.N D.K (Enum.list.map p))
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM D.N D.K 0) :
    exec D.N D.K (tryKeyC D B r) w 19 =
      (keyEnc D).enc (attemptOutput D (kbOf D B hB r) msk F p) :=
  by
    classical
    have h := exec_tryKeyC D hK B r hB hBK hr hq hcount msk.mpk F msk.T p w hM hA hT hP h1 hZ
    convert h using 1
    congr 1
    unfold attemptOutput
    dsimp only
    split_ifs <;> simp_all only [keyOfOutput]

/-- The input contract left for the actual sampler/EvalPK front to establish. -/
structure TryReady (D : Dims) (msk : MSKt D) (F : BP Pos)
    (p : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D) (w : St) : Prop where
  publicKey : w 14 = (mpkEnc D).enc msk.mpk
  evaluated : w 8 = encL D.N D.K (matL (keyPK (helperMap D) msk.mpk F))
  trapdoor : w 16 = (matE D (Wb D) (Fin D.K)).enc msk.T
  candidate : w 9 = encL D.N D.K (Enum.list.map p)
  bit : w rB1 = [false]
  zero : w rZ = encRM D.N D.K 0

/-- Mapping the actual VM attempt over uniform ready candidates gives the encoded KeyGen law. -/
theorem map_uniform_exec_tryKeyC (D : Dims) (hK : 2 ≤ D.K) (B r : ℕ) (hB : 2 ^ B ≤ D.q)
    (hBK : B ≤ D.K) (hr : 2 * r < 2 ^ B) (hq : 2 ^ (B + 1) ≤ D.q)
    (hcount : 2 * (D.K - B) < D.q) (msk : MSKt D) (F : BP Pos)
    (states : (PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D) → St) (ready : ∀ p, TryReady D msk F p (states p)) :
    (PMF.uniformOfFinset (kbOf D B hB r).Big (kbOf D B hB r).hBig).map
      (fun p ↦ exec D.N D.K (tryKeyC D B r) (states p) 19) =
    (keyGenLaw (S := setting D) (kbOf D B hB r).Big (kbOf D B hB r).Small
      (kbOf D B hB r).hBig gadDec (helperMap D) msk F).map (keyEnc D).enc := by
  rw [← map_uniform_attemptOutput, PMF.map_comp]
  congr 1
  funext p
  exact exec_tryKeyC_output D hK B r hB hBK hr hq hcount msk F p (states p)
    (ready p).publicKey (ready p).evaluated (ready p).trapdoor (ready p).candidate
    (ready p).bit (ready p).zero

/-- Fair-coin decoding followed by the executable attempt has the same exact output law. -/
theorem map_coins_exec_tryKeyC (D : Dims) (hK : 2 ≤ D.K) (B r : ℕ) (hB : 2 ^ B ≤ D.q)
    (hBK : B ≤ D.K) (hr : 2 * r < 2 ^ B) (hq : 2 ^ (B + 1) ≤ D.q)
    (hcount : 2 * (D.K - B) < D.q) (msk : MSKt D) (F : BP Pos)
    (states : (PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D) → St) (ready : ∀ p, TryReady D msk F p (states p)) :
    (uniformList (nPI D * D.N * B)).map
      (fun cs ↦ exec D.N D.K (tryKeyC D B r) (states (coinDec D B cs)) 19) =
    (keyGenLaw (S := setting D) (kbOf D B hB r).Big (kbOf D B hB r).Small
      (kbOf D B hB r).hBig gadDec (helperMap D) msk F).map (keyEnc D).enc := by
  have h := map_uniform_exec_tryKeyC D hK B r hB hBK hr hq hcount msk F states ready
  rw [← map_uniformList_coinDec_kbOf D B hB r, PMF.map_comp] at h
  exact h

open Params

/-- Concrete single-try distribution, with all box-test inequalities discharged. -/
theorem map_coins_exec_tryKeyC_Dc (msk : MSKt Dc) (F : BP Pos)
    (states : (PIdxD Dc → Rg Dc) → St)
    (ready : ∀ p, TryReady Dc msk F p (states p)) :
    (uniformList (nPI Dc * Dc.N * Bk)).map
      (fun cs ↦ exec Dc.N Dc.K (tryKeyC Dc Bk rSmall) (states (coinDec Dc Bk cs)) 19) =
    (keyGenLaw (S := setting Dc) kbDc.Big kbDc.Small kbDc.hBig
      gadDec (helperMap Dc) msk F).map (keyEnc Dc).enc := by
  have hk : 2 ≤ Dc.K := by change 2 ≤ Kc; rw [Kc_def]; norm_num
  have h := map_coins_exec_tryKeyC Dc hk Bk rSmall hBk_Dc Bk_lt_Kc.le
    small_test_conditions_Dc.1 small_test_conditions_Dc.2.1 small_test_conditions_Dc.2.2
    msk F states ready
  rw [← kbDc_def] at h
  exact h

end AdvancedEncryption.ExpLUT.Prog
