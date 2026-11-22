import PE.Impl.DualUse.Prog.WfB2Time
import PE.Impl.DualUse.Prog.KeyPTime2

/-!
# The numbers of the block-structured `W_f` block at `confP`

Closed numerical checks (`decide +kernel`) at `N = 2^33`, `K = 2^25`, `k = K + 1`, `d = 2^60`,
`W = 512`, the stream offsets and `|sdEnc|` below `2^234`, the gate list below `2^64` bits: the
bounds between the phases of `wfBody` and the steps of the two runs of the machine (`absC`).
-/

namespace AdvancedEncryption.DualUse.Prog

namespace WB2

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.ValVM SigabaNeo.Tape.Prog SigabaNeo.Tape.Prog.KST
  SigabaNeo.Tape.Prog.StepT SigabaNeo.Lattices.Algo SigabaNeo.Lattices

set_option maxRecDepth 100000

/-! ### The numbers -/

def Nc : ℕ := 2 ^ 33
def Kc : ℕ := 2 ^ 25
def kc : ℕ := Kc + 1
def dc : ℕ := 2 ^ 60
def Wc : ℕ := 512
/-- A bound of `|sdEnc|` and of the stream offsets. -/
def Lb : ℕ := 2 ^ 234
/-- A bound of the gate list. -/
def Lgc : ℕ := 2 ^ 64
def M31c : ℕ := 2 ^ 145
/-- A bound of every tape. -/
def Mall : ℕ := 2 ^ 240

/-- The input of the body: `sdEnc` and the gate list. -/
def β0c : Fin 256 → ℕ := fun t => if t = mw SDW then Lb else if t = mw GS then Lgc else 0

def wTc : List (Fin 256 × ℕ) := wordsTx Nc Kc kc dc Wc 64 Lb Lb Lb
def vTc : Fin 256 → ℕ := vTn Nc Kc kc dc Wc wTc β0c M31c
def L0c : List ℕ := (List.finRange 120).map fun x => vTc (mw x)

/-- The word bounds after the run of `f̂` (`absC`). -/
def L1c : List ℕ :=
  [22300745863144621053336468703077086896586752, 22300745863144621053336468703077086896586752,
    22300745863144621053336468703077086896586752, 22300745863144621053336468703077086896586752,
    22300745863144621053336468703077086896586752, 22300745863144621053336468703077086896586752,
    22300745863144621053336468703077086896586752, 22300745863144621053336468703077086896586752,
    22300745863144621053336468703077086896586752, 22300745863144621053336468703077086896586752,
    22300745863144621053336468703077086896586752, 22300745863144621053336468703077086896586752,
    33554433, 33554434, 748288882914913356444567965553997006106698098671616,
    748288905215659219589189018890465709183784995258368,
    748288927516405082733810072226934412260871891845120,
    748288905215659219589189018890465709183784995258368,
    748288905215659219589189018890465709183784995258368,
    748288882914913356444567965553997006106698098671616, 33554432,
    748288905215659219589189018890465709183784995258368, 33554433,
    748288905215659219589189018890465709183784995258368,
    748288882914913356444567965553997006106698098671616,
    748288882914913356444567965553997006106698098671616,
    748288882914913356444567965553997006106698098671616, 2,
    22300745863144621053336468703077086896586752, 1,
    748288882914913356444567965553997006106698098671616,
    22300745863144621053336468703077086896586752,
    431359185240924449424539262895519653566728020926381085143727045869568,
    191561948317226878284786409527687245575580467733725184,
    6427752560159852033206020497807343326620361240679943526940672,
    431359185240924449424539262895519653566728020926381085143727045869568,
    431359185240924449424539262895519653566728020926381085143727045869568, 576460769483292673,
    576460769483292673, 576460769483292673, 1, 1, 1, 64, 64,
    862718370481848897352500759961212594244320110744768158074057894395904,
    6427752560159852033206020497807343326620361240679943526940672, 8589934591, 8589934591,
    8589934592, 8589934591, 12855505120319704066412040995614686653240722481359887053881344,
    431359185240924448676250379980606297122160055372384079037028947197952,
    191561948317226878284786409527687245575580467733725184,
    6427752560159852033206020497807343326620361240679943526940672, 67108866, 67108866,
    748288882914913356444567965553997006106698098671616,
    431359185240924449424539262895519653566728020926381085143727045869568, 576460769483292673,
    431359185240924449424539262895519653566728020926381085143727045869568,
    27606985387162255149739023449108101809804435888681546220650096895197184,
    27606985387162255149739023449108101809804435888681546220650096895197184,
    862718370481848897352500759961212594244320110744768158074057894395904,
    27606985387162255149739023449108101809804435888681546220650096895197184,
    431359185240924448676250379980606297122160055372384079037028947197952,
    27606985387162255149739023449108101809804435888681546220650096895197184,
    27606985387162255149739023449108101809804435888681546220650096895197184,
    12855505120319704066412040995614686653240722481359887053881344,
    748288882914913356444567965553997006106698098671616,
    22300745863144621033993654724551891646152704, 288230376151711744, 2, 2, 33554433, 8589934592,
    6427752560159852033206020497807343326620361240679943526940672,
    862718370481848897352500759961212594244320110744768158074057894395904,
    6427752560159852033206020497807343326620361240679943526940672,
    22300745863144621053336468703077086896586752,
    191561948294926132421641788474350776872503380837138432, 8589934592, 8589934592,
    6427752560159852033206020497807343326620361240679943526940672, 33554433, 33554433, 134217732,
    748288882914913356444567965553997006106698098671616,
    27606985387162255149739023449108101809804435888681546220650096895197184,
    18446744073709551616, 2, 33554433, 8589934592, 8589934591,
    191561948294926132421641788474350776872503380837138432,
    748288860614167493299946912217528303029611202084864, 0,
    12855505120319704066412040995614686653240722481359887053881344,
    431359185240924448676250379980606297122160055372384079037028947197952,
    748288882914913356444567965553997006106698098671616,
    442574524057188484341832889860102060847336216812066065091991699825098752,
    18446744073709551616, 1535,
    433084621981888146470955381500528722310648695593873615353177062986743808,
    885149048114376968683665779720204121694672433624132130183983399650197504,
    442574524057188484341832889860102060847336216812066065091991699825098752, 512, 33554431,
    288230376151711743, 862718370481848897352500759961212594244320110744768158074057894395904,
    862718370481848897352500759961212594244320110744768158074057894395904,
    442574524057188484341832889860102060847336216812066065091991699825098752,
    885149048114376968683665779720204121694672433624132130183983399650197504, 512,
    433084621981888146470955381500528722310648695593873615353177062986743808,
    862718370481848897352500759961212594244320110744768158074057894395904,
    8627183704818488973525007599612125942443201107447681580740578943959040, 134217732, 503,
    8627183704818488973525007599612125942443201107447681580740578943959040]

def wGc : List (Fin 256 × ℕ) := wordsG Nc Kc kc dc Wc Lb Lb Lb
def β1c : Fin 256 → ℕ := encB (bsT Nc Kc kc dc) (VT Nc Kc kc dc) (gB L1c)
def vGc : Fin 256 → ℕ := vGn Nc Kc kc dc Wc wGc β1c M31c
def L0Gc : List ℕ := (List.finRange 120).map fun x => vGc (mw x)

/-- The word bounds after the predicate's run. -/
def L1Gc : List ℕ :=
  [19342813690294819098722304, 38685627380589638197444608,
    22300745863144621033993654724551891646152704, 288230376151711744, 33554432, 8589934592,
    288230376151711744, 33554433, 19342813690294819098722304, 38685627380589638197444608,
    22300745863144621072679282393371905995309056, 22300745863144621033993654724551891646152704,
    0, 0, 0, 33554432, 8589934592, 0, 33554432, 0, 0, 0, 0, 0, 0, 0, 33554432, 0, 0, 1, 0,
    22300745863144621053336468703077086896586752,
    431359185240924449424539262895519653566728020926381085143727045869568,
    191561948317226878284786409527687245575580467733725184,
    6427752560159852033206020497807343326620361240679943526940672,
    431359185240924449424539262895519653566728020926381085143727045869568,
    431359185240924449424539262895519653566728020926381085143727045869568, 576460769483292673,
    576460769483292673, 576460769483292673, 1, 1, 1, 64, 64,
    862718370481848897352500759961212594244320110744768158074057894395904,
    6427752560159852033206020497807343326620361240679943526940672, 8589934591, 8589934591,
    8589934592, 8589934591, 12855505120319704066412040995614686653240722481359887053881344,
    431359185240924448676250379980606297122160055372384079037028947197952,
    191561948317226878284786409527687245575580467733725184,
    6427752560159852033206020497807343326620361240679943526940672, 67108866, 67108866,
    748288882914913356444567965553997006106698098671616,
    431359185240924449424539262895519653566728020926381085143727045869568, 576460769483292673,
    431359185240924449424539262895519653566728020926381085143727045869568,
    374144463758203537963422891702166634113208288280576, 19342814266755588582014976,
    19342814266755588582014976,
    27606985387162255149739023449108101809804435888681546220650096895197184,
    431359185240924448676250379980606297122160055372384079037028947197952,
    27606985387162255149739023449108101809804435888681546220650096895197184,
    27606985387162255149739023449108101809804435888681546220650096895197184,
    12855505120319704066412040995614686653240722481359887053881344, 38685627380589638197444608,
    22300745863144621033993654724551891646152704, 288230376151711744, 10,
    374144463758203537963422891702166634113208288280576, 19342814266755588582014976,
    19342814266755588582014976, 6427752560159852033206020497807343326620361240679943526940672,
    862718370481848897352500759961212594244320110744768158074057894395904,
    27606985387162255149739023449108101809804435888681546220650096895197184,
    22300745863144621053336468703077086896586752,
    191561948294926132421641788474350776872503380837138432, 8589934592, 8589934592,
    6427752560159852033206020497807343326620361240679943526940672, 33554433,
    19342814266755588582014976, 134217732, 748288882914913356444567965553997006106698098671616,
    27606985387162255149739023449108101809804435888681546220650096895197184,
    18446744073709551616, 2, 33554433, 8589934592, 8589934591,
    191561948294926132421641788474350776872503380837138432,
    748288860614167493299946912217528303029611202084864, 0,
    12855505120319704066412040995614686653240722481359887053881344,
    431359185240924448676250379980606297122160055372384079037028947197952,
    748288882914913356444567965553997006106698098671616,
    11440282627793190610284471867799787775593545728, 18446744073709551616, 1535,
    11194974423298599778484999761472696809645146112,
    22880565255586381220568943735599575551187091456,
    11440282627793190610284471867799787775593545728, 512, 512, 288230376151711743,
    22300745863144621072679282393371905995309056, 22300745863144621072679282393371905995309056,
    11440282627793190610284471867799787775593545728,
    22880565255586381220568943735599575551187091456, 512,
    11194974423298599778484999761472696809645146112,
    22300745863144621072679282393371905995309056, 223007458631446210726792823933719059953090560,
    134217732, 503, 223007458631446210726792823933719059953090560]

def β4c : Fin 256 → ℕ := encB (bsG Nc Kc kc dc) (VG Nc Kc kc dc) (gB L1Gc)
def v5c : Fin 256 → ℕ :=
  Function.update (tmplB tX0 (keyT Nc Kc kc dc) (Prog.lenBoundT (clrsP keyClr) β4c)) (ms 87)
    (tmplB tX0 (keyT Nc Kc kc dc) (Prog.lenBoundT (clrsP keyClr) β4c) (ms 87) + 1)

/-! ### The checks -/

/-- The result of a run is `L` with at most `B` steps. -/
def chkR (r : Option (List ℕ × ℕ)) (L : List ℕ) (B : ℕ) : Bool :=
  match r with
  | some (L', T) => L' == L && decide (T ≤ B)
  | none => false

theorem of_chkR {r : Option (List ℕ × ℕ)} {L : List ℕ} {B : ℕ} (h : chkR r L B = true) :
    ∃ T, r = some (L, T) ∧ T ≤ B := by
  rcases r with _ | ⟨L', T⟩
  · simp [chkR] at h
  · simp only [chkR, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨T, by rw [h.1], h.2⟩

theorem chk_hinT : (fun j => tmplB tX0 (tmpl31 Nc Kc kc dc) (Prog.lenBoundT (cp (mw GS) (mw GSC))
    (Prog.lenBoundT (clr (mw 12)) (ccV Wc (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0c)))) (tm31 j)) ≤
    Sym.bnd (tmVars M31c Nc Kc kc (lenA Nc Kc kc dc)) σTmF := by decide +kernel

theorem chk_htopT : ∀ j, tmplB tX0 (tmpl31 Nc Kc kc dc) (Prog.lenBoundT (cp (mw GS) (mw GSC))
    (Prog.lenBoundT (clr (mw 12)) (ccV Wc (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0c)))) (tm31 j) ≤ M31c := by
  decide +kernel

theorem chk_g1 : vTc ≤ encB (bsT Nc Kc kc dc) (VT Nc Kc kc dc) (gB L0c) := by decide +kernel

theorem chk_V : VT Nc Kc kc dc ≤ bsT Nc Kc kc dc 1 ∧ VT Nc Kc kc dc ≤ bsT Nc Kc kc dc 2 ∧
    (∀ t, bsT Nc Kc kc dc t ≤ Mall) ∧ VT Nc Kc kc dc ≤ Mall := by decide +kernel

theorem chk_r1 : chkR (absC (bsT Nc Kc kc dc) (VT Nc Kc kc dc) (Sym.pEval [0, Nc, Kc, kc, dc] cStep2)
    Mall 30 fhatFullC L0c) L1c (2 ^ 545) = true := by decide +kernel

theorem chk_hinG : (fun j => tmplB tX0 (tmpl31 Nc Kc kc dc) (Prog.lenBoundT (cp (mw GS) (mw GSC))
    (Prog.lenBoundT (clr (mw 12)) (ccV Wc (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β1c)))) (tm31 j)) ≤
    Sym.bnd (tmVars M31c Nc Kc kc (lenA Nc Kc kc dc)) σTmF := by decide +kernel

theorem chk_htopG : ∀ j, tmplB tX0 (tmpl31 Nc Kc kc dc) (Prog.lenBoundT (cp (mw GS) (mw GSC))
    (Prog.lenBoundT (clr (mw 12)) (ccV Wc (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β1c)))) (tm31 j) ≤ M31c := by
  decide +kernel

theorem chk_g3 : vGc ≤ encB (bsG Nc Kc kc dc) (VG Nc Kc kc dc) (gB L0Gc) := by decide +kernel

theorem chk_VG : VG Nc Kc kc dc ≤ bsG Nc Kc kc dc 1 ∧ VG Nc Kc kc dc ≤ bsG Nc Kc kc dc 2 ∧
    (∀ t, bsG Nc Kc kc dc t ≤ Mall) ∧ VG Nc Kc kc dc ≤ Mall := by decide +kernel

theorem chk_r2 : chkR (absC (bsG Nc Kc kc dc) (VG Nc Kc kc dc) (Sym.pEval [0, Nc, Kc, kc, dc] cStepG2)
    Mall 30 gswFullC L0Gc) L1Gc (2 ^ 480) = true := by decide +kernel

/-- The top of the frame of `simKeyP`. -/
def Msk : ℕ := 2 ^ 230

theorem chk_sk : (fun j => v5c (oK2 j)) ≤ ℓSK Msk Nc Kc dc kc (nPos Nc kc) (VT Nc Kc kc dc)
    (lenA Nc Kc kc 1) (gB L1Gc FOUT) (gB L1Gc 61) (gB L1Gc OUTW) 1 (VG Nc Kc kc dc)
    (lenA Nc Kc kc 2) ∧ ∀ j, v5c (oK2 j) ≤ Msk := by decide +kernel

theorem chk_skT : (2 * Msk + 3) * simKeySweeps Nc Kc dc kc (nPos Nc kc) (VT Nc Kc kc dc)
    (lenA Nc Kc kc 1) 1 (VG Nc Kc kc dc) (lenA Nc Kc kc 2) ≤ 2 ^ 548 := by decide +kernel

/-! ### The small checks of the preparations -/

/-- The bounds after the framed `simKeyP`. -/
def v6c : Fin 256 → ℕ := embedF (ValVM.mkE oK2 oK2_inj) v5c
  fun j => if j = 0 then dc * (2 * kc) * (Nc * Kc) else Msk

theorem chk_small :
    (∀ t, β0c t ≤ Mall) ∧
    (∀ t, ccV Wc (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0c) t ≤ Mall) ∧
    (∀ t, tmOutN Nc Kc kc dc M31c (tmplB tX0 (tmpl31 Nc Kc kc dc) (Prog.lenBoundT (cp (mw GS) (mw GSC))
      (Prog.lenBoundT (clr (mw 12)) (ccV Wc (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0c))))) t ≤ Mall) ∧
    (∀ x ∈ tmpl31 Nc Kc kc dc, x.2 ≤ Mall) ∧
    (∀ x ∈ stepT Nc Kc kc dc ++ wTc, x.2 ≤ Mall) ∧
    (∀ t, β1c t ≤ Mall) ∧
    (∀ t, ccV Wc (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β1c) t ≤ Mall) ∧
    (∀ t, tmOutN Nc Kc kc dc M31c (tmplB tX0 (tmpl31 Nc Kc kc dc) (Prog.lenBoundT (cp (mw GS) (mw GSC))
      (Prog.lenBoundT (clr (mw 12)) (ccV Wc (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β1c))))) t ≤ Mall) ∧
    (∀ x ∈ stepG Nc Kc kc dc ++ wGc, x.2 ≤ Mall) ∧
    (∀ t, β4c t ≤ Mall) ∧ (∀ x ∈ keyT Nc Kc kc dc, x.2 ≤ Mall) ∧ (∀ t, v6c t ≤ Mall) := by
  decide +kernel

theorem chk_sum :
    cntT Wc (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0c) + capT2 Wc (embedF (ValVM.mkE cntE cntE_inj) (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0c) (cntOut Wc (Prog.lenBoundT (cp (mw GSC) (mw GS)) β0c))) +
      (2 * M31c + 3) * simTmplSweeps Nc Kc kc +
      90 * uT (Mall + 6) + (2 ^ 545 + (cntT Wc (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β1c) +
      capT2 Wc (embedF (ValVM.mkE cntE cntE_inj) (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β1c) (cntOut Wc (Prog.lenBoundT (clrsP lowW ⨾ cp (mw GS) (mw GSC)) β1c))) +
      (2 * M31c + 3) * simTmplSweeps Nc Kc kc + 120 * uT (Mall + 40) + (2 ^ 480 +
      (120 * uT (Mall + 100) + (2 ^ 548 + 256 * (2 * (Mall + 256) + 5)))))) ≤ 2 ^ 549 := by
  decide +kernel

/-! ### The time of the block at `confP` -/

theorem lenL0c : L0c.length = 120 := by simp [L0c]
theorem lenL0Gc : L0Gc.length = 120 := by simp [L0Gc]

set_option maxHeartbeats 4000000 in
/-- **The time of the block-structured `W_f` block at the sizes of `confP`**: from `sdEnc` of at
most `2^234` bits on tape `0` and a gate list of at most `2^64` bits on tape `1`, at most `2^549`
steps, every tape below `2^240` afterwards. -/
theorem time_wfB2_conf {N K : ℕ} (hk : 2 ^ K < 2 ^ (K + 1)) (c : Conf N K (K + 1)) (hN : N = Nc)
    (hK : K = Kc) (hd : c.d = dc) (hth : treeHeight N (K + 1) ≤ 64)
    (hoB : offB c ≤ Lb) (hoW : offW hk c ≤ Lb) (hoP : offPsi hk c ≤ Lb) (hoR : offR hk c ≤ Lb)
    (hoX : offPsi hk c + 10 * lenPsi N K (K + 1) ≤ Lb) (Lsd Lg : ℕ) (hLsd : Lsd ≤ Lb)
    (hLg : Lg ≤ Lgc) :
    XProg.timeBoundT (wfB2 hk c Wc) (io2 (R := 254) Lsd Lg 0) ≤ 2 ^ 549 ∧
      ∀ t, XProg.lenBoundT (wfB2 hk c Wc) (io2 (R := 254) Lsd Lg 0) t ≤ Mall := by
  subst hN hK
  obtain ⟨s0, s2, s6, s31, sT, s1, s2G, s6G, sG, s4, sK, s6'⟩ := chk_small
  -- the preparation of `f̂`
  have p1 := ph_prepT hk c Wc β0c M31c (by rw [hd]; exact chk_hinT) (by rw [hd]; exact chk_htopT)
  have hTl : TLe (wordsT Nc Kc (Kc + 1) c.d Wc (offB c) (offW hk c) (offPsi hk c)) wTc := by
    rw [wordsT_eq, hd]; exact TLe_wordsTx _ _ _ _ _ hth hoB hoW hoP
  have g1 : vT hk c Wc β0c M31c ≤ encB (bsT Nc Kc kc dc) (VT Nc Kc kc dc) (gB L0c) :=
    (vT_le hk c Wc β0c M31c wTc hTl).trans (by rw [hd]; exact chk_g1)
  -- the run of `f̂`
  obtain ⟨T1, hr1, hT1⟩ := of_chkR chk_r1
  have p2 := ph_runT Nc Kc kc dc Mall 30 L0c L1c T1 lenL0c chk_V.1 chk_V.2.1 chk_V.2.2.1
    chk_V.2.2.2 hr1
  -- the preparation of the predicate
  have p3 := ph_prepG hk c Wc β1c M31c (by rw [hd]; exact chk_hinG) (by rw [hd]; exact chk_htopG)
  have hGl : TLe (wordsG Nc Kc (Kc + 1) c.d Wc (offPsi hk c) (offR hk c)
      (offPsi hk c + 10 * lenPsi Nc Kc (Kc + 1))) wGc := by
    rw [hd]; exact TLe_wordsG _ _ _ _ _ hoP hoR hoX
  have g3 : vG hk c Wc β1c M31c ≤ encB (bsG Nc Kc kc dc) (VG Nc Kc kc dc) (gB L0Gc) :=
    (vG_le hk c Wc β1c M31c wGc hGl).trans (by rw [hd]; exact chk_g3)
  -- the predicate's run
  obtain ⟨T2, hr2, hT2⟩ := of_chkR chk_r2
  have p4 := ph_runG Nc Kc kc dc Mall 30 L0Gc L1Gc T2 lenL0Gc chk_VG.1 chk_VG.2.1 chk_VG.2.2.1
    chk_VG.2.2.2 hr2
  -- the key sum
  have p5 := ph_keyPrep Nc Kc kc dc β4c
  have hkp : keyPrep Nc Kc (Kc + 1) c.d = keyPrep Nc Kc kc dc := by rw [hd]; rfl
  rw [← hkp] at p5
  have p6 := ph_simKey v5c Msk Nc Kc dc kc (nPos Nc kc) (VT Nc Kc kc dc) (lenA Nc Kc kc 1)
    (gB L1Gc FOUT) (gB L1Gc 61) (gB L1Gc OUTW) 1 (VG Nc Kc kc dc) (lenA Nc Kc kc 2) chk_sk.1 chk_sk.2
  have p7 := ph_finClr v6c
  have body := ph_wfBody hk c Wc p1 g1 p2 p3 g3 p4 p5 p6 p7
  -- the input
  have hin : (fun j => io2 (R := 254) Lsd Lg 0 (eW j)) ≤ β0c := fun t => by
    obtain ⟨e0, e1, -, -⟩ := swp_eq t
    show io2 (R := 254) Lsd Lg 0 (swp t) ≤ β0c t
    simp only [io2, β0c, e0, e1]
    split_ifs <;> omega
  obtain ⟨ht, hl⟩ := ph_wfB2 hk c Wc (body.mono hin le_rfl le_rfl) _ le_rfl
  refine ⟨ht.trans ?_, fun t => (hl t).trans ?_⟩
  · -- the steps
    have a1 := tT_le hk c Wc β0c M31c Mall s0 s2 (by rw [tmOut_eq, hd]; exact s6)
      (by rw [hd]; exact s31) (TLe_le (TLe_append (TLe_refl _) hTl) (by rw [hd]; exact sT))
    have a3 := tG_le hk c Wc β1c M31c Mall s1 s2G (by rw [tmOut_eq, hd]; exact s6G)
      (by rw [hd]; exact s31) (TLe_le (TLe_append (TLe_refl _) hGl) (by rw [hd]; exact sG))
    have a5 := tK_le Nc Kc kc dc β4c Mall s4 sK
    have a6 := chk_skT
    have a7 := tF_le v6c Mall s6'
    exact (Nat.add_le_add a1 (Nat.add_le_add hT1 (Nat.add_le_add a3 (Nat.add_le_add hT2
      (Nat.add_le_add a5 (Nat.add_le_add a6 a7)))))).trans chk_sum
  · -- the lengths
    have hng : (clrsP finClr).NoGrow := by
      show (clrsP finClr).noGrowB = true
      have : ∀ l : List (Fin 256), (clrsP l).noGrowB = true := by
        intro l; induction l with
        | nil => rfl
        | cons x l ih => simp [clrsP, Prog.noGrowB, ih, Prim.noGrowB]
      exact this _
    have hf := Sym.lenBoundT_le_const (clrsP finClr) hng s6'
    rcases embedF_cases eW (io2 (R := 254) Lsd Lg 0) (Prog.lenBoundT (clrsP finClr) v6c) t with
      ⟨_, h⟩ | ⟨j, _, h⟩
    · rw [h]; simp only [io2]; split_ifs <;> simp only [Mall, Lb, Lgc] at * <;> omega
    · rw [h]; exact hf j

/-- **The key component with the block-structured `W_f` block at the sizes of `confP`**:
`time_keyP2` with `time_wfB2_conf`, when the SimData word and the front end's output are below
`2^234` and `2^64` bits. -/
theorem time_keyP_wfB2 {N K : ℕ} (hk : 2 ^ K < 2 ^ (K + 1)) (c : Conf N K (K + 1)) (hN : N = Nc)
    (hK : K = Kc) (hd : c.d = dc) (hth : treeHeight N (K + 1) ≤ 64)
    (hoB : offB c ≤ Lb) (hoW : offW hk c ≤ Lb) (hoP : offPsi hk c ≤ Lb) (hoR : offR hk c ≤ Lb)
    (hoX : offPsi hk c + 10 * lenPsi N K (K + 1) ≤ Lb)
    {sdP : XProg 82} {Ls Ts Lsd : ℕ} (hsT : XProg.timeBoundT sdP (io2 (R := 80) Ls 0 0) ≤ Ts)
    (hsL : XProg.lenBoundT sdP (io2 (R := 80) Ls 0 0) ≤ io2 Lsd 0 0) (hLsd : Lsd ≤ Lb)
    (hF : frontL c.L Wc ≤ Lgc) (cf : KeyCfg) (K₀ : ℕ) :
    XProg.timeBoundT (keyP hk c sdP (wfB2 hk c Wc) Wc cf) (io2 (R := 254) Ls K₀ 0) ≤
        Ts + frontT c.L Wc K₀ + branchT hk c (fun _ => 2 ^ 549) (fun _ => Mall) cf
          (keyM hk c Lsd Wc cf) + clrT (branchL hk c (fun _ => Mall) cf (keyM hk c Lsd Wc cf)) ∧
      XProg.lenBoundT (keyP hk c sdP (wfB2 hk c Wc) Wc cf) (io2 (R := 254) Ls K₀ 0) ≤
        io2 (branchL hk c (fun _ => Mall) cf (keyM hk c Lsd Wc cf)) 0 0 := by
  obtain ⟨hwT, hwL⟩ := time_wfB2_conf hk c hN hK hd hth hoB hoW hoP hoR hoX Lsd (frontL c.L Wc)
    hLsd hF
  exact time_keyP2 hsT hsL Wc hwT hwL cf K₀

end WB2

end AdvancedEncryption.DualUse.Prog
