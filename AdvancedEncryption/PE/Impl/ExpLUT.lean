import PE.Impl.ExpLUT.Prog.EncTimeConf
import PE.Impl.ExpLUT.Prog.EncTightBase
import PE.Impl.ExpLUT.Prog.EncTightInit
import PE.Impl.ExpLUT.Prog.EncTightCert
import PE.Impl.ExpLUT.Prog.EncTightCore
import PE.Impl.ExpLUT.Prog.EncTimeTight
import PE.Impl.ExpLUT.Prog.EncTightPrep
import PE.Impl.ExpLUT.Prog.EncTightFront
import PE.Impl.ExpLUT.Prog.EncSamplerTimeConf
import PE.Impl.ExpLUT.Prog.DecSteps
import PE.Impl.ExpLUT.Prog.DecSplit
import PE.Impl.ExpLUT.Prog.DecRounds
import PE.Impl.ExpLUT.Prog.DecRoundT
import PE.Impl.ExpLUT.Prog.DecRound
import PE.Impl.ExpLUT.Prog.DecRep
import PE.Impl.ExpLUT.Prog.DecMul
import PE.Impl.ExpLUT.Prog.DecLut
import PE.Impl.ExpLUT.Prog.DecFront
import PE.Impl.ExpLUT.Prog.DecFinalD
import PE.Impl.ExpLUT.Prog.DecFinal
import PE.Impl.ExpLUT.Prog.DecEnc
import PE.Impl.ExpLUT.Prog.DecCoefMath
import PE.Impl.ExpLUT.Prog.DecCoef
import PE.Impl.ExpLUT.Prog.DecCalls
import PE.Impl.ExpLUT.Prog.DecBlocks
import PE.Impl.ExpLUT.Prog.DecAlg
import PE.Impl.ExpLUT.Prog.KeyVM
import PE.Impl.ExpLUT.Prog.KeyTryVM
import PE.Impl.ExpLUT.Prog.KeyCoins
import PE.Impl.ExpLUT.Prog.KeyCoinVM
import PE.Impl.ExpLUT.Prog.KeySample
import PE.Impl.ExpLUT.Prog.KeyBoxTest
import PE.Impl.ExpLUT.Prog.KeyBoxLoop
import PE.Impl.ExpLUT.Prog.KeyShift
import PE.Impl.ExpLUT.Prog.KeyDecompose
import PE.Impl.ExpLUT.Prog.KeyPublicRow
import PE.Impl.ExpLUT.Prog.KeyGather
import PE.Impl.ExpLUT.Prog.KeyRowAut
import PE.Impl.ExpLUT.Prog.KeyBHCodec
import PE.Impl.ExpLUT.Prog.KeyCoefficients
import PE.Impl.ExpLUT.Prog.KeyGadget
import PE.Impl.ExpLUT.Prog.KeyPublicMachine
import PE.Impl.ExpLUT.Prog.KeyTarget
import PE.Impl.ExpLUT.Prog.KeyCorrection
import PE.Impl.ExpLUT.Prog.KeyProposal
import PE.Impl.ExpLUT.Prog.KeyAccept
import PE.Impl.ExpLUT.Prog.KeyTryLaw
import PE.Impl.ExpLUT.Prog.KeyEvalCodec
import PE.Impl.ExpLUT.Prog.KeyEvalRead
import PE.Impl.ExpLUT.Prog.KeyEvalFront
import PE.Impl.ExpLUT.Prog.KeyEvalInit
import PE.Impl.ExpLUT.Prog.KeyCandidate
import PE.Impl.ExpLUT.Prog.KeyInput
import PE.Impl.ExpLUT.Prog.KeyCore
import PE.Impl.ExpLUT.Prog.KeyOutput
import PE.Impl.ExpLUT.Prog.KeyBranch
import PE.Impl.ExpLUT.Prog.KeyFront
import PE.Impl.ExpLUT.Prog.KeyMachine
import PE.Impl.ExpLUT.Prog.KeySizeBasic
import PE.Impl.ExpLUT.Prog.KeyGatherSize
import PE.Impl.ExpLUT.Prog.KeyAcceptSize
import PE.Impl.ExpLUT.Prog.KeyCorrectionSize
import PE.Impl.ExpLUT.Prog.KeyCoefficientSize
import PE.Impl.ExpLUT.Prog.KeyPublicSize
import PE.Impl.ExpLUT.Prog.KeyDigitsSize
import PE.Impl.ExpLUT.Prog.KeyTrySize
import PE.Impl.ExpLUT.Prog.KeyPrepareSize
import PE.Impl.ExpLUT.Prog.KeyProgramSize
import PE.Impl.ExpLUT.Prog.KeySizeConf
import PE.Impl.ExpLUT.Prog.KeyTimeBasic
import PE.Impl.ExpLUT.Prog.KeyTimeMoves
import PE.Impl.ExpLUT.Prog.KeyTimeChecked
import PE.Impl.ExpLUT.Prog.KeyTimeLoad
import PE.Impl.ExpLUT.Prog.KeyTimeRing
import PE.Impl.ExpLUT.Prog.KeyTimeBinary
import PE.Impl.ExpLUT.Prog.KeyTimeInvariant
import PE.Impl.ExpLUT.Prog.KeyTimeCounted
import PE.Impl.ExpLUT.Prog.KeyTimeArithmetic
import PE.Impl.ExpLUT.Prog.KeyTimeOpInvariant
import PE.Impl.ExpLUT.Prog.KeyTimeControl
import PE.Impl.ExpLUT.Prog.KeyTimeAppend
import PE.Impl.ExpLUT.Prog.KeyTimeLoadScratch
import PE.Impl.ExpLUT.Prog.KeyTimeNat
import PE.Impl.ExpLUT.Prog.KeyTimeTemplates
import PE.Impl.ExpLUT.Prog.KeyTimeInit
import PE.Impl.ExpLUT.Prog.KeyTimeScratch
import PE.Impl.ExpLUT.Prog.KeyTimeMoveScratch
import PE.Impl.ExpLUT.Prog.KeyTimeRead
import PE.Impl.ExpLUT.Prog.KeyTimeEvalInputs
import PE.Impl.ExpLUT.Prog.KeyTimeLayout
import PE.Impl.ExpLUT.Prog.KeyTimeCoefV
import PE.Impl.ExpLUT.Prog.KeyTimeGrowth
import PE.Impl.ExpLUT.Prog.KeyTimeBitLoop
import PE.Impl.ExpLUT.Prog.KeyTimeCoefA
import PE.Impl.ExpLUT.Prog.KeyTimeMatrixGrowth
import PE.Impl.ExpLUT.Prog.KeyTimeMatAdd
import PE.Impl.ExpLUT.Prog.KeyTimeGadget
import PE.Impl.ExpLUT.Prog.KeyTimeMatAddExact
import PE.Impl.ExpLUT.Prog.KeyTimeDigitAcc
import PE.Impl.ExpLUT.Prog.KeyTimeInner
import PE.Impl.ExpLUT.Prog.KeyTimeColumns
import PE.Impl.ExpLUT.Prog.KeyTimeMatrix
import PE.Impl.ExpLUT.Prog.KeyTimeAutomorphism
import PE.Impl.ExpLUT.Prog.KeyTimeChain
import PE.Impl.ExpLUT.Prog.KeyTimeCoefFlexible
import PE.Impl.ExpLUT.Prog.KeyTimeEval
import PE.Impl.ExpLUT.Prog.KeyTimeEvalReady
import PE.Impl.ExpLUT.Prog.KeyTimePrepare
import PE.Impl.ExpLUT.Prog.KeyTimeDecode
import PE.Impl.ExpLUT.Prog.KeyTimeDecodeQueue
import PE.Impl.ExpLUT.Prog.KeyTimeCandidate
import PE.Impl.ExpLUT.Prog.KeyTimeCoins
import PE.Impl.ExpLUT.Prog.KeyTimeQueueArithmetic
import PE.Impl.ExpLUT.Prog.KeyTimeGather
import PE.Impl.ExpLUT.Prog.KeyTimeShift
import PE.Impl.ExpLUT.Prog.KeyTimeCorrectionLoad
import PE.Impl.ExpLUT.Prog.KeyTimeCorrectionCoord
import PE.Impl.ExpLUT.Prog.KeyTimeCorrection
import PE.Impl.ExpLUT.Prog.KeyTimeDecompose
import PE.Impl.ExpLUT.Prog.KeyTimeTarget
import PE.Impl.ExpLUT.Prog.KeyTimeDigitsTail
import PE.Impl.ExpLUT.Prog.KeyTimePowers
import PE.Impl.ExpLUT.Prog.KeyTimeNegativeReady
import PE.Impl.ExpLUT.Prog.KeyTimePrefix
import PE.Impl.ExpLUT.Prog.KeyTimeGatherAut
import PE.Impl.ExpLUT.Prog.KeyTimeBH
import PE.Impl.ExpLUT.Prog.KeyTimePublicKernels
import PE.Impl.ExpLUT.Prog.KeyTimeProposal
import PE.Impl.ExpLUT.Prog.KeyTimeAssembly
import PE.Impl.ExpLUT.Prog.KeyTimeRadius
import PE.Impl.ExpLUT.Prog.KeyTimeAcceptInit
import PE.Impl.ExpLUT.Prog.KeyTimeBoxDigits
import PE.Impl.ExpLUT.Prog.KeyTimeBoxFamily
import PE.Impl.ExpLUT.Prog.KeyTimeAccept
import PE.Impl.ExpLUT.Prog.KeyTimeCore
import PE.Impl.ExpLUT.Prog.KeyTimeOutput
import PE.Impl.ExpLUT.Prog.KeyTimeLiteral
import PE.Impl.ExpLUT.Prog.KeyTimeEnter
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMUtil
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMIO
import PE.Impl.ExpLUT.Prog.KeyTryMath
import PE.Impl.ExpLUT.Prog.KeyLut
import PE.Impl.ExpLUT.Prog.KeyEval
import PE.Impl.ExpLUT.Prog.KeyBoxW
import PE.Impl.ExpLUT.Prog.AuthWCost
import PE.Impl.ExpLUT.Prog.AuthW
import PE.Impl.ExpLUT.Prog.Words
import PE.Impl.ExpLUT.Prog.UnifCanon
import PE.Impl.ExpLUT.Prog.SetupTime
import PE.Impl.ExpLUT.Prog.SetupSize
import PE.Impl.ExpLUT.Prog.SetupP
import PE.Impl.ExpLUT.Prog.SetupGad
import PE.Impl.ExpLUT.Prog.SetupConf
import PE.Impl.ExpLUT.Prog.Samplers
import PE.Impl.ExpLUT.Prog.Eval
import PE.Impl.ExpLUT.Prog.EncSamplersConf
import PE.Impl.ExpLUT.Prog.EncSamplers
import PE.Impl.ExpLUT.Prog.EncRow
import PE.Impl.ExpLUT.Basic
import PE.Impl.ExpLUT.Ops
import PE.Impl.ExpLUT.LUT
import PE.Impl.ExpLUT.Eval
import PE.Impl.ExpLUT.Noise
import PE.Impl.ExpLUT.Canonical
import PE.Impl.ExpLUT.NegacyclicNorm
import PE.Impl.ExpLUT.Scheme
import PE.Impl.ExpLUT.Correctness
import PE.Impl.ExpLUT.KeyGen
import PE.Impl.ExpLUT.CorrectBound
import PE.Impl.ExpLUT.Laws
import PE.Impl.ExpLUT.SimForm
import PE.Impl.ExpLUT.SimEval
import PE.Impl.ExpLUT.SimBound
import PE.Impl.ExpLUT.SimTrap
import PE.Impl.ExpLUT.SimKeys
import PE.Impl.ExpLUT.SimTrapRev
import PE.Impl.ExpLUT.GameChain
import PE.Impl.ExpLUT.Params.Conf
import PE.Impl.ExpLUT.Params.Noise
import PE.Impl.ExpLUT.Params.Correct
import PE.Impl.ExpLUT.BPBridge
import PE.Impl.ExpLUT.AH.Final
import PE.Impl.ExpLUT.FloodBound
import PE.Impl.ExpLUT.AH.Flood
import PE.Impl.ExpLUT.AH.CircBridge
import PE.Impl.ExpLUT.AH.RedChain
import PE.Impl.ExpLUT.Prog.RedDecode
import PE.Impl.ExpLUT.AH.RedConst
import PE.Impl.ExpLUT.Prog.AuthWX
import PE.Impl.ExpLUT.AH.RedSecret
import PE.Impl.ExpLUT.AH.RedCompsR
import PE.Impl.ExpLUT.Prog.RedSetup
import PE.Impl.ExpLUT.Prog.EncWordMath
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.EncPhases
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.EncTail
import PE.Impl.ExpLUT.Prog.EncTailMath
import PE.Impl.ExpLUT.Prog.EncHelperMath
import PE.Impl.ExpLUT.Prog.EncAutMath
import PE.Impl.ExpLUT.Prog.EncDigitMath
import PE.Impl.ExpLUT.Prog.EncDigitCodec
import PE.Impl.ExpLUT.Prog.EncAutPhase
import PE.Impl.ExpLUT.Prog.EncInputPhase
import PE.Impl.ExpLUT.Prog.EncInputCodec
import PE.Impl.ExpLUT.Prog.EncTailCodec
import PE.Impl.ExpLUT.Prog.EncHelpers
import PE.Impl.ExpLUT.Prog.EncAutomorphisms
import PE.Impl.ExpLUT.Prog.EncBPhase
import PE.Impl.ExpLUT.Prog.EncCore
import PE.Impl.ExpLUT.Prog.EncInit
import PE.Impl.ExpLUT.Prog.EncInitSpec
import PE.Impl.ExpLUT.Prog.EncComplete
import PE.Impl.ExpLUT.Prog.EncMachineConf
import PE.Impl.ExpLUT.Prog.EncFront
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.EncCb
import PE.Impl.ExpLUT.Prog.KeyTimeInvalid
import PE.Impl.ExpLUT.Prog.KeyTimeFront
import PE.Impl.ExpLUT.AH.Correct
import PE.Impl.ExpLUT.SubmissionCore
import PE.Impl.ExpLUT.AH.RedConstDc
import PE.Impl.ExpLUT.Prog.RedSetupPUC
import PE.Impl.ExpLUT.Prog.RedSetupP
import PE.Impl.ExpLUT.Prog.RedSetupPDc
import PE.Impl.ExpLUT.Prog.RedSetupPSize
import PE.Impl.ExpLUT.Prog.RedKeyU
import PE.Impl.ExpLUT.Prog.RedKeyTry
import PE.Impl.ExpLUT.Prog.RedKeyX
import PE.Impl.ExpLUT.Prog.RedKeySimTD
import PE.Impl.ExpLUT.Prog.RedKeySimES
import PE.Impl.ExpLUT.Prog.RedKeySimEMath
import PE.Impl.ExpLUT.Prog.RedKeySimE
import PE.Impl.ExpLUT.Prog.RedPubFront
import PE.Impl.ExpLUT.Prog.RedPubPMath
import PE.Impl.ExpLUT.Prog.RedPubPInst
import PE.Impl.ExpLUT.Prog.DecDescConf
import PE.Impl.ExpLUT.Prog.DecTimeVM
import PE.Impl.ExpLUT.Prog.RedChalPhases
import PE.Impl.ExpLUT.Prog.RedChalDc
import PE.Impl.ExpLUT.Prog.RedPubPComps
import PE.Impl.ExpLUT.SubmissionDec
import PE.Impl.ExpLUT.SubmissionAssembly
import PE.Impl.ExpLUT.Prog.RedKeyMComp
import PE.Impl.ExpLUT.Prog.RedKeyTTop
import PE.Impl.ExpLUT.Prog.RedKeyMidPk
import PE.Impl.ExpLUT.Prog.RedKeyPktBridge
import PE.Impl.ExpLUT.Prog.RedKeyPktStateD
import PE.Impl.ExpLUT.Prog.RedKeyPktOk
import PE.Impl.ExpLUT.SubmissionKey
import PE.Impl.ExpLUT.Prog.RedKeyTSpec
import PE.Impl.ExpLUT.Prog.RedKeyC4
import PE.Impl.ExpLUT.Prog.RedKeyC3Fin
import PE.Impl.ExpLUT.Prog.RedKeyC3M
import PE.Impl.ExpLUT.Prog.RedKeyCW
import PE.Impl.ExpLUT.Prog.RedKeyCWPk
import PE.Impl.ExpLUT.Submission
import PE.Impl.ExpLUT.Prog.DecTight

/-!
# Predicate encryption from lookup tables over exponents (ePrint 2026/2539 §4–§5)

The algebra of §4 and the scheme and correctness of §5, over an abstract ring with automorphisms
(`SigabaNeo.Lattices.ExpRing`); see `PE/Impl/ExpLUT/PLAN.md`.

* `Basic`: the setting (`Setting`), encodings (`Encodes`), gadget ciphertexts (`IsGC`).
* `Ops`: Add, SMul, Mul (eq. (1)), Aut_k (eq. (2)) with exact output equations.
* `LUT`: the rounds along the binary basis and the lookup tables (Lemma 8).
* `Eval`: branching programs over encodings (Lemma 9, exact).
* `Noise`: norm-level bounds (Lemma 9's `γ`, `Δ`).
* `Canonical`, `NegacyclicNorm`: the canonical setting `idx j = g^j` (Lemma 8 discharged) and the
  coefficient norm of `ℤ_q[X]/(X^{2^e} + 1)`.
* `Scheme`: Setup, Enc, KeyGen matrices (eq. (3)), Dec (§5.1).
* `Correctness`: eq. (4) and Theorem 1 exactly; `CorrectBound`: at the norm level.
* `KeyGen`: keys by box rejection, with a trapdoor-independent law.
* `Laws`: the laws of the coins; Theorem 1 in probability.

The proof of Theorem 2 (Appendix A):

* `SimForm`, `SimEval`, `SimBound`: simulation forms (Definition 3), Lemma 10, Corollary 1 and the
  coefficient bound `B_R̂`.
* `SimTrap`, `SimKeys`: Lemma 11 (the gadget trapdoor `X` and `T_sim`), the key laws.
* `HybLaws`, `HybView`, `Hybrid0`, `Hybrid12`, `Hybrid3`, `Reduction`, `Hybrid5`, `Hybrid5U`,
  `Hybrid6`: the hybrids H0–H6 and the reduction to circular Ring-LWE.
* `GameChain`: the chain over the generic attribute-hiding game.
* `Params/Conf`: the concrete configuration (`q = 2^{2^16} − 1`, `n = 2^24`, `W = 2^22`, `m̄`, laws,
  key boxes and their cover bound); `Params/Noise`: the noise certificate (Lemma 9, Lemma 11's
  shift, `corrBound < q/4`); `Params/Correct`: correctness at the concrete parameters.
* `BPBridge`: the universe's programs of width `w8` as branching programs; correctness for them.
* `AH/*` (package G): attribute hiding of the implementation (`AH/Final.attributeHiding_Dc`).
-/
