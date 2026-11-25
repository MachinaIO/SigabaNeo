import PE.Impl.RingBTVW.Prog.EncCore
import SigabaNeoStd.Machines.Prog.AbsBound

/-!
# A per-tape certificate of the core of `Enc`

The abstract interpreter of `SigabaNeoStd.Machines.Prog.AbsBound` (`check`, by `decide +kernel`)
runs over the whole core `encCoreP` from the abstract store `σE`: every tape at most the top size
(variable `0`), but the templates `13 … 38` at their lengths, as polynomials in the variables

  `1` `N`, `2` `K`, `3` `k`, `4` `d`, `5` the number `T` of trapdoor columns,
  `6` the number `J` of encodings, `7` the number `n_A` of attribute bits, `8` `k − K`, `9` `N K − K`

(no template is a numeral multiple of `n_A`, so the certificate holds for every number of attribute
bits). Every loop of the core is charged the length of its own counter (a template or a copy of
one), not the top size. The sweeps `wE` (each sweep costs `2 · top + 3` steps) are
dominated by `44 N² K² k J`: the `J` BGG+ encodings, each a row of `2k` ring products
(`22 N² K²` sweeps each, schoolbook).
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Sym

/-- The monomial `c · x₁^e₁ · x₂^e₂ ⋯` (no factor of the top size). -/
def mE (c : ℕ) (e : List ℕ) : Poly := [(0 :: e, c)]

/-- The lengths of the templates `13 … 38`. -/
def tmplE : List Poly :=
  [mE 1 [0, 1], mE 1 [1], mE 1 [1, 1], pC 1, pC 1, mE 1 [0, 0, 1], mE 1 [0, 0, 0, 1],
    mE 1 [0, 0, 0, 0, 1], mE 2 [0, 0, 1], mE 1 [0, 0, 0, 0, 0, 0, 1], mE 2 [1, 1, 1], mE 4 [1, 1, 1],
    mE 4 [1, 0, 1], mE 2 [1, 0, 1], mE 4 [0, 0, 1, 0, 0, 0, 1], mE 1 [1, 0, 0, 0, 0, 0, 0, 1], mE 1 [0, 0, 0, 0, 0, 1],
    mE 1 [1, 1, 0, 1], mE 1 [1, 0, 0, 1], mE 1 [1, 1, 0, 0, 1], mE 1 [1, 0, 0, 0, 1],
    mE 4 [1, 1, 1, 0, 0, 0, 1], mE 4 [1, 0, 2, 0, 0, 0, 1], mE 2 [1, 1, 1, 0, 0, 1], mE 1 [0, 0, 0, 0, 0, 0, 0, 0, 1],
    mE 1 [1, 1, 1]]

/-- The abstract store at the entry of the core: the templates at their lengths, every other tape
at most the top size. -/
def σE : Asg := List.replicate 13 pTop ++ tmplE ++ List.replicate 81 pTop

/-- The sweeps of the core. -/
def wE : Poly :=
  [([], 179),
  ([0, 0, 1], 34),
  ([0, 0, 0, 1], 34),
  ([0, 1, 0, 1], 9),
  ([0, 1, 1, 1], 36),
  ([0, 0, 1, 1], 11),
  ([0, 0, 0, 0, 1], 88),
  ([0, 1, 1, 0, 1], 149),
  ([0, 0, 0, 0, 2], 4),
  ([0, 1, 1, 0, 2], 3),
  ([0, 1, 0, 0, 1], 145),
  ([0, 2, 0, 0, 1], 61),
  ([0, 2, 1, 0, 1], 97),
  ([0, 2, 2, 0, 1], 22),
  ([0, 0, 1, 0, 1], 23),
  ([0, 1, 1], 134),
  ([0, 0, 0, 0, 0, 1], 88),
  ([0, 1, 1, 0, 0, 1], 149),
  ([0, 0, 0, 0, 0, 2], 4),
  ([0, 1, 1, 0, 0, 2], 3),
  ([0, 1, 0, 0, 0, 1], 145),
  ([0, 2, 0, 0, 0, 1], 61),
  ([0, 2, 1, 0, 0, 1], 97),
  ([0, 2, 2, 0, 0, 1], 22),
  ([0, 0, 1, 0, 0, 1], 23),
  ([0, 1], 145),
  ([0, 2], 61),
  ([0, 2, 1], 97),
  ([0, 2, 2], 22),
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 3),
  ([0, 0, 0, 0, 0, 0, 0, 1], 27),
  ([0, 0, 0, 1, 0, 0, 0, 1], 72),
  ([0, 0, 0, 1, 1, 0, 0, 1], 62),
  ([0, 1, 1, 1, 1, 0, 0, 1], 146),
  ([0, 1, 0, 1, 1, 0, 0, 1], 112),
  ([0, 1, 1, 1, 0, 0, 0, 1], 248),
  ([0, 1, 0, 1, 0, 0, 0, 1], 112),
  ([0, 0, 1, 1, 0, 0, 0, 1], 28),
  ([0, 1, 2, 1, 0, 0, 0, 1], 12),
  ([0, 1, 0, 1, 0, 0, 0, 1, 1], 12),
  ([0, 0, 0, 0, 0, 0, 1], 49),
  ([0, 1, 1, 1, 0, 0, 1], 392),
  ([0, 1, 0, 1, 0, 0, 1], 346),
  ([0, 0, 0, 1, 0, 0, 1], 176),
  ([0, 0, 0, 2, 0, 0, 1], 16),
  ([0, 1, 1, 2, 0, 0, 1], 12),
  ([0, 2, 0, 1, 0, 0, 1], 122),
  ([0, 2, 1, 1, 0, 0, 1], 194),
  ([0, 2, 2, 1, 0, 0, 1], 44),
  ([0, 0, 1, 1, 0, 0, 1], 46),
  ([0, 1, 1, 0, 0, 0, 1], 3)]

set_option maxRecDepth 100000 in
/-- **The certificate of the core.** -/
theorem check_encCoreP : check 8 encCoreP σE [] wE = true := by decide +kernel

end AdvancedEncryption.RingBTVW.Prog
