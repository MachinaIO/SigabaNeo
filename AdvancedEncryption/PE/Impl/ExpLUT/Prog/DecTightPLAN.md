# Tight clock of the ExpLUT `Dec` machine (`Prog/DecTight*.lean`)

**Result:** `AdvancedEncryption.ExpLUT.Prog.DecConf.time_decMachine_tight : decMachine.time ≤ 2 ^ 225`
(`Prog/DecTight.lean`). This replaces `DecConf.time_decMachine : decMachine.time ≤ 2 ^ 727`.
Axioms: `propext, Classical.choice, Quot.sound`. There is no `sorry`, no `native_decide` and no new axiom.

## Files (import chain)

| module | content | build (fresh) |
|---|---|---|
| `DecTightBase` | `dtChk` (block checker on `DecT.absRun`) + `dtChk_sound`; `CodeOK` glue (`codeOK_seqT/monoT/nopT`); parameters `dtP` (`Mo = 2^40`, `Mt = 2^25`) + `dtP_valid`; `pkL` | 1.6 s |
| `DecTightData` | generated literal bound vectors at block boundaries (`dtB0 … dtBend`) and clock claims (`dtT…`) | 2.2 s |
| `DecTightLutF` | `dtChk_lutF`: `lutC false` (one kernel run, ≈ 55k abstract instruction evaluations) | 97 s |
| `DecTightLutT` | `dtChk_lutT`: `lutC true` | 95 s |
| `DecTightPre` | the splits, `fixC`, the copies, `mulC i`/`tblC i` for all `i < 16`, the step tails, `finC` | 4.7 s |
| `DecTightVM` | `dt_decCode : CodeOK (2^40) N K decCode (toB dtB0) (toB dtBend) dtTvm`, `dtTvm_le : dtTvm ≤ 2^224` | 1.6 s |
| `DecTightFront` | shape `dtFv` (op area / templates / registers / other tapes); parse, length test, templates (exact lengths), constants, framed code, output, invalid branch | 4.8 s |
| `DecTight` | `fu_decProgram`, `fu_total`, **`time_decMachine_tight`** | 1.9 s |

`DecTightLutF` and `DecTightLutT` are independent, so lake builds them in parallel. A full fresh
build of the eight modules takes 1 min 51 s wall-clock.

## How it works

* **VM part.** `DecT.absRun` (the flow-sensitive interpreter of `DecTimeVM`, already proved sound) is
  run **block by block** with `decide +kernel` (`dtChk`). The bound vectors at the block boundaries are literals
  (`DecTightData`), and blocks are glued with generic `CodeOK` lemmas, so no concrete code is
  unfolded by the glue.
  * Reuse: steps `1 … 15` start from the same bound vector `dtBs`, and step 0's start vector is below it.
    So `dtBs` is an invariant of every step. `lutC false` is certified **once** and used 15 times;
    `lutC true` is certified once. `mulC i` and `tblC i` are checked for all `i < 16` in one bounded `decide` each.
    The bound vectors don't depend on `i`; the clock claim is the maximum, at `i = 15`. `dt_stepsN` is the
    induction over `stepsN`.
  * The operation area is `Mo = 2^40 = N K` (it was `2^110`). That needs the front to keep tapes
    `0 … 39` empty and the registers apart, which is what `dtFv` does.
  * VM clock: `dtTvm ≈ 2^223.7`. 16 × `lutC` (≈ 2^219.7 each) dominates. Inside `lutC`, the 22
    automorphism rounds' stream moves (`.mv 126 166 77`, ...) cost `(2·|stream|+3)·10·|count|`
    with a 2^97.5-bit stream. That is inherent to the bit-by-bit move cost model and the static (non-decreasing) stream bounds.
* **Front.** Parsing ≈ 2^220.7 (`Prog.ubp_unfrP`, doubling bounds up to 2^109), the length test
  ≈ 2^221.6 (`lenEqP_bounds` with `S = 2^109`), templates ≈ 2^209.9 (each charged
  `(2n+1)(4M+12)` with its own `n`, generic `vb_tmplsT`; `κD` is bounded by `2N` via `mod_lt`, so it is never
  evaluated), constants ≈ 2^151, output/invalid branches ≈ 2^111.
* Total ≈ 2^224.13, so `T = 225`, the best power of two for this analysis.

## Kernel lessons applied

* The concrete composite programs are never unfolded with `show`/`rfl` in the timing lemmas. Only
  `stepC`/`devalC`/`decCode` are unfolded one `ofList` layer (cheap; their blocks are opaque constants).
* `omega` does not see `Pi`-order facts like `hℓ i : ℓ i ≤ L i`, because the `≤` instance is left unreduced.
  State them with a type ascription (`show ℓ 43 ≤ L 43 from hℓ 43`) or through `dtPile`.
* The generated literals are trusted nowhere. They only enter through `dtChk … = true` checked by `decide +kernel`.

## Regenerating `DecTightData` (only needed if `decCode` or the parameters change)

1. Serialize the code (scratch file outside the repo, `lake env lean ser.lean`; takes about 4 s):

```lean
import PE.Impl.ExpLUT.Prog.DecTimeConf
open AdvancedEncryption.ExpLUT.Prog SigabaNeo.Tape.RingVM
def ser : Code → List String → List String
  | .add d a b, acc => s!"add {d} {a} {b}" :: acc
  | .sub d a b, acc => s!"sub {d} {a} {b}" :: acc
  | .mul d a b, acc => s!"mul {d} {a} {b}" :: acc
  | .canon d a, acc => s!"canon {d} {a}" :: acc
  | .neg d a, acc => s!"neg {d} {a}" :: acc
  | .digit d a t, acc => s!"digit {d} {a} {t}" :: acc
  | .rotB d a t, acc => s!"rotB {d} {a} {t}" :: acc
  | .aut d a t, acc => s!"aut {d} {a} {t}" :: acc
  | .rhoJ d a t, acc => s!"rhoJ {d} {a} {t}" :: acc
  | .mv d s c, acc => s!"mv {d} {s} {c}" :: acc
  | .cp d s, acc => s!"cp {d} {s}" :: acc
  | .drop t c, acc => s!"drop {t} {c}" :: acc
  | .clr t, acc => s!"clr {t}" :: acc
  | .tl t, acc => s!"tl {t}" :: acc
  | .nop, acc => "nop" :: acc
  | .rep c b, acc => s!"rep {c}" :: ser b acc
  | .seq p q, acc => "seq" :: ser p (ser q acc)
  | .ifb t p q, acc => s!"ifb {t}" :: ser p (ser q acc)
#eval IO.FS.writeFile "decCode.txt" ("\n".intercalate (ser decCode []))
```

2. Run the Python mirror of `DecT.absRun` below, `python3 -I dectight_gen.py decCode.txt states.lean`
   (under 1 s). Paste `states.lean` into `DecTightData.lean` after the header. The `#eval`
   interpreter is far slower than this mirror, and slower than the kernel too.

```python
import sys, math
sys.setrecursionlimit(100000)
Wd = 2**256
K = 2**16; N = 2**24; NK = N*K

def parse(path):
    toks = open(path).read().split('\n')
    pos = 0
    def go():
        nonlocal pos
        t = toks[pos].split(); pos += 1
        op = t[0]
        if op == 'seq':
            p = go(); q = go(); return ('seq', p, q)
        if op == 'ifb':
            p = go(); q = go(); return ('ifb', int(t[1]), p, q)
        if op == 'rep':
            b = go(); return ('rep', int(t[1]), b)
        return (op,) + tuple(int(x) for x in t[1:])
    return go()

def mEval(rho, es):
    r = 1
    for i, e in enumerate(es):
        r *= (rho[i] if i < len(rho) else 0) ** e
    return r
def pEval(rho, p): return sum(c * mEval(rho, m) for (m, c) in p)
def rhoLd(T, N, K, m): return [T, N, K, m, 0, 0, 0]
wNotM = [([], 15), ([0, 1, 1], 11)]
wRhoJ = [([], 3), ([0, 0, 0, 1], 4), ([0, 0, 1, 1], 7)]
wRotB = [([], 3), ([0, 0, 0, 1], 11), ([0, 1, 0, 1], 19), ([0, 1, 1, 1], 18)]
wMulRM = [([], 24), ([0, 1], 29), ([0, 1, 1], 24), ([0, 2], 71), ([0, 2, 1], 107), ([0, 2, 2], 22), ([0, 0, 1], 7)]
wAut = [([], 10), ([0, 1], 55), ([0, 1, 1], 40), ([0, 1, 0, 1], 8), ([0, 1, 1, 1], 14)]
wCanon = [([], 7), ([0, 1], 44), ([0, 1, 1], 40)]

class P: pass
def mkP(Mo, Mt, wDigitM):
    p = P(); p.Mo = Mo; p.N = N; p.K = K; p.Mt = Mt
    p.cAdd = 40*NK + 44*N + 7
    p.cMul = pEval(rhoLd(Mo,N,K,0), wMulRM)
    p.cCanon = pEval(rhoLd(Mo,N,K,0), wCanon)
    p.cNeg = pEval(rhoLd(Mo,N,K,0), wNotM)
    p.cDig = pEval(rhoLd(Mo,N,K,Mt), wDigitM)
    p.cRot = pEval(rhoLd(Mo,N,K,Mt), wRotB)
    p.cAut = pEval(rhoLd(Mo,N,K,Mt), wAut)
    p.cRho = pEval(rhoLd(Mo,N,K,Mt), wRhoJ)
    return p

def bset(B, x, v):
    B = list(B); B[x] = min(v, Wd - 1); return B
def rset(P, B, d): return bset(B, d, max(B[d], NK))
def bmax(A, B): return [max(a, b) for a, b in zip(A, B)]
def ble(A, B): return all(a <= b for a, b in zip(A, B))

stats = {'instr': 0, 'rounds': 0}
def run(P, c, B, fuel=8):
    op = c[0]; Mo = P.Mo
    stats['instr'] += 1
    if op in ('add', 'sub', 'mul'):
        d, a, b = c[1:]; B2 = rset(P, B, d)
        W = P.cMul if op == 'mul' else P.cAdd
        T = (2*max(Mo,B2[a])+3)*(30+10*NK) + (2*max(Mo,B2[b])+3)*(30+10*NK) + (2*Mo+3)*W + (2*max(Mo,B2[d])+3)*10
        return B2, T
    if op in ('canon', 'neg'):
        d, a = c[1:]; B2 = rset(P, B, d)
        W = P.cCanon if op == 'canon' else P.cNeg
        return B2, (2*max(Mo,B2[a])+3)*(30+10*NK) + (2*Mo+3)*W + (2*max(Mo,B2[d])+3)*10
    if op in ('digit', 'rotB', 'aut', 'rhoJ'):
        d, a, t = c[1:]; B2 = rset(P, B, d)
        W = {'digit': P.cDig, 'rotB': P.cRot, 'aut': P.cAut, 'rhoJ': P.cRho}[op]
        if not B2[t] <= P.Mt: raise Exception(f"template too big {c} {B2[t]}")
        return B2, (2*max(Mo,B2[a])+3)*(30+10*NK) + (2*max(Mo,B2[t])+3) + (2*Mo+3)*W + (2*max(Mo,B2[d])+3)*10
    if op == 'mv':
        d, s, cc = c[1:]
        return B, (2*max(B[s], max(B[d], B[cc]))+3)*(20+10*B[cc])+3
    if op == 'cp':
        d, s = c[1:]
        return bset(B, d, B[s]), 2*max(B[d], B[s])+3
    if op == 'drop':
        t, cc = c[1:]
        return B, (2*max(B[t], B[cc])+3)*(20+10*B[cc])+3
    if op in ('clr', 'tl'):
        return B, 2*B[c[1]]+3
    if op == 'nop': return B, 3
    if op == 'seq':
        B1, T1 = run(P, c[1], B, fuel); B2, T2 = run(P, c[2], B1, fuel); return B2, T1 + T2
    if op == 'ifb':
        B1, T1 = run(P, c[2], B, fuel); B2, T2 = run(P, c[3], B, fuel); return bmax(B1, B2), max(T1, T2) + 1
    if op == 'rep':
        t, b = c[1], c[2]
        X = B
        for _ in range(fuel):
            stats['rounds'] += 1
            X2, Tb = run(P, b, X, fuel)
            if ble(X2, X):
                return X, X[t]*(2*max(Mo, max(X))+3+Tb+1)+2
            X = bmax(X, X2)
        raise Exception("loopFix out of fuel")
    raise Exception(op)
wDigit = [([], 11), ([0, 0, 1], 11), ([0, 1, 1], 44), ([0, 1, 2], 18), ([0, 1], 28)]
wDigitM = wDigit + [([0, 1, 1, 1], 18), ([0, 1, 0, 1], 44), ([0, 0, 0, 1], 11), ([0, 1, 2, 0], 18)]
Mo = 2**40; Mt = 2**25
P0 = mkP(Mo, Mt, wDigitM)
mb = 3*NK + 408
init = [(1,1),(2,NK),(3,NK),(4,K),(5,K-1),(6,2*K*NK),(7,4*K*NK),(8,2*K),(9,2),(10,2*(2*K)*K*(2*K*NK)),
   (12,2**22),(13,22),(14,14),(15,K-2),(16,(mb+K)*NK),(17,mb+K),(18,44*2*K),(19,44*2*K*NK),(56,K*NK),(74,44),
   (78,14*2**22),(180,2*(mb+K)*NK),(181,44*(2*(2*K*NK))),(182,16*(2*K*NK)),(183,16*(2**34*(2*(2*K*NK)))),
   (184,22*(2**34*(2*(2*K*NK)))),(185,2*NK),(186,22*(2**34*(2*K*NK))),(187,16*(2**34*(2*K*NK))),(188,4*K),
   (189,2**92),(73,2**109),(75,1),(76,2**109),(77,2**109)] + [(20+t, 2*N) for t in range(22)] + [(42+b, 2*N) for b in range(14)]
B0 = [0]*200
for x, v in init: B0[x] = v
c = parse(sys.argv[1])
assert c[0] == 'seq'
S1 = c[1]; r = c[2]; S2 = r[1]; r = r[2]; F = r[1]; r = r[2]; DV = r[1]; FIN = r[2]
assert DV[0] == 'seq'; c1 = DV[1]; c2 = DV[2][1]; ST = DV[2][2][1]; assert DV[2][2][2] == ('nop',)
lst = []
s = ST
while s[0] == 'seq':
    lst.append(s[2]); s = s[1]
lst.reverse(); assert len(lst) == 16 and s == ('nop',)
def ceilT(T, sig=12):
    e = max(0, T.bit_length() - sig)
    m = -(-T // 2**e)
    return m, e
def le(A, B): return all(a <= b for a, b in zip(A, B))
states = {}; times = {}
states['dtB0'] = B0
B1, times['S1'] = run(P0, S1, B0); states['dtB1'] = B1
B2, times['S2'] = run(P0, S2, B1); states['dtB2'] = B2
B3, times['F'] = run(P0, F, B2); states['dtB3'] = B3
B4, times['c1'] = run(P0, c1, B3); states['dtB4'] = B4
B5, times['c2'] = run(P0, c2, B4)
Bs = run(P0, lst[0], B5)[0]
assert le(B5, Bs); states['dtBs'] = Bs
mt = 0; tt = 0
for i, st in enumerate(lst):
    m = st[1]; rest = st[2]; tb = rest[1]; lut = rest[2][1]; tail = rest[2][2]
    Bm1, T = run(P0, m, Bs); mt = max(mt, T)
    Bm, T2 = run(P0, tb, Bm1); tt = max(tt, T2)
    if i == 0: Bm1_0, Bm_0 = Bm1, Bm
    assert Bm1 == Bm1_0 and Bm == Bm_0
times['mul'] = mt; times['tbl'] = tt
states['dtBm1'] = Bm1_0; states['dtBm'] = Bm_0
lutF = lst[0][2][2][1]; lutT = lst[15][2][2][1]; tail = lst[0][2][2][2]
assert tail == lst[15][2][2][2]
XF, times['lutF'] = run(P0, lutF, Bm_0); XT, times['lutT'] = run(P0, lutT, Bm_0)
states['dtXF'] = XF; states['dtXT'] = XT
Y1, times['tailF'] = run(P0, tail, XF); Y2, times['tailT'] = run(P0, tail, XT)
assert le(Y1, Bs) and le(Y2, Bs)
Bend, times['fin'] = run(P0, FIN, Bs); states['dtBend'] = Bend
for k, v in times.items():
    print(k, "2^%.3f" % math.log2(v), ceilT(v))
def lean(name, B):
    items = ", ".join(f"({x}, {v})" for x, v in enumerate(B) if v)
    return f"/-- A bound vector (generated). -/\ndef {name} : ℕ := pkL [{items}]\n\n"
with open(sys.argv[2], 'w') as f:
    for nm, B in states.items():
        f.write(lean(nm, B))
    for k, v in times.items():
        m, e = ceilT(v); f.write(f"/-- A clock claim (generated). -/\ndef dtT{k} : ℕ := {m} * 2 ^ {e}\n\n")
print(Bend[179], max(Bend), max(max(v) for v in states.values()))
```

## Integration notes for the parent

* Aggregator: import `PE.Impl.ExpLUT.Prog.DecTight` (it imports the other seven modules).
* `time_decMachine_tight` can replace `DecConf.time_decMachine` (2^727) wherever the Dec clock
  enters the claimed cost (for example `SubmissionDec`). Its statement is the same with `2 ^ 225`.
* Every new name is in the `AdvancedEncryption.ExpLUT.Prog.DecTight` namespace, except
  `DecConf.time_decMachine_tight`. Generic short names carry a `dt`/`fu` prefix (`dtFv`, `dtPsh`,
  `dtL2`, …).
* Possible further tightening (not done): the parse and length-test bounds (≈ 2^221 each) come from the
  coarse doubling of `ubp_unfrP`, and a decreasing-stream abstract domain could lower the move costs. Neither
  helps below 2^224 without a new cost analysis of the move primitive.
