"""Emit the geometric witnesses for the input clauses of the pruned E7 refutation."""
import argparse
import json
from itertools import combinations_with_replacement
from pathlib import Path

from watson_e7_certificate import checks, join, table, write_module
from watson_six_contact_tables import inverse, mat, vec
from watson_six_resolution import named_table

OPEN = 'open Matrix MaskResolution Local ContactCone\n'
PAIRS = list(combinations_with_replacement(range(7),2))


def pack(row, width):
    assert all(0 <= x < 1 << width for x in row)
    return sum(x << (width*i) for i,x in enumerate(row))


def family(folder, stem, imports, count, segment, predicate, proof):
    deps, spans = [], []
    for a in range(0,count,segment):
        module = stem+str(a)
        deps.append(module)
        local, statements = [], []
        for i in range(a,min(count,a+segment)):
            label = f'{stem}At{i}'
            statements.append(f'private theorem {label} : ∀ j : Fin 1, {predicate} ({i}+j.val) := by\n'
                              f'  intro j; have eq := Fin.eq_zero j; subst j\n'+proof(i))
            local.append((i,1,label))
        label = f'{stem}From{a}'
        statements.append(join(local,predicate,label))
        spans.append((a,len(local),label))
        write_module(folder,module,imports,OPEN+'\n'.join(statements))
    return deps, join(spans,predicate,stem+'All')


def emit(folder, data, used):
    z = data['contacts']
    selected = [data['reasons'][i] for i in used]
    rels = sorted({r[1] for r in selected if r[0]=='relation'})
    relids = {r:i for i,r in enumerate(rels)}
    weights = []
    for q in data['inverse']:
        row = [0]*63
        for j,t in zip(data['basis'],q,strict=True): row[j]=2*t
        weights.append(row)
    lookup = [[PAIRS.index(tuple(sorted([a,b]))) for b in range(7)] for a in range(7)]
    column_words = [hex(pack([v[j]+2 for v in z],3)) for j in range(7)]
    body = OPEN + f'''private def column : Fin 7 → ℕ := {vec(column_words)}
def Z (i : Fin 63) (a : Fin 7) : ℤ := (((column a >>> (3*i.val)) % 8 : ℕ) : ℤ) - 2
'''
    write_module(folder,'WatsonE7Lines',['WatsonSevenSupport'],body)
    body = OPEN + f'''theorem tight : ∀ i, Z i ≠ 0 ∧ value (representative 12) (Z i) = 1 :=
  fun i ↦ tight_of_rat (Z i) ((by decide +kernel : ∀ j, (fun a ↦ (Z j a : ℚ)) ⬝ᵥ (forms 12 *ᵥ fun a ↦ (Z j a : ℚ)) = 1) i)
private def coeff : Fin 28 → Fin 63 → ℤ := {vec(map(vec,weights))}
private def lookup : Fin 7 → Fin 7 → Fin 28 := {vec(map(vec,lookup))}
private def w (a b : Fin 7) := coeff (lookup a b)
'''
    for a in range(7):
        body += f'private theorem mom{a} : ∀ b x y, ContactCone.moment Z (w {a} b) x y = {data["scale"]} * (ContactCone.picked {a} b x y + ContactCone.picked b {a} x y) := by decide +kernel\n'
    body += f'''theorem separates : ∀ D, D.IsHermitian → (∀ i, contact (Z i) D = 0) → D = 0 := by
  apply separates_of_moments Z {data["scale"]} (by decide) w
  intro a; fin_cases a
''' + ''.join(f'  · exact mom{a}\n' for a in range(7))
    write_module(folder,'WatsonE7Separates',['WatsonE7Lines'],body)

    # Words are split into blocks of five original generators. Each cached block
    # is identified with its product by checking the action on all 63 lines.
    words = [r[-1] for r in selected if r[0] in ('symmetry','ray')]
    subwords = sorted({tuple(w[j:j+5]) for w in words for j in range(0,len(w),5)})
    wordids = {w:i for i,w in enumerate(subwords)}
    def blocks(w):
        return [wordids[tuple(w[j:j+5])] for j in range(0,len(w),5)]
    orig = data['permutations']
    body = OPEN + '''def coord (w : ℕ) (i : Fin 63) : Fin 63 := Fin.ofNat 63 ((w >>> (6*i.val)) % 64)
'''
    def permdef(name,p):
        ip = [p.index(j) for j in range(63)]
        return (f'def {name} : Equiv.Perm (Fin 63) :=\n'
                f'  ⟨coord {hex(pack(p,6))}, coord {hex(pack(ip,6))}, by decide +kernel, by decide +kernel⟩\n')
    for i,(p,g) in enumerate(zip(orig,data['generators'],strict=True)):
        body += permdef(f'generator{i}',p)
        body += f'''private def unit{i} : IntMat := {mat(g)}
private def inverse{i} : IntMat := {mat(inverse(g))}
private theorem real{i} : Realizes (cone 12) Z generator{i} := by
  apply Local.realized generator{i} unit{i} inverse{i}
  · exact matrix_eq_of_entries _ _ (by decide +kernel)
  · exact matrix_eq_of_entries _ _ (by decide +kernel)
  · decide +kernel
'''
    body += f'''def generators : Fin 2 → Equiv.Perm (Fin 63) := {vec(['generator0','generator1'])}
theorem generators_realize : ∀ i, Realizes (cone 12) Z (generators i) := by
  intro i; fin_cases i
  · exact real0
  · exact real1
'''
    write_module(folder,'WatsonE7Generators',['WatsonE7Lines'],body)
    body = OPEN
    for i,w in enumerate(subwords):
        p = list(range(63))
        for g in w: p=[p[j] for j in orig[g]]
        body += permdef(f'block{i}',p)
        body += f'''private theorem valid{i} : Realizes (cone 12) Z block{i} := by
  have h : block{i} = Six.composeWord generators {list(w)} :=
    Equiv.ext (by decide +kernel)
  rw [h]
  exact realizes_word _ generators_realize _
'''
    n = len(subwords)
    body += '\n'.join(named_table('permutation', 'Equiv.Perm (Fin 63)', [f'block{i}' for i in range(n)],True))
    body += f'\ndef perms (i : Fin {n}) := permutation i.val\n'
    # Fin.cases is sufficient for this small family.
    body += 'theorem autocert : ∀ i, Realizes (cone 12) Z (perms i) := by\n  intro i; fin_cases i\n'
    body += ''.join(f'  · exact valid{i}\n' for i in range(n))
    write_module(folder,'WatsonE7Permutations',['WatsonE7Generators'],body)
    rows = data['relations']
    body = OPEN + table('rowWord',[pack([t+5 for t in rows[r]],4) for r in rels])
    body += f'''def rows (r : Fin {len(rels)}) (i : Fin 63) : ℤ := (((rowWord r.val >>> (4*i.val)) % 16 : ℕ) : ℤ) - 5
abbrev relOK (r : ℕ) := ∀ a b, ContactCone.moment Z (rows (Fin.ofNat {len(rels)} r)) a b = 0
'''
    write_module(folder,'WatsonE7Rows',['WatsonE7Lines'],body)
    deps,root = checks(folder,'WatsonE7Relation',['WatsonE7Rows'],'relOK',len(rels),24,2)
    write_module(folder,'WatsonE7Relations',deps,root+f'''theorem relcert : ∀ r a b, ContactCone.moment Z (rows r) a b = 0 := by
  intro r; simpa [relOK,Fin.ofNat,Nat.mod_eq_of_lt r.isLt] using WatsonE7RelationAll r
''')
    values = [[sum(t*v[a]*v[b]*(1 if a==b else 2) for t,(a,b) in zip(seed,PAIRS,strict=True))
               for v in z] for seed in data['raySeeds']]
    width = max(max(v) for v in values).bit_length()
    body = OPEN + table('valueWord',[pack(v,width) for v in values])
    body += f'''def values (r : Fin 157) (i : Fin 63) : ℤ := ((valueWord r.val >>> ({width}*i.val)) % {1<<width} : ℕ)
abbrev seedOK (i : ℕ) := SeedValid (cone 12) Z (values (Fin.ofNat 157 i))
'''
    write_module(folder,'WatsonE7Values',['WatsonE7Lines'],body)
    def seedproof(i):
        return f'''  apply Local.seedValid_of_pivot Z _ ⟨{i}, by decide +kernel⟩
  · exact matrix_eq_of_entries _ _ (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel'''
    deps,root = family(folder,'WatsonE7Seed',['WatsonE7Values'],157,10,'seedOK',seedproof)
    write_module(folder,'WatsonE7Seeds',deps,OPEN+root+'''theorem seedcert : ∀ r, SeedValid (cone 12) Z (values r) := by
  intro r; simpa [seedOK,Fin.ofNat,Nat.mod_eq_of_lt r.isLt] using WatsonE7SeedAll r
''')
    # Tag in the low two bits. Words use six bits per block with zero as terminator.
    assert n<=63
    def wordcode(w): return pack([i+1 for i in blocks(w)],6)
    codes = []
    for tag,*args in selected:
        if tag=='nonzero': code=0
        elif tag=='relation':
            r,i=args
            code=1+4*(i+64*(int(rows[r][i]<0)+2*relids[r]))
        elif tag=='symmetry': code=2+4*wordcode(args[0])
        else: code=3+4*(args[0]+256*wordcode(args[1]))
        codes.append(code)
    body = OPEN + table('reasonCode',codes,8,max(x.bit_length() for x in codes))
    body += f'''private def decodeWord : ℕ → ℕ → List (Fin {n})
  | 0, _ => []
  | k+1, w => if w = 0 then [] else Fin.ofNat {n} ((w % 64)-1) :: decodeWord k (w >>> 6)
def reason (i : ℕ) : Six.Reason 63 {n} {len(rels)} 157 :=
  let w := reasonCode i
  let a := w >>> 2
  match w % 4 with
  | 0 => .nonzero
  | 1 => .relation (Fin.ofNat {len(rels)} (a >>> 7)) (a.testBit 6) (Fin.ofNat 63 (a % 64))
  | 2 => .symmetry (decodeWord 5 a)
  | _ => .ray (Fin.ofNat 157 (a % 256)) (decodeWord 5 (a >>> 8))
abbrev inputOK (i : ℕ) := Six.usable perms rows values (bank i) (reason i)
'''
    write_module(folder,'WatsonE7Reasons',['WatsonE7Permutations','WatsonE7Rows','WatsonE7Values','WatsonE7RupBank'],body)
    deps,root = checks(folder,'WatsonE7Input',['WatsonE7Reasons'],'inputOK',len(used),48,8)
    write_module(folder,'WatsonSevenContacts12',deps+['WatsonE7Relations','WatsonE7Seeds','WatsonE7Separates','WatsonSevenResolution12'],OPEN+root+'''
theorem normal : NormalSupport (cone 12) Z :=
  normal_of_clauses Z perms rows values autocert relcert seedcert bank reason
    (by simpa using WatsonE7InputAll) unsat

theorem coverage : RayCoverageAt 12 := Local.coverage Z tight separates normal
''')


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('scratch',type=Path)
    parser.add_argument('folder',type=Path)
    args=parser.parse_args()
    emit(args.folder,json.loads((args.scratch/'support12.json').read_text()),
         json.loads((args.scratch/'used12.json').read_text()))
