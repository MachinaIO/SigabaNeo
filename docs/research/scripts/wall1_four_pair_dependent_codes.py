"""Girth-filtered norm-four extensions of four-pair anchors."""
from collections import Counter
from itertools import combinations
from wall1_rare_second_line import norm_rows
from wall1_shared_dependent_codes import determinant


UPPER_COUNTS={84:96,116:24}

def det4(rows):
    return sum((-1)**j*rows[0][j]*determinant(*(tuple(row[k] for k in range(4) if k!=j) for row in rows[1:])) for j in range(4))


def exact_counts():
    results=[]
    for mixed in (False,True):
        pairs=[]
        for j in range(4):
            row=[0]*9;row[2*j]=1;row[2*j+1]=-1 if mixed else 1;pairs.append(row)
        rows=[tuple(x-y for x,y in zip(pairs[i],pairs[i+1])) for i in range(3)]
        adj=((12,8,4),(8,16,8),(4,8,12))
        counts=Counter();total=0
        for v in norm_rows(9,4):
            if not v[-1]:continue
            total+=1
            x=[sum(a*b for a,b in zip(row,v)) for row in rows]
            gram=128-sum(x[i]*adj[i][j]*x[j] for i in range(3) for j in range(3))
            columns=list(zip(*rows,v))
            minors={indices:det4([columns[i] for i in indices]) for indices in combinations(range(9),4)}
            assert 1 in map(abs,minors.values()) and max(map(abs,minors.values()))<7
            if all(any(minors[indices] for indices in combinations(complement,4))
                   for complement in combinations(range(9),6)):
                counts[gram]+=1
        assert total==168
        results.append(dict(sorted(counts.items())))
    assert results==[{84:96},{84:72,116:24}]
    assert {d:max(c.get(d,0) for c in results) for d in UPPER_COUNTS}==UPPER_COUNTS
    print('Affine type counts:',results)
    return results


if __name__=='__main__':exact_counts()
