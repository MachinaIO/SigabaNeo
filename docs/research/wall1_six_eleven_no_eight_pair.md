# A six-support circuit excludes two norm-eight minima on eleven positions

Consider the c=6,H=11 no-norm-six family in the two-relation coefficient
cover, over q=3329. The code has full support and contains the prescribed
six-support circuit. Any balanced norm-eight vector has unit support eight,
or has support five or two. Girth six excludes the last two possibilities.

Suppose two independent norm-eight vectors generate the short plane. Their
supports cover all eleven positions, since their reductions span the
full-support rank-two code. Each has three exclusive positions and they
share five. The projective column classes are the two exclusive groups of
size three and the two possible shared sign groups. A codeword of support
six must vanish on a class of size five. Therefore all five shared columns
have the same relative sign, and the vectors have scalar product +/-5.
Their sum or difference then has squared norm 16-10=6, contradicting the
no-six family. Equivalently this pair cannot be Gauss reduced.

These column classes are identical over the rationals and over F_3329:
all entries are 0,+/-1 and the distinct slopes are 0,infinity,+1,-1.
An exclusive coordinate from each vector gives a unit minor, so their
integer span is saturated and their reductions remain independent. The
existing short-plane lifting cutoff is unchanged.

Consequently the reduced squared minima are either (8,at least10), with
second squared GS length at least10-8/4=8, or the first minimum is at least10,
with the usual lower GS pair (10,15/2). Thus the complete no-six bound can
use K(8,8)^N+K(10,15/2)^N, minimized with the previous complete bound.
Here K includes the original cutoff14 tail and all periodic terms. No
coefficient class is removed and no new addback is required.

The exact checker fixes an arbitrary balanced unit-eight first row and
enumerates all3920 full-support balanced second rows. All304 pairs with a
six-support codeword have inner product magnitude5 and a norm-six difference.
Fixing the first row loses no generality: permutations and global negation
preserve balance and cover every such first row. This computation supports
the all-configurations argument above, not a claim of completed BKZ success.

Run `python3 docs/research/scripts/wall1_six_eleven_no_eight_pair.py`.
