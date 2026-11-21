# A short primitive mark in a lattice with Haar transverse quotient

For every fixed dimension and every proper terminal block of size at least two, the probability of the Part 8 event tends to **zero** as the marked length tends to zero in the model below. This holds for every selection of a fully BKZ-reduced basis. The reason is early recovery. A separate flag estimate bounds failure with a *nonzero* projection, including loss of primitivity.

## The probability space

Simply adjoining an independent uniform direction of length $r>0$ to a full-rank Haar lattice in dimension $n\ge3$ almost surely destroys discreteness. Conditional on the lattice $B$, the exceptional directions for which $mu\in B$ for some positive integer $m$ are countable. Otherwise the multiples of $u$ are distinct modulo $B$. Compactness of the torus gives a convergent subsequence and differences of representatives approaching zero in $B+\mathbb Zu$.

Instead choose $u=r\theta$ with uniform unit direction. In $u^\perp$, of dimension $h=n-1$, choose a Haar unimodular lattice $H$ in orthonormal coordinates independently of the direction, and put $M=r^{-1/h}H$. Choose a uniform character $f:M\to\mathbb R/r\mathbb Z$ (independent uniform values on a basis). Define
$$
 L=\{y+t\theta:y\in M,\ t\bmod r=f(y)\}.
$$
Lifting a basis of $M$ and adjoining $u$ gives a basis of $L$, with determinant $r\det M=1$. Projection $P$ off the mark maps $L$ onto $M$ with kernel $\mathbb Zu$, so the mark is primitive. This defines the marked experiment directly. All estimates below even allow arbitrary lift characters. Haar counting is applied only in the transverse dimension.

## How often can the mark reach a proper terminal block?

Let $2\le\beta<n$, $k=n-\beta$, and $p=p_0^{(k)}$ be the deterministic Part 6 constant. Let $S$ mean that the projected shortest vectors are exactly the two signed projections of $u$, both nonzero. Then
$$
 \Pr(S)\le \Pr(\exists\text{ fully BKZ-reduced basis with }u\text{ outside its rank-}k\text{ prefix})
 \le \min\{1,A(h,1)e^{hp}r^n\}.
$$
Indeed every vector outside the marked line has length at least $\lambda_1(M)$. On $\lambda_1(M)>re^p$, Part 7 with $R=re^p$ forces **every** fully reduced basis to start with $\pm u$. Since $k\ge1$, the terminal projection vanishes. In the complementary event $H$ has a primitive line of generator length at most $r^{1+1/h}e^p$. The expected count of these lines gives the displayed upper bound. Here $A(h,1)=V_h/(2\zeta(h))$, with $V_h$ the volume of the unit ball. For $\beta=n$ the same argument with threshold $r$ instead gives $\Pr(S)\ge 1-A(h,1)r^n$, since the prefix is empty. [Part 6](wall1_prefix.md) and [Part 7](ratio_unique.md)

For instance at $n=3,\beta=2,r=1/4$, $e^p=2/\sqrt3$ and $A(2,1)=3/\pi$. Thus $\Pr(S)\le 1/(16\pi)$, while the probability every reduced basis starts with the mark is at least $1-1/(16\pi)$. An explicit instance is the diagonal basis of lengths $(1/4,2,2)$ marked at its first vector. Its determinant is one, every projected block starts with a shortest vector by orthogonality, and the marked projection is zero. The probability estimate applies to the ensemble independently of this single example.

## A simultaneous bound for the two nonzero failure modes

For $1\le j<h$ put $F_j(T)=\min(1,A(h,j)r^j T^h)$ with the constant of Part 5. Set $F_h(T)=\mathbf1_{T\ge1/r}$. These bound the probability that $M$ contains a primitive rank-$j$ subgroup of determinant at most $T$. Indeed its counterpart in $H$ has determinant at most $r^{j/h}T$, so the assertion follows from the first moment, with the full-rank case given by $\det M$. [Part 5 and its constants](wall1_sublattice.md), [Kim's mean value formula](https://arxiv.org/abs/2005.10874)

For any $X>0$, the probability that **some** primitive rank-$k$ prefix $W$ of determinant at most $X$ has nonzero marked projection and fails Part 8 is at most
$$
 \min\{1,F_k(X/2)+F_{k+1}(Xr)\}.
$$
To prove this, write $v=\pi_W u\ne0$. Then $P$ is injective on the real span of $W$. In $L/W$ the divisibility $a$ of $u+W$ equals the order of the torsion subgroup after quotienting by that element (extend its primitive direction to a basis). This last quotient is $M/PW$. Thus $PW$ has index $a$ in its saturation. Orthogonal projection contracts volumes, so when $a\ge2$ its saturation has determinant at most $X/2$.

For an off-line failure Part 8 supplies a primitive rank-$(k+1)$ extension $U$ excluding $u$ with $\det U\le\det W\,\|v\|\le Xr$. Primitivity implies its real span excludes $u$. Therefore $PU$ has rank $k+1$ and its saturation has determinant at most $Xr$. The two transverse counts and a union bound finish the proof. For full BKZ one may substitute the deterministic $X=e^{U_k}$ of Part 6. The bound controls the joint event of failure and nonvanishing, without conditioning the Haar law on the selected prefix. [Part 8](wall1_planted_flags.md)

The transverse argument also gives a deterministic reduction for any primitive mark in a unimodular lattice. Transferring the probabilities requires small-sublattice counts for its actual transverse quotient. A lower bound for terminal success additionally needs the selected prefix's probability of excluding the mark. In the very-short-mark regime that probability itself goes to zero for full BKZ. No comparison in block size with the q-ary GSA prediction or bound for the verified slide output follows here.


## Independent audit (Nov 2026)

Verdict: **correct** (construction, early-recovery bound via Part 7, the value (3/π)(4/3)(1/4)³ = 1/(16π) ≈ 0.0199, and the flag estimate all checked).
