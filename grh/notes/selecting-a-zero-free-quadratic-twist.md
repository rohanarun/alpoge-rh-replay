# How a single twist removes cancellation for every character

Fix a modulus $N$, an invertible class $a$ whose primes are $7\bmod 8$ and
coprime to $N$, a height $H\ge0$, and $1/2<\beta<1$. A prime $d$ of the
class is bad if **some** character $\xi\bmod N$ has a quadratic twist
$\xi(\cdot/d)$ with a zero in $\Re s\ge\beta$, $|\Im s|\le H$. The proof
needs one $d$ outside this union. Choosing a different prime for each
character would leave twisted zeros in the sum of logarithmic derivatives.
[Compact criterion](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Endgame/OneSidedCriterion.lean#L28) ·
[Maintained criterion](https://github.com/leanprover-community/riemann-hypothesis/blob/c5451bd3ba92480e05c4218f5221bb2900c58706/src/New/Reduction/Zeros/Criterion.lean#L41)

## From a zero to a power saving

Let $J$ be the integral of the absolute theta tails for a primitive twist
and its Möbius-weighted coefficients, truncated at $1/T$. The proof uses the
test function $F=\Gamma_j L\,\mathcal M-\Gamma_j^2$, where $\mathcal M$ is
the truncated mollifier. If $J\le T^\alpha$ and the conductor is at most
$T^2$, the boundary estimates give $|F|\ll T^{2\alpha}$ on $\Re s=1/2$
and $|F|\ll T^{-1}$ on $\Re s=2$. At a zero of $L$, one has
$|F|=|\Gamma_j|^2$, bounded below on the fixed rectangle
$1/2\le\Re s\le1$, $|\Im s|\le H$. Zeros further right are already
excluded for these nonprincipal twists.
[Compact boundary estimate](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Analytic/QuadraticTwist/ZeroFreeTwist.lean#L25) ·
[Maintained boundary estimates](https://github.com/leanprover-community/riemann-hypothesis/blob/c5451bd3ba92480e05c4218f5221bb2900c58706/src/Lib/Analytic/QuadraticTwist.lean#L221)

Write $\Delta=\beta-1/2$ and $w=\Delta/(3/2)$. By three-lines interpolation
the exponent at any point of the rectangle with $\Re s\ge\beta$ is at most
$2\alpha(1-w)-w$. If this is negative, the lower bound at a zero forces
$J>T^\alpha$ once $T$ is large enough. In the formal proof
$\Delta=9\delta$ and $\alpha=2\delta$, so the exponent at the left edge
of this smaller rectangle is $-2\delta-24\delta^2$.

The available first-moment estimate is $\sum J\ll_\epsilon T^{2+\epsilon}$
for every $\epsilon>0$. It sums over integer parameters after quadratic
reciprocity, so it bounds the subsum of the nonnegative tails indexed
by the bad primes for each fixed character. The number of such primes is
therefore $O(T^{2+\epsilon-\alpha})$. For $d\le X$, taking $T^2=NX$ covers
the conductor of every primitive inducing twist. Changing level introduces
only Euler factors that are nonzero in this box. Summing over the finitely
many characters preserves the power saving. The compact edition states a
per-character count and takes the union in the selection lemma. The
maintained edition takes the union in the counting lemma itself.
[First-moment estimate](https://github.com/leanprover-community/riemann-hypothesis/blob/c5451bd3ba92480e05c4218f5221bb2900c58706/src/Lib/Analytic/QuadraticTwist.lean#L629) ·
[Compact count and selection](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Analytic/QuadraticTwist/ZeroFreeTwist.lean#L147) ·
[Maintained count](https://github.com/leanprover-community/riemann-hypothesis/blob/c5451bd3ba92480e05c4218f5221bb2900c58706/src/Lib/Analytic/QuadraticTwist.lean#L737)

## How much saving the selection uses

Let $B(X)$ count the union of bad primes in the class. The proof takes
$\epsilon=\delta$ and obtains $B(X)\ll X^{1-\delta/2}$. The same boundary
and moment estimates give a stronger bound when their exponents are
chosen separately.

$$
 B(X)\ll_{N,H,\beta,\gamma} X^{1-\gamma}
 \qquad\left(0<\gamma<\frac{w}{4(1-w)}
                  =\frac{\beta-1/2}{4(2-\beta)}\right).
$$

Indeed, choose $2\gamma<\alpha<w/(2(1-w))$ and
$0<\epsilon\le\alpha-2\gamma$. This makes the interpolation exponent
negative and gives the stated counting exponent. For instance, at
$\beta=3/4$, $\alpha=1/12$ and $\epsilon=1/60$ give interpolation exponent
$-1/36$ and counting exponent $1-1/30$. The maintained theorem's
$1-1/72$ already suffices.

For any positive saving $\gamma$, the bad primes in $[2^k,2^{k+1})$
contribute $O((k+1)2^{-k\gamma})$ to $\sum_d(\log d)/d$. Their total
weight is finite, whereas that of the primes in the invertible class
diverges. Hence the good primes carry a divergent total weight, and one
can avoid any prescribed finite set. In the zero-free criterion one sets
$H=|\Im\rho|$ for the candidate zero $\rho$. The bounds may depend on
that height. The selected $d$ works simultaneously for every character
in that box, which is what eliminates all twisted zero orders in the
residue at $\rho$.
[Maintained prime selection](https://github.com/leanprover-community/riemann-hypothesis/blob/c5451bd3ba92480e05c4218f5221bb2900c58706/src/Lib/Analytic/QuadraticTwist.lean#L795)
