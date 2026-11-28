# The signed height behind Theorem C

Theorem C bounds $V+2\delta$ from below, where $V$ bounds log squared
covolume and $\delta$ bounds the index of an almost-spanning family.
Its proof selects a twist $\theta_\iota$ separately for each prime and
embedding $\iota$. Two facts are essential: each individual height bound
can be negative, and the two determinant bounds must use the **same**
choice at each embedding.
[Compact Theorem C](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Endgame/LongForms.lean#L63) ·
[Maintained Theorem C](https://github.com/leanprover-community/riemann-hypothesis/blob/c5451bd3ba92480e05c4218f5221bb2900c58706/src/New/Determinant/Twist/LongForms.lean#L274)

## An exact calculation for the height used here

Write $\mathcal H(c,u)$ for `HeightLe c u`. It permits one common nonzero
multiplier $H$, an archimedean bound $\log|\sigma H|\le a$ for every
$\sigma$, and finite-place bounds $|\iota(Hu_\iota)|_p\le p^{e_p}$ with
$e_p\ge0$. The cost $a+\sum_{p\in S}e_p\log p$ must be at most $c$ for
every finite set $S$. The archimedean term $a$ may be negative.
[Height definition](https://github.com/leanprover-community/riemann-hypothesis/blob/c5451bd3ba92480e05c4218f5221bb2900c58706/src/New/Reduction/Lattices/Heights.lean#L52)

Suppose $u_\iota=r_p\in\mathbf Q^\times$ at every embedding over $p$,
with $v_p(r_p)=0$ outside a finite set of primes. Its **least** admissible
bound is
$$
c_*=-\sum_p v_p(r_p)\log p .
$$
Indeed $H=\prod_p p^{-v_p(r_p)}$ makes each $H r_p$ a $p$-adic unit.
Set every $e_p=0$ and $a=\log H$. Applying the same construction to
$u^{-1}$ gives bound $-c_*$. Any bound $c$ for $u$ then gives bound
$c-c_*$ for the constant family $1$, so $c\ge c_*$ by the product formula.
For example $r_2=4$, $r_3=9$, $r_p=1$ elsewhere give $c_*=-\log 36$.
Thus a negative estimate for a family of determinant ratios is consistent
with the formal height definition.
[Product formula for the constant family](https://github.com/leanprover-community/riemann-hypothesis/blob/c5451bd3ba92480e05c4218f5221bb2900c58706/src/New/Reduction/Lattices/Heights.lean#L202)

## The two directions of the determinant estimate

Put $r_\iota=Z(\theta_\iota)/Z(1)$ for the forward ratio. Completing the
family to a basis makes the common basis determinant cancel from this
ratio. Clearing the original vectors costs $\delta$ at $\iota$ and
$\delta$ at its conjugate because the Gram pairing is Hermitian. If
$k$ vectors are added with bounds $S$ for log squared norm and $B$ for
the height of the inverse squared clearing scalar, the forward bound is
$V+2\delta+k(S+B)$. The reverse ratio receives a height bound $I$ from the
factorization of the chain into single lifts. Nonzero volumes give
$r_\iota r_\iota^{-1}=1$ at every $\iota$, hence
$$
0\le V+2\delta+k(S+B)+I .
$$
The product formula is applied to this constant family. Applying it to
$r$ alone would already fail for the explicit family above.
[Forward bound and cancellation](https://github.com/leanprover-community/riemann-hypothesis/blob/c5451bd3ba92480e05c4218f5221bb2900c58706/src/New/Reduction/Lattices/TwistedLattice.lean#L448) ·
[Inverse chain bound](https://github.com/leanprover-community/riemann-hypothesis/blob/c5451bd3ba92480e05c4218f5221bb2900c58706/src/New/Determinant/Twist/LongForms.lean#L192)

The compact proof bounds $r$ and $r^{-2}$, then squares the first bound.
With $D$ the target dimension, $E=fa\log^4 b$, and $M$ its main height,
this gives $0\le2(V+2\delta+Db)+2D(2E-M)$. Using $b\le E$ recovers
$D(M-3E)\le V+2\delta$. The maintained proof bounds $r^{-1}$ directly
and retains the completion cost until the final step.
[Compact forward and inverse bounds](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Endgame/LongForms.lean#L19) ·
[Maintained completion cost](https://github.com/leanprover-community/riemann-hypothesis/blob/c5451bd3ba92480e05c4218f5221bb2900c58706/src/New/Determinant/Twist/LongForms.lean#L223)

The coefficient $2$ on the index is already sharp in the underlying
lattice inequality. Take one complex coordinate with the standard
Hermitian form, only the identity twist and lift, and the usual
valuation ring at every embedding. For $y=p^{-k}$, $k>0$, the squared
covolume is $p^{-2k}$, and clearing $y$ at $p$ requires valuation $k$.
Thus $V=-2k\log p$, $\delta=k\log p$, the two ratios are one, and there
is no completion cost. Equality holds in $V+2\delta=0$. This tests the
lattice input to Theorem C independently of the arithmetic construction
of its twists.
