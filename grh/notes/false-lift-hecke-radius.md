# The sharp small-root disk for a bounded spherical descent

In the false-lift argument, a descent is bounded, spherical at a split place of residue cardinality $q$, and killed by the Hecke polynomial $P(X)$. Both editions show that the descent vanishes if $q^{m+1}|X|\le1$, where $m$ is the local rank. For $m\ge1$, the same conclusion holds throughout $|X|<q^{-(m-1)}$. The constant function gives a kernel at the positive boundary point. [Compact vanishing lemma](https://github.com/leanprover-community/riemann-hypothesis/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/SiegelWeil/DescentsVanishPlanes.lean#L13-L28) · [Readable lemma and its application to a descent](../src/New/OneLift/FalseLifts/HyperbolicPlaneStep.lean)

Fix the other adelic coordinates. Right invariance under $K=\mathrm{GL}_m(\mathcal O)$ identifies the local function with a function of lattices $L=g\mathcal O^m$. For a uniformizer $\pi$, the transposed representatives in `heckePolyOp_eq_sum` run once through the sublattices $M$ with $\pi L\subseteq M\subseteq L$. For $j=\dim_{\mathbb F_q}(L/M)$ their coefficient is $(-X)^j q^{j(j-1)/2}$. In particular, the term for $M=L$ is the identity. [Coset representatives](../src/Lib/Weil/Unramified/HeckeGL.lean) · [Hecke polynomial acting on spherical vectors](../src/Lib/Weil/Unramified/HeckeTransfer.lean)

Define an operator on bounded functions by summing over all finite-index sublattices,

$$
(A(X)f)(L)=\sum_{M\subseteq L} X^{\operatorname{length}_{\mathcal O}(L/M)} f(M).
$$

For $r=|X|<q^{-(m-1)}$, this converges absolutely and uniformly in $L$. Indeed, a triangular basis matrix with diagonal $\pi^{e_1},\ldots,\pi^{e_m}$ has $q^{\sum_i(m-i)e_i}$ choices in column Hermite normal form. Each of the $m-i$ entries to the right of the $i$-th pivot is reduced modulo $\pi^{e_i}$. Summing over the $e_i\ge0$ gives the uniform majorant $\|f\|_\infty\prod_{j=0}^{m-1}(1-q^j r)^{-1}$.

Expand $A(X)P(X)f$ and fix an endpoint $N\subseteq L$. The allowable intermediate lattices $M$ correspond to the subspaces $M/N$ of $(L/N)[\pi]$. All paths to $N$ carry the same power $X^{\operatorname{length}(L/N)}$. If $k=\dim_{\mathbb F_q}(L/N)[\pi]$, the remaining coefficient is

$$
\sum_{j=0}^k {k\brack j}_q (-1)^j q^{j(j-1)/2}
=\prod_{i=0}^{k-1}(1-q^i).
$$

This is zero for $N\ne L$, since a nonzero finite-length quotient has nonzero $\pi$-torsion. For $N=L$ it is 1. Absolute convergence justifies regrouping, so $A(X)P(X)=I$ and $P(X)f=0$ forces $f=0$. On the constant function, the same subspace identity gives $P(X)1=\prod_{i=0}^{m-1}(1-q^i X)$. Its first positive zero is exactly $q^{-(m-1)}$. [Finite-field subspace identity](../src/Lib/General/Combinatorics.lean)
