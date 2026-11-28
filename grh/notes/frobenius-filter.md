# What attachment determines at Frobenius elements

A trivial rank-one representation can satisfy `GaloisRep.Attached` for a system of polynomials that differs from its characteristic polynomial at **every prime**, with a coefficient error of 2-adic norm 1 at infinitely many primes. The example below tests the attachment predicate itself. The extra hypotheses about eigenforms and sphericity enter separately in `SphericalCompat`. [Definitions of attachment and spherical compatibility](../src/Lib/GaloisRep/Main/AttachedRepresentations.lean)

## An infinite set of exceptional primes

Work over $\mathbb Q$ and write $G$ for its absolute Galois group. For $n\ge0$ let $p_n$ be the least prime divisor of $2^{2^n}+1$ and put $S=\{p_n:n\ge0\}$. The order of 2 modulo $p_n$ is exactly $2^{n+1}$, since $2^{2^n}\equiv-1\pmod {p_n}$. This makes the $p_n$ distinct and gives $p_n\equiv1\pmod{2^{n+1}}$.

The condition $p\notin S$ holds along `mostFrobenii`. To see the quantifiers, take any nonempty open $V\subset G$. The 2-adic cyclotomic character $\chi_2:G\to\mathbb Z_2^\times$ is an open surjection. Its image of $V$ is open and therefore contains a residue class $a\bmod 2^k$ with $a\not\equiv1\pmod{2^k}$. Intersecting $V$ with the inverse image of this class gives a nonempty open $O$. At any odd $p$, every geometric Frobenius above $p$ has image $p^{-1}$ under $\chi_2$. For $n+1\ge k$, the image at $p_n$ is thus 1 modulo $2^k$ and cannot occur in $O$. Discarding the finitely many smaller indices verifies the filter condition on $O$. [Definition of the filter](../src/Lib/GaloisRep/Main/Defs.lean) · [Cyclotomic Frobenius convention in Lean](../src/Lib/ClassField/Places/DecompositionCyclotomic.lean) · [Milne, *Algebraic Number Theory*, Example 8.18](https://www.jmilne.org/math/CourseNotes/ANTc.pdf)

## A polynomial system with no exact matches

Take $\ell=2$, $j=\mathrm{id}_G$ and $\rho(g)=1$ in rank one. Set $P_p(X)=X-(1+e_p)$, where $e_p=1$ for $p\in S$ and $e_p=2^p$ otherwise. The characteristic polynomial is $X-1$, so its difference from $P_p$ is the nonzero constant $e_p$ at every prime. Any choice of the field isomorphism $\iota_2$ fixes these rational coefficients.

For each $\eta>0$, the coefficient error on $p\notin S$ has norm $2^{-p}\le\eta$ outside finitely many small primes. Intersect this cofinite condition with the filter condition just proved. This establishes `eventually_norm_coeff_le` for all coefficients at once. The representation is continuous, its trace pairing on scalar matrices is nondegenerate, and $j$ is open. These are all four fields of `Attached`. At the fixed tolerance $\eta=1/2$, the coefficient bound still fails at every $p_n$.

For each $g\in G$, `Attached.tendsto_charpoly_coeff` takes the limit along the *same* filter refined by neighborhoods of $g$. In this example the constant coefficient tends to $-1$ and the trace is 1. In general, Chebotarev makes the refined filter nontrivial at every $g$. Two representations attached to the same system therefore obtain the same coefficient limits over a common Galois element, which is the uniqueness step in `Attached.trace_eq`. [Coefficient limits and trace equality](../src/Lib/GaloisRep/Main/AttachedRepresentations.lean)
