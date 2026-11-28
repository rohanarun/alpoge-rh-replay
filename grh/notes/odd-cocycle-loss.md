# How one integer bounds the odd-cocycle loss at every prime

The congruence argument needs a bound on the denominators of projections to spaces of lifts. Part of the denominator at a prime $\ell$ comes from lengths of modules of odd cocycles. These modules vary with the prime, the coefficient ring, the Tate twist and the precision. The cyclotomic estimate gives one positive integer $X$ for all of them. This makes it possible to add the local losses over primes. [Local denominator estimate](../src/New/Congruences/FirstOrder/RibetElement.lean#L110-L136) · [Global denominator estimate](../src/New/Congruences/FitTwistsExist.lean#L192-L213)

## What is being bounded?

Fix a CM field $E\subseteq\mathbb Q(\mu_N)$ with $N>0$, and a nonnegative integer $t$. Write $h_E$ for the class number of $E$. The statement of `New.exists_length_shaOdd_le` gives an $X$ satisfying

$$
1\le X\le 2^{4(N+t+3)^{27}}h_E.
$$

**Once $X$ is chosen**, for every prime $\ell$, every allowed coefficient ring $\mathcal O$, every $0\le e<t$, and every precision $\nu\ge 0$,

$$
\operatorname{length}_{\mathcal O}
  \bigl(\texttt{shaOdd}(\ell,E,\mathcal O,e,\nu)\bigr)
\le v_{\mathcal O}(X).
$$

Here $\mathcal O$ is the ring of integers in a finite extension of $\mathbb Q_\ell$ with enough roots of unity for the characters modulo $N$. `oddClassBound D` chooses this $X$ for the field, conductor and $t$ of the proof data $D$. For each $\ell$, sufficiently large coefficient rings in the directed family used by the proof satisfy the roots-of-unity condition. [Uniform bound and quantifiers](../src/Lib/Cyclotomic/OddSha.lean#L610-L627) · [Choice of the integer and coefficient rings](../src/New/Congruences/FirstOrder/TraceRelations.lean#L73-L98)

For $e>0$, an element of `shaOdd` is a continuous cocycle on the absolute Galois group of $E$ with coefficients in $(\mathcal O/\ell^\nu)(-e)$. It is unramified away from $\ell$, vanishes on the kernel of the cyclotomic character in each decomposition group above $\ell$, and satisfies $z(cgc^{-1})=-z(g)$ for complex conjugation $c$. For $e=0$, the action is trivial, the local condition above $\ell$ uses inertia, and the objects are everywhere-unramified continuous homomorphisms. The word “classes” in the denominator estimate refers here to this concrete module of maps. Forming $H^1$ would identify cocycles differing by a coboundary. The bound used here is already a bound on the cocycles themselves. [Definition and local conditions](../src/Lib/GaloisRep/Main/SelmerModules.lean#L165-L185) · [Scope of the comparison with Ш¹](../src/Lib/Cyclotomic/OddSha.lean#L14-L26)

## Why one integer suffices

For $e=0$ the class number supplies the bound. For each $0<e<t$ the proof takes a bounded Stickelberger integer, constructs an annihilator from it and bounds the number of Galois elements needed to detect a cocycle. Over a discrete valuation ring, a nonzero annihilator bounds the length of a cyclic module. Taking a direct sum of copies can multiply the length while preserving the annihilator. A cocycle here is determined by its values at the detecting elements, so their number also bounds how many coordinates contribute to the length. It then multiplies the resulting factors for all $0<e<t$ and includes $h_E$. This product is fixed before the proof splits into small and large $\ell$. [Annihilation and detection](../src/Lib/Cyclotomic/OddSha.lean#L42-L58) · [Product construction](../src/Lib/Cyclotomic/OddSha.lean#L628-L655)

The distinction between $v_{\mathcal O}$ and $v_\ell$ matters in a ramified coefficient ring. With the normalization giving $\mathcal O/\ell\mathcal O$ length one, $v_{\mathcal O}(X)$ becomes the ordinary integer valuation $v_\ell(X)$. In the local argument there are $t'\le t$ characters. The odd-cocycle contribution from each is at most $v_\ell(X)$ after normalization, so this part of their combined cost is at most $t'v_\ell(X)$. [Normalized lengths in the local bound](../src/New/Congruences/FirstOrder/RibetElement.lean#L121-L140)

For any finite set $S$ of primes, integer factorization gives

$$
\sum_{\ell\in S}v_\ell(X)\log\ell
=\log\!\left(\prod_{\ell\in S}\ell^{v_\ell(X)}\right)
\le \log X.
$$

Primes dividing $X$ may therefore contribute positive lengths. At primes outside its support the length bound is zero. A separate size bound for each prime would give a different estimate. For example, take $S=\{2,3,5\}$ and choose $X_\ell=\ell$ for each of those primes. Every chosen integer is at most $5$, yet the weighted sum is $\log 30>\log 5$. A common $X$ makes the product in the display a divisor of $X$.

For the proof data $D$, the explicit bound on $X$ gives $\log X\le 4(N+t+3)^{27}\log 2+\log h_E\le D.x^{2000}$. This is the sense in which the odd-cocycle term is “negligible.” Its contribution to the global denominator sum is bounded by $D.t\cdot D.x^{2000}$. A second term comes from the chosen finite group order. Their combined bound feeds the estimate for clearing denominators, which is used to assemble a regular family of twists. [Weighted bound](../src/New/Congruences/FitTwistsExist.lean#L157-L176) · [Two denominator terms](../src/New/Congruences/FitTwistsExist.lean#L192-L213) · [Clearing denominators](../src/New/Congruences/FitTwistsExist.lean#L237-L258) · [Application to the family](../src/New/Congruences/FitTwistsExist.lean#L520-L543)
