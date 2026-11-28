# The exact primitive-root average in Selmer specialization

The compact proof specializes integral polynomials of unbounded degree at a common root of unity. The readable proof chooses an order first and averages over the primitive roots of that order. For $h\ge1$, its bound $h+1$ for one root's clipped valuation sum can be sharpened to the exact maximum $h+1-1/(\ell-1)$. This gives a direct check of the normalization $v(\ell)=1$ in the specialization step. [Compact specialization](https://github.com/leanprover-community/riemann-hypothesis/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/RootsOfUnityPoints.lean#L18-L29) · [Readable root-counting argument](../src/New/Congruences/Selmer/RootsOfUnity.lean)

Let $S_h$ be the primitive $\ell^h$-th roots and $u=1+\alpha$ a unit in the valuation ring of $\overline{\mathbb Q}_\ell$. Choose $\xi\in S_h$ maximizing $v(u-\xi)$, with $v(0)=\infty$. For any other $\zeta\in S_h$, the ultrametric inequality gives $v(\xi-\zeta)\ge\min(v(\xi-u),v(u-\zeta))=v(u-\zeta)$. Thus

$$
\sum_{\zeta\in S_h}\min\{v(\zeta-u),1\}
\le 1+\sum_{\zeta\ne\xi,\ \zeta\in S_h}v(\xi-\zeta)
=1+v(\Phi_{\ell^h}'(\xi)).
$$

Differentiate $(X^{\ell^{h-1}}-1)\Phi_{\ell^h}(X)=X^{\ell^h}-1$ at $\xi$. The denominator $\xi^{\ell^{h-1}}-1$ has valuation $1/(\ell-1)$ since $\xi^{\ell^{h-1}}$ has order $\ell$. The numerator $\ell^h\xi^{\ell^h-1}$ has valuation $h$. The bound is attained when $u=\xi$. The term at $\xi$ contributes 1, and every other distance has valuation $1/\varphi(\ell^j)\le1$ for the order $\ell^j$ of $\zeta/\xi$. The separate level $h=0$ consists only of 1 and has maximum 1.

For example, at $\ell=3$, $h=2$, take $u$ of order 9. Among the other five primitive ninth roots, two ratios have order 3 and three have order 9. The sum is $1+2/2+3/6=5/2$, attaining the formula.

To see how the estimate enters `exists_rootOfUnity_eval_le_gaussVal_add`, put $r_h=1/\varphi(\ell^h)$ and $C_h=h+1-1/(\ell-1)$. Let $R_h$ be the multiset of polynomial roots of valuation $r_h$. Sum the bound over $\alpha\in R_h$ with $u=1+\alpha$, then divide by $|S_h|=1/r_h$. Some primitive $\zeta$ has total clipped valuation at most $|R_h|r_h C_h$. If this is at most $\delta<1$, every term lies below the clipping threshold, so the same bound holds for the ordinary valuation sum.

The readable proof has $\sum_h |R_h|r_h\le B$ over its eligible levels $1\le h\le h_0$ with $r_h\le\rho$. It follows that $B<\delta\sum_h 1/C_h$ suffices to find the required level. The improved condition is uniform in the polynomial degree. The several-variable theorem iterates the one-variable choice, and its Selmer application also evaluates powers of the selected roots. [One-variable and several-variable statements](../src/New/Congruences/Selmer/RootsOfUnity.lean) · [Application to powers](../src/New/Congruences/Selmer/GeneralTheorem.lean)
