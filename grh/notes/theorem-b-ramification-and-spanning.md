# Theorem B with ramification before the choice of translates

Both editions of `Data.enough_forms` produce translates spanning at least $(1-4/b^2)d$ dimensions of the target. Their counts use different source dimensions. The compact statement bounds $|t|n$ by $5d\log(1+b^2)$, where $n$ is the dimension of the **full** source. The readable statement bounds $|t|\dim U$ by $5d\log(1+2b^2)$, where $U$ is the ramified source. The compact count also follows from the readable edition's estimates, by imposing ramification before choosing the translates. [Compact statement](https://github.com/leanprover-community/riemann-hypothesis/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Endgame/ShortAndEnough.lean#L170-L178) · [Readable statement and proof](../src/New/Reduction/ShortAndEnough.lean)

## The cost of imposing ramification

Write $V$ for the full source of dimension $n>0$, $W$ for the target of dimension $d>0$, $B_s$ for `goodPoincare s`, and $E$ for `ramifyingOp univ`. In the readable edition $U=E(V)$ and $\dim\ker E/n\le f/(N-1)\le b^{-8}$. For every $F\subseteq W$ of codimension $ud$, `isSpread_goodPoincare` supplies an $s$ with $\dim B_s^{-1}F/n\le 1-u/2+3/(16b^2)$. [Ramifying operator and rank bounds](../src/New/UpperBound/Size/ShortColumns.lean) · [Bound for one translate](../src/New/Spanning/SecondMoment/SpanningTheorem.lean)

Set $H=B_s^{-1}F$. The restriction of $E$ to $E^{-1}H$ surjects onto $U\cap H$ with kernel $\ker E$. Consequently

$$
\frac{\dim (B_sE)^{-1}F}{n}
=\frac{\dim\ker E+\dim(U\cap H)}{n}
\le 1-\frac u2+\frac{3}{16b^2}+b^{-8}
\le 1-\frac u2+b^{-2}.
$$

Here $b\ge2$ suffices for the last inequality. The same $s$ works for this $F$, and $B_sE$ has image $B_s(U)$, exactly the range of the readable normalized map. The compact proof includes this preimage cost in `ramifiedColumns_fill_rows`. The readable proof first covers the target with images of $V$, then bounds the loss on restricting to $U$ by $|t|\operatorname{codim} U$. [Compact preimage bound](https://github.com/leanprover-community/riemann-hypothesis/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Columns/ChainValuation.lean#L236-L241) · [Compact filling theorem](https://github.com/leanprover-community/riemann-hypothesis/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Filling/FillingTheorem.lean#L22-L39) · [Readable range identity and restriction step](../src/New/Reduction/ShortAndEnough.lean)

## Why the constants are 4 and 5

Put $\eta=b^{-2}$. While the missing share $u$ exceeds $4\eta$, adding the image of the chosen $B_sE$ increases the span by $g=n-\dim(B_sE)^{-1}F\ge n(u/2-\eta)>0$. The new missing share is $u-g/d$. The compact lemma `exists_few_translates` uses the potential $\Psi(u)=5d\log(1+u/\eta)$. The inequality $-\log(1-z)\ge z$ for $0\le z<1$ gives

$$
\Psi(u)-\Psi(u-g/d)\ge\frac{5g}{u+\eta}
\ge n\frac{5(u/2-\eta)}{u+\eta}\ge n.
$$

The last inequality is precisely $u\ge4\eta$. Each new translate therefore consumes at least $n$ of the initial potential $\Psi(1)$, and every step strictly increases the integer dimension of the span. At termination its dimension is at least $(1-4/b^2)d$, while $|t|n\le\Psi(1)=5d\log(1+b^2)$. This derives the compact count for the readable maps using their full source dimension. [Compact potential argument](https://github.com/leanprover-community/riemann-hypothesis/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Heights/OneDeterminant.lean#L88-L111)
