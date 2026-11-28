# How Theorem A turns a local gain into a short form

Theorem A uses one positive rational multiplier for all translates of the Poincaré map. At each prime its denominator removes a proved power of that prime from a theta lift. At infinity the same denominator reduces the squared norm. The compact and readable editions choose the exponent differently. The distinction matters when the gain is fractional. [Compact `Data.short_forms`](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Endgame/ShortAndEnough.lean#L134-L168) · [Readable `span_short_integralRamified_eq_top` and `indexLe_normalizedPoincare`](../src/New/Reduction/ShortAndEnough.lean)

## Where the local gain holds

Fix an exceptional non-split prime $p<x_1$ and a $p$-adic place. Write $G$ for the requested gain and $L$ for the local loss unit in the edition under consideration. Here $p$ is inert and can pair two of the distinguished places, causing a loss in successive lifts. One chooses a full mark (one prime from each relevant conjugate pair) and lets $Y$ be the ordered product of its scaled Hecke operators. If $M$ is the integral source module, the proof works on

$$
S=Y^mM+p^{j_p}M,
$$

where $m$ is the number of lifts and $j_p$ is the collision exponent. Transferring a copy of $Y$ through each lift yields a valuation bound $G-2L$ on the first summand. On the second, the scalar $p^{j_p}$ pays for all collisions and gives $G-L$. The ultrametric inequality gives $G-2L$ on $S$. The elementary-divisor estimate bounds the colength exponent of $S$ in $M$ by $3L$ per source dimension in the compact edition and by $L$ in the readable edition. Both bounds are needed since a large valuation on a very small submodule alone would say little about the index of a family of forms. [Compact transfer and its iteration](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Columns/LocalStatement.lean#L145-L194) · [Compact colength and valuation bounds](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Columns/LocalStatement.lean#L230-L307) · [Readable local divisibility](../src/New/UpperBound/Divisibility/LocalDivisibility.lean)

## Why the rounding changes

Use $v_p(p)=1$. For a denominator factor $p^{-\beta}$, the normalized lift has valuation at least $G-2L-\beta$. The two proofs get a nonnegative value as follows.

| At a small non-split prime | Compact edition | Readable edition |
| --- | --- | --- |
| Allowed loss $E$ | $3L$ | $2L$ |
| Exponent $\beta$ removed | $\lceil G-3L\rceil$ | $\lfloor G-2L\rfloor$ |
| Lower bound after normalization | $G-2L-\lceil G-3L\rceil>L-1\ge0$ | $G-2L-\lfloor G-2L\rfloor\ge0$ |

The compact local lemma takes any integer $\beta<G-E+1$. Its proof uses $L\ge1$ at these primes, so its choice $\beta=\lceil G-E\rceil$ satisfies the stronger valuation bound on $S$. The rational multiplier has exponent $-\beta=\lfloor E-G\rfloor$. Hence its contribution to the log squared norm is at most $2(E-G)\log p$. [Compact allowed loss](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Columns/SizeEstimates.lean#L81-L88) · [Compact `exists_indexDvd_Bmu_divisible`](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Columns/LocalStatement.lean#L280-L305)

The readable local lemma supplies the real bound $G-E$. Write $\delta_p=G-E-\lfloor G-E\rfloor$. Its rational multiplier has exponent $E-G+\delta_p$. The archimedean excess over $2(E-G)\log p$ is exactly $2\delta_p\log p$. Over the primes in the multiplier (the small non-split primes and $N$), this excess is at most $2\sum_p\log p\le 2b$. This is the $2b$ in the error budget of Theorem A(a). The factor of two comes from the squared norm. Theorem A(b) then carries the local colength bound through each translate to bound the index of a finite family. [Readable allowed loss](../src/New/UpperBound/Size/Estimates.lean) · [Readable normalization, squared norm and index](../src/New/Reduction/ShortAndEnough.lean)

For a scalar check, take $G=37/4$ and $L=7/3$. The available valuation is $55/12$, the compact exponent is $3$ and the readable exponent is $4$. These leave $19/12$ and $7/12$ respectively. Applying a ceiling directly to the readable bound would remove $5$ and leave $-5/12$. The endpoint valuation occurs in $\overline{\mathbb Q}_p$: any root of $X^{12}-p^{55}$ has valuation $55/12$. This example checks the rounding argument independently of the global construction of the source forms.
