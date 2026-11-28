# Reading the reduced one-curve exponent from its base-$p$ digits

The [one-curve exponent theorem](../src/New/Derivatives/FormalGroup/Exponent.lean#L708)
writes the Taylor series of a scaled theta function as $W\exp(c_\varpi\Xi)$.
Here is a coefficient test for the particular $\Xi$ constructed in the proof.
All equalities of coefficients below are in $\mathcal O_{\mathbf C_p}/(\pi_p)$.
The prime $d$ is $7\bmod 8$ and the prime $p$ is nonsplit, so $p$ is odd.

### Inert primes

Write $\lambda$ for the image of the unit in the
[inert-prime lemma](../src/New/Derivatives/FormalGroup/Exponent.lean#L630).
The reduced parameter is $Y=\sum_{k\ge0} z^{p^{2k}}$. Frobenius sends the
even positions to odd ones, giving

$$
\Xi=\lambda\,Y^p Y
=\lambda\sum_{u\ {\rm even},\ v\ {\rm odd}} z^{p^u+p^v}.
$$

The coefficient at $N$ is $\lambda$ exactly when the base-$p$ expansion of
$N$ has two digits equal to one, one in an even position and one in an odd
position, and all other digits zero. Position zero is the units place.
Every other coefficient vanishes. There is a unique summand at each
eligible degree. In the theorem's indexing, $j=\min(u,v)$ and $e=|u-v|$,
so $N=p^j(1+p^e)$ and $e$ is odd. In particular the number of nonzero
coefficients in $0\le N<p^L$ is
$\lceil L/2\rceil\lfloor L/2\rfloor=\lfloor L^2/4\rfloor$.

### The ramified prime

For $p=d$, the [ramified-prime lemma](../src/New/Derivatives/FormalGroup/Exponent.lean#L669)
gives $\Xi=\lambda(Y^2-z^2/2)$ with $Y=\sum_{k\ge0}z^{p^k}$.
Distinct positions give two ordered summands in the square. A repeated
position gives just one, with no carry since $p$ is odd.

| Base-$p$ shape of $N$ | Coefficient |
| --- | --- |
| $N=2$ | $\lambda/2$ |
| A single digit two in a positive position | $\lambda$ |
| Two digits one in distinct positions | $2\lambda$ |
| Any other shape | $0$ |

There are $L+\binom L2=L(L+1)/2$ eligible degrees below $p^L$.
Since two is invertible, all those degrees occur if the reduced $\lambda$
is nonzero. If it vanishes, the reduced exponent is zero. The unit
conclusion in the combined theorem applies to the inert case.

### Two finite checks

Take $d=7$. At the inert prime $p=3$, truncating at $3^6$ gives exactly
the nine degrees $4,12,28,36,84,108,244,252,324$, each with coefficient
$\lambda$. At $p=7$, the coefficient multipliers below $7^3$ are
$(2,4),(8,2),(14,1),(50,2),(56,2),(98,1)$, written as (degree,
multiplier modulo seven). In particular the correction at degree two
leaves the repeated-position coefficients at degrees 14 and 98 intact.
