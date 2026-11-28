# Interpolating the prime remainder in the reciprocal cutoff

An integer upper bound for `primeRemainder` transfers to all real cutoffs
with an explicit additive error. The argument uses the two adjacent integer
values and is independent of the sizes or signs of the arithmetic weights.
See [the definition of the remainder](../src/New/Reduction/Zeros/PrimeError.lean)
and [the integer-to-real step](../src/New/Reduction/OneSidedBound.lean).

Fix the prime $d$ and positive modulus $q$. Write $\phi=\varphi(q)$ and
$R(y)=\sum_{m\le y}\lambda(m)(1/m-1/y)-\log(y)/\phi-c_q$ for $y\ge1$.
Choose an integer $n\ge1$ and $n\le y\le n+1$. Put
$a=1/(n+1)$, $b=1/n$, $u=1/y$, and $\theta=(b-u)/(b-a)$.
Then $u=(1-\theta)b+\theta a$. There is an exact interpolation formula

$$
R(y)=(1-\theta)R(n)+\theta R(n+1)
 +\frac{\log u-(1-\theta)\log b-\theta\log a}{\phi}.
$$

Indeed, for the entire closed interval one can sum just over $m\le n$.
At $y=n+1$ the extra summand has factor $1/(n+1)-1/y=0$.
The resulting sum is affine in $u$, and the constant $c_q$ cancels.

The numerator in the last term is nonnegative by concavity of $\log$.
For its upper bound, $v\mapsto\log v+v^2/(2a^2)$ is convex on $[a,b]$.
Comparing this function with its endpoint chord gives

$$
0\le \log u-(1-\theta)\log b-\theta\log a
\le \frac{(b-u)(u-a)}{2a^2}
\le \frac{(b-a)^2}{8a^2}=\frac{1}{8n^2}.
$$

Suppose $R(m)\le C m^t$ for all sufficiently large integers $m$, with
$C\ge0$ and $-1\le t\le0$. The function $u\mapsto u^{-t}$ is concave,
so $(1-\theta)n^t+\theta(n+1)^t\le y^t$. Consequently, for all
sufficiently large real $y$,

$$
R(y)\le C y^t+\frac{1}{8\varphi(q)\lfloor y\rfloor^2}.
$$

Thus any coefficient $C+\eta$, $\eta>0$, works eventually at the same
exponent. In particular, taking $C=64\varphi(q_0)+3$ and
$t=-1/2+6\delta$ from `eventually_primeRemainder_natCast_le` gives this
alternative transfer directly from the integer estimate. For a prescribed
$\varepsilon>0$, choosing $0<\delta<\min(1/100,\varepsilon/6)$ gives
strict exponent slack, so $C$ itself works eventually at
$-1/2+\varepsilon$. The calculation concerns the interpolation step only.
