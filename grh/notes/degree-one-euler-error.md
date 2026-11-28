# The error from retaining only degree-one prime terms

In [the Euler-product module](../src/Lib/ClassField/HeckeL/EulerProduct.lean#L162),
a place $v$ above $p$ has norm $q_v=p^{f_v}$ and coefficient $|a_v|\le1$.
The proof of `hasPrimeDensity_of_tendsto` retains $a_vq_v^{-s}$ only when
$f_v=1$. What happens to the omitted part at $s=1$?

For $\Re s>1$ use the Euler logarithm given by the sum of its local power
series. The difference between that logarithm and the retained sum is

$$
H(s)=\sum_p\sum_{v\mid p}\ \sum_{\substack{m\ge1\\mf_v\ge2}}
     \frac{a_v^m}{m}\,p^{-mf_vs}.
$$

This choice of logarithm fixes the sign. The Lean proof defines its local
error $E(s,v)$ starting from $\log(1-a_vq_v^{-s})$, so its sum is $-H(s)$.
See [the assembly of the density estimate](../src/Lib/ClassField/HeckeL/EulerProduct.lean#L323).

### Convergence near one

For $\Re s\ge\sigma_0>1/2$, each local series is bounded in absolute value
by $p^{-2\sigma_0}/(1-2^{-\sigma_0})$. Indeed, its exponents $mf_v$ are
distinct integers at least two. At most $[K:\mathbf Q]$ places lie above
$p$, so the series converges locally uniformly and $H$ is holomorphic on
$\Re s>1/2$. In particular the omitted part has the definite limit $H(1)$.
The threshold is attained in the example $K=\mathbf Q$, $a_p=1$: as real
$s\downarrow1/2$, the positive square terms alone contribute
$\frac12\sum_p p^{-2s}\to\infty$.

This also identifies the limiting constant under the hypotheses of the
density lemma. If $(s-1)^\ell\,\mathrm{eulerProd}(a,s)\to c\ne0$ from the
right, the continuous Euler logarithm plus $\ell\log(s-1)$ tends to a
logarithm $C$ of $c$. To see this, take a local logarithm of the normalized
product near $c$. Its difference from the continuous logarithm belongs to
$2\pi i\mathbf Z$ and is constant on a short interval. Subtracting $H(s)$
now gives

$$
\lim_{s\downarrow1}\left(\sum_{f_v=1}a_v q_v^{-s}+\ell\log(s-1)\right)
= C-H(1).
$$

### Sharp local constant on the real interval used in Lean

For $s\ge1$, the local error times $p^2$ is bounded by one of two explicit
series. Both bounds are attained with $a_v=1$, $s=1$, and $p=2$.

| Residue degree | Majorant for the scaled error | Maximum |
| --- | --- | --- |
| $f_v=1$ | $\sum_{m\ge2}p^{2-m}/m$ | $4\log 2-2$ |
| $f_v\ge2$ | $\sum_{m\ge1}p^{2-2m}/m$ | $4\log(4/3)$ |

Every term in either majorant is nonincreasing in $p$. The first maximum
occurs for $v=(2)$ over $\mathbf Q$. The second occurs with $f_v=2$ over
$\mathbf Q(\sqrt{-3})$, since $X^2+X+1$ is irreducible modulo 2 in the
integral presentation $\mathbf Z[X]/(X^2+X+1)$ of its ring of integers.
Setting $a_v=1$ at that inert place and zero elsewhere also realizes the
global limit formula with $\ell=0$, $c=4/3$, and $C=H(1)=\log(4/3)$.
Thus $4\log(4/3)$ is the optimal constant valid for all places in the
module's local estimate $|E(s,v)|\le 2/p^2$. For $s>1$ the same value is
a supremum approached from the right.
