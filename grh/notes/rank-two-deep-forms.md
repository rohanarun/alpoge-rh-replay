# An exact dimension for rank-two forms of depth one

Consider a [Frobenius cycle](../src/New/UpperBound/ElementaryDivisors/TwistingData.lean)
with $P=p^f\ge5$, $W=K=\mathbf F_{P^2}$, $N=k=2$ and $r=1$.
Take the even embedding to be the identity, the odd embedding to be the
$P$-power map, and `sqrtPrime` to be zero. The identity $x^{P^2}=x$
closes the cycle. For degree $n$ in each letter, the dimension over $K$ is

$$
\dim \mathrm{deepForms}(2,n,1,1)=
\begin{cases}
0 & n<P,\\
(n+1)^2-(P^2+1) & n\ge P.
\end{cases}
$$

This computes one layer of the filtration bounded in
[`sum_finrank_deepForms_le`](../src/New/UpperBound/ElementaryDivisors/Depth.lean).

### The condition on the projective line

Write $x_0,x_1$ for the even variables and $y_0,y_1$ for the odd ones.
The deep variables are $x_1$ and $y_0$. Thus the only forbidden coefficient
at depth one is that of $x_0^n y_1^n$, in every translate of the form $F$.
If the first row of $g$ is $(a,b)$, the second row of its inverse transpose
is $(-b,a)/\det g$. The odd action applies the $P$-power embedding to that
row. Up to the nonzero scalar $(\det g)^{-Pn}$, the forbidden coefficient is

$$
F(a,b;-b^P,a^P).
$$

Every nonzero first row occurs. Scaling the row by $c$ scales the displayed
value by $c^{(P+1)n}$. Therefore it suffices to evaluate at the $P^2+1$
projective rows $(1,t)$ and $(0,1)$. The kernel of this evaluation matrix
is precisely the depth-one space.

### Computing the rank

Use the monomials $x_0^{n-i}x_1^i y_0^j y_1^{n-j}$ for $0\le i,j\le n$.
On $(1,t)$ their values are $(-1)^j t^{i+Pj}$, and at infinity only
$i=j=n$ has nonzero value. The signs can be removed by rescaling columns.

* For $n<P$, the exponents $i+Pj$ are distinct and at most $P^2-1$.
  A polynomial of degree less than $P^2$ vanishing on $K$ is zero. The
  affine rows already give full column rank $(n+1)^2$.
* For $n\ge P$, the integer intervals $[Pj,Pj+n]$, $0\le j\le n$,
  cover every exponent from zero through $(P+1)n$. In particular there
  are columns for degrees $0,\ldots,P^2-1$, all strictly below the top
  degree. They give a basis of functions on the affine line and vanish
  at infinity. The top column has nonzero value at infinity and raises
  the rank to $P^2+1$.

For example, at $P=5$ the dimension jumps from zero at $n=4$ (25
coefficients) to ten at $n=5$ (36 coefficients and 26 independent
conditions). At $n=5$, the monomial-weight argument in
`exists_le_weight_of_mem_deepForms` requires $(i+j)/5\ge1$ for a
witness. There are 21 eligible columns. The projective-line calculation
explains how the actual dimension can be smaller than this layer bound.
