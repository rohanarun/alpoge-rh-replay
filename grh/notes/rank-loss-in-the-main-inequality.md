# Where the rank enters the main inequality

Theorem B gives $n$ independent forms in a target of dimension $d>0$. Write $\theta=n/d$. The proof uses $\theta\ge 1-4/b^2$ twice. The two uses have different sensitivity to rank loss.

### Completing the lattice

In `integral_forms_long_with_completion_cost`, each of the $d-n$ missing directions costs at most $2x_1^2 b^2+b$. Thus the **per-dimension** completion cost is at most

$$
(1-\theta)(2x_1^2 b^2+b)
\le 4(2x_1^2+1/b)\le b.
$$

The first inequality uses the full codimension estimate; the second is a scale inequality of the admissible data. Replacing the first estimate by $\theta\ge 1/2$ at this point would leave a term of order $x_1^2 b^2$ per dimension. It is only after this cost has been absorbed into Theorem C that half rank suffices. [Completion estimate](../src/New/Determinant/Twist/LongForms.lean#L126-L139) · [Application to Theorem C](../src/New/Determinant/Twist/LongForms.lean#L270-L282)

### Comparing the upper and lower bounds

Set $M=\mathtt{mainAmount}$, $R=m\,\mathtt{totalRemainder}$, $S=fa\log^4 b$, and $I=10\log(1+2b^2)\,\mathtt{errorUnit}$. Here $M,S,I\ge0$; the remainder $R$ can have either sign. Hadamard's inequality contributes $n(M-R+S)$, and twice the index bound contributes $2dI$. Dividing the comparison in `star_inequality` by $d$ gives

$$
M-3S\le\theta(M-R+S)+2I.
$$

Keeping $\theta$ until the end exhibits the full-rank contribution and the correction:

$$
R\le 4S+2I+(\theta^{-1}-1)(3S+2I-M).
$$

In particular, once $M\ge 3S+2I$, a deficient rank does not enlarge this upper bound. If only a lower bound $0<\theta_0\le\theta\le1$ is known, the exact upper envelope of the scalar comparison is $4S+2I+(\theta_0^{-1}-1)\max(3S+2I-M,0)$. The maximum is at $\theta_0$ when the correction is positive and at $1$ otherwise. [Definitions and comparison in Lean](../src/New/Reduction/MainInequality.lean#L95-L103) · [Covolume, index and rank bounds](../src/New/Reduction/MainInequality.lean#L116-L163)

For $\theta_0=1/2$, dropping $M$ gives $R\le7S+4I$. Equality is possible in this scalar relaxation: set $M=0$, $\theta=1/2$ and $R=7S+4I$. Lean takes the coarser route $\theta R\le4S+2I$, then $R\le8S+4I$; both suffice for its $fa\log^5 b$ budget. The equality example tests the constants after Theorem C has been supplied. It makes no assertion that actual admissible data attain half rank.
