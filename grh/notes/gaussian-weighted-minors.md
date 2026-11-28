# The factor of one half in the Gaussian bound for weighted minors

For an integer weight $w=(w_i)$ and $k$ in the maximal compact group, the readable proof uses

$$
|\mathrm{weightMinors}(w,k)|^2 \leq e^{-Q_w(k)/2},
\qquad Q_w(k)=\sum_{i,j}|w_i-w_j|\,|k_{ij}|^2 .
$$

The coefficient $1/2$ counts the two off-diagonal blocks of a unitary matrix. A two-dimensional rotation shows that this coefficient is optimal even arbitrarily close to the identity. [GaussianShape.lean, **norm_weightMinors_sq_le_exp**](../src/New/Appendix/DiscreteSeries/GaussianShape.lean)

## One threshold

Let $P$ project onto the coordinates in a set $S$. With those coordinates first, write the unitary matrix in blocks as

$$
k=\begin{pmatrix}A&B\\ C&D\end{pmatrix}.
$$

The principal minor on $S$ is $\det A$. Unitarity gives $A^*A+C^*C=I$ and $AA^*+BB^*=I$. Taking traces yields $\|B\|_F^2=\|C\|_F^2$. Since $[P,k]$ has off-diagonal blocks $B$ and $-C$, its squared Frobenius norm is $2\|C\|_F^2$. The eigenvalues $\lambda_j$ of $C^*C$ lie in $[0,1]$, so

$$
|\det A|^2=\prod_j(1-\lambda_j)
\leq \exp\!\left(-\sum_j\lambda_j\right)
=\exp\!\left(-\tfrac12\|[P,k]\|_F^2\right).
$$

Equality holds precisely when $C=0$, equivalently when $k$ commutes with $P$. This argument includes singular $A$ because the product can be zero. [MinorExpansion.lean, **norm_principalMinor_sq_le_exp**](../src/New/Appendix/DiscreteSeries/MinorExpansion.lean)

## All thresholds

Choose integers $a\le w_i\le b$. The finite product for $\mathrm{weightMinors}$ consists of $\det(k)^a$ and the principal minors for $P_t$ projecting onto $\{i:w_i\ge t\}$, with $a<t\le b$. The determinant factor has modulus one, including for negative $a$. The $(i,j)$ entry contributes $|k_{ij}|^2$ to $\|[P_t,k]\|_F^2$ precisely when the threshold separates $w_i$ and $w_j$. There are $|w_i-w_j|$ such integers. Multiplication of the single-minor bounds gives the displayed bound, with equality precisely when $k_{ij}=0$ for all unequal weights. Coordinates of equal weight can mix freely within the group. [MinorProducts.lean, **weightMinors_eq_det_zpow_mul_prod**](../src/Lib/General/LinearAlgebra/MinorProducts.lean) · [GaussianShape.lean, **sum_norm_lie_coordProj_sq**](../src/New/Appendix/DiscreteSeries/GaussianShape.lean)

For a finite check take the positive signature, $w=(-1,1,4)$, and $k=R_{12}R_{23}$, where the two coordinate rotations have $(\cos,\sin)=(3/5,4/5)$ and $(5/13,12/13)$ respectively. The two thresholds $0,1$ select coordinates $\{2,3\}$, whose minor is $3/5$. The three thresholds $2,3,4$ select $\{3\}$, whose minor is $5/13$. Thus the squared product is $(3/5)^4(5/13)^6$. Summing the nine entries of $Q_w(k)$ gives $Q_w(k)/2=2(16/25)+3(144/169)$.

Finally take $w=(0,1)$ and a single plane rotation of angle $\theta$ in the same signature. Its squared weighted minor is $\cos^2\theta$ and $Q_w(k)=2\sin^2\theta$. As $\theta\to0$ through nonzero angles, $-\log(\cos^2\theta)/(2\sin^2\theta)\to1/2$. Any larger coefficient in the exponent fails for sufficiently small rotations.
