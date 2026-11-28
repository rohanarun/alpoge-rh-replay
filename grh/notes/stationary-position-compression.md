# A five-node stationary compression

How can a diagonal matrix with five negative eigenvalues compress to one with two positive eigenvalues? The stationary-position construction uses an indefinite Hermitian form. Its isometry intertwines the two matrices up to a nonzero term along an isotropic line. The following instance of the polynomial construction computes that term explicitly. [StationaryPosition.lean, **exists_intDiagonal_mul_positionIsometry**](../src/New/Appendix/DiscreteSeries/StationaryPosition.lean)

Take no common coordinates, $L=5$, $L'=2$, and $d=1$, so $L=L'+2d+1$. Choose decreasing nodes $\mu=(-2,-3,-4,-5,-6)$ and increasing nodes $\nu=(1,2)$. Set

$$
A=\operatorname{diag}(\mu),\quad J=\operatorname{diag}(1,-1,1,-1,1),\quad
J'=\operatorname{diag}(1,-1),\quad \Lambda=\operatorname{diag}(1,2).
$$

Write $p(t)=\prod_i(t-\mu_i)$ and $q(t)=(t-1)(t-2)$. The vector $[F]$ of a polynomial has entry $F(\mu_i)/\sqrt{|p'(\mu_i)q(\mu_i)|}$ at $i$. In particular $A[F]=[tF]$. To check all pairings with rational arithmetic, take $e(F)=(F(\mu_i))_i$ before scaling the rows. Then $[F]^*J[G]=e(F)^*He(G)$, where

$$
H=\operatorname{diag}(1/288,-1/120,1/120,-1/252,1/1344).
$$

The signs come from $J$ and the denominators are the values $|p'(\mu_i)q(\mu_i)|$. The two flag vectors are $v_1=[q]$ and $v_2=[tq]$. For the two isometry columns the unscaled polynomials are $q/(t-1)=t-2$ and $q/(t-2)=t-1$. Putting these four raw evaluation columns in a matrix $E$ gives the exact check

$$
E=\big(e(q),e(tq),e(t-2),e(t-1)\big),\qquad
E^*HE=\operatorname{diag}(0,1,1/2520,-1/6720).
$$

Thus $v_1$ is a nonzero isotropic vector, $Av_1=v_2$, and both flag columns are orthogonal to both isometry columns. The flag columns are independent since the nodes are distinct and $q(\mu_i)\ne0$. The scales from the proof are $\sqrt{|p(\nu_j)/q'(\nu_j)|}$, which give the isometry

$$
I=\big(\sqrt{2520}\,[t-2],\ \sqrt{6720}\,[t-1]\big),\qquad I^*JI=J'.
$$

In each column the identity $(t-\nu_j)\,q(t)/(t-\nu_j)=q(t)$ now gives

$$
AI-I\Lambda=v_1\begin{pmatrix}\sqrt{2520}&\sqrt{6720}\end{pmatrix}.
$$

Taking the form adjoint $I^\dagger=J'I^*J$ kills the right-hand side because $I^*Jv_1=0$. Consequently $I^\dagger A I=\Lambda$. The residual has rank one in the direction $v_1$, orthogonal to the nondegenerate image of $I$. This example checks the signed Gram and compression identities used to construct a stationary position. [Positions.lean, **formAdjoint**](../src/New/Appendix/DiscreteSeries/Positions.lean) · [StationaryPosition.lean, **IsPosition.formAdjoint_mul_mul_eq**](../src/New/Appendix/DiscreteSeries/StationaryPosition.lean)
