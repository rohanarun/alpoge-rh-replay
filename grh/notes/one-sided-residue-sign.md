# Why an upper bound excludes zeros

The sign in the one-sided criterion comes from two places. The smoothing kernel fixes the sign of the residue attached to an untwisted zero. The upper bound fixes the opposite sign for the residue of a positive measure's transform. The calculation below tracks both signs through the readable edition.

## The smoothing kernel

Write $Q$ for the modulus, $d$ for an odd prime coprime to $Q$, and $\chi_d(n)=(n/d)$ for the Legendre symbol. Put $\lambda(n)=\mathbf{1}_{n\equiv1\bmod Q}\Lambda(n)(1-\chi_d(n))$. Write $E_\psi$ for the entire function obtained from $L(s,\psi)$ by multiplying by $s-1$ when $\psi$ is principal. In the sum below, $\psi$ runs over the characters modulo $Q$. Define

$$
G(s)=\frac{1}{\varphi(Q)}
\left(\sum_\psi \left[\frac{E'_{\psi\chi_d}}{E_{\psi\chi_d}}(s)
-\frac{E'_\psi}{E_\psi}(s)\right]-1\right),
\qquad c=\Re G(1).
$$

The remainder is $R(y)=\sum_{n\le y}\lambda(n)(1/n-1/y)-\log(y)/\varphi(Q)-c$. For its transform $\Phi(s)=\int_0^\infty R(e^v)e^{(1-s)v}\,dv$, a single term of the sum supplies the kernel

$$
\int_{\log n}^\infty (n^{-1}-e^{-v})e^{(1-s)v}\,dv
=n^{-s}\left(\frac{1}{s-1}-\frac{1}{s}\right)
=\frac{n^{-s}}{s(s-1)}.
$$

Work first in $\Re s>2$, where Lean identifies the integral. Character orthogonality gives $\sum_n\lambda(n)n^{-s}=s/(\varphi(Q)(s-1))+G(s)$. Multiplying by the kernel factor produces $1/(\varphi(Q)(s-1)^2)$, exactly the transform of the logarithm subtracted in $R$. Hence

$$
\Phi(s)=\frac{G(s)/s-c}{s-1}.
$$

At $s=1$ the singularity is removable because $G$ is analytic there and $G(1)=c$. At $\rho\ne 0,1$ let $U(\rho)$ and $T_d(\rho)$ be the sums of the vanishing orders of $E_\psi$ and $E_{\psi\chi_d}$ respectively. The residue of $G$ is $(T_d-U)/\varphi(Q)$. Dividing by $\rho(\rho-1)$ gives

$$
r(\rho)=\operatorname{Res}_\rho\Phi
=\frac{U(\rho)-T_d(\rho)}{\varphi(Q)\rho(1-\rho)}.
$$

The corresponding declarations are **integral_primeRemainder** and **isPolar_primeRemainder**. [PrimeError.lean](../src/New/Reduction/Zeros/PrimeError.lean)

## Where the upper bound enters

Fix a candidate $\rho\ne1$ and choose $1/2<\beta<\Re\rho$. At the application to a character modulo $q$, take $Q=18480q$ and $d_0=Q/2-1$. The bound $R(y)\le(128\varphi(Q)+32)y^{\beta-1}$ holds eventually for each prime $d\equiv d_0\bmod Q$, using $\varepsilon=\beta-1/2$. The threshold may depend on $d$. From this class choose **one** $d$ for which every twisted $E_{\psi\chi_d}$ has no zero in $\Re s\ge\beta$, $|\Im s|\le|\Im\rho|$. This region contains both $\rho$ and every real $x>\beta$, so $T_d$ vanishes at all these points. [OneSidedBound.lean](../src/New/Reduction/OneSidedBound.lean) · [QuadraticTwist.lean](../src/Lib/Analytic/QuadraticTwist.lean)

For real $\beta<x<1$, $x(1-x)>0$ and $U(x)\ge0$, hence $r(x)\ge0$. At and to the right of $1$ the residue is zero. The upper bound allows a constant $K$ such that $K e^{\beta v}-e^vR(e^v)\ge0$ for all $v>0$. The Laplace transform of that density is $K/(s-\beta)-\Phi(s)$ far to the right. If its abscissa of convergence were $a>\beta$, Landau's theorem would force a singularity at $a$. Its only possible pole there is simple, with residue $-r(a)\le0$. A simple real pole of a nonnegative Laplace transform must have positive residue, as seen by approaching $a$ from the right. This rules out $a>\beta$. Thus $\Phi$ has zero residue at $\rho$. The displayed residue formula now gives $U(\rho)=0$, and each individual untwisted vanishing order is zero. [Landau.lean](../src/Lib/Analytic/Landau.lean) · [Criterion.lean](../src/New/Reduction/Zeros/Criterion.lean)

A sign check for the abstract lemma is to choose $1/2<\beta<a<1$ and take the test function $F(v)=-e^{(a-1)v}$. It obeys the upper bound $F(v)\le0$ and even decays. Its transform is $-1/(s-a)$ for $\Re s>a$. The pole survives precisely because the real residue is $-1$.
