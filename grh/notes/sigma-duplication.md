# Sigma duplication in the half-period coordinate

[DLMF 23.10.10](https://dlmf.nist.gov/23.10.E10) gives
$\sigma_{\rm W}(2w)=-\wp'(w)\sigma_{\rm W}(w)^4$.
In [`CMLattice.sigma_two_mul_eq`](../src/Lib/CM/Integrality/Doubling.lean),
the sign is positive and the fourth power is a theta section. Two changes of
normalization account for this.

1. [`PeriodPair.σ`](../src/Lib/CM/Sigma/Basic.lean) is an odd theta section
   with derivative one at zero. Changing Weierstrass sigma by a factor
   $e^{bw^2}$ preserves the duplication identity since both sides acquire
   $e^{4bw^2}$. This explains why the same DLMF identity holds for the section
   used in `New.sigma_two_mul`.
2. Put $w=z+t$, where $t$ has order two modulo the lattice $\Lambda$, and set
   $x(z)=\wp(z+t)-\wp(t)$. Write $E=\exp(H(t,z)+H(t,t)/2)$ and
   $c_0=(T_t\sigma)(0)$. In the Lean normalization,
   $\sigma(w)=E c_0\theta(z)$, $c_0^4=1$, and
   $\sigma(2w)=-E^4\sigma(2z)$. The last sign is the multiplier for the
   period $2t$: its half $t$ lies outside $\Lambda$. Substitution gives
   $\sigma(2z)=x'(z)\theta(z)^4$ for $w\notin\Lambda$.
   A local check fixes the sign before squaring: $\wp'(t)=0$ and
   $\wp''(t)=2$ give $x'(z)=2z+O(z^2)$, while $\theta(0)=1$ and
   $\sigma'(0)=1$.

## An independent check on the quartics

[DLMF 23.10.7](https://dlmf.nist.gov/23.10.E7) gives a second route to the
ratio of the two polynomials in [`New.doublingForms`](../src/Lib/CM/Integrality/Doubling.lean).
Write $e=\wp(t)$, $c=a_1$, so $c^2=12e$, and let
$F(X)=4X^3+c^2X^2+4X$. At $X=x(z)$, the translated curve has
$\wp'(w)^2=F(X)$ and $\wp''(w)=F'(X)/2$. Substitution in the DLMF formula gives

$$
\wp(2w)-e=-2X-3e+\frac{F'(X)^2}{16F(X)}
          =\frac{(1-X^2)^2}{F(X)}.
$$

The last equality follows by expanding $F'(X)^2-16(2X+3e)F(X)$.
Now $2w=2z+2t$ and $2t\in\Lambda$, so $\wp(2w)-e=x(2z+t)$.
The half-period relation
[`translatedX_mul_translatedX_add_t`](../src/Lib/CM/Sigma/ThetaSections.lean)
then gives $x(2z)=F(X)/(1-X^2)^2$ wherever the quotients are defined.
Thus in the project's coordinates $(u,v)=(\theta(z)^2,\sigma(z)^2)$,
with $X=v/u$, the **second coordinate divided by the first** is

$$
\frac{uv(4u^2+c^2uv+4v^2)}{(u^2-v^2)^2}.
$$

This calculation compares rational functions away from their poles. Lean's
`theta_two_mul` and `sigma_two_mul_sq` separately prove identities of entire
sections, including at zeros of the denominator. The factor $c^4-64$ in
`norm_doublingForms_eq_one` can also be read off the pair: at the two
candidate common projective zeros $(1,1)$ and $(1,-1)$ of its first
coordinate, the second takes the values $8+c^2$ and $c^2-8$. Their product
is $c^4-64$.
