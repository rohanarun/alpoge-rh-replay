# From the Chowla–Selberg gamma product to the CM lattice area

For a prime $d\equiv 7\pmod 8$, set $K=\mathbf Q(\sqrt{-d})$, $h=|\mathrm{Cl}(K)|$, and $\chi(m)=(m/d)$. The right side of `New.CMLattice.chowla_selberg` is the common area of certain rescaled conjugate lattices. In the notation of the classical gamma product, that area is

$$
B_d=\frac{\pi}{\sqrt d}
\left(\prod_{m=1}^{d-1}\Gamma(m/d)^{\chi(m)}\right)^{1/h}.
$$

### Matching the constants

Selberg and Chowla use a **negative** discriminant where Lean uses the positive integer $d$. Their Kronecker character for discriminant $-d$ is the Legendre character $\chi$ above. Write $P_d$ for the product in parentheses and $w$ for the number of roots of unity in $K$. On p. 110, the display immediately before equation (2) gives

$$
L'(1,\chi)=-\frac{\pi}{\sqrt d}\log P_d
+\frac{2h\pi}{w\sqrt d}\bigl(\gamma+\log(2\pi)\bigr).
$$

The factor at $m=d$ in the paper is $1$. Dividing by the class number formula $L(1,\chi)=2\pi h/(w\sqrt d)$ gives $\gamma-L'(1,\chi)/L(1,\chi)=(w/2h)\log P_d-\log(2\pi)$. Here $w=2$, since $d\ge 7$. The character is real, so the left side is exactly `chowlaSelbergConst d`. Multiplying its exponential by the Lean prefactor $2\pi^2/\sqrt d$ gives $B_d$. [Selberg and Chowla, *On Epstein’s zeta-function*, p. 110](https://doi.org/10.1515/crll.1967.227.86) · [Facsimile of the printed page](https://indico.mitp.uni-mainz.de/event/33/contributions/1437/attachments/1156/1224/elizalde.pdf#page=15)

### Which area appears in the proof?

In `sum_kronecker_terms`, take one CM lattice per ideal class $c$, with area $A_c$ and Weierstrass discriminant $\Delta_c=a_{1,c}^4-64$. The lemma says that the geometric mean of $A_c|\Delta_c|^{1/6}$ is $B_d$. It derives the mean by summing Kronecker’s limit formula over the classes. Comparing values at $s=1$ yields $wL(1,\chi)=2\pi h/\sqrt d$ (the local equality `h_val`), and comparing right derivatives yields the logarithmic derivative used above. The gamma product enters only in translating the answer into the paper’s notation. [Lean derivation at the audited revision](https://github.com/rohanarun/alpoge-rh-replay/blob/3fb826c01895b79e56bd9ea6582a9bf8ae8f4033/grh/src/Lib/CM/ChowlaSelberg.lean#L578-L625)

One way to check the scale is to write the period lattice as $a(\mathbf Z+\tau\mathbf Z)$ with $y=\operatorname{Im}\tau>0$. Then $A=|a|^2 y$ and $|\Delta|=(2\pi/|a|)^{12}|\eta(\tau)|^{24}$, so the arbitrary scale $a$ cancels and $A|\Delta|^{1/6}=4\pi^2 y|\eta(\tau)|^4$. For $d=23$, the reduced forms $(1,1,6),(2,1,3),(2,-1,3)$ give three values of $\tau=(-b+i\sqrt{23})/(2a_{\rm form})$. The geometric mean of their three scaled quantities and the gamma product with exponent $1/3$ both give $B_{23}\approx 11.1807825101$. [Period and discriminant normalization](https://github.com/rohanarun/alpoge-rh-replay/blob/3fb826c01895b79e56bd9ea6582a9bf8ae8f4033/grh/src/Lib/CM/KroneckerLimit.lean#L55-L74)

### Why the next lemma needs a unit

For a fixed CM lattice $C$, `chowla_selberg` constructs **one** $u$ such that $A(C^\sigma)|\sigma u|^2=B_d$ for every $\sigma\in\mathrm{Aut}(\mathbf C/K)$, and $|\iota_p u|_p=1$ at every $p$-adic place. The class-average formula supplies the complex value. To produce $u$, the proof chooses ideal representatives with product $(1)$ and takes a $12h$-th root of the product of their adjusted discriminants. The isogeny norm identity and the finite-place discriminant identity give the unit condition. Downstream, `periodFactor` divides the vacuum root by this same $u$. Division preserves the finite-place norm of the numerator, and the conjugate-area identity determines the complex scale. [Unit construction](https://github.com/rohanarun/alpoge-rh-replay/blob/3fb826c01895b79e56bd9ea6582a9bf8ae8f4033/grh/src/Lib/CM/ChowlaSelberg.lean#L692-L750) · [Choice of unit and period factor](https://github.com/rohanarun/alpoge-rh-replay/blob/3fb826c01895b79e56bd9ea6582a9bf8ae8f4033/grh/src/New/Derivatives/Vacuum/TightFrames.lean#L101-L129)
