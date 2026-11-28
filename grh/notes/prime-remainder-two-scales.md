# What the prime number theorem supplies at the second cutoff

The proof bounds a smoothed prime-counting remainder at two different arguments. The desired conclusion is an upper bound of order $x^{-1/2+\eta}$ at the integer $x$, for every fixed $\eta>0$. The classical analytic input bounds the absolute value of the remainder at a much larger integer $x_1$. The size of $x_1$ determines what this input can contribute.

Fix the modulus $q_0$ and the auxiliary prime $d$ specified by the parameters of the proof. Write $R_j(y)=\mathtt{primeRemainder}\ d\ j\ y$. This is the smoothed sum of $\Lambda(n)(1-(n/d))(1/n-1/y)$ over $n\le y$, $n\equiv1\pmod j$, with its main term and constant subtracted. Here $(n/d)$ denotes the Legendre symbol and $\Lambda$ is the von Mangoldt function. The geometric argument gives

$$
R_{q_0}(x)\le \frac{\varphi(q_0)(\log b)^6}{m}
+|R_{q_0}(x_1)|+(\log b)|R_1(x_1)|.
$$

The ordinary prime number theorem used here gives $|R_j(y)|\le (\log y)^{-B}$ eventually for each fixed integer $B\ge0$, for both $j=q_0$ and $j=1$. The source derives this from a zero-free region near $\operatorname{Re}s=1$ and a Tauberian theorem. Its threshold may depend on $d,q_0,B$. [Geometric inequality](../src/New/Reduction/OneSidedBound.lean#L42-L76) · [Zero-free region](../src/New/Reduction/Zeros/PrimeNumberTheorem.lean#L169-L182) · [Prime number theorem](../src/New/Reduction/Zeros/PrimeNumberTheorem.lean#L202-L218)

### Testing the polynomial lower bound

The general data impose $x_1\ge x^{10^6}$. To test the strength of this inequality, take $x_1=x^K$ for any fixed $K\ge10^6$, and consider the comparison function $F(y)=\exp(-\sqrt{\log y})$ for $y\ge1$. For every fixed $B$, writing $u=\sqrt{\log y}$ gives $(\log y)^B F(y)=u^{2B} e^{-u}\to0$. Thus $F$ satisfies all the stated inverse-logarithmic bounds. Yet $x^2 F(x^K)=\exp(2\log x-\sqrt{K\log x})\to\infty$. Even the whole family of PNT estimates cannot, on its own, give $|R_j(x_1)|\le x^{-2}$ from this polynomial separation. [Scale condition in the data](../src/New/Reduction/Data/AdmissibleData.lean#L103-L110)

### The cutoff in the existence theorem

Fix $0<\varepsilon<1/100$. For **every** sufficiently large integer $x$, the proof constructs data with $x_1=\lfloor\exp(x^{\varepsilon/6})\rfloor$, $\log b\le 2x^\varepsilon$ and $m\ge\sqrt x$. It proves $\log x_1\ge x^{\varepsilon/6}-1\ge x^{\varepsilon/12}$ eventually. Choose one integer $B\ge24/\varepsilon$ before sending $x$ to infinity. For either modulus, once past both PNT thresholds,

$$
|R_j(x_1)|\le (\log x_1)^{-B}\le x^{-\varepsilon B/12}\le x^{-2}.
$$

The weighted tail is then at most $2x^{-2+\varepsilon}$. The first term in the geometric inequality is at most $64\varphi(q_0)x^{-1/2+6\varepsilon}$, so altogether $R_{q_0}(x)\le (64\varphi(q_0)+3)x^{-1/2+6\varepsilon}$. The factor $x^{-1/2}$ at the primary cutoff comes from $1/m$. The final zero-free criterion takes the auxiliary prime $d$ outside the eventual-in-$x$ assertion, so each $d$ may have its own threshold. [Construction](../src/New/Reduction/Data/Existence.lean#L893-L901) · [Cutoff conversion](../src/New/Reduction/OneSidedBound.lean#L83-L126) · [Three-term bound](../src/New/Reduction/OneSidedBound.lean#L134-L166) · [Order of quantifiers](../src/New/Reduction/OneSidedBound.lean#L261-L272)
