# From a Behrend sphere to a sparse set of places

The sparsity test allows a place to occur several times. Fix a prime $p\le L$, a base place $\sigma\in T$, and let $m$ be $q_1$ with its entire $p$-part removed. Mark an exponent $0<i<\ell_0$ if either $p^i$ or $-p^i$ occurs among the ratios $\tau/\sigma\pmod m$ for $\tau\in T$. Then `IsSparse` says that each such list has at most one **exponent**. Two different exponents can violate the condition even if they reach the same place. [Lean definition](../src/New/Reduction/Data/AdmissibleData.lean#L57-L67)

### Why the signs cost a factor of two

Write the chosen places as $-g^e$, with $g=1+3\ell_0q_0$. For odd $p$ the proof projects to the factor modulo $2^{s+v}$ where $g$ has order $2^s$. If $i<j$ are both marked, raising the two ratios to powers $2j$ and $2i$ gives the same $p^{2ij}$. The factors of two remove the independently chosen signs. The resulting congruence is

$$
2j e_2\equiv 2(j-i)e_1+2i e_3 \pmod {2^s}.
$$

The Behrend construction allows positive weights of total at most $2\ell_0$. Its base $2\ell_0 H$ keeps both weighted digit expansions carry-free, and the room condition keeps their values below $2^s$. Thus the congruence is an equality of digit vectors; strict convexity on a common sphere forces $e_1=e_2=e_3$. Keeping the factor of two preserves the modulus throughout. [Digit argument](../src/New/Reduction/Data/Existence.lean#L86-L120) · [Group order and exponent comparison](../src/New/Reduction/Data/Existence.lean#L220-L238)

Equal exponents still need to be ruled out. They would give $p^{2i}=1\pmod {2^{s+1}}$, which implies $2^s\le (p+1)2i$ and contradicts $2\ell_0(L+1)<2^s$. For $p=2$ the surviving factor is instead $3\ell_0$. Every ratio equals $1$ there; squaring a signed hit would give $4^i=1$, impossible because $4$ has order $\ell_0$ modulo $3\ell_0$. [The two prime cases](../src/New/Reduction/Data/Existence.lean#L204-L244)

### An exact finite check

Take $q_0=18480$, $d=9239$, $s=64$, $L=31$, and four base-$2\ell_0 H$ digits with $H=4$. Here $\ell_0=2187$, the room condition holds, and the squared-radius-14 shell consists of the 24 permutations of $(0,1,2,3)$. The cardinality guarantee for these parameters is $4^4/(4\cdot4^2)=4$. The following Python checks the resulting places directly against the definition. A second set in the same residue class supplies a failing control: at the base place $-1$, the exponents 20 and 40 both hit for $p=13$.

```python
from itertools import permutations

q0, s, ell0, H, L = 18480, 64, 2187, 4, 31
q1 = q0 * 3 * ell0 * 2**s
base, g = 2 * ell0 * H, 1 + 3 * ell0 * q0
assert base**4 <= 2**s and 2 * ell0 * (L + 1) < 2**s
exponents = [sum(x * base**k for k, x in enumerate(digits))
             for digits in permutations(range(H))]
places = {-pow(g, e, q1) % q1 for e in exponents}
assert len(places) == 24 and all(x % q0 == q0 - 1 for x in places)

def hits(points, sigma, p):
    modulus = q1
    while modulus % p == 0:
        modulus //= p
    inverse = pow(sigma, -1, modulus)
    ratios = {tau * inverse % modulus for tau in points}
    power, marked = 1, []
    for i in range(1, ell0):
        power = power * p % modulus
        if power in ratios or -power % modulus in ratios:
            marked.append(i)
    return marked

primes = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31)
assert max(len(hits(places, sigma, p)) for sigma in places for p in primes) == 0
control = {-pow(13, i, q1) % q1 for i in (0, 20, 40)}
assert all(x % q0 == q0 - 1 for x in control)
assert {20, 40} <= set(hits(control, q1 - 1, 13))
```
