# Averaging the finite prime sum over places

The step from the main inequality to a bound for the prime remainder sums the finite prime sums over the places congruent to $1$ modulo $q_0$. Moving the selected places within the fibre over $-1$ can change individual prime sums while leaving their sum fixed. The corresponding Lean lemmas are `card_filter_mem_bPlaces`, `sum_aPlaces_primeSum` and `totalRemainder_eq` in [PrimeSums.lean](../src/New/Reduction/PrimeSums.lean).

## Counting one prime power at a time

Write $G=(\mathbb Z/q_1)^\times$, $A=\ker(G\to (\mathbb Z/q_0)^\times)$ and let $B$ be the selected places in the fibre over $-1$. Denote by $g_n$ the place named by $-n$. For $n\equiv1\pmod {q_0}$, multiplication by $g_n$ sends $A$ bijectively onto the whole fibre over $-1$. Exactly $|B|$ values of $\tau\in A$ therefore satisfy $g_n\tau\in B$. For any other unit $n$, the image is a different fibre. If $n$ is a nonunit modulo $q_1$, `placeOfInt` returns the identity. Here $q_0$ and $q_1$ have the same prime divisors and $1\ne -1\pmod {q_0}$, so this case also gives zero hits. See [FieldsAndPlaces.lean](../src/New/Reduction/Data/FieldsAndPlaces.lean).

Let $H_z(n)=(1/n-1/z)_+$, $\lambda(n)=\Lambda(n)(1-(n/d))$, and $S_q(z)=\sum_{1\le n\le a,\ n\equiv1\bmod q}\lambda(n)H_z(n)$. The cutoffs satisfy $x\le x_1\le a$. The weight is $a/x$ on $B$ and $a/x_1$ elsewhere. Starting with the latter weight at every place and applying the count gives

$$
\frac1a\sum_{\tau\in A}s_{\rm fin}(a,\tau)
=|A|S_1(x_1)+|B|\bigl(S_{q_0}(x)-S_{q_0}(x_1)\bigr).
$$

In particular the cutoff correction has a negative sign when expressed as a loss. Inserting $S_q(z)=R_q(z)+\log z/\varphi(q)+c_q$ cancels $c_{q_0}$ between the two cutoffs. The fraction of *all* places in $B$ is $|B|/(|A|\varphi(q_0))$. Thus the geometric mean of the weights contributes $|B|\log(x/x_1)/\varphi(q_0)$ to $|A|s_{\rm main}/a$, alongside $|A|(\log x_1+c_1)$. Subtracting these terms gives the coefficients $|A|$ of $R_1(x_1)$ and $|B|$ of $R_{q_0}(x)-R_{q_0}(x_1)$ in `totalRemainder_eq`, after division by $a$.

## Two inert primes and two choices of places

Take $q_0=18480$, $d=582119$ (prime, with $d+1=63q_0/2$) and tower exponent $s=1$. Then $q_1=486q_0=8981280$ and $A=\{1+jq_0:0\le j<486\}$. Take $x=30000$ and $a=x_1=60000$, giving weights $2$ and $1$. This finite example isolates the averaging identity. The tower and scales do not satisfy the growth conditions on `New.Data`.

Up to $60000$, the residue class $1\bmod q_0$ contains $1$, $p=18481$, $36961=23\cdot1607$ and $r=55441$. Only $p$ and $r$ are prime powers. Both are prime and their Legendre symbols modulo $d$ are $-1$ (Euler's criterion gives $p^{291059}\equiv r^{291059}\equiv-1\pmod d$). At a place hit by $p$, changing the weight from $1$ to $2$ subtracts $U=2\log p$ from the prime sum. At a place hit by $r$ it subtracts $V=2(60000/r-1)\log r$, since $x<r<x_1$.

Let $h=r/p\equiv6911521\pmod {q_1}$, and compare $B_1=\{-1,-h\}$ with $B_2=\{-1,-h^2\}$, all residues taken modulo $q_1$. If $u=-p\tau$, then $-r\tau=hu$. A simultaneous hit is therefore counted by $|\{u\in B:hu\in B\}|$. The element $h$ has order $243$ (its $81$st power is $2993761$ and its $243$rd power is $1$ modulo $q_1$). This yields the following counts over the $486$ places.

| Selected places | Neither prime | Only $p$ | Only $r$ | Both |
| --- | ---: | ---: | ---: | ---: |
| $B_1$ | 483 | 1 | 1 | 1 |
| $B_2$ | 482 | 2 | 2 | 0 |

Relative to the common sum with weight $1$ everywhere, both choices lose $2U+2V$ in total. Their distributions over places differ. For uniform $\tau\in A$, the variance of $s_{\rm fin}(a,\tau)$ for $B_1$ exceeds that for $B_2$ by $2UV/486$, from the single simultaneous hit. The first-moment identity in the proof uses only $|B|$ because each prime power is counted separately.
