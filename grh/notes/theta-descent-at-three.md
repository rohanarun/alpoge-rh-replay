# A nonintegral block in theta descent, worked out at 3

How can a point with a nonintegral block ratio contribute zero to a theta descent? In the following example some integral changes of variables fix the point. At a twist place one of those changes multiplies the form by $-1$. The pairing is unchanged by the change of variables, so its value at the form is its own negative. The proof in Lean works for arbitrary nontrivial residue characters by summing over a finite matrix group. [Vanishing for a nonintegral block](../src/New/OneLift/FalseLifts/BottomOfTower.lean#L1425-L1454)

## An integral matrix with a nonintegral block ratio

Work over $\mathbb Q_3$ and include the first two coordinates into three. This is a possible completion at a split prime of a CM field. For instance, $3$ splits in $\mathbb Q(\sqrt{-2})$ since $T^2+2$ has two distinct roots modulo $3$. Consider the three-row, two-column matrix

$$
x=\begin{pmatrix}3&0\\0&1\\1&0\end{pmatrix},
\qquad x'=\begin{pmatrix}3&0\\0&1\end{pmatrix},
\qquad x''=\begin{pmatrix}1&0\end{pmatrix}.
$$

The top block is invertible over the field. Its determinant has 3-adic valuation one, and $x''(x')^{-1}=(1/3,0)$ is outside $\mathbb Z_3^2$. The row $L=(1,0,-3)$ satisfies $Lx=0$ exactly. Its first two coordinates reduce to the nonzero row $\lambda=(1,0)$ and its last coordinate reduces to zero. These are the conditions on an annihilating row at a twist place. [Block ratio and annihilating row](../src/New/OneLift/FalseLifts/BottomOfTower.lean#L264-L288)

For $a,b\in\mathbb Z_3$, form the rank-one shear

$$
h_{a,b}=I_3+\begin{pmatrix}a\\b\\0\end{pmatrix}L
=\begin{pmatrix}1+a&0&-3a\\ b&1&-3b\\ 0&0&1\end{pmatrix}.
$$

Then $h_{a,b}x=x$ because $Lx=0$. Its determinant is $1+a$, so $h_{a,b}$ is invertible over $\mathbb Z_3$ exactly when $a\not\equiv 2\pmod 3$. Reduction kills the entries $-3a,-3b$. The upper block of the result is $s=\left(\begin{smallmatrix}1+\bar a&0\\\bar b&1\end{smallmatrix}\right)$. The proof needs an integral lift for each such residue matrix. For instance, $h_{0,1}$ has order three after reduction, although $h_{0,1}^3=h_{0,3}$ has a nonzero entry $3$ in position $(2,1)$ over $\mathbb Z_3$. The finite sum is indexed by residue blocks. [Shear and determinant](../src/New/OneLift/FalseLifts/BottomOfTower.lean#L128-L142) · [Determinant identity](../src/New/OneLift/FalseLifts/BottomOfTower.lean#L161-L165) · [Lifting residue blocks](../src/New/OneLift/FalseLifts/BottomOfTower.lean#L1375-L1393)

## Which six matrices cancel?

Over $k=\mathbb F_3$, $\ker\lambda$ is the line spanned by the second basis vector. Its *pointwise* stabilizer $H\subseteq\mathrm{GL}_2(k)$ consists of the matrices whose second column is $(0,1)^\mathsf T$. Thus $H$ consists precisely of the six invertible $s$ above. Preserving the line as a set would also allow second column $(0,2)^\mathsf T$, giving twelve matrices. [Definition of the hyperplane group](../src/New/OneLift/FalseLifts/BottomOfTower.lean#L192-L208)

Let $\chi:k^\times\to\{1,-1\}\subset\mathbb C^\times$ be the nontrivial character, so $\chi(1)=1$ and $\chi(2)=-1$. Every determinant used here lies in $k^\times$. With $\bar b$ running through all three residues, the complete sum is

| $\bar a$ | $\det s$ | Number of blocks | $\chi(\det s)^{-1}$ per block | Contribution |
| ---: | ---: | ---: | ---: | ---: |
| $0$ | $1$ | $3$ | $1$ | $3$ |
| $1$ | $2$ | $3$ | $-1$ | $-3$ |

At a twist place, the single-place block action on $y$ is just $\chi(\det s)^{-1}y$. Its sum is zero. In general the determinant maps the hyperplane group onto $k^\times$ for $\lambda\ne0$, so the inverse of a nontrivial character has sum zero there as well. At a chosen place the block action also applies a representation to $y$. As a finite-group test, taking the representation $\sigma(s)=\chi(\det s)$ on $\mathbb C$ makes every weighted action $\chi(\det s)^{-1}\sigma(s)$ the identity. The sum acts as $6$, which explains the separate annihilation hypothesis on the form at the chosen places. [Character sum](../src/New/OneLift/FalseLifts/BottomOfTower.lean#L210-L226) · [Two block actions](../src/New/OneLift/FalseLifts/BottomOfTower.lean#L1324-L1348) · [Use of the two hypotheses](../src/New/OneLift/FalseLifts/BottomOfTower.lean#L1350-L1366)

## From the sum to a pairing

For the global descent data in the theorem, let $B(y)$ be the pairing against the indicator of a class around the adelic point $z$. The proof lifts each $s\in H$ to a level element fixing the relevant components of $z$. Translation therefore gives $B(\operatorname{blockAction}(s)y)=B(y)$ for every $s$. Adding these equalities gives $6B(y)=0$ in our residue example, because the block actions sum to zero and the conjugate-linear pairing $B$ is additive. The pairing is complex-valued, so $B(y)=0$. [Translation and summation](../src/New/OneLift/FalseLifts/BottomOfTower.lean#L1436-L1454)

The matrices above realize the local nonintegral ratio, annihilating row and twist-place character sum. Applying the global result also requires a descent pair with its level and Weil data, an adelic point and a form satisfying the hypotheses at the other places. The theorem for *all* descent data additionally assumes vanishing for the block datum and treats points with integral ratios in a separate branch. The later period theorem requires $2r+2N+3<n$. With $r=2$ and $n=3$, that inequality already fails at $N=0$. [Rank assumption in the period theorem](../src/New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean#L10-L18) · [Local-to-global hypotheses](../src/New/OneLift/FalseLifts/BottomOfTower.lean#L8-L35) · [Bottom-of-tower theorem](../src/New/OneLift/FalseLifts/BottomOfTower.lean#L1456-L1483)
