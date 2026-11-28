# A singular Gram block in the lattice Jacobi identity

The [lattice Jacobi identity](../src/Lib/General/NumberTheory/LatticeCovolumes.lean#L324)
allows an isotropic column space. The [application to the link lattice](../src/New/Spanning/RemainingTerms/LinkLattice.lean#L304)
uses the nonzero determinant of the bordered Gram matrix. Here is a
two-dimensional case in which the bordered determinant is nonzero even
though both diagonal blocks vanish.

Use the [adelic pair](../src/Lib/Adelic/Adeles/LocalFactors.lean#L221)
$R=\widehat{\mathcal O}_E\subset A=\mathbb A_{E,f}$ for
$E=\mathbf Q(\zeta_{5040})$. Write $D=[E:\mathbf Q]$. All entries below
embed diagonally. Put

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
F=h e_1,\qquad n=e_1,\qquad p=(u,v)^t
$$

with $0\ne h\in\mathcal O_E$, $u,v\in E$, and border parameter
$c\in\mathbf Q^\times$. The form $J$ is unimodular, $n$ is primitive,
and $F^*Jn=0$. The kernel of $n^*J=(0,1)$ equals $A e_1=F A$.
In particular the two column spaces coincide. The integral inverse image
$\{y:Fy\in R^2\}$ is $h^{-1}R$, so its index over $R$ is
$[h^{-1}R:R]=[R:hR]=|N_{E/\mathbf Q}(h)|$.

The matrix on the right side of Jacobi's identity and the scalar on the
orthogonal line on the left are respectively

$$
G=\begin{pmatrix}
0&\bar h v\\
\bar v h&\bar u v+\bar v u+c
\end{pmatrix},\qquad
n^*(J+c^{-1}Jpp^*J)n=\frac{v\bar v}{c}.
$$

Hence $\det G=-h\bar h v\bar v$. On a principal element the
[generalized index equals the absolute field norm](../src/Lib/Adelic/Adeles/IdeleModulus.lean#L406).
Multiplying the generalized index of $v\bar v/c$ by the **square** of
$[h^{-1}R:R]$ and by the generalized index of $c$ gives exactly the
generalized index of $\det G$.

For a concrete test, choose $i=\zeta_{5040}^{1260}$, $h=1+i$,
$u=1$, $v=1+2i$ and $c=-2$. Then

$$
G=\begin{pmatrix}0&3+i\\3-i&0\end{pmatrix},\qquad
\det G=-10,\qquad n^*(J+c^{-1}Jpp^*J)n=-5/2 .
$$

Here $[h^{-1}R:R]=2^{D/2}$ by the norm tower through $\mathbf Q(i)$.
The three factors in the index identity give
$(5/2)^D (2^{D/2})^2 2^D=10^D$.
Neither diagonal block of $G$ can be inverted to take its Schur
complement. The [basis used in the proof](../src/Lib/General/NumberTheory/LatticeCovolumes.lean#L266)
is visible in this example: saturate $F$ to $e_1$ and use its $J$-dual
lift $e_2$. The columns $(e_2,n)$ form an integral basis.
