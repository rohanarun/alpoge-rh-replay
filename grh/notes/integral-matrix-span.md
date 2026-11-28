# Stable lattices and the ring over which the image spans

For a compact subgroup of $\mathrm{GL}_n(\overline{\mathbf Q}_\ell)$, Conrad's
Theorem 1 puts all its matrices in $\mathrm{GL}_n(F)$ for **one** finite
extension $F/\mathbf Q_\ell$. The readable proof also finds an integral
model: `New.eventually_exists_isLatticeIn` conjugates a continuous
representation of a compact group into matrices over every sufficiently large
coefficient ring. An invariant norm supplies the integral basis, and
compactness and the Baire argument give the finite field of coefficients.
[Conrad, Theorem 1](https://kconrad.math.uconn.edu/blurbs/gradnumthy/GLnQpbar.pdf#page=1)
· [Lean statement and proof](../src/Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean)

The additional input in
[`New.Selmer.IsLatticeIn.span_range_eq_top_of_map_pow_eq_map_conj`](../src/Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean)
is a tame pair $\gamma,\phi$ and an eigenvalue whose $q$-power conjugates are
pairwise distinct modulo the maximal ideal. Under the lemma's power and
conjugacy hypotheses, the image of the integral representation $u$ spans
$M_n(O)$ **over $O$**, and $u(\phi^{-n})$ is scalar. Both conclusions are used
in [`eventually_span_eq_top_and_exists_scalar_of_tame_pair`](../src/New/Congruences/GaloisRepresentations/RowsAndColumnsFromLabels.lean).

Why does the ring matter? Fix a lattice $O^n$ over a discrete valuation ring
$O$ with fraction field $F$. If the $O$-span of the image is $M_n(O)$, then
every stable full $O$-lattice $L$ in $F^n$ is homothetic to $O^n$. Indeed each
matrix unit preserves $L$. The diagonal matrix units split $L$ into coordinate
fractional ideals; the off-diagonal matrix units identify all those ideals. Thus
$L=I^n$ for one fractional ideal $I$, which is principal over $O$.

For a counterexample with full **field** span, take
$O=\mathbf Z_\ell$, $F=\mathbf Q_\ell$, and $G=1+\ell M_2(O)$. This compact
group spans $M_2(F)$: subtract $1$ from $1+\ell E_{ij}$ and divide by $\ell$.
Its image acts trivially on $O^2/\ell O^2$, so the inverse image of each
residue line is stable. In particular $O e_1\oplus \ell O e_2$ is stable
and has index $\ell$ in $O^2$. A scalar sublattice of $O^2$ has index
$\ell^{2k}$ for an integer $k\geq 0$, so these two lattices are inequivalent
up to homothety. Reduction of the $O$-span of $G$ gives only scalar matrices.
