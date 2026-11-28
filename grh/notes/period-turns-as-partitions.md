# Counting the turns in the period transfer

The [first-to-last path theorem](../src/New/Determinant/AuxiliaryForms/DiagonalTurns.lean#L636)
uses one factor for every ordered pair $(i,j)$ in an $m$ by $m$ square.
A partition gives a direct way to recover those labels from the path and
to check the reflection of the two halves.

Write the path, in its original direction from $(m,0)$ to $(0,m)$, as a
word with $m$ left steps $L$ and $m$ up steps $U$. For $0\le j<m$ let
$\lambda_j$ be the horizontal coordinate of the up step starting at
height $j$. Equivalently it is the number of left steps still to come at
that point. The weakly decreasing row lengths $\lambda_j$ form a
partition in the $m$ by $m$ square. The word can be recovered by moving
left to $\lambda_j$ before each up step and completing the final row
with the remaining left steps.

### Recovering the two halves

Every step reduces $x-y$ by one. After exactly $m$ steps the path reaches
$(l,l)$. For $j<l$ we have $\lambda_j\ge l$, and for $j\ge l$ we have
$\lambda_j\le l$. Thus $l$ is the side of the largest square in the
partition's upper-left corner (the Durfee square, with row zero on top).

The [definition of `TwoGridPath.squares`](../src/New/Determinant/AuxiliaryForms/GridPaths.lean#L194)
reconstructs the partition from three disjoint pieces.

* The $l$ by $l$ square gives all $(i,j)$ with $i,j<l$.
* The second half, read backwards, records rows $j\ge l$ at their original
  widths $\lambda_j$. These cells are `half false`'s squares.
* A left step in the first half from $(i+1,j)$ to $(i,j)$ has $i\ge l$.
  After exchanging the coordinates it contributes $(a,i)$ for $a<j$.
  Swapping back gives the cells $(i,a)$ in column $i$ of the first $l$
  rows. This is the `Prod.swap` on `half true`'s squares.

For example, $LULLUU$ at $m=3$ has row lengths $(2,0,0)$ and $l=1$.
The extra cell beyond the Durfee square is $(1,0)$. Before reflection the
first half records it as $(0,1)$. The diagonal is also a count check:
exactly $\binom{m}{l}^2$ words pass through $(l,l)$, since each half has
length $m$ and independently chooses the positions of its $l$ steps of
one type.

### One new cell per turn

A turn replaces $LU$ by $UL$. If the old corner is $(i,j)$, only row $j$
changes, and its length increases from $i$ to $i+1$. This adds precisely cell
$(i,j)$, agreeing with [`Turn.squares_eq`](../src/New/Determinant/AuxiliaryForms/GridPaths.lean#L237).
The first and last paths correspond to the empty and full partitions.
Every complete sequence of turns therefore uses each of the $m^2$ labels
exactly once. A concrete order is to move the first up step past every
left step, then the second one, and so on. This visits
$(0,j),\ldots,(m-1,j)$ in each successive row $j$.

This explains the product over all ordered pairs and the exponent $m^2$
on `vectorCountBound`. For $m=3$ there are 20 paths and 30 possible
single turns between them. Starting the empty partition with count one
and summing the counts of the partitions obtained by removing one corner
gives 42 complete turn sequences. Each sequence has length nine.
