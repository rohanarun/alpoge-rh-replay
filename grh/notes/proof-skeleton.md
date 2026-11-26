# Proof skeleton: from the five statements to the three main theorems

This note is a reading aid, not a verification and not a substitute for `GUIDE.md` or `INDEX.md`.
`GUIDE.md` is organised by topic and reads bottom-up; `INDEX.md` is a table of results and sources.
This note does one different thing: it follows the **single logical chain** from the five headline
statements down to the three main theorems (A, B, C), naming the exact file and line of each step.
A newcomer who wants to see "what actually proves RH, in order" can read this in a few minutes and
then use `GUIDE.md` to descend into any one step.

Everything below is at commit `de0d3a3f06` (readable edition `grh/`, Lean v4.37.0-rc1). Line
numbers refer to that commit. This note is a contribution to `grh/notes/` in the spirit of
`auto-research.md` item 4 ("Understand"); it changes no proof file and touches no challenge file.

## The five statements

`Statements.lean` defines four propositions in Mathlib's terms (`RiemannZetaZerosOnLine` at
`src/Statements.lean:7`, `DirichletLNonvanishingRightOfHalf`, `DirichletLZerosOnLine`,
`PrimitiveDirichletLZerosOnLine`). `src/Main.lean` proves the five theorems from a single object,
`New.grh`, plus two symmetry lemmas:

| theorem (`src/Main.lean`) | proof term |
|---|---|
| `riemannHypothesis` (L9) | `New.zeta_zeros_on_line New.grh` |
| `riemannZeta_eq_zero_re` (L12) | `riemannHypothesis` |
| `LFunction_ne_zero_of_half_lt_re` (L17) | `New.grh` |
| `LFunction_eq_zero_re` (L21) | `New.zeros_on_line New.grh` |
| `LFunction_eq_zero_re_of_isPrimitive` (L25) | `LFunction_eq_zero_re` |

So the whole development has one mathematical target:

> `New.grh : DirichletLNonvanishingRightOfHalf` — no Dirichlet L-function vanishes in `re s > 1/2`
> (except the pole at `s = 1` for the principal character).

The other two ingredients are pure functional equation: `New.zeros_on_line`
(`src/New/Main.lean:32`) and `New.zeta_zeros_on_line` (`:41`) pass from a zero-free half-plane to
zeros on the critical line via `gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero`.

## The chain from `grh` down to Theorems A, B, C

Read this top to bottom; each box is proved from the boxes below it.

```
five statements (src/Main.lean:9-26)
        |
        v
New.grh : nonvanishing in re s > 1/2        (New/Reduction/OneSidedBound.lean:239)
        |
        | uses the one-sided criterion
        v
New.LFunction_ne_zero_of_primeRemainder_le  (New/Reduction/Zeros/Criterion.lean:41)
        |
        | needs: R_q(x) <= A * x^(beta-1) eventually, for 1/2 < beta < re(rho)
        v
eventually_primeRemainder_le_mul_rpow       (New/Reduction/OneSidedBound.lean:204)
   R(y) <= (128 phi(q0)+32) y^(-1/2+eps)     <-- "the one-sided bound"
        |
        | from the integer bound (L129) + prime remainder at the far cutoff x1
        v
Data.primeRemainder_le                       (New/Reduction/OneSidedBound.lean:37)
        |
        | divides star_inequality by m * a * #Phi_b
        v
star_inequality : m * rem <= f * a * (log b)^5   (New/Reduction/MainInequality.lean:91)
        |
        | mainAmount cancels; built from Theorems A, B, C
        +------------------+------------------+
        v                  v                  v
  Theorem A          Theorem B          Theorem C
  short forms        enough forms       integral forms are long
  (ShortAndEnough    (ShortAndEnough    (Determinant/Twist/LongForms.lean:255)
   .lean:192,312)     .lean:387)
```

### The single inequality everything reduces to

`MainInequality.lean:9-18` states it plainly. For a family of `n <= dim` target forms with covolume
bound `V` and index bound `delta`:

```
mainAmount <= (V + 2*delta) / dim  <=  mainAmount - (n/dim) * m * rem
```

The upper bound is Theorems A + B (build a spanning family with controlled covolume and index);
the lower bound is Theorem C. The `mainAmount` cancels between them, leaving `m * rem` bounded by
the errors (`MainInequality.lean:59-69`: `f a log^4 b` from size, `20 log(1+2b^2) f a log^3 b`
from index, `3 f a log^4 b` from covolume), which are of order `f a log^5 b`.

### What each main theorem supplies

- **Theorem A** — `span_short_integralRamified_eq_top` (`ShortAndEnough.lean:192`) and
  `indexLe_normalizedPoincare` (`:312`): a multiple of the projected Poincaré series has short lifts
  and small index. Its two ingredients are the seesaw identity (`New/UpperBound/Seesaw`) and the
  local divisibility of the composite lift (`New/UpperBound/Divisibility/LocalDivisibility`).
- **Theorem B** — `enough_forms` (`:387`): few translates of the Poincaré map span almost all of the
  target. This is the second moment / spanning result in `New/Spanning`.
- **Theorem C** — `integral_forms_long` (`LongForms.lean:255`): covolume plus twice the index of a
  spanning family is at least about the main amount. It comes from a twist for each prime
  (`covolume_add_index_nonneg`) and the height of `Z(1)/Z(xi_iota)` (`heightLe_chainDeterminant_one_div`),
  drawing on `New/Determinant`, `New/OneLift` and `New/Congruences`.

## How the last analytic step closes

`OneSidedBound.lean:239-268` is short enough to summarise. Fix a Dirichlet character `chi` modulo
`q` and a zero `rho` with `re rho > 1/2`. Pick `beta` with `1/2 < beta < re rho`. Set
`d0 = 9240 q - 1`, so `d0 + 1 = q0/2` for `q0 = 18480 q`. For any prime `d` congruent to `d0` mod
`18480 q`, the one-sided bound applies (with exponent `beta - 1/2 > 0`), giving the hypothesis of
the criterion; `LFunction_ne_zero_of_primeRemainder_le` then gives nonvanishing of the induced
character at `rho`, and inducing back multiplies by finitely many nonvanishing local factors.

## A naming note on the index

The one-sided bound is named `eventually_primeRemainder_le_mul_rpow`
(`New/Reduction/OneSidedBound.lean:204`). An older name, `eventually_primeRemainder_le_rpow`, still
appears in some indexes and may be what a reader finds when searching; it is not a declaration in
this tree. The upstream index has already been corrected in
`leanprover-community/riemann-hypothesis#5638`.
