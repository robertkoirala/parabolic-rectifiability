# Overview

This page introduces the mathematics formalized in this library, states the
main results in words with their Lean names, and records where the Lean
encoding differs from the conventions of a paper. The precise statements are in
[theorems.md](theorems.md), the definitions are listed in
[definitions.md](definitions.md), and the module structure is described in
[architecture.md](architecture.md).

## The setting

The ambient space is $`X=\mathbb R^n\times\mathbb R`$ with the parabolic metric
and dilations

```math
d_P((x,t),(y,s))=\max\{\lVert x-y\rVert,\sqrt{|t-s|}\},
\qquad \delta_r(x,t)=(rx,r^2t).
```

In Lean, `Space n` is the product of `Spatial n` (Euclidean $`n`$-space) and
`Time`, the real line with the square-root metric `Metric.Snowflaking`; the
product metric is the maximum, and `point x t` inserts ordinary coordinates
([Basic.lean](../ParabolicRectifiability/Basic.lean#L32)). Translated dilations
$`T(q,a)(x,t)=((x-q_x)/a,(t-q_t)/a^2)`$ are `similarity q a`
([Metric/Similarity.lean](../ParabolicRectifiability/Metric/Similarity.lean#L35)).
$`P(a,R)`$ is the open ball `Metric.ball a R`. The Hausdorff measure
$`\mathcal H_P^k`$ is mathlib's unnormalized `Measure.hausdorffMeasure k` for this
metric (`hausdorffP n k`, [Metric/Hausdorff.lean](../ParabolicRectifiability/Metric/Hausdorff.lean#L26)). The parabolic dimension of $`X`$ is $`n+2`$.

The principal results take $`n\ge1`$ and an integer $`1\le k\le n+2`$.

### Models

Two kinds of affine models of parabolic dimension $`k`$ are used.

- A *horizontal* model is an affine spatial $`k`$-plane at a fixed time (`HorizontalModel n k`). It requires $`1\le k\le n`$.
- A *vertical* model is an affine spatial plane of rank $`k-2`$ times all of time (`VerticalModel n k`). It requires $`2\le k\le n+2`$; the rank is allowed to be $`0`$ (at $`k=2`$) and, at $`k=n+2`$, a vertical model is the whole space.

`FamilyKind` is `horizontal`, `vertical` or `mixed`, and `Models n k T` is the
corresponding type of models: the mixed family is the disjoint union of the two.
A family is *given* when this type is nonempty. In other dimensions the type is
empty, rather than containing a fictitious model; for example horizontal models
do not exist at $`k=n+1`$ and $`k=n+2`$, nor vertical models at $`k=1`$.

### Beta numbers and square energies

For a measure $`\mu`$, a family $`T`$, a center $`z`$ and a radius $`r>0`$,

```math
\beta_{\mu,T}^2(z,r)=r^{-k-2}\inf_{L\in T}\int_{P(z,r)}d_P(w,L)^2\,d\mu(w),
\qquad
S^R_{\mu,T}(z)=\int_0^R\beta_{\mu,T}^2(z,r)\,\frac{dr}{r}.
```

These are `betaSq` and `squareEnergy`
([Measure/Beta.lean](../ParabolicRectifiability/Measure/Beta.lean#L73),
[Measure/ScaleEnergy.lean](../ParabolicRectifiability/Measure/ScaleEnergy.lean#L102)).
The superscript of $`S`$ is the scale endpoint, never an exponent. The
beta-$`p`$ versions, for real $`p>0`$, are

```math
B_p(z,r)=r^{-k-p}\inf_{L\in T}\int_{P(z,r)}d_P(w,L)^p\,d\mu(w),\quad
S_p^a(z)=\int_0^aB_p(z,r)^{2/p}\frac{dr}{r},\quad
T_p^a(z)=\int_0^aB_p(z,r)\frac{dr}{r}
```

(`betaPow`, `energyS`, `energyT` in
[Foundations/BetaPow.lean](../ParabolicRectifiability/Foundations/BetaPow.lean#L45)).
The identities $`B_2=\beta^2`$ and $`S_2=T_2=S`$ are theorems, not definitions.

### Graphs and rectifiability

A *horizontal graph* of slope at most $`\varepsilon`$ is given over an arbitrary
subset of a spatial $`k`$-plane $`U`$: a normal displacement $`g:A\to U^\perp`$ and a
time function $`h:A\to\mathbb R`$ with
$`\max\{\lVert g(u)-g(v)\rVert,\sqrt{|h(u)-h(v)|}\}\le\varepsilon\lVert u-v\rVert`$
(`HorizontalGraph`). A *regular vertical graph* is a full space-time graph over
the base $`W\times\mathbb R`$, $`\dim W=k-2`$: $`(u,t)\mapsto(a+u+G(u,t),t)`$ with $`G`$
normal-valued, parabolic Lipschitz, and with the half-time derivative
$`|D_t|^{1/2}G`$ in parabolic BMO; the total norm is the sum of the Lipschitz
constant and the BMO seminorm. Two classes of vertical functions occur
([Foundations/Graphs.lean](../ParabolicRectifiability/Foundations/Graphs.lean#L35),
[Geometry/Graphs.lean](../ParabolicRectifiability/Geometry/Graphs.lean#L41)):
the *general* regular class, with no support or $`L^2`$ hypothesis, and the
smaller *constructed* class $`G=c+H`$ with $`H`$ compactly supported. A proved
inclusion relates them; see [theorems.md](theorems.md) for which statement uses
which.

A set $`K`$ has a *typed graph cover at tolerance $`\varepsilon`$* if countably many
graphs of the type, with slope or norm at most $`\varepsilon`$, cover $`K`$ up to a
set of zero $`\mathcal H_P^k`$ outer measure. A measure $`\mu`$ is *regularly
rectifiable of type $`T`$* (`IsRegularlyRectifiableMeasure T k μ`) if
$`\mu\ll\mathcal H_P^k`$ and $`\mu`$ is carried by countably many type-$`T`$ graphs,
each with its own finite slope or norm.

### Measures and densities

Densities are $`\Theta_*^k(\mu,z)=\liminf_{r\downarrow0}\mu(P(z,r))/r^k`$ and
$`\Theta^{k,*}(\mu,z)=\limsup_{r\downarrow0}\mu(P(z,r))/r^k`$, valued in
$`[0,\infty]`$. An *intrinsic source* is a measure absolutely continuous with
respect to $`\mathcal H_P^k`$ that has a Borel carrier which is a countable union
of Borel sets of finite $`\mathcal H_P^k`$ measure (`IsIntrinsicSource`).

## The main results

Throughout, $`\mu`$ is a locally Radon measure on $`X`$ (see the conventions
below), $`n\ge1`$ and $`1\le k\le n+2`$.

1. **Parabolic rectifiable Reifenberg theorem.**
   `ParabolicRectifiability.rectifiable_reifenberg` (with
   `main_rectifiability`, `fixed_family_rectifiability`,
   `ambient_rectifiability`, `family_rectifiable_reifenberg`).
   If the set of points of the unit ball where the mixed square energy with
   endpoint 2 exceeds $`M`$ has $`\mu`$-measure at most $`\Gamma`$, then
   $`\mu=\mu_++\mu_H+\mu_V`$, where $`\mu_H,\mu_V`$ are restrictions of $`\mu`$ to
   disjoint Borel subsets of the unit ball, their supports are compact, they are
   covered by horizontal, respectively regular vertical, graphs at every
   tolerance up to $`\mathcal H_P^k`$-null sets, the union of the supports obeys
   $`k`$-dimensional Hausdorff-content, separated-set, tube-volume and packing
   bounds, and $`\mu_+(P(0,1))\le CM+\Gamma`$ with $`C=C(n)`$. No density, doubling
   or finite-mass assumption is made. For a fixed testing family the opposite
   retained piece is zero. At $`k=n+2`$ the remainder in the unit ball is zero with
   no energy hypothesis.

2. **Qualitative characterization.**
   `ParabolicRectifiability.Characterization.qualitative_characterization`.
   For a given family $`T`$, regular type-$`T`$ rectifiability of $`\mu`$ is
   equivalent, for one or for every endpoint $`R>0`$, to each of three conditions:
   finite square energy with positive upper and finite lower density; finite
   square energy with positive finite upper density; absolute continuity,
   a Borel sigma-finite $`\mathcal H_P^k`$ carrier, and finite square energy,
   all $`\mu`$-almost everywhere.

3. **Canonical decomposition and integral criteria.**
   `ParabolicRectifiability.IntegralCanonical.canonical_decomposition`
   and `integral_criterion`. For an intrinsic source (or one with positive
   finite upper density a.e.), splitting $`\mu`$ along the sets where the
   horizontal, the vertical, and the mixed square energy are finite gives a
   unique decomposition into a horizontally rectifiable, a regularly vertically
   rectifiable and a graph-pure measure, pairwise mutually singular and
   independent of the endpoint. Separately, finiteness of the square energy
   $`\mu`$-a.e. can be replaced by any of five integral tests (vanishing capped
   tail, vanishing normalized capped energy, compact integrable exhaustion,
   strictly positive weight, adaptive concave gauge), and each of the three
   structural conditions can be paired with each test: fifteen criteria for
   regular rectifiability.

4. **Quantitative characterization.**
   `ParabolicRectifiability.QuantitativeCharacterization.quantitative_characterization`.
   For an $`A`$-Ahlfors regular measure with unbounded support, the Carleson
   energy $`M_\beta=\sup R^{-k}\int_{P(a,R)}S^R\,d\mu`$ is finite if and only if
   $`\mu`$ is quantitatively rectifiable: absolutely continuous with respect to
   $`\mathcal H_P^k`$ and admitting, at every root $`P(a,R)`$ centered on the
   support, a regular mixed covering with packing constants $`K`$. The covering
   constant is bounded by $`C(1+M_\beta)`$ and $`M_\beta\le CK`$, with a reverse
   bound $`M_\beta\le C_{\rm rev}K`$ for every value $`L\ge1`$ of the second covering parameter.

Enhancements and beta-$`p`$.

- **Graph-domain covers and scaling.**
  `Enhancements.graphDomainCover_of_fixedCarrier` produces, for a compact
  carrier of finite $`\mathcal H_P^k`$ measure with typed graph covers,
  graph-domain covers (graph maps, disjoint traces, small patches, and charge
  estimates controlled by $`\mathcal H_P^k`$). `Enhancements.scaled_rectifiable_reifenberg`
  transports the rectifiable Reifenberg decomposition to an arbitrary parent ball
  $`P(a,R)`$ with the scaling identities for $`\beta`$ and the energy and loss
  $`\le CMR^k+\Gamma`$. The library also proves the graph-domain enhancement of
  the rectifiable Reifenberg supports (`graph_enhanced_rectifiable_reifenberg`), power-energy and
  gauge-energy rate theorems (`power_rate`, `gauge_rate`) and density
  corollaries in the `Enhancements` area.
- **Beta-$`p`$.** `BetaP.betaP_support_theorem`: for $`p\ge2`$ the energy $`S_p`$ and
  for $`0<p\le2`$ the energy $`T_p`$ give the support decomposition with loss
  $`CM^{p/2}R^k+\Gamma`$, respectively $`CMR^k+\Gamma`$, with $`C=C(n,p)`$. The
  `BetaP` area also contains the graph enhancement, integrated rates, the
  classification of the beta-$`p`$ conditions (`betaP_classification`) and
  witnesses showing which implications fail (`betaP_failures`,
  `betaP_directWitnesses`); the `Examples` area contains the underlying
  constructions.

## How the Lean encoding differs from paper conventions

- **Measures.** Measures are nonnegative (mathlib `Measure`). "Locally Radon" is `IsFiniteMeasureOnCompacts μ` together with `μ.InnerRegular`; total mass may be infinite.
- **Values in $`[0,\infty]`$.** Beta numbers, energies, densities and Hausdorff measures take values in `ℝ≥0∞`. A statement that an energy is finite is the condition `< ⊤`. Real parameters ($`M`$, $`\Gamma`$, constants) are converted with `ENNReal.ofReal`.
- **No division by ball mass.** The beta number is normalized by $`r^{-k-2}`$ (and $`r^{-k-p}`$), never by $`\mu(P(z,r))`$. All energies are computed from the *whole* source measure; restricting the points at which one tests never changes the source. In the threshold statements the exceptional set is defined with the energy of the original $`\mu`$, before any restriction.
- **Endpoint conventions.** The scale endpoint of a square energy is written $`R`$ (or $`a`$), since $`T`$ names the family. For $`R\le0`$ the energy is zero. Beta numbers are $`0`$ for $`r\le0`$.
- **Empty families.** The infimum over an empty family is $`+\infty`$, so for an empty family $`\beta=\infty`$ at every positive radius and every positive-endpoint energy is $`\infty`$, even for the zero measure. Statements therefore carry the hypothesis `Nonempty (Models n k T)`; for the mixed family it holds automatically when $`1\le k\le n+2`$.
- **Graph covers.** Graph families are indexed by subsets of $`\mathbb N`$ so that finite and empty families need no padding. Horizontal graphs have arbitrary partial domains, may be disconnected, and carry no extension of the time function. Covers are modulo $`\mathcal H_P^k`$ *outer* measure: graph images need not be Borel. The Hausdorff-null exceptional sets may carry source mass.
- **Rectifiable measures.** `IsRegularlyRectifiableMeasure` allows each graph its own finite slope or norm and requires no local finiteness. Refinement to every positive tolerance is a conclusion of the theorems, not part of the definition.
- **Half-time derivative.** $`|D_t|^{1/2}`$ is defined through its Fourier symbol on Schwartz tests, with values in $`L^2`$. That a function $`g`$ is the half-time derivative of $`G`$ is a distributional identity, tested against real smooth compactly supported functions, one normal component at a time. The parabolic BMO seminorm uses intrinsic parabolic balls of positive radius on the vertical base and requires local integrability.
- **Retained pieces.** In the rectifiable Reifenberg theorem the retained pieces are restrictions of $`\mu`$ to Borel sets, and the compactness and covers concern the *actual topological supports* of the restrictions. The remainder includes all mass outside the unit ball; the bound concerns its mass inside it. The beta-$`p`$ theorem instead gives a decomposition into nonnegative measures that are not asserted to be restrictions.
- **Quantifier order.** Constants are chosen first: $`C=C(n)`$ (or $`C(n,p)`$, or $`L_0,C`$ depending on $`(n,k,A)`$) before $`k`$, the measure, the thresholds and every graph tolerance. Retained sets are fixed before the tolerances.
- **Absolute continuity.** The threshold decomposition does not assert absolute continuity of the source. Absolute continuity with respect to $`\mathcal H_P^k`$ is part of the definitions of regular rectifiability and of quantitative rectifiability, and a bare covering does not supply it.
- **Mixed and fixed families.** `T = mixed` means one family of each type with a common null remainder; fixed-family statements use only that type and its graph class and force the other retained measure and support to be zero.
