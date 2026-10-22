# Checked results

Every result below (104 in all) is proved in the library, and its statement is restated with a `sorry` proof in [`verification/Spec`](../verification/Spec.lean). Comparator also checks 18 auxiliary statements (monotonicity and measurability lemmas, and facts the definitions need); [`comparator.json`](../comparator.json) lists all of them. `lake comparator` checks that the library proves exactly each of these statements, using only the axioms `propext`, `Classical.choice` and `Quot.sound` (see [verification/README.md](../verification/README.md)).

Names are relative to the namespace `ParabolicRectifiability`. The first column links to the proof, the last to the statement in the specification. The main theorems are explained in detail at the start of the section of each main result.


## Conventions

- `Space n` is $\mathbb R^n\times\mathbb R$ with the parabolic metric; `n` is a natural number with `1 ≤ n`.
- `k` is a natural number with `1 ≤ k ≤ n + 2`. The family `T : FamilyKind` is `horizontal`, `vertical` or `mixed`; "available" means `Nonempty (Models n k T)`.
- "Locally Radon" is `IsFiniteMeasureOnCompacts μ` together with `μ.InnerRegular`. Measures are nonnegative.
- A superscript on the square energy is its scale endpoint, never an exponent: $S^R_{\mu,T}(z)=\int_0^R\beta^2_{\mu,T}(z,r)\,dr/r$, so $S^2$ is the energy with endpoint $2$.
- Real parameters `M, Γ` are compared with measures through `ENNReal.ofReal`.
- Constants such as `C` are existentially quantified before everything else except `n` (and `p` or `A` where stated), so they do not depend on `k`, `μ`, `M`, `Γ` or any graph tolerance unless stated.

## 1. The parabolic rectifiable Reifenberg theorem


Shared vocabulary.

- [`RetainedSets n`](../ParabolicRectifiability/Specifications/Rectifiability.lean#L30): two disjoint Borel subsets `horizontal`, `vertical` of the open ball `Metric.ball (point 0 0) 1`.
- For a source `μ` and `D : RetainedSets n`, the horizontal and vertical measures are the restrictions of `μ` to the two sets; the remainder is the restriction of `μ` to the complement of their union (it contains all mass outside the unit ball). The supports are the actual topological supports (`Measure.support`) of the two restrictions; they need not equal the retained sets.
- [`exceptionalSet μ k M`](../ParabolicRectifiability/Measure/ScaleEnergy.lean#L117) is the set of points of the open unit ball where the mixed-family square energy [`squareEnergy μ k .mixed 2 z`](../ParabolicRectifiability/Measure/ScaleEnergy.lean#L102) (scale integral over $0<r<2$, computed from the original `μ`) exceeds `M`.
- [`HasRectifiabilityContentBounds k C K`](../ParabolicRectifiability/Specifications/Rectifiability.lean#L80), for a set `K`, bundles five bounds with one constant `C`. Local parents have arbitrary centers `q` and radii `0 < R ≤ 1`.
  1. $\mathcal H_P^k(K\cap P(q,R))\le CR^k$.
  2. A finite set in $K\cap P(q,R)$ that is $r$-separated ($0<r\le R$) has at most $C(R/r)^k$ points.
  3. The parabolic volume of the open $r$-neighbourhood of $K$ is at most $Cr^{\,n+2-k}$ for $0<r\le1$ (natural-number subtraction in the exponent).
  4. Finite families of pairwise disjoint balls $P(z_i,r_i)$ with centers in $K\cap P(q,R)$ and radii in $(0,R]$ satisfy $\sum_i r_i^k\le CR^k$.
  5. The same for countable families.
- [`IsRectifiabilityDecomposition k C M Γ μ D`](../ParabolicRectifiability/Specifications/Rectifiability.lean#L106) asserts all of the following.
  - $\mu=\mu\llcorner(D_H\cup D_V)^c+\mu\llcorner D_H+\mu\llcorner D_V$.
  - The remainder has mass at most $CM+\Gamma$ in the open unit ball.
  - The horizontal and vertical supports are compact and contained in the closed unit ball.
  - If $\neg(1\le k\le n)$ the horizontal measure is zero and its support is empty; if $\neg(2\le k\le n+2)$ the same holds for the vertical one.
  - For every $\varepsilon>0$, the horizontal support has a countable cover by horizontal graphs of slope at most $\varepsilon$, and the vertical support a countable cover by regular vertical graphs of norm at most $\varepsilon$, in each case up to an $\mathcal H_P^k$-null set (`HasHorizontalGraphCover`, `HasRegularVerticalGraphCover`).
  - The union of the two supports satisfies `HasRectifiabilityContentBounds k C`.
  - The retained sets, hence the supports, are fixed before the tolerance $\varepsilon$ is chosen.
  - Nothing is asserted about absolute continuity of the retained measures or pure unrectifiability of the remainder.

### `rectifiable_reifenberg`

Statement in the specification: [`verification/Spec/Main.lean`](../verification/Spec/Main.lean#L122).


Proof: [Main.lean#L135](../ParabolicRectifiability/Main.lean#L135). Hypotheses displayed in the declaration.

The mixed case of item 1, stated for `n` and `hn : 1 ≤ n`. For `1 ≤ k ≤ n + 2`, locally Radon `μ`, and `M, Γ ≥ 0` with `μ(exceptionalSet μ k M) ≤ Γ`, there is `D` with `IsRectifiabilityDecomposition k C M Γ μ D`. Availability of the mixed family for `1 ≤ k ≤ n + 2` is proved inside (`AdmissibleModel.nonempty_of_range`).

Remarks. The retained measures are restrictions of the original source. The Hausdorff-null exceptional sets in the graph covers may carry source mass.

### `family_rectifiable_reifenberg`

Statement in the specification: [`verification/Spec/Main.lean`](../verification/Spec/Main.lean#L102).


Proof: [Main.lean#L88](../ParabolicRectifiability/Main.lean#L88). Spec: [Spec.lean](../verification/Spec.lean). Statement: written out in the declaration, concluding with [`HasFamilyDecomposition`](../ParabolicRectifiability/Decomposition/Interfaces.lean#L171).

For `n ≥ 1` there is `C > 0` such that for every `1 ≤ k ≤ n + 2`, every available family `T`, every locally Radon `μ` and all `M, Γ ≥ 0` with
`μ(P(0,1) ∩ {z : M < S^{2}_{μ,T}(z)}) ≤ Γ`
(here the energy is that of the family `T`, scale integral over $0<r<2$), there is `D : RetainedSets n` with `IsRectifiabilityDecomposition k C M Γ μ D` and, in addition, if `T = horizontal` the vertical measure is zero with empty support, and if `T = vertical` the horizontal measure is zero with empty support.

Remarks. Both `M = 0` and `Γ = 0` are allowed. No density, doubling or finite-total-mass hypothesis is imposed. The proof combines the positive-threshold, zero-threshold and ambient branches.

### `main_rectifiability`

Statement in the specification: [`verification/Spec/Main.lean`](../verification/Spec/Main.lean#L133).


Proof: [Main.lean#L151](../ParabolicRectifiability/Main.lean#L151). Statement: [`MainRectifiabilityStatement`](../ParabolicRectifiability/Specifications/Rectifiability.lean#L127).

The statement of item 2 as a closed proposition: `∀ n ≥ 1, ∃ C > 0, ∀ k, 1 ≤ k ≤ n + 2 → ∀ μ locally Radon, ∀ M Γ ≥ 0, μ(exceptionalSet μ k M) ≤ Γ → ∃ D, IsRectifiabilityDecomposition k C M Γ μ D`. The proof is `rectifiable_reifenberg` itself.

### `fixed_family_rectifiability`

Statement in the specification: [`verification/Spec/Main.lean`](../verification/Spec/Main.lean#L139).


Proof: [Main.lean#L157](../ParabolicRectifiability/Main.lean#L157). Statement: [`FixedFamilyRectifiabilityStatement T`](../ParabolicRectifiability/Specifications/Rectifiability.lean#L139), for an arbitrary `T : FamilyKind`.

For `n ≥ 1` there is `C > 0` such that for `1 ≤ k ≤ n + 2` with `Nonempty (Models n k T)`, locally Radon `μ`, `M, Γ ≥ 0` and `μ(P(0,1) ∩ {M < S^2_{μ,T}}) ≤ Γ`, there is `D` with `IsRectifiabilityDecomposition k C M Γ μ D`, vertical measure and support zero when `T = horizontal`, horizontal measure and support zero when `T = vertical`.

Remarks. For `T = mixed` the two extra clauses are vacuous and the statement is item 2 with an explicit availability hypothesis. The energy hypothesis uses the energy of the chosen family only.

### `ambient_rectifiability`

Statement in the specification: [`verification/Spec/Main.lean`](../verification/Spec/Main.lean#L143).


Proof: [Main.lean#L164](../ParabolicRectifiability/Main.lean#L164). Statement: [`AmbientRectifiabilityStatement`](../ParabolicRectifiability/Specifications/Rectifiability.lean#L152).

For `n ≥ 1` there is `C > 0` such that every locally Radon `μ` admits `D` with `IsRectifiabilityDecomposition (n + 2) C 0 0 μ D` and remainder mass exactly zero in the open unit ball.

Remarks. At $k=n+2$ there is no beta hypothesis at all. The exponent $n+2-k$ in the tube bound is $0$.

### `Enhancements.scaled_rectifiable_reifenberg`

Statement in the specification: [`verification/Spec/Enhancements/Theorems/ScalingRates.lean`](../verification/Spec/Enhancements/Theorems/ScalingRates.lean#L131).


Proof: [Enhancements/Theorems/ScalingRates.lean#L18](../ParabolicRectifiability/Enhancements/Theorems/ScalingRates.lean#L18). Statement: [`ScaledRectifiableReifenbergStatement`](../ParabolicRectifiability/Enhancements/Statements/ScalingRates.lean#L73), a conjunction of [`ScalingIdentitiesStatement`](../ParabolicRectifiability/Enhancements/Statements/ScalingRates.lean#L36) and, for each `n ≥ 1`, `∃ C > 0, ScaledThresholdProperty n C` ([L59](../ParabolicRectifiability/Enhancements/Statements/ScalingRates.lean#L59)).

Scaling identities. For `n ≥ 1`, `1 ≤ k ≤ n + 2`, locally Radon `μ`, a center `a`, `R > 0` and an available family `T`, let $F(y)=a+\delta_Ry$ and $\nu=R^{-k}(F^{-1})_\#\mu$ (`rescaledSource`). Then $\beta^2_{\nu,T}(y,s)=\beta^2_{\mu,T}(Fy,Rs)$ for all $y$ and $s>0$, and $S^2_{\nu,T}(y)=S^{2R}_{\mu,T}(Fy)$ for all $y$.

Scaled decomposition. For each `n ≥ 1` there is `C > 0` such that for `1 ≤ k ≤ n + 2`, locally Radon `μ`, a center `a`, `R > 0`, an available family `T` and `M, Γ ≥ 0` with $\mu(P(a,R)\cap\{S^{2R}_{\mu,T}>M\})\le\Gamma$, there are Borel sets $E_H,E_V\subset P(a,R)$ with:

- [`IsLocalEnhancedDecomposition k T C a R μ E_H E_V`](../ParabolicRectifiability/Enhancements/Decomposition.lean#L85): disjointness; $\mu=\mu\llcorner(E_H\cup E_V)^c+\mu\llcorner E_H+\mu\llcorner E_V$; zero measure and empty support for unavailable types and (for a fixed family) for the other type; the support bounds of the actual supports at center $a$ and scale $R$ (compactness, containment in $\bar P(a,R)$, typed graph covers at every tolerance, global Hausdorff bound $CR^k$, local Hausdorff, separated-set, tube and packing bounds); and, for every $\varepsilon,\delta>0$, graph-domain covers with total charge $\le CR^k$ and local charge $\le Cs^k$ for $0<s\le R$, for the union and each typed subfamily;
- loss $\mu\llcorner(E_H\cup E_V)^c(P(a,R))\le CMR^k+\Gamma$.

Remarks. The constant is chosen before $k$, $\mu$, $a$, $R$, $T$, $M$, $\Gamma$, the tolerance and the mesh. The graph-domain covers use vertical graphs from the general regular class.

### `Enhancements.graphDomainCover_of_fixedCarrier`

Statement in the specification: [`verification/Spec/Enhancements/Theorems/GraphDomains.lean`](../verification/Spec/Enhancements/Theorems/GraphDomains.lean#L88).


Proof: [Enhancements/Theorems/GraphDomains.lean#L30](../ParabolicRectifiability/Enhancements/Theorems/GraphDomains.lean#L30). Statement: [`FixedCarrierGraphDomainStatement`](../ParabolicRectifiability/Enhancements/Statements/GraphDomains.lean#L41).

For `n ≥ 1` there is `C > 0` such that for `1 ≤ k ≤ n + 2`, a type `T` that is horizontal or vertical and available, and a compact `K` with $\mathcal H_P^k(K)<\infty$ having, for every $\eta>0$, a countable type-$T$ graph cover up to an $\mathcal H_P^k$-null set, the following holds for all $\varepsilon,\delta>0$: the carrier pair $(K,\emptyset)$ (for $T$ horizontal) or $(\emptyset,K)$ (for $T$ vertical) admits a [`GraphDomainCover n k C ε δ`](../ParabolicRectifiability/Foundations/GraphDomainCover.lean#L214). The same cover satisfies the local-growth bound: whenever $\mathcal H_P^k(K\cap P(q,s))\le As^k$ for all $q$ and $0<s\le R_*$ ($A\ge0$, $R_*>0$ quantified after the cover), its local patch charge at $(q,R)$ is at most $CAR^k$ for $0<2R\le R_*$.

A graph-domain cover consists of countably many graph maps of slope or regular norm at most $\min\{\varepsilon,1\}$, pairwise disjoint Borel traces in $K$ covering it up to an $\mathcal H_P^k$-null set, Borel trace preimages, and countably many patches centered on the traces with radii in $(0,\delta]$ covering $K$ up to a null set; the trace estimate $\sum\lambda(\text{trace preimage}\cap\Phi^{-1}(U))\le C\mathcal H_P^k(K\cap U)$ for Borel $U$; and total and local charge bounds $\sum_\alpha c_\alpha\le C\mathcal H_P^k(K)$, $\sum_{\alpha\in I(q,R)}c_\alpha\le C\mathcal H_P^k(K\cap P(q,2R))$, where $c_\alpha=\rho_\alpha^k+\lambda(B_\alpha)+\mathcal H_P^k(P_\alpha)$ for horizontal patches (with the analogous quantity for vertical ones).

Remarks. Vertical graphs here are from the general regular class (`GeneralRegularVerticalGraph`). The constant is chosen before $k$, $T$, $K$, the graph directions, $\varepsilon$ and $\delta$.

### Further results

| Result | Statement | Spec |
|---|---|---|
| [`Enhancements.density_rectifiable_reifenberg`](../ParabolicRectifiability/Enhancements/Theorems/Density.lean#L35) | **Rectifiable Reifenberg density bounds.** For each `n ≥ 1` there is `C > 0` such that, for `1 ≤ k ≤ n+2`, locally Radon `μ`, `U = P(0,1)` and real `M, Γ ≥ 0` with `μ(U ∩ {S²_{μ,A_k} > M}) ≤ Γ` (no integrated energy assumption):  * if `0 ≤ A` and `Θ_*^k(μ,·) ≤ A` `μ`-a.e. | [statement](../verification/Spec/Enhancements/Theorems/Density.lean#L137) |
| [`Enhancements.density_scaling`](../ParabolicRectifiability/Enhancements/Theorems/Density.lean#L43) | **All local scales and their exact normalization.** For each `n ≥ 1` there is `C > 0` such that, for `1 ≤ k ≤ n+2`, locally Radon `μ`, `q ∈ X`, `R > 0`, and with `F_{q,R} = P(q,R) ∩ {Θ^{k,*} ≥ a}`:  * if `𝓔_{q,R} = ∫_{P(q,R)} S^{2R}_{μ,A_k} dμ < ∞`: - for `0 ≤ A` with `Θ_*^k ≤ … | [statement](../verification/Spec/Enhancements/Theorems/Density.lean#L142) |
| [`Enhancements.density_three_parts`](../ParabolicRectifiability/Enhancements/Theorems/Density.lean#L25) | **All three density conclusions.** For each `n ≥ 1` there is `C > 0` (depending only on `n` and the fixed Hausdorff normalization, so chosen before `k`, `μ`, `A` and `a`) such that, for `1 ≤ k ≤ n+2`, locally Radon `μ`, `U = P(0,1)` and `𝓔 = ∫_U S²_{μ,A_k} dμ < … | [statement](../verification/Spec/Enhancements/Theorems/Density.lean#L133) |
| [`Enhancements.gauge_rate`](../ParabolicRectifiability/Enhancements/Theorems/ScalingRates.lean#L29) | **Gauge rate and an approximated numerical infimum.** As for the power rate, `C₀` is one constant per `n` for which the scaled threshold decomposition holds, chosen before `k`, `μ`, `a`, `R`, `Φ`, `M` and `η`. | [statement](../verification/Spec/Enhancements/Theorems/ScalingRates.lean#L140) |
| [`Enhancements.graph_enhanced_rectifiable_reifenberg`](../ParabolicRectifiability/Enhancements/Theorems/GraphDomains.lean#L37) | The rectifiable Reifenberg conclusion with graph-domain covers of its fixed actual supports at every `ε, δ > 0`. | [statement](../verification/Spec/Enhancements/Theorems/GraphDomains.lean#L95) |
| [`Enhancements.power_rate`](../ParabolicRectifiability/Enhancements/Theorems/ScalingRates.lean#L23) | **Power-energy rate, including zero energy.** Here `C₀` is the unchanged core threshold constant, independent of `q`: for each `n ≥ 1` there is one `C₀ > 0`, chosen before `k`, `μ`, `a`, `R`, `T` and `q`, for which the scaled threshold decomposition holds with constant … | [statement](../verification/Spec/Enhancements/Theorems/ScalingRates.lean#L135) |
| [`Enhancements.rectifiable_reifenberg_theorem`](../ParabolicRectifiability/Enhancements/Theorems/MainTheorem.lean#L23) | The rectifiable Reifenberg theorem: the mixed, available fixed-family and ambient rectifiable Reifenberg conclusions with the general regular graph class. | [statement](../verification/Spec/Enhancements/Theorems/MainTheorem.lean#L79) |
| [`Enhancements.scaled_rectifiable_reifenberg_core`](../ParabolicRectifiability/Enhancements/Theorems/ScaledCore.lean#L25) | **Scaled rectifiable Reifenberg theorem without graph-domain covers.** the scaled rectifiable Reifenberg theorem on an arbitrary parent ball `P(q,R)`, without the graph-domain clause. | [statement](../verification/Spec/Enhancements/Theorems/ScaledCore.lean#L133) |

## 2. The qualitative characterization, integral criteria and canonical decomposition

### `Characterization.qualitative_characterization`

Statement in the specification: [`verification/Spec/Characterization/Theorems/Main.lean`](../verification/Spec/Characterization/Theorems/Main.lean#L140).


Proof: [Characterization/Theorems/Main.lean#L31](../ParabolicRectifiability/Characterization/Theorems/Main.lean#L31). Statement: [`QualitativeCharacterizationStatement`](../ParabolicRectifiability/Characterization/Statements/Main.lean#L55).

For `n ≥ 1`, `1 ≤ k ≤ n + 2`, an available family `T` and locally Radon `μ`, write $S^R=$ `squareEnergy μ k T R`, $\Theta_*,\Theta^*$ for `lowerDensity`, `upperDensity`, and `IsRegularlyRectifiableMeasure T k μ` for ($\mu\ll\mathcal H_P^k$ and $\mu$ is carried by countably many type-$T$ graphs, each of finite slope or regular norm; [definition](../ParabolicRectifiability/Foundations/Graphs.lean#L137)). Then regular rectifiability is equivalent to each of the following, once with "for one $R>0$" and once with "for every $R>0$":

- $S^R<\infty$, $\Theta^*>0$ and $\Theta_*<\infty$, $\mu$-a.e.;
- $S^R<\infty$ and $0<\Theta^*<\infty$, $\mu$-a.e.;
- $\mu\ll\mathcal H_P^k$, $\mu$ has a Borel sigma-finite $\mathcal H_P^k$ carrier, and $S^R<\infty$ $\mu$-a.e.

Moreover, rectifiability implies $0<\Theta_*\le\Theta^*<\infty$ $\mu$-a.e. and, for every $\varepsilon>0$, a cover of $\mu$ by type-$T$ graphs of slope or norm at most $\varepsilon$ (`HasTypedMeasureCover T k μ ε`). Finally, if $k=n+2$ then $S^R\equiv0$ for every $R$, point and family.

Remarks. Rectifiability here has no uniform graph bound; the refinement to every positive tolerance is a conclusion. The ambient endpoint is included.

### `IntegralCanonical.integral_criterion`

Statement in the specification: [`verification/Spec/IntegralCanonical/Theorems/Integral.lean`](../verification/Spec/IntegralCanonical/Theorems/Integral.lean#L155).


Proof: [IntegralCanonical/Theorems/Integral.lean#L36](../ParabolicRectifiability/IntegralCanonical/Theorems/Integral.lean#L36). Statement: [`IntegralCriterionStatement`](../ParabolicRectifiability/IntegralCanonical/Statements/Integral.lean#L70).

Setting as in item 6 (`n ≥ 1`, `1 ≤ k ≤ n + 2`, locally Radon `μ`, available `T`). Let `i ∈ Fin 3` index a structural condition ([`StructuralCondition`](../ParabolicRectifiability/IntegralCanonical/Defs.lean#L87)) and `j ∈ Fin 5` an integral test ([`IntegralTest`](../ParabolicRectifiability/IntegralCanonical/Defs.lean#L162)):

- (a) $\Theta^*>0$ and $\Theta_*<\infty$ a.e.; (b) $0<\Theta^*<\infty$ a.e.; (c) $\mu$ is an intrinsic source;
- (1) capped tail: $\int_A\min\{1,S^\rho\}\,d\mu\to0$ as $\rho\downarrow0$; (2) capped value: $L^{-1}\int_A\min\{S^R,L\}\,d\mu\to0$ as $L\to\infty$; (3) compact exhaustion: increasing compact $K_j$ exhausting $\mu$-almost all space with $\int_{K_j}S^R\,d\mu<\infty$; (4) positive weight: a Borel $w:X\to(0,1]$ with $\int_A wS^R\,d\mu<\infty$; (5) adaptive gauge: for each $A$ a continuous nondecreasing concave unbounded $\Phi$ with $\Phi(0)=0$ and $\int_A\Phi(S^R)\,d\mu<\infty$.

Here $A$ ranges over bounded cylinders (open balls of positive real radius) in tests (1), (2), (4), (5). For every pair $(i,j)$ the statement asserts:

- for every $R>0$, $\mu$ is regularly type-$T$ rectifiable if and only if condition $i$ holds and test $j$ holds at endpoint $R$ on all bounded cylinders;
- equivalently, if and only if condition $i$ holds and test $j$ holds at every $R>0$;
- for the tests other than (3), that is (1), (2), (4), (5), testing on the balls $P(0,m)$, $m\ge1$, only, suffices;
- condition $i$ with test $j$ implies $0<\Theta_*\le\Theta^*<\infty$ a.e. and typed graph covers at every positive tolerance.

Remarks. The compact exhaustion test restricts the testing points; the energy source remains $\mu$. In the Lean encoding the index `j = 2` is test (3).

### `IntegralCanonical.canonical_decomposition`

Statement in the specification: [`verification/Spec/IntegralCanonical/Theorems/Canonical.lean`](../verification/Spec/IntegralCanonical/Theorems/Canonical.lean#L149).


Proof: [IntegralCanonical/Theorems/Canonical.lean#L44](../ParabolicRectifiability/IntegralCanonical/Theorems/Canonical.lean#L44). Statement: [`CanonicalDecompositionStatement`](../ParabolicRectifiability/IntegralCanonical/Statements/Canonical.lean#L97); conclusion: [`IsCanonicalDecomposition`](../ParabolicRectifiability/IntegralCanonical/Statements/Canonical.lean#L51).

Hypotheses: `n ≥ 1`, `1 ≤ k ≤ n + 2`, `μ` locally Radon, and either `IsIntrinsicSource k μ` ($\mu\ll\mathcal H_P^k$ with a Borel sigma-finite $\mathcal H_P^k$ carrier) or $0<\Theta^{k,*}<\infty$ $\mu$-a.e.; and any $R>0$. Let $E_T=\{S^R_{\mu,T}<\infty\}$ for $T=H,V,\text{mixed}$ (energies of the full original $\mu$), $E_+=E_{\rm mixed}^c$, and $\mu_H,\mu_V,\mu_+$ the restrictions of $\mu$ to $E_H,E_V,E_+$. Conclusions:

- the three sets are measurable; $\mu(E_H\cap E_V)=0$ and $\mu(E_{\rm mixed}\setminus(E_H\cup E_V))=0$;
- each of $\mu_H,\mu_V,\mu_+$ is locally Radon, $\mu=\mu_H+\mu_V+\mu_+$, and the three are pairwise mutually singular;
- $\mu_H$ is regularly horizontally rectifiable and $\mu_V$ regularly vertically rectifiable, with covers at every tolerance $\varepsilon>0$;
- $\mu_+$ is graph pure: zero outer measure on every horizontal graph of finite slope and every full regular vertical graph of finite norm, hence on countable unions of such;
- uniqueness: any nonnegative decomposition $\mu=\rho_H+\rho_V+\rho_P$ into a horizontally rectifiable, a regularly vertically rectifiable and a graph-pure measure has $(\rho_H,\rho_V,\rho_P)=(\mu_H,\mu_V,\mu_+)$ (mutual singularity of the competitor is not assumed);
- the three measures do not depend on the positive endpoint $R$.

Remarks. The finite-energy sets $E_H,E_V$ may literally overlap; only their $\mu$-measure of intersection vanishes. At $k=n+2$ the library's guards theorem (`canonical_guards`) gives $(\mu_H,\mu_V,\mu_+)=(0,\mu,0)$ under the source-class assumption.

### Further results

| Result | Statement | Spec |
|---|---|---|
| [`Characterization.adrGoodSet_restrict_le`](../ParabolicRectifiability/Characterization/Theorems/SourceTransfer.lean#L47) | **Good-set domination.** On the good set `G_A` of a global ADR reference `σ`, the restricted source satisfies `ν⌊G_A ≤ (5^k/c) A σ`. | [statement](../verification/Spec/Characterization/Theorems/SourceTransfer.lean#L58) |
| [`Characterization.exists_bad_region_replacement`](../ParabolicRectifiability/Characterization/Theorems/SourceTransfer.lean#L53) | **Bad-region replacement.** Disjoint Whitney balls in the bad region with exact Borel allocation of its source mass, the bad-mass bound, the piece bound, and domination of the replaced source with total-mass preservation. | [statement](../verification/Spec/Characterization/Theorems/SourceTransfer.lean#L64) |
| [`Characterization.exists_typed_refinement_measure`](../ParabolicRectifiability/Characterization/Theorems/Branches.lean#L64) | **Typed refinement, measure version.** A locally Radon regularly rectifiable measure splits once into disjoint Borel horizontal and vertical source pieces whose restrictions are carried by graphs of their own type at every positive tolerance, with finite own-type … | [statement](../verification/Spec/Characterization/Theorems/Branches.lean#L173) |
| [`Characterization.exists_typed_refinement_set`](../ParabolicRectifiability/Characterization/Theorems/Branches.lean#L57) | **Typed refinement, set version.** A Borel set of finite `H_P^k` measure with finite mixed square energy splits once into disjoint Borel horizontal and vertical pieces, each covered by graphs of its own type at every positive tolerance and with finite own-type … | [statement](../verification/Spec/Characterization/Theorems/Branches.lean#L166) |
| [`Characterization.fivefold_selection`](../ParabolicRectifiability/Characterization/Theorems/SourceTransfer.lean#L28) | **Fivefold selection.** A family of open balls with positive, uniformly bounded radii in a separable metric space has a countable pairwise disjoint subfamily whose fivefold dilates contain all original centres. | [statement](../verification/Spec/Characterization/Theorems/SourceTransfer.lean#L39) |
| [`Characterization.hasTypedMeasureCover_of_intrinsic`](../ParabolicRectifiability/Characterization/Theorems/Branches.lean#L35) | **Intrinsic sufficiency.** A locally Radon `μ ≪ H_P^k` with a Borel sigma-finite `H_P^k` carrier and finite square energy `μ`-a.e. | [statement](../verification/Spec/Characterization/Theorems/Branches.lean#L144) |
| [`Characterization.hausdorffP_graph_squareEnergy_eq_top_eq_zero`](../ParabolicRectifiability/Characterization/Theorems/Branches.lean#L43) | An arbitrary locally Radon ambient source has finite own-type square energy `H_P^k`-almost everywhere on each individual finite-norm graph, for every positive endpoint. | [statement](../verification/Spec/Characterization/Theorems/Branches.lean#L152) |
| [`Characterization.isRegularlyRectifiableSet_of_finite_hausdorff`](../ParabolicRectifiability/Characterization/Theorems/Branches.lean#L29) | For Borel `E` of finite `H_P^k` measure, square finiteness for the restricted source `η = H_P^k⌊E` at one positive endpoint implies typed set rectifiability at every positive tolerance. | [statement](../verification/Spec/Characterization/Theorems/Branches.lean#L138) |
| [`Characterization.radon_continuous_approximation`](../ParabolicRectifiability/Characterization/Theorems/SourceTransfer.lean#L35) | Continuous compactly supported ambient functions are dense in `L¹` for a locally Radon source on a closed isometrically embedded subspace, and for each Borel restriction. | [statement](../verification/Spec/Characterization/Theorems/SourceTransfer.lean#L46) |
| [`Characterization.regularlyRectifiableMeasure_necessity`](../ParabolicRectifiability/Characterization/Theorems/Branches.lean#L50) | A locally Radon regularly rectifiable measure has a Borel sigma-finite Hausdorff carrier, positive finite lower and upper densities, and finite full-source mixed and own-family energies. | [statement](../verification/Spec/Characterization/Theorems/Branches.lean#L159) |
| [`Characterization.squareEnergy_lt_top_of_adr_carrier`](../ParabolicRectifiability/Characterization/Theorems/SourceTransfer.lean#L60) | If an ADR reference source has finite own-family square energy at endpoint `1` almost everywhere, then every finite ambient source has finite square energy there at reference-almost every carrier point. | [statement](../verification/Spec/Characterization/Theorems/SourceTransfer.lean#L71) |
| [`Characterization.tendsto_partition_average`](../ParabolicRectifiability/Characterization/Theorems/SourceTransfer.lean#L42) | For a finite inner regular source carried by a bounded Borel set, averages of an integrable real function over exact nested countable Borel partitions converge almost everywhere when the containing-cell extended diameters tend … | [statement](../verification/Spec/Characterization/Theorems/SourceTransfer.lean#L53) |
| [`IntegralCanonical.canonical_guards`](../ParabolicRectifiability/IntegralCanonical/Theorems/Canonical.lean#L58) | Boundary cases of the canonical sets: `E_V = ∅` at `k = 1`, `E_H = ∅` at `k = n + 1`, and for intrinsic sources the ambient decomposition is `(0, μ, 0)`. | [statement](../verification/Spec/IntegralCanonical/Theorems/Canonical.lean#L163) |
| [`IntegralCanonical.integral_equivalences`](../ParabolicRectifiability/IntegralCanonical/Theorems/Integral.lean#L28) | Exact detection of the infinite-square set: on a bounded Borel `A`, both capped limits equal `μ(A ∩ {S¹ = ∞})`. | [statement](../verification/Spec/IntegralCanonical/Theorems/Integral.lean#L147) |
| [`IntegralCanonical.isIntrinsicSource_of_upperDensity`](../ParabolicRectifiability/IntegralCanonical/Theorems/Canonical.lean#L36) | Positive finite upper `k`-density almost everywhere implies `μ ≪ H_P^k` and a Borel sigma-finite `H_P^k` carrier for a locally Radon source in `1 ≤ k ≤ n + 2`. | [statement](../verification/Spec/IntegralCanonical/Theorems/Canonical.lean#L141) |
| [`IntegralCanonical.type_separation`](../ParabolicRectifiability/IntegralCanonical/Theorems/Canonical.lean#L51) | For `2 ≤ k ≤ n`, an ordinary vertical graph of Lipschitz bound `L` and a horizontal graph of slope `ε ≤ 1` with `L ε ≤ 1/2` have `H_P^k`-null intersection. | [statement](../verification/Spec/IntegralCanonical/Theorems/Canonical.lean#L156) |

## 3. The quantitative characterization

### `QuantitativeCharacterization.quantitative_characterization`

Statement in the specification: [`verification/Spec/QuantitativeCharacterization/Theorems/Characterization.lean`](../verification/Spec/QuantitativeCharacterization/Theorems/Characterization.lean#L127).


Proof: [QuantitativeCharacterization/Theorems/Characterization.lean#L24](../ParabolicRectifiability/QuantitativeCharacterization/Theorems/Characterization.lean#L24). Statement: [`QuantitativeCharacterizationStatement`](../ParabolicRectifiability/QuantitativeCharacterization/Statements/Characterization.lean#L63), with body [`MainTheoremBounds`](../ParabolicRectifiability/QuantitativeCharacterization/Statements/Characterization.lean#L39).

Fix `n ≥ 1`, `1 ≤ k ≤ n + 2` and `A ≥ 1`. Consider locally Radon `μ ≠ 0` with unbounded support that is globally $A$-Ahlfors regular ([`IsADR`](../ParabolicRectifiability/Foundations/ADR.lean#L53): $A^{-1}r^k\le\mu(P(z,r))\le Ar^k$ for every $z\in\operatorname{supp}\mu$ and every $r>0$). Let $M_\beta(\mu)=\sup_{a\in\operatorname{supp}\mu,\,R>0}R^{-k}\int_{P(a,R)}S^R_{\mu,\rm mix}\,d\mu$ ([`carlesonEnergy`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L50)).

1. There are $L_0\ge1$ and $C\ge1$, depending on $(n,k,A)$ only, such that for every such $\mu$:
   - $M_\beta(\mu)<\infty$ if and only if $\mu$ is $(K,L_0)$-quantitatively mixed rectifiable for some finite $K\ge1$ ([`IsQuantitativelyMixedRectifiable`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L205));
   - if $M_\beta(\mu)<\infty$ then $\mu$ is $(C(1+M_\beta(\mu)),L_0)$-quantitatively rectifiable;
   - $M_\beta(\mu)\le CK$ whenever $\mu$ is $(K,L_0)$-quantitatively rectifiable with $K\ge1$.
2. For every $L\ge1$ there is $C_{\rm rev}(n,k,A,L)>0$ such that on the same class, $(K,L)$-quantitative rectifiability with $K\ge1$ gives $M_\beta(\mu)\le C_{\rm rev}K$.

Here $(K,L)$-quantitative mixed rectifiability means $\mu\ll\mathcal H_P^k$ and, for every $a\in\operatorname{supp}\mu$ and $R>0$, a nonempty set of [`RegularMixedCovering k K L μ a R`](../ParabolicRectifiability/QuantitativeCharacterization/Coverings.lean#L83): a countable family of typed $L$-references (horizontal, vertical or ambient) with balls $P(a_i,R_i)\subset P(a,LR)$ centered on the support and meeting the reference carrier, root packing $\sum R_i^k\le KR^k$, local packing $\sum_{a_i\in P(b,s),R_i\le s}R_i^k\le Ks^k$, a bad set of $d\mu\,dr/r$-mass at most $KR^k$, and scale sets $\mathcal U_i$ that together with the bad set partition $(P(a,R)\cap\operatorname{supp}\mu)\times(0,R)$ modulo $d\mu\,dr/r$, with $\mathcal U_i\subset\{L^{-1}\operatorname{dist}(z,\Gamma_i)\le r<R_i\}$.

Remarks. The constants $L_0,C$ are chosen before the measure and the covering may depend on the root. Absolute continuity is part of the definition of quantitative rectifiability; a covering alone does not provide it. The Ahlfors bounds hold at every support center and every positive radius. The statement concerns the mixed family only, and all beta numbers use the whole original measure with no division by ball mass.

### Further results

| Result | Statement | Spec |
|---|---|---|
| [`QuantitativeCharacterization.ambient_endpoint`](../ParabolicRectifiability/QuantitativeCharacterization/Theorems/Approximants.lean#L34) | **The ambient case `k = n + 2`.** Exact statement: `AmbientEndpointStatement`. | [statement](../verification/Spec/QuantitativeCharacterization/Theorems/Approximants.lean#L159) |
| [`QuantitativeCharacterization.any_cover_rectifiable`](../ParabolicRectifiability/QuantitativeCharacterization/Theorems/Pieces.lean#L17) | **A measure with a quantitative covering is rectifiable.** The proof uses the reference estimates and intrinsic sufficiency. | [statement](../verification/Spec/QuantitativeCharacterization/Theorems/Pieces.lean#L146) |
| [`QuantitativeCharacterization.betaPow_carleson_comparison`](../ParabolicRectifiability/QuantitativeCharacterization/Theorems/Characterization.lean#L31) | **The beta-`p` Carleson comparison.** Obtained from the quantitative characterization by `betaPow_carleson_comparison_of_providers` applied to `BetaP.claws_holder_proof`, `BetaP.cclamp_betaPowClamping_proof` and `Foundations.f3_betaPow_two_eq_betaSq_proof`. | [statement](../verification/Spec/QuantitativeCharacterization/Theorems/Characterization.lean#L134) |
| [`QuantitativeCharacterization.beta_scaling`](../ParabolicRectifiability/QuantitativeCharacterization/Theorems/Geometry.lean#L25) | **The scaling identity.** From `betaSq_rescaledSource` at the centre `(similarity a R hR).symm z`. | [statement](../verification/Spec/QuantitativeCharacterization/Theorems/Geometry.lean#L83) |
| [`QuantitativeCharacterization.bounded_support`](../ParabolicRectifiability/QuantitativeCharacterization/Theorems/Approximants.lean#L30) | **The bounded-support case.** Exact statement: `BoundedSupportStatement`. | [statement](../verification/Spec/QuantitativeCharacterization/Theorems/Approximants.lean#L155) |
| [`QuantitativeCharacterization.countable_quantitative_pieces`](../ParabolicRectifiability/QuantitativeCharacterization/Theorems/Pieces.lean#L22) | **Countable quantitative pieces.** The proof uses typed refinement and `any_cover_rectifiable`. | [statement](../verification/Spec/QuantitativeCharacterization/Theorems/Pieces.lean#L151) |
| [`QuantitativeCharacterization.isQuantitativelyMixedRectifiable_mono`](../ParabolicRectifiability/QuantitativeCharacterization/Theorems/Geometry.lean#L34) | Increasing either quantitative constant preserves the covering property: from `1 ≤ K ≤ K′` and `1 ≤ L ≤ L′`, an `(K,L)` source is also an `(K′,L′)` source. | [statement](../verification/Spec/QuantitativeCharacterization/Theorems/Geometry.lean#L90) |
| [`QuantitativeCharacterization.measure_approximants`](../ParabolicRectifiability/QuantitativeCharacterization/Theorems/Approximants.lean#L22) | **Approximants of a covering.** Exact statement: `MeasureApproximantsStatement`. | [statement](../verification/Spec/QuantitativeCharacterization/Theorems/Approximants.lean#L147) |
| [`QuantitativeCharacterization.quantitative_common_constants`](../ParabolicRectifiability/QuantitativeCharacterization/Theorems/Approximants.lean#L40) | Common constants `L₀, C` (and `B_loc`, `C(A,k)`) of the quantitative characterization and its local, bounded-support and beta-`p` corollaries. | [statement](../verification/Spec/QuantitativeCharacterization/Theorems/Approximants.lean#L165) |
| [`QuantitativeCharacterization.uniform_local`](../ParabolicRectifiability/QuantitativeCharacterization/Theorems/Approximants.lean#L26) | **The local forward and reverse clauses.** Exact statement: `UniformLocalStatement`. | [statement](../verification/Spec/QuantitativeCharacterization/Theorems/Approximants.lean#L151) |

## 4. Beta-p theory

### `BetaP.betaP_support_theorem`

Statement in the specification: [`verification/Spec/BetaP/Theorems/Main.lean`](../verification/Spec/BetaP/Theorems/Main.lean#L141).


Proof: [BetaP/Theorems/Main.lean#L35](../ParabolicRectifiability/BetaP/Theorems/Main.lean#L35). Statement: [`BetaPSupportStatement`](../ParabolicRectifiability/BetaP/Statements/Main.lean#L79); conclusion: [`IsBetaPDecomposition`](../ParabolicRectifiability/BetaP/Statements/Main.lean#L46).

For every `n ≥ 1` and real `p > 0` there is `C = C(n,p) > 0` such that for `1 ≤ k ≤ n + 2`, every available family `T` and every locally Radon `μ`:

- Unit clause. For `M, Γ ≥ 0`: if $p\ge2$ and $\mu(P(0,1)\cap\{S_p^{2}>M\})\le\Gamma$ (energy [`energyS`](../ParabolicRectifiability/Foundations/BetaPow.lean#L61), endpoint $2$), there are measures $\mu_+,\mu_H,\mu_V$ forming an `IsBetaPDecomposition` at center $0$, radius $1$, with loss bound $CM^{p/2}+\Gamma$; if $p\le2$ and $\mu(P(0,1)\cap\{T_p^{2}>M\})\le\Gamma$ (energy [`energyT`](../ParabolicRectifiability/Foundations/BetaPow.lean#L70)), the same with loss bound $CM+\Gamma$.
- Localized clause. For every center $q$, radius $R_0>0$ and $M,\Gamma\ge0$, the same with threshold sets in $P(q,R_0)$, scale endpoint $2R_0$, and loss bounds $CM^{p/2}R_0^k+\Gamma$ (for $p\ge2$) and $CMR_0^k+\Gamma$ (for $p\le2$).
- Ambient clause. If $k=n+2$ there is an `IsBetaPDecomposition` at center $0$, radius $1$ with loss exactly $0$, with no energy hypothesis.

An `IsBetaPDecomposition k T C a R loss μ μ₊ μ_H μ_V` asserts: $\mu=\mu_++\mu_H+\mu_V$ as nonnegative measures; $\mu_+(P(a,R))\le$ `loss`; $\mu_H$ and $\mu_V$ vanish outside $P(a,R)$; $\mu_H=0$ if horizontal models are unavailable or $T$ is vertical, and $\mu_V=0$ if vertical models are unavailable or $T$ is horizontal; and the actual supports of $\mu_H,\mu_V$ satisfy [`HasRegularSupportBounds k C a R`](../ParabolicRectifiability/Foundations/SupportBounds.lean#L43).

Remarks. This is a decomposition into nonnegative measures, not into restrictions of $\mu$. The measures, hence their supports, are fixed before any graph tolerance. At $M=0$ the loss is exactly $\Gamma$. The two energies $S_p$ and $T_p$ are defined separately; $S_p$ is used for $p\ge2$ and $T_p$ for $p\le2$, the favorable exponent ranges.

### Further results

| Result | Statement | Spec |
|---|---|---|
| [`BetaP.activeRadiusPacking`](../ParabolicRectifiability/BetaP/Theorems/Main.lean#L41) | Active-radius packing for `p ≥ 2` and `1 ≤ k < n + 2`: disjoint positive-radius balls in `P(q,R)` with `0 < b_i ≤ b` and full-source tails `∫_{r_i}^∞ B_p(σ;z_i,s)^{2/p} ds/s ≤ B` satisfy `σ(X) ≤ C(n,p) (b + B^{p/2}) R^k`. | [statement](../verification/Spec/BetaP/Theorems/Main.lean#L148) |
| [`BetaP.activeRadiusPacking_exceptional`](../ParabolicRectifiability/BetaP/Theorems/Main.lean#L58) | If the all-scale tail condition holds outside a finite set of indices whose atomic weights sum to at most `Γ`, the packing bound is `σ(X) ≤ C(n,p) (b + B^{p/2}) R^k + Γ`. | [statement](../verification/Spec/BetaP/Theorems/Main.lean#L168) |
| [`BetaP.activeRadiusPacking_truncated`](../ParabolicRectifiability/BetaP/Theorems/Main.lean#L47) | The active-radius mass bound with the source at each scale replaced by `σ_s = Σ_{r_j ≤ s} b_j r_j^k δ_{z_j}`. | [statement](../verification/Spec/BetaP/Theorems/Main.lean#L155) |
| [`BetaP.activeRadiusPacking_unitParent`](../ParabolicRectifiability/BetaP/Theorems/Main.lean#L52) | For a packing in `P(q,1)`, the full atomic-source tails need only be integrated over `(r_i,2)` to obtain `σ(X) ≤ C(n,p) (b + B^{p/2})`, for `p ≥ 2` and `1 ≤ k < n + 2`. | [statement](../verification/Spec/BetaP/Theorems/Main.lean#L161) |
| [`BetaP.activeRadiusPacking_unitParent_exceptional`](../ParabolicRectifiability/BetaP/Theorems/Main.lean#L63) | The unit-parent active-radius bound with tails over `(r_i,2)` required only outside indices of total weight at most `Γ`: `σ(X) ≤ C(n,p) (b + B^{p/2}) + Γ`. | [statement](../verification/Spec/BetaP/Theorems/Main.lean#L174) |
| [`BetaP.betaP_classification`](../ParabolicRectifiability/BetaP/Theorems/Corollaries.lean#L145) | The complete beta-`p` classification: the ten necessity/sufficiency entries for `k < n + 2`, the ambient endpoint, and endpoint invariance. | [statement](../verification/Spec/BetaP/Theorems/Corollaries.lean#L281) |
| [`BetaP.betaP_directWitnesses`](../ParabolicRectifiability/BetaP/Theorems/Failures.lean#L55) | The two direct Hausdorff-source witnesses and their exact constant-time transfer, assembled as `DirectWitnessesStatement`. | [statement](../verification/Spec/BetaP/Theorems/Failures.lean#L173) |
| [`BetaP.betaP_endpointInvariance`](../ParabolicRectifiability/BetaP/Theorems/Corollaries.lean#L138) | For a locally Radon source, every family, `p > 0`, and centre, finiteness of each of `S_p^a` and `T_p^a` is independent of the positive endpoint `a`. | [statement](../verification/Spec/BetaP/Theorems/Corollaries.lean#L273) |
| [`BetaP.betaP_failures`](../ParabolicRectifiability/BetaP/Theorems/Failures.lean#L82) | The three impossibility assertions outside the support ranges, assembled as `BetaPFailuresStatement`: below-two `S_p` threshold loss, above-two `T_p` threshold loss, and above-two integrated `T_p` loss, each in its specified … | [statement](../verification/Spec/BetaP/Theorems/Failures.lean#L200) |
| [`BetaP.betaP_graphEnhancement`](../ParabolicRectifiability/BetaP/Theorems/Corollaries.lean#L43) | The beta-`p` support decomposition with graph-domain cost bounds on its own supports (`BetaPGraphEnhancementStatement`). | [statement](../verification/Spec/BetaP/Theorems/Corollaries.lean#L172) |
| [`BetaP.betaP_integratedRate`](../ParabolicRectifiability/BetaP/Theorems/Corollaries.lean#L50) | Finite integrated full-source energy gives the support and graph-domain conclusions with local remainder `C R^{2k/(p+2)} ℰ^{p/(p+2)}` for `p ≥ 2`, where `ℰ = ∫_{P(q,R)} S_p^{2R} dμ`, or `C R^{k/2} 𝒯^{1/2}` for `0 < p ≤ 2`, … | [statement](../verification/Spec/BetaP/Theorems/Corollaries.lean#L180) |
| [`BetaP.betaP_integratedSharpness`](../ParabolicRectifiability/BetaP/Theorems/Corollaries.lean#L57) | The amplitude powers `p/(p+2)` for integrated `S_p`, `p ≥ 2`, and `1/2` for integrated `T_p`, `0 < p ≤ 2`, are forced for pure-power bounds uniform over all amplitudes `c > 0` of the diffuse source, when `1 ≤ k < n + 2`. | [statement](../verification/Spec/BetaP/Theorems/Corollaries.lean#L188) |
| [`BetaP.betaPow_annulus`](../ParabolicRectifiability/BetaP/Theorems/Laws.lean#L45) | For a locally Radon source, an available family and `p > 0`, both scale integrands `B_p^{2/p}` and `B_p` have finite integral over each finite annulus `(u,v)`, `0 < u < v`. | [statement](../verification/Spec/BetaP/Theorems/Laws.lean#L80) |
| [`BetaP.betaPow_clamping`](../ParabolicRectifiability/BetaP/Theorems/Laws.lean#L64) | The density-free clamping comparisons. | [statement](../verification/Spec/BetaP/Theorems/Laws.lean#L104) |
| [`BetaP.betaPow_holder`](../ParabolicRectifiability/BetaP/Theorems/Laws.lean#L61) | Hölder with the density factor. | [statement](../verification/Spec/BetaP/Theorems/Laws.lean#L100) |
| [`BetaP.betaPow_measurability`](../ParabolicRectifiability/BetaP/Theorems/Laws.lean#L37) | Borel measurability of `B_p`, `S_p^a`, `T_p^a`. | [statement](../verification/Spec/BetaP/Theorems/Laws.lean#L70) |
| [`BetaP.betaPow_rescaling`](../ParabolicRectifiability/BetaP/Theorems/Laws.lean#L53) | The dilation law for `rescaledSource`, endpoint `aR`. | [statement](../verification/Spec/BetaP/Theorems/Laws.lean#L90) |
| [`BetaP.betaPow_restriction`](../ParabolicRectifiability/BetaP/Theorems/Laws.lean#L40) | Monotonicity of `B_p` under source restriction. | [statement](../verification/Spec/BetaP/Theorems/Laws.lean#L74) |
| [`BetaP.betaPow_smul`](../ParabolicRectifiability/BetaP/Theorems/Laws.lean#L50) | Positive amplitude scaling: `B_{p,cμ} = c B_{p,μ}` for real `c > 0`, every source, family, centre, and radius. | [statement](../verification/Spec/BetaP/Theorems/Laws.lean#L86) |
| [`BetaP.betaPow_zeroSource`](../ParabolicRectifiability/BetaP/Theorems/Laws.lean#L58) | For an available family and `p > 0`, the zero source has `B_p = 0` at every radius and zero `S_p^a`, `T_p^a` at every positive endpoint. | [statement](../verification/Spec/BetaP/Theorems/Laws.lean#L96) |
| [`BetaP.classification_ambient`](../ParabolicRectifiability/BetaP/Theorems/Corollaries.lean#L131) | At `k = n + 2`, a locally Radon source with positive finite upper density is regularly rectifiable with arbitrary-positive-bound covers. | [statement](../verification/Spec/BetaP/Theorems/Corollaries.lean#L266) |
| [`BetaP.directWitness_minus`](../ParabolicRectifiability/BetaP/Theorems/Failures.lean#L41) | A compact purely one-unrectifiable planar set of Hausdorff measure `1` has positive bounded upper density and bounded finite-endpoint `S_p`, for every `0 < p < 2`. | [statement](../verification/Spec/BetaP/Theorems/Failures.lean#L159) |
| [`BetaP.directWitness_plus`](../ParabolicRectifiability/BetaP/Theorems/Failures.lean#L49) | A bounded Borel union of nondegenerate planar horizontal segments has Hausdorff measure in `[1,100/99]` and density ratio tending to `2` almost everywhere, while outside one countable set all `S_p^a` diverge simultaneously for … | [statement](../verification/Spec/BetaP/Theorems/Failures.lean#L167) |
| [`BetaP.emptyTestingBall`](../ParabolicRectifiability/BetaP/Theorems/Laws.lean#L29) | An empty testing ball gives `B_p = 0` for a nonempty family. | [statement](../verification/Spec/BetaP/Theorems/Laws.lean#L60) |
| [`BetaP.spAboveTwo_notNecessary`](../ParabolicRectifiability/BetaP/Theorems/Corollaries.lean#L95) | For each `p > 2` and `a > 0`, there is a locally Radon source in `Space 2` with positive finite upper `1`-density, regular rectifiability and covers at every positive slope, for which `S_p^a` finiteness fails on a set of … | [statement](../verification/Spec/BetaP/Theorems/Corollaries.lean#L230) |
| [`BetaP.spAboveTwo_sufficient`](../ParabolicRectifiability/BetaP/Theorems/Corollaries.lean#L89) | For `1 ≤ k < n + 2`, `p > 2`, and `a > 0`, full-source `S_p^a` finiteness almost everywhere implies regular mixed measure rectifiability with arbitrary-positive-bound covers. | [statement](../verification/Spec/BetaP/Theorems/Corollaries.lean#L223) |
| [`BetaP.spBelowTwo_necessary`](../ParabolicRectifiability/BetaP/Theorems/Corollaries.lean#L71) | For `1 ≤ k < n + 2`, regular mixed measure rectifiability implies full-source `S_p^a < ∞` almost everywhere for every fixed `0 < p < 2` and `a > 0`. | [statement](../verification/Spec/BetaP/Theorems/Corollaries.lean#L202) |
| [`BetaP.spBelowTwo_noVanishingRemainder`](../ParabolicRectifiability/BetaP/Theorems/Failures.lean#L62) | For `0 < p < 2`, no nonnegative modulus `Φ(M) → 0` as `M ↓ 0` gives a universal `S_p^2` threshold remainder bound `Φ(M) + Γ` at `n = 2`, `k = 1`, even allowing one good measure carried by a compact set covered modulo `H_P¹` by … | [statement](../verification/Spec/BetaP/Theorems/Failures.lean#L180) |
| [`BetaP.spBelowTwo_notSufficient`](../ParabolicRectifiability/BetaP/Theorems/Corollaries.lean#L64) | For each `0 < p < 2` and `a > 0`, there is a locally Radon source in `Space 2` with positive finite upper `1`-density and finite `S_p^a` almost everywhere that is not regularly rectifiable. | [statement](../verification/Spec/BetaP/Theorems/Corollaries.lean#L195) |
| [`BetaP.square_necessary`](../ParabolicRectifiability/BetaP/Theorems/Corollaries.lean#L83) | For `1 ≤ k < n + 2`, regular mixed measure rectifiability implies both `S_2^a < ∞` and `T_2^a < ∞` almost everywhere at every fixed `a > 0`. | [statement](../verification/Spec/BetaP/Theorems/Corollaries.lean#L216) |
| [`BetaP.square_sufficient`](../ParabolicRectifiability/BetaP/Theorems/Corollaries.lean#L77) | For `1 ≤ k < n + 2`, finiteness almost everywhere of either `S_2^a` or `T_2^a`, `a > 0`, implies regular mixed measure rectifiability and covers at every positive bound. | [statement](../verification/Spec/BetaP/Theorems/Corollaries.lean#L209) |
| [`BetaP.timeSlice_transfer`](../ParabolicRectifiability/BetaP/Theorems/Failures.lean#L33) | Constant-time transfer at `n = 2`, `k = 1`: every planar source has exactly the Euclidean horizontal/mixed `B_p` at every radius and `S_p^a` at every `a > 0`. | [statement](../verification/Spec/BetaP/Theorems/Failures.lean#L151) |
| [`BetaP.tpAboveTwo_necessary`](../ParabolicRectifiability/BetaP/Theorems/Corollaries.lean#L124) | For `1 ≤ k < n + 2`, regular mixed measure rectifiability implies full-source `T_p^a < ∞` almost everywhere for every fixed `p > 2` and `a > 0`. | [statement](../verification/Spec/BetaP/Theorems/Corollaries.lean#L258) |
| [`BetaP.tpAboveTwo_noIntegratedRemainder`](../ParabolicRectifiability/BetaP/Theorems/Failures.lean#L76) | For `p > 2`, no nonnegative modulus `Ψ(e) → 0` as `e ↓ 0` bounds the unit-ball remainder by `Ψ(e)` for every locally Radon source at `n = 1`, `k = 2` with finite actual energy `e = ∫_{P(0,1)} T_p^2 dμ`, even with arbitrary … | [statement](../verification/Spec/BetaP/Theorems/Failures.lean#L194) |
| [`BetaP.tpAboveTwo_noVanishingRemainder`](../ParabolicRectifiability/BetaP/Theorems/Failures.lean#L68) | For `p > 2`, no nonnegative modulus `Φ(M) → 0` as `M ↓ 0` gives a universal `T_p^2` threshold remainder bound `Φ(M) + Γ` at `n = 1`, `k = 2`, even allowing one good measure on an arbitrary countably regular carrier modulo a … | [statement](../verification/Spec/BetaP/Theorems/Failures.lean#L186) |
| [`BetaP.tpAboveTwo_notSufficient`](../ParabolicRectifiability/BetaP/Theorems/Corollaries.lean#L116) | For each `p > 2` and `a > 0`, there is a locally Radon source in `Space 1` with positive finite upper `2`-density and finite `T_p^a` almost everywhere that is not regularly rectifiable. | [statement](../verification/Spec/BetaP/Theorems/Corollaries.lean#L251) |
| [`BetaP.tpBelowTwo_notNecessary`](../ParabolicRectifiability/BetaP/Theorems/Corollaries.lean#L108) | For each `0 < p < 2` and `a > 0`, there is a locally Radon source in `Space 1` with positive finite upper `2`-density, regular rectifiability and arbitrary-positive-bound covers, for which `T_p^a` finiteness fails on a set of … | [statement](../verification/Spec/BetaP/Theorems/Corollaries.lean#L244) |
| [`BetaP.tpBelowTwo_sufficient`](../ParabolicRectifiability/BetaP/Theorems/Corollaries.lean#L102) | For `1 ≤ k < n + 2`, `0 < p < 2`, and `a > 0`, full-source `T_p^a` finiteness almost everywhere implies regular mixed measure rectifiability with covers at every positive bound. | [statement](../verification/Spec/BetaP/Theorems/Corollaries.lean#L237) |
| [`BetaP.unavailableFamily`](../ParabolicRectifiability/BetaP/Theorems/Laws.lean#L34) | For an unavailable family and `p > 0`, `B_p = ⊤` at every positive radius and `S_p^a = T_p^a = ⊤` at every positive endpoint, for every source. | [statement](../verification/Spec/BetaP/Theorems/Laws.lean#L66) |

## 5. Examples and counterexamples



| Result | Statement | Spec |
|---|---|---|
| [`Examples.dense_atoms_density_support`](../ParabolicRectifiability/Examples/Theorems/DensityExamples.lean#L27) | For `1 ≤ k < n + 2`, distinct points dense in `D = closedBall 0 (1/4)` give the finite nonzero source `denseAtomMeasure k z`. | [statement](../verification/Spec/Examples/Theorems/DensityExamples.lean#L77) |
| [`Examples.density_tests`](../ParabolicRectifiability/Examples/Theorems/DensityExamples.lean#L34) | The flat, diffuse, and atomic tests. | [statement](../verification/Spec/Examples/Theorems/DensityExamples.lean#L84) |
| [`Examples.exact_reductions`](../ParabolicRectifiability/Examples/Theorems/Reductions.lean#L25) | The exact Euclidean reductions: constant-time pushforwards preserve horizontal and mixed beta-`p` energies; | [statement](../verification/Spec/Examples/Theorems/Reductions.lean#L78) |
| [`Examples.lacunary_convergence`](../ParabolicRectifiability/Examples/Theorems/Lacunary.lean#L31) | For `0 < ε ≤ 3/16` and `IsLacunaryData a N`, the primitive series is absolutely summable at every real time and its finite partial sums converge uniformly on `ℝ` to `lacunaryFunction ε a N`. | [statement](../verification/Spec/Examples/Theorems/Lacunary.lean#L113) |
| [`Examples.lacunary_estimates`](../ParabolicRectifiability/Examples/Theorems/Lacunary.lean#L41) | The lacunary graph estimates: isometry for `√\|t-s\|`, exact ball and Hausdorff identities, density and ADR statements, all-scale upper `T_q` bounds for `q ≥ 1`, and restriction-stable lower bounds for `q > 0`. | [statement](../verification/Spec/Examples/Theorems/Lacunary.lean#L123) |
| [`Examples.lacunary_exponent_witnesses`](../ParabolicRectifiability/Examples/Theorems/Lacunary.lean#L58) | Complementary `T_p` witnesses. | [statement](../verification/Spec/Examples/Theorems/Lacunary.lean#L140) |
| [`Examples.lacunary_nonregular`](../ParabolicRectifiability/Examples/Theorems/Lacunary.lean#L49) | For `a_j = (j+1)^{-1/2}`, the compact lacunary graph has positive finite `H_P²` measure and ordinary graph covers at every positive slope, but its source is null on every finite-norm general regular vertical graph and is not … | [statement](../verification/Spec/Examples/Theorems/Lacunary.lean#L131) |

## 6. Supporting results



| Result | Statement | Spec |
|---|---|---|
| [`Foundations.absolutelyContinuous_of_lowerDensity_squareEnergy`](../ParabolicRectifiability/Foundations/Theorems/DensityBridges.lean#L34) | The absolute-continuity bridge. | [statement](../verification/Spec/Foundations/Theorems/DensityBridges.lean#L138) |
| [`Foundations.ambient_absolutely_continuous_density`](../ParabolicRectifiability/Foundations/Theorems/Ambient.lean#L58) | Fourth clause: a locally Radon `μ ≪ L^{n+1}` has positive finite lower and upper `(n + 2)`-densities `μ`-almost everywhere. | [statement](../verification/Spec/Foundations/Theorems/Ambient.lean#L127) |
| [`Foundations.ambient_characterization`](../ParabolicRectifiability/Foundations/Theorems/Ambient.lean#L52) | Third clause: for locally Radon `μ`, regular `(n + 2)`-rectifiability (mixed or vertical) `↔ μ ≪ H_P^{n+2}` `↔` `0 < Θ^{n+2,*} < ∞` `μ`-almost everywhere. | [statement](../verification/Spec/Foundations/Theorems/Ambient.lean#L121) |
| [`Foundations.ambient_energy_zero`](../ParabolicRectifiability/Foundations/Theorems/Ambient.lean#L32) | First clause: at `k = n + 2` every available natural beta and square function of a locally Radon source vanishes identically. | [statement](../verification/Spec/Foundations/Theorems/Ambient.lean#L101) |
| [`Foundations.ambient_energy_zero_arbitrary_source`](../ParabolicRectifiability/Foundations/Theorems/Ambient.lean#L38) | Generalization of the first clause to an arbitrary measure: at `k = n + 2` every available natural beta and square function vanishes identically. | [statement](../verification/Spec/Foundations/Theorems/Ambient.lean#L107) |
| [`Foundations.ambient_local_core`](../ParabolicRectifiability/Foundations/Theorems/Ambient.lean#L66) | Fifth clause: for a locally Radon `μ` and every `P(q,R)`, the decomposition `μ = μ⌊P(q,R)ᶜ + μ⌊P(q,R)` has zero remainder on `P(q,R)`, and `supp(μ⌊P(q,R))` satisfies the regular support bounds at `n + 2`, with one dimensional … | [statement](../verification/Spec/Foundations/Theorems/Ambient.lean#L135) |
| [`Foundations.ambient_zero_graph_cover`](../ParabolicRectifiability/Foundations/Theorems/Ambient.lean#L46) | Second clause: the zero-function full regular graph is all of `X` at every positive tolerance, and every set is regularly `(n + 2)`-rectifiable of vertical and of mixed type. | [statement](../verification/Spec/Foundations/Theorems/Ambient.lean#L115) |
| [`Foundations.hasGeneralRegularVerticalGraphCover_of_hasRegularVerticalGraphCover`](../ParabolicRectifiability/Foundations/Theorems/CompactBridge.lean#L49) | Cover inclusion without loss of tolerance. | [statement](../verification/Spec/Foundations/Theorems/CompactBridge.lean#L46) |
| [`Foundations.hausdorffP_le_of_upperDensity`](../ParabolicRectifiability/Foundations/Theorems/DensityBridges.lean#L29) | Positive upper density gives Hausdorff domination. | [statement](../verification/Spec/Foundations/Theorems/DensityBridges.lean#L133) |
| [`Foundations.isGeneralRegularVerticalFunction_of_isRegularVerticalFunction`](../ParabolicRectifiability/Foundations/Theorems/CompactBridge.lean#L38) | Function inclusion at the same tolerance. | [statement](../verification/Spec/Foundations/Theorems/CompactBridge.lean#L39) |
| [`Foundations.packing_mass_bound`](../ParabolicRectifiability/Foundations/Theorems/DensityBridges.lean#L24) | Packing turns lower density into retained mass. | [statement](../verification/Spec/Foundations/Theorems/DensityBridges.lean#L128) |
| [`Foundations.representsGeneralHalfTimeDerivative_of_compactPerturbation`](../ParabolicRectifiability/Foundations/Theorems/CompactBridge.lean#L31) | Representative identification for the compact bridge. | [statement](../verification/Spec/Foundations/Theorems/CompactBridge.lean#L32) |
