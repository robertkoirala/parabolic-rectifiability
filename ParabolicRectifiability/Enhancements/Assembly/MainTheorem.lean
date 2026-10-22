import ParabolicRectifiability.Main
import ParabolicRectifiability.Enhancements.Statements.MainTheorem
import ParabolicRectifiability.Foundations.Statements.CompactBridge
import ParabolicRectifiability.Enhancements.Assembly.IntermediateStatements

/-! # Assembly of the parabolic rectifiable Reifenberg theorem

The main theorem is

`rectifiable_reifenberg_theorem_of_providers : CompactBridgeCoverStatement → RectifiableReifenbergTheoremStatement`.

Proof assembly:

* the theorems `family_rectifiable_reifenberg` (mixed and
  fixed-family clauses) and `ambient_retained_decomposition` (ambient clause) give actual
  retained sets with all their conclusions;
* these fields are projected onto `IsRectifiableReifenbergDecomposition`; the only
  non-identity steps are the vertical covers, transported to the general regular class by
  the statement `CompactBridgeCoverStatement` (hypothesis), and the new global
  bound `H_P^k(K) ≤ C`, supplied by `exists_hausdorffP_le_of_local_bound`
  from the local Hausdorff field;
* one constant: `C = (C_f + C_a)(1 + N)`, where `C_f`, `C_a` are the constants of the two
  decomposition theorems and `N` the covering number of `exists_hausdorffP_le_of_local_bound`;
  the `mono_constant` lemmas keep the coefficient one on `Γ`.

The field adapter between `IsRectifiabilityDecomposition` and `HasRegularSupportBounds` at
`(0,1)` is `rectifiableReifenbergDecomposition_of_rectifiabilityDecomposition`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Enhancements

open ParabolicRectifiability.Foundations

/-- Increasing the constant preserves the support bundle at a nonnegative scale. -/
theorem supportBounds_mono_constant {n k : ℕ} {C C' : ℝ} {a : Space n} {R : ℝ}
    {KH KV : Set (Space n)} (h : HasRegularSupportBounds k C a R KH KV) (hC : C ≤ C')
    (hR : 0 ≤ R) : HasRegularSupportBounds k C' a R KH KV where
  horizontal_compact := h.horizontal_compact
  vertical_compact := h.vertical_compact
  horizontal_subset := h.horizontal_subset
  vertical_subset := h.vertical_subset
  horizontal_unavailable := h.horizontal_unavailable
  vertical_unavailable := h.vertical_unavailable
  horizontal_graphs := h.horizontal_graphs
  vertical_graphs := h.vertical_graphs
  hausdorff_total := h.hausdorff_total.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hC (pow_nonneg hR _)))
  hausdorff_local := fun q s hs hsR => (h.hausdorff_local q s hs hsR).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC (pow_nonneg hs.le _)))
  separated := fun q s r hs hsR hr hrs F hF hsep =>
    (h.separated q s r hs hsR hr hrs F hF hsep).trans
      (mul_le_mul_of_nonneg_right hC (pow_nonneg (div_nonneg hs.le hr.le) _))
  minkowski := fun r hr hrR => (h.minkowski r hr hrR).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (pow_nonneg hR _))
      (pow_nonneg hr.le _)))
  finite_packing := fun q s hs hsR l z r hz hr hdisj =>
    (h.finite_packing q s hs hsR l z r hz hr hdisj).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC (pow_nonneg hs.le _)))
  countable_packing := fun q s hs hsR I z r hz hr hdisj =>
    (h.countable_packing q s hs hsR I z r hz hr hdisj).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC (pow_nonneg hs.le _)))

/-- Increasing the constant preserves every conclusion of the parabolic rectifiable Reifenberg theorem for the same
retained sets; the coefficient of `Γ` stays one. -/
theorem rectifiableReifenbergDecomposition_mono_constant {n k : ℕ} {C C' M Γ : ℝ}
    {μ : Measure (Space n)} {D : RetainedSets n}
    (h : IsRectifiableReifenbergDecomposition k C M Γ μ D) (hC : C ≤ C') (hM : 0 ≤ M) :
    IsRectifiableReifenbergDecomposition k C' M Γ μ D where
  measure_eq := h.measure_eq
  remainder_bound := h.remainder_bound.trans (ENNReal.ofReal_le_ofReal
    (by have := mul_le_mul_of_nonneg_right hC hM; linarith))
  horizontal_unavailable := h.horizontal_unavailable
  vertical_unavailable := h.vertical_unavailable
  supports := supportBounds_mono_constant h.supports hC zero_le_one

/-- Field adapter: the decomposition, the compact-to-general cover bridge and a
global Hausdorff bound give every conclusion of the parabolic rectifiable Reifenberg theorem for the same
retained sets. -/
theorem rectifiableReifenbergDecomposition_of_rectifiabilityDecomposition
    (hbridge : CompactBridgeCoverStatement) {n k : ℕ} {C M Γ : ℝ} {μ : Measure (Space n)}
    {D : RetainedSets n} (hD : IsRectifiabilityDecomposition k C M Γ μ D)
    (hglobal : hausdorffP n k (D.supportUnion μ) ≤ ENNReal.ofReal C) :
    IsRectifiableReifenbergDecomposition k C M Γ μ D where
  measure_eq := hD.measure_eq
  remainder_bound := hD.remainder_bound
  horizontal_unavailable := hD.horizontal_unavailable
  vertical_unavailable := hD.vertical_unavailable
  supports :=
    { horizontal_compact := hD.horizontal_compact
      vertical_compact := hD.vertical_compact
      horizontal_subset := hD.horizontal_in_unit
      vertical_subset := hD.vertical_in_unit
      horizontal_unavailable := fun h => (hD.horizontal_unavailable h).2
      vertical_unavailable := fun h => (hD.vertical_unavailable h).2
      horizontal_graphs := hD.horizontal_graphs
      vertical_graphs := fun ε hε => hbridge n k _ ε (hD.vertical_graphs ε hε)
      hausdorff_total := by rw [one_pow, mul_one]; exact hglobal
      hausdorff_local := hD.content.hausdorff
      separated := hD.content.separated
      minkowski := fun r hr hr1 => by
        rw [one_pow, mul_one]; exact hD.content.minkowski r hr hr1
      finite_packing := hD.content.finite_packing
      countable_packing := hD.content.countable_packing }

/-- One output of the decomposition theorems with constant `C₁ ≤ C₀` becomes an output of the parabolic rectifiable Reifenberg theorem
with the final constant `C₀ (1 + N)`, using `exists_hausdorffP_le_of_local_bound` for
the global Hausdorff bound. -/
theorem rectifiableReifenbergDecomposition_of_frozen (hbridge : CompactBridgeCoverStatement)
    {n k : ℕ} {N C₀ C₁ M Γ : ℝ} (hN : 0 < N) (hC₀ : 0 ≤ C₀)
    (hglob : ∀ (k : ℕ) (C : ℝ) (K : Set (Space n)),
      K ⊆ Metric.closedBall (point 0 0) 1 →
      (∀ (q : Space n) (R : ℝ), 0 < R → R ≤ 1 →
        hausdorffP n k (K ∩ Metric.ball q R) ≤ ENNReal.ofReal (C * R ^ k)) →
      hausdorffP n k K ≤ ENNReal.ofReal (N * C))
    {μ : Measure (Space n)} {D : RetainedSets n}
    (hD : IsRectifiabilityDecomposition k C₁ M Γ μ D) (h₁ : C₁ ≤ C₀) (hM : 0 ≤ M) :
    IsRectifiableReifenbergDecomposition k (C₀ * (1 + N)) M Γ μ D := by
  have hD₀ := hD.mono_constant h₁ hM
  have hC₀N : C₀ ≤ C₀ * (1 + N) := by nlinarith
  apply rectifiableReifenbergDecomposition_of_rectifiabilityDecomposition hbridge
    (hD₀.mono_constant hC₀N hM)
  have hsub : D.supportUnion μ ⊆ Metric.closedBall (point 0 0) 1 :=
    union_subset hD.horizontal_in_unit hD.vertical_in_unit
  refine (hglob k C₀ _ hsub hD₀.content.hausdorff).trans (ENNReal.ofReal_le_ofReal ?_)
  nlinarith

/-- **The parabolic rectifiable Reifenberg theorem.**

Inputs: the theorems `family_rectifiable_reifenberg` and
`ambient_retained_decomposition` and the `mono_constant` lemmas; the statement
`CompactBridgeCoverStatement` as a hypothesis (implication form); and
`exists_hausdorffP_le_of_local_bound`. -/
theorem rectifiable_reifenberg_theorem_of_providers (hbridge : CompactBridgeCoverStatement) :
    RectifiableReifenbergTheoremStatement := by
  intro n hn
  obtain ⟨Cf, hCf, hfam⟩ := family_rectifiable_reifenberg n hn
  obtain ⟨Ca, hCa, hamb⟩ := ambient_retained_decomposition n hn
  obtain ⟨N, hN, hglob⟩ := exists_hausdorffP_le_of_local_bound n
  have hC₀ : 0 ≤ Cf + Ca := by linarith
  refine ⟨(Cf + Ca) * (1 + N), mul_pos (by linarith) (by linarith), ?_, ?_, ?_⟩
  · intro k hk hkn μ hμ hreg M Γ hM hΓ hbad
    obtain ⟨D, hD, -, -⟩ := hfam k hk hkn .mixed (AdmissibleModel.nonempty_of_range hn hk hkn)
      μ hμ hreg M Γ hM hΓ hbad
    exact ⟨D, rectifiableReifenbergDecomposition_of_frozen hbridge hN hC₀ hglob hD (by linarith) hM⟩
  · intro k hk hkn T _ hT μ hμ hreg M Γ hM hΓ hbad
    obtain ⟨D, hD, hH, hV⟩ := hfam k hk hkn T hT μ hμ hreg M Γ hM hΓ hbad
    exact ⟨D, rectifiableReifenbergDecomposition_of_frozen hbridge hN hC₀ hglob hD (by linarith) hM,
      hH, hV⟩
  · intro μ hμ hreg
    obtain ⟨hD, hrem⟩ := hamb μ hμ hreg
    exact ⟨ambientRetainedSets n,
      rectifiableReifenbergDecomposition_of_frozen hbridge hN hC₀ hglob hD (by linarith) le_rfl, hrem⟩

end ParabolicRectifiability.Enhancements
