import ParabolicRectifiability.Main
import ParabolicRectifiability.Enhancements.Statements.MainTheorem
import ParabolicRectifiability.Foundations.Statements.CompactBridge
import ParabolicRectifiability.Enhancements.Proofs.ElementaryBounds
import ParabolicRectifiability.Foundations.Proofs.CompactBridge

/-! # Composition of the parabolic rectifiable Reifenberg theorem

This module assembles the parabolic rectifiable Reifenberg theorem from the
rectifiability decomposition (`IsRectifiabilityDecomposition`), the compact-to-general bridge for regular
vertical graphs, and the passage from local to global Hausdorff bounds.

* `compactBridgeFunction_proof` and `compactBridgeCover_proof` derive the compact-bridge
  statements from `compactBridgeRepresentative_proof`: a regular vertical function with a
  compact perturbation is a regular vertical function in the general sense, at the same
  tolerance.
* `rectifiable_reifenberg_theorem_of_providers` reduces the parabolic rectifiable Reifenberg theorem to the cover bridge, using
  `family_rectifiable_reifenberg`, `ambient_retained_decomposition` and
  `exists_hausdorffP_le_of_local_bound_proof`.
* `rectifiable_reifenberg_theorem : RectifiableReifenbergTheoremStatement` applies this reduction to
  `compactBridgeCover_proof`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Composition

open ParabolicRectifiability.Enhancements
open ParabolicRectifiability.Foundations

/-! ## The compact bridge for regular vertical graphs -/

/-- Compact bridge, function form: a compactly perturbed regular vertical function is a
regular vertical function at the same tolerance. Proved from
`compactBridgeRepresentative_proof`. -/
theorem compactBridgeFunction_proof : CompactBridgeFunctionStatement := by
  intro n W G ε h
  obtain ⟨c, H, g, L, B, hG, -, hL, hB, hrep, hle⟩ := h
  subst hG
  exact ⟨g, L, B, hL, hB,
    compactBridgeRepresentative_proof n W c H g hrep, hle⟩

/-- Compact bridge, cover form: a cover by compactly perturbed regular vertical graphs is a
regular vertical graph cover without loss of tolerance. Proved from
`compactBridgeFunction_proof`. -/
theorem compactBridgeCover_proof : CompactBridgeCoverStatement := by
  intro n k K ε h
  obtain ⟨I, G, hG⟩ := h
  refine ⟨I, fun i =>
    { vertical_dimension := (G i).vertical_dimension
      direction := (G i).direction
      rank_eq := (G i).rank_eq
      offset := (G i).offset
      function := (G i).function
      regular := compactBridgeFunction_proof n
        (G i).direction (G i).function ε (G i).regular }, ?_⟩
  exact hG

/-! ## From the rectifiability decomposition to the parabolic rectifiable Reifenberg theorem -/

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

/-- Field adapter: the rectifiability decomposition, the compact-to-general cover bridge and a
global Hausdorff bound give every conclusion of the parabolic rectifiable Reifenberg theorem for the same retained
sets. -/
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

/-- A rectifiability decomposition with constant `C₁ ≤ C₀` becomes an output of the parabolic rectifiable Reifenberg theorem
with the final constant `C₀ (1 + N)`, using the hypothesis `hglob` (local Hausdorff bounds
on all balls of radius at most one imply the global bound with factor `N`). -/
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

/-- The parabolic rectifiable Reifenberg theorem from the compact-bridge cover statement. The mixed and family branches
come from `family_rectifiable_reifenberg`, the ambient branch from
`ambient_retained_decomposition`, and the global Hausdorff bound from
`exists_hausdorffP_le_of_local_bound_proof`. -/
theorem rectifiable_reifenberg_theorem_of_providers (hbridge : CompactBridgeCoverStatement) :
    RectifiableReifenbergTheoremStatement := by
  intro n hn
  obtain ⟨Cf, hCf, hfam⟩ := family_rectifiable_reifenberg n hn
  obtain ⟨Ca, hCa, hamb⟩ := ambient_retained_decomposition n hn
  obtain ⟨N, hN, hglob⟩ := exists_hausdorffP_le_of_local_bound_proof n
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

/-- **The parabolic rectifiable Reifenberg theorem**: `rectifiable_reifenberg_theorem_of_providers`
applied to the compact-bridge cover inclusion `compactBridgeCover_proof`. -/
theorem rectifiable_reifenberg_theorem : RectifiableReifenbergTheoremStatement :=
  rectifiable_reifenberg_theorem_of_providers compactBridgeCover_proof

end ParabolicRectifiability.Composition
