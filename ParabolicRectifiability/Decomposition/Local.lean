import ParabolicRectifiability.Decomposition.Interfaces
import ParabolicRectifiability.Decomposition.SourceLocalization
import ParabolicRectifiability.Decomposition.TypedPieces
import ParabolicRectifiability.Geometry.Horizontal.Cover
import ParabolicRectifiability.Measure.Neck.LocalStatements
import ParabolicRectifiability.Decomposition.Carrier.VerticalCover

/-! # Local steps of the rectifiable Reifenberg decomposition

The intermediate results of the positive-threshold decomposition, each proved
by the corresponding `_proof` theorem: finite localization of the square-good
part, geometric extraction, density refinement, horizontal and vertical graph
covers of the cores, compact typed pieces, and variable-radius packing. The
statements fix actual source restrictions, charts, density and scale-energy data.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace ParabolicRectifiability

/-- Restricting the source decreases the entire all-scale square. -/
theorem allScaleEnergy_restrict_le {n : ℕ} (ν : Measure (Space n))
    (G : Set (Space n)) (k : ℕ) (T : FamilyKind) (z : Space n) :
    allScaleEnergy (ν.restrict G) k T z ≤ allScaleEnergy ν k T z := by
  exact lintegral_mono fun r => betaSq_restrict_le ν G k T z r

/-- Finite Borel localization and the exact-tail bridge.
The harmless bound `2*M` dominates `M/(1-2^(-k-2))` for `k≥1`. -/
theorem exists_good_source_localization (n : ℕ) (hn : 1 ≤ n) :
    ∃ N : ℕ, 0 < N ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
      ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ M : ℝ, 0 ≤ M → Nonempty (GoodSourceLocalization μ k T M N) := by
  exact goodSourceLocalization_exists n hn

/-- The geometric decomposition: the geometric carrier and genuine typed core certificates, before regular graph extraction.
The source loss is measured with `ν`, never with Hausdorff measure. -/
theorem exists_geometric_extraction (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → k < n + 2 →
      ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ ν : Measure (Space n), IsFiniteMeasure ν → ν.InnerRegular →
      ∀ c : Space n, ν.support ⊆ Metric.closedBall c (1 / 64) →
      ∀ M : ℝ, 0 < M →
      (∀ᵐ z ∂ν, allScaleEnergy ν k T z ≤ ENNReal.ofReal (2 * M)) →
      Nonempty (GeometricExtraction ν k T M C) := by
  exact exists_geometric_extraction_proof n hn

/-- Density selection with `a = M`, applied to the unchanged source `ν|G`.
The factor `1+L/a` is at most three. Compactness, loss, lower mass and the
equal-radius estimates are all part of the conclusion. -/
theorem exists_density_refinement (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → k < n + 2 →
      ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ ν : Measure (Space n), IsFiniteMeasure ν → ν.InnerRegular →
      ∀ c : Space n, ν.support ⊆ Metric.closedBall c (1 / 64) →
      ∀ M : ℝ, 0 < M →
      (∀ᵐ z ∂ν, allScaleEnergy ν k T z ≤ ENNReal.ofReal (2 * M)) →
      ∀ G : Set (Space n), IsCompact G → G ⊆ ν.support →
      Nonempty (DensityRefinement ν k M C G) := by
  exact exists_density_refinement_proof n hn

/-- Horizontal regularity: the actual spatial chart and finite horizontal
square yield arbitrarily small subset graphs on the same compact core. -/
theorem horizontal_core_graph_cover {n k : ℕ} {K : Set (Space n)}
    (hK : IsHorizontalCore k K) (ε : ℝ) (hε : 0 < ε) :
    HasHorizontalGraphCover k K ε := by
  exact horizontal_core_graph_cover_proof hK ε hε

/-- Regular vertical carrier: finite own-Hausdorff square, upper growth and positive
lower density yield regular full vertical graphs, including spatial rank zero. -/
theorem vertical_core_graph_cover {n k : ℕ} {K : Set (Space n)}
    (hK : IsVerticalCore k K) (ε : ℝ) (hε : 0 < ε) :
    HasRegularVerticalGraphCover k K ε := by
  exact vertical_core_graph_cover_proof hK ε hε

/-- Compactification: choose types and compact approximants using the original
finite source. The additional loss is `M`. Core graph covers are supplied by
`horizontal_core_graph_cover` and `vertical_core_graph_cover`. -/
theorem exists_compact_typed_pieces {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n + 2)
    (T : FamilyKind) (hT : Nonempty (Models n k T))
    (ν : Measure (Space n)) (hν : IsFiniteMeasure ν) (hreg : ν.InnerRegular)
    (M Cg Cd : ℝ) (hM : 0 < M) (hCg : 0 < Cg) (hCd : 0 < Cd)
    (G : GeometricExtraction ν k T M Cg) (D : DensityRefinement ν k M Cd G.carrier)
    (hH : ∀ i ε, 0 < ε → HasHorizontalGraphCover k (G.horizontalCore i) ε)
    (hV : ∀ i ε, 0 < ε → HasRegularVerticalGraphCover k (G.verticalCore i) ε) :
    Nonempty (CompactTypedPieces ν k T M (Cg + Cd + 1) D.set) := by
  exact compactTypedPieces_exists hk hkn T hT ν hν hreg M Cg Cd hM hCg hCd G D hH hV

/-- The variable-radius packing transfer. Its lower mass hypothesis deliberately
uses `ν|G`, not the final retained restrictions. Finite disjoint balls feed the
barycenter transfer and the discrete packing estimate. -/
theorem exists_finite_ball_packing_constant (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → k < n + 2 →
      ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ ν : Measure (Space n), IsFiniteMeasure ν → ν.InnerRegular →
      ∀ c : Space n, ν.support ⊆ Metric.closedBall c (1 / 64) →
      ∀ M : ℝ, 0 < M →
      (∀ᵐ z ∂ν, allScaleEnergy ν k T z ≤ ENNReal.ofReal (2 * M)) →
      ∀ G : Set (Space n), IsCompact G → G ⊆ ν.support →
      ∀ K : Set (Space n), K ⊆ G → HasUniformLowerMass (ν.restrict G) k M K →
      HasFiniteBallPacking k C K := by
  exact exists_finite_ball_packing_constant_proof n hn

end ParabolicRectifiability
