import ParabolicRectifiability.Geometry.Chart.RecurrenceEstimates
import ParabolicRectifiability.Geometry.Neck.BufferedReferenceAssembly
import ParabolicRectifiability.Geometry.Neck.StructureAssembly
import ParabolicRectifiability.Geometry.Neck.BufferedReference
import ParabolicRectifiability.Geometry.Neck.NeckAttachment
import ParabolicRectifiability.Geometry.Neck.LocalContent
import ParabolicRectifiability.Geometry.Neck.VerticalCoreDensity
import ParabolicRectifiability.Geometry.Neck.HorizontalCoreDensity

/-!
# Neck: the six neck theorems

Each of the six theorems `<name>_proof` has the type of the neck theorem `<name>`
(vertical and horizontal coherent chart, buffered reference, neck structure). Each is a
one-line application of the assembly results of `HubTreeChart`, `HubTreeBuffer` and
`HubTreeStructure`, with the remaining inputs supplied by their proofs:

* the recurrence and finite metric estimates: `CoherentChart.recurrences_proof`,
  `CoherentChart.finite_metric_proof`, fed by
  `CoherentChart.induction_estimates_proof`;
* the buffer constructions: `verticalBufferedReference_of_chart_proof`,
  `horizontalBufferedReference_of_chart_proof`;
* the horizontal distance and exact attachments: `horizontal_dist_eq_of_mem_centers_proof`,
  `vertical_hasParametrization_of_chart_proof`, `horizontal_hasParametrization_of_chart_proof`;
* the local content bounds: `vertical_localContent_of_parametrization_proof`,
  `horizontal_localContent_of_parametrization_proof`;
* the core density: `vertical_coreLowerDensity_of_parametrization_proof` and
  `horizontal_coreLowerDensity_of_parametrization_proof`.
-/

noncomputable section

namespace ParabolicRectifiability

namespace NeckHubTree

open MeasureTheory Set
open scoped ENNReal
open CoherentChart

universe u

/-- The recurrence estimates, at the hypothesis type of `finite_chart_of_leaves`,
from `CoherentChart.recurrences_proof` and the induction estimates. -/
theorem recurrences_leaf_proof :
    ∀ {n m : ℕ} {ι : Type u} {F : CoherentFamily n m ι} {σ δ E : ℝ} {N : ℕ},
          0 < σ → 0 ≤ δ → DeltaSmall n σ δ → EnergySmall n σ E → F.IsCoherentUpTo σ δ N →
          ∀ (P : InitialChart F), PathBoundUpTo F P E N →
          (∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ) (v : Spatial m),
            99 / 100 * ‖v‖ ≤ ‖fderiv ℝ (fun w => stage F P j w t) u v‖ ∧
              ‖fderiv ℝ (fun w => stage F P j w t) u v‖ ≤ 101 / 100 * ‖v‖) ∧
          (∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ),
            ‖fderiv ℝ (fun v => fderiv ℝ (fun w => stage F P j w t) v) u‖ ≤
                chartCa n σ * chartEps n σ δ / F.scale j ∧
              ‖deriv (fun s => stage F P j u s) t‖ ≤ chartCa n σ * chartEps n σ δ / F.scale j) ∧
          (∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ),
            ‖deriv (fun s => stage F P (j + 1) u s - stage F P j u s) t‖ ≤
              chartCΔ n σ * chartEps n σ δ / F.scale j) :=
  fun {_n _m _ι F σ δ E N} hσ hδ hsmall hEsmall hF P hpath =>
    CoherentChart.recurrences_proof
      (fun {F σ δ N} hσ hδ hsmall hF P => CoherentChart.induction_estimates_proof (F := F)
        (σ := σ) (δ := δ) (N := N) hσ hδ hsmall hF P)
      (F := F) (σ := σ) (δ := δ) (E := E) (N := N) hσ hδ hsmall hEsmall hF P hpath

/-- The finite metric estimates, at the hypothesis type of `finite_chart_of_leaves`,
from `CoherentChart.finite_metric_proof` and the induction estimates. -/
theorem finite_metric_leaf_proof :
    ∀ {n m : ℕ} {ι : Type u} {F : CoherentFamily n m ι} {σ δ E : ℝ} {N : ℕ},
          0 < σ → 0 ≤ δ → DeltaSmall n σ δ → EnergySmall n σ E → F.IsCoherentUpTo σ δ N →
          ∀ (P : InitialChart F), PathBoundUpTo F P E N →
          ∀ j ≤ N + 1,
            (∀ (u : Spatial m) (t s : ℝ),
              ‖stage F P j u t - stage F P j u s‖ ≤
                chartCt n σ * chartEps n σ δ * Real.sqrt |t - s|) ∧
            (∀ (u v : Spatial m) (t : ℝ),
              9 / 10 * ‖u - v‖ ≤ ‖stage F P j u t - stage F P j v t‖ ∧
                ‖stage F P j u t - stage F P j v t‖ ≤ 101 / 100 * ‖u - v‖) ∧
            (∀ (u v : Spatial m) (t s : ℝ),
              4 / 5 * dist (point u t) (point v s) ≤
                  dist (point (stage F P j u t) t) (point (stage F P j v s) s) ∧
                dist (point (stage F P j u t) t) (point (stage F P j v s) s) ≤
                  11 / 10 * dist (point u t) (point v s)) :=
  fun {_n _m _ι F σ δ E N} hσ hδ hsmall hEsmall hF P hpath =>
    CoherentChart.finite_metric_proof
      (fun {F σ δ N} hσ hδ hsmall hF P => CoherentChart.induction_estimates_proof (F := F)
        (σ := σ) (δ := δ) (N := N) hσ hδ hsmall hF P)
      (F := F) (σ := σ) (δ := δ) (E := E) (N := N) hσ hδ hsmall hEsmall hF P hpath

/-- The statement of `vertical_coherent_chart`. -/
theorem vertical_coherent_chart_proof (n : ℕ) (σ : ℝ) (hσ : 0 < σ) (hσ₁ : σ ≤ 1) :
    ∃ δ₀ E₀ κ₀ C : ℝ, 0 < δ₀ ∧ 0 < E₀ ∧ 0 < κ₀ ∧ 0 < C ∧
      ∀ {m : ℕ} {ι : Type u} (F : CoherentFamily n m ι) (δ E : ℝ),
        0 ≤ δ → δ ≤ δ₀ → 0 ≤ E → E ≤ E₀ →
        F.IsCoherent σ δ → F.VerticalSquareBound E →
        ∃ G : Spatial m → ℝ → Spatial n,
          (∀ p p' : Space m,
            4 / 5 * dist p p' ≤ dist (timePreservingMap G p) (timePreservingMap G p') ∧
              dist (timePreservingMap G p) (timePreservingMap G p') ≤ 11 / 10 * dist p p') ∧
          (∀ (u : Spatial m) (t s : ℝ), ‖G u t - G u s‖ ≤ C * δ * Real.sqrt |t - s|) ∧
          IsClosed (Set.range (timePreservingMap G)) ∧
          ∀ κ : ℝ, 0 ≤ κ → κ ≤ κ₀ → F.HasCenterHeight κ →
            (∀ z : Space n, F.IsLevelLimit z → z ∈ Set.range (timePreservingMap G)) ∧
            ∀ θ : ℝ, 0 ≤ θ → ∀ (c : Space n) (d : ℝ) (p : Option (ℕ × ι)),
              F.IsStoppingParent θ c d p →
                ∃ u : Spatial m, ‖G u c.2.val - c.1‖ ≤ C * 10 * (θ + δ) * d :=
  vertical_coherent_chart_of_leaves recurrences_leaf_proof finite_metric_leaf_proof
    n σ hσ hσ₁

/-- The statement of `horizontal_coherent_chart`. -/
theorem horizontal_coherent_chart_proof (n : ℕ) (σ : ℝ) (hσ : 0 < σ) (hσ₁ : σ ≤ 1) :
    ∃ δ₀ E₀ κ₀ C : ℝ, 0 < δ₀ ∧ 0 < E₀ ∧ 0 < κ₀ ∧ 0 < C ∧
      ∀ {m : ℕ} {ι : Type u} (F : CoherentFamily n m ι) (δ E γ : ℝ),
        0 ≤ δ → δ ≤ δ₀ → 0 ≤ E → E ≤ E₀ → 0 ≤ γ → γ ≤ min (σ ^ 2) 1 / 4 →
        F.IsCoherent σ δ → F.HorizontalSquareBound E → F.IsTimeCompatible γ →
        ∃ G : Spatial m → Spatial n,
          (∀ u v : Spatial m,
            4 / 5 * ‖u - v‖ ≤ ‖G u - G v‖ ∧ ‖G u - G v‖ ≤ 11 / 10 * ‖u - v‖) ∧
          IsClosed (Set.range G) ∧
          ∀ κ : ℝ, 0 ≤ κ → κ ≤ κ₀ → F.HasCenterHeight κ →
            (∀ z : Space n, F.IsLevelLimit z → z.1 ∈ Set.range G) ∧
            ∀ θ : ℝ, 0 ≤ θ → ∀ (c : Space n) (d : ℝ) (p : Option (ℕ × ι)),
              F.IsStoppingParent θ c d p →
                ∃ u : Spatial m, ‖G u - c.1‖ ≤ C * 10 * (θ + δ) * d :=
  horizontal_coherent_chart_of_leaves recurrences_leaf_proof finite_metric_leaf_proof
    n σ hσ hσ₁

/-- The statement of `vertical_buffered_reference`. -/
theorem vertical_buffered_reference_proof (n : ℕ) (σ : ℝ) (hσ : 0 < σ) (hσ₁ : σ ≤ 1) :
    ∃ δ₀ E₀ κ₀ cb : ℝ, 0 < δ₀ ∧ 0 < E₀ ∧ 0 < κ₀ ∧ 0 < cb ∧
      ∀ Cs : ℝ, 0 < Cs → ∃ Cr Cm : ℝ, 0 < Cr ∧ 0 < Cm ∧
        ∀ {m : ℕ} {ι : Type u} (F : CoherentFamily n m ι) (N : ℕ) (q : Space n)
          (R δ E κ : ℝ), 0 < R → 0 ≤ δ → δ ≤ δ₀ → 0 ≤ E → E ≤ E₀ → 0 ≤ κ → κ ≤ κ₀ →
          F.IsCoherentUpTo σ δ N → F.VerticalSquareBoundUpTo E N →
          F.HasCenterHeightUpTo κ N →
          F.initialRadius ≤ Cs * R →
          (∀ j ≤ N, ∀ a ∈ F.index j, F.center j a ∈ Metric.ball q (Cs * R)) →
          (∃ x ∈ F.initialPlane.toSet, ‖x - q.1‖ ≤ Cs * R) →
          F.HasVerticalBufferedReference R Cr Cm cb N :=
  vertical_buffered_reference_of_finite_chart
    (finite_chart_of_leaves recurrences_leaf_proof finite_metric_leaf_proof)
    verticalBufferedReference_of_chart_proof n σ hσ hσ₁

/-- The statement of `horizontal_buffered_reference`. -/
theorem horizontal_buffered_reference_proof (n : ℕ) (σ : ℝ) (hσ : 0 < σ) (hσ₁ : σ ≤ 1) :
    ∃ δ₀ E₀ κ₀ cb : ℝ, 0 < δ₀ ∧ 0 < E₀ ∧ 0 < κ₀ ∧ 0 < cb ∧
      ∀ Cs : ℝ, 0 < Cs → ∃ Cr Cm : ℝ, 0 < Cr ∧ 0 < Cm ∧
        ∀ {m : ℕ} {ι : Type u} (F : CoherentFamily n m ι) (N : ℕ) (q : Space n)
          (R δ E κ γ : ℝ), 0 < R → 0 ≤ δ → δ ≤ δ₀ → 0 ≤ E → E ≤ E₀ → 0 ≤ κ → κ ≤ κ₀ →
          0 ≤ γ → γ ≤ min (σ ^ 2) 1 / 4 →
          F.IsCoherentUpTo σ δ N → F.HorizontalSquareBoundUpTo E N →
          F.HasCenterHeightUpTo κ N → F.IsTimeCompatibleUpTo γ N →
          F.initialRadius ≤ Cs * R →
          (∀ j ≤ N, ∀ a ∈ F.index j, F.center j a ∈ Metric.ball q (Cs * R)) →
          (∃ x ∈ F.initialPlane.toSet, ‖x - q.1‖ ≤ Cs * R) →
          F.HasHorizontalBufferedReference R Cr Cm cb N :=
  horizontal_buffered_reference_of_finite_chart
    (finite_chart_of_leaves recurrences_leaf_proof finite_metric_leaf_proof)
    horizontalBufferedReference_of_chart_proof n σ hσ hσ₁

/-- The statement of `vertical_neck_structure`. -/
theorem vertical_neck_structure_proof (n : ℕ) :
    ∃ (cb : ℝ → ℝ) (Cr Cm : ℝ → ℝ → ℝ),
      (∀ σ : ℝ, 0 < σ → σ ≤ 1 →
        0 < cb σ ∧ ∀ Cs : ℝ, 0 < Cs → 0 < Cr σ Cs ∧ 0 < Cm σ Cs) ∧
      ∀ c₀ : ℝ, 0 < c₀ → ∃ C : ℝ, 1 ≤ C ∧ ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
        ∃ δ₀ E₀ κ₀ θ₀ : ℝ, 0 < δ₀ ∧ 0 < E₀ ∧ 0 < κ₀ ∧ 0 < θ₀ ∧
          ∀ {k : ℕ} {ι : Type u} {q : Space n} {R Cd Cs δ E κ θ γ : ℝ}
            (N : NeckRegion n k .vertical ι q R c₀ Cd Cs σ δ E κ θ γ),
            δ ≤ δ₀ → E ≤ E₀ → κ ≤ κ₀ → θ ≤ θ₀ →
            N.HasVerticalParametrization 2 ∧ N.HasLocalContentBound C ∧
              N.HasTotalContentBound (C * (2 + Cd) ^ k) ∧ N.HasCoreDensity C ∧
              ∀ M : ℕ, N.family.HasVerticalBufferedReference R (Cr σ Cs) (Cm σ Cs) (cb σ) M :=
  vertical_neck_structure_of_hubs vertical_coherent_chart_proof vertical_buffered_reference_proof
    vertical_hasParametrization_of_chart_proof vertical_localContent_of_parametrization_proof
    vertical_coreLowerDensity_of_parametrization_proof n

/-- The statement of `horizontal_neck_structure`. -/
theorem horizontal_neck_structure_proof (n : ℕ) :
    ∃ (cb : ℝ → ℝ) (Cr Cm : ℝ → ℝ → ℝ),
      (∀ σ : ℝ, 0 < σ → σ ≤ 1 →
        0 < cb σ ∧ ∀ Cs : ℝ, 0 < Cs → 0 < Cr σ Cs ∧ 0 < Cm σ Cs) ∧
      ∀ c₀ : ℝ, 0 < c₀ → ∃ C : ℝ, 1 ≤ C ∧ ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
        ∃ δ₀ E₀ κ₀ θ₀ : ℝ, 0 < δ₀ ∧ 0 < E₀ ∧ 0 < κ₀ ∧ 0 < θ₀ ∧
          ∀ {k : ℕ} {ι : Type u} {q : Space n} {R Cd Cs δ E κ θ γ : ℝ}
            (N : NeckRegion n k .horizontal ι q R c₀ Cd Cs σ δ E κ θ γ),
            δ ≤ δ₀ → E ≤ E₀ → κ ≤ κ₀ → θ ≤ θ₀ → γ ≤ min (σ ^ 2) (min (c₀ ^ 2) 1) / 4 →
            N.HasHorizontalParametrization 2 ∧ N.HasLocalContentBound C ∧
              N.HasTotalContentBound (C * (2 + Cd) ^ k) ∧ N.HasCoreDensity C ∧
              ∀ M : ℕ,
                N.family.HasHorizontalBufferedReference R (Cr σ Cs) (Cm σ Cs) (cb σ) M :=
  horizontal_neck_structure_of_hubs horizontal_coherent_chart_proof
    horizontal_buffered_reference_proof horizontal_dist_eq_of_mem_centers_proof
    horizontal_hasParametrization_of_chart_proof horizontal_localContent_of_parametrization_proof
    horizontal_coreLowerDensity_of_parametrization_proof n

end NeckHubTree

end ParabolicRectifiability
