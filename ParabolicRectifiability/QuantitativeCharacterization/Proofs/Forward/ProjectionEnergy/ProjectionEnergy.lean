import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.ProjectionEnergy
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Completion.DerivativeRecurrence
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.ProjectionEnergy.PathErrorSum
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.ProjectionEnergy.Tail
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.ProjectionEnergy.MajorantSum
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.ProjectionEnergy.DiscreteAffine
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.ProjectionEnergy.SmallRadii
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.ProjectionEnergy.ScaleInterpolation
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.ProjectionEnergy.KernelIntegration
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.ProjectionEnergy.AllRadius
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.ProjectionEnergy.CurvatureContinuous
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.ProjectionEnergy.PathErrorMeasurable

/-! # Projection-energy estimate: composition of the proofs

Composition of the proofs of the projection-energy estimate into the statement
`d1e_hub_projectionEnergy`, under `d1e2comp_` names (`d1erecur_curvature_zero` replaces
`d1e2_curvature_zero`).

The only open hypothesis is `d1e_AffinePoincareStatement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

/-! ## Elementary helpers -/

/-- The affine Carleson bound on the standard base is monotone in its constant. -/
theorem d1e2comp_hasAffineCarlesonBound_mono {m d : ℕ} {f : Space m → Spatial d} {B B' : ℝ}
    (h : HasAffineCarlesonBound (parabolicVolume m) f B) (hB : B ≤ B') :
    HasAffineCarlesonBound (parabolicVolume m) f B' :=
  ⟨h.1.trans hB, fun z R hR => (h.2 z R hR).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hB (pow_nonneg hR.le _)))⟩

/-- The normalized derivative size `b_j` is nonnegative. -/
theorem d1e2comp_curvature_nonneg {n m : ℕ} {ι : Type*} (F : CoherentFamily n m ι)
    (P : CoherentChart.InitialChart F) (j : ℕ) (u : Spatial m) (t : ℝ) :
    0 ≤ d1e_curvature F P j u t := by
  unfold d1e_curvature
  exact mul_nonneg (CoherentChart.scale_pos F j).le
    (add_nonneg (ContinuousLinearMap.opNorm_nonneg _)
      (norm_nonneg (deriv (fun s => CoherentChart.stage F P j u s) t)))

/-- The path error `d_j` is nonnegative. -/
theorem d1e2comp_pathError_nonneg {n m : ℕ} {ι : Type*} (F : CoherentFamily n m ι)
    (P : CoherentChart.InitialChart F) (j : ℕ) (u : Spatial m) (t : ℝ) :
    0 ≤ d1e_pathError F P j u t := by
  unfold d1e_pathError
  exact ENNReal.toReal_nonneg

/-! ## Part 1: the path estimates of the actual family -/

/-- **Part 1: the path estimates of the actual family**
(`d1e2_PathEstimatesStatement`). The recurrence constant `C` and thresholds
`δ₁, E₁` of the derivative recurrence and the path threshold `δ₂` are chosen first; then
`C_W = 4C² + 2`, `C_T = 2C²`, `δ₀ = min δ₁ δ₂`, `E₀ = E₁`. At a family and chart, the sequence
lemma and the tail lemma are applied pointwise to the actual sequences
`b_j(p) = d1e_curvature F P j p`, `d_j(p) = d1e_pathError F P j p` and
`F_j(p) = CoherentChart.stage F P j p`. -/
theorem d1e2comp_pathEstimates (hB1 : d1e_DerivativeRecurrenceStatement) :
    d1e2_PathEstimatesStatement := by
  intro n σ hσ hσ₁
  obtain ⟨C, δ₁, E₁, hC, hδ₁, hE₁, hrec⟩ := hB1 n σ hσ hσ₁
  obtain ⟨δ₂, hδ₂, hpath⟩ := d1e2_pathError_sum_proof n σ hσ
  refine ⟨4 * C ^ 2 + 2, 2 * C ^ 2, min δ₁ δ₂, E₁, by positivity, by positivity,
    lt_min hδ₁ hδ₂, hE₁, ?_⟩
  intro m ι F δ E hδ hδm hE hEm hF hSq P
  have hsum := hpath F δ E hδ (hδm.trans (min_le_right _ _)) hF hSq P
  have hR := hrec F δ E hδ (hδm.trans (min_le_left _ _)) hE hEm hF hSq P
  have hT := fun p : Space m =>
    d1e2_tail_proof (fun j => CoherentChart.stage F P j p.1 p.2.val) F.scale
      (fun j => d1e_pathError F P j p.1 p.2.val) C E hC (CoherentChart.scale_pos F 0)
      (CoherentChart.scale_succ F) (fun j => d1e2comp_pathError_nonneg F P j p.1 p.2.val)
      (hsum p.1 p.2.val) (fun j => (hR p.1 p.2.val j).2)
  refine ⟨fun p => ?_, fun p j => (hT p).1 j, fun p => (hT p).2⟩
  exact d1e2_majorant_sum_proof (fun j => d1e_curvature F P j p.1 p.2.val)
    (fun j => d1e_pathError F P j p.1 p.2.val) C E hC
    (fun j => d1e2comp_curvature_nonneg F P j p.1 p.2.val) (d1erecur_curvature_zero F P p.1 p.2.val)
    (fun j => (hR p.1 p.2.val j).1) (hsum p.1 p.2.val)

/-! ## Part 2: measurability of the explicit majorants -/

/-- **Part 2: the level majorant `W_j = b_j² + T_j` is measurable**:
`b_j` is continuous, every `d_ℓ` is Borel, and a countable sum of measurable `ℝ≥0∞`-valued
functions is measurable. -/
theorem d1e2comp_levelMajorant_measurable {n m : ℕ} {ι : Type} (F : CoherentFamily n m ι)
    (P : CoherentChart.InitialChart F) (j : ℕ) : Measurable (d1e2_levelMajorant F P j) := by
  have h1 : Measurable fun p : Space m => ENNReal.ofReal (d1e_curvature F P j p.1 p.2.val ^ 2) :=
    ((d1e2_curvature_continuous_proof F P j).measurable.pow_const 2).ennreal_ofReal
  have h2 : Measurable fun p : Space m => d1e2_tailSum F P j p :=
    Measurable.tsum fun ℓ =>
      (((d1e2_pathError_measurable_proof F P (j + ℓ)).pow_const 2).const_mul
        (CoherentChart.ratio ^ ℓ)).ennreal_ofReal
  show Measurable fun p : Space m =>
    ENNReal.ofReal (d1e_curvature F P j p.1 p.2.val ^ 2) + d1e2_tailSum F P j p
  exact h1.add h2

/-! ## Part 3: the all-radius assembly and the final estimate -/

/-- **The projection-energy estimate**: exactly the type of
`d1e_hub_projectionEnergy`. Part 1 gives the path estimates and the estimate at the discrete
radii; part 2 the measurable majorants and the integrated energy at radii at most `r₀`; part 3
the radii above `r₀` and the all-radius assembly, all for the displacement `F⁰ - F₀` of one
family and one chart. The constant is the sum over the ranks `m' ≤ n` of the per-rank
constants; the actual rank satisfies `m ≤ n`. -/
theorem d1e2comp_hub_projectionEnergy_glue :
    d1e_DerivativeRecurrenceStatement → d1e_AffinePoincareStatement →
      d1e_ProjectionEnergyStatement := by
  intro hB1 hB2 n σ hσ hσ₁
  obtain ⟨CW, CT, δ₀, E₀, hCW, hCT, hδ₀, hE₀, hpe⟩ := d1e2comp_pathEstimates hB1 n σ hσ hσ₁
  choose CD hCD hdisc using d1e2_discrete_affine_proof hB2
  choose CS hCS hsmall using d1e2_small_radii_proof d1e2_scale_interpolation_proof d1e2_kernel_integration_proof
  choose CA hCA hall using d1e2_all_radius_proof
  have hK : ∀ m' : ℕ, 0 ≤ CS m' * (2 * (CD m' + CT)) * CW + CA m' * CT := fun m' =>
    add_nonneg (mul_nonneg (mul_nonneg (hCS m') (mul_nonneg zero_le_two
      (add_nonneg (hCD m') hCT))) hCW) (mul_nonneg (hCA m') hCT)
  refine ⟨∑ m' ∈ Finset.range (n + 1), (CS m' * (2 * (CD m' + CT)) * CW + CA m' * CT),
    δ₀, E₀, Finset.sum_nonneg fun m' _ => hK m', hδ₀, hE₀, ?_⟩
  intro m ι F δ E hδ hδm hE hEm hF hSq P
  obtain ⟨hW, htail, hsup⟩ := hpe F δ E hδ hδm hE hEm hF hSq P
  have hmn : m ≤ n := AffineSpatialPlane.nonempty_iff.mp ⟨F.initialPlane⟩
  have hS := hsmall m
    (fun p : Space m => d1e_projectionLimit F P p.1 p.2.val - (P.origin + P.isometry p.1))
    F.scale (fun j => d1e2_levelMajorant F P j) (2 * (CD m + CT)) (CW * E)
    (CoherentChart.scale_pos F 0) (CoherentChart.scale_succ F)
    (mul_nonneg zero_le_two (add_nonneg (hCD m) hCT)) (mul_nonneg hCW hE)
    (fun j => d1e2comp_levelMajorant_measurable F P j) hW (hdisc m F P CT hCT htail)
  have hA := hall m
    (fun p : Space m => d1e_projectionLimit F P p.1 p.2.val - (P.origin + P.isometry p.1))
    (F.scale 0) (CS m * (2 * (CD m + CT)) * (CW * E)) (CT * E) (CoherentChart.scale_pos F 0)
    (mul_nonneg (mul_nonneg (hCS m) (mul_nonneg zero_le_two (add_nonneg (hCD m) hCT)))
      (mul_nonneg hCW hE))
    (mul_nonneg hCT hE) hsup hS
  refine d1e2comp_hasAffineCarlesonBound_mono hA ?_
  have hle : CS m * (2 * (CD m + CT)) * CW + CA m * CT ≤
      ∑ m' ∈ Finset.range (n + 1), (CS m' * (2 * (CD m' + CT)) * CW + CA m' * CT) :=
    Finset.single_le_sum (f := fun m' => CS m' * (2 * (CD m' + CT)) * CW + CA m' * CT)
      (fun m' _ => hK m') (Finset.mem_range.mpr (Nat.lt_succ_of_le hmn))
  calc CS m * (2 * (CD m + CT)) * (CW * E) + CA m * (CT * E)
      = (CS m * (2 * (CD m + CT)) * CW + CA m * CT) * E := by ring
    _ ≤ (∑ m' ∈ Finset.range (n + 1), (CS m' * (2 * (CD m' + CT)) * CW + CA m' * CT)) * E :=
        mul_le_mul_of_nonneg_right hle hE

/-- **Composition of the projection-energy estimate**: the statement `d1e_hub_projectionEnergy` with the
derivative recurrence discharged by `d1e_derivative_recurrence_proof`. Only the
affine Poincaré hypothesis remains open. -/
theorem d1e2comp_hub_projectionEnergy_of_poincare :
    d1e_AffinePoincareStatement → d1e_ProjectionEnergyStatement :=
  d1e2comp_hub_projectionEnergy_glue d1e_derivative_recurrence_proof

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
