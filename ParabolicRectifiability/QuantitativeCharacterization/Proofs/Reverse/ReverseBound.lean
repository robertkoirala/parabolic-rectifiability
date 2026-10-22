import ParabolicRectifiability.QuantitativeCharacterization.Statements.ReverseBound
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Geometry
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reverse.WhitneyCells
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reverse.OnCarrier
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reverse.HallInequality
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reverse.KernelOfPartition
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reverse.CouplingOfParts
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reverse.Comparison
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reverse.ErrorIntegral
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reverse.MainTerm
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reverse.ModelTransfer
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reverse.CoveringAssembly
import ParabolicRectifiability.Measure.Neck.Packing

/-! # The reverse bound: composition

`d2comp_exists_local_reverse_bound_of_inputs` assembles the local reverse bound from the proofs of
the component statements, taking every input statement as a premise (implication form):

1. `ReferenceEstimatesStatement`;
2. `ba1_horizontal_basic`; 3. `ba1_vertical_basic`; 4. `ba1_ambient_basic`.

Its conclusion is exactly the type of `exists_local_reverse_bound`, which is closed by
`exact d2comp_exists_local_reverse_bound_of_inputs reference_estimates <ba1 proofs>`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization.ReverseTree

open ParabolicRectifiability.Foundations

/-- Every typed `L`-reference measure is finite on compacts (basic-fact premises; the ambient
reference by the existing instance). -/
theorem d2comp_reference_finite
    (hHor : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∀ H : HorizontalReference n k L,
      Measurable H.map ∧ IsClosed H.carrier ∧ IsFiniteMeasureOnCompacts H.measure ∧
        H.measure.InnerRegular)
    (hVer : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∀ V : VerticalReference n k L,
      MeasurableEmbedding V.map ∧ IsClosed V.carrier ∧ V.measure.support = V.carrier ∧
        IsFiniteMeasureOnCompacts V.measure ∧ V.measure.InnerRegular)
    {n k : ℕ} {L : ℝ} (hL : 1 ≤ L) (ρ : Reference n k L) :
    IsFiniteMeasureOnCompacts ρ.measure := by
  cases ρ with
  | horizontal H => exact (hHor n k L hL H).2.2.1
  | vertical V => exact (hVer n k L hL V).2.2.2.1
  | ambient h =>
    show IsFiniteMeasureOnCompacts (parabolicVolume n)
    infer_instance

/-- Every typed `L`-reference has support equal to its carrier (horizontal: definition of the
carrier; vertical and ambient: basic-fact premises). -/
theorem d2comp_reference_support
    (hVer : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∀ V : VerticalReference n k L,
      MeasurableEmbedding V.map ∧ IsClosed V.carrier ∧ V.measure.support = V.carrier ∧
        IsFiniteMeasureOnCompacts V.measure ∧ V.measure.InnerRegular)
    (hAmb : ∀ n : ℕ, (parabolicVolume n).InnerRegular ∧
      (parabolicVolume n).support = Set.univ)
    {n k : ℕ} {L : ℝ} (hL : 1 ≤ L) (ρ : Reference n k L) :
    ρ.measure.support = ρ.carrier := by
  cases ρ with
  | horizontal H => rfl
  | vertical V => exact (hVer n k L hL V).2.2.1
  | ambient h => exact (hAmb n).2

/-- **The local reverse bound, composed**, in
implication form over the four inputs. Conclusion: exactly the type of
`exists_local_reverse_bound`. -/
theorem d2comp_exists_local_reverse_bound_of_inputs
    (hRef : ReferenceEstimatesStatement)
    (hHor : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∀ H : HorizontalReference n k L,
      Measurable H.map ∧ IsClosed H.carrier ∧ IsFiniteMeasureOnCompacts H.measure ∧
        H.measure.InnerRegular)
    (hVer : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∀ V : VerticalReference n k L,
      MeasurableEmbedding V.map ∧ IsClosed V.carrier ∧ V.measure.support = V.carrier ∧
        IsFiniteMeasureOnCompacts V.measure ∧ V.measure.InnerRegular)
    (hAmb : ∀ n : ℕ, (parabolicVolume n).InnerRegular ∧
      (parabolicVolume n).support = Set.univ) :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ L : ℝ, 1 ≤ L → ∃ Brev : ℝ, 1 ≤ Brev ∧ ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 0 < C ∧
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → ∀ K : ℝ, 1 ≤ K →
        Nonempty (RegularMixedCovering k K L μ a R) →
        (∀ b ∈ μ.support ∩ Metric.ball a (Brev * R), ∀ s : ℝ, 0 < s → s ≤ Brev * R →
          μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k)) →
        (∫⁻ z in Metric.ball a R, squareEnergy μ k .mixed R z ∂μ) ≤
          ENNReal.ofReal (C * K * R ^ k) := by
  have hCoupling : CouplingStatement :=
    d2_coupling_of_parts_proof d2_whitney_cells_proof d2_on_carrier_proof
      d2_hall_inequality_proof d2_kernel_of_partition_proof
  have hTransfer : ModelTransferStatement :=
    d2_model_transfer_of_parts_proof hCoupling d2_comparison_proof d2_error_integral_proof
      d2_main_term_proof
  intro n hn k hk hkn L hL
  obtain ⟨Aref, hAref, Cref, hCref, href⟩ := hRef n hn k hk hkn L hL
  obtain ⟨Bm, hBm, hT⟩ := hTransfer n hn k hk hkn L hL Aref hAref Cref hCref
  have hBL : 1 ≤ (1 + Bm) * L := by
    have h := mul_le_mul_of_nonneg_left hL (by linarith : (0 : ℝ) ≤ 1 + Bm)
    linarith
  refine ⟨(1 + Bm) * L, hBL, fun A hA => ?_⟩
  obtain ⟨C₁, hC₁, hT'⟩ := hT A hA
  refine ⟨A + C₁, by linarith, ?_⟩
  intro μ hμ hμr a ha R hR K hK hcov hgrowth
  obtain ⟨𝒞⟩ := hcov
  have hRB : R ≤ (1 + Bm) * L * R := by
    have h := mul_le_mul_of_nonneg_right hBL hR.le
    linarith
  refine d2_covering_assembly_proof n hn k hk hkn L K A C₁ hL hK hA hC₁ μ hμ hμr a ha R hR 𝒞
    (fun b hb s hs hsR =>
      hgrowth b ⟨hb.1, Metric.ball_subset_ball hRB hb.2⟩ s hs (hsR.trans hRB))
    (fun i => ?_)
  have hri : 0 < 𝒞.radius i := 𝒞.radius_pos i
  have hsub := 𝒞.ball_subset i
  have hRi : 𝒞.radius i ≤ L * R := radius_le_of_ball_subset hri hsub
  have hci : dist (𝒞.center i) a < L * R :=
    Metric.mem_ball.mp (hsub (Metric.mem_ball_self hri))
  have hBRi : Bm * 𝒞.radius i ≤ Bm * (L * R) :=
    mul_le_mul_of_nonneg_left hRi (by linarith)
  have hBmLR : Bm * (L * R) + L * R = (1 + Bm) * L * R := by ring
  obtain ⟨hADR, hE, -⟩ := href (𝒞.reference i)
  refine hT' μ hμ hμr (𝒞.reference i).kind (𝒞.reference i).carrier (𝒞.reference i).measure
    (d2comp_reference_finite hHor hVer hL (𝒞.reference i))
    (d2comp_reference_support hVer hAmb hL (𝒞.reference i)) hADR hE
    (𝒞.center i) (𝒞.center_mem_support i) (𝒞.radius i) hri (𝒞.ball_meets_carrier i) ?_
  intro b hb s hs hsle
  have hb2 : dist b (𝒞.center i) < Bm * 𝒞.radius i := Metric.mem_ball.mp hb.2
  refine hgrowth b ⟨hb.1, ?_⟩ s hs ?_
  · rw [Metric.mem_ball]
    calc dist b a ≤ dist b (𝒞.center i) + dist (𝒞.center i) a := dist_triangle _ _ _
      _ < Bm * 𝒞.radius i + L * R := add_lt_add hb2 hci
      _ ≤ (1 + Bm) * L * R := by linarith
  · have hLR : 0 ≤ L * R := mul_nonneg (by linarith) hR.le
    linarith

end ParabolicRectifiability.QuantitativeCharacterization.ReverseTree
