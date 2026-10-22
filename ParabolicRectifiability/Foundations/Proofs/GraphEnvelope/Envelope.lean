import ParabolicRectifiability.Foundations.Proofs.GraphEnvelope.Lemmas

/-! # Borel envelopes of horizontal and vertical graphs

`fgenv_graph_borel_envelope` proves the statement of
`ParabolicRectifiability.Characterization.graph_borel_envelope`: every horizontal graph lies in
a horizontal graph of the same slope bound with Borel image of locally finite `H_P^k` measure,
and every general regular vertical graph has Borel image of locally finite `H_P^k` measure.

Proof: the horizontal envelope is the closed extension `fgenv_horizontal_closed_extension`;
its image is Borel by `fgenv_horizontal_image_measurableSet_of_isClosed` (closed domain) and
locally of finite `H_P^k` measure by `fgenv_horizontal_hausdorffP_inter_ball_lt_top` (any
horizontal graph). The vertical image is Borel by `fgenv_vertical_image_measurableSet` and
locally finite by `fgenv_vertical_hausdorffP_inter_ball_lt_top`.
-/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.Foundations

/-- Borel envelopes of graphs: the statement of `graph_borel_envelope`. -/
theorem fgenv_graph_borel_envelope :
    ∀ n k : ℕ,
      (∀ (ε : ℝ) (G : HorizontalGraph n k ε), ∃ G' : HorizontalGraph n k ε,
        G.image ⊆ G'.image ∧ MeasurableSet G'.image ∧
        ∀ (q : Space n) (R : ℝ), hausdorffP n k (G'.image ∩ Metric.ball q R) < ⊤) ∧
      (∀ (ε : ℝ) (G : GeneralRegularVerticalGraph n k ε), MeasurableSet G.image ∧
        ∀ (q : Space n) (R : ℝ), hausdorffP n k (G.image ∩ Metric.ball q R) < ⊤) := by
  intro n k
  refine ⟨fun ε G => ?_, fun ε G => ⟨fgenv_vertical_image_measurableSet n k ε G,
    fgenv_vertical_hausdorffP_inter_ball_lt_top n k ε G⟩⟩
  obtain ⟨G', hsub, hclosed⟩ := fgenv_horizontal_closed_extension n k ε G
  exact ⟨G', hsub, fgenv_horizontal_image_measurableSet_of_isClosed n k ε G' hclosed,
    fgenv_horizontal_hausdorffP_inter_ball_lt_top n k ε G'⟩

end ParabolicRectifiability.Foundations
