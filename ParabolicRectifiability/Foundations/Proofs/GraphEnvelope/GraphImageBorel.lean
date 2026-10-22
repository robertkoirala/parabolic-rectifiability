import ParabolicRectifiability.Foundations.Graphs

/-! # Horizontal (closed domain) and vertical graph images are Borel

Proofs of `fgenv_horizontal_image_measurableSet_of_isClosed` and
`fgenv_vertical_image_measurableSet`, with the same types.

Route (both): the graph map is continuous (Lipschitz) on a sigma-compact domain, so the image is
sigma-compact; a sigma-compact subset of a Hausdorff Borel space is a countable union of closed
sets and hence Borel. No hypotheses are used beyond those of the statements.
-/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.Foundations

/-- A sigma-compact subset of a Hausdorff Borel space is measurable. -/
theorem bf1genv2_measurableSet_of_isSigmaCompact {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] {s : Set X} (hs : IsSigmaCompact s) :
    MeasurableSet s := by
  obtain ⟨K, hK, rfl⟩ := hs
  exact MeasurableSet.iUnion fun i => (hK i).isClosed.measurableSet

/-- The graph map of a horizontal graph, with the displayed formula of `HorizontalGraph.image`. -/
def bf1genv2_horizontalMap {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε) (u : G.domain) :
    Space n :=
  point (G.offset + (u.val : Spatial n) + (G.normal u : Spatial n)) (G.time u)

theorem bf1genv2_horizontal_image_eq {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε) :
    G.image = Set.range (bf1genv2_horizontalMap G) := rfl

/-- The horizontal graph map is Lipschitz on its domain, with constant `1 + |ε|`. -/
theorem bf1genv2_horizontalMap_lipschitz {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε) :
    LipschitzWith (⟨1 + |ε|, by positivity⟩ : NNReal) (bf1genv2_horizontalMap G) := by
  refine LipschitzWith.of_dist_le_mul fun u v => ?_
  have hs := G.small_slope u v
  have hd : dist u v = ‖(u.val : Spatial n) - (v.val : Spatial n)‖ := by
    simp [Subtype.dist_eq, dist_eq_norm]
  have hn : ‖(G.normal u : Spatial n) - (G.normal v : Spatial n)‖ =
      ‖G.normal u - G.normal v‖ := by simp
  have hc : 0 ≤ ‖(u.val : Spatial n) - (v.val : Spatial n)‖ := norm_nonneg _
  have hε : ε * ‖(u.val : Spatial n) - (v.val : Spatial n)‖ ≤
      |ε| * ‖(u.val : Spatial n) - (v.val : Spatial n)‖ :=
    mul_le_mul_of_nonneg_right (le_abs_self ε) hc
  have h1 : ‖G.normal u - G.normal v‖ ≤ ε * ‖(u.val : Spatial n) - (v.val : Spatial n)‖ :=
    le_trans (le_max_left _ _) hs
  have h2 : Real.sqrt |G.time u - G.time v| ≤ ε * ‖(u.val : Spatial n) - (v.val : Spatial n)‖ :=
    le_trans (le_max_right _ _) hs
  unfold bf1genv2_horizontalMap
  rw [dist_point, hd]
  show max _ _ ≤ (1 + |ε|) * _
  refine max_le ?_ ?_
  · have e : G.offset + (u.val : Spatial n) + (G.normal u : Spatial n) -
        (G.offset + (v.val : Spatial n) + (G.normal v : Spatial n)) =
        ((u.val : Spatial n) - (v.val : Spatial n)) +
          ((G.normal u : Spatial n) - (G.normal v : Spatial n)) := by abel
    rw [e]
    refine le_trans (norm_add_le _ _) ?_
    rw [hn]
    nlinarith
  · nlinarith [abs_nonneg ε]

theorem bf1genv2_horizontalMap_continuous {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε) :
    Continuous (bf1genv2_horizontalMap G) :=
  (bf1genv2_horizontalMap_lipschitz G).continuous

/-- A closed-domain horizontal graph has a Borel image. -/
theorem fgenv_horizontal_image_measurableSet_of_isClosed_proof (n k : ℕ) (ε : ℝ)
    (G : HorizontalGraph n k ε) (hD : IsClosed G.domain) : MeasurableSet G.image := by
  have : ProperSpace G.domain := ProperSpace.of_isClosed hD
  rw [bf1genv2_horizontal_image_eq]
  exact bf1genv2_measurableSet_of_isSigmaCompact
    (isSigmaCompact_range (bf1genv2_horizontalMap_continuous G))

/-- The graph map of a full general regular vertical graph is continuous (it is built from the
Lipschitz function `G.function`). -/
theorem bf1genv2_vertical_map_continuous {n k : ℕ} {ε : ℝ}
    (G : GeneralRegularVerticalGraph n k ε) : Continuous G.map := by
  obtain ⟨g, L, B, hL, -⟩ := G.regular
  have hF : Continuous G.function := hL.continuous
  unfold GeneralRegularVerticalGraph.map
  refine Continuous.prodMk ?_ continuous_snd
  exact (continuous_const.add (continuous_subtype_val.comp continuous_fst)).add
    (continuous_subtype_val.comp hF)

/-- The image of a full general regular vertical graph is Borel. -/
theorem fgenv_vertical_image_measurableSet_proof (n k : ℕ) (ε : ℝ)
    (G : GeneralRegularVerticalGraph n k ε) : MeasurableSet G.image := by
  exact bf1genv2_measurableSet_of_isSigmaCompact
    (isSigmaCompact_range (bf1genv2_vertical_map_continuous G))

end ParabolicRectifiability.Foundations
