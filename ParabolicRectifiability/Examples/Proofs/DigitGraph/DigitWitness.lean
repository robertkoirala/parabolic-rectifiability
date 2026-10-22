import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitLemmas

/-! # The digit-graph witness below the quadratic exponent: assembled properties

The four planar conclusions about the digit graph `E` and its natural measure `μ`: the measure
identification (`e2_sb_measureHub`), upper density bounds (`e2_sb_densityHub`), uniformly bounded
energies `S_{p,μ}^a` for `0 < p < 2` (`e2_sb_spHub`), and, on one set of full measure, divergence
of `S_{2,μ}^a` together with vanishing lower density (`e2_sb_fullHub`). Each is assembled from the
intermediate lemmas of `BelowTwoDigitLeaves` by supplying their hypotheses; these conclusions are
used to prove the corresponding failure statement of the `BetaP` area.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- **The measure:** `E` is compact, `H¹(E) = 1` and `H¹⌊E = μ`. -/
theorem e2_sb_measureHub : E2sbMeasureHub := by
  have hG := e2_sb_grid
  have hT := e2_sb_tails hG
  have hC := e2_sb_cover hG hT (e2_sb_digit hG hT)
  have hI := e2_sb_identify e2_sb_measurable hC
  exact ⟨hC.1, hI.2, hI.1⟩

/-- **Upper density:** the upper one-density of `μ` lies in `[1/2, 2]` on `E`. -/
theorem e2_sb_densityHub : E2sbDensityBounds := by
  have hG := e2_sb_grid
  have hT := e2_sb_tails hG
  exact (e2_sb_density hG hT (e2_sb_digit hG hT) e2_sb_measurable).2

/-- **Subquadratic exponents:** for `0 < p < 2` and finite `a > 0`, `S_{p,μ}^a` is
bounded on `E` uniformly in the centre. -/
theorem e2_sb_spHub : E2sbSpAll := by
  have hG := e2_sb_grid
  have hT := e2_sb_tails hG
  have hD := e2_sb_digit hG hT
  have hM := e2_sb_measurable
  have hL := e2_planarLine
  have hB := e2_sb_band hG hT hD (e2_sb_periodic hG) hM (e2_sb_density hG hT hD hM) hL
  exact e2_sb_spAll hM hL (e2_sb_spSmall hG hT hB)

/-- **The quadratic exponent on a full set:** on one common set of full `μ`-measure, `S_{2,μ}^a = ∞` for
every `a > 0` and the lower one-density of `μ` vanishes. -/
theorem e2_sb_fullHub : E2sbFullHub := by
  have hG := e2_sb_grid
  have hT := e2_sb_tails hG
  have hD := e2_sb_digit hG hT
  have hP := e2_sb_periodic hG
  have hM := e2_sb_measurable
  have hLC := e2_sb_lineCost hG hT hD hP hM (e2_sb_primitive hG) e2_variance e2_planarLine
  have hQB := e2_sb_quadBand hG hT hD hM hLC
  have hQD := e2_sb_quadDiverge hG hT
  have hLD := e2_sb_lowerDensity hG hT hD hP hM
  have hBC := e2_sb_borelCantelli hG hT
  have hMk := e2_sb_markedAE hG hD hM
  unfold E2sbBorelCantelli at hBC
  unfold E2sbMarkedAE at hMk
  have hmem : ∀ᵐ x ∂(volume.restrict (Ico (0 : ℝ) 1)), x ∈ Ico (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ico
  refine e2_sb_fullSet hM (fun z => (∀ a : ℝ, 0 < a → euclideanEnergyS e2_sbSource 1 2 a z = ⊤) ∧
    BetaP.planarLowerDensity e2_sbSource z = 0) ?_
  filter_upwards [hBC, hMk, hmem] with x hxBC hxMk hx
  refine ⟨hQD e2_sbSource (e2_sbGraph x) ?_, hLD x hxMk⟩
  filter_upwards [hxBC, eventually_ge_atTop 1] with j hj hj1
  obtain ⟨k, hk₁, hk₂⟩ := hj
  exact fun r hr₁ hr₂ => hQB j hj1 k x hx hk₁ hk₂ r hr₁ hr₂

end ParabolicRectifiability.Examples
