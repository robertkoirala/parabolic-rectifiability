import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentStatements

/-! # The translated cost of a baseline and satellite segment

The unit-normal equation gives the exact extended distance to every affine line.
Parametrizing each segment and translating its parameter by `x` reduces both
integrals to the fitting inequality with offset `c - α * x - β * y`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.BetaP (Plane horizontalSegment)

/-- Translation preserves Lebesgue integrals over translated closed intervals. -/
private theorem e2_sap_lintegral_Icc_translate (f : ℝ → ℝ≥0∞) (x a b : ℝ) :
    (∫⁻ s in Icc (x + a) (x + b), f s) = ∫⁻ s in Icc a b, f (x + s) := by
  have hpre : (fun s : ℝ => x + s) ⁻¹' Icc (x + a) (x + b) = Icc a b := by
    ext s
    simp only [mem_preimage, mem_Icc, add_le_add_iff_left]
  rw [← (measurePreserving_add_left volume x).setLIntegral_comp_preimage_emb
    (Homeomorph.addLeft x).measurableEmbedding f (Icc (x + a) (x + b)), hpre]

/-- The exact pair-cost implication, using a normalized equation for an arbitrary line. -/
theorem e2_sap_pairCost_proof (hL : E2PlanarLine) (hS : E2sapSegment) (hF : E2sapFit) :
    E2sapPairCost := by
  intro p hp x y h δ ξ hh hδ hδmax hξ U
  obtain ⟨α, β, c, hnorm, hdist⟩ := hL.1 U
  have hbase : x - h ≤ x + h := by linarith
  have hsat : x + ξ - δ * h / 2 ≤ x + ξ + δ * h / 2 := by
    nlinarith [mul_pos hδ hh]
  rw [(hS (x - h) (x + h) y hbase).2.2,
    (hS (x + ξ - δ * h / 2) (x + ξ + δ * h / 2) (y + h) hsat).2.2]
  have hI :
      (∫⁻ s in Icc (x - h) (x + h), Metric.infEDist (e2_sapPt s y) U.toSet ^ p) =
        ∫⁻ s in Icc (-h) h, ENNReal.ofReal |α * s - (c - α * x - β * y)| ^ p := by
    rw [sub_eq_add_neg, e2_sap_lintegral_Icc_translate]
    apply lintegral_congr
    intro s
    rw [hdist]
    simp only [e2_sapPt, Matrix.cons_val_zero, Matrix.cons_val_one]
    congr 3
    ring
  have hJ :
      (∫⁻ s in Icc (x + ξ - δ * h / 2) (x + ξ + δ * h / 2),
        Metric.infEDist (e2_sapPt s (y + h)) U.toSet ^ p) =
        ∫⁻ s in Icc (ξ - δ * h / 2) (ξ + δ * h / 2),
          ENNReal.ofReal |α * s + β * h - (c - α * x - β * y)| ^ p := by
    have hlo : x + ξ - δ * h / 2 = x + (ξ - δ * h / 2) := by ring
    rw [hlo, add_assoc x ξ, e2_sap_lintegral_Icc_translate]
    apply lintegral_congr
    intro s
    rw [hdist]
    simp only [e2_sapPt, Matrix.cons_val_zero, Matrix.cons_val_one]
    congr 3
    ring
  rw [hI, hJ]
  exact hF p hp h δ ξ hh hδ hδmax hξ α β (c - α * x - β * y) hnorm

end ParabolicRectifiability.Examples
