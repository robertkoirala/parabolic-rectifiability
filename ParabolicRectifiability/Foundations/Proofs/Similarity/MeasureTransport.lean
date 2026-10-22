import ParabolicRectifiability.Decomposition.Carrier.Transport
import ParabolicRectifiability.Analysis.TraceExtension.Similarity

/-! # Measure transport by a parabolic similarity

Proofs of `fsim_hausdorffP_preimage_similarity`, `fsim_support_restrict_preimage_homeomorph`
and `fsim_parabolicVolume_thickening_preimage_similarity`. Each `<name>_proof` has exactly the
type of the statement `<name>`.

* `fsim_hausdorffP_preimage_similarity`: `S⁻¹' A` is mapped onto `A` by `S`, and the
  exact scaling `hausdorffP_image_similarity` gives `H^k(A) = R^{-k} H^k(S⁻¹' A)`; multiply by `R^k`. Every set, every `k`.
* `fsim_support_restrict_preimage_homeomorph`: the support is tested on open sets only
  (`Measure.support_eq_forall_isOpen`), on which both restrictions evaluate by
  `Measure.restrict_apply`; the pushforward evaluates on every set by
  `MeasurableEquiv.map_apply`; `c ≠ 0` keeps positivity; open sets correspond by `e⁻¹'`.
* `fsim_parabolicVolume_thickening_preimage_similarity`: the identity
  `infEDist z (S⁻¹' K) = R · infEDist (S z) K` (`fsimb2_infEDist_preimage_similarity`, valid at
  `⊤` and for empty `K`) makes the left set `S⁻¹'` of the open right set for every real `r`
  (`ofReal r = ofReal R · ofReal (r / R)`, also for `r ≤ 0`); then
  `map_similarity_parabolicVolume`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Foundations

/-- **Hausdorff measure under the similarity.** `H_P^k(S⁻¹' A) = R^k H_P^k(A)` for every `k` and every set `A`. -/
theorem fsim_hausdorffP_preimage_similarity_proof (n k : ℕ) (a : Space n) (R : ℝ) (hR : 0 < R)
    (A : Set (Space n)) :
    hausdorffP n k (similarity a R hR ⁻¹' A) = ENNReal.ofReal R ^ k * hausdorffP n k A := by
  have h := hausdorffP_image_similarity k a R hR (similarity a R hR ⁻¹' A)
  rw [Homeomorph.image_preimage] at h
  rw [h, ← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hR).ne'
    ENNReal.ofReal_ne_top, one_pow, one_mul]

/-- **Actual supports of pulled-back restrictions.** The actual support of `μ⌊e⁻¹(A)` is `e⁻¹` of the actual support of
`(c · e_# μ)⌊A`, for every measure, homeomorphism, set `A` and `c ∈ (0, ∞)`. -/
theorem fsim_support_restrict_preimage_homeomorph_proof {X Y : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (e : X ≃ₜ Y) (c : ℝ≥0∞) (hc0 : c ≠ 0) (_hct : c ≠ ⊤) (A : Set Y) :
    (μ.restrict (e ⁻¹' A)).support = e ⁻¹' ((c • μ.map e).restrict A).support := by
  have hL : ∀ U : Set X, IsOpen U → μ.restrict (e ⁻¹' A) U = μ (U ∩ e ⁻¹' A) :=
    fun U hU => Measure.restrict_apply hU.measurableSet
  have hR : ∀ V : Set Y, IsOpen V →
      ((c • μ.map e).restrict A) V = c * μ (e ⁻¹' V ∩ e ⁻¹' A) := by
    intro V hV
    rw [Measure.restrict_apply hV.measurableSet, Measure.smul_apply, smul_eq_mul,
      ← e.toMeasurableEquiv_coe, MeasurableEquiv.map_apply, preimage_inter]
  ext x
  simp only [Measure.support_eq_forall_isOpen, mem_ofPred_eq, mem_preimage]
  constructor
  · intro h V hxV hV
    have hU : IsOpen (e ⁻¹' V) := hV.preimage e.continuous
    have hpos := h (e ⁻¹' V) hxV hU
    rw [hL _ hU] at hpos
    rw [hR V hV]
    exact ENNReal.mul_pos hc0 hpos.ne'
  · intro h U hxU hU
    have hV : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
    have hxV : e x ∈ e.symm ⁻¹' U := by
      rw [mem_preimage, Homeomorph.symm_apply_apply]
      exact hxU
    have hpos := h _ hxV hV
    have hpre : e ⁻¹' (e.symm ⁻¹' U) = U := by
      ext y
      rw [mem_preimage, mem_preimage, Homeomorph.symm_apply_apply]
    rw [hR _ hV, hpre] at hpos
    rw [hL U hU]
    exact (ENNReal.mul_pos_iff.1 hpos).2

/-- `infEDist z (S⁻¹' K) = R · infEDist (S z) K` for every set `K` (both sides `⊤` for empty
`K`). -/
theorem fsimb2_infEDist_preimage_similarity {n : ℕ} (a : Space n) (R : ℝ) (hR : 0 < R)
    (K : Set (Space n)) (z : Space n) :
    Metric.infEDist z (similarity a R hR ⁻¹' K) =
      ENNReal.ofReal R * Metric.infEDist (similarity a R hR z) K := by
  have hR0 : ENNReal.ofReal R ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  rw [← Homeomorph.image_symm]
  simp only [Metric.infEDist, iInf_image]
  rw [ENNReal.mul_iInf_of_ne hR0 ENNReal.ofReal_ne_top]
  refine iInf_congr fun w => ?_
  rw [ENNReal.mul_iInf_of_ne hR0 ENNReal.ofReal_ne_top]
  refine iInf_congr fun _ => ?_
  have h := edist_similarity_symm a R hR (similarity a R hR z) w
  rwa [Homeomorph.symm_apply_apply] at h

/-- **Tubular neighbourhoods under the similarity.** `|{z : dist(z, S⁻¹' K) < r}| = R^{n+2} |{w : dist(w, K) < r/R}|` for every
set `K` and every real `r`. -/
theorem fsim_parabolicVolume_thickening_preimage_similarity_proof {n : ℕ} (a : Space n) (R : ℝ)
    (hR : 0 < R) (K : Set (Space n)) (r : ℝ) :
    parabolicVolume n {z | Metric.infEDist z (similarity a R hR ⁻¹' K) < ENNReal.ofReal r} =
      ENNReal.ofReal R ^ (n + 2) *
        parabolicVolume n {w | Metric.infEDist w K < ENNReal.ofReal (r / R)} := by
  have hR0 : ENNReal.ofReal R ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  have hr : ENNReal.ofReal r = ENNReal.ofReal R * ENNReal.ofReal (r / R) := by
    rw [← ENNReal.ofReal_mul hR.le, mul_div_cancel₀ r hR.ne']
  have hset : {z | Metric.infEDist z (similarity a R hR ⁻¹' K) < ENNReal.ofReal r} =
      similarity a R hR ⁻¹' {w | Metric.infEDist w K < ENNReal.ofReal (r / R)} := by
    ext z
    rw [mem_ofPred_eq, mem_preimage, mem_ofPred_eq, fsimb2_infEDist_preimage_similarity, hr,
      ENNReal.mul_lt_mul_iff_right hR0 ENNReal.ofReal_ne_top]
  have hmeas : MeasurableSet {w | Metric.infEDist w K < ENNReal.ofReal (r / R)} :=
    (Metric.isOpen_thickening (δ := r / R) (E := K)).measurableSet
  rw [hset, ← Measure.map_apply (similarity a R hR).measurable hmeas,
    map_similarity_parabolicVolume, Measure.smul_apply, smul_eq_mul]

end ParabolicRectifiability.Foundations
