import ParabolicRectifiability.BetaP.Proofs.Counterexamples.RowStatements
import ParabolicRectifiability.BetaP.Proofs.Laws.Measurability

/-! # Uniform `S_p` tails on a compact set

Proves `c2_uniform_tails : C2UniformTailsStatement`.

Proof:
* `f_m = energyS ω k T p (1/(m+1))` is Borel in the centre by
  `cfit_measurable_energyS` (the energy half of `cfit_betaPowMeasurability_proof`; a finite
  `ω` is finite on compacts by instances);
* `f_m ≤ S_p^1` (monotonicity of the endpoint, `c2_energyS_mono_endpoint`) and `f_m ↓ 0` on `A`
  (`tendsto_measure_iInter_atTop` for `scaleMeasure.withDensity (B_p^{2/p})`);
* Egorov `MeasureTheory.tendstoUniformlyOn_of_ae_tendsto'` on the real parts, with exceptional
  mass at most `ω(A)/2`;
* a compact `K` of positive mass inside the measurable full subset `(toMeasurable ω Aᶜ)ᶜ ⊆ A`
  minus the exceptional set (`MeasurableSet.exists_lt_isCompact_of_ne_top`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- `S_p^a(y)` is monotone in the endpoint `a`. -/
theorem c2_energyS_mono_endpoint {n : ℕ} (ω : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (p : ℝ) (y : Space n) {a b : ℝ} (hab : a ≤ b) :
    energyS ω k T p a y ≤ energyS ω k T p b y :=
  lintegral_mono_set (Ioo_subset_Ioo_right hab)

theorem c2_one_div_succ_pos (m : ℕ) : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity

theorem c2_one_div_succ_le_one (m : ℕ) : 1 / ((m : ℝ) + 1) ≤ 1 := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [div_le_one (by positivity)]
  linarith

/-- For `S_p^1(y) < ∞`, the tails `S_p^{1/(m+1)}(y)` tend to `0`. -/
theorem c2_energyS_tendsto_zero {n : ℕ} (ω : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (p : ℝ) (y : Space n) (hy : energyS ω k T p 1 y < ⊤) :
    Tendsto (fun m : ℕ => energyS ω k T p (1 / ((m : ℝ) + 1)) y) atTop (𝓝 0) := by
  let ν : Measure ℝ := scaleMeasure.withDensity fun r => betaPow ω k T p y r ^ (2 / p)
  have hE : ∀ a : ℝ, energyS ω k T p a y = ν (Ioo 0 a) := fun a => by
    show _ = scaleMeasure.withDensity (fun r => betaPow ω k T p y r ^ (2 / p)) (Ioo 0 a)
    rw [withDensity_apply _ measurableSet_Ioo]
    rfl
  have hanti : Antitone fun m : ℕ => Ioo (0 : ℝ) (1 / ((m : ℝ) + 1)) := fun i j hij =>
    Ioo_subset_Ioo_right (Nat.one_div_le_one_div hij)
  have hinter : (⋂ m : ℕ, Ioo (0 : ℝ) (1 / ((m : ℝ) + 1))) = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun r hr => ?_
    rw [mem_iInter] at hr
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (hr 0).1
    exact lt_asymm hm (hr m).2
  have hfin : ∃ m : ℕ, ν (Ioo (0 : ℝ) (1 / ((m : ℝ) + 1))) ≠ ⊤ := by
    refine ⟨0, ?_⟩
    rw [← hE]
    simpa using hy.ne
  have h := tendsto_measure_iInter_atTop (fun _ => measurableSet_Ioo.nullMeasurableSet) hanti hfin
  rw [hinter, measure_empty] at h
  exact h.congr fun m => (hE _).symm

/-- Egorov with compact inner approximation (`C2UniformTailsStatement`). -/
theorem c2_uniform_tails_proof : C2UniformTailsStatement := by
  intro n _hn k _hk _hkn T _hT ω _hω p hp A hA hApos hfin
  have hf_meas : ∀ m : ℕ, Measurable (energyS ω k T p (1 / ((m : ℝ) + 1))) := fun m =>
    cfit_measurable_energyS ω k T hp.le _
  have hf_lt : ∀ (m : ℕ) (y : Space n), y ∈ A → energyS ω k T p (1 / ((m : ℝ) + 1)) y ≠ ⊤ :=
    fun m y hy => ((c2_energyS_mono_endpoint ω k T p y (c2_one_div_succ_le_one m)).trans_lt
      (hfin y hy)).ne
  -- almost-everywhere convergence of the real parts to `0`
  have hAae : ∀ᵐ y ∂ω, y ∈ A := mem_ae_iff.mpr hA
  have hae : ∀ᵐ y ∂ω, Tendsto (fun m : ℕ => (energyS ω k T p (1 / ((m : ℝ) + 1)) y).toReal)
      atTop (𝓝 ((fun _ : Space n => (0 : ℝ)) y)) := by
    filter_upwards [hAae] with y hy
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (c2_energyS_tendsto_zero ω k T p y (hfin y hy))
    rw [ENNReal.toReal_zero] at h
    exact h
  have hA0 : ω A ≠ 0 := hApos.ne'
  have hAtop : ω A ≠ ⊤ := measure_ne_top ω A
  -- Egorov
  obtain ⟨t, htm, ht, hunif⟩ := tendstoUniformlyOn_of_ae_tendsto' (μ := ω)
    (f := fun (m : ℕ) (y : Space n) => (energyS ω k T p (1 / ((m : ℝ) + 1)) y).toReal)
    (g := fun _ => (0 : ℝ))
    (fun m => (hf_meas m).ennreal_toReal.stronglyMeasurable) stronglyMeasurable_const hae
    (ENNReal.half_pos hA0)
  -- a measurable full subset of `A`, minus the exceptional set
  have hA'm : MeasurableSet (toMeasurable ω Aᶜ)ᶜ := (measurableSet_toMeasurable ω Aᶜ).compl
  have hA'A : (toMeasurable ω Aᶜ)ᶜ ⊆ A := fun y hy => by
    by_contra hyA
    exact hy (subset_toMeasurable ω Aᶜ hyA)
  have hBm : MeasurableSet ((toMeasurable ω Aᶜ)ᶜ \ t) := hA'm.diff htm
  have hAB : ω A ≤ ω ((toMeasurable ω Aᶜ)ᶜ \ t) + ω t := by
    calc ω A ≤ ω (((toMeasurable ω Aᶜ)ᶜ \ t ∪ t) ∪ toMeasurable ω Aᶜ) := by
          refine measure_mono fun y _ => ?_
          by_cases h1 : y ∈ toMeasurable ω Aᶜ
          · exact Or.inr h1
          · by_cases h2 : y ∈ t
            · exact Or.inl (Or.inr h2)
            · exact Or.inl (Or.inl ⟨h1, h2⟩)
      _ ≤ ω ((toMeasurable ω Aᶜ)ᶜ \ t ∪ t) + ω (toMeasurable ω Aᶜ) := measure_union_le _ _
      _ = ω ((toMeasurable ω Aᶜ)ᶜ \ t ∪ t) := by rw [measure_toMeasurable, hA, add_zero]
      _ ≤ ω ((toMeasurable ω Aᶜ)ᶜ \ t) + ω t := measure_union_le _ _
  have hBpos : 0 < ω ((toMeasurable ω Aᶜ)ᶜ \ t) := by
    rw [pos_iff_ne_zero]
    intro h0
    have hle : ω A ≤ ω A / 2 := by
      calc ω A ≤ ω ((toMeasurable ω Aᶜ)ᶜ \ t) + ω t := hAB
        _ = ω t := by rw [h0, zero_add]
        _ ≤ ω A / 2 := ht
    exact absurd hle (not_le.mpr (ENNReal.half_lt_self hA0 hAtop))
  -- compact inner approximation
  obtain ⟨K, hKB, hKc, hKpos⟩ := hBm.exists_lt_isCompact_of_ne_top (measure_ne_top ω _) hBpos
  have hKA : K ⊆ A := fun y hy => hA'A (hKB hy).1
  have hKt : K ⊆ tᶜ := fun y hy => (hKB hy).2
  refine ⟨K, hKc, hKA, hKpos, fun M hM => ?_⟩
  obtain ⟨m, hm⟩ := (Metric.tendstoUniformlyOn_iff.mp hunif M hM).exists
  refine ⟨1 / ((m : ℝ) + 1), c2_one_div_succ_pos m, fun y hy => ?_⟩
  have hd := hm y (hKt hy)
  simp only [Real.dist_eq, zero_sub, abs_neg] at hd
  rw [ENNReal.le_ofReal_iff_toReal_le (hf_lt m y (hKA hy)) hM.le]
  exact (le_abs_self _).trans hd.le

end ParabolicRectifiability.BetaP
