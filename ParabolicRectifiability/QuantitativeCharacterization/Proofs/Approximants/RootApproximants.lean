import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Approximants.ComponentTheorems
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Approximants.MultiplicityBasics
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Trace.ComponentTheorems
import ParabolicRectifiability.Foundations.Proofs.Rectifiability.SumsFromRestrictions

/-! # Root approximants and their canonical limits

Assembly of the root approximants from the intermediate lemmas on factorial moments, the
exponential tail, the typed split, local absolute continuity, trace carriage, reference-null
transfer and canonical identification, together with the rectifiability of absolutely continuous
restrictions and of countable sums (`f2i_isRegularlyRectifiableMeasure_of_absolutelyContinuous`,
`f2i_isRegularlyRectifiableMeasure_sum`).

* `dp2_typedTrace_restrict_rectifiable`: for `ν ≪ H_P^k` and Borel `F` inside the typed trace of
  type `T`, `ν⌊F` is typed rectifiable of type `T` (`dp2_restrict_carrier_rectifiable` on each
  reference of type `T`, then the cover lemma; reference exceptional null sets are `μ`-null too).
* `dp2_approximant_rectifiable`: the approximants of a typed split, through
  `dp2_local_absolute_continuity`.
* `dp2_restrict_rectifiable_of_layers`: if every approximant `μ⌊(F ∩ {m ≤ N})` is typed
  rectifiable and `m < ∞` a.e. on `F`, then so is `μ⌊F` (decomposition into multiplicity layers,
  through the domination `μ⌊F ≤ Σ_N μ⌊F⌊{m ≤ N}`; no exact sum identity needed).
* `dp2_exists_root_approximants`: has exactly the type of `exists_root_approximants`.
* `dp2_approximant_canonical_limits`: has exactly the type of `approximant_canonical_limits`; it
  passes the two rectifiability lemmas above to `dp2_canonical_identification`, which takes them
  as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- Reference-null transfer on a typed trace: for `ν ≪ H_P^k` and a Borel `F` inside the typed
trace of type `T`, `ν⌊F` is regularly rectifiable of type `T`. `dp2_restrict_carrier_rectifiable`
applies to `ν⌊F` on the carrier of each reference of type `T`; these carriers cover `F`. -/
theorem dp2_typedTrace_restrict_rectifiable {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hkn : k ≤ n + 2) {K L : ℝ} (hL : 1 ≤ L) {μ : Measure (Space n)} {a : Space n} {R : ℝ}
    (𝒞 : RegularMixedCovering k K L μ a R)
    (hcov1 : ∀ ρ : Reference n k L, HasTypedMeasureCover ρ.kind k ρ.measure 1)
    (ν : Measure (Space n)) (hν : ν ≪ hausdorffP n k) (T : FamilyKind) (F : Set (Space n))
    (hF : MeasurableSet F) (hFT : F ⊆ 𝒞.typedTrace T) :
    IsRegularlyRectifiableMeasure T k (ν.restrict F) := by
  refine f2i_isRegularlyRectifiableMeasure_of_restrict_cover T
    (fun j : {i : 𝒞.index // (𝒞.reference i).kind = T} => (𝒞.reference j.1).carrier) ?_ ?_
  · rw [Measure.restrict_apply' hF]
    refine measure_mono_null (fun z hz => ?_) (measure_empty (μ := ν))
    obtain ⟨hzU, hzF⟩ := hz
    have hzT := hFT hzF
    simp only [RegularMixedCovering.typedTrace, Set.mem_iUnion, Set.mem_inter_iff] at hzT
    obtain ⟨i, hi, -, hzc⟩ := hzT
    exact (hzU (Set.mem_iUnion.2 ⟨⟨i, hi⟩, hzc⟩)).elim
  · intro j
    have h := dp2_restrict_carrier_rectifiable n hn k hk hkn L hL (𝒞.reference j.1) (hcov1 _)
      (ν.restrict F) ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hν)
    rw [j.2] at h
    exact h

/-- The approximants of a Borel `F ⊆ P₀` inside the typed trace of type `T` are typed rectifiable
of type `T`, given `μ⌊P₀ ≪ H_P^k` (`dp2_local_absolute_continuity`) and the typed reference covers at tolerance `1`. -/
theorem dp2_approximant_rectifiable {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n + 2)
    {K L : ℝ} (hL : 1 ≤ L) {μ : Measure (Space n)} {a : Space n} {R : ℝ}
    (𝒞 : RegularMixedCovering k K L μ a R)
    (hcov1 : ∀ ρ : Reference n k L, HasTypedMeasureCover ρ.kind k ρ.measure 1)
    (hac : μ.restrict (Metric.ball a R) ≪ hausdorffP n k) (T : FamilyKind) (F : Set (Space n))
    (hF : MeasurableSet F) (hFP : F ⊆ Metric.ball a R) (hFT : F ⊆ 𝒞.typedTrace T) (N : ℕ) :
    IsRegularlyRectifiableMeasure T k (𝒞.approximant F N) := by
  have hsub : F ∩ {z | 𝒞.multiplicity z ≤ (N : ℕ∞)} ⊆ Metric.ball a R :=
    Set.inter_subset_left.trans hFP
  have heq : 𝒞.approximant F N =
      (μ.restrict (Metric.ball a R)).restrict (F ∩ {z | 𝒞.multiplicity z ≤ (N : ℕ∞)}) :=
    (Measure.restrict_restrict_of_subset hsub).symm
  rw [heq]
  exact dp2_typedTrace_restrict_rectifiable hn hk hkn hL 𝒞 hcov1 _ hac T _
    (hF.inter (dp2_measurableSet_multiplicity_le 𝒞 N)) (Set.inter_subset_left.trans hFT)

/-- Multiplicity layers: typed rectifiable approximants of a Borel `F ⊆ P₀` with `m < ∞` a.e. on
`P₀` give a typed rectifiable `μ⌊F`, by the cover lemma over the Borel sets `{m ≤ N}`
(`f2i_isRegularlyRectifiableMeasure_sum`, then
`f2i_isRegularlyRectifiableMeasure_of_absolutelyContinuous`). -/
theorem dp2_restrict_rectifiable_of_layers {n k : ℕ} {K L : ℝ} {μ : Measure (Space n)}
    {a : Space n} {R : ℝ} (𝒞 : RegularMixedCovering k K L μ a R)
    (hfm : ∀ᵐ z ∂μ, z ∈ Metric.ball a R → 𝒞.multiplicity z < ⊤) (T : FamilyKind)
    (F : Set (Space n)) (hF : MeasurableSet F) (hFP : F ⊆ Metric.ball a R)
    (hrect : ∀ N : ℕ, IsRegularlyRectifiableMeasure T k (𝒞.approximant F N)) :
    IsRegularlyRectifiableMeasure T k (μ.restrict F) := by
  refine f2i_isRegularlyRectifiableMeasure_of_restrict_cover T
    (fun N : ℕ => {z | 𝒞.multiplicity z ≤ (N : ℕ∞)}) ?_ ?_
  · rw [Measure.restrict_apply' hF]
    refine measure_mono_null (fun z hz => ?_) (ae_iff.1 hfm)
    obtain ⟨hzU, hzF⟩ := hz
    have htop : 𝒞.multiplicity z = ⊤ := by
      by_contra hne
      obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 hne
      exact hzU (Set.mem_iUnion.2 ⟨N, le_of_eq hN.symm⟩)
    show ¬(z ∈ Metric.ball a R → 𝒞.multiplicity z < ⊤)
    intro h
    exact (h (hFP hzF)).ne htop
  · intro N
    have heq : (μ.restrict F).restrict {z | 𝒞.multiplicity z ≤ (N : ℕ∞)} =
        𝒞.approximant F N := by
      show _ = μ.restrict (F ∩ {z | 𝒞.multiplicity z ≤ (N : ℕ∞)})
      rw [Measure.restrict_restrict' hF, Set.inter_comm]
    rw [heq]
    exact hrect N

/-- **Root approximants** (the statement of `exists_root_approximants`). Model-ball growth
(`dp2_ball_growth_of_local`), factorial moments (`dp2_factorial_moments`), finite multiplicity
(`dp2_ae_multiplicity_lt_top`), trace carriage (`dp2_trace_carriage`), the typed split and measure
identity (`dp2_typed_split`), local absolute continuity and reference-null transfer (typed
rectifiable approximants), and the exponential tail (`dp2_exponential_tail`) with its two
specializations (relative tail `2^k + A²`, absolute tail `max(2A, 2^k + 1)`). -/
theorem dp2_exists_root_approximants :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ A : ℝ, 1 ≤ A → ∀ L : ℝ, 1 ≤ L →
    (∀ ρ : Reference n k L, ∀ ε : ℝ, 0 < ε → HasTypedMeasureCover ρ.kind k ρ.measure ε) →
    ∀ K : ℝ, 1 ≤ K → ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → ∀ 𝒞 : RegularMixedCovering k K L μ a R,
      (∀ b ∈ μ.support ∩ Metric.ball a (2 * L * R), ∀ s : ℝ, 0 < s → s ≤ 2 * L * R →
        μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k)) →
      ∃ FH FV : Set (Space n), 𝒞.IsTypedTraceSplit FH FV ∧ 𝒞.MeasureIdentity FH FV ∧
        (∀ N : ℕ, IsRegularlyRectifiableMeasure .horizontal k (𝒞.approximant FH N) ∧
          IsRegularlyRectifiableMeasure .vertical k (𝒞.approximant FV N)) ∧
        (ENNReal.ofReal (A⁻¹ * R ^ k) ≤ μ (Metric.ball a R) →
          𝒞.RelativeTail ((2 : ℝ) ^ k + A ^ 2)) ∧
        ∀ N : ℕ, 𝒞.residual N (Metric.ball a R) ≤
          ENNReal.ofReal (max (2 * A) ((2 : ℝ) ^ k + 1) * R ^ k *
            Real.exp (-(N : ℝ) / (max (2 * A) ((2 : ℝ) ^ k + 1) * K))) := by
  intro n hn k hk hkn A hA L hL hcov K hK μ hfin hreg a ha R hR 𝒞 hgrowth
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hball := dp2_ball_growth_of_local 𝒞 hA0 hL hR hgrowth
  have hmom := dp2_factorial_moments n k K L A μ a R 𝒞 hball
  have hfm := dp2_ae_multiplicity_lt_top 𝒞 (hmom 1 le_rfl)
  have htr := dp2_trace_carriage n k K L hL μ hfin hreg a R 𝒞 hfm
  obtain ⟨FH, FV, hs, hid⟩ := dp2_typed_split n k K L hL μ a R 𝒞 htr
  have hac := dp2_local_absolute_continuity n hn k hk hkn A L hL μ hfin hreg a R hR hgrowth
  have htail := dp2_exponential_tail n k K L A μ a R 𝒞 (by linarith) hmom
  have hcov1 : ∀ ρ : Reference n k L, HasTypedMeasureCover ρ.kind k ρ.measure 1 :=
    fun ρ => hcov ρ 1 one_pos
  have hLR : 0 < L * R := mul_pos (by linarith) hR
  have hRLR : R ≤ L * R := le_mul_of_one_le_left hR.le hL
  have hroot : μ (Metric.ball a R) ≤ ENNReal.ofReal (A * R ^ k) :=
    hgrowth a ⟨ha, Metric.mem_ball_self (by linarith)⟩ R hR (by linarith)
  refine ⟨FH, FV, hs, hid, fun N => ⟨?_, ?_⟩,
    fun hlow => dp2_relativeTail_of_exponentialTail 𝒞 hA hK htail hlow,
    dp2_absoluteTail_of_exponentialTail 𝒞 hA hK hR htail hroot⟩
  · exact dp2_approximant_rectifiable hn hk hkn hL 𝒞 hcov1 hac .horizontal FH
      hs.measurable_horizontal hs.horizontal_subset_root hs.horizontal_subset_trace N
  · exact dp2_approximant_rectifiable hn hk hkn hL 𝒞 hcov1 hac .vertical FV
      hs.measurable_vertical hs.vertical_subset_root hs.vertical_subset_trace N

/-- **Canonical limits of the approximants** (the statement of `approximant_canonical_limits`).
Model-ball growth (`dp2_ball_growth_of_global`), the first factorial moment and
`dp2_ae_multiplicity_lt_top` (finite multiplicity), multiplicity layers
(`dp2_restrict_rectifiable_of_layers`: the limits `μ⌊F_H`, `μ⌊F_V` are typed rectifiable),
canonical uniqueness (`dp2_canonical_identification`, which receives the two rectifiability
lemmas as hypotheses here) and the monotone limits with antitone residual
(`dp2_approximant_limits`). -/
theorem dp2_approximant_canonical_limits :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ A L K : ℝ, 1 ≤ L → 1 ≤ K →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    IntegralCanonical.IsCanonicalDecomposition k μ 1 →
    (∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k)) →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → ∀ 𝒞 : RegularMixedCovering k K L μ a R,
    ∀ FH FV : Set (Space n), 𝒞.IsTypedTraceSplit FH FV →
    (∀ N : ℕ, IsRegularlyRectifiableMeasure .horizontal k (𝒞.approximant FH N) ∧
      IsRegularlyRectifiableMeasure .vertical k (𝒞.approximant FV N)) →
      𝒞.HasCanonicalLimits FH FV := by
  intro n _ k _ _ A L K _ _ μ hfin _ hcan hgrowth a _ R _ 𝒞 FH FV hs hrect
  have hball := dp2_ball_growth_of_global 𝒞 hgrowth
  have hfm := dp2_ae_multiplicity_lt_top 𝒞 (dp2_factorial_moments n k K L A μ a R 𝒞 hball 1 le_rfl)
  obtain ⟨hlimF, hanti, hres⟩ := dp2_approximant_limits n k K L μ a R 𝒞 hfin hfm
  have hH : IsRegularlyRectifiableMeasure .horizontal k (μ.restrict FH) :=
    dp2_restrict_rectifiable_of_layers 𝒞 hfm .horizontal FH hs.measurable_horizontal
      hs.horizontal_subset_root fun N => (hrect N).1
  have hV : IsRegularlyRectifiableMeasure .vertical k (μ.restrict FV) :=
    dp2_restrict_rectifiable_of_layers 𝒞 hfm .vertical FV hs.measurable_vertical
      hs.vertical_subset_root fun N => (hrect N).2
  obtain ⟨hidH, hidV⟩ := dp2_canonical_identification
    (@f2i_isRegularlyRectifiableMeasure_of_absolutelyContinuous_proof)
    (@f2i_isRegularlyRectifiableMeasure_sum_proof)
    n k μ hcan (Metric.ball a R) FH FV
    measurableSet_ball hs.measurable_horizontal hs.measurable_vertical
    hs.disjoint hs.horizontal_subset_root hs.vertical_subset_root
    hs.null_remainder hH hV
  obtain ⟨hmonH, htH⟩ := hlimF FH hs.horizontal_subset_root
  obtain ⟨hmonV, htV⟩ := hlimF FV hs.vertical_subset_root
  exact
    { horizontal_rectifiable := fun N => (hrect N).1
      vertical_rectifiable := fun N => (hrect N).2
      horizontal_monotone := hmonH
      vertical_monotone := hmonV
      horizontal_tendsto := fun S hS => by rw [← hidH]; exact htH S hS
      vertical_tendsto := fun S hS => by rw [← hidV]; exact htV S hS
      residual_antitone := hanti
      residual_tendsto_zero := hres }

end ParabolicRectifiability.QuantitativeCharacterization
