import ParabolicRectifiability.Enhancements.Assembly.ScalingRates
import ParabolicRectifiability.Enhancements.Statements.Density
import ParabolicRectifiability.Foundations.Statements.DensityBridges
import ParabolicRectifiability.Characterization.Statements.Branches

/-! # Assembly of the density corollaries

Main theorems (implication form over the statements they use):

* `density_three_parts_of_providers : … → DensityThreePartsStatement`;
* `density_rectifiable_reifenberg_of_providers : … → DensityRectifiableReifenbergStatement`;
* `density_scaling_of_providers : … → DensityScalingStatement`.

Proof assembly:

* the decomposition is the power rate with `q = 1` (integrated versions), the scaled
  threshold property (local weak versions), or the parabolic rectifiable Reifenberg theorem itself (unit weak version);
* mass bound: `PackingMassStatement` on `K ∩ P(q,R)` (packing from the
  support bundle), plus `μ(E_T \ K_T) = 0` for actual supports (`density_mass_le`);
* Hausdorff bound: `H_P^k(F) ≤ H_P^k(K) + H_P^k(F \ K)`, the second term by the
  density identity off the closed carrier and `UpperDensityDominationStatement`
  applied to the remainder `μ⁺`, locally Radon by `RestrictLocallyRadonStatement`
  (`density_hausdorff_levelSet_le`);
* set rectifiability of `F`: domination `H_P^k⌊F ≤ (C_k/a) μ` (upper domination), energy
  transfer (`BetaEnergyDominationStatement`) and the finite-Hausdorff criterion
  (`density_levelSet_rectifiable`);
* measure rectifiability: `ACBridgeStatement`, then the graph exceptions
  of `F` are `μ⌊U`-null (`measure_rectifiable_of_set`);
* local scales: every input is stated at an arbitrary centre and scale, so the local
  versions are assembled directly from the scaled decompositions.

One dimensional constant `5^{n+2} (1 + C₀)(1 + C_u)` absorbs the packing factor `5^k`,
the core constant `C₀` and a uniform upper-domination constant `C_u` for `k ≤ n+2`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Enhancements

open ParabolicRectifiability.Foundations
open ParabolicRectifiability.Characterization (FiniteHausdorffCriterionStatement)

/-! ## A uniform upper-domination constant -/

/-- The domination inequality of `UpperDensityDominationStatement` for one dimension `k`
with constant `C`. -/
def UpperDominationBound (n k : ℕ) (C : ℝ) : Prop :=
  ∀ O : Set (Space n), IsOpen O → Bornology.IsBounded O →
  ∀ F : Set (Space n), MeasurableSet F → F ⊆ O →
  ∀ a : ℝ, 0 < a →
  ∀ ρ : Measure (Space n), IsFiniteMeasureOnCompacts ρ → ρ.InnerRegular →
    (∀ z ∈ F, ENNReal.ofReal a ≤ upperDensity ρ k z) →
    ∀ B : Set (Space n), MeasurableSet B →
      hausdorffP n k (F ∩ B) ≤ ENNReal.ofReal (C / a) * ρ (F ∩ B)

theorem upperDominationBound_mono {n k : ℕ} {C C' : ℝ} (h : UpperDominationBound n k C)
    (hC : C ≤ C') : UpperDominationBound n k C' :=
  fun O hO hOb F hF hFO a ha ρ hρ hρr hden B hB =>
    (h O hO hOb F hF hFO a ha ρ hρ hρr hden B hB).trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hC ha.le)) le_rfl)

/-- One constant for all `1 ≤ k ≤ n+2` (the Foundations constant depends on `k`). -/
theorem exists_uniform_upperDominationBound (hUD : UpperDensityDominationStatement) (n : ℕ)
    (hn : 1 ≤ n) :
    ∃ Cu : ℝ, 0 < Cu ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → UpperDominationBound n k Cu := by
  suffices h : ∀ m : ℕ, ∃ Cu : ℝ, 0 < Cu ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ m → k ≤ n + 2 → UpperDominationBound n k Cu by
    obtain ⟨Cu, hCu, h⟩ := h (n + 2)
    exact ⟨Cu, hCu, fun k hk hkn => h k hk hkn hkn⟩
  intro m
  induction m with
  | zero => exact ⟨1, one_pos, fun k hk hk0 _ => absurd hk (by omega)⟩
  | succ m ih =>
    obtain ⟨Cu, hCu, hm⟩ := ih
    obtain ⟨Ck, hCk, hk⟩ := hUD (m + 1) (by omega)
    refine ⟨Cu + Ck, by linarith, fun k hk1 hkm hkn => ?_⟩
    rcases Nat.lt_or_ge k (m + 1) with hlt | hge
    · exact upperDominationBound_mono (hm k hk1 (by omega) hkn) (by linarith)
    · obtain rfl : k = m + 1 := by omega
      refine upperDominationBound_mono ?_ (by linarith : Ck ≤ Cu + Ck)
      intro O hO hOb F hF hFO a ha ρ hρ hρr hden B hB
      exact ((hk n hn hkn O hO hOb F hF hFO a ha ρ hρ hρr hden).1 B hB).1

/-! ## Elementary measure facts -/

/-- The density level set is Borel (`DensityMeasurabilityStatement`). -/
theorem measurableSet_upperDensityLevelSet (hDM : DensityMeasurabilityStatement) {n k : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n + 2) {μ : Measure (Space n)}
    (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular) {O : Set (Space n)}
    (hO : MeasurableSet O) (a : ℝ) : MeasurableSet (upperDensityLevelSet μ k O a) :=
  hO.inter (measurableSet_le measurable_const (hDM n hn k hk hkn μ hμ hreg).2)

/-- An a.e. upper-density bound on `O` makes the level set a full `μ⌊O` carrier. -/
theorem levelSet_carrier {n k : ℕ} {μ : Measure (Space n)} {O : Set (Space n)}
    (hO : MeasurableSet O) {a : ℝ}
    (hup : ∀ᵐ z ∂μ, z ∈ O → ENNReal.ofReal a ≤ upperDensity μ k z) :
    μ.restrict O (upperDensityLevelSet μ k O a)ᶜ = 0 := by
  rw [Measure.restrict_apply' hO]
  refine measure_mono_null ?_ (ae_iff.mp hup)
  rintro z ⟨hzF, hzO⟩ h
  exact hzF ⟨hzO, h hzO⟩

/-- Finite integrated energy gives finite square function a.e. on the cylinder. -/
theorem ae_squareEnergy_lt_top_of_localSquareEnergy {n k : ℕ} {μ : Measure (Space n)}
    (hμ : IsFiniteMeasureOnCompacts μ) {q : Space n} {R : ℝ}
    (h : localSquareEnergy μ k .mixed q R < ⊤) :
    ∀ᵐ z ∂μ, z ∈ Metric.ball q R → squareEnergy μ k .mixed (2 * R) z < ⊤ :=
  (ae_restrict_iff' measurableSet_ball).mp
    (ae_lt_top (measurable_squareEnergy μ k .mixed (2 * R)) h.ne)

/-- Subsets of regularly rectifiable sets are regularly rectifiable. -/
theorem isRegularlyRectifiableSet_mono {n k : ℕ} {E F : Set (Space n)} (hEF : E ⊆ F)
    (hF : IsRegularlyRectifiableSet .mixed k F) : IsRegularlyRectifiableSet .mixed k E := by
  intro ε hε
  obtain ⟨I, J, H, V, h0⟩ := hF ε hε
  exact ⟨I, J, H, V, measure_mono_null (sdiff_subset_sdiff_left hEF) h0⟩

/-- Absolute continuity, a full carrier and set rectifiability of the
carrier give measure rectifiability with covers at every positive tolerance. -/
theorem measure_rectifiable_of_set {n k : ℕ} {ν : Measure (Space n)} {F : Set (Space n)}
    (hAC : ν ≪ hausdorffP n k) (hcar : ν Fᶜ = 0) (hF : IsRegularlyRectifiableSet .mixed k F) :
    IsRegularlyRectifiableMeasure .mixed k ν ∧
      ∀ ε : ℝ, 0 < ε → HasTypedMeasureCover .mixed k ν ε := by
  have hcov : ∀ ε : ℝ, 0 < ε → HasTypedMeasureCover .mixed k ν ε := by
    intro ε hε
    obtain ⟨I, J, H, V, h0⟩ := hF ε hε
    refine ⟨I, J, H, V, measure_mono_null (fun z hz => ?_) (measure_union_null hcar (hAC h0))⟩
    by_cases hzF : z ∈ F
    · exact Or.inr ⟨hzF, hz⟩
    · exact Or.inl hzF
  refine ⟨⟨hAC, ?_⟩, hcov⟩
  obtain ⟨I, J, H, V, h⟩ := hcov 1 one_pos
  exact ⟨I, J, fun _ => 1, H, fun _ => 1, V, h⟩

/-- `ACBridgeStatement` applied on a cylinder with endpoint `2R`. -/
theorem density_absolutelyContinuous (hAC : ACBridgeStatement) {n k : ℕ} (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hkn : k ≤ n + 2) {μ : Measure (Space n)} (hμ : IsFiniteMeasureOnCompacts μ)
    (hreg : μ.InnerRegular) {q : Space n} {R A : ℝ} (hR : 0 < R)
    (hlow : ∀ᵐ z ∂μ, z ∈ Metric.ball q R → lowerDensity μ k z ≤ ENNReal.ofReal A)
    (hfin : ∀ᵐ z ∂μ, z ∈ Metric.ball q R → squareEnergy μ k .mixed (2 * R) z < ⊤) :
    μ.restrict (Metric.ball q R) ≪ hausdorffP n k :=
  hAC n hn k hk hkn _ Metric.isOpen_ball μ hμ hreg (2 * R) (by positivity) .mixed
    (AdmissibleModel.nonempty_of_range hn hk hkn)
    ((hlow.and hfin).mono fun _ hz hzB => ⟨(hz.1 hzB).trans_lt ENNReal.ofReal_lt_top, hz.2 hzB⟩)

/-! ## Mass and Hausdorff bounds of a restriction decomposition -/

/-- Packing turns a lower-density bound into mass on
the retained supports (`PackingMassStatement` on `K ∩ P(q,R)`); the actual supports carry
the retained restrictions. -/
theorem density_mass_le (hPM : PackingMassStatement) {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hkn : k ≤ n + 2) {μ : Measure (Space n)} (hμ : IsFiniteMeasureOnCompacts μ)
    (hreg : μ.InnerRegular) {q : Space n} {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    {EH EV : Set (Space n)}
    (hS : HasRegularSupportBounds k C q R (μ.restrict EH).support (μ.restrict EV).support)
    {A : ℝ} (hA : 0 ≤ A)
    (hlow : ∀ᵐ z ∂μ, z ∈ Metric.ball q R → lowerDensity μ k z ≤ ENNReal.ofReal A) :
    μ (Metric.ball q R) ≤
      μ.restrict (EH ∪ EV)ᶜ (Metric.ball q R) + ENNReal.ofReal (5 ^ k * C * A * R ^ k) := by
  have hKc : IsClosed ((μ.restrict EH).support ∪ (μ.restrict EV).support) :=
    Measure.isClosed_support.union Measure.isClosed_support
  have hK'm : MeasurableSet
      (((μ.restrict EH).support ∪ (μ.restrict EV).support) ∩ Metric.ball q R) :=
    hKc.measurableSet.inter measurableSet_ball
  have hpack := hPM n hn k hk hkn _ hK'm R C hR hC
    (fun q' ρ hρ hρR l z r hz hr hdisj =>
      hS.finite_packing q' ρ hρ hρR l z r (fun i => ⟨(hz i).1.1, (hz i).2⟩) hr hdisj)
    μ hμ hreg A hA (hlow.mono fun _ hz hzK => hz hzK.2) q R hR le_rfl
  rw [Measure.restrict_apply measurableSet_ball, inter_eq_right.mpr inter_subset_right]
    at hpack
  have hEH : μ (EH \ (μ.restrict EH).support) = 0 := by
    have h := Measure.measure_compl_support (μ := μ.restrict EH)
    rwa [Measure.restrict_apply Measure.isClosed_support.isOpen_compl.measurableSet,
      inter_comm, ← sdiff_eq] at h
  have hEV : μ (EV \ (μ.restrict EV).support) = 0 := by
    have h := Measure.measure_compl_support (μ := μ.restrict EV)
    rwa [Measure.restrict_apply Measure.isClosed_support.isOpen_compl.measurableSet,
      inter_comm, ← sdiff_eq] at h
  have hsub : Metric.ball q R ⊆ (Metric.ball q R ∩ (EH ∪ EV)ᶜ) ∪
      (((μ.restrict EH).support ∪ (μ.restrict EV).support) ∩ Metric.ball q R) ∪
      (EH \ (μ.restrict EH).support) ∪ (EV \ (μ.restrict EV).support) := by
    intro z hz
    by_cases hE : z ∈ EH ∪ EV
    · rcases hE with hH | hV
      · by_cases hzK : z ∈ (μ.restrict EH).support
        · exact Or.inl (Or.inl (Or.inr ⟨Or.inl hzK, hz⟩))
        · exact Or.inl (Or.inr ⟨hH, hzK⟩)
      · by_cases hzK : z ∈ (μ.restrict EV).support
        · exact Or.inl (Or.inl (Or.inr ⟨Or.inr hzK, hz⟩))
        · exact Or.inr ⟨hV, hzK⟩
    · exact Or.inl (Or.inl (Or.inl ⟨hz, hE⟩))
  calc μ (Metric.ball q R)
      ≤ μ (Metric.ball q R ∩ (EH ∪ EV)ᶜ) +
          μ (((μ.restrict EH).support ∪ (μ.restrict EV).support) ∩ Metric.ball q R) +
          μ (EH \ (μ.restrict EH).support) + μ (EV \ (μ.restrict EV).support) :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add
          ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) le_rfl))
    _ = μ.restrict (EH ∪ EV)ᶜ (Metric.ball q R) +
          μ (((μ.restrict EH).support ∪ (μ.restrict EV).support) ∩ Metric.ball q R) := by
        rw [hEH, hEV, add_zero, add_zero, Measure.restrict_apply measurableSet_ball]
    _ ≤ μ.restrict (EH ∪ EV)ᶜ (Metric.ball q R) + ENNReal.ofReal (5 ^ k * C * A * R ^ k) :=
        add_le_add le_rfl hpack

/-- Hausdorff part: the level set is controlled on the closed retained carrier by the support
bundle and off it by upper domination applied to the remainder `μ⁺`. -/
theorem density_hausdorff_levelSet_le (hRL : RestrictLocallyRadonStatement)
    (hDM : DensityMeasurabilityStatement) {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hkn : k ≤ n + 2) {μ : Measure (Space n)} (hμ : IsFiniteMeasureOnCompacts μ)
    (hreg : μ.InnerRegular) {q : Space n} {R C : ℝ} {EH EV : Set (Space n)}
    (hEH : MeasurableSet EH) (hEV : MeasurableSet EV)
    (hmeas : μ = μ.restrict (EH ∪ EV)ᶜ + μ.restrict EH + μ.restrict EV)
    (hS : HasRegularSupportBounds k C q R (μ.restrict EH).support (μ.restrict EV).support)
    {Cu : ℝ} (hUD : UpperDominationBound n k Cu) {a : ℝ} (ha : 0 < a) :
    hausdorffP n k (upperDensityLevelSet μ k (Metric.ball q R) a) ≤
      ENNReal.ofReal (C * R ^ k) +
        ENNReal.ofReal (Cu / a) * μ.restrict (EH ∪ EV)ᶜ (Metric.ball q R) := by
  have hFm := measurableSet_upperDensityLevelSet hDM hn hk hkn hμ hreg
    (measurableSet_ball (x := q) (ε := R)) a
  have hKc : IsClosed ((μ.restrict EH).support ∪ (μ.restrict EV).support) :=
    Measure.isClosed_support.union Measure.isClosed_support
  obtain ⟨hpc, hpr⟩ := hRL n hn μ hμ hreg _ (hEH.union hEV).compl
  have hsum : μ = μ.restrict (EH ∪ EV)ᶜ + (μ.restrict EH + μ.restrict EV) := by
    rw [← add_assoc]
    exact hmeas
  have hcarried : (μ.restrict EH + μ.restrict EV)
      ((μ.restrict EH).support ∪ (μ.restrict EV).support)ᶜ = 0 := by
    rw [Measure.add_apply,
      measure_mono_null (compl_subset_compl.mpr subset_union_left) Measure.measure_compl_support,
      measure_mono_null (compl_subset_compl.mpr subset_union_right) Measure.measure_compl_support,
      add_zero]
  have hden : ∀ z ∈ upperDensityLevelSet μ k (Metric.ball q R) a \
      ((μ.restrict EH).support ∪ (μ.restrict EV).support),
      ENNReal.ofReal a ≤ upperDensity (μ.restrict (EH ∪ EV)ᶜ) k z := by
    rintro z ⟨hzF, hzK⟩
    rw [upperDensity_eq_of_not_mem_closed_carrier k μ _ _ _ hKc hsum hcarried hzK]
    exact hzF.2
  have hout := hUD (Metric.ball q R) Metric.isOpen_ball Metric.isBounded_ball _
    (hFm.diff hKc.measurableSet) (sdiff_subset.trans inter_subset_left) a ha _ hpc hpr hden
    univ MeasurableSet.univ
  rw [inter_univ] at hout
  calc hausdorffP n k (upperDensityLevelSet μ k (Metric.ball q R) a)
      ≤ hausdorffP n k (upperDensityLevelSet μ k (Metric.ball q R) a ∩
            ((μ.restrict EH).support ∪ (μ.restrict EV).support)) +
        hausdorffP n k (upperDensityLevelSet μ k (Metric.ball q R) a \
            ((μ.restrict EH).support ∪ (μ.restrict EV).support)) :=
        measure_le_inter_add_sdiff _ _ _
    _ ≤ ENNReal.ofReal (C * R ^ k) +
        ENNReal.ofReal (Cu / a) * μ.restrict (EH ∪ EV)ᶜ (Metric.ball q R) :=
      add_le_add ((measure_mono inter_subset_right).trans hS.hausdorff_total)
        (hout.trans (mul_le_mul' le_rfl (measure_mono (sdiff_subset.trans inter_subset_left))))

/-- Both numerical bounds for a restriction decomposition with loss at most `L`. -/
theorem density_bounds_of_decomposition (hPM : PackingMassStatement)
    (hRL : RestrictLocallyRadonStatement) (hDM : DensityMeasurabilityStatement) {n k : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n + 2) {μ : Measure (Space n)}
    (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular) {q : Space n}
    {R C₀ Cu L : ℝ} (hR : 0 < R) (hC₀ : 0 ≤ C₀) (hCu : 0 ≤ Cu) (hL : 0 ≤ L)
    {EH EV : Set (Space n)} (hEH : MeasurableSet EH) (hEV : MeasurableSet EV)
    (hmeas : μ = μ.restrict (EH ∪ EV)ᶜ + μ.restrict EH + μ.restrict EV)
    (hS : HasRegularSupportBounds k C₀ q R (μ.restrict EH).support (μ.restrict EV).support)
    (hloss : μ.restrict (EH ∪ EV)ᶜ (Metric.ball q R) ≤ ENNReal.ofReal L)
    (hUD : UpperDominationBound n k Cu) :
    (∀ A : ℝ, 0 ≤ A →
      (∀ᵐ z ∂μ, z ∈ Metric.ball q R → lowerDensity μ k z ≤ ENNReal.ofReal A) →
      μ (Metric.ball q R) ≤ ENNReal.ofReal (L + 5 ^ k * C₀ * A * R ^ k)) ∧
    (∀ a : ℝ, 0 < a →
      hausdorffP n k (upperDensityLevelSet μ k (Metric.ball q R) a) ≤
        ENNReal.ofReal (C₀ * R ^ k + Cu / a * L)) := by
  refine ⟨fun A hA hlow => ?_, fun a ha => ?_⟩
  · calc μ (Metric.ball q R)
        ≤ μ.restrict (EH ∪ EV)ᶜ (Metric.ball q R) + ENNReal.ofReal (5 ^ k * C₀ * A * R ^ k) :=
          density_mass_le hPM hn hk hkn hμ hreg hR hC₀ hS hA hlow
      _ ≤ ENNReal.ofReal L + ENNReal.ofReal (5 ^ k * C₀ * A * R ^ k) := add_le_add hloss le_rfl
      _ = ENNReal.ofReal (L + 5 ^ k * C₀ * A * R ^ k) :=
          (ENNReal.ofReal_add hL (by positivity)).symm
  · calc hausdorffP n k (upperDensityLevelSet μ k (Metric.ball q R) a)
        ≤ ENNReal.ofReal (C₀ * R ^ k) +
            ENNReal.ofReal (Cu / a) * μ.restrict (EH ∪ EV)ᶜ (Metric.ball q R) :=
          density_hausdorff_levelSet_le hRL hDM hn hk hkn hμ hreg hEH hEV hmeas hS hUD ha
      _ ≤ ENNReal.ofReal (C₀ * R ^ k) + ENNReal.ofReal (Cu / a) * ENNReal.ofReal L :=
          add_le_add le_rfl (mul_le_mul' le_rfl hloss)
      _ = ENNReal.ofReal (C₀ * R ^ k + Cu / a * L) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]

/-- Rectifiability part: the level set is regularly rectifiable as a set, by domination,
energy transfer and the finite-Hausdorff criterion. -/
theorem density_levelSet_rectifiable (hFH : FiniteHausdorffCriterionStatement)
    (hBED : BetaEnergyDominationStatement) (hDM : DensityMeasurabilityStatement) {n k : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n + 2) {μ : Measure (Space n)}
    (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular) {q : Space n} {R : ℝ}
    (hR : 0 < R) {Cu : ℝ} (hCu : 0 < Cu) (hUD : UpperDominationBound n k Cu) {a : ℝ}
    (ha : 0 < a)
    (hfin : ∀ᵐ z ∂μ, z ∈ Metric.ball q R → squareEnergy μ k .mixed (2 * R) z < ⊤) :
    IsRegularlyRectifiableSet .mixed k (upperDensityLevelSet μ k (Metric.ball q R) a) := by
  have hFm := measurableSet_upperDensityLevelSet hDM hn hk hkn hμ hreg
    (measurableSet_ball (x := q) (ε := R)) a
  have hFO : upperDensityLevelSet μ k (Metric.ball q R) a ⊆ Metric.ball q R :=
    inter_subset_left
  have hdomF : ∀ B, MeasurableSet B →
      hausdorffP n k (upperDensityLevelSet μ k (Metric.ball q R) a ∩ B) ≤
        ENNReal.ofReal (Cu / a) * μ (upperDensityLevelSet μ k (Metric.ball q R) a ∩ B) :=
    hUD (Metric.ball q R) Metric.isOpen_ball Metric.isBounded_ball _ hFm hFO a ha μ hμ hreg
      (fun _ hz => hz.2)
  have hcpos : 0 < Cu / a := div_pos hCu ha
  have hle : (hausdorffP n k).restrict (upperDensityLevelSet μ k (Metric.ball q R) a) ≤
      ENNReal.ofReal (Cu / a) • μ := by
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.restrict_apply hs, Measure.smul_apply, smul_eq_mul, inter_comm]
    exact (hdomF s hs).trans (mul_le_mul' le_rfl (measure_mono inter_subset_right))
  have hFfin : hausdorffP n k (upperDensityLevelSet μ k (Metric.ball q R) a) < ⊤ := by
    have h := hdomF univ MeasurableSet.univ
    rw [inter_univ] at h
    exact h.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ((measure_mono hFO).trans_lt (measure_ball_lt_top μ q R)))
  have hE := (hBED n hn k hk hkn .mixed μ _ (Cu / a) hcpos hle).2 (2 * R) (by positivity)
  have hmeasS := measurable_squareEnergy μ k .mixed (2 * R)
  have hη : ∀ᵐ z ∂(hausdorffP n k).restrict (upperDensityLevelSet μ k (Metric.ball q R) a),
      squareEnergy μ k .mixed (2 * R) z < ⊤ := by
    rw [ae_iff, Measure.restrict_apply' hFm, inter_comm]
    have hBm : MeasurableSet {z | ¬ squareEnergy μ k .mixed (2 * R) z < ⊤} :=
      (measurableSet_lt hmeasS measurable_const).compl
    have hnull : μ (upperDensityLevelSet μ k (Metric.ball q R) a ∩
        {z | ¬ squareEnergy μ k .mixed (2 * R) z < ⊤}) = 0 := by
      refine measure_mono_null ?_ (ae_iff.mp hfin)
      intro z hz h
      exact hz.2 (h (hFO hz.1))
    refine le_antisymm ((hdomF _ hBm).trans (le_of_eq ?_)) zero_le
    rw [hnull, mul_zero]
  have hηS : ∀ᵐ z ∂(hausdorffP n k).restrict (upperDensityLevelSet μ k (Metric.ball q R) a),
      squareEnergy ((hausdorffP n k).restrict (upperDensityLevelSet μ k (Metric.ball q R) a))
        k .mixed (2 * R) z < ⊤ :=
    hη.mono fun z hz => (hE z).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hz)
  exact hFH.1 n hn k hk hkn .mixed (AdmissibleModel.nonempty_of_range hn hk hkn) _ hFm hFfin
    ⟨2 * R, by positivity, hηS⟩

/-! ## The dimensional constant -/

theorem density_constant_bounds {C₀ Cu K : ℝ} (h0 : 0 ≤ C₀) (hu : 0 ≤ Cu) (hK : 1 ≤ K) :
    C₀ + 1 ≤ K * (1 + C₀) * (1 + Cu) ∧ Cu * (C₀ + 1) ≤ K * (1 + C₀) * (1 + Cu) ∧
      Cu ≤ K * (1 + C₀) * (1 + Cu) ∧ C₀ ≤ K * (1 + C₀) * (1 + Cu) ∧
      K * C₀ ≤ K * (1 + C₀) * (1 + Cu) := by
  have hP0 : 0 ≤ (1 + C₀) * (1 + Cu) := by positivity
  have hP : 1 + C₀ ≤ (1 + C₀) * (1 + Cu) := by nlinarith
  have hP2 : Cu * (C₀ + 1) ≤ (1 + C₀) * (1 + Cu) := by nlinarith
  have hKP : (1 + C₀) * (1 + Cu) ≤ K * (1 + C₀) * (1 + Cu) := by nlinarith
  have hKC : K * C₀ ≤ K * ((1 + C₀) * (1 + Cu)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  refine ⟨by linarith, by linarith, by nlinarith, by linarith, by linarith [mul_assoc K (1 + C₀) (1 + Cu)]⟩

/-! ## Local integrated and weak packages -/

/-- All integrated conclusions at the scale `P(q,R)`, from the power rate with `q = 1`. -/
theorem density_local_integrated (hPM : PackingMassStatement)
    (hRL : RestrictLocallyRadonStatement) (hDM : DensityMeasurabilityStatement)
    (hBED : BetaEnergyDominationStatement) (hAC : ACBridgeStatement)
    (hFH : FiniteHausdorffCriterionStatement) {n : ℕ} (hn : 1 ≤ n) {C₀ Cu C : ℝ}
    (hC₀ : 0 < C₀) (hCu : 0 < Cu) (hCdef : C = 5 ^ (n + 2) * (1 + C₀) * (1 + Cu))
    (hpow : PowerRateProperty n C₀)
    (hUD : ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → UpperDominationBound n k Cu) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ n + 2) {μ : Measure (Space n)} (hμ : IsFiniteMeasureOnCompacts μ)
    (hreg : μ.InnerRegular) {q : Space n} {R : ℝ} (hR : 0 < R)
    (hE : localSquareEnergy μ k .mixed q R < ⊤) :
    (∀ A : ℝ, 0 ≤ A →
      (∀ᵐ z ∂μ, z ∈ Metric.ball q R → lowerDensity μ k z ≤ ENNReal.ofReal A) →
      μ (Metric.ball q R) ≤ ENNReal.ofReal (C * (A * R ^ k +
        R ^ ((k : ℝ) / 2) * Real.sqrt (localSquareEnergy μ k .mixed q R).toReal))) ∧
    (∀ a : ℝ, 0 < a →
      (∀ᵐ z ∂μ, z ∈ Metric.ball q R → ENNReal.ofReal a ≤ upperDensity μ k z) →
      μ.restrict (Metric.ball q R) (upperDensityLevelSet μ k (Metric.ball q R) a)ᶜ = 0 ∧
      IsRegularlyRectifiableSet .mixed k (upperDensityLevelSet μ k (Metric.ball q R) a) ∧
      hausdorffP n k (upperDensityLevelSet μ k (Metric.ball q R) a) ≤
        ENNReal.ofReal (C * (R ^ k + a⁻¹ * R ^ ((k : ℝ) / 2) *
          Real.sqrt (localSquareEnergy μ k .mixed q R).toReal))) ∧
    (∀ a : ℝ, 0 < a →
      (∀ z ∈ μ.support ∩ Metric.ball q R, ENNReal.ofReal a ≤ upperDensity μ k z) →
      IsRegularlyRectifiableSet .mixed k (μ.support ∩ Metric.ball q R) ∧
      hausdorffP n k (μ.support ∩ Metric.ball q R) ≤
        ENNReal.ofReal (C * (R ^ k + a⁻¹ * R ^ ((k : ℝ) / 2) *
          Real.sqrt (localSquareEnergy μ k .mixed q R).toReal))) ∧
    (∀ A a : ℝ, 0 ≤ A → 0 < a →
      (∀ᵐ z ∂μ, z ∈ Metric.ball q R → lowerDensity μ k z ≤ ENNReal.ofReal A) →
      (∀ᵐ z ∂μ, z ∈ Metric.ball q R → ENNReal.ofReal a ≤ upperDensity μ k z) →
      μ.restrict (Metric.ball q R) ≪ hausdorffP n k ∧
      IsRegularlyRectifiableMeasure .mixed k (μ.restrict (Metric.ball q R)) ∧
      ∀ ε : ℝ, 0 < ε → HasTypedMeasureCover .mixed k (μ.restrict (Metric.ball q R)) ε) := by
  have hpowE : powerEnergy μ k .mixed 1 q R = localSquareEnergy μ k .mixed q R := by
    simp only [powerEnergy, localSquareEnergy, ENNReal.rpow_one]
  obtain ⟨EH, EV, hloc, hloss, -⟩ := hpow.1 k hk hkn μ hμ hreg q R hR .mixed
    (AdmissibleModel.nonempty_of_range hn hk hkn) 1 one_pos (by rw [hpowE]; exact hE)
  set Z := R ^ ((k : ℝ) / 2) * Real.sqrt (localSquareEnergy μ k .mixed q R).toReal with hZ
  have hZ0 : 0 ≤ Z := mul_nonneg (Real.rpow_nonneg hR.le _) (Real.sqrt_nonneg _)
  have hlossE : μ.restrict (EH ∪ EV)ᶜ (Metric.ball q R) ≤ ENNReal.ofReal ((C₀ + 1) * Z) := by
    refine hloss.trans_eq ?_
    have h1 : (k : ℝ) * 1 / (1 + 1) = (k : ℝ) / 2 := by ring
    have h2 : (1 : ℝ) / (1 + 1) = 1 / 2 := by norm_num
    rw [hpowE, h1, h2, ← Real.sqrt_eq_rpow, hZ, mul_assoc]
  obtain ⟨hmass, hhaus⟩ := density_bounds_of_decomposition hPM hRL hDM hn hk hkn hμ hreg hR
    hC₀.le hCu.le (by positivity) hloc.measurable_horizontal hloc.measurable_vertical
    hloc.measure_eq hloc.supports hlossE (hUD k hk hkn)
  have hfin := ae_squareEnergy_lt_top_of_localSquareEnergy hμ hE
  have hK : (1 : ℝ) ≤ 5 ^ (n + 2) := one_le_pow₀ (by norm_num)
  obtain ⟨hb1, hb2, -, hb4, hb5⟩ := density_constant_bounds hC₀.le hCu.le hK
  rw [← hCdef] at hb1 hb2 hb4 hb5
  have h5C : 5 ^ k * C₀ ≤ C :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hkn) hC₀.le).trans hb5
  have hRk : 0 ≤ R ^ k := pow_nonneg hR.le k
  have hrect : ∀ a : ℝ, 0 < a →
      IsRegularlyRectifiableSet .mixed k (upperDensityLevelSet μ k (Metric.ball q R) a) :=
    fun a ha => density_levelSet_rectifiable hFH hBED hDM hn hk hkn hμ hreg hR hCu
      (hUD k hk hkn) ha hfin
  have hHF : ∀ a : ℝ, 0 < a →
      hausdorffP n k (upperDensityLevelSet μ k (Metric.ball q R) a) ≤
        ENNReal.ofReal (C * (R ^ k + a⁻¹ * R ^ ((k : ℝ) / 2) *
          Real.sqrt (localSquareEnergy μ k .mixed q R).toReal)) := by
    intro a ha
    refine (hhaus a ha).trans (ENNReal.ofReal_le_ofReal ?_)
    have haZ : 0 ≤ a⁻¹ * Z := mul_nonneg (inv_nonneg.mpr ha.le) hZ0
    have e : Cu / a * ((C₀ + 1) * Z) = (Cu * (C₀ + 1)) * (a⁻¹ * Z) := by ring
    have e' : C * (R ^ k + a⁻¹ * R ^ ((k : ℝ) / 2) *
        Real.sqrt (localSquareEnergy μ k .mixed q R).toReal) = C * R ^ k + C * (a⁻¹ * Z) := by
      rw [hZ]; ring
    rw [e, e']
    exact add_le_add (mul_le_mul_of_nonneg_right hb4 hRk) (mul_le_mul_of_nonneg_right hb2 haZ)
  refine ⟨fun A hA hlow => ?_, fun a ha hup => ⟨levelSet_carrier measurableSet_ball hup,
    hrect a ha, hHF a ha⟩, fun a ha hpt => ?_, fun A a hA ha hlow hup => ?_⟩
  · refine (hmass A hA hlow).trans (ENNReal.ofReal_le_ofReal ?_)
    have hAR : 0 ≤ A * R ^ k := mul_nonneg hA hRk
    nlinarith [mul_le_mul_of_nonneg_right hb1 hZ0, mul_le_mul_of_nonneg_right h5C hAR]
  · have hsub : μ.support ∩ Metric.ball q R ⊆ upperDensityLevelSet μ k (Metric.ball q R) a :=
      fun z hz => ⟨hz.2, hpt z hz⟩
    exact ⟨isRegularlyRectifiableSet_mono hsub (hrect a ha), (measure_mono hsub).trans (hHF a ha)⟩
  · have hac := density_absolutelyContinuous hAC hn hk hkn hμ hreg hR hlow hfin
    obtain ⟨hmr, hcov⟩ := measure_rectifiable_of_set hac (levelSet_carrier measurableSet_ball hup)
      (hrect a ha)
    exact ⟨hac, hmr, hcov⟩

/-- The rectifiable Reifenberg conclusions at the scale `P(q,R)`, from the scaled threshold property. -/
theorem density_local_weak (hPM : PackingMassStatement) (hRL : RestrictLocallyRadonStatement)
    (hDM : DensityMeasurabilityStatement) {n : ℕ} (hn : 1 ≤ n) {C₀ Cu C : ℝ} (hC₀ : 0 < C₀)
    (hCu : 0 < Cu) (hCdef : C = 5 ^ (n + 2) * (1 + C₀) * (1 + Cu))
    (hS : ScaledThresholdProperty n C₀)
    (hUD : ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → UpperDominationBound n k Cu) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ n + 2) {μ : Measure (Space n)} (hμ : IsFiniteMeasureOnCompacts μ)
    (hreg : μ.InnerRegular) {q : Space n} {R : ℝ} (hR : 0 < R) {M Γ : ℝ} (hM : 0 ≤ M)
    (hΓ : 0 ≤ Γ)
    (hbad : μ (Metric.ball q R ∩
      {z | ENNReal.ofReal M < squareEnergy μ k .mixed (2 * R) z}) ≤ ENNReal.ofReal Γ) :
    (∀ A : ℝ, 0 ≤ A →
      (∀ᵐ z ∂μ, z ∈ Metric.ball q R → lowerDensity μ k z ≤ ENNReal.ofReal A) →
      μ (Metric.ball q R) ≤ ENNReal.ofReal (C * (A + M) * R ^ k + Γ)) ∧
    (∀ a : ℝ, 0 < a →
      hausdorffP n k (upperDensityLevelSet μ k (Metric.ball q R) a) ≤
        ENNReal.ofReal (C * R ^ k + C / a * (C * M * R ^ k + Γ))) := by
  obtain ⟨EH, EV, hloc, hloss⟩ := hS k hk hkn μ hμ hreg q R hR .mixed
    (AdmissibleModel.nonempty_of_range hn hk hkn) M Γ hM hΓ hbad
  have hRk : 0 ≤ R ^ k := pow_nonneg hR.le k
  have hMR : 0 ≤ M * R ^ k := mul_nonneg hM hRk
  obtain ⟨hmass, hhaus⟩ := density_bounds_of_decomposition hPM hRL hDM hn hk hkn hμ hreg hR
    hC₀.le hCu.le (by positivity) hloc.measurable_horizontal hloc.measurable_vertical
    hloc.measure_eq hloc.supports hloss (hUD k hk hkn)
  have hK : (1 : ℝ) ≤ 5 ^ (n + 2) := one_le_pow₀ (by norm_num)
  obtain ⟨-, -, hb3, hb4, hb5⟩ := density_constant_bounds hC₀.le hCu.le hK
  rw [← hCdef] at hb3 hb4 hb5
  have h5C : 5 ^ k * C₀ ≤ C :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hkn) hC₀.le).trans hb5
  have hC0 : 0 ≤ C := hC₀.le.trans hb4
  refine ⟨fun A hA hlow => (hmass A hA hlow).trans (ENNReal.ofReal_le_ofReal ?_),
    fun a ha => (hhaus a ha).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  · have hAR : 0 ≤ A * R ^ k := mul_nonneg hA hRk
    nlinarith [mul_le_mul_of_nonneg_right hb4 hMR, mul_le_mul_of_nonneg_right h5C hAR]
  · have hX : C₀ * M * R ^ k + Γ ≤ C * M * R ^ k + Γ := by
      nlinarith [mul_le_mul_of_nonneg_right hb4 hMR]
    exact add_le_add (mul_le_mul_of_nonneg_right hb4 hRk)
      (mul_le_mul (div_le_div_of_nonneg_right hb3 ha.le) hX (by positivity)
        (div_nonneg hC0 ha.le))

/-! ## The three density statements -/

/-- **All three density conclusions.** The local integrated package at `P(0,1)`. -/
theorem density_three_parts_of_providers (hbridge : CompactBridgeCoverStatement)
    (hER : SquareEnergyRescalingStatement) (hPM : PackingMassStatement)
    (hUD : UpperDensityDominationStatement) (hAC : ACBridgeStatement)
    (hDM : DensityMeasurabilityStatement) (hBED : BetaEnergyDominationStatement)
    (hRL : RestrictLocallyRadonStatement) (hFH : FiniteHausdorffCriterionStatement) :
    DensityThreePartsStatement := by
  intro n hn
  obtain ⟨C₀, hC₀, -, hpow⟩ := power_rate_of_providers hbridge hER n hn
  obtain ⟨Cu, hCu, hUDu⟩ := exists_uniform_upperDominationBound hUD n hn
  refine ⟨5 ^ (n + 2) * (1 + C₀) * (1 + Cu), by positivity, ?_⟩
  intro k hk hkn μ hμ hreg hE
  have hEeq : localSquareEnergy μ k .mixed (point 0 0) 1 = unitSquareEnergy μ k .mixed := by
    simp only [localSquareEnergy, unitSquareEnergy, mul_one]
  obtain ⟨h1, h2, h3, h4⟩ := density_local_integrated hPM hRL hDM hBED hAC hFH hn hC₀ hCu
    rfl hpow hUDu hk hkn hμ hreg (q := point 0 0) one_pos (by rw [hEeq]; exact hE)
  rw [hEeq] at h1 h2 h3
  have e1 : ∀ A x : ℝ, 5 ^ (n + 2) * (1 + C₀) * (1 + Cu) *
      (A * (1 : ℝ) ^ k + (1 : ℝ) ^ ((k : ℝ) / 2) * x) =
        5 ^ (n + 2) * (1 + C₀) * (1 + Cu) * (A + x) := by
    intro A x; rw [one_pow, Real.one_rpow]; ring
  have e2 : ∀ a x : ℝ, 5 ^ (n + 2) * (1 + C₀) * (1 + Cu) *
      ((1 : ℝ) ^ k + a⁻¹ * (1 : ℝ) ^ ((k : ℝ) / 2) * x) =
        5 ^ (n + 2) * (1 + C₀) * (1 + Cu) * (1 + x / a) := by
    intro a x; rw [one_pow, Real.one_rpow, mul_one, inv_mul_eq_div]
  refine ⟨fun A hA hlow => ?_, fun a ha hup => ?_, fun a ha hpt => ?_,
    fun A a hA ha hlow hup => ?_⟩
  · exact (h1 A hA hlow).trans_eq (by rw [e1])
  · obtain ⟨hc, hr, hb⟩ := h2 a ha hup
    exact ⟨measurableSet_upperDensityLevelSet hDM hn hk hkn hμ hreg measurableSet_ball a, hc,
      hr, hb.trans_eq (by rw [e2])⟩
  · obtain ⟨hr, hb⟩ := h3 a ha hpt
    exact ⟨hr, hb.trans_eq (by rw [e2])⟩
  · obtain ⟨hac, hmr, hcov⟩ := h4 A a hA ha hlow hup
    exact ⟨hac, hmr, hcov, (h1 A hA hlow).trans_eq (by rw [e1]),
      (h2 a ha hup).2.2.trans_eq (by rw [e2])⟩

/-- **Rectifiable Reifenberg density bounds.** From the parabolic rectifiable Reifenberg theorem directly, using the packing-mass and
upper-domination statements. -/
theorem density_rectifiable_reifenberg_of_providers (hbridge : CompactBridgeCoverStatement)
    (hPM : PackingMassStatement) (hUD : UpperDensityDominationStatement)
    (hDM : DensityMeasurabilityStatement) (hRL : RestrictLocallyRadonStatement) :
    DensityRectifiableReifenbergStatement := by
  intro n hn
  obtain ⟨C₀, hC₀, hmix, -, -⟩ := rectifiable_reifenberg_theorem_of_providers hbridge n hn
  obtain ⟨Cu, hCu, hUDu⟩ := exists_uniform_upperDominationBound hUD n hn
  refine ⟨5 ^ (n + 2) * (1 + C₀) * (1 + Cu), by positivity, ?_⟩
  intro k hk hkn μ hμ hreg M Γ hM hΓ hbad
  obtain ⟨D, hD⟩ := hmix k hk hkn μ hμ hreg M Γ hM hΓ hbad
  obtain ⟨hmass, hhaus⟩ := density_bounds_of_decomposition hPM hRL hDM hn hk hkn hμ hreg
    (q := point 0 0) (L := C₀ * M + Γ) one_pos hC₀.le hCu.le (by positivity)
    (EH := D.horizontal) (EV := D.vertical) D.measurable_horizontal D.measurable_vertical
    hD.measure_eq hD.supports hD.remainder_bound (hUDu k hk hkn)
  have hK : (1 : ℝ) ≤ 5 ^ (n + 2) := one_le_pow₀ (by norm_num)
  obtain ⟨-, -, hb3, hb4, hb5⟩ := density_constant_bounds hC₀.le hCu.le hK
  have h5C : 5 ^ k * C₀ ≤ 5 ^ (n + 2) * (1 + C₀) * (1 + Cu) :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hkn) hC₀.le).trans hb5
  have hC0 : 0 ≤ 5 ^ (n + 2) * (1 + C₀) * (1 + Cu) := hC₀.le.trans hb4
  have hH : ∀ a : ℝ, 0 < a →
      hausdorffP n k (upperDensityLevelSet μ k (Metric.ball (point 0 0) 1) a) ≤
        ENNReal.ofReal (5 ^ (n + 2) * (1 + C₀) * (1 + Cu) +
          5 ^ (n + 2) * (1 + C₀) * (1 + Cu) / a *
            (5 ^ (n + 2) * (1 + C₀) * (1 + Cu) * M + Γ)) := by
    intro a ha
    refine (hhaus a ha).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [one_pow, mul_one]
    have hX : C₀ * M + Γ ≤ 5 ^ (n + 2) * (1 + C₀) * (1 + Cu) * M + Γ := by
      nlinarith [mul_le_mul_of_nonneg_right hb4 hM]
    exact add_le_add hb4 (mul_le_mul (div_le_div_of_nonneg_right hb3 ha.le) hX
      (by positivity) (div_nonneg hC0 ha.le))
  refine ⟨fun A hA hlow => ?_, fun a ha => ⟨measurableSet_upperDensityLevelSet hDM hn hk hkn
    hμ hreg measurableSet_ball a, hH a ha⟩, fun a _ hup => levelSet_carrier measurableSet_ball hup,
    fun a ha hpt => ?_⟩
  · refine (hmass A hA hlow).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [one_pow, mul_one]
    nlinarith [mul_le_mul_of_nonneg_right hb4 hM, mul_le_mul_of_nonneg_right h5C hA]
  · have hsub : μ.support ∩ Metric.ball (point 0 0) 1 ⊆
        upperDensityLevelSet μ k (Metric.ball (point 0 0) 1) a := fun z hz => ⟨hz.2, hpt z hz⟩
    exact (measure_mono hsub).trans (hH a ha)

/-- **All local scales.** Integrated versions from the power rate (`q = 1`) at `P(q,R)`, weak
versions from the scaled threshold property, both with the same core constant. -/
theorem density_scaling_of_providers (hbridge : CompactBridgeCoverStatement)
    (hER : SquareEnergyRescalingStatement) (hPM : PackingMassStatement)
    (hUD : UpperDensityDominationStatement) (hAC : ACBridgeStatement)
    (hDM : DensityMeasurabilityStatement) (hBED : BetaEnergyDominationStatement)
    (hRL : RestrictLocallyRadonStatement) (hFH : FiniteHausdorffCriterionStatement) :
    DensityScalingStatement := by
  intro n hn
  obtain ⟨C₀, hC₀, hS, hpow⟩ := power_rate_of_providers hbridge hER n hn
  obtain ⟨Cu, hCu, hUDu⟩ := exists_uniform_upperDominationBound hUD n hn
  refine ⟨5 ^ (n + 2) * (1 + C₀) * (1 + Cu), by positivity, ?_⟩
  intro k hk hkn μ hμ hreg q R hR
  exact ⟨fun hE => density_local_integrated hPM hRL hDM hBED hAC hFH hn hC₀ hCu rfl hpow hUDu
      hk hkn hμ hreg hR hE,
    fun M Γ hM hΓ hbad => density_local_weak hPM hRL hDM hn hC₀ hCu rfl hS hUDu hk hkn hμ hreg
      hR hM hΓ hbad⟩

end ParabolicRectifiability.Enhancements
