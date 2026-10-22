import ParabolicRectifiability.Decomposition.Assembly
import ParabolicRectifiability.Decomposition.ZeroThresholdAndAmbientBranches

/-!
# Rectifiable Reifenberg rectifiability and its fixed-family and ambient forms

For an arbitrary nonnegative Radon source, the mixed square-energy threshold
produces two retained Borel pieces with compact actual supports and remainder
mass at most `C * M + Γ` in the open unit ball. The same pieces work for every
positive graph tolerance; their covers have parabolic Hausdorff-null exceptions.
The source may have infinite total mass and may charge those exceptions.

`rectifiable_reifenberg` displays the hypotheses and quantifier order.
`main_rectifiability`, `fixed_family_rectifiability` and `ambient_rectifiability`
prove the public statements `MainRectifiabilityStatement`,
`FixedFamilyRectifiabilityStatement` and `AmbientRectifiabilityStatement`.
`family_rectifiable_reifenberg` combines the positive-threshold branch
`positive_threshold_family_decomposition`, the zero-threshold branch
`zero_threshold_family_decomposition` and the ambient branch
`ambient_retained_decomposition`. The scaled and graph-domain enhancements are
proved in the `Enhancements` area.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability

/-- Increasing a dimensional constant preserves all five quantitative outputs. -/
theorem HasRectifiabilityContentBounds.mono_constant {n k : ℕ} {C C' : ℝ}
    {K : Set (Space n)} (h : HasRectifiabilityContentBounds k C K) (hC : C ≤ C') :
    HasRectifiabilityContentBounds k C' K where
  hausdorff := by
    intro q R hR hR1
    exact (h.hausdorff q R hR hR1).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hC (pow_nonneg hR.le _)))
  separated := by
    intro q R r hR hR1 hr hrR F hF hsep
    exact (h.separated q R r hR hR1 hr hrR F hF hsep).trans
      (mul_le_mul_of_nonneg_right hC (pow_nonneg (div_nonneg hR.le hr.le) _))
  minkowski := by
    intro r hr hr1
    exact (h.minkowski r hr hr1).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hC (pow_nonneg hr.le _)))
  finite_packing := by
    intro q R hR hR1 l z r hz hr hdisj
    exact (h.finite_packing q R hR hR1 l z r hz hr hdisj).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC (pow_nonneg hR.le _)))
  countable_packing := by
    intro q R hR hR1 I z r hz hr hdisj
    exact (h.countable_packing q R hR hR1 I z r hz hr hdisj).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC (pow_nonneg hR.le _)))

/-- Monotonicity does not alter the retained sets or any graph tolerance. -/
theorem IsRectifiabilityDecomposition.mono_constant {n k : ℕ} {C C' M Γ : ℝ}
    {μ : Measure (Space n)} {D : RetainedSets n}
    (h : IsRectifiabilityDecomposition k C M Γ μ D) (hC : C ≤ C') (hM : 0 ≤ M) :
    IsRectifiabilityDecomposition k C' M Γ μ D :=
  { h with
    remainder_bound := h.remainder_bound.trans (ENNReal.ofReal_le_ofReal
      (by have := mul_le_mul_of_nonneg_right hC hM; linarith))
    content := h.content.mono_constant hC }

theorem HasFamilyDecomposition.mono_constant {n k : ℕ} {T : FamilyKind}
    {C C' M Γ : ℝ} {μ : Measure (Space n)}
    (h : HasFamilyDecomposition k T C M Γ μ) (hC : C ≤ C') (hM : 0 ≤ M) :
    HasFamilyDecomposition k T C' M Γ μ := by
  obtain ⟨D, hD, hH, hV⟩ := h
  exact ⟨D, hD.mono_constant hC hM, hH, hV⟩

/-- The ambient zero-remainder output also satisfies any nonnegative threshold. -/
theorem IsRectifiabilityDecomposition.of_zero_threshold {n k : ℕ}
    {C M Γ : ℝ} {μ : Measure (Space n)} {D : RetainedSets n}
    (h : IsRectifiabilityDecomposition k C 0 0 μ D)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hΓ : 0 ≤ Γ) :
    IsRectifiabilityDecomposition k C M Γ μ D :=
  { h with
    remainder_bound := by
      exact h.remainder_bound.trans (ENNReal.ofReal_le_ofReal (by nlinarith)) }

/-- A positive constant depending only on `n` works simultaneously for
`1 ≤ k ≤ n + 2` and every available horizontal, vertical or mixed testing family.
The square energy uses the original source on scales `0 < r < 2`; its bad set
is measured in the open unit ball. Both `M = 0` and `Γ = 0` are allowed.
For a single testing type, the opposite retained measure and support vanish.
The proof combines the positive, zero and ambient branches. -/
theorem family_rectifiable_reifenberg (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
      ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ M Γ : ℝ, 0 ≤ M → 0 ≤ Γ →
      μ (Metric.ball (point 0 0) 1 ∩
        {z | ENNReal.ofReal M < squareEnergy μ k T 2 z}) ≤ ENNReal.ofReal Γ →
      HasFamilyDecomposition k T C M Γ μ := by
  obtain ⟨Cp, hCp, hpositive⟩ := positive_threshold_family_decomposition n hn
  obtain ⟨Cz, hCz, hzero⟩ := zero_threshold_family_decomposition n hn
  obtain ⟨Ca, hCa, hambient⟩ := ambient_retained_decomposition n hn
  let C := Cp + Cz + Ca
  have hp : Cp ≤ C := by dsimp [C]; linarith
  have hz : Cz ≤ C := by dsimp [C]; linarith
  have ha : Ca ≤ C := by dsimp [C]; linarith
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro k hk hkn T hT μ hμ hreg M Γ hM hΓ hbad
  by_cases htop : k = n + 2
  · subst k
    obtain ⟨hD, _⟩ := hambient μ hμ hreg
    refine ⟨ambientRetainedSets n,
      (hD.of_zero_threshold hCa.le hM hΓ).mono_constant ha hM, ?_, ?_⟩
    · intro hT'
      subst T
      have hr := HorizontalModel.nonempty_iff.mp hT
      omega
    · intro _
      simp [ambientRetainedSets, RetainedSets.horizontalMeasure,
        RetainedSets.horizontalSupport]
  · have hklt : k < n + 2 := lt_of_le_of_ne hkn htop
    by_cases hM0 : M = 0
    · subst M
      apply (hzero k hk hkn T hT μ hμ hreg Γ hΓ
        (by simpa only [ENNReal.ofReal_zero] using hbad)).mono_constant hz le_rfl
    · exact (hpositive k hk hklt T hT μ hμ hreg M Γ
        (lt_of_le_of_ne hM (Ne.symm hM0)) hΓ hbad).mono_constant hp hM

/-- Parabolic rectifiable Reifenberg theorem for the original Radon
source, without density, doubling or finite-total-mass assumptions.

After choosing `C` from `n`, every allowed `k`, source, and nonnegative `M, Γ`
with exceptional mass at most `Γ` admit retained sets `D`. Their actual supports
are compact, lie in the closed unit ball, and admit every positive graph
tolerance. `IsRectifiabilityDecomposition` also gives the exact remainder bound
`C * M + Γ` and all local Hausdorff, separation, tubular-volume and finite or
countable variable-radius packing bounds. Hausdorff-null graph exceptions
need not be null for the retained source measures. -/
theorem rectifiable_reifenberg (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ M Γ : ℝ, 0 ≤ M → 0 ≤ Γ →
        μ (exceptionalSet μ k M) ≤ ENNReal.ofReal Γ →
        ∃ D : RetainedSets n, IsRectifiabilityDecomposition k C M Γ μ D := by
  obtain ⟨C, hC, h⟩ := family_rectifiable_reifenberg n hn
  refine ⟨C, hC, ?_⟩
  intro k hk hkn μ hμ hreg M Γ hM hΓ hbad
  obtain ⟨D, hD, _, _⟩ := h k hk hkn .mixed
    (AdmissibleModel.nonempty_of_range hn hk hkn) μ hμ hreg M Γ hM hΓ hbad
  exact ⟨D, hD⟩

/-- The main rectifiability theorem: `rectifiable_reifenberg` is, definitionally,
a proof of `MainRectifiabilityStatement`. -/
theorem main_rectifiability : MainRectifiabilityStatement :=
  rectifiable_reifenberg

/-- The same assembly retains the fixed-family conclusion, including its zero
opposite output. Family availability is the hypothesis `Nonempty (Models n k T)`
of `FixedFamilyRectifiabilityStatement`. -/
theorem fixed_family_rectifiability (T : FamilyKind) : FixedFamilyRectifiabilityStatement T := by
  intro n hn
  obtain ⟨C, hC, h⟩ := family_rectifiable_reifenberg n hn
  exact ⟨C, hC, fun k hk hkn hT μ hμ hreg M Γ hM hΓ hbad =>
    h k hk hkn T hT μ hμ hreg M Γ hM hΓ hbad⟩

/-- The ambient statement has no beta premise and exactly zero remainder. -/
theorem ambient_rectifiability : AmbientRectifiabilityStatement := by
  intro n hn
  obtain ⟨C, hC, h⟩ := ambient_retained_decomposition n hn
  refine ⟨C, hC, ?_⟩
  intro μ hμ hreg
  exact ⟨ambientRetainedSets n, h μ hμ hreg⟩

end ParabolicRectifiability
