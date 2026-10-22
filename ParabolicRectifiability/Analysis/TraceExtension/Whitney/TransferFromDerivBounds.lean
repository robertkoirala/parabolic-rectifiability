import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Lipschitz
import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Micro
import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Recentering

/-! # The full Whitney transfer

For a smooth
Whitney partition, an `L`-Lipschitz `g` on the node set and node Carleson integrals at
most `B R^k`, the filling is `C L`-Lipschitz (`whitneyFilling_lipschitz_proof`) and has affine Carleson
constant `C (L² + B)`. For fixed `z, R` and each center `y` the scale range `(0,R)` is
split at `2s = δ(y)`:

* microscopic scales: `whitneyFilling_affineErrorSq_le_micro_proof` and the scale integral `∫ (s/δ)² ds/s ≤ 1/4`;
* macroscopic scales: the transfer inequality `whitney_macro_transfer_proof` gives the node error at scale
  `C₂ s` and the cube defect; their `y`-integrals are bounded by recentering
(`whitney_recentering_le_proof`)
  together with the Carleson hypothesis at radius `C' R`, and by the summable cube
  defect (`whitney_cube_defect_le_proof`).

The cube-defect term is jointly measurable, which justifies splitting the outer
integral; the other pieces are bounded by a constant or kept under a constant factor.

The transfer is proved in implication form: the derivative-bound statement of
`whitneyFilling_deriv_bounds_proof` is a hypothesis, used only through the microscopic
error bound.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

universe u v

/-- The integrated cube defect over the macroscopic scale range is measurable in the
center variable. -/
theorem WhitneyData.measurable_setLIntegral_cubeDefect {m : ℕ} {ι : Type*} [Countable ι]
    {F₀ : Set (Space m)} {D a : ℝ} (W : WhitneyData m ι F₀ D a) (R : ℝ) :
    Measurable fun y : Space m =>
      ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s}, W.cubeDefect y s ∂scaleMeasure := by
  have hT : MeasurableSet
      {p : Space m × ℝ | p.2 ∈ Ioo 0 R ∧ Metric.infDist p.1 F₀ ≤ 2 * p.2} :=
    (measurableSet_Ioo.preimage measurable_snd).inter
      (measurableSet_le ((Metric.continuous_infDist_pt F₀).measurable.comp measurable_fst)
        (measurable_const.mul measurable_snd))
  have heq : (fun y : Space m =>
      ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s}, W.cubeDefect y s ∂scaleMeasure) =
      fun y => ∫⁻ s, {p : Space m × ℝ | p.2 ∈ Ioo 0 R ∧ Metric.infDist p.1 F₀ ≤ 2 * p.2}.indicator
        (fun p => W.cubeDefect p.1 p.2) (y, s) ∂scaleMeasure := by
    funext y
    have hS : MeasurableSet (Ioo 0 R ∩ {s : ℝ | Metric.infDist y F₀ ≤ 2 * s}) :=
      measurableSet_Ioo.inter (measurableSet_le measurable_const (measurable_const.mul measurable_id))
    rw [← lintegral_indicator hS]
    refine lintegral_congr fun s => ?_
    by_cases hs : s ∈ Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s}
    · rw [indicator_of_mem hs, indicator_of_mem (show (y, s) ∈
        {p : Space m × ℝ | p.2 ∈ Ioo 0 R ∧ Metric.infDist p.1 F₀ ≤ 2 * p.2} from hs)]
    · rw [indicator_of_notMem hs, indicator_of_notMem (show (y, s) ∉
        {p : Space m × ℝ | p.2 ∈ Ioo 0 R ∧ Metric.infDist p.1 F₀ ≤ 2 * p.2} from hs)]
  rw [heq]
  exact (W.measurable_cubeDefect.indicator hT).lintegral_prod_right'

/-- **The full Whitney transfer**, in implication form: the derivative-bound statement of
`whitneyFilling_deriv_bounds_proof` implies the full transfer. -/
theorem whitney_transfer_proof (m : ℕ) (D a H b K : ℝ) (N : ℕ) (ha : 2 ≤ a) (hH : 0 ≤ H)
    (hderiv : ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} [Countable ι] {F₀ : Set (Space m)}
      (W : WhitneyData m ι F₀ D a), IsClosed F₀ → F₀.Nonempty →
      ∀ (P : WhitneyPartition W H b K N) {Y : Type v} [NormedAddCommGroup Y]
        [InnerProductSpace ℝ Y] (g : Space m → Y) (L : ℝ≥0), LipschitzOnWith L g W.nodeSet →
        ContDiffOn ℝ 2 (fun y : Coordinates m => whitneyFilling P.toWhitneyWeights g (point y.1 y.2))
            {y | point y.1 y.2 ∉ F₀} ∧
          ∀ q ∉ F₀,
            ‖fderiv ℝ (fun v => whitneyFilling P.toWhitneyWeights g (point v q.2.val)) q.1‖ ≤
                C * L ∧
              ‖fderiv ℝ (fun v => fderiv ℝ
                  (fun w => whitneyFilling P.toWhitneyWeights g (point w q.2.val)) v) q.1‖ ≤
                C * L / Metric.infDist q F₀ ∧
              ‖deriv (fun t => whitneyFilling P.toWhitneyWeights g (point q.1 t)) q.2.val‖ ≤
                C * L / Metric.infDist q F₀) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ {ι : Type u} [Countable ι] {F₀ : Set (Space m)}
      (W : WhitneyData m ι F₀ D a), IsCompact F₀ → F₀.Nonempty →
      ∀ (P : WhitneyPartition W H b K N) {Y : Type v} [NormedAddCommGroup Y]
        [InnerProductSpace ℝ Y] (g : Space m → Y) (L : ℝ≥0), LipschitzOnWith L g W.nodeSet →
        ∀ B : ℝ, 0 ≤ B →
        (∀ (z : Space m) (R : ℝ), 0 < R →
          W.nodeCarlesonIntegral g L z R ≤ ENNReal.ofReal (B * R ^ (m + 2))) →
        LipschitzWith (C * L) (whitneyFilling P.toWhitneyWeights g) ∧
          HasAffineCarlesonBound (parabolicVolume m) (whitneyFilling P.toWhitneyWeights g)
            (C * ((L : ℝ) ^ 2 + B)) := by
  obtain ⟨Clip, hClip⟩ := whitneyFilling_lipschitz_proof.{u, v} m D a H b K N
  obtain ⟨Cμ, hCμ0, hCμ⟩ :=
    whitneyFilling_affineErrorSq_le_micro_proof.{u, v} m D a H b K N hderiv
  obtain ⟨Crec, C', hCrec0, hC'1, hrec⟩ := whitney_recentering_le_proof.{u, v} m D a ha
  obtain ⟨Ccarl, hCcarl⟩ : ∃ x : ℝ, x = Cμ * (omega m).toReal / 2 +
      2 * (H + D) ^ 2 * ((2 * (omega m).toReal) ^ 2 * ((1 + 3 * D / a) ^ (m + 2) *
        (2 + 6 * D / a) ^ (m + 2) / (2 * (a / 3) ^ 2))) +
      2 * (1 + 3 * D / a) ^ (m + 4) * Crec * C' ^ (m + 2) := ⟨_, rfl⟩
  refine ⟨Clip + Real.toNNReal Ccarl + 1, by positivity, ?_⟩
  intro ι _ F₀ W hF₀c hne P Y _ _ g L hg B hB hNC
  have hF₀ : IsClosed F₀ := hF₀c.isClosed
  have ha0 : 0 < a := by linarith
  have hD : 1 ≤ D := W.one_le_D
  have hL : (0 : ℝ) ≤ L := NNReal.coe_nonneg L
  have hCge : Ccarl ≤ ((Clip + Real.toNNReal Ccarl + 1 : ℝ≥0) : ℝ) := by
    have h1 := Real.le_coe_toNNReal Ccarl
    have h2 := NNReal.coe_nonneg Clip
    rw [NNReal.coe_add, NNReal.coe_add, NNReal.coe_one]
    linarith
  refine ⟨(hClip W hF₀ hne P g L hg).weaken
    (mul_le_mul_left (le_self_add.trans le_self_add) L), ?_⟩
  refine ⟨mul_nonneg (NNReal.coe_nonneg _) (add_nonneg (sq_nonneg _) hB), fun z R hR => ?_⟩
  rw [baseDimension_spatial, affineCarlesonIntegral]
  -- constants
  have h3D : 0 ≤ 3 * D / a := div_nonneg (by linarith) ha0.le
  have hX0 : 0 ≤ (1 + 3 * D / a) ^ (m + 4) := pow_nonneg (by linarith) _
  have hκd : 0 ≤ (1 + 3 * D / a) ^ (m + 2) * (2 + 6 * D / a) ^ (m + 2) / (2 * (a / 3) ^ 2) := by
    have h6 : 0 ≤ 6 * D / a := div_nonneg (by linarith) ha0.le
    exact div_nonneg (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _))
      (by positivity)
  have hω : 0 ≤ (omega m).toReal := ENNReal.toReal_nonneg
  have hc0 : 0 ≤ 2 * (H + D) ^ 2 * (L : ℝ) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hm0 : 0 ≤ Cμ * (L : ℝ) ^ 2 / 4 := div_nonneg (mul_nonneg hCμ0 (sq_nonneg _)) (by norm_num)
  have hRk : 0 ≤ R ^ (m + 2) := pow_nonneg hR.le _
  have hC'R : 0 < C' * R := mul_pos (by linarith) hR
  have h2X : (2 * ENNReal.ofReal ((1 + 3 * D / a) ^ (m + 4))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top
  -- the pointwise split of the scale integral
  have hsplit : ∀ y : Space m,
      ∫⁻ s in Ioo 0 R, affineErrorSq (parabolicVolume m) (whitneyFilling P.toWhitneyWeights g) y s
        ∂scaleMeasure ≤
      (ENNReal.ofReal (Cμ * (L : ℝ) ^ 2 / 4) +
        2 * ENNReal.ofReal ((1 + 3 * D / a) ^ (m + 4)) *
          ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s},
            constrainedAffineErrorSq W.nodeMeasure g L y ((1 + 3 * D / a) * s) ∂scaleMeasure) +
      ENNReal.ofReal (2 * (H + D) ^ 2 * (L : ℝ) ^ 2) *
        ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s}, W.cubeDefect y s ∂scaleMeasure := by
    intro y
    have hS₂ : MeasurableSet (Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s}) :=
      measurableSet_Ioo.inter (measurableSet_le measurable_const
        (measurable_const.mul measurable_id))
    have hcover : Ioo 0 R ⊆ (Ioo 0 R ∩ {s | 2 * s < Metric.infDist y F₀}) ∪
        (Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s}) := fun s hs => by
      rcases lt_or_ge (2 * s) (Metric.infDist y F₀) with h | h
      · exact Or.inl ⟨hs, h⟩
      · exact Or.inr ⟨hs, h⟩
    have hmicro := setLIntegral_microRange_le
      (f := fun s => affineErrorSq (parabolicVolume m) (whitneyFilling P.toWhitneyWeights g) y s)
      (δ := Metric.infDist y F₀) R (mul_nonneg hCμ0 (sq_nonneg (L : ℝ)))
      fun s hs hsy => hCμ W hF₀ hne P g L hg y s hs hsy
    have hmacro : ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s},
        affineErrorSq (parabolicVolume m) (whitneyFilling P.toWhitneyWeights g) y s
          ∂scaleMeasure ≤
        2 * ENNReal.ofReal ((1 + 3 * D / a) ^ (m + 4)) *
          ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s},
            constrainedAffineErrorSq W.nodeMeasure g L y ((1 + 3 * D / a) * s) ∂scaleMeasure +
        ENNReal.ofReal (2 * (H + D) ^ 2 * (L : ℝ) ^ 2) *
          ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s}, W.cubeDefect y s
            ∂scaleMeasure := by
      calc
        _ ≤ ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s},
              (2 * ENNReal.ofReal ((1 + 3 * D / a) ^ (m + 4)) *
                constrainedAffineErrorSq W.nodeMeasure g L y ((1 + 3 * D / a) * s) +
              ENNReal.ofReal (2 * (H + D) ^ 2 * (L : ℝ) ^ 2) * W.cubeDefect y s)
                ∂scaleMeasure :=
          setLIntegral_mono' hS₂ fun s hs =>
            whitney_macro_transfer_proof W hF₀ hne hH P.toWhitneyWeights g L hg y s hs.1.1 hs.2
        _ = _ := by
          have hmeas : Measurable fun s =>
              ENNReal.ofReal (2 * (H + D) ^ 2 * (L : ℝ) ^ 2) * W.cubeDefect y s :=
            (W.measurable_cubeDefect.comp measurable_prodMk_left).const_mul _
          rw [lintegral_add_right _ hmeas, lintegral_const_mul' _ _ h2X,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc
      _ ≤ ∫⁻ s in (Ioo 0 R ∩ {s | 2 * s < Metric.infDist y F₀}) ∪
            (Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s}),
            affineErrorSq (parabolicVolume m) (whitneyFilling P.toWhitneyWeights g) y s
              ∂scaleMeasure := lintegral_mono_set hcover
      _ ≤ _ := lintegral_union_le _ _ _
      _ ≤ _ := add_le_add hmicro hmacro
      _ = _ := by rw [add_assoc]
  -- integrate over the ball
  have hDft := W.measurable_setLIntegral_cubeDefect R
  calc
    _ ≤ ∫⁻ y in Metric.ball z R, ((ENNReal.ofReal (Cμ * (L : ℝ) ^ 2 / 4) +
          2 * ENNReal.ofReal ((1 + 3 * D / a) ^ (m + 4)) *
            ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s},
              constrainedAffineErrorSq W.nodeMeasure g L y ((1 + 3 * D / a) * s) ∂scaleMeasure) +
        ENNReal.ofReal (2 * (H + D) ^ 2 * (L : ℝ) ^ 2) *
          ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s}, W.cubeDefect y s ∂scaleMeasure)
            ∂parabolicVolume m :=
      lintegral_mono hsplit
    _ = (ENNReal.ofReal (Cμ * (L : ℝ) ^ 2 / 4) * parabolicVolume m (Metric.ball z R) +
          2 * ENNReal.ofReal ((1 + 3 * D / a) ^ (m + 4)) *
            ∫⁻ y in Metric.ball z R, ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s},
              constrainedAffineErrorSq W.nodeMeasure g L y ((1 + 3 * D / a) * s)
                ∂scaleMeasure ∂parabolicVolume m) +
        ENNReal.ofReal (2 * (H + D) ^ 2 * (L : ℝ) ^ 2) *
          ∫⁻ y in Metric.ball z R, ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s},
            W.cubeDefect y s ∂scaleMeasure ∂parabolicVolume m := by
      rw [lintegral_add_right _ (hDft.const_mul (ENNReal.ofReal (2 * (H + D) ^ 2 * (L : ℝ) ^ 2))),
        lintegral_add_left measurable_const,
        setLIntegral_const, lintegral_const_mul' _ _ h2X,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ (ENNReal.ofReal (Cμ * (L : ℝ) ^ 2 / 4) * parabolicVolume m (Metric.ball z R) +
          2 * ENNReal.ofReal ((1 + 3 * D / a) ^ (m + 4)) *
            (ENNReal.ofReal Crec * ENNReal.ofReal (B * (C' * R) ^ (m + 2)))) +
        ENNReal.ofReal (2 * (H + D) ^ 2 * (L : ℝ) ^ 2) *
          ((2 * omega m) ^ 2 * ENNReal.ofReal ((1 + 3 * D / a) ^ (m + 2) *
            (2 + 6 * D / a) ^ (m + 2) / (2 * (a / 3) ^ 2) * R ^ (m + 2))) := by
      gcongr
      · exact (hrec W hF₀ g L z R hR).trans
          (mul_le_mul_right (hNC z (C' * R) hC'R) _)
      · exact whitney_cube_defect_le_proof W hF₀ z R hR
    _ = ENNReal.ofReal (Cμ * (L : ℝ) ^ 2 / 4 * (2 * (omega m).toReal * R ^ (m + 2)) +
          2 * (1 + 3 * D / a) ^ (m + 4) * (Crec * (B * (C' * R) ^ (m + 2))) +
          2 * (H + D) ^ 2 * (L : ℝ) ^ 2 * ((2 * (omega m).toReal) ^ 2 *
            ((1 + 3 * D / a) ^ (m + 2) * (2 + 6 * D / a) ^ (m + 2) / (2 * (a / 3) ^ 2) *
              R ^ (m + 2)))) := by
      have hvol : parabolicVolume m (Metric.ball z R) =
          ENNReal.ofReal (2 * (omega m).toReal * R ^ (m + 2)) := by
        rw [parabolicVolume_ball z R hR, two_mul_omega_mul_ofReal_pow m hR.le]
      have h2ω : (2 * omega m) ^ 2 = ENNReal.ofReal ((2 * (omega m).toReal) ^ 2) := by
        rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_ofNat, ENNReal.ofReal_toReal (omega_lt_top m).ne]
      have ht1 : 0 ≤ Cμ * (L : ℝ) ^ 2 / 4 * (2 * (omega m).toReal * R ^ (m + 2)) :=
        mul_nonneg hm0 (mul_nonneg (mul_nonneg (by norm_num) hω) hRk)
      have ht2 : 0 ≤ 2 * (1 + 3 * D / a) ^ (m + 4) * (Crec * (B * (C' * R) ^ (m + 2))) :=
        mul_nonneg (mul_nonneg (by norm_num) hX0)
          (mul_nonneg hCrec0 (mul_nonneg hB (pow_nonneg hC'R.le _)))
      have ht3 : 0 ≤ 2 * (H + D) ^ 2 * (L : ℝ) ^ 2 * ((2 * (omega m).toReal) ^ 2 *
          ((1 + 3 * D / a) ^ (m + 2) * (2 + 6 * D / a) ^ (m + 2) / (2 * (a / 3) ^ 2) *
            R ^ (m + 2))) :=
        mul_nonneg hc0 (mul_nonneg (sq_nonneg _) (mul_nonneg hκd hRk))
      rw [hvol, h2ω, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul hm0,
        ← ENNReal.ofReal_mul hCrec0, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hX0),
        ← ENNReal.ofReal_mul (sq_nonneg (2 * (omega m).toReal)), ← ENNReal.ofReal_mul hc0,
        ← ENNReal.ofReal_add ht1 ht2, ← ENNReal.ofReal_add (add_nonneg ht1 ht2) ht3]
    _ ≤ ENNReal.ofReal (((Clip + Real.toNNReal Ccarl + 1 : ℝ≥0) : ℝ) * ((L : ℝ) ^ 2 + B) *
          R ^ (m + 2)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      have hκ := hκd
      have hdiff : Ccarl * ((L : ℝ) ^ 2 + B) * R ^ (m + 2) -
          (Cμ * (L : ℝ) ^ 2 / 4 * (2 * (omega m).toReal * R ^ (m + 2)) +
            2 * (1 + 3 * D / a) ^ (m + 4) * (Crec * (B * (C' * R) ^ (m + 2))) +
            2 * (H + D) ^ 2 * (L : ℝ) ^ 2 * ((2 * (omega m).toReal) ^ 2 *
              ((1 + 3 * D / a) ^ (m + 2) * (2 + 6 * D / a) ^ (m + 2) / (2 * (a / 3) ^ 2) *
                R ^ (m + 2)))) =
          Cμ * (omega m).toReal / 2 * B * R ^ (m + 2) +
            2 * (1 + 3 * D / a) ^ (m + 4) * Crec * C' ^ (m + 2) * (L : ℝ) ^ 2 * R ^ (m + 2) +
            2 * (H + D) ^ 2 * ((2 * (omega m).toReal) ^ 2 * ((1 + 3 * D / a) ^ (m + 2) *
              (2 + 6 * D / a) ^ (m + 2) / (2 * (a / 3) ^ 2))) * B * R ^ (m + 2) := by
        rw [hCcarl]
        ring
      have hpos : 0 ≤ Cμ * (omega m).toReal / 2 * B * R ^ (m + 2) +
            2 * (1 + 3 * D / a) ^ (m + 4) * Crec * C' ^ (m + 2) * (L : ℝ) ^ 2 * R ^ (m + 2) +
            2 * (H + D) ^ 2 * ((2 * (omega m).toReal) ^ 2 * ((1 + 3 * D / a) ^ (m + 2) *
              (2 + 6 * D / a) ^ (m + 2) / (2 * (a / 3) ^ 2))) * B * R ^ (m + 2) := by
        have hC'0 : 0 ≤ C' := by linarith
        refine add_nonneg (add_nonneg ?_ ?_) ?_
        · exact mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hCμ0 hω) (by norm_num)) hB) hRk
        · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hX0)
            hCrec0) (pow_nonneg hC'0 _)) (sq_nonneg _)) hRk
        · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
            (mul_nonneg (sq_nonneg _) hκ)) hB) hRk
      have hmono : Ccarl * ((L : ℝ) ^ 2 + B) * R ^ (m + 2) ≤
          ((Clip + Real.toNNReal Ccarl + 1 : ℝ≥0) : ℝ) * ((L : ℝ) ^ 2 + B) * R ^ (m + 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCge (add_nonneg (sq_nonneg _) hB)) hRk
      linarith

end ParabolicRectifiability
