import ParabolicRectifiability.Foundations.Assembly.ProvedStatements
import ParabolicRectifiability.Main

/-! # The three density lemmas

The packing-mass and upper-density domination lemmas are independent statements. The
absolute-continuity bridge is assembled as follows:
* level sets `G_{j,m} = O ∩ {Θ_*^k ≤ j} ∩ {S_{μ,T}^R ≤ m}` (Borel by
  `densities_measurable_of_locallyRadon` and `measurable_squareEnergy`), and the
  restricted sources `ν_{j,m} = μ⌊G_{j,m}` (locally Radon by
  `restrict_isFiniteMeasureOnCompacts_innerRegular`);
* restriction monotonicity (`squareEnergy_restrict_le`; `lowerDensity_mono_measure`
  below) gives `S_{ν_{j,m},T}^R ≤ m` and `Θ_*^k(ν_{j,m}) ≤ j`, `ν_{j,m}`-almost everywhere;
* the growth bound `ν_{j,m}(P(q,ρ)) ≤ C_n (j + m) ρ^k`, `0 < ρ ≤ R/2`, is
  `exists_boundedGrowth_constant`, fed with the core theorem
  `family_rectifiable_reifenberg` (applied directly) and
  `restrict_ball_le_of_packing_lowerDensity`;
* `absolutelyContinuous_hausdorffP_of_growth` gives `ν_{j,m} ≪ H_P^k`;
* the countable union of the `G_{j,m}` carries `μ⌊O` up to the `μ`-null exception.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- Packing turns lower density into retained mass. -/
theorem packing_mass_skeleton : PackingMassStatement :=
  restrict_ball_le_of_packing_lowerDensity

/-- Positive upper density gives Hausdorff domination. -/
theorem upper_density_domination_skeleton : UpperDensityDominationStatement :=
  hausdorffP_le_of_upperDensity_ge

/-- The lower density is monotone in the source (restriction monotonicity). -/
theorem lowerDensity_mono_measure {n : ℕ} {ν μ : Measure (Space n)} (h : ν ≤ μ) (k : ℕ)
    (z : Space n) : lowerDensity ν k z ≤ lowerDensity μ k z := by
  unfold lowerDensity
  refine Filter.liminf_le_liminf (Filter.Eventually.of_forall fun r => ?_)
  unfold densityRatio
  gcongr

/-- **The absolute-continuity bridge**, assembled from the pieces listed above. -/
theorem ac_bridge_skeleton : ACBridgeStatement := by
  intro n hn k hk hkn O hO μ hμ hreg R hR T hT hae
  obtain ⟨C, hC, hbg⟩ := exists_boundedGrowth_constant n hn
    (family_rectifiable_reifenberg n hn) restrict_ball_le_of_packing_lowerDensity
  have hmeasD : Measurable (lowerDensity μ k) :=
    (densities_measurable_of_locallyRadon n hn k hk hkn μ hμ hreg).1
  have hmeasS : Measurable (squareEnergy μ k T R) := measurable_squareEnergy μ k T R
  let G : ℕ → ℕ → Set (Space n) := fun j m =>
    O ∩ {z | lowerDensity μ k z ≤ ENNReal.ofReal j} ∩
      {z | squareEnergy μ k T R z ≤ ENNReal.ofReal m}
  have hG : ∀ j m, MeasurableSet (G j m) := fun j m =>
    (hO.measurableSet.inter (measurableSet_le hmeasD measurable_const)).inter
      (measurableSet_le hmeasS measurable_const)
  have hac : ∀ j m, μ.restrict (G j m) ≪ hausdorffP n k := by
    intro j m
    obtain ⟨hνfin, hνreg⟩ :=
      restrict_isFiniteMeasureOnCompacts_innerRegular n hn μ hμ hreg (G j m) (hG j m)
    have hνae : ∀ᵐ z ∂(μ.restrict (G j m)),
        squareEnergy (μ.restrict (G j m)) k T R z ≤ ENNReal.ofReal m ∧
          lowerDensity (μ.restrict (G j m)) k z ≤ ENNReal.ofReal j :=
      (ae_restrict_mem (hG j m)).mono fun z hz =>
        ⟨(squareEnergy_restrict_le μ (G j m) k T R z).trans hz.2,
          (lowerDensity_mono_measure Measure.restrict_le_self k z).trans hz.1.2⟩
    have hgrowth := hbg k hk hkn T hT _ hνfin hνreg j m R (Nat.cast_nonneg j)
      (Nat.cast_nonneg m) hR hνae
    exact absolutelyContinuous_hausdorffP_of_growth n hn k hk hkn _ hνfin hνreg
      (C * (j + m)) (R / 2) (by positivity) fun p r hr hrR => hgrowth p r hr hrR
  intro s hs
  rw [Measure.restrict_apply' hO.measurableSet]
  have hbad : μ {z | z ∈ O ∧ ¬ (lowerDensity μ k z < ⊤ ∧ squareEnergy μ k T R z < ⊤)} = 0 :=
    measure_mono_null (fun z hz => fun h => hz.2 (h hz.1)) (ae_iff.1 hae)
  have hcover : s ∩ O ⊆ (⋃ j, ⋃ m, s ∩ G j m) ∪
      {z | z ∈ O ∧ ¬ (lowerDensity μ k z < ⊤ ∧ squareEnergy μ k T R z < ⊤)} := by
    intro z hz
    by_cases hfin : lowerDensity μ k z < ⊤ ∧ squareEnergy μ k T R z < ⊤
    · obtain ⟨j, hj⟩ := ENNReal.exists_nat_gt hfin.1.ne
      obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hfin.2.ne
      refine Or.inl (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨m, hz.1, ⟨hz.2, ?_⟩, ?_⟩⟩)
      · show lowerDensity μ k z ≤ ENNReal.ofReal j
        rw [ENNReal.ofReal_natCast]
        exact hj.le
      · show squareEnergy μ k T R z ≤ ENNReal.ofReal m
        rw [ENNReal.ofReal_natCast]
        exact hm.le
    · exact Or.inr ⟨hz.2, hfin⟩
  refine measure_mono_null hcover (measure_union_null (measure_iUnion_null fun j =>
    measure_iUnion_null fun m => ?_) hbad)
  have h0 := hac j m hs
  rwa [Measure.restrict_apply' (hG j m)] at h0

end ParabolicRectifiability.Foundations
