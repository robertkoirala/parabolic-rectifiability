import ParabolicRectifiability.Characterization.Proofs.Replacement.Statements

/-! # Whitney selection for the replacement of the bad region

Proves `b3_rp_whitneySelection : RpWhitneySelectionStatement` as
`b3_rp_whitneySelection_proof`: Whitney selection for a closed nonempty `G ⊆ Γ`.

Route. `FivefoldSelectionStatement` is the first hypothesis of the type. For
`z ∈ Γ \ G` put `s(z) = infDist z G > 0` (`G` closed, nonempty) and `r_z = s(z)/100`.
Since `Γ ∩ P(z, s(z)) ⊆ Γ \ G` and `σ(Γᶜ) = 0`, lower ADR gives `c s(z)^k ≤ σ(Γ \ G) < ∞`,
so `s(z) ≤ max 1 (σ(Γ \ G)/c)` (as `k ≥ 1`) and the radii are bounded. Fivefold selection is applied once
in `X = Space n` to the index type `↥(Γ \ G)`, centres `z`, radii `r_z`; it returns a
countable pairwise disjoint `J₀` whose fivefold dilates contain every centre, hence cover
`Γ \ G`. **Injective reindexing** (pattern of `b4_fivefold_density_selection_proof`): choose
an injection `q : J₀ → ℕ`, set `I = range q`, and transport through
`Equiv.ofInjective q : J₀ ≃ I`; disjointness of the relative balls transfers because the
equivalence is injective. Proximity: `infDist z G < 2 s(z) = 200 r_z` gives `g ∈ G` with
`dist z g < 200 r_z` (`Metric.infDist_lt_iff`). For `Γ \ G = ∅` the same construction gives
`I = ∅`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations
open ParabolicRectifiability.Characterization.ReplacementTree

/-- The relative ball of radius `infDist z G` around `z` misses `G`. -/
theorem b3rpw_ball_inter_subset {n : ℕ} {Γ G : Set (Space n)} (z : Space n) :
    Γ ∩ Metric.ball z (Metric.infDist z G) ⊆ Γ \ G := by
  rintro p ⟨hpΓ, hp⟩
  refine ⟨hpΓ, fun hpG => ?_⟩
  have h1 : Metric.infDist z G ≤ dist z p := Metric.infDist_le_dist_of_mem hpG
  have h2 : dist p z < Metric.infDist z G := hp
  rw [dist_comm] at h2
  linarith

/-- Radius bound from lower ADR: a relative ball `Γ ∩ P(z, s)` inside `Γ \ G` has
`c s^k ≤ σ(Γ \ G)`, hence `s ≤ max 1 (σ(Γ \ G)/c)`. -/
theorem b3rpw_radius_le {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)} {σ : Measure (Space n)}
    (hΓ : IsADRCarrier k c C Γ σ) {G : Set (Space n)} (hfin : σ (Γ \ G) < ⊤)
    {z : Space n} (hz : z ∈ Γ) {s : ℝ} (hs : 0 < s)
    (hsub : Γ ∩ Metric.ball z s ⊆ Γ \ G) :
    s ≤ max 1 ((σ (Γ \ G)).toReal / c) := by
  have hnull : σ Γᶜ = 0 := by
    have h := Measure.measure_compl_support (μ := σ)
    rwa [hΓ.support_eq] at h
  have hball : σ (Metric.ball z s) ≤ σ (Γ \ G) := by
    calc σ (Metric.ball z s) ≤ σ (Γ ∩ Metric.ball z s ∪ Γᶜ) := by
          refine measure_mono fun p hp => ?_
          by_cases h : p ∈ Γ
          · exact Or.inl ⟨h, hp⟩
          · exact Or.inr h
      _ ≤ σ (Γ ∩ Metric.ball z s) + σ Γᶜ := measure_union_le _ _
      _ = σ (Γ ∩ Metric.ball z s) := by rw [hnull, add_zero]
      _ ≤ σ (Γ \ G) := measure_mono hsub
  have hreal : c * s ^ k ≤ (σ (Γ \ G)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfin.ne).1 ((hΓ.lower z hz s hs).trans hball)
  rcases le_or_gt s 1 with h1 | h1
  · exact le_max_of_le_left h1
  · refine le_max_of_le_right ?_
    rw [le_div_iff₀ hΓ.lower_pos]
    have hsk : s ≤ s ^ k := le_self_pow₀ h1.le hΓ.dimension_pos.ne'
    calc s * c ≤ s ^ k * c := mul_le_mul_of_nonneg_right hsk hΓ.lower_pos.le
      _ = c * s ^ k := mul_comm _ _
      _ ≤ (σ (Γ \ G)).toReal := hreal

/-- Whitney selection: `RpWhitneySelectionStatement`. -/
theorem b3_rp_whitneySelection_proof : RpWhitneySelectionStatement := by
  intro h5 n k c C Γ σ hΓ G hGc hGne _hGΓ hfin
  -- Positivity of `infDist` off the closed nonempty `G`.
  have hpos : ∀ p : ↥(Γ \ G), 0 < Metric.infDist p.1 G := fun p =>
    (hGc.notMem_iff_infDist_pos hGne).1 p.2.2
  -- Fivefold selection once, in `X = Space n`, on the balls `P(z, infDist z G / 100)`, `z ∈ Γ \ G`.
  obtain ⟨J₀, hJc, hJd, hJcov⟩ := h5 (Space n) (↥(Γ \ G))
    (fun p => p.1) (fun p => Metric.infDist p.1 G / 100)
    (fun p => div_pos (hpos p) (by norm_num))
    ⟨max 1 ((σ (Γ \ G)).toReal / c) / 100, fun p => by
      have hb := b3rpw_radius_le hΓ hfin p.2.1 (hpos p) (b3rpw_ball_inter_subset p.1)
      show Metric.infDist p.1 G / 100 ≤ max 1 ((σ (Γ \ G)).toReal / c) / 100
      linarith⟩
  -- Injective reindexing: `q : J₀ → ℕ` injective, `I = range q`, `E : J₀ ≃ I`.
  have : Countable J₀ := hJc.to_subtype
  obtain ⟨q, hq⟩ := Countable.exists_injective_nat J₀
  obtain ⟨E, -⟩ : ∃ E : J₀ ≃ Set.range q, E = Equiv.ofInjective q hq := ⟨_, rfl⟩
  refine ⟨Set.range q, fun i => (E.symm i).1.1, fun i => Metric.infDist (E.symm i).1.1 G / 100,
    fun i => ⟨(E.symm i).1.2.1, div_pos (hpos (E.symm i).1) (by norm_num)⟩, ?_, ?_, ?_, ?_⟩
  · -- Disjointness transfers through the injective `E.symm`.
    intro i j hij
    have hne : (E.symm i).1 ≠ (E.symm j).1 := fun h =>
      hij (E.symm.injective (Subtype.ext h))
    have hd : Disjoint (Metric.ball (E.symm i).1.1 (Metric.infDist (E.symm i).1.1 G / 100))
        (Metric.ball (E.symm j).1.1 (Metric.infDist (E.symm j).1.1 G / 100)) :=
      hJd (E.symm i).2 (E.symm j).2 hne
    show Disjoint (Γ ∩ Metric.ball _ _) (Γ ∩ Metric.ball _ _)
    exact hd.mono inter_subset_right inter_subset_right
  · -- The relative balls lie in `Γ \ G`.
    intro i
    have h0 := hpos (E.symm i).1
    refine (inter_subset_inter_right Γ (Metric.ball_subset_ball ?_)).trans
      (b3rpw_ball_inter_subset (E.symm i).1.1)
    linarith
  · -- Every point of `Γ \ G` is a centre, hence in a selected fivefold dilate.
    intro p hp
    obtain ⟨j, hj, hpj⟩ := hJcov ⟨p, hp⟩
    refine mem_iUnion.2 ⟨E ⟨j, hj⟩, ?_⟩
    show p ∈ Metric.ball (E.symm (E ⟨j, hj⟩)).1.1
      (5 * (Metric.infDist (E.symm (E ⟨j, hj⟩)).1.1 G / 100))
    rw [Equiv.symm_apply_apply]
    exact hpj
  · -- Proximity: `infDist z G < 2 infDist z G = 200 r_z`.
    intro i
    have h0 := hpos (E.symm i).1
    have hlt : Metric.infDist (E.symm i).1.1 G <
        200 * (Metric.infDist (E.symm i).1.1 G / 100) := by linarith
    obtain ⟨g, hg, hdist⟩ := (Metric.infDist_lt_iff hGne).1 hlt
    exact ⟨g, hg, hdist⟩

end ParabolicRectifiability.Characterization
