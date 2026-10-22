import ParabolicRectifiability.Analysis.TraceExtension.Reservoirs.Geometry

/-! # Robust reservoir sets

The reservoir lemma `exists_reservoir_sets_proof` (the reservoir sets and their robust
simplex bound).

Constants, depending only on `m` and `c`: the slab width `θ = c / 2^(m+3)`, the frame
constant `s = frameConst m θ 2`, the mesh number `M = ⌈4 (m+1)² / s⌉ + 1`,
`c₁ = c / (2 (2M)^m)` and `c₂ = s / 2`.

Given `σ ≤ dp` with `σ(P(x,R)) ≥ c R^k`, the heavy grid cells (mass at least `c₁ R^k`)
cannot all lie in a slab of half-width `θ R`, whose volume in `P(x,R)` is at most
`c R^k / 4`. The successive selection therefore yields heavy cells `S_0, …, S_m` with
reference points forming a frame with lower bound `s R`; every probability barycenter
of `S_l` is within `m R / M` of its reference point, and the perturbation bound gives
`c₂ R`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

open Reservoirs

/-- **Reservoir lemma.** A source
`σ ≤ dp` with `σ(P(x,R)) ≥ c R^k` contains Borel sets `S_0, …, S_m ⊆ P(x,R)` of
mass at least `c₁ R^k` such that the barycenters of any probability measures
carried by them span a simplex with `σ_min ≥ c₂ R`. Constants depend only on `m, c`. -/
theorem exists_reservoir_sets_proof (m : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (x : Space m) (R : ℝ) (σ : Measure (Space m)),
      0 < R → σ ≤ parabolicVolume m →
      ENNReal.ofReal (c * R ^ (m + 2)) ≤ σ (Metric.ball x R) →
      ∃ S : Fin (m + 1) → Set (Space m),
        (∀ l, MeasurableSet (S l) ∧ S l ⊆ Metric.ball x R ∧
          ENNReal.ofReal (c₁ * R ^ (m + 2)) ≤ σ (S l)) ∧
        ∀ ρ : Fin (m + 1) → Measure (Space m),
          (∀ l, IsProbabilityMeasure (ρ l) ∧ ρ l (S l)ᶜ = 0) →
          ∀ v : Fin m → ℝ, c₂ * R * ‖WithLp.toLp 2 v‖ ≤
            ‖∑ l : Fin m, v l • ((∫ z, z.1 ∂ρ l.succ) - ∫ z, z.1 ∂ρ 0)‖ := by
  -- Constants.
  set θ : ℝ := c / 2 ^ (m + 3) with hθdef
  have hθ : 0 < θ := by rw [hθdef]; positivity
  set s : ℝ := frameConst m θ 2 with hsdef
  have hs : 0 < s := frameConst_pos hθ (by norm_num)
  set M : ℕ := ⌈4 * ((m : ℝ) + 1) ^ 2 / s⌉₊ + 1 with hMdef
  have hMpos : 0 < M := Nat.succ_pos _
  have hM' : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hMs : 4 * ((m : ℝ) + 1) ^ 2 ≤ s * M := by
    have h1 : 4 * ((m : ℝ) + 1) ^ 2 / s ≤ M := by
      calc 4 * ((m : ℝ) + 1) ^ 2 / s ≤ ⌈4 * ((m : ℝ) + 1) ^ 2 / s⌉₊ := Nat.le_ceil _
        _ ≤ M := by rw [hMdef]; push_cast; linarith
    rw [div_le_iff₀ hs] at h1
    linarith
  set N : ℕ := (2 * M) ^ m with hNdef
  have hN : (0 : ℝ) < N := by
    have : 0 < N := pow_pos (by omega) _
    exact_mod_cast this
  refine ⟨c / (2 * N), s / 2, div_pos hc (by linarith), half_pos hs, ?_⟩
  intro x R σ hR hσ hmass
  set a : ℝ := c * R ^ (m + 2) with hadef
  have ha : 0 < a := by rw [hadef]; positivity
  set B := Metric.ball x R with hBdef
  -- The grid cells cover the ball.
  have hcover : B ⊆ ⋃ g ∈ gridIndices m M, gridCell M x R g := by
    intro z hz
    exact mem_iUnion₂.mpr ⟨gridIndex M x R z, gridIndex_mem hMpos hR hz,
      mem_gridCell_of_mem_ball hz⟩
  have hheavy : a / (2 * ((gridIndices m M).card : ℝ)) = c / (2 * N) * R ^ (m + 2) := by
    rw [card_gridIndices, ← hNdef, hadef]
    ring
  -- Admissible reference points: spatial parts of points of heavy cells.
  set P : Spatial m → Prop := fun q => ∃ g ∈ gridIndices m M,
    ENNReal.ofReal (c / (2 * N) * R ^ (m + 2)) ≤ σ (gridCell M x R g) ∧
      ∃ z ∈ gridCell M x R g, z.1 = q with hPdef
  have hP : ∃ q, P q := by
    obtain ⟨g, hg, hgh, z, hz, -⟩ := exists_heavy_not_mem σ (gridIndices m M)
      (gridCell M x R) B ∅ hcover ha hmass (by simpa using ENNReal.ofReal_pos.mpr (half_pos ha))
    rw [hheavy] at hgh
    exact ⟨z.1, g, hg, hgh, z, hz, rfl⟩
  have hslab : ∀ e : Spatial m, ‖e‖ = 1 → ∀ q₀ : Spatial m,
      ∃ q, P q ∧ θ * R ≤ |inner ℝ e (q - q₀)| := by
    intro e he q₀
    set T : Set (Space m) := {z | |inner ℝ e z.1 - inner ℝ e q₀| < θ * R} with hT
    have hTsmall : σ (B ∩ T) < ENNReal.ofReal (a / 2) := by
      calc σ (B ∩ T) ≤ parabolicVolume m (B ∩ T) := Measure.le_iff'.mp hσ _
        _ ≤ ENNReal.ofReal (2 ^ (m + 1) * (θ * R) * R ^ (m + 1)) :=
          parabolicVolume_ball_inter_slab_le' x hR e he _ (mul_pos hθ hR).le
        _ < ENNReal.ofReal (a / 2) := by
          rw [ENNReal.ofReal_lt_ofReal_iff (half_pos ha), hθdef, hadef]
          have h2 : (0 : ℝ) < 2 ^ (m + 1) := by positivity
          have hRp : 0 < R ^ (m + 2) := by positivity
          have e1 : (2 : ℝ) ^ (m + 3) = 2 ^ (m + 1) * 4 := by ring
          have e2 : (2 : ℝ) ^ (m + 1) * (c / (2 ^ (m + 1) * 4) * R) * R ^ (m + 1) =
              c * R ^ (m + 2) / 4 := by
            field_simp
            try ring
          rw [e1, e2]
          nlinarith
    obtain ⟨g, hg, hgh, z, hz, hzT⟩ := exists_heavy_not_mem σ (gridIndices m M)
      (gridCell M x R) B T hcover ha hmass hTsmall
    rw [hheavy] at hgh
    refine ⟨z.1, ⟨g, hg, hgh, z, hz, rfl⟩, ?_⟩
    rw [inner_sub_right]
    simp only [hT, Set.mem_ofPred_eq, not_lt] at hzT
    exact hzT
  -- Successive selection of the reference points.
  obtain ⟨q, hqP, hqe⟩ := exists_successive_selection P hP hslab
  simp only [hPdef] at hqP
  choose g hg hgh z hz hzq using hqP
  refine ⟨fun l => gridCell M x R (g l), fun l => ⟨measurableSet_gridCell M x R (g l),
    gridCell_subset_ball M x R (g l), hgh l⟩, ?_⟩
  intro ρ hρ v
  -- The reference frame.
  have hd : ∀ l : Fin m, ‖q l.succ - q 0‖ ≤ 2 * R := by
    intro l
    have h1 := norm_spatial_sub_lt_of_mem_ball (gridCell_subset_ball M x R _ (hz l.succ))
    have h2 := norm_spatial_sub_lt_of_mem_ball (gridCell_subset_ball M x R _ (hz 0))
    rw [hzq] at h1 h2
    calc ‖q l.succ - q 0‖ ≤ ‖q l.succ - x.1‖ + ‖x.1 - q 0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ R + R := by rw [norm_sub_rev x.1]; exact add_le_add h1.le h2.le
      _ = 2 * R := by ring
  have hframe := frame_lower_bound (E := Spatial m) hθ (by norm_num : (0 : ℝ) ≤ 2) hR
    (fun l => q l.succ - q 0) hd hqe
  -- Barycenters stay near the reference points.
  have hb : ∀ l, ‖(∫ w, w.1 ∂ρ l) - q l‖ ≤ (m / M : ℝ) * R := by
    intro l
    have := (hρ l).1
    have := norm_integral_spatial_sub_le (ρ l) _ (hρ l).2 (q l) (C := m * (R / M))
      fun w hw => by
        rw [← hzq l]
        exact norm_sub_le_of_mem_gridCell hMpos hR hw (hz l)
    calc ‖(∫ w, w.1 ∂ρ l) - q l‖ ≤ m * (R / M) := this
      _ = (m / M : ℝ) * R := by ring
  have hpert := perturbed_lower_bound q (fun l => ∫ w, w.1 ∂ρ l) hb hframe v
  have hconst : s / 2 ≤ s - 2 * m * ((m : ℝ) / M) := by
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [show 2 * (m : ℝ) * (m / M) = 2 * m ^ 2 / M by ring]
    have : 2 * (m : ℝ) ^ 2 / M ≤ s / 2 := by
      rw [div_le_iff₀ hM']
      nlinarith
    linarith
  calc s / 2 * R * ‖WithLp.toLp 2 v‖ ≤ (s - 2 * m * ((m : ℝ) / M)) * R * ‖WithLp.toLp 2 v‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconst hR.le) (norm_nonneg _)
    _ ≤ _ := hpert

end ParabolicRectifiability
