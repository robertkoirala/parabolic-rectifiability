import ParabolicRectifiability.Measure.Neck.Certificates
import ParabolicRectifiability.Metric.BaseVolume

/-!
# Parameter-volume packing of the centers of a certified neck

Proof of `certified_center_packing`, as `certified_center_packing_proof`.

Centers `c_i` of a certified neck over `P(q, R)` with
`d_P(c_i, c_j) ≥ (24/25) max(r_i, r_j)` and `r_i ≤ R/η` have parameters `p_i` in the
neck's exact parametrization (distortion `L`). The forward Lipschitz bound gives
`d(p_i, p_j) ≥ (24/(25L)) max(r_i, r_j)`, so the full parameter balls of radii
`s_i = 6 r_i/(25L)` are disjoint; the inverse bound and `c_i ∈ closure P(q,R)` put them in
one parameter ball of radius `(2L + 1/η) R`. The parameter space is `ℝ^k` with Lebesgue
measure (horizontal; the physical time is only used on the parameter set itself, through
the bi-Lipschitz bounds of the center map) or `ℝ^{k-2} × ℝ` with its parabolic reference
volume (vertical); in both cases balls of radius `s` have volume `ω s^k`, which gives
`∑ r_i^k ≤ ((25L/6)(2L + 1/η))^k R^k`. The constant is made uniform over `1 ≤ k < n + 2`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators Function

/-- Packing by volume: disjoint balls `P(p_i, s_i)` inside a ball of radius `ρ₀`, in a space
whose balls have volume `ω s^k`, satisfy `∑ s_i^k ≤ ρ₀^k`. -/
theorem ms7_tsum_le_of_disjoint_balls {Y : Type*} [MetricSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] (μ : Measure Y) (ω : ℝ≥0∞) (hω0 : ω ≠ 0) (hωt : ω ≠ ⊤) (k : ℕ)
    (hball : ∀ (x : Y) (s : ℝ), 0 < s → μ (Metric.ball x s) = ω * ENNReal.ofReal s ^ k)
    {I : Type*} [Countable I] (p : I → Y) (s : I → ℝ) (hs : ∀ i, 0 < s i)
    (hdisj : Pairwise (Disjoint on fun i => Metric.ball (p i) (s i)))
    (x₀ : Y) (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) (hsub : ∀ i, Metric.ball (p i) (s i) ⊆ Metric.ball x₀ ρ₀) :
    ∑' i, ENNReal.ofReal (s i) ^ k ≤ ENNReal.ofReal ρ₀ ^ k := by
  have h1 : ∑' i, μ (Metric.ball (p i) (s i)) ≤ μ (Metric.ball x₀ ρ₀) := by
    rw [← measure_iUnion hdisj (fun i => measurableSet_ball)]
    exact measure_mono (iUnion_subset hsub)
  rw [tsum_congr fun i => hball (p i) (s i) (hs i), hball x₀ ρ₀ hρ₀,
    ENNReal.tsum_mul_left] at h1
  exact (ENNReal.mul_le_mul_iff_right hω0 hωt).mp h1

/-- Packing of separated points through a bi-Lipschitz parametrization with distortion `L`
into a parameter space whose balls have volume `ω s^k`. -/
theorem ms7_param_packing {X Y : Type*} [PseudoMetricSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure Y) (ω : ℝ≥0∞) (hω0 : ω ≠ 0)
    (hωt : ω ≠ ⊤) (k : ℕ)
    (hball : ∀ (x : Y) (s : ℝ), 0 < s → μ (Metric.ball x s) = ω * ENNReal.ofReal s ^ k)
    {L η R : ℝ} (hL : 1 ≤ L) (hη : 0 < η) (hR : 0 < R) (q : X)
    {I : Type*} [Countable I] (c : I → X) (r : I → ℝ) (p : I → Y)
    (hc : ∀ i, c i ∈ Metric.closedBall q R) (hr : ∀ i, 0 < r i ∧ r i ≤ R / η)
    (hsep : ∀ i j, i ≠ j → 24 / 25 * max (r i) (r j) ≤ dist (c i) (c j))
    (hfwd : ∀ i j, dist (c i) (c j) ≤ L * dist (p i) (p j))
    (hinv : ∀ i j, L⁻¹ * dist (p i) (p j) ≤ dist (c i) (c j)) :
    ∑' i, ENNReal.ofReal (r i) ^ k ≤
      ENNReal.ofReal ((25 * L / 6 * (2 * L + 1 / η)) ^ k * R ^ k) := by
  have hL0 : 0 < L := by linarith
  have hLne : L ≠ 0 := hL0.ne'
  have hη' : 0 < 1 / η := one_div_pos.mpr hη
  rcases isEmpty_or_nonempty I with hI | ⟨⟨i₀⟩⟩
  · simp [tsum_empty]
  obtain ⟨s, hs_def⟩ : ∃ s : I → ℝ, s = fun i => 6 * r i / (25 * L) := ⟨_, rfl⟩
  have hs : ∀ i, 0 < s i := fun i => by
    rw [hs_def]; exact div_pos (mul_pos (by norm_num) (hr i).1) (mul_pos (by norm_num) hL0)
  have hLs : ∀ i, L * s i = 6 * r i / 25 := fun i => by
    rw [hs_def]; field_simp
  have hrs : ∀ i, r i = 25 * L / 6 * s i := fun i => by
    rw [hs_def]; field_simp
  have hsr : ∀ i, s i ≤ r i := fun i => by
    have h1 := hLs i
    have h2 := (hr i).1
    have h3 := hs i
    nlinarith
  -- the parameter balls are disjoint
  have hdisj : Pairwise (Disjoint on fun i => Metric.ball (p i) (s i)) := by
    intro i j hij
    refine Metric.ball_disjoint_ball (le_of_mul_le_mul_left ?_ hL0)
    have h1 := hsep i j hij
    have h2 := hfwd i j
    have h3 := le_max_left (r i) (r j)
    have h4 := le_max_right (r i) (r j)
    have h5 := (hr i).1
    rw [mul_add, hLs, hLs]
    linarith
  -- and lie in one parameter ball
  have hdc : ∀ i j, dist (c i) (c j) ≤ 2 * R := fun i j => by
    have h1 := Metric.mem_closedBall.mp (hc i)
    have h2 := Metric.mem_closedBall.mp (hc j)
    linarith [dist_triangle_right (c i) (c j) q]
  have hdp : ∀ i j, dist (p i) (p j) ≤ L * (2 * R) := fun i j => by
    have h := mul_le_mul_of_nonneg_left (hinv i j) hL0.le
    rw [← mul_assoc, mul_inv_cancel₀ hL0.ne', one_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hdc i j) hL0.le)
  have hsub : ∀ i, Metric.ball (p i) (s i) ⊆ Metric.ball (p i₀) ((2 * L + 1 / η) * R) := by
    intro i y hy
    rw [Metric.mem_ball] at hy ⊢
    have h1 := dist_triangle y (p i) (p i₀)
    have h2 := hdp i i₀
    have h3 : s i ≤ R / η := (hsr i).trans (hr i).2
    have h4 : R / η = 1 / η * R := by ring
    linarith
  have hρ₀ : 0 < (2 * L + 1 / η) * R := by positivity
  have hsum := ms7_tsum_le_of_disjoint_balls μ ω hω0 hωt k hball p s hs hdisj (p i₀) _ hρ₀ hsub
  have hA : 0 ≤ 25 * L / 6 := by positivity
  calc ∑' i, ENNReal.ofReal (r i) ^ k
      = ∑' i, ENNReal.ofReal (25 * L / 6) ^ k * ENNReal.ofReal (s i) ^ k := by
        refine tsum_congr fun i => ?_
        rw [hrs i, ENNReal.ofReal_mul hA, mul_pow]
    _ = ENNReal.ofReal (25 * L / 6) ^ k * ∑' i, ENNReal.ofReal (s i) ^ k :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (25 * L / 6) ^ k * ENNReal.ofReal ((2 * L + 1 / η) * R) ^ k := by
        gcongr
    _ = ENNReal.ofReal ((25 * L / 6 * (2 * L + 1 / η)) ^ k * R ^ k) := by
        rw [← mul_pow, ← ENNReal.ofReal_mul hA,
          ← ENNReal.ofReal_pow (mul_nonneg hA hρ₀.le), ← mul_assoc, mul_pow]

/-- **`certified_center_packing`**: centers of a
certified neck with `d_P(c_i, c_j) ≥ (24/25) max(r_i, r_j)` and `r_i ≤ R/η` satisfy
`∑ r_i^k ≤ C_v R^k`, with `C_v = ((25L/6)(2L + 1/η))^{n+1}`. -/
theorem certified_center_packing_proof (n : ℕ) (L η : ℝ) (hL : 1 ≤ L) (hη : 0 < η) :
    ∃ Cv : ℝ, 0 < Cv ∧ ∀ {k : ℕ} {T : NeckType} {ι : Type} {q : Space n}
      {R c₀ Cd Cs σ δ E κ θ γ : ℝ} (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ)
      (ν : Measure (Space n)) (B : ℝ), 1 ≤ k → k < n + 2 → N.IsCertified ν B B L →
      ∀ (I : Type) [Countable I] (c : I → Space n) (r : I → ℝ),
        (∀ i, c i ∈ N.centers) → (∀ i, 0 < r i ∧ r i ≤ R / η) →
        (∀ i j, i ≠ j → 24 / 25 * max (r i) (r j) ≤ dist (c i) (c j)) →
        ∑' i, ENNReal.ofReal (r i) ^ k ≤ ENNReal.ofReal (Cv * R ^ k) := by
  have hη' : 0 < 1 / η := one_div_pos.mpr hη
  have hM : 1 ≤ 25 * L / 6 * (2 * L + 1 / η) := by
    have h1 : 1 ≤ 25 * L / 6 := by linarith
    have h2 : 1 ≤ 2 * L + 1 / η := by linarith
    exact one_le_mul_of_one_le_of_one_le h1 h2
  refine ⟨(25 * L / 6 * (2 * L + 1 / η)) ^ (n + 1), by positivity, ?_⟩
  intro k T ι q R c₀ Cd Cs σ δ E κ θ γ N ν B _hk hkn hcert I _ c r hc hr hsep
  have hR : 0 < R := N.parameters.R_pos
  have hcR : ∀ i, c i ∈ Metric.closedBall q R := fun i => N.centers_subset (hc i)
  suffices h : ∑' i, ENNReal.ofReal (r i) ^ k ≤
      ENNReal.ofReal ((25 * L / 6 * (2 * L + 1 / η)) ^ k * R ^ k) by
    refine h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hM (by omega)) (pow_nonneg hR.le k)))
  cases T with
  | horizontal =>
    obtain ⟨G, -, A, τ, -, hφ, hrange⟩ := hcert.parametrization.1 rfl
    have hcmem : ∀ i, ∃ u : A, point (G u) (τ u) = c i := fun i => by
      have h := hc i
      rw [← hrange] at h
      exact Set.mem_range.mp h
    choose u hu using hcmem
    refine ms7_param_packing (volume : Measure (Spatial k)) (omega k) (omega_pos k).ne'
      (omega_lt_top k).ne k (fun x s hs => volume_spatial_ball x hs) hL hη hR q c r
      (fun i => (u i : Spatial k)) hcR hr hsep ?_ ?_
    · intro i j
      rw [← hu i, ← hu j]
      exact (hφ (u i) (u j)).2
    · intro i j
      rw [← hu i, ← hu j]
      exact (hφ (u i) (u j)).1
  | vertical =>
    obtain ⟨G, A, hG, -, himg⟩ := hcert.parametrization.2 rfl
    have h2k : 2 ≤ k := (show 2 ≤ k ∧ k ≤ n + 2 from N.available).1
    have hcmem : ∀ i, ∃ p : Space (k - 2), timePreservingMap G p = c i := fun i => by
      have h := hc i
      rw [← himg] at h
      obtain ⟨p, -, hp⟩ := h
      exact ⟨p, hp⟩
    choose p hp using hcmem
    refine ms7_param_packing (parabolicVolume (k - 2)) (2 * omega (k - 2))
      (mul_ne_zero two_ne_zero (omega_pos _).ne')
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (omega_lt_top _).ne) k ?_ hL hη hR q c r p
      hcR hr hsep ?_ ?_
    · intro x s hs
      rw [parabolicVolume_ball x s hs, Nat.sub_add_cancel h2k]
    · intro i j
      rw [← hp i, ← hp j]
      exact (hG (p i) (p j)).2
    · intro i j
      rw [← hp i, ← hp j]
      exact (hG (p i) (p j)).1

end ParabolicRectifiability
