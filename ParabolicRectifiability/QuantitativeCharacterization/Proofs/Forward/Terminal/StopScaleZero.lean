import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal

/-! # The zero set of the stopping scale

Proof of `d1c_stopScaleZero_proof`:
`ρ(z) = 0 ↔ z ∈ 𝒞₀ = ⋂_j closure G_j`, with the two statements `AncestorStatement` and
`StopScaleLipschitzStatement` as hypotheses (implication form).

* (⇒) fix a depth `j` and `ε > 0`; since `ρ(z) = 0`, choose a member `Q`
  with `ℓ_Q + dist_P(z, Q) < min(ℓ_{root+j}, ε/2)`; its level is at least `root + j`; its member
  ancestor at that level contains `Q`; a point of `Q` lies within `ε` of `z`. As `ε` is arbitrary,
  `z ∈ closure G_j`.
* (⇐) `z ∈ closure G_m` for a depth `m` with `ℓ_m < ρ(z)/2` gives a member `Q` of depth `m` and
  `y ∈ Q` with `dist(z, y) < ρ(z)/2`, so `ρ(z) ≤ ℓ_Q + dist(z, y) < ρ(z)`, unless `ρ(z) = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

/-- The ten-adic scales are positive. -/
theorem d1czero_scale_pos {r₀ : ℝ} (h : 0 < r₀) (j : ℕ) : 0 < coherentScale r₀ j := by
  unfold coherentScale
  positivity

/-- The ten-adic scales decrease. -/
theorem d1czero_scale_anti {r₀ : ℝ} (h : 0 < r₀) {i j : ℕ} (hij : i ≤ j) :
    coherentScale r₀ j ≤ coherentScale r₀ i := by
  unfold coherentScale
  exact div_le_div_of_nonneg_left h.le (by positivity) (pow_le_pow_right₀ (by norm_num) hij)

/-- The ten-adic scales become arbitrarily small. -/
theorem d1czero_scale_small (r₀ : ℝ) {ε : ℝ} (hε : 0 < ε) : ∃ j : ℕ, coherentScale r₀ j < ε := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (r₀ / ε) (by norm_num : (1 : ℝ) < 10)
  refine ⟨j, ?_⟩
  unfold coherentScale
  have h10 : (0 : ℝ) < 10 ^ j := by positivity
  rw [div_lt_iff₀ h10]
  rw [div_lt_iff₀ hε] at hj
  linarith [mul_comm ((10 : ℝ) ^ j) ε]

/-- The centre of a cell lies in its cell. -/
theorem d1czero_center_mem_cell {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} (P : DirectPartition E ℓ₀)
    {Q : ℕ × Space n} (hQ : P.IsCell Q) : Q.2 ∈ P.cellOf Q := by
  apply P.inner_subset Q.1 Q.2 hQ
  exact ⟨P.center_subset Q.1 hQ,
    Metric.mem_ball_self (div_pos (d1czero_scale_pos P.scale_pos Q.1) (by norm_num))⟩

/-- **The zero set of the stopping scale** (`StopScaleZeroStatement`, in implication form). -/
theorem d1c_stopScaleZero_proof :
    AncestorStatement → StopScaleLipschitzStatement → StopScaleZeroStatement := by
  intro hAnc hLip n E ℓ₀ P μ k Λ b 𝒢 z
  obtain ⟨hnonneg, -, hle, -⟩ := hLip n E ℓ₀ P μ k Λ b 𝒢
  have hroot : 0 < ℓ₀ := P.scale_pos
  have : Nonempty 𝒢.members := ⟨⟨𝒢.root, 𝒢.root_mem⟩⟩
  constructor
  · intro hz
    show z ∈ ⋂ j, closure (𝒢.levelSet j)
    refine Set.mem_iInter.mpr fun j => ?_
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hmin : 0 < min (P.scale (𝒢.root.1 + j)) (ε / 2) :=
      lt_min (d1czero_scale_pos hroot _) (by linarith)
    have hlt : (⨅ Q : 𝒢.members, (P.scale Q.1.1 + Metric.infDist z (P.cellOf Q.1))) <
        min (P.scale (𝒢.root.1 + j)) (ε / 2) := by
      have h0 : 𝒢.stopScale z = 0 := hz
      unfold GoodRegion.stopScale at h0
      rw [h0]
      exact hmin
    obtain ⟨Q, hQ⟩ := exists_lt_of_ciInf_lt hlt
    have hA := lt_of_lt_of_le hQ (min_le_left _ _)
    have hB := lt_of_lt_of_le hQ (min_le_right _ _)
    have hinf : 0 ≤ Metric.infDist z (P.cellOf Q.1) := Metric.infDist_nonneg
    have hsc : 0 < P.scale Q.1.1 := d1czero_scale_pos hroot _
    have hdepth : 𝒢.root.1 + j ≤ Q.1.1 := by
      by_contra hcon
      have h' : P.scale (𝒢.root.1 + j) ≤ P.scale Q.1.1 :=
        d1czero_scale_anti hroot (le_of_lt (not_le.mp hcon))
      linarith
    obtain ⟨Q', hQ'mem, hQ'lvl, hsub⟩ :=
      (hAnc n E ℓ₀ P μ k Λ b 𝒢).2 Q.1 Q.2 (𝒢.root.1 + j) (Nat.le_add_right _ _) hdepth
    have hne : (P.cellOf Q.1).Nonempty :=
      ⟨Q.1.2, d1czero_center_mem_cell P (𝒢.below_root Q.1 Q.2).1⟩
    obtain ⟨y, hy, hzy⟩ := (Metric.infDist_lt_iff hne).mp (show
      Metric.infDist z (P.cellOf Q.1) < ε / 2 by linarith)
    refine ⟨y, ?_, by linarith⟩
    simp only [GoodRegion.levelSet, Set.mem_iUnion]
    exact ⟨Q', ⟨hQ'mem, hQ'lvl⟩, hsub hy⟩
  · intro hz
    by_contra hne
    have hpos : 0 < 𝒢.stopScale z := lt_of_le_of_ne (hnonneg z) (Ne.symm hne)
    obtain ⟨m, hm⟩ := d1czero_scale_small ℓ₀ (half_pos hpos)
    have hz' : z ∈ ⋂ j, closure (𝒢.levelSet j) := hz
    have hzm : z ∈ closure (𝒢.levelSet m) := Set.mem_iInter.mp hz' m
    obtain ⟨y, hy, hzy⟩ := Metric.mem_closure_iff.mp hzm (𝒢.stopScale z / 2) (half_pos hpos)
    simp only [GoodRegion.levelSet, Set.mem_iUnion] at hy
    obtain ⟨Q, ⟨hQmem, hQlvl⟩, hyQ⟩ := hy
    have h1 := hle Q hQmem z
    have h2 : Metric.infDist z (P.cellOf Q) ≤ dist z y := Metric.infDist_le_dist_of_mem hyQ
    have h3 : P.scale Q.1 ≤ coherentScale ℓ₀ m := by
      show coherentScale ℓ₀ Q.1 ≤ coherentScale ℓ₀ m
      rw [hQlvl]
      exact d1czero_scale_anti hroot (Nat.le_add_left _ _)
    linarith

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
