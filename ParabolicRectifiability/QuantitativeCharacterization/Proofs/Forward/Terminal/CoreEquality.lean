import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal

/-! # Core equality and core limits (`d1c_coreEquality`)

Proof of `d1c_coreEquality_proof`.

* `⋂_j closure S_j ⊆ 𝒞₀`: on `S_j` (`j ≥ 1`) the cutoff is below `r_j`, so `ρ < 1000 r_j` there
  (the cutoff's grid bracket on `0 < ρ ≤ ℓ_*`); `ρ` is `1`-Lipschitz, so `ρ ≤ 1000 r_j` on
  `closure S_j`; as `r_j → 0`, `ρ = 0` on the intersection, which is `𝒞₀`.
* `𝒞₀ ⊆ closure S_j`: `𝒞₀ ⊆ closure G_0 ⊆ closure S`; for `z ∈ 𝒞₀` (`ρ(z) = 0`) every terminal
  centre `c` of a stage `m ≤ j` has `dist(c, z) ≥ ρ(c) ≥ 100 f(c) = 100 r_m`, so a point of `S`
  within `r_j` of `z` lies in no hole of the stages `≤ j`, i.e. in `S_j`.
* Core limits: for `z ∈ 𝒞₀` and each `m`, a point of `S_{m+1}` within `r_{m+1}` of `z` lies in an
  open net ball `P(g, κ_net r_{m+1})` of a candidate `g` of stage `m + 1` (`cand_cover`), so
  `dist(g, z) < (1 + κ_net) r_{m+1} → 0`.

The statements `StopScaleLipschitzStatement`, `StopScaleZeroStatement`, `CutoffStatement` and
`StageFactsStatement` enter as hypotheses (implication form). The edge case "empty core" is
covered: both sides are then empty and the limit clause is vacuous. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

section D1CCore

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

theorem d1ccore_stageScale_pos (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) : 0 < stageScale 𝒢 j := by
  unfold stageScale coherentScale
  have := d1c_rootScale_pos 𝒢
  positivity

theorem d1ccore_stageScale_anti (𝒢 : GoodRegion P μ k Λ b) {j j' : ℕ} (h : j ≤ j') :
    stageScale 𝒢 j' ≤ stageScale 𝒢 j := by
  unfold stageScale coherentScale
  have := d1c_rootScale_pos 𝒢
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_right₀ (by norm_num) h)

theorem d1ccore_tendsto_stageScale (𝒢 : GoodRegion P μ k Λ b) :
    Tendsto (fun j => stageScale 𝒢 j) atTop (𝓝 0) := by
  have h : Tendsto (fun j : ℕ => (48 * 𝒢.rootScale) * ((1 : ℝ) / 10) ^ j) atTop
      (𝓝 ((48 * 𝒢.rootScale) * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
  rw [mul_zero] at h
  refine h.congr fun j => ?_
  simp only [stageScale, coherentScale, div_pow, one_pow, mul_one_div]

/-- `r_{j+1} → 0`, scaled by a constant. -/
theorem d1ccore_tendsto_const_mul_succ (𝒢 : GoodRegion P μ k Λ b) (a : ℝ) :
    Tendsto (fun j : ℕ => a * stageScale 𝒢 (j + 1)) atTop (𝓝 0) := by
  have h := ((d1ccore_tendsto_stageScale 𝒢).comp (tendsto_add_atTop_nat 1)).const_mul a
  rw [mul_zero] at h
  exact h

/-- The limiting core lies in the closure of the root cell (`G_0 ⊆ S`). -/
theorem d1ccore_limitCore_subset_closure (𝒢 : GoodRegion P μ k Λ b) :
    𝒢.limitCore ⊆ closure 𝒢.rootCell := by
  intro z hz
  have h0 : z ∈ closure (𝒢.levelSet 0) := by
    unfold GoodRegion.limitCore at hz
    exact mem_iInter.mp hz 0
  refine closure_mono ?_ h0
  intro w hw
  simp only [GoodRegion.levelSet, mem_iUnion, exists_prop] at hw
  obtain ⟨Q, ⟨hQ, -⟩, hwQ⟩ := hw
  exact (𝒢.below_root Q hQ).2.2 hwQ

end D1CCore

/-- **Core equality and core limits** (`d1c_coreEquality`). -/
theorem d1c_coreEquality_proof :
    StopScaleLipschitzStatement → StopScaleZeroStatement → CutoffStatement →
      StageFactsStatement → CoreEqualityStatement := by
  intro hLip hZero hCut hSF n E ℓ₀ P μ k Λ b 𝒢 C hsel
  have hsf := hSF n E ℓ₀ P μ k Λ b 𝒢 C hsel
  obtain ⟨hLip0, hLipD, -, hLip4⟩ := hLip n E ℓ₀ P μ k Λ b 𝒢
  obtain ⟨hCut1, -, -, hCut4⟩ := hCut n E ℓ₀ P μ k Λ b 𝒢
  have hcont : Continuous 𝒢.stopScale := (LipschitzWith.of_le_add hLipD).continuous
  -- `ρ < 1000 r_j` on `S_j`, `j ≥ 1`
  have hbound : ∀ j, 1 ≤ j → ∀ w ∈ C.kept 𝒢 j, 𝒢.stopScale w < 1000 * stageScale 𝒢 j := by
    intro j hj w hw
    have hpos_j := d1ccore_stageScale_pos 𝒢 j
    rcases (hLip0 w).eq_or_lt with h | h
    · rw [← h]
      linarith
    · have hle : 𝒢.stopScale w ≤ 𝒢.rootScale :=
        hLip4 𝒢.root 𝒢.root_mem w (hsf.kept_subset j hw)
      obtain ⟨m, _, hm, _, hm2⟩ := hCut4 w h hle
      have hdone := hsel.term_done j hj w hw
      rw [hm] at hdone
      linarith
  -- points of `S` near a core point survive the stages `≤ j`
  have hnear : ∀ z ∈ 𝒢.limitCore, ∀ j, ∀ w ∈ 𝒢.rootCell, dist w z < stageScale 𝒢 j →
      w ∈ C.kept 𝒢 j := by
    intro z hz j
    have hρz : 𝒢.stopScale z = 0 := (hZero n E ℓ₀ P μ k Λ b 𝒢 z).mpr hz
    induction j with
    | zero => intro w hw _; exact hw
    | succ m ih =>
      intro w hw hwz
      have hwm : w ∈ C.kept 𝒢 m :=
        ih w hw (lt_of_lt_of_le hwz (d1ccore_stageScale_anti 𝒢 (Nat.le_succ m)))
      show w ∈ C.kept 𝒢 m \ ⋃ (i : ℕ) (_ : i < C.termCount (m + 1)),
        Metric.ball (C.term (m + 1) i) (stageCutoff 𝒢 (C.term (m + 1) i))
      refine ⟨hwm, fun hu => ?_⟩
      obtain ⟨i, hi, hwi⟩ := mem_iUnion₂.mp hu
      have hrad := hsf.term_radius (m + 1) (by omega) i hi
      have h100 := (hCut1 (C.term (m + 1) i)).2
      have hρc : 𝒢.stopScale (C.term (m + 1) i) ≤
          𝒢.stopScale z + dist (C.term (m + 1) i) z := hLipD _ _
      rw [Metric.mem_ball, hrad, dist_comm] at hwi
      rw [hrad] at h100
      have htri : dist (C.term (m + 1) i) z ≤ dist (C.term (m + 1) i) w + dist w z :=
        dist_triangle _ _ _
      have hpos := d1ccore_stageScale_pos 𝒢 (m + 1)
      linarith
  have hcore : ∀ j, ∀ z ∈ 𝒢.limitCore, z ∈ closure (C.kept 𝒢 j) := by
    intro j z hz
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨w, hw, hwz⟩ := Metric.mem_closure_iff.mp
      (d1ccore_limitCore_subset_closure 𝒢 hz) (min ε (stageScale 𝒢 j))
      (lt_min hε (d1ccore_stageScale_pos 𝒢 j))
    refine ⟨w, hnear z hz j w hw ?_, lt_of_lt_of_le hwz (min_le_left _ _)⟩
    rw [dist_comm]
    exact lt_of_lt_of_le hwz (min_le_right _ _)
  refine ⟨?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro z hz
      rw [mem_iInter] at hz
      apply (hZero n E ℓ₀ P μ k Λ b 𝒢 z).mp
      have hle : ∀ j : ℕ, 𝒢.stopScale z ≤ 1000 * stageScale 𝒢 (j + 1) := by
        intro j
        have hsub : closure (C.kept 𝒢 (j + 1)) ⊆
            {w | 𝒢.stopScale w ≤ 1000 * stageScale 𝒢 (j + 1)} :=
          closure_minimal (fun w hw => (hbound (j + 1) (by omega) w hw).le)
            (isClosed_le hcont continuous_const)
        exact hsub (hz (j + 1))
      exact le_antisymm (ge_of_tendsto' (d1ccore_tendsto_const_mul_succ 𝒢 1000) hle) (hLip0 z)
    · intro z hz
      exact mem_iInter.mpr fun j => hcore j z hz
  · intro z hz
    have hex : ∀ m : ℕ, ∃ i, i < C.candCount (m + 1) ∧
        dist (C.cand (m + 1) i) z < (1 + 𝒢.type.sourceSeparation) * stageScale 𝒢 (m + 1) := by
      intro m
      obtain ⟨w, hw, hzw⟩ := Metric.mem_closure_iff.mp (hcore (m + 1) z hz)
        (stageScale 𝒢 (m + 1)) (d1ccore_stageScale_pos 𝒢 (m + 1))
      obtain ⟨i, hi, hwi⟩ := mem_iUnion₂.mp (hsel.cand_cover (m + 1) (by omega) hw)
      refine ⟨i, hi, ?_⟩
      rw [Metric.mem_ball] at hwi
      calc dist (C.cand (m + 1) i) z ≤ dist (C.cand (m + 1) i) w + dist w z :=
            dist_triangle _ _ _
        _ = dist w (C.cand (m + 1) i) + dist z w := by
            rw [dist_comm (C.cand (m + 1) i) w, dist_comm w z]
        _ < 𝒢.type.sourceSeparation * stageScale 𝒢 (m + 1) + stageScale 𝒢 (m + 1) :=
            add_lt_add hwi hzw
        _ = (1 + 𝒢.type.sourceSeparation) * stageScale 𝒢 (m + 1) := by ring
    choose idx hidx hdist using hex
    refine ⟨fun m => m + 1, idx, fun m => ⟨Nat.le_add_left 1 m, hidx m⟩,
      tendsto_add_atTop_nat 1, ?_⟩
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun m => dist_nonneg) (fun m => (hdist m).le)
      (d1ccore_tendsto_const_mul_succ 𝒢 (1 + 𝒢.type.sourceSeparation))

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
