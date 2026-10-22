import ParabolicRectifiability.QuantitativeCharacterization.Statements.TraceComponents

/-! # Points of infinite multiplicity form an `H_P^k`-null set

Proof of `dp2_infinite_multiplicity_null`, whose statement is
`dp2_InfiniteMultiplicityNullStatement`.

Proof idea (Hausdorff tail covers; no estimate of `Σ_i μ(P_i)` and no property of `μ` is used).
1. Root packing: `Σ_i R_i^k ≤ ofReal (K R^k) < ⊤`, so the tails `Σ_{i ∉ F} R_i^k` tend to `0`
   along finite sets `F` (`ENNReal.tendsto_tsum_compl_atTop_zero`); since `k ≥ 1`, every
   `R_i` with `i ∉ F` is at most `(Σ_{i ∉ F} R_i^k)^{1/k}`, so the mesh tends to `0` as well.
2. A point of infinite multiplicity lies in infinitely many `P_i`, hence in `⋃_{i ∉ F} P_i` for
   every finite `F` (`dp2_imn_subset_tail`).
3. In the parabolic metric of `Space n` (the one defining `hausdorffP`), `ediam P(c,r) ≤ 2r`
   (`dp2_imn_ediam_ball_le`); `Measure.hausdorffMeasure_le_liminf_tsum` along finite sets with
   the covers `{P_i : i ∉ F}` gives `H_P^k(S) ≤ liminf_F 2^k Σ_{i ∉ F} R_i^k = 0`
   (`dp2_imn_hausdorff_null_of_tail_cover`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

/-- The extended diameter of a ball is at most twice its radius. At `Space n` this is the
parabolic diameter, since `Metric.ball` and `hausdorffP` use the same metric instance. -/
theorem dp2_imn_ediam_ball_le {X : Type*} [PseudoMetricSpace X] (c : X) (r : ℝ) :
    Metric.ediam (Metric.ball c r) ≤ 2 * ENNReal.ofReal r := by
  calc Metric.ediam (Metric.ball c r) ≤ ENNReal.ofReal (2 * r) := by
        refine Metric.ediam_le_of_forall_dist_le fun x hx y hy => ?_
        have hx' : dist x c < r := Metric.mem_ball.1 hx
        have hy' : dist y c < r := Metric.mem_ball.1 hy
        calc dist x y ≤ dist x c + dist c y := dist_triangle x c y
          _ ≤ 2 * r := by rw [dist_comm c y]; linarith
    _ = 2 * ENNReal.ofReal r := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]

/-- **Hausdorff tail covers.** Let `k ≥ 1` and let `B(c_i, ρ_i)` be countably many balls with
`Σ_i ρ_i^k < ∞`. A set contained in `⋃_{i ∉ F} B(c_i, ρ_i)` for every finite `F` is
`H^k`-null. -/
theorem dp2_imn_hausdorff_null_of_tail_cover {X ι : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [Countable ι] {k : ℕ} (hk : 1 ≤ k) (c : ι → X) (ρ : ι → ℝ)
    (hsum : ∑' i, ENNReal.ofReal (ρ i) ^ k ≠ ⊤) (S : Set X)
    (hS : ∀ F : Finset ι, S ⊆ ⋃ j : {i // i ∉ F}, Metric.ball (c j) (ρ j)) :
    (Measure.hausdorffMeasure (k : ℝ) : Measure X) S = 0 := by
  have hk0 : k ≠ 0 := by omega
  have hkinv : (0 : ℝ) < (k : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 (by omega))
  -- Step 1: the tails of the root packing sum, and the mesh, tend to zero.
  have htail : Tendsto (fun F : Finset ι => ∑' j : {i // i ∉ F}, ENNReal.ofReal (ρ j) ^ k)
      atTop (𝓝 0) := ENNReal.tendsto_tsum_compl_atTop_zero hsum
  have hr : Tendsto (fun F : Finset ι =>
      2 * (∑' j : {i // i ∉ F}, ENNReal.ofReal (ρ j) ^ k) ^ (k : ℝ)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun F : Finset ι =>
        (∑' j : {i // i ∉ F}, ENNReal.ofReal (ρ j) ^ k) ^ (k : ℝ)⁻¹) atTop (𝓝 0) := by
      have h0 := ((ENNReal.continuous_rpow_const (y := (k : ℝ)⁻¹)).tendsto 0).comp htail
      rw [ENNReal.zero_rpow_of_pos hkinv] at h0
      exact h0
    have h2 := ENNReal.Tendsto.const_mul (a := 2) h1 (Or.inr ENNReal.ofNat_ne_top)
    rw [mul_zero] at h2
    exact h2
  have hdiam : ∀ (F : Finset ι) (j : {i // i ∉ F}), Metric.ediam (Metric.ball (c j) (ρ j)) ≤
      2 * (∑' j : {i // i ∉ F}, ENNReal.ofReal (ρ j) ^ k) ^ (k : ℝ)⁻¹ := by
    intro F j
    refine (dp2_imn_ediam_ball_le _ _).trans ?_
    gcongr
    calc ENNReal.ofReal (ρ j) = (ENNReal.ofReal (ρ j) ^ k) ^ (k : ℝ)⁻¹ :=
          (ENNReal.pow_rpow_inv_natCast hk0 _).symm
      _ ≤ _ := ENNReal.rpow_le_rpow
          (ENNReal.le_tsum (f := fun j : {i // i ∉ F} => ENNReal.ofReal (ρ j) ^ k) j) hkinv.le
  -- Steps 2-3: Hausdorff tail covers.
  have hH := Measure.hausdorffMeasure_le_liminf_tsum (β := Finset ι)
    (ι := fun F : Finset ι => {i // i ∉ F}) (k : ℝ) S _ hr
    (fun F (j : {i // i ∉ F}) => Metric.ball (c j) (ρ j))
    (Eventually.of_forall hdiam) (Eventually.of_forall hS)
  have hle : ∀ F : Finset ι,
      ∑' j : {i // i ∉ F}, Metric.ediam (Metric.ball (c j) (ρ j)) ^ (k : ℝ) ≤
        2 ^ k * ∑' j : {i // i ∉ F}, ENNReal.ofReal (ρ j) ^ k := by
    intro F
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun j => ?_
    rw [ENNReal.rpow_natCast, ← mul_pow]
    exact pow_le_pow_left₀ zero_le (dp2_imn_ediam_ball_le _ _) k
  have hlim : Tendsto (fun F : Finset ι => 2 ^ k * ∑' j : {i // i ∉ F}, ENNReal.ofReal (ρ j) ^ k)
      atTop (𝓝 0) := by
    have h2 := ENNReal.Tendsto.const_mul (a := 2 ^ k) htail
      (Or.inr (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))
    rw [mul_zero] at h2
    exact h2
  refine le_antisymm (hH.trans ?_) zero_le
  calc liminf (fun F : Finset ι =>
        ∑' j : {i // i ∉ F}, Metric.ediam (Metric.ball (c j) (ρ j)) ^ (k : ℝ)) atTop
      ≤ liminf (fun F : Finset ι =>
          2 ^ k * ∑' j : {i // i ∉ F}, ENNReal.ofReal (ρ j) ^ k) atTop :=
        liminf_le_liminf (Eventually.of_forall hle)
    _ = 0 := hlim.liminf_eq

/-- A point of infinite multiplicity lies in infinitely many model balls, hence in the tail
union `⋃_{i ∉ F} P_i` for every finite set of indices `F`. -/
theorem dp2_imn_subset_tail {n k : ℕ} {K L : ℝ} {μ : Measure (Space n)} {a : Space n} {R : ℝ}
    (𝒞 : RegularMixedCovering k K L μ a R) (F : Finset 𝒞.index) :
    {z | 𝒞.multiplicity z = ⊤} ⊆
      ⋃ j : {i // i ∉ F}, Metric.ball (𝒞.center j) (𝒞.radius j) := by
  intro z hz
  have hz' : {i : 𝒞.index | z ∈ 𝒞.ball i}.encard = ⊤ := hz
  obtain ⟨i, hi, hiF⟩ := (Set.encard_eq_top_iff.1 hz').exists_notMem_finset F
  exact Set.mem_iUnion.2 ⟨⟨i, hiF⟩, hi⟩

/-- **Infinite multiplicity is null.** For every regular mixed covering with `k ≥ 1`, the points of infinite
multiplicity form an `H_P^k`-null set. Only the root packing field is used. -/
theorem dp2_infinite_multiplicity_null_proof : dp2_InfiniteMultiplicityNullStatement := by
  intro n k hk K L μ a R 𝒞
  rw [hausdorffP_eq]
  exact dp2_imn_hausdorff_null_of_tail_cover hk 𝒞.center 𝒞.radius
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top 𝒞.root_packing) _ (dp2_imn_subset_tail 𝒞)

end ParabolicRectifiability.QuantitativeCharacterization
