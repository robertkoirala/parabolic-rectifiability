import ParabolicRectifiability.Analysis.SmoothCutoff.NormalizedWeights
import ParabolicRectifiability.Analysis.SmoothCutoff.ParabolicBump
import ParabolicRectifiability.Metric.Measure

/-!
# The smooth parabolic partition

Fix a dimension `n` and a separation parameter `σ > 0`. For a radius `r > 0` and
a finite family of centers `z_a` (`a ∈ I`) whose open parabolic balls of radius
`σ r / 3` are pairwise disjoint, the weights are

    ψ_a(x,t) = a(‖x - x_a‖²/r²) b((t - t_a)/r²),   Ψ = ∑_a ψ_a,
    θ_a = ψ_a f(Ψ),   f(s) = χ(s)/s  (and 0 for s ≤ 0).

They are defined from `r`, the finset `I` and the centers alone
(`parabolicWeight r I z a`): there is no truncation parameter, so the weights at
a given level do not change with a later truncation.

The constant `partitionConstant n σ ≥ 1` is a function of `n` and `σ` only, so it
is chosen before the family, the centers and the radius. The proof combines:

* the overlap count: at most `D = ((9 + σ)/σ)^(n+2)` centers lie within parabolic
  distance `3r` of any point, by comparing the ambient parabolic volumes of the
  disjoint `σr/3`-balls with the volume of the concentric `(3 + σ/3) r`-ball;
* the bump bounds `‖D_x^k ψ_a‖ ≤ B r^{-k}`, `‖∂_t ψ_a‖ ≤ B r^{-2}` of
  `parabolicBump` (constant `bumpBound n`), with every bump whose center is at distance `≥ 3r`
  identically zero near the point (closed support inside the open `3r`-ball);
* the abstract normalization bound `sum_norm_iteratedFDeriv_normalizedWeight_le`, applied once to
  the spatial section `y ↦ θ_a(y,t)` with scale `r⁻¹` and once to the time
  section `s ↦ θ_a(x,s)` with scale `r⁻²`.

No assumption on a source measure enters; the overlap count uses only the
ambient `parabolicVolume`.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

namespace ParabolicRectifiability

open SmoothCutoff

variable {n : ℕ} {ι : Type*}

/-! ### Overlap -/

/-- Disjoint balls of radius `ρ` with centers within `R` of a point number at most
`((R + ρ)/ρ)^(n+2)`. -/
theorem card_filter_dist_lt_le {I : Finset ι} {z : ι → Space n} {ρ R : ℝ} (hρ : 0 < ρ)
    (hR : 0 ≤ R) (hdisj : (I : Set ι).PairwiseDisjoint fun a => Metric.ball (z a) ρ)
    (q : Space n) :
    ((I.filter fun a => dist q (z a) < R).card : ℝ) ≤ ((R + ρ) / ρ) ^ (n + 2) := by
  classical
  set A := I.filter fun a => dist q (z a) < R with hAdef
  have hsub : (⋃ a ∈ A, Metric.ball (z a) ρ) ⊆ Metric.ball q (R + ρ) := by
    intro p hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨a, ha, hpa⟩ := hp
    have hqa := (Finset.mem_filter.mp ha).2
    rw [Metric.mem_ball] at hpa ⊢
    calc dist p q ≤ dist p (z a) + dist (z a) q := dist_triangle _ _ _
      _ < ρ + R := add_lt_add hpa (by rwa [dist_comm])
      _ = R + ρ := add_comm _ _
  have hdA : (A : Set ι).PairwiseDisjoint fun a => Metric.ball (z a) ρ :=
    hdisj.subset (Finset.coe_subset.mpr (Finset.filter_subset _ I))
  have hunion := measure_biUnion_finset (μ := parabolicVolume n) hdA
    (fun a _ => measurableSet_ball)
  have hle : ∑ a ∈ A, parabolicVolume n (Metric.ball (z a) ρ) ≤
      parabolicVolume n (Metric.ball q (R + ρ)) := by
    rw [← hunion]
    exact measure_mono hsub
  have hRρ : 0 < R + ρ := by linarith
  simp only [parabolicVolume_ball _ _ hρ, parabolicVolume_ball _ _ hRρ, Finset.sum_const,
    nsmul_eq_mul] at hle
  have hfin : 2 * omega n * ENNReal.ofReal (R + ρ) ^ (n + 2) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (omega_lt_top n).ne)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hreal := ENNReal.toReal_mono hfin hle
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hρ.le,
    ENNReal.toReal_ofReal hRρ.le, ENNReal.toReal_natCast, ENNReal.toReal_ofNat] at hreal
  have hω : 0 < (omega n).toReal := ENNReal.toReal_pos (omega_pos n).ne' (omega_lt_top n).ne
  have hρk : 0 < ρ ^ (n + 2) := pow_pos hρ _
  rw [div_pow, le_div_iff₀ hρk]
  have h2 : 2 * (omega n).toReal * ((A.card : ℝ) * ρ ^ (n + 2)) ≤
      2 * (omega n).toReal * (R + ρ) ^ (n + 2) := by
    calc 2 * (omega n).toReal * ((A.card : ℝ) * ρ ^ (n + 2))
        = (A.card : ℝ) * (2 * (omega n).toReal * ρ ^ (n + 2)) := by ring
      _ ≤ 2 * (omega n).toReal * (R + ρ) ^ (n + 2) := hreal
  exact le_of_mul_le_mul_left h2 (by positivity)

/-- The overlap bound `D = ((9 + σ)/σ)^(n+2)`. -/
def overlapBound (n : ℕ) (σ : ℝ) : ℝ := ((9 + σ) / σ) ^ (n + 2)

theorem overlapBound_nonneg (n : ℕ) {σ : ℝ} (hσ : 0 < σ) : 0 ≤ overlapBound n σ := by
  unfold overlapBound
  positivity

/-- At most `D` centers lie within parabolic distance `3r` of any point. -/
theorem card_filter_dist_lt_three_mul_le {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r)
    {I : Finset ι} {z : ι → Space n}
    (hdisj : (I : Set ι).PairwiseDisjoint fun a => Metric.ball (z a) (σ * r / 3))
    (q : Space n) :
    ((I.filter fun a => dist q (z a) < 3 * r).card : ℝ) ≤ overlapBound n σ := by
  have h := card_filter_dist_lt_le (ρ := σ * r / 3) (R := 3 * r) (by positivity)
    (by positivity) hdisj q
  have he : (3 * r + σ * r / 3) / (σ * r / 3) = (9 + σ) / σ := by
    field_simp
    ring
  rwa [he] at h

/-! ### The weights -/

/-- The total mass `Ψ = ∑_{a ∈ I} ψ_a`. -/
def parabolicMass (r : ℝ) (I : Finset ι) (z : ι → Space n) (p : Coordinates n) : ℝ :=
  ∑ b ∈ I, parabolicBump r (z b) p

/-- The partition weights `θ_a = ψ_a f(Ψ)`. They depend
only on the radius, the finite family `I` and its centers. -/
def parabolicWeight (r : ℝ) (I : Finset ι) (z : ι → Space n) (a : ι) :
    Coordinates n → ℝ :=
  normalizedWeight I (fun b => parabolicBump r (z b)) a

theorem parabolicWeight_apply (r : ℝ) (I : Finset ι) (z : ι → Space n) (a : ι)
    (p : Coordinates n) :
    parabolicWeight r I z a p = parabolicBump r (z a) p * normalizer (parabolicMass r I z p) :=
  rfl

/-- The weights depend on the centers only through the centers of the family. -/
theorem parabolicWeight_congr (r : ℝ) (I : Finset ι) {z z' : ι → Space n}
    (h : ∀ b ∈ I, z b = z' b) {a : ι} (ha : a ∈ I) :
    parabolicWeight r I z a = parabolicWeight r I z' a := by
  funext p
  simp only [parabolicWeight, normalizedWeight, h a ha]
  rw [Finset.sum_congr rfl fun b hb => by rw [h b hb]]

/-- The partition constant `C₀(n, σ) ≥ 1`. -/
def partitionConstant (n : ℕ) (σ : ℝ) : ℝ :=
  2 * weightConstant (overlapBound n σ) (bumpBound n) (normalizerBound (overlapBound n σ)) + 1

private theorem weightConstant_partition_nonneg (n : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    0 ≤ weightConstant (overlapBound n σ) (bumpBound n) (normalizerBound (overlapBound n σ)) :=
  weightConstant_nonneg (overlapBound_nonneg n hσ) (bumpBound_nonneg n)
    (normalizerBound_nonneg _)

theorem one_le_partitionConstant (n : ℕ) {σ : ℝ} (hσ : 0 < σ) : 1 ≤ partitionConstant n σ := by
  have := weightConstant_partition_nonneg n hσ
  unfold partitionConstant
  linarith

theorem contDiff_parabolicWeight (r : ℝ) (I : Finset ι) (z : ι → Space n) (a : ι) :
    ContDiff ℝ ∞ (parabolicWeight r I z a) :=
  contDiff_normalizedWeight I (fun b _ => contDiff_parabolicBump r (z b))
    (contDiff_parabolicBump r (z a))

theorem parabolicWeight_nonneg (r : ℝ) (I : Finset ι) (z : ι → Space n) (a : ι)
    (p : Coordinates n) : 0 ≤ parabolicWeight r I z a p :=
  normalizedWeight_nonneg I _ (parabolicBump_nonneg r (z a) p)

/-- The weights sum to `χ(Ψ)` at every point, including where `Ψ = 0` and in the
transition region `1/4 < Ψ < 1/2`. -/
theorem sum_parabolicWeight (r : ℝ) (I : Finset ι) (z : ι → Space n) (p : Coordinates n) :
    ∑ a ∈ I, parabolicWeight r I z a p = activation (parabolicMass r I z p) :=
  sum_normalizedWeight I _ p

theorem sum_parabolicWeight_nonneg (r : ℝ) (I : Finset ι) (z : ι → Space n)
    (p : Coordinates n) : 0 ≤ ∑ a ∈ I, parabolicWeight r I z a p :=
  sum_normalizedWeight_nonneg I _ p

theorem sum_parabolicWeight_le_one (r : ℝ) (I : Finset ι) (z : ι → Space n)
    (p : Coordinates n) : ∑ a ∈ I, parabolicWeight r I z a p ≤ 1 :=
  sum_normalizedWeight_le_one I _ p

/-- The weights sum to one on the union of the open parabolic `2r`-balls. -/
theorem sum_parabolicWeight_eq_one {r : ℝ} (hr : 0 < r) (I : Finset ι) (z : ι → Space n)
    {p : Coordinates n} (hp : ∃ a ∈ I, point p.1 p.2 ∈ Metric.ball (z a) (2 * r)) :
    ∑ a ∈ I, parabolicWeight r I z a p = 1 := by
  obtain ⟨a, ha, hpa⟩ := hp
  refine sum_normalizedWeight_eq_one I _ ?_
  have h1 : parabolicBump r (z a) p = 1 := parabolicBump_eq_one hr hpa
  have hle : parabolicBump r (z a) p ≤ ∑ b ∈ I, parabolicBump r (z b) p :=
    Finset.single_le_sum (f := fun b => parabolicBump r (z b) p)
      (fun b _ => parabolicBump_nonneg r (z b) p) ha
  linarith

/-! ### Supports -/

theorem parabolicWeight_eventuallyEq_zero {r : ℝ} (hr : 0 < r) (I : Finset ι)
    (z : ι → Space n) {a : ι} {p : Coordinates n} (hp : p ∉ bumpSupportSet r (z a)) :
    parabolicWeight r I z a =ᶠ[𝓝 p] fun _ => 0 :=
  normalizedWeight_eventuallyEq_zero I _ (parabolicBump_eventuallyEq_zero hr hp)

private theorem spatial_section_eventuallyEq_zero {f : Coordinates n → ℝ} {p : Coordinates n}
    (h : f =ᶠ[𝓝 p] fun _ => 0) : (fun y => f (y, p.2)) =ᶠ[𝓝 p.1] fun _ => 0 :=
  ((continuous_id.prodMk continuous_const).tendsto p.1).eventually h

private theorem time_section_eventuallyEq_zero {f : Coordinates n → ℝ} {p : Coordinates n}
    (h : f =ᶠ[𝓝 p] fun _ => 0) : (fun s => f (p.1, s)) =ᶠ[𝓝 p.2] fun _ => 0 :=
  ((continuous_const.prodMk continuous_id).tendsto p.2).eventually h

private theorem fderiv_eq_zero_of_eventuallyEq_zero {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E}
    (h : f =ᶠ[𝓝 x] fun _ => 0) : fderiv ℝ f x = 0 := by
  rw [h.fderiv_eq]
  exact fderiv_const_apply 0

private theorem fderiv_eventuallyEq_zero {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E}
    (h : f =ᶠ[𝓝 x] fun _ => 0) : fderiv ℝ f =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [h.eventually_nhds] with y hy
  exact fderiv_eq_zero_of_eventuallyEq_zero hy

private theorem tsupport_subset_of_eq_zero {V : Type*} [Zero V] {g : Coordinates n → V}
    {S : Set (Coordinates n)} (hS : IsClosed S) (h : ∀ p ∉ S, g p = 0) : tsupport g ⊆ S :=
  closure_minimal (fun p hp => by_contra fun hpS => hp (h p hpS)) hS

/-- The closed support of a weight lies in the open parabolic `3r`-ball. -/
theorem tsupport_parabolicWeight_subset {r : ℝ} (hr : 0 < r) (I : Finset ι)
    (z : ι → Space n) (a : ι) {p : Coordinates n}
    (hp : p ∈ tsupport (parabolicWeight r I z a)) :
    point p.1 p.2 ∈ Metric.ball (z a) (3 * r) := by
  refine point_mem_ball_of_mem_bumpSupportSet hr ?_
  refine tsupport_subset_of_eq_zero (isClosed_bumpSupportSet r (z a)) (fun q hq => ?_) hp
  exact (parabolicWeight_eventuallyEq_zero hr I z hq).eq_of_nhds

/-- The closed support of the first spatial derivative lies in the open `3r`-ball. -/
theorem tsupport_fderiv_spatial_parabolicWeight_subset {r : ℝ} (hr : 0 < r) (I : Finset ι)
    (z : ι → Space n) (a : ι) {p : Coordinates n}
    (hp : p ∈ tsupport fun q : Coordinates n =>
      fderiv ℝ (fun y => parabolicWeight r I z a (y, q.2)) q.1) :
    point p.1 p.2 ∈ Metric.ball (z a) (3 * r) := by
  refine point_mem_ball_of_mem_bumpSupportSet hr ?_
  refine tsupport_subset_of_eq_zero (isClosed_bumpSupportSet r (z a)) (fun q hq => ?_) hp
  exact fderiv_eq_zero_of_eventuallyEq_zero
    (spatial_section_eventuallyEq_zero (parabolicWeight_eventuallyEq_zero hr I z hq))

/-- The closed support of the second spatial derivative lies in the open `3r`-ball. -/
theorem tsupport_fderiv_fderiv_spatial_parabolicWeight_subset {r : ℝ} (hr : 0 < r)
    (I : Finset ι) (z : ι → Space n) (a : ι) {p : Coordinates n}
    (hp : p ∈ tsupport fun q : Coordinates n =>
      fderiv ℝ (fderiv ℝ fun y => parabolicWeight r I z a (y, q.2)) q.1) :
    point p.1 p.2 ∈ Metric.ball (z a) (3 * r) := by
  refine point_mem_ball_of_mem_bumpSupportSet hr ?_
  refine tsupport_subset_of_eq_zero (isClosed_bumpSupportSet r (z a)) (fun q hq => ?_) hp
  exact fderiv_eq_zero_of_eventuallyEq_zero (fderiv_eventuallyEq_zero
    (spatial_section_eventuallyEq_zero (parabolicWeight_eventuallyEq_zero hr I z hq)))

/-- The closed support of the time derivative lies in the open `3r`-ball. -/
theorem tsupport_deriv_time_parabolicWeight_subset {r : ℝ} (hr : 0 < r) (I : Finset ι)
    (z : ι → Space n) (a : ι) {p : Coordinates n}
    (hp : p ∈ tsupport fun q : Coordinates n =>
      deriv (fun s => parabolicWeight r I z a (q.1, s)) q.2) :
    point p.1 p.2 ∈ Metric.ball (z a) (3 * r) := by
  refine point_mem_ball_of_mem_bumpSupportSet hr ?_
  refine tsupport_subset_of_eq_zero (isClosed_bumpSupportSet r (z a)) (fun q hq => ?_) hp
  rw [(time_section_eventuallyEq_zero (parabolicWeight_eventuallyEq_zero hr I z hq)).deriv_eq]
  exact deriv_const _ _

/-! ### Derivative bounds -/

/-- An index whose center is at parabolic distance at least `3r` is locally zero. -/
private theorem parabolicBump_eventuallyEq_zero_of_le_dist {r : ℝ} (hr : 0 < r)
    {w : Space n} {p : Coordinates n} (h : ¬ dist (point p.1 p.2) w < 3 * r) :
    parabolicBump r w =ᶠ[𝓝 p] fun _ => 0 := by
  refine parabolicBump_eventuallyEq_zero hr fun hp => h ?_
  exact Metric.mem_ball.mp (point_mem_ball_of_mem_bumpSupportSet hr hp)

/-- The `k`-th spatial derivatives, `k ≤ 2`, summed over the family. -/
theorem sum_norm_iteratedFDeriv_spatial_parabolicWeight_le {σ r : ℝ} (hσ : 0 < σ)
    (hr : 0 < r) {I : Finset ι} {z : ι → Space n}
    (hdisj : (I : Set ι).PairwiseDisjoint fun a => Metric.ball (z a) (σ * r / 3))
    (x : Spatial n) (t : ℝ) {k : ℕ} (hk : k ≤ 2) :
    ∑ a ∈ I, ‖iteratedFDeriv ℝ k (fun y => parabolicWeight r I z a (y, t)) x‖ ≤
      weightConstant (overlapBound n σ) (bumpBound n) (normalizerBound (overlapBound n σ)) *
        r⁻¹ ^ k := by
  classical
  exact sum_norm_iteratedFDeriv_normalizedWeight_le
    (ψ := fun b y => parabolicBump r (z b) (y, t))
    (fun b _ => (contDiff_parabolicBump r (z b)).comp (contDiff_id.prodMk contDiff_const))
    (fun b _ => parabolicBump_nonneg r (z b) _) (fun b _ => parabolicBump_le_one r (z b) _)
    (A := I.filter fun b => dist (point x t) (z b) < 3 * r) (Finset.filter_subset _ I)
    (fun b _ hb => spatial_section_eventuallyEq_zero (p := (x, t))
      (parabolicBump_eventuallyEq_zero_of_le_dist hr fun h =>
        hb (Finset.mem_filter.mpr ⟨‹_›, h⟩)))
    (card_filter_dist_lt_three_mul_le hσ hr hdisj (point x t)) (bumpBound_nonneg n)
    (inv_nonneg.2 hr.le)
    (fun b _ i _ hi => norm_iteratedFDeriv_parabolicBump_spatial_le hr (z b) t x hi)
    (fun i hi s hs => norm_iteratedFDeriv_normalizer_le hi hs) hk

/-- The `k`-th time derivatives, `k ≤ 2`, summed over the family. -/
theorem sum_norm_iteratedFDeriv_time_parabolicWeight_le {σ r : ℝ} (hσ : 0 < σ)
    (hr : 0 < r) {I : Finset ι} {z : ι → Space n}
    (hdisj : (I : Set ι).PairwiseDisjoint fun a => Metric.ball (z a) (σ * r / 3))
    (x : Spatial n) (t : ℝ) {k : ℕ} (hk : k ≤ 2) :
    ∑ a ∈ I, ‖iteratedFDeriv ℝ k (fun s => parabolicWeight r I z a (x, s)) t‖ ≤
      weightConstant (overlapBound n σ) (bumpBound n) (normalizerBound (overlapBound n σ)) *
        (r ^ 2)⁻¹ ^ k := by
  classical
  exact sum_norm_iteratedFDeriv_normalizedWeight_le
    (ψ := fun b s => parabolicBump r (z b) (x, s))
    (fun b _ => (contDiff_parabolicBump r (z b)).comp (contDiff_const.prodMk contDiff_id))
    (fun b _ => parabolicBump_nonneg r (z b) _) (fun b _ => parabolicBump_le_one r (z b) _)
    (A := I.filter fun b => dist (point x t) (z b) < 3 * r) (Finset.filter_subset _ I)
    (fun b _ hb => time_section_eventuallyEq_zero (p := (x, t))
      (parabolicBump_eventuallyEq_zero_of_le_dist hr fun h =>
        hb (Finset.mem_filter.mpr ⟨‹_›, h⟩)))
    (card_filter_dist_lt_three_mul_le hσ hr hdisj (point x t)) (bumpBound_nonneg n)
    (inv_nonneg.2 (by positivity))
    (fun b _ i _ hi => norm_iteratedFDeriv_parabolicBump_time_le hr (z b) x t hi)
    (fun i hi s hs => norm_iteratedFDeriv_normalizer_le hi hs) hk

/-- `∑_a ‖D_x θ_a‖ ≤ C₀ / r`. -/
theorem sum_norm_fderiv_spatial_parabolicWeight_le {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r)
    {I : Finset ι} {z : ι → Space n}
    (hdisj : (I : Set ι).PairwiseDisjoint fun a => Metric.ball (z a) (σ * r / 3))
    (x : Spatial n) (t : ℝ) :
    ∑ a ∈ I, ‖fderiv ℝ (fun y => parabolicWeight r I z a (y, t)) x‖ ≤
      partitionConstant n σ / r := by
  have h := sum_norm_iteratedFDeriv_spatial_parabolicWeight_le hσ hr hdisj x t
    (k := 1) (by norm_num)
  simp only [norm_iteratedFDeriv_one, pow_one] at h
  refine h.trans ?_
  rw [← div_eq_mul_inv]
  have := weightConstant_partition_nonneg n hσ
  exact div_le_div_of_nonneg_right (by unfold partitionConstant; linarith) hr.le

/-- `∑_a (‖D_x² θ_a‖ + |∂_t θ_a|) ≤ C₀ / r²`. -/
theorem sum_norm_fderiv_fderiv_spatial_add_abs_deriv_time_parabolicWeight_le {σ r : ℝ}
    (hσ : 0 < σ) (hr : 0 < r) {I : Finset ι} {z : ι → Space n}
    (hdisj : (I : Set ι).PairwiseDisjoint fun a => Metric.ball (z a) (σ * r / 3))
    (x : Spatial n) (t : ℝ) :
    ∑ a ∈ I, (‖fderiv ℝ (fderiv ℝ fun y => parabolicWeight r I z a (y, t)) x‖ +
        |deriv (fun s => parabolicWeight r I z a (x, s)) t|) ≤
      partitionConstant n σ / r ^ 2 := by
  have h2 := sum_norm_iteratedFDeriv_spatial_parabolicWeight_le hσ hr hdisj x t
    (k := 2) le_rfl
  have ht := sum_norm_iteratedFDeriv_time_parabolicWeight_le hσ hr hdisj x t
    (k := 1) (by norm_num)
  have e2 : ∀ a, ‖fderiv ℝ (fderiv ℝ fun y => parabolicWeight r I z a (y, t)) x‖ =
      ‖iteratedFDeriv ℝ 2 (fun y => parabolicWeight r I z a (y, t)) x‖ := fun a => by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  have et : ∀ a, |deriv (fun s => parabolicWeight r I z a (x, s)) t| =
      ‖iteratedFDeriv ℝ 1 (fun s => parabolicWeight r I z a (x, s)) t‖ := fun a => by
    rw [← Real.norm_eq_abs, norm_deriv_eq_norm_fderiv, norm_iteratedFDeriv_one]
  simp only [e2, et, Finset.sum_add_distrib]
  refine (add_le_add h2 ht).trans ?_
  have := weightConstant_partition_nonneg n hσ
  set K := weightConstant (overlapBound n σ) (bumpBound n) (normalizerBound (overlapBound n σ))
    with hK
  have e : K * r⁻¹ ^ 2 + K * (r ^ 2)⁻¹ ^ 1 = 2 * K / r ^ 2 := by
    rw [inv_pow, pow_one, div_eq_mul_inv]
    ring
  rw [e]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  unfold partitionConstant
  linarith

/-! ### The assembled partition theorem -/

/-- The properties of a smooth parabolic partition for one finite family. -/
structure IsSmoothParabolicPartition (n : ℕ) {ι : Type*} (I : Finset ι) (z : ι → Space n)
    (r C₀ : ℝ) (θ : ι → Coordinates n → ℝ) : Prop where
  contDiff : ∀ a, ContDiff ℝ ∞ (θ a)
  nonneg : ∀ a p, 0 ≤ θ a p
  sum_nonneg : ∀ p, 0 ≤ ∑ a ∈ I, θ a p
  sum_le_one : ∀ p, ∑ a ∈ I, θ a p ≤ 1
  sum_eq_one : ∀ p : Coordinates n, (∃ a ∈ I, point p.1 p.2 ∈ Metric.ball (z a) (2 * r)) →
    ∑ a ∈ I, θ a p = 1
  tsupport_subset : ∀ a, ∀ p ∈ tsupport (θ a), point p.1 p.2 ∈ Metric.ball (z a) (3 * r)
  tsupport_fderiv_subset : ∀ a, ∀ p ∈ tsupport fun q : Coordinates n =>
      fderiv ℝ (fun y => θ a (y, q.2)) q.1, point p.1 p.2 ∈ Metric.ball (z a) (3 * r)
  tsupport_fderiv_fderiv_subset : ∀ a, ∀ p ∈ tsupport fun q : Coordinates n =>
      fderiv ℝ (fderiv ℝ fun y => θ a (y, q.2)) q.1,
      point p.1 p.2 ∈ Metric.ball (z a) (3 * r)
  tsupport_deriv_subset : ∀ a, ∀ p ∈ tsupport fun q : Coordinates n =>
      deriv (fun s => θ a (q.1, s)) q.2, point p.1 p.2 ∈ Metric.ball (z a) (3 * r)
  first : ∀ x t, ∑ a ∈ I, ‖fderiv ℝ (fun y => θ a (y, t)) x‖ ≤ C₀ / r
  second : ∀ x t, ∑ a ∈ I, (‖fderiv ℝ (fderiv ℝ fun y => θ a (y, t)) x‖ +
      |deriv (fun s => θ a (x, s)) t|) ≤ C₀ / r ^ 2

/-- **Smooth parabolic partition.** The constant `partitionConstant n σ ≥ 1` depends
only on `n` and `σ`. For every `r > 0` and every finite family of centers whose
open parabolic `σr/3`-balls are pairwise disjoint, the weights
`parabolicWeight r I z` form a smooth parabolic partition with that constant. -/
theorem isSmoothParabolicPartition_parabolicWeight {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r)
    (I : Finset ι) (z : ι → Space n)
    (hdisj : (I : Set ι).PairwiseDisjoint fun a => Metric.ball (z a) (σ * r / 3)) :
    IsSmoothParabolicPartition n I z r (partitionConstant n σ) (parabolicWeight r I z) where
  contDiff := contDiff_parabolicWeight r I z
  nonneg := parabolicWeight_nonneg r I z
  sum_nonneg := sum_parabolicWeight_nonneg r I z
  sum_le_one := sum_parabolicWeight_le_one r I z
  sum_eq_one _ hp := sum_parabolicWeight_eq_one hr I z hp
  tsupport_subset a _ hp := tsupport_parabolicWeight_subset hr I z a hp
  tsupport_fderiv_subset a _ hp := tsupport_fderiv_spatial_parabolicWeight_subset hr I z a hp
  tsupport_fderiv_fderiv_subset a _ hp :=
    tsupport_fderiv_fderiv_spatial_parabolicWeight_subset hr I z a hp
  tsupport_deriv_subset a _ hp := tsupport_deriv_time_parabolicWeight_subset hr I z a hp
  first x t := sum_norm_fderiv_spatial_parabolicWeight_le hσ hr hdisj x t
  second x t := sum_norm_fderiv_fderiv_spatial_add_abs_deriv_time_parabolicWeight_le hσ hr hdisj x t

/-- The partition theorem with the constant quantified before the family: for each `n` and
`σ > 0` there is `C₀ ≥ 1` such that every admissible family at every radius has a
smooth parabolic partition with constant `C₀`, given by the explicit weights. -/
theorem exists_smoothParabolicPartition_constant (n : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ {ι : Type*} (I : Finset ι) (z : ι → Space n) (r : ℝ), 0 < r →
      (I : Set ι).PairwiseDisjoint (fun a => Metric.ball (z a) (σ * r / 3)) →
      IsSmoothParabolicPartition n I z r C₀ (parabolicWeight r I z) :=
  ⟨partitionConstant n σ, one_le_partitionConstant n hσ,
    fun I z _ hr hdisj => isSmoothParabolicPartition_parabolicWeight hσ hr I z hdisj⟩

end ParabolicRectifiability
