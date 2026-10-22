import ParabolicRectifiability.Metric.Hausdorff

/-!
# Local content from a bi-Lipschitz parametrization

The general packing and Hausdorff-image estimate for the local content bound, stated for an arbitrary parameter space `X` and target space `Y`.

The parameter space carries a measure `μ` with exact ball volume `μ(B(x,r)) = v r^k`, and its
`k`-dimensional Hausdorff measure satisfies `H^k(B(x,r)) ≤ D r^k`. A map `ψ : A → Y`, defined
only on a subset `A ⊆ X`, has distortion `L`:
`L⁻¹ d(u,v) ≤ d(ψ u, ψ v) ≤ L d(u,v)`. Its range contains a core `C₀` and a family `S` of
stopping centers with radii `d_c > 0` and separation `c₀ max(d_c, d_{c'}) ≤ d(c,c')`.
Then for every `z ∈ Y` and `s > 0`

`H^k(C₀ ∩ B(z,s)) + ∑_{c ∈ S ∩ B(z,s), d_c ≤ s} d_c^k ≤ (L^k D (2L)^k + ((2L + a)/a)^k) s^k`,

with `a = c₀/(4L)`.

* The core estimate applies the Lipschitz image bound for Hausdorff measure to the
  preimage of `C₀ ∩ B(z,s)`, a subset of `A` contained in one parameter ball of radius `2Ls`.
* The stopping estimate packs the **full** parameter balls `B(u_c, a d_c)` of `X`, whose centers
  `u_c ∈ A` are preimages of the stopping centers; the balls need not lie in `A`. They are
  pairwise disjoint by the separation and lie in one parameter ball of radius `(2L + a)s`.
  The sum is controlled through its finite partial sums.
-/

noncomputable section

namespace ParabolicRectifiability

namespace NeckHubTree

open MeasureTheory Set Metric
open scoped ENNReal NNReal

section General

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
/-- The lower distortion bound, solved for the parameter distance. -/
theorem nk4_dist_le_of_distortion {L : ℝ} (hL : 0 < L) {A : Set X} (ψ : A → Y)
    {u v : A} (h : L⁻¹ * dist u v ≤ dist (ψ u) (ψ v)) :
    dist (u : X) v ≤ L * dist (ψ u) (ψ v) :=
  (inv_mul_le_iff₀ hL).1 h

/-- **Core part.** The `k`-dimensional Hausdorff measure of the part of the range of a
distortion-`L` map inside a ball of radius `s` is at most `L^k D (2L)^k s^k`. -/
theorem nk4_hausdorff_inter_ball_le (k : ℕ) {D L : ℝ} (hL : 0 < L)
    (hH : ∀ (x : X) (r : ℝ), 0 < r →
      (Measure.hausdorffMeasure (k : ℝ) : Measure X) (ball x r) ≤ ENNReal.ofReal (D * r ^ k))
    {A : Set X} (ψ : A → Y)
    (hψ : ∀ u v : A, L⁻¹ * dist u v ≤ dist (ψ u) (ψ v) ∧ dist (ψ u) (ψ v) ≤ L * dist u v)
    {C₀ : Set Y} (hC₀ : C₀ ⊆ range ψ) (z : Y) {s : ℝ} (hs : 0 < s) :
    (Measure.hausdorffMeasure (k : ℝ) : Measure Y) (C₀ ∩ ball z s) ≤
      ENNReal.ofReal (L ^ k * D * (2 * L) ^ k * s ^ k) := by
  rcases (C₀ ∩ ball z s).eq_empty_or_nonempty with h | ⟨y₀, hy₀C, hy₀B⟩
  · rw [h, measure_empty]
    exact zero_le
  obtain ⟨u₀, rfl⟩ := hC₀ hy₀C
  have himage : ψ '' (ψ ⁻¹' (C₀ ∩ ball z s)) = C₀ ∩ ball z s :=
    image_preimage_eq_of_subset (inter_subset_left.trans hC₀)
  have hlip : LipschitzWith (Real.toNNReal L) ψ := LipschitzWith.of_dist_le_mul fun u v => by
    rw [Real.coe_toNNReal _ hL.le]
    exact (hψ u v).2
  have hsub : (Subtype.val : A → X) '' (ψ ⁻¹' (C₀ ∩ ball z s)) ⊆
      ball (u₀ : X) (2 * L * s) := by
    rintro _ ⟨u, hu, rfl⟩
    have h2 : dist (ψ u) (ψ u₀) < 2 * s :=
      calc dist (ψ u) (ψ u₀) ≤ dist (ψ u) z + dist z (ψ u₀) := dist_triangle _ _ _
        _ < s + s := add_lt_add (mem_ball.1 hu.2) (mem_ball'.1 hy₀B)
        _ = 2 * s := by ring
    rw [mem_ball]
    calc dist (u : X) u₀ ≤ L * dist (ψ u) (ψ u₀) := nk4_dist_le_of_distortion hL ψ (hψ u u₀).1
      _ < L * (2 * s) := mul_lt_mul_of_pos_left h2 hL
      _ = 2 * L * s := by ring
  have hball := (measure_mono hsub).trans (hH (u₀ : X) (2 * L * s) (by positivity))
  calc (Measure.hausdorffMeasure (k : ℝ) : Measure Y) (C₀ ∩ ball z s)
      = (Measure.hausdorffMeasure (k : ℝ) : Measure Y) (ψ '' (ψ ⁻¹' (C₀ ∩ ball z s))) := by
        rw [himage]
    _ ≤ (Real.toNNReal L : ℝ≥0∞) ^ k *
          (Measure.hausdorffMeasure (k : ℝ) : Measure X)
            ((Subtype.val : A → X) '' (ψ ⁻¹' (C₀ ∩ ball z s))) :=
        hausdorffMeasure_subtype_image_le hlip k _
    _ ≤ ENNReal.ofReal L ^ k * ENNReal.ofReal (D * (2 * L * s) ^ k) :=
        mul_le_mul_right hball _
    _ = ENNReal.ofReal (L ^ k * D * (2 * L) ^ k * s ^ k) := by
        rw [← ENNReal.ofReal_pow hL.le, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

omit [MeasurableSpace Y] [BorelSpace Y] in
/-- **Stopping part (packing).** For separated stopping centers in the range of a
distortion-`L` map, `∑_{c ∈ S ∩ B(z,s), d_c ≤ s} d_c^k ≤ ((2L + a)/a)^k s^k`, `a = c₀/(4L)`.
The packed balls are full parameter balls centered at preimages; they need not lie in `A`. -/
theorem nk4_stopping_tsum_le (k : ℕ) (μ : Measure X) {v : ℝ≥0∞} (hv0 : v ≠ 0) (hvtop : v ≠ ∞)
    (hball : ∀ (x : X) (r : ℝ), 0 < r → μ (ball x r) = v * ENNReal.ofReal r ^ k)
    {L c₀ : ℝ} (hL : 0 < L) (hc₀ : 0 < c₀) {A : Set X} (ψ : A → Y)
    (hψ : ∀ u v : A, L⁻¹ * dist u v ≤ dist (ψ u) (ψ v) ∧ dist (ψ u) (ψ v) ≤ L * dist u v)
    {S : Set Y} (hS : S ⊆ range ψ) (d : Y → ℝ) (hpos : ∀ c ∈ S, 0 < d c)
    (hsep : ∀ c ∈ S, ∀ c' ∈ S, c ≠ c' → c₀ * max (d c) (d c') ≤ dist c c')
    (z : Y) {s : ℝ} (hs : 0 < s) :
    ∑' c : ↥(S ∩ ball z s ∩ {c | d c ≤ s}), ENNReal.ofReal (d c ^ k) ≤
      ENNReal.ofReal (((2 * L + c₀ / (4 * L)) / (c₀ / (4 * L))) ^ k * s ^ k) := by
  set a : ℝ := c₀ / (4 * L) with ha_def
  have ha : 0 < a := by positivity
  have hnn : ∀ c : ↥(S ∩ ball z s ∩ {c | d c ≤ s}), 0 ≤ d c := fun c => (hpos c c.2.1.1).le
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun T => ?_
  rcases T.eq_empty_or_nonempty with rfl | ⟨c₁, -⟩
  · rw [Finset.sum_empty]
    exact zero_le
  have hpre : ∀ c : ↥(S ∩ ball z s ∩ {c | d c ≤ s}), ∃ u : A, ψ u = c :=
    fun c => hS c.2.1.1
  choose p hp using hpre
  -- the packed balls: full parameter balls centered at the preimages
  let B : ↥(S ∩ ball z s ∩ {c | d c ≤ s}) → Set X := fun c => ball ((p c : A) : X) (a * d c)
  have hdisj : (T : Set ↥(S ∩ ball z s ∩ {c | d c ≤ s})).PairwiseDisjoint B := by
    intro c _ c' _ hne
    show Disjoint (ball ((p c : A) : X) (a * d c)) (ball ((p c' : A) : X) (a * d c'))
    refine ball_disjoint_ball ?_
    have hcc' : (c : Y) ≠ c' := fun h => hne (Subtype.ext h)
    have hsep' := hsep c c.2.1.1 c' c'.2.1.1 hcc'
    have hM : 0 ≤ max (d c) (d c') := (hnn c).trans (le_max_left _ _)
    have h1 : L⁻¹ * dist (c : Y) c' ≤ dist ((p c : A) : X) (p c') := by
      have := (hψ (p c) (p c')).2
      rw [hp, hp] at this
      exact (inv_mul_le_iff₀ hL).2 this
    have hkey : 2 * a * max (d c) (d c') = L⁻¹ * (c₀ * max (d c) (d c')) / 2 := by
      rw [ha_def]
      ring
    calc a * d c + a * d c' ≤ 2 * a * max (d c) (d c') := by
          have e1 := mul_le_mul_of_nonneg_left (le_max_left (d c) (d c')) ha.le
          have e2 := mul_le_mul_of_nonneg_left (le_max_right (d c) (d c')) ha.le
          linarith
      _ = L⁻¹ * (c₀ * max (d c) (d c')) / 2 := hkey
      _ ≤ L⁻¹ * (c₀ * max (d c) (d c')) :=
          half_le_self (mul_nonneg (inv_nonneg.2 hL.le) (mul_nonneg hc₀.le hM))
      _ ≤ L⁻¹ * dist (c : Y) c' := mul_le_mul_of_nonneg_left hsep' (inv_nonneg.2 hL.le)
      _ ≤ dist ((p c : A) : X) (p c') := h1
  have hsub : (⋃ c ∈ T, B c) ⊆ ball ((p c₁ : A) : X) ((2 * L + a) * s) := by
    refine iUnion₂_subset fun c _ => ?_
    intro w hw
    have hw' : dist w ((p c : A) : X) < a * d c := hw
    rw [mem_ball]
    have h2 : dist (c : Y) c₁ < 2 * s :=
      calc dist (c : Y) c₁ ≤ dist (c : Y) z + dist z c₁ := dist_triangle _ _ _
        _ < s + s := add_lt_add (mem_ball.1 c.2.1.2) (mem_ball'.1 c₁.2.1.2)
        _ = 2 * s := by ring
    have h3 : dist ((p c : A) : X) (p c₁) ≤ L * dist (c : Y) c₁ := by
      have := nk4_dist_le_of_distortion hL ψ (hψ (p c) (p c₁)).1
      rwa [hp, hp] at this
    have h4 : a * d c ≤ a * s := mul_le_mul_of_nonneg_left c.2.2 ha.le
    calc dist w ((p c₁ : A) : X) ≤ dist w ((p c : A) : X) + dist ((p c : A) : X) (p c₁) :=
          dist_triangle _ _ _
      _ < a * d c + L * (2 * s) := add_lt_add_of_lt_of_le hw' (h3.trans_lt
          (mul_lt_mul_of_pos_left h2 hL)).le
      _ ≤ a * s + L * (2 * s) := by linarith
      _ = (2 * L + a) * s := by ring
  have hle : ∑ c ∈ T, μ (B c) ≤ μ (ball ((p c₁ : A) : X) ((2 * L + a) * s)) := by
    rw [← measure_biUnion_finset hdisj fun c _ => measurableSet_ball]
    exact measure_mono hsub
  rw [hball _ _ (by positivity),
    Finset.sum_congr rfl fun c _ => hball ((p c : A) : X) (a * d c) (mul_pos ha (hpos c c.2.1.1)),
    ← Finset.mul_sum, ENNReal.mul_le_mul_iff_right hv0 hvtop] at hle
  -- pass to real numbers
  have hreal : ∑ c ∈ T, (a * d c) ^ k ≤ ((2 * L + a) * s) ^ k := by
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity),
      ENNReal.ofReal_sum_of_nonneg fun c _ => pow_nonneg (mul_nonneg ha.le (hnn c)) k,
      ENNReal.ofReal_pow (by positivity)]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_)) hle
    exact ENNReal.ofReal_pow (mul_nonneg ha.le (hnn c)) k
  have hfac : ∑ c ∈ T, (a * d c) ^ k = a ^ k * ∑ c ∈ T, d c ^ k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => mul_pow a (d c) k
  rw [hfac] at hreal
  rw [← ENNReal.ofReal_sum_of_nonneg fun c _ => pow_nonneg (hnn c) k]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (pow_pos ha k), ← mul_pow]
  calc (∑ c ∈ T, d c ^ k) * a ^ k = a ^ k * ∑ c ∈ T, d c ^ k := mul_comm _ _
    _ ≤ ((2 * L + a) * s) ^ k := hreal

/-- **General content lemma.** For a distortion-`L` map `ψ : A → Y` on a subset of
a parameter space with exact ball volume `v r^k` and Hausdorff ball bound `D r^k`, a core
`C₀` and separated stopping centers `S` in its range satisfy, for all `z ∈ Y` and `s > 0`,
`H^k(C₀ ∩ B(z,s)) + ∑_{c ∈ S ∩ B(z,s), d_c ≤ s} d_c^k ≤ (L^k D (2L)^k + ((2L+a)/a)^k) s^k`,
where `a = c₀/(4L)`. -/
theorem nk4_localContent_of_distortion (k : ℕ) (μ : Measure X) {v : ℝ≥0∞} (hv0 : v ≠ 0)
    (hvtop : v ≠ ∞) (hball : ∀ (x : X) (r : ℝ), 0 < r → μ (ball x r) = v * ENNReal.ofReal r ^ k)
    {D : ℝ} (hD : 0 ≤ D)
    (hH : ∀ (x : X) (r : ℝ), 0 < r →
      (Measure.hausdorffMeasure (k : ℝ) : Measure X) (ball x r) ≤ ENNReal.ofReal (D * r ^ k))
    {L c₀ : ℝ} (hL : 0 < L) (hc₀ : 0 < c₀) {A : Set X} (ψ : A → Y)
    (hψ : ∀ u v : A, L⁻¹ * dist u v ≤ dist (ψ u) (ψ v) ∧ dist (ψ u) (ψ v) ≤ L * dist u v)
    {C₀ S : Set Y} (hC₀ : C₀ ⊆ range ψ) (hS : S ⊆ range ψ) (d : Y → ℝ)
    (hpos : ∀ c ∈ S, 0 < d c)
    (hsep : ∀ c ∈ S, ∀ c' ∈ S, c ≠ c' → c₀ * max (d c) (d c') ≤ dist c c')
    (z : Y) {s : ℝ} (hs : 0 < s) :
    (Measure.hausdorffMeasure (k : ℝ) : Measure Y) (C₀ ∩ ball z s) +
        ∑' c : ↥(S ∩ ball z s ∩ {c | d c ≤ s}), ENNReal.ofReal (d c ^ k) ≤
      ENNReal.ofReal
        ((L ^ k * D * (2 * L) ^ k + ((2 * L + c₀ / (4 * L)) / (c₀ / (4 * L))) ^ k) * s ^ k) := by
  have ha : 0 < c₀ / (4 * L) := by positivity
  rw [add_mul, ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add (nk4_hausdorff_inter_ball_le k hL hH ψ hψ hC₀ z hs)
    (nk4_stopping_tsum_le k μ hv0 hvtop hball hL hc₀ ψ hψ hS d hpos hsep z hs)

end General

end NeckHubTree

end ParabolicRectifiability
