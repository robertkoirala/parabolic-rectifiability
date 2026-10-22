import ParabolicRectifiability.Decomposition.SourceAssembly
import ParabolicRectifiability.Metric.BaseVolume

/-! # The ambient endpoint and content bounds for isometric model sets

This module proves the ambient-dimension case of the decomposition theorem: at `k = n + 2` retain `μ|P(0,1)` vertically and nothing
horizontally. The sole vertical model is the whole space and the graph of the
zero function on the full spatial direction covers everything. All content and
packing bounds follow from volume comparisons, and the unit-ball remainder is
exactly zero. No beta or energy hypothesis is used.

The content bounds are proved in a form that also serves flat model sets. Let
`ι : Y → Space n` be an isometry and `ν` a measure on `Y` whose open balls have
volume exactly `v r^k`, with `𝓗^k ≤ h ν`. For `K ⊆ range ι`:

* `K ∩ P(q,R)` lies in the image of a `Y`-ball of radius `2R`, so its
  `k`-dimensional Hausdorff measure is at most `h v (2R)^k`.
* Disjoint balls of radii `ρ_i` inside a ball of radius `S` satisfy
  `∑ ρ_i^k ≤ S^k`. This gives the separated-set bound `6^k (R/r)^k` (radius
  `r/2` balls inside radius `3R`) and finite packing `3^k R^k`; ambient
  disjoint balls pull back to disjoint `Y`-balls.
* If `K ⊆ P̄(c,1)` and `k ≤ n + 2`, a maximal `r`-separated subset of `K` has at
  most `12^k r^{-k}` points and its `2r`-balls cover the `r`-neighbourhood, whose
  volume is therefore at most `12^k 2^{n+3} ω_n r^{n+2-k}`.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace ParabolicRectifiability

section IsometricModel

variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Disjoint balls inside a ball, for a measure with exact ball volume `v r^k`. -/
theorem sum_radius_pow_le_of_disjoint_balls {ν : Measure Y} {k : ℕ} {v : ℝ≥0∞}
    (hv : v ≠ 0) (hvfin : v ≠ ∞)
    (hball : ∀ y r, 0 < r → ν (Metric.ball y r) = v * ENNReal.ofReal r ^ k)
    {ι : Type*} (s : Finset ι) (y : ι → Y) (ρ : ι → ℝ) (hρ : ∀ i ∈ s, 0 < ρ i)
    (hd : (s : Set ι).PairwiseDisjoint fun i => Metric.ball (y i) (ρ i))
    (y₀ : Y) {S : ℝ} (hS : 0 < S)
    (hsub : ∀ i ∈ s, Metric.ball (y i) (ρ i) ⊆ Metric.ball y₀ S) :
    ∑ i ∈ s, ENNReal.ofReal (ρ i) ^ k ≤ ENNReal.ofReal S ^ k := by
  have h1 : ν (⋃ i ∈ s, Metric.ball (y i) (ρ i)) = v * ∑ i ∈ s, ENNReal.ofReal (ρ i) ^ k := by
    rw [measure_biUnion_finset hd (fun i _ => measurableSet_ball), Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => hball _ _ (hρ i hi)
  have h2 : ν (⋃ i ∈ s, Metric.ball (y i) (ρ i)) ≤ v * ENNReal.ofReal S ^ k := by
    rw [← hball y₀ S hS]
    exact measure_mono (iUnion₂_subset hsub)
  rw [h1] at h2
  exact (ENNReal.mul_le_mul_iff_right hv hvfin).mp h2

variable {n k : ℕ} {ν : Measure Y} {v h : ℝ≥0∞} {ι : Y → Space n} {K : Set (Space n)}

omit [MeasurableSpace Y] [BorelSpace Y] in
/-- Two points of `K ∩ P(q,R)` have preimages at distance less than `2R`. -/
theorem dist_lt_two_mul_of_mem_ball (hι : Isometry ι) {q : Space n} {R : ℝ}
    {y y₀ : Y} (hy : ι y ∈ Metric.ball q R) (hy₀ : ι y₀ ∈ Metric.ball q R) :
    dist y y₀ < 2 * R := by
  rw [← hι.dist_eq]
  calc dist (ι y) (ι y₀) ≤ dist (ι y) q + dist (ι y₀) q := dist_triangle_right _ _ _
    _ < R + R := add_lt_add hy hy₀
    _ = 2 * R := by ring

/-- The local Hausdorff bound for a subset of an isometric model. -/
theorem hausdorffP_inter_ball_le_of_isometry (hvfin : v ≠ ∞)
    (hball : ∀ y r, 0 < r → ν (Metric.ball y r) = v * ENNReal.ofReal r ^ k)
    (hH : ∀ E : Set Y, Measure.hausdorffMeasure (k : ℝ) E ≤ h * ν E)
    (hhfin : h ≠ ∞) (hι : Isometry ι) (hK : K ⊆ range ι) (q : Space n) {R : ℝ} (hR : 0 < R) :
    hausdorffP n k (K ∩ Metric.ball q R) ≤
      ENNReal.ofReal ((h * v).toReal * 2 ^ k * R ^ k) := by
  rcases (K ∩ Metric.ball q R).eq_empty_or_nonempty with he | ⟨z₀, hz₀K, hz₀B⟩
  · rw [he, measure_empty]
    exact zero_le
  obtain ⟨y₀, rfl⟩ := hK hz₀K
  have hsub : K ∩ Metric.ball q R ⊆ ι '' Metric.ball y₀ (2 * R) := by
    rintro z ⟨hzK, hzB⟩
    obtain ⟨y, rfl⟩ := hK hzK
    exact ⟨y, dist_lt_two_mul_of_mem_ball hι hzB hz₀B, rfl⟩
  have hfin : h * v ≠ ∞ := ENNReal.mul_ne_top hhfin hvfin
  calc hausdorffP n k (K ∩ Metric.ball q R)
      ≤ Measure.hausdorffMeasure (k : ℝ) (ι '' Metric.ball y₀ (2 * R)) := by
        rw [hausdorffP_eq]
        exact measure_mono hsub
    _ = Measure.hausdorffMeasure (k : ℝ) (Metric.ball y₀ (2 * R)) :=
        hι.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg k)) _
    _ ≤ h * ν (Metric.ball y₀ (2 * R)) := hH _
    _ = h * v * ENNReal.ofReal (2 * R) ^ k := by
        rw [hball y₀ (2 * R) (by positivity), mul_assoc]
    _ = ENNReal.ofReal ((h * v).toReal * (2 ^ k * R ^ k)) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin, ← mul_pow,
          ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2 * R)]
    _ = ENNReal.ofReal ((h * v).toReal * 2 ^ k * R ^ k) := by rw [mul_assoc]

/-- An `r`-separated subset of `K ∩ P(q,R)` has at most `6^k (R/r)^k` points. -/
theorem card_le_of_separated_of_isometry (hv : v ≠ 0) (hvfin : v ≠ ∞)
    (hball : ∀ y r, 0 < r → ν (Metric.ball y r) = v * ENNReal.ofReal r ^ k)
    (hι : Isometry ι) (hK : K ⊆ range ι) (q : Space n) {R r : ℝ} (hr : 0 < r)
    (hrR : r ≤ R) (F : Finset (Space n)) (hF : (↑F : Set (Space n)) ⊆ K ∩ Metric.ball q R)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → r ≤ dist x y) :
    (F.card : ℝ) ≤ 6 ^ k * (R / r) ^ k := by
  have hR : 0 < R := hr.trans_le hrR
  rcases F.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨y₀, hy₀⟩ := hK (hF hz₀).1
  have : Nonempty Y := ⟨y₀⟩
  have hpre : ∀ x ∈ F, ι (Function.invFun ι x) = x := fun x hx =>
    Function.invFun_eq (hK (hF hx).1)
  have hsum := sum_radius_pow_le_of_disjoint_balls hv hvfin hball F (Function.invFun ι)
    (fun _ => r / 2) (fun _ _ => half_pos hr) ?_ y₀ (by positivity : 0 < 3 * R) ?_
  · beta_reduce at hsum
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_pow (half_pos hr).le,
      ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 3 * R),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_le_ofReal_iff (by positivity : (0 : ℝ) ≤ (3 * R) ^ k)] at hsum
    have h6 : (6 : ℝ) * (R / r) = 3 * R / (r / 2) := by
      field_simp
      ring
    rw [← mul_pow, h6, div_pow, le_div_iff₀ (by positivity : (0 : ℝ) < (r / 2) ^ k)]
    exact hsum
  · intro x hx x' hx' hxx'
    change Disjoint _ _
    apply Metric.ball_disjoint_ball
    rw [← hι.dist_eq, hpre x hx, hpre x' hx']
    linarith [hsep x hx x' hx' hxx']
  · intro x hx
    apply Metric.ball_subset_ball'
    have hd := dist_lt_two_mul_of_mem_ball hι (q := q) (R := R)
      (by rw [hpre x hx]; exact (hF hx).2) (by rw [hy₀]; exact (hF hz₀).2)
    linarith

/-- Finite disjoint packing in `K ∩ P(q,R)` with constant `3^k`. -/
theorem sum_pow_le_of_disjoint_of_isometry (hv : v ≠ 0) (hvfin : v ≠ ∞)
    (hball : ∀ y r, 0 < r → ν (Metric.ball y r) = v * ENNReal.ofReal r ^ k)
    (hι : Isometry ι) (hK : K ⊆ range ι) : HasFiniteBallPacking k (3 ^ k) K := by
  intro q R hR _ l z r hz hr hd
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact zero_le
  let i₀ : Fin l := ⟨0, hl⟩
  obtain ⟨y₀, -⟩ := hK (hz i₀).1
  have : Nonempty Y := ⟨y₀⟩
  have hpre : ∀ i, ι (Function.invFun ι (z i)) = z i := fun i =>
    Function.invFun_eq (hK (hz i).1)
  have hsum := sum_radius_pow_le_of_disjoint_balls hv hvfin hball Finset.univ
    (fun i => Function.invFun ι (z i)) r (fun i _ => (hr i).1) ?_
    (Function.invFun ι (z i₀)) (by positivity : 0 < 3 * R) ?_
  · rw [← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 3 * R), mul_pow] at hsum
    exact hsum
  · intro i _ j _ hij
    change Disjoint _ _
    refine Set.disjoint_left.mpr fun w hwi hwj => ?_
    have hi : ι w ∈ Metric.ball (z i) (r i) := by
      rw [Metric.mem_ball, ← hpre i, hι.dist_eq]
      exact hwi
    have hj : ι w ∈ Metric.ball (z j) (r j) := by
      rw [Metric.mem_ball, ← hpre j, hι.dist_eq]
      exact hwj
    exact Set.disjoint_left.mp (hd i j hij) hi hj
  · intro i _
    apply Metric.ball_subset_ball'
    have hdist := dist_lt_two_mul_of_mem_ball hι (q := q) (R := R)
      (by rw [hpre i]; exact (hz i).2) (by rw [hpre i₀]; exact (hz i₀).2)
    linarith [(hr i).2]

/-- A maximal `r`-separated subset of `K ⊆ P̄(c,1)` has `r`-balls covering `K`. -/
theorem exists_separated_net_of_isometry (hv : v ≠ 0) (hvfin : v ≠ ∞)
    (hball : ∀ y r, 0 < r → ν (Metric.ball y r) = v * ENNReal.ofReal r ^ k)
    (hι : Isometry ι) (hK : K ⊆ range ι) {c : Space n}
    (hKc : K ⊆ Metric.closedBall c 1) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ F : Finset (Space n), (F.card : ℝ) ≤ 12 ^ k / r ^ k ∧
      ∀ w ∈ K, ∃ p ∈ F, dist w p < r := by
  classical
  have hbound : ∀ F : Finset (Space n), (↑F : Set (Space n)) ⊆ K →
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → r ≤ dist x y) → (F.card : ℝ) ≤ 12 ^ k / r ^ k := by
    intro F hF hsep
    have hF' : (↑F : Set (Space n)) ⊆ K ∩ Metric.ball c 2 := fun x hx =>
      ⟨hF hx, Metric.mem_ball.mpr
        (lt_of_le_of_lt (Metric.mem_closedBall.mp (hKc (hF hx))) (by norm_num))⟩
    have h := card_le_of_separated_of_isometry hv hvfin hball hι hK c hr
      (by linarith) F hF' hsep
    calc (F.card : ℝ) ≤ 6 ^ k * (2 / r) ^ k := h
      _ = 12 ^ k / r ^ k := by
        rw [div_pow, ← mul_div_assoc, ← mul_pow]
        norm_num
  let P : ℕ → Prop := fun m => ∃ F : Finset (Space n), (↑F : Set (Space n)) ⊆ K ∧
    (∀ x ∈ F, ∀ y ∈ F, x ≠ y → r ≤ dist x y) ∧ F.card = m
  let B : ℕ := ⌊(12 : ℝ) ^ k / r ^ k⌋₊
  have hP0 : P 0 := ⟨∅, by simp, by simp, rfl⟩
  obtain ⟨F, hFK, hFsep, hFcard⟩ : P (Nat.findGreatest P B) :=
    Nat.findGreatest_spec (Nat.zero_le B) hP0
  refine ⟨F, hbound F hFK hFsep, ?_⟩
  intro w hw
  by_contra hcon
  push Not at hcon
  have hwF : w ∉ F := fun hwF => by
    have := hcon w hwF
    rw [dist_self] at this
    linarith
  have hsep' : ∀ x ∈ insert w F, ∀ y ∈ insert w F, x ≠ y → r ≤ dist x y := by
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with hxw | hxF <;>
      rcases Finset.mem_insert.mp hy with hyw | hyF
    · exact absurd (hxw.trans hyw.symm) hxy
    · rw [hxw]
      exact hcon y hyF
    · rw [hyw, dist_comm]
      exact hcon x hxF
    · exact hFsep x hxF y hyF hxy
  have hsubK : (↑(insert w F) : Set (Space n)) ⊆ K := by
    rw [Finset.coe_insert]
    exact Set.insert_subset hw hFK
  have hcard : (insert w F).card = Nat.findGreatest P B + 1 := by
    rw [Finset.card_insert_of_notMem hwF, hFcard]
  have hle : Nat.findGreatest P B + 1 ≤ B := by
    rw [← hcard]
    exact Nat.le_floor (hbound _ hsubK hsep')
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hle ⟨_, hsubK, hsep', hcard⟩

/-- The tubular-volume bound with exponent `n + 2 - k`. -/
theorem parabolicVolume_thickening_le_of_isometry (hv : v ≠ 0) (hvfin : v ≠ ∞)
    (hball : ∀ y r, 0 < r → ν (Metric.ball y r) = v * ENNReal.ofReal r ^ k)
    (hι : Isometry ι) (hK : K ⊆ range ι) {c : Space n}
    (hKc : K ⊆ Metric.closedBall c 1) (hkn : k ≤ n + 2) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    parabolicVolume n {z | Metric.infEDist z K < ENNReal.ofReal r} ≤
      ENNReal.ofReal (12 ^ k * 2 ^ (n + 3) * (omega n).toReal * r ^ (n + 2 - k)) := by
  obtain ⟨F, hFcard, hnet⟩ := exists_separated_net_of_isometry hv hvfin hball hι hK hKc hr hr1
  have hcover : {z | Metric.infEDist z K < ENNReal.ofReal r} ⊆
      ⋃ p ∈ F, Metric.ball p (2 * r) := by
    intro z hz
    obtain ⟨w, hwK, hzw⟩ := Metric.infEDist_lt_iff.mp hz
    obtain ⟨p, hpF, hwp⟩ := hnet w hwK
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hr] at hzw
    refine mem_iUnion₂.mpr ⟨p, hpF, ?_⟩
    rw [Metric.mem_ball]
    linarith [dist_triangle z w p]
  have hw : 0 ≤ (omega n).toReal := ENNReal.toReal_nonneg
  have hballvol : ∀ p : Space n, parabolicVolume n (Metric.ball p (2 * r)) =
      ENNReal.ofReal (2 * (omega n).toReal * (2 * r) ^ (n + 2)) := by
    intro p
    rw [parabolicVolume_ball p (2 * r) (by positivity),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (omega n).toReal),
      ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2 * r),
      ENNReal.ofReal_mul (p := 2) (q := (omega n).toReal) (by norm_num),
      ENNReal.ofReal_toReal (omega_lt_top n).ne, ENNReal.ofReal_ofNat]
  calc parabolicVolume n {z | Metric.infEDist z K < ENNReal.ofReal r}
      ≤ ∑ p ∈ F, parabolicVolume n (Metric.ball p (2 * r)) :=
        (measure_mono hcover).trans (measure_biUnion_finset_le _ _)
    _ = ENNReal.ofReal (F.card * (2 * (omega n).toReal * (2 * r) ^ (n + 2))) := by
        simp only [hballvol, Finset.sum_const, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (12 ^ k * 2 ^ (n + 3) * (omega n).toReal * r ^ (n + 2 - k)) := by
        apply ENNReal.ofReal_le_ofReal
        have hsplit : r ^ (n + 2) = r ^ k * r ^ (n + 2 - k) := by
          rw [← pow_add, Nat.add_sub_cancel' hkn]
        have hrk : r ^ k ≠ 0 := (pow_pos hr k).ne'
        calc (F.card : ℝ) * (2 * (omega n).toReal * (2 * r) ^ (n + 2))
            ≤ 12 ^ k / r ^ k * (2 * (omega n).toReal * (2 * r) ^ (n + 2)) :=
              mul_le_mul_of_nonneg_right hFcard (by positivity)
          _ = 12 ^ k * 2 ^ (n + 3) * (omega n).toReal * r ^ (n + 2 - k) := by
              rw [mul_pow, hsplit]
              field_simp
              ring

/-- The constant for all equal-radius bounds and finite packing. -/
def isometricModelConstant (n k : ℕ) (hv : ℝ≥0∞) : ℝ :=
  hv.toReal * 2 ^ k + 6 ^ k + 12 ^ k * 2 ^ (n + 3) * (omega n).toReal

theorem isometricModelConstant_nonneg (n k : ℕ) (hv : ℝ≥0∞) :
    0 ≤ isometricModelConstant n k hv := by
  unfold isometricModelConstant
  have := (omega n).toReal_nonneg
  have := hv.toReal_nonneg
  positivity

theorem isometricModelConstant_pos (n k : ℕ) (hv : ℝ≥0∞) :
    0 < isometricModelConstant n k hv := by
  unfold isometricModelConstant
  have := (omega n).toReal_nonneg
  have := hv.toReal_nonneg
  positivity

/-- All metric content bounds and finite packing for a bounded subset of an
isometric model with exact ball volume and a Hausdorff upper comparison. -/
theorem content_of_isometry (hv : v ≠ 0) (hvfin : v ≠ ∞)
    (hball : ∀ y r, 0 < r → ν (Metric.ball y r) = v * ENNReal.ofReal r ^ k)
    (hH : ∀ E : Set Y, Measure.hausdorffMeasure (k : ℝ) E ≤ h * ν E) (hhfin : h ≠ ∞)
    (hι : Isometry ι) (hK : K ⊆ range ι) {c : Space n}
    (hKc : K ⊆ Metric.closedBall c 1) (hkn : k ≤ n + 2) :
    HasMetricContentBounds k (isometricModelConstant n k (h * v)) K ∧
      HasFiniteBallPacking k (isometricModelConstant n k (h * v)) K := by
  have hw : 0 ≤ (omega n).toReal := ENNReal.toReal_nonneg
  have hhv : 0 ≤ (h * v).toReal := ENNReal.toReal_nonneg
  have h6 : (0 : ℝ) ≤ 6 ^ k := by positivity
  have h12 : (0 : ℝ) ≤ 12 ^ k * 2 ^ (n + 3) * (omega n).toReal := by positivity
  have hhv2 : (0 : ℝ) ≤ (h * v).toReal * 2 ^ k := by positivity
  have h1 : (h * v).toReal * 2 ^ k ≤ isometricModelConstant n k (h * v) := by
    unfold isometricModelConstant
    linarith
  have h2 : (6 : ℝ) ^ k ≤ isometricModelConstant n k (h * v) := by
    unfold isometricModelConstant
    linarith
  have h3 : (3 : ℝ) ^ k ≤ isometricModelConstant n k (h * v) :=
    (pow_le_pow_left₀ (by norm_num) (by norm_num : (3 : ℝ) ≤ 6) k).trans h2
  have h4 : (12 : ℝ) ^ k * 2 ^ (n + 3) * (omega n).toReal ≤
      isometricModelConstant n k (h * v) := by
    unfold isometricModelConstant
    linarith
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro q R hR _
    refine (hausdorffP_inter_ball_le_of_isometry hvfin hball hH hhfin hι hK q hR).trans ?_
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h1 (by positivity))
  · intro q R r hR _ hr hrR F hF hsep
    exact (card_le_of_separated_of_isometry hv hvfin hball hι hK q hr hrR F hF hsep).trans
      (mul_le_mul_of_nonneg_right h2 (by positivity))
  · intro r hr hr1
    refine (parabolicVolume_thickening_le_of_isometry hv hvfin hball hι hK hKc hkn hr hr1).trans ?_
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h4 (by positivity))
  · intro q R hR hR1 l z r hz hr hd
    refine (sum_pow_le_of_disjoint_of_isometry hv hvfin hball hι hK q R hR hR1 l z r hz hr
      hd).trans ?_
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h3 (by positivity))

end IsometricModel

/-! ### The ambient endpoint -/

/-- At ambient dimension retain the whole original source inside the unit
ball vertically and nothing horizontally. Field for field this is
`ambientRetainedSets`, which is defined in a module importing this one; the two
are definitionally equal. -/
def unitBallVerticalSets (n : ℕ) : RetainedSets n where
  horizontal := ∅
  vertical := Metric.ball (point 0 0) 1
  measurable_horizontal := MeasurableSet.empty
  measurable_vertical := measurableSet_ball
  disjoint := by simp
  horizontal_subset := empty_subset _
  vertical_subset := Subset.rfl

/-- The zero function is a regular vertical function at every nonnegative
tolerance, on every spatial direction: constant `0`, compact perturbation `0`,
Lipschitz constant `0` and the zero half-time derivative with BMO bound `0`. -/
theorem isRegularVerticalFunction_zero {n : ℕ} (W : Submodule ℝ (Spatial n)) {ε : ℝ}
    (hε : 0 ≤ ε) : IsRegularVerticalFunction W (fun _ => 0) ε := by
  refine ⟨0, fun _ => 0, fun _ => 0, 0, 0, by simp, HasCompactSupport.zero,
    LipschitzWith.const 0, ⟨NNReal.coe_nonneg _, locallyIntegrable_zero, ?_⟩, ?_, by simpa using hε⟩
  · intro p r _
    simp [parabolicBallAverage]
  · intro i
    have h : normalFourierComponent W (fun _ => 0) i = fun _ => (0 : ℝ) := by
      funext x
      simp [normalFourierComponent]
    rw [h]
    exact ⟨MemLp.zero, HalfTimeDerivative.repHalf_zero isOpen_univ⟩

/-- The full vertical graph of the zero function covers the whole space. -/
theorem hasRegularVerticalGraphCover_ambient {n : ℕ} (K : Set (Space n)) {ε : ℝ}
    (hε : 0 ≤ ε) : HasRegularVerticalGraphCover (n + 2) K ε := by
  have hrank : Module.finrank ℝ (⊤ : Submodule ℝ (Spatial n)) + 2 = n + 2 := by
    rw [finrank_top, finrank_euclideanSpace_fin]
  let G : RegularVerticalGraph n (n + 2) ε :=
    { vertical_dimension := by omega
      direction := ⊤
      rank_eq := hrank
      offset := 0
      function := fun _ => 0
      regular := isRegularVerticalFunction_zero ⊤ hε }
  have hcov : K ⊆ G.image := by
    intro z _
    refine ⟨(⟨z.1, Submodule.mem_top⟩, z.2), ?_⟩
    simp [G]
  exact ⟨{0}, fun _ => G, measure_mono_null
    (fun x hx => (hx.2 (mem_iUnion.mpr ⟨⟨0, rfl⟩, hcov hx.1⟩)).elim) measure_empty⟩

/-- The statement of `ambient_retained_decomposition`, with the retained sets
written `unitBallVerticalSets`. The constant is
the isometric-model constant of `Space n` itself, plus one. -/
theorem ambientRetainedDecomposition_proof (n : ℕ) (_hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : Measure (Space n),
      IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      IsRectifiabilityDecomposition (n + 2) C 0 0 μ (unitBallVerticalSets n) ∧
      (unitBallVerticalSets n).remainderMeasure μ (Metric.ball (point 0 0) 1) = 0 := by
  have hv0 : 2 * omega n ≠ 0 := (ENNReal.mul_pos (by norm_num) (omega_pos n).ne').ne'
  have hvfin : 2 * omega n ≠ ∞ := ENNReal.mul_ne_top (by norm_num) (omega_lt_top n).ne
  have hball : ∀ (y : Space n) r, 0 < r →
      parabolicVolume n (Metric.ball y r) = 2 * omega n * ENNReal.ofReal r ^ (n + 2) :=
    fun y r hr => parabolicVolume_ball y r hr
  have hH : ∀ E : Set (Space n), Measure.hausdorffMeasure ((n + 2 : ℕ) : ℝ) E ≤
      verticalHausdorffConstant n * parabolicVolume n E :=
    fun E => (parabolic_hausdorff_comparison n E).2
  refine ⟨isometricModelConstant n (n + 2) (verticalHausdorffConstant n * (2 * omega n)),
    isometricModelConstant_pos _ _ _, fun μ _ _ => ?_⟩
  set D := unitBallVerticalSets n
  have hHmeas : D.horizontalMeasure μ = 0 := Measure.restrict_empty
  have hHsupp : D.horizontalSupport μ = ∅ := by
    show (D.horizontalMeasure μ).support = ∅
    rw [hHmeas, Measure.support_zero]
  have hVsupp : D.verticalSupport μ ⊆ Metric.closedBall (point 0 0) 1 :=
    support_restrict_subset_of_isClosed μ Metric.ball_subset_closedBall
      Metric.isClosed_closedBall
  have hK : D.supportUnion μ ⊆ Metric.closedBall (point 0 0) 1 := by
    show D.horizontalSupport μ ∪ D.verticalSupport μ ⊆ _
    rw [hHsupp, empty_union]
    exact hVsupp
  have hzero : D.remainderMeasure μ (Metric.ball (point 0 0) 1) = 0 := by
    show μ.restrict (∅ ∪ Metric.ball (point 0 0) 1)ᶜ (Metric.ball (point 0 0) 1) = 0
    rw [Measure.restrict_apply measurableSet_ball, empty_union, inter_compl_self,
      measure_empty]
  obtain ⟨hmet, hpack⟩ := content_of_isometry hv0 hvfin hball hH
    (verticalHausdorffConstant_lt_top n).ne isometry_id (fun z _ => ⟨z, rfl⟩) hK
    le_rfl
  refine ⟨?_, hzero⟩
  exact
    { measure_eq := D.measure_eq_sum μ
      remainder_bound := by
        rw [hzero]
        exact zero_le
      horizontal_compact := by
        rw [hHsupp]
        exact isCompact_empty
      vertical_compact :=
        (isCompact_closedBall _ _).of_isClosed_subset Measure.isClosed_support hVsupp
      horizontal_in_unit := by
        rw [hHsupp]
        exact empty_subset _
      vertical_in_unit := hVsupp
      horizontal_unavailable := fun _ => ⟨hHmeas, hHsupp⟩
      vertical_unavailable := fun h => (h ⟨by omega, le_rfl⟩).elim
      horizontal_graphs := fun ε _ => by
        rw [hHsupp]
        exact ⟨∅, fun i => absurd i.2 (Set.notMem_empty _), by simp⟩
      vertical_graphs := fun ε hε => hasRegularVerticalGraphCover_ambient _ hε.le
      content := HasRectifiabilityContentBounds.of_metric_packing hmet hpack }

end ParabolicRectifiability
