import ParabolicRectifiability.Basic

/-!
# Countably many exact attachments

The exact attachment lemma and its Euclidean-parameter form, used in the horizontal
chart construction.

A bi-Lipschitz map `Φ⁰(p) = (F⁰ p, τ p)` with constant `L ≤ 3/2` is corrected by a
spatial perturbation `G`, a pointwise sum of metric tents
`φ_c(p) = max 0 (1 - d(p, p_c) / (χ d_c))`, so that it passes exactly through the
prescribed centers, stays unchanged on the preimage of the core, and remains
bi-Lipschitz with constant `2`. No smoothness, countability or local finiteness is
used: the separated tents have pairwise disjoint supports, so at every point at most one
summand is nonzero (the sum is a `finsum`).

The shared tent estimate is `norm_tentSum_sub_le`; the perturbation estimate for a
product target with the maximum metric is `lipschitz_antilipschitz_of_perturb`.
`exists_exact_attachment` is the general statement for a target `V × Z`;
`exists_exact_attachment_vertical` is the parabolic form with base `Space m`
(`ℝ^m` with snowflaked time) and target `Space n`; `exists_exact_attachment_spatial`
is the Euclidean-parameter spatial form.

Compactness of the core and its containment in the image of `Φ⁰` are
not needed for these conclusions and are not assumed.
-/

noncomputable section

namespace ParabolicRectifiability.ExactAttachment

open Metric
open scoped NNReal

/-! ### Metric tents -/

section Tent

variable {P : Type*} [PseudoMetricSpace P]

/-- The metric tent of height one at `q` and radius `ρ`. -/
def tent (q : P) (ρ : ℝ) (p : P) : ℝ := max 0 (1 - dist p q / ρ)

theorem tent_self (q : P) (ρ : ℝ) : tent q ρ q = 1 := by
  rw [tent, dist_self, zero_div, sub_zero]
  exact max_eq_right zero_le_one

theorem tent_eq_zero {q p : P} {ρ : ℝ} (hρ : 0 < ρ) (h : ρ ≤ dist p q) : tent q ρ p = 0 := by
  rw [tent]
  apply max_eq_left
  have : 1 ≤ dist p q / ρ := (one_le_div hρ).mpr h
  linarith

theorem dist_lt_of_tent_ne_zero {q p : P} {ρ : ℝ} (hρ : 0 < ρ) (h : tent q ρ p ≠ 0) :
    dist p q < ρ :=
  not_le.mp fun hc => h (tent_eq_zero hρ hc)

/-- A tent of radius `ρ` is `1/ρ`-Lipschitz. -/
theorem abs_tent_sub_le (q : P) {ρ : ℝ} (hρ : 0 < ρ) (p p' : P) :
    |tent q ρ p - tent q ρ p'| ≤ dist p p' / ρ := by
  have h1 : |tent q ρ p - tent q ρ p'| ≤ |(1 - dist p q / ρ) - (1 - dist p' q / ρ)| := by
    simp only [tent]
    rw [max_comm 0, max_comm 0]
    exact abs_max_sub_max_le_abs _ _ _
  have h2 : (1 - dist p q / ρ) - (1 - dist p' q / ρ) = (dist p' q - dist p q) / ρ := by ring
  rw [h2, abs_div, abs_of_pos hρ] at h1
  have h3 : |dist p' q - dist p q| ≤ dist p p' := by
    rw [abs_sub_comm]
    exact abs_dist_sub_le p p' q
  exact h1.trans (div_le_div_of_nonneg_right h3 hρ.le)

end Tent

/-! ### Sums of separated tents -/

section TentSum

variable {P : Type*} [PseudoMetricSpace P]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {ι : Type*}

/-- The pointwise sum `∑ φ_i(p) v_i` of tents; separated tents make it a single term. -/
def tentSum (q : ι → P) (ρ : ι → ℝ) (v : ι → V) (p : P) : V :=
  ∑ᶠ i, tent (q i) (ρ i) p • v i

variable {q : ι → P} {ρ : ι → ℝ} {v : ι → V}

theorem tentSum_eq_of_forall_ne {p : P} (i : ι)
    (h : ∀ j, j ≠ i → tent (q j) (ρ j) p = 0) :
    tentSum q ρ v p = tent (q i) (ρ i) p • v i :=
  finsum_eq_single _ i fun j hj => by rw [h j hj, zero_smul]

theorem tentSum_eq_zero_of_forall {p : P} (h : ∀ j, tent (q j) (ρ j) p = 0) :
    tentSum q ρ v p = 0 := by
  unfold tentSum
  simp only [h, zero_smul, finsum_zero]

theorem tentSum_eq_zero (hρ : ∀ i, 0 < ρ i) {p : P} (h : ∀ i, ρ i ≤ dist p (q i)) :
    tentSum q ρ v p = 0 :=
  tentSum_eq_zero_of_forall fun j => tent_eq_zero (hρ j) (h j)

/-- Separated tents have disjoint supports. -/
theorem tent_eq_zero_of_ne (hρ : ∀ i, 0 < ρ i)
    (hsep : ∀ i j, i ≠ j → ρ i + ρ j ≤ dist (q i) (q j)) {p : P} {i j : ι} (hij : i ≠ j)
    (hi : tent (q i) (ρ i) p ≠ 0) : tent (q j) (ρ j) p = 0 := by
  by_contra hj
  have h1 := dist_lt_of_tent_ne_zero (hρ i) hi
  have h2 := dist_lt_of_tent_ne_zero (hρ j) hj
  have h3 := dist_triangle_left (q i) (q j) p
  have h4 := hsep i j hij
  linarith

theorem tentSum_center (hρ : ∀ i, 0 < ρ i)
    (hsep : ∀ i j, i ≠ j → ρ i + ρ j ≤ dist (q i) (q j)) (i : ι) :
    tentSum q ρ v (q i) = v i := by
  rw [tentSum_eq_of_forall_ne i, tent_self, one_smul]
  intro j hj
  apply tent_eq_zero (hρ j)
  have h := hsep j i hj
  have := hρ i
  rw [dist_comm] at h
  linarith

theorem norm_smul_tent_sub_le (hρ : ∀ i, 0 < ρ i) {K : ℝ} (hv : ∀ i, ‖v i‖ ≤ K * ρ i)
    (i : ι) (p p' : P) :
    ‖(tent (q i) (ρ i) p - tent (q i) (ρ i) p') • v i‖ ≤ K * dist p p' := by
  rw [norm_smul, Real.norm_eq_abs]
  calc |tent (q i) (ρ i) p - tent (q i) (ρ i) p'| * ‖v i‖
      ≤ dist p p' / ρ i * (K * ρ i) :=
        mul_le_mul (abs_tent_sub_le (q i) (hρ i) p p') (hv i) (norm_nonneg _)
          (div_nonneg dist_nonneg (hρ i).le)
    _ = K * dist p p' * (ρ i / ρ i) := by ring
    _ = K * dist p p' := by rw [div_self (hρ i).ne', mul_one]

theorem norm_tentSum_sub_le_of_index (hρ : ∀ i, 0 < ρ i) {K : ℝ} (hK : 0 ≤ K)
    (hv : ∀ i, ‖v i‖ ≤ K * ρ i) {p p' : P} (i j : ι)
    (hp : ∀ k, k ≠ i → tent (q k) (ρ k) p = 0) (hp' : ∀ k, k ≠ j → tent (q k) (ρ k) p' = 0) :
    ‖tentSum q ρ v p - tentSum q ρ v p'‖ ≤ 2 * K * dist p p' := by
  rw [tentSum_eq_of_forall_ne i hp, tentSum_eq_of_forall_ne j hp']
  have hKd : 0 ≤ K * dist p p' := mul_nonneg hK dist_nonneg
  by_cases hij : i = j
  · rw [← hij, ← sub_smul]
    have := norm_smul_tent_sub_le (q := q) hρ hv i p p'
    linarith
  · have h1 : tent (q i) (ρ i) p' = 0 := hp' i hij
    have h2 : tent (q j) (ρ j) p = 0 := hp j (Ne.symm hij)
    have he : tent (q i) (ρ i) p • v i - tent (q j) (ρ j) p' • v j =
        (tent (q i) (ρ i) p - tent (q i) (ρ i) p') • v i +
          (tent (q j) (ρ j) p - tent (q j) (ρ j) p') • v j := by
      rw [h1, h2, sub_zero, zero_sub, neg_smul, ← sub_eq_add_neg]
    rw [he]
    calc _ ≤ ‖(tent (q i) (ρ i) p - tent (q i) (ρ i) p') • v i‖ +
          ‖(tent (q j) (ρ j) p - tent (q j) (ρ j) p') • v j‖ := norm_add_le _ _
      _ ≤ K * dist p p' + K * dist p p' :=
          add_le_add (norm_smul_tent_sub_le (q := q) hρ hv i p p')
            (norm_smul_tent_sub_le (q := q) hρ hv j p p')
      _ = 2 * K * dist p p' := by ring

/-- The shared tent estimate: separated tents carrying vectors `‖v_i‖ ≤ K ρ_i` sum to a
`2K`-Lipschitz map, with no finiteness hypothesis on the family. -/
theorem norm_tentSum_sub_le (hρ : ∀ i, 0 < ρ i)
    (hsep : ∀ i j, i ≠ j → ρ i + ρ j ≤ dist (q i) (q j)) {K : ℝ} (hK : 0 ≤ K)
    (hv : ∀ i, ‖v i‖ ≤ K * ρ i) (p p' : P) :
    ‖tentSum q ρ v p - tentSum q ρ v p'‖ ≤ 2 * K * dist p p' := by
  by_cases hp : ∃ i, tent (q i) (ρ i) p ≠ 0
  · obtain ⟨i, hi⟩ := hp
    have hpi : ∀ k, k ≠ i → tent (q k) (ρ k) p = 0 :=
      fun k hk => tent_eq_zero_of_ne hρ hsep (Ne.symm hk) hi
    by_cases hp' : ∃ j, tent (q j) (ρ j) p' ≠ 0
    · obtain ⟨j, hj⟩ := hp'
      exact norm_tentSum_sub_le_of_index hρ hK hv i j hpi
        (fun k hk => tent_eq_zero_of_ne hρ hsep (Ne.symm hk) hj)
    · simp only [not_exists, ne_eq, not_not] at hp'
      exact norm_tentSum_sub_le_of_index hρ hK hv i i hpi (fun k _ => hp' k)
  · simp only [not_exists, ne_eq, not_not] at hp
    by_cases hp' : ∃ j, tent (q j) (ρ j) p' ≠ 0
    · obtain ⟨j, hj⟩ := hp'
      exact norm_tentSum_sub_le_of_index hρ hK hv j j (fun k _ => hp k)
        (fun k hk => tent_eq_zero_of_ne hρ hsep (Ne.symm hk) hj)
    · simp only [not_exists, ne_eq, not_not] at hp'
      rw [tentSum_eq_zero_of_forall hp, tentSum_eq_zero_of_forall hp', sub_zero, norm_zero]
      exact mul_nonneg (mul_nonneg zero_le_two hK) dist_nonneg

end TentSum

/-! ### Perturbing the spatial coordinate of a product map -/

section Perturb

variable {V Z : Type*} [NormedAddCommGroup V] [PseudoMetricSpace Z]

/-- Changing the first coordinate changes the maximum distance by at most the change. -/
theorem abs_dist_add_sub_dist_le (x x' g g' : V) (z z' : Z) :
    |dist ((x + g, z) : V × Z) (x' + g', z') - dist ((x, z) : V × Z) (x', z')| ≤ ‖g - g'‖ := by
  simp only [Prod.dist_eq]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  rw [dist_eq_norm, dist_eq_norm]
  have h : x + g - (x' + g') - (x - x') = g - g' := by abel
  calc |‖x + g - (x' + g')‖ - ‖x - x'‖| ≤ ‖x + g - (x' + g') - (x - x')‖ :=
        abs_norm_sub_norm_le _ _
    _ = ‖g - g'‖ := by rw [h]

/-- A `1/6`-Lipschitz spatial perturbation of an `L`-bi-Lipschitz map, `L ≤ 3/2`,
is `2`-bi-Lipschitz. -/
theorem lipschitz_antilipschitz_of_perturb {P : Type*} [PseudoMetricSpace P]
    (F₀ G : P → V) (τ : P → Z) (L : ℝ≥0) (hL : (L : ℝ) ≤ 3 / 2)
    (hlip : LipschitzWith L (fun p => ((F₀ p, τ p) : V × Z)))
    (hanti : AntilipschitzWith L (fun p => ((F₀ p, τ p) : V × Z)))
    (hG : ∀ p p', ‖G p - G p'‖ ≤ dist p p' / 6) :
    LipschitzWith 2 (fun p => ((F₀ p + G p, τ p) : V × Z)) ∧
      AntilipschitzWith 2 (fun p => ((F₀ p + G p, τ p) : V × Z)) := by
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  have h2c : ((2 : ℝ≥0) : ℝ) = 2 := by norm_num
  have key : ∀ p p', |dist ((F₀ p + G p, τ p) : V × Z) (F₀ p' + G p', τ p') -
      dist ((F₀ p, τ p) : V × Z) (F₀ p', τ p')| ≤ dist p p' / 6 :=
    fun p p' => (abs_dist_add_sub_dist_le _ _ _ _ _ _).trans (hG p p')
  constructor
  · apply LipschitzWith.of_dist_le_mul
    intro p p'
    show dist ((F₀ p + G p, τ p) : V × Z) (F₀ p' + G p', τ p') ≤ ((2 : ℝ≥0) : ℝ) * dist p p'
    have h1 : dist ((F₀ p, τ p) : V × Z) (F₀ p', τ p') ≤ L * dist p p' := hlip.dist_le_mul p p'
    have h2 := (abs_le.mp (key p p')).2
    have h3 : (L : ℝ) * dist p p' ≤ 3 / 2 * dist p p' :=
      mul_le_mul_of_nonneg_right hL dist_nonneg
    have hd : 0 ≤ dist p p' := dist_nonneg
    rw [h2c]
    linarith
  · apply AntilipschitzWith.of_le_mul_dist
    intro p p'
    show dist p p' ≤ ((2 : ℝ≥0) : ℝ) * dist ((F₀ p + G p, τ p) : V × Z) (F₀ p' + G p', τ p')
    have h1 : dist p p' ≤ L * dist ((F₀ p, τ p) : V × Z) (F₀ p', τ p') := hanti.le_mul_dist p p'
    have h2 := (abs_le.mp (key p p')).1
    have hd : 0 ≤ dist p p' := dist_nonneg
    have hD : 0 ≤ dist ((F₀ p + G p, τ p) : V × Z) (F₀ p' + G p', τ p') := dist_nonneg
    have h3 : (L : ℝ) * dist ((F₀ p, τ p) : V × Z) (F₀ p', τ p') ≤
        L * (dist ((F₀ p + G p, τ p) : V × Z) (F₀ p' + G p', τ p') + dist p p' / 6) :=
      mul_le_mul_of_nonneg_left (by linarith) hL0
    have h4 : (L : ℝ) * (dist p p' / 6) ≤ 3 / 2 * (dist p p' / 6) :=
      mul_le_mul_of_nonneg_right hL (by positivity)
    have h5 : (L : ℝ) * dist ((F₀ p + G p, τ p) : V × Z) (F₀ p' + G p', τ p') ≤
        3 / 2 * dist ((F₀ p + G p, τ p) : V × Z) (F₀ p' + G p', τ p') :=
      mul_le_mul_of_nonneg_right hL hD
    rw [h2c]
    linarith

end Perturb

/-! ### The attachment -/

/-- The numerics of the attachment lemma: with `c₁ = min(c₀,1)/3` and `χ = c₁/10`,
`ζ ≤ min(c₀,1)/720` gives `4ζ/χ ≤ 1/6`. -/
theorem attachment_numerics {c₀ ζ : ℝ} (hm : 0 < min c₀ 1) (hζ : ζ ≤ min c₀ 1 / 720) :
    4 * ζ / (min c₀ 1 / 3 / 10) ≤ 1 / 6 := by
  rw [div_le_iff₀ (by positivity)]
  linarith

section Attachment

variable {P V Z ι : Type*} [PseudoMetricSpace P] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [PseudoMetricSpace Z]

/-- Exact attachment for a general parameter space `P` and product target `V × Z`
with the maximum metric. `Φ⁰ p = (F⁰ p, τ p)` is `L`-bi-Lipschitz with `L ≤ 3/2`; the
centers `c i` with radii `d i > 0` are `c₀`-separated and at distance at least `d i` from
the core `C₀`; the parameters `p i` lie at the centers' own `Z`-coordinates with spatial
error at most `2ζ d i`, `0 ≤ ζ ≤ min(c₀,1)/720`. Then a spatial perturbation `G` makes
`Φ = (F⁰ + G, τ)` `2`-bi-Lipschitz, keeps `Φ⁰` unchanged on its preimage of `C₀`, and
attaches every center exactly. -/
theorem exists_exact_attachment (F₀ : P → V) (τ : P → Z) (L : ℝ≥0) (hL : (L : ℝ) ≤ 3 / 2)
    (hlip : LipschitzWith L (fun p => ((F₀ p, τ p) : V × Z)))
    (hanti : AntilipschitzWith L (fun p => ((F₀ p, τ p) : V × Z)))
    (C₀ : Set (V × Z)) (c : ι → V × Z) (d : ι → ℝ) (c₀ : ℝ) (hd : ∀ i, 0 < d i)
    (hsep : ∀ i j, i ≠ j → c₀ * max (d i) (d j) ≤ dist (c i) (c j))
    (hcore : ∀ i, ∀ z ∈ C₀, d i ≤ dist (c i) z)
    (p : ι → P) (htime : ∀ i, τ (p i) = (c i).2)
    (ζ : ℝ) (hζ0 : 0 ≤ ζ) (hζ : ζ ≤ min c₀ 1 / 720)
    (hclose : ∀ i, ‖F₀ (p i) - (c i).1‖ ≤ 2 * ζ * d i) :
    ∃ G : P → V,
      LipschitzWith 2 (fun q => ((F₀ q + G q, τ q) : V × Z)) ∧
      AntilipschitzWith 2 (fun q => ((F₀ q + G q, τ q) : V × Z)) ∧
      (∀ q, ((F₀ q, τ q) : V × Z) ∈ C₀ → G q = 0) ∧
      (∀ i, ((F₀ (p i) + G (p i), τ (p i)) : V × Z) = c i) ∧
      (∀ q q', ‖G q - G q'‖ ≤ dist q q' / 6) := by
  have hcenter : ∀ i, dist ((F₀ (p i), τ (p i)) : V × Z) (c i) ≤ 2 * ζ * d i := by
    intro i
    simp only [Prod.dist_eq, htime, dist_self, dist_eq_norm]
    exact max_le (hclose i) (mul_nonneg (mul_nonneg zero_le_two hζ0) (hd i).le)
  suffices hG : ∃ G : P → V, (∀ q q', ‖G q - G q'‖ ≤ dist q q' / 6) ∧
      (∀ q, ((F₀ q, τ q) : V × Z) ∈ C₀ → G q = 0) ∧ (∀ i, G (p i) = (c i).1 - F₀ (p i)) by
    obtain ⟨G, hGl, hG0, hGc⟩ := hG
    obtain ⟨hl2, ha2⟩ := lipschitz_antilipschitz_of_perturb F₀ G τ L hL hlip hanti hGl
    refine ⟨G, hl2, ha2, hG0, fun i => ?_, hGl⟩
    rw [hGc i, htime i]
    ext
    · simp
    · rfl
  rcases hζ0.eq_or_lt with hζz | hζpos
  · -- `ζ = 0`: the centers are already attained and no correction is needed.
    refine ⟨fun _ => 0, fun q q' => ?_, fun q _ => rfl, fun i => ?_⟩
    · simp only [sub_self, norm_zero]
      positivity
    · have h := hclose i
      rw [← hζz, mul_zero, zero_mul] at h
      have he : F₀ (p i) = (c i).1 := sub_eq_zero.mp (norm_le_zero_iff.mp h)
      show (0 : V) = (c i).1 - F₀ (p i)
      rw [he, sub_self]
  · set m₀ := min c₀ 1
    have hm₀ : 0 < m₀ := by linarith
    have hm₀c : m₀ ≤ c₀ := min_le_left _ _
    have hm₀1 : m₀ ≤ 1 := min_le_right _ _
    set χ := m₀ / 3 / 10 with hχdef
    have hχ : 0 < χ := by positivity
    have hχne : χ ≠ 0 := hχ.ne'
    have hρ : ∀ i, 0 < χ * d i := fun i => mul_pos hχ (hd i)
    -- Parameter separation: the closed tents are disjoint.
    have hsepP : ∀ i j, i ≠ j → χ * d i + χ * d j ≤ dist (p i) (p j) := by
      intro i j hij
      have h1 := hsep i j hij
      have h2 := hcenter i
      have h3 := hcenter j
      have h4 : dist ((F₀ (p i), τ (p i)) : V × Z) (F₀ (p j), τ (p j)) ≤
          L * dist (p i) (p j) := hlip.dist_le_mul _ _
      have h5 : (L : ℝ) * dist (p i) (p j) ≤ 3 / 2 * dist (p i) (p j) :=
        mul_le_mul_of_nonneg_right hL dist_nonneg
      have h6 := dist_triangle4 (c i) ((F₀ (p i), τ (p i)) : V × Z) (F₀ (p j), τ (p j)) (c j)
      rw [dist_comm (c i) ((F₀ (p i), τ (p i)) : V × Z)] at h6
      have hMi : d i ≤ max (d i) (d j) := le_max_left _ _
      have hMj : d j ≤ max (d i) (d j) := le_max_right _ _
      have hM0 : 0 ≤ max (d i) (d j) := (hd i).le.trans hMi
      have e1 : ζ * d i ≤ ζ * max (d i) (d j) := mul_le_mul_of_nonneg_left hMi hζpos.le
      have e2 : ζ * d j ≤ ζ * max (d i) (d j) := mul_le_mul_of_nonneg_left hMj hζpos.le
      have e3 : ζ * max (d i) (d j) ≤ m₀ / 720 * max (d i) (d j) :=
        mul_le_mul_of_nonneg_right hζ hM0
      have e4 : m₀ * max (d i) (d j) ≤ c₀ * max (d i) (d j) :=
        mul_le_mul_of_nonneg_right hm₀c hM0
      have e5 : m₀ * d i ≤ m₀ * max (d i) (d j) := mul_le_mul_of_nonneg_left hMi hm₀.le
      have e6 : m₀ * d j ≤ m₀ * max (d i) (d j) := mul_le_mul_of_nonneg_left hMj hm₀.le
      have e7 : 0 ≤ m₀ * max (d i) (d j) := mul_nonneg hm₀.le hM0
      rw [hχdef]
      linarith
    -- Parameters of the core lie outside every tent.
    have hcoreP : ∀ q, ((F₀ q, τ q) : V × Z) ∈ C₀ → ∀ i, χ * d i ≤ dist q (p i) := by
      intro q hq i
      have h1 := hcore i _ hq
      have h2 := hcenter i
      have h4 : dist ((F₀ (p i), τ (p i)) : V × Z) (F₀ q, τ q) ≤ L * dist (p i) q :=
        hlip.dist_le_mul _ _
      have h5 : (L : ℝ) * dist (p i) q ≤ 3 / 2 * dist (p i) q :=
        mul_le_mul_of_nonneg_right hL dist_nonneg
      have h6 := dist_triangle (c i) ((F₀ (p i), τ (p i)) : V × Z) (F₀ q, τ q)
      rw [dist_comm (c i) ((F₀ (p i), τ (p i)) : V × Z)] at h6
      rw [dist_comm q]
      have e1 : ζ * d i ≤ 1 / 720 * d i :=
        mul_le_mul_of_nonneg_right (by linarith) (hd i).le
      have e2 : m₀ * d i ≤ 1 * d i := mul_le_mul_of_nonneg_right hm₀1 (hd i).le
      have := hd i
      rw [hχdef]
      linarith
    have hK : 0 ≤ 2 * ζ / χ := div_nonneg (by linarith) hχ.le
    have hv : ∀ i, ‖(c i).1 - F₀ (p i)‖ ≤ 2 * ζ / χ * (χ * d i) := by
      intro i
      rw [norm_sub_rev]
      calc ‖F₀ (p i) - (c i).1‖ ≤ 2 * ζ * d i := hclose i
        _ = 2 * ζ / χ * (χ * d i) := by field_simp
    have hnum : 4 * ζ / χ ≤ 1 / 6 := attachment_numerics hm₀ hζ
    refine ⟨tentSum p (fun i => χ * d i) (fun i => (c i).1 - F₀ (p i)), fun q q' => ?_,
      fun q hq => tentSum_eq_zero hρ (hcoreP q hq),
      fun i => tentSum_center hρ hsepP i⟩
    calc _ ≤ 2 * (2 * ζ / χ) * dist q q' := norm_tentSum_sub_le hρ hsepP hK hv q q'
      _ = 4 * ζ / χ * dist q q' := by ring
      _ ≤ 1 / 6 * dist q q' := mul_le_mul_of_nonneg_right hnum dist_nonneg
      _ = dist q q' / 6 := by ring

end Attachment

/-- Exact attachment in its parabolic form: parameters in the base `Space m`
(`ℝ^m` with snowflaked time), `Φ⁰(u,t) = (F⁰(u,t), t)` into `Space n`, and parameters
`p i` at the centers' own times. -/
theorem exists_exact_attachment_vertical {m n : ℕ} {ι : Type*}
    (F₀ : Space m → Spatial n) (L : ℝ≥0) (hL : (L : ℝ) ≤ 3 / 2)
    (hlip : LipschitzWith L (fun p : Space m => ((F₀ p, p.2) : Space n)))
    (hanti : AntilipschitzWith L (fun p : Space m => ((F₀ p, p.2) : Space n)))
    (C₀ : Set (Space n)) (c : ι → Space n) (d : ι → ℝ) (c₀ : ℝ) (hd : ∀ i, 0 < d i)
    (hsep : ∀ i j, i ≠ j → c₀ * max (d i) (d j) ≤ dist (c i) (c j))
    (hcore : ∀ i, ∀ z ∈ C₀, d i ≤ dist (c i) z)
    (p : ι → Space m) (htime : ∀ i, (p i).2 = (c i).2)
    (ζ : ℝ) (hζ0 : 0 ≤ ζ) (hζ : ζ ≤ min c₀ 1 / 720)
    (hclose : ∀ i, ‖F₀ (p i) - (c i).1‖ ≤ 2 * ζ * d i) :
    ∃ G : Space m → Spatial n,
      LipschitzWith 2 (fun q : Space m => ((F₀ q + G q, q.2) : Space n)) ∧
      AntilipschitzWith 2 (fun q : Space m => ((F₀ q + G q, q.2) : Space n)) ∧
      (∀ q, ((F₀ q, q.2) : Space n) ∈ C₀ → G q = 0) ∧
      (∀ i, ((F₀ (p i) + G (p i), (p i).2) : Space n) = c i) ∧
      (∀ q q', ‖G q - G q'‖ ≤ dist q q' / 6) :=
  exists_exact_attachment F₀ Prod.snd L hL hlip hanti C₀ c d c₀ hd hsep hcore p htime
    ζ hζ0 hζ hclose

section Spatial

variable {P V ι : Type*} [PseudoMetricSpace P] [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedSpace ℝ V] in
theorem dist_pair_unit (a b : V) : dist ((a, ()) : V × Unit) (b, ()) = dist a b := by
  simp only [Prod.dist_eq, dist_self]
  exact max_eq_left dist_nonneg

omit [NormedSpace ℝ V] in
theorem dist_pair_unit_left (a : V) (w : V × Unit) :
    dist ((a, ()) : V × Unit) w = dist a w.1 := by
  obtain ⟨b, hb⟩ := w
  cases hb
  exact dist_pair_unit a b

/-- The Euclidean-parameter spatial form used for horizontal charts: `F⁰ : P → V`
`L`-bi-Lipschitz with `L ≤ 3/2`, spatial centers with the same separations. -/
theorem exists_exact_attachment_spatial (F₀ : P → V) (L : ℝ≥0) (hL : (L : ℝ) ≤ 3 / 2)
    (hlip : LipschitzWith L F₀) (hanti : AntilipschitzWith L F₀)
    (C₀ : Set V) (x : ι → V) (d : ι → ℝ) (c₀ : ℝ) (hd : ∀ i, 0 < d i)
    (hsep : ∀ i j, i ≠ j → c₀ * max (d i) (d j) ≤ dist (x i) (x j))
    (hcore : ∀ i, ∀ z ∈ C₀, d i ≤ dist (x i) z)
    (u : ι → P) (ζ : ℝ) (hζ0 : 0 ≤ ζ) (hζ : ζ ≤ min c₀ 1 / 720)
    (hclose : ∀ i, ‖F₀ (u i) - x i‖ ≤ 2 * ζ * d i) :
    ∃ G : P → V,
      LipschitzWith 2 (fun q => F₀ q + G q) ∧ AntilipschitzWith 2 (fun q => F₀ q + G q) ∧
      (∀ q, F₀ q ∈ C₀ → G q = 0) ∧ (∀ i, F₀ (u i) + G (u i) = x i) ∧
      (∀ q q', ‖G q - G q'‖ ≤ dist q q' / 6) := by
  have hlip' : LipschitzWith L (fun q => ((F₀ q, ()) : V × Unit)) :=
    LipschitzWith.of_dist_le_mul fun q q' => by
      show dist ((F₀ q, ()) : V × Unit) (F₀ q', ()) ≤ _
      rw [dist_pair_unit]
      exact hlip.dist_le_mul q q'
  have hanti' : AntilipschitzWith L (fun q => ((F₀ q, ()) : V × Unit)) :=
    AntilipschitzWith.of_le_mul_dist fun q q' => by
      show _ ≤ _ * dist ((F₀ q, ()) : V × Unit) (F₀ q', ())
      rw [dist_pair_unit]
      exact hanti.le_mul_dist q q'
  obtain ⟨G, h1, h2, h3, h4, h5⟩ := exists_exact_attachment F₀ (fun _ => ()) L hL hlip' hanti'
    {w | w.1 ∈ C₀} (fun i => (x i, ())) d c₀ hd
    (fun i j hij => by
      show c₀ * max (d i) (d j) ≤ dist ((x i, ()) : V × Unit) (x j, ())
      rw [dist_pair_unit]
      exact hsep i j hij)
    (fun i w hw => by
      show d i ≤ dist ((x i, ()) : V × Unit) w
      rw [dist_pair_unit_left]
      exact hcore i _ hw)
    u (fun _ => rfl) ζ hζ0 hζ hclose
  refine ⟨G, LipschitzWith.of_dist_le_mul fun q q' => ?_,
    AntilipschitzWith.of_le_mul_dist fun q q' => ?_, fun q hq => h3 q hq,
    fun i => congrArg Prod.fst (h4 i), h5⟩
  · have h : dist ((F₀ q + G q, ()) : V × Unit) (F₀ q' + G q', ()) ≤
        ((2 : ℝ≥0) : ℝ) * dist q q' :=
      h1.dist_le_mul q q'
    show dist (F₀ q + G q) (F₀ q' + G q') ≤ _
    rw [← dist_pair_unit]
    exact h
  · have h : dist q q' ≤
        ((2 : ℝ≥0) : ℝ) * dist ((F₀ q + G q, ()) : V × Unit) (F₀ q' + G q', ()) :=
      h2.le_mul_dist q q'
    show dist q q' ≤ _ * dist (F₀ q + G q) (F₀ q' + G q')
    rw [← dist_pair_unit]
    exact h

end Spatial

end ParabolicRectifiability.ExactAttachment
