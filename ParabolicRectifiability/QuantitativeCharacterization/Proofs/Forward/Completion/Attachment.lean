import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Completion

/-! # The smooth separated attachments

`d1e_attachment_proof` has the type `d1e_AttachmentStatement`.

Route. Write `B = SmoothCutoff.bumpBound (k - 2) ≥ 1`, `d_c = N.radius c` and
`r_c = χ d_c / 3`; the margin is `c_A = (144 B)⁻¹`. Every statement concerns the maps defined
from the one datum `K`; the bump is the base
`SmoothCutoff.parabolicBump` (never the metric tents of `exists_exact_attachment`).
* **Bump.** `φ_c = parabolicBump r_c p_c` has `‖D_x φ_c‖ ≤ B/r_c`, `|∂_t φ_c| ≤ B/r_c²` and
  `0 ≤ φ_c ≤ 1`; the mean value theorem in each variable and `|φ_c(p) - φ_c(p')| ≤ 1` for
  `d_P(p,p') > r_c` give `|φ_c(p) - φ_c(p')| ≤ (2B/r_c) d_P(p,p') = (6B/(χ d_c)) d_P(p,p')`.
  It is one at `p_c` and vanishes off the open ball `P_b(p_c, χ d_c)`
  (`point_mem_ball_of_mem_bumpSupportSet`: its closed support lies strictly inside).
* **Supports.** By `ball_disjoint` the open balls `P_b(p_c, χ d_c)` are pairwise disjoint
  (closed balls may touch), so at each parameter at most one term of `G = ∑' g_c` is nonzero and
  `G` is a finite sum over the at most two active stops of any two parameters.
* **Lipschitz.** `|v_c| ≤ 2ζ d_c` gives `Lip_P g_c ≤ 12 B ζ/χ ≤ 1/12`, hence
  `Lip_P G ≤ 1/6 < 2/9`; in particular `G` is continuous.
* **Bi-Lipschitz and displacement.** `Φ` differs from `Φ⁰` by `G` in the spatial coordinate only,
  so `4/5 - 1/6 ≥ 1/2` and `11/10 + 1/6 ≤ 2`; `Lip_P(F - F₀) ≤ 11/10 + 1/6 + 1 ≤ 3`.
* **Exact attachment.** `G(p_c) = v_c` (own bump one, others zero), so `Φ(p_c) = c` by
  `pre_time`; at a core preimage every bump vanishes (`core_avoid`), so `Φ = Φ⁰` there and the
  core stays in the image.
* **Compact support.** `|Φ⁰(p_c) - c| ≤ 2|ζ| C_d R`, `c ∈ closedBall q R` and the lower metric
  bound of `Φ⁰` bound every `p_c`; the radii are at most `C_d R`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

/-! ## The base bump on the parameter space -/

section Bump

variable {m : ℕ}

/-- The parabolic distance of the base `Space m`. -/
theorem d1eattach_dist_eq (p p' : Space m) :
    dist p p' = max ‖p.1 - p'.1‖ (Real.sqrt |p.2.val - p'.2.val|) :=
  dist_point p.1 p'.1 p.2.val p'.2.val

theorem d1eattach_norm_fst_le (p p' : Space m) : ‖p.1 - p'.1‖ ≤ dist p p' := by
  rw [d1eattach_dist_eq]
  exact le_max_left _ _

theorem d1eattach_abs_time_le (p p' : Space m) : |p.2.val - p'.2.val| ≤ dist p p' ^ 2 := by
  have h : Real.sqrt |p.2.val - p'.2.val| ≤ dist p p' := by
    rw [d1eattach_dist_eq]
    exact le_max_right _ _
  calc |p.2.val - p'.2.val| = Real.sqrt |p.2.val - p'.2.val| ^ 2 :=
        (Real.sq_sqrt (abs_nonneg _)).symm
    _ ≤ dist p p' ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

/-- **Parabolic Lipschitz bound of the base bump**: `|φ(p) - φ(p')| ≤ (2B/r) d_P(p,p')`. -/
theorem d1eattach_abs_bump_sub_le {r : ℝ} (hr : 0 < r) (z p p' : Space m) :
    |SmoothCutoff.parabolicBump r z (p.1, p.2.val) -
        SmoothCutoff.parabolicBump r z (p'.1, p'.2.val)| ≤
      2 * SmoothCutoff.bumpBound m / r * dist p p' := by
  have hB1 : 1 ≤ SmoothCutoff.bumpBound m := SmoothCutoff.one_le_bumpBound m
  have hd0 : 0 ≤ dist p p' := dist_nonneg
  have hx := d1eattach_norm_fst_le p p'
  have ht := d1eattach_abs_time_le p p'
  have hdiff : Differentiable ℝ (SmoothCutoff.parabolicBump r z) :=
    (SmoothCutoff.contDiff_parabolicBump r z).differentiable (by simp)
  have hsp : ‖SmoothCutoff.parabolicBump r z (p.1, p.2.val) -
      SmoothCutoff.parabolicBump r z (p'.1, p.2.val)‖ ≤
        SmoothCutoff.bumpBound m / r * ‖p.1 - p'.1‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (f := fun y : Spatial m => SmoothCutoff.parabolicBump r z (y, p.2.val))
      (fun y _ => by
        have hg : DifferentiableAt ℝ (fun w : Spatial m => ((w, p.2.val) : Spatial m × ℝ)) y :=
          differentiableAt_id.prodMk (differentiableAt_const _)
        exact (hdiff (y, p.2.val)).comp y hg)
      (fun y _ => SmoothCutoff.norm_fderiv_parabolicBump_spatial_le hr z p.2.val y)
      convex_univ (mem_univ p'.1) (mem_univ p.1)
  have htm : ‖SmoothCutoff.parabolicBump r z (p'.1, p.2.val) -
      SmoothCutoff.parabolicBump r z (p'.1, p'.2.val)‖ ≤
        SmoothCutoff.bumpBound m / r ^ 2 * ‖p.2.val - p'.2.val‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun s : ℝ => SmoothCutoff.parabolicBump r z (p'.1, s))
      (fun s _ => by
        have hg : DifferentiableAt ℝ (fun w : ℝ => ((p'.1, w) : Spatial m × ℝ)) s :=
          (differentiableAt_const _).prodMk differentiableAt_id
        exact (hdiff (p'.1, s)).comp s hg)
      (fun s _ => by
        rw [Real.norm_eq_abs]
        exact SmoothCutoff.abs_deriv_parabolicBump_time_le hr z p'.1 s)
      convex_univ (mem_univ p'.2.val) (mem_univ p.2.val)
  rw [Real.norm_eq_abs] at hsp htm
  rw [Real.norm_eq_abs] at htm
  have hB0 : 0 ≤ SmoothCutoff.bumpBound m / r := div_nonneg (by linarith) hr.le
  have hB2 : 0 ≤ SmoothCutoff.bumpBound m / r ^ 2 := div_nonneg (by linarith) (by positivity)
  have hsum : |SmoothCutoff.parabolicBump r z (p.1, p.2.val) -
      SmoothCutoff.parabolicBump r z (p'.1, p'.2.val)| ≤
        SmoothCutoff.bumpBound m / r * dist p p' +
          SmoothCutoff.bumpBound m / r ^ 2 * dist p p' ^ 2 :=
    calc _ ≤ |SmoothCutoff.parabolicBump r z (p.1, p.2.val) -
            SmoothCutoff.parabolicBump r z (p'.1, p.2.val)| +
          |SmoothCutoff.parabolicBump r z (p'.1, p.2.val) -
            SmoothCutoff.parabolicBump r z (p'.1, p'.2.val)| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add (hsp.trans (mul_le_mul_of_nonneg_left hx hB0))
          (htm.trans (mul_le_mul_of_nonneg_left ht hB2))
  rcases le_or_gt (dist p p') r with hdr | hdr
  · have h1 : dist p p' / r ≤ 1 := (div_le_one hr).2 hdr
    have e : SmoothCutoff.bumpBound m / r ^ 2 * dist p p' ^ 2 =
        SmoothCutoff.bumpBound m / r * dist p p' * (dist p p' / r) := by
      field_simp
    have h2 : SmoothCutoff.bumpBound m / r * dist p p' * (dist p p' / r) ≤
        SmoothCutoff.bumpBound m / r * dist p p' :=
      (mul_le_mul_of_nonneg_left h1 (mul_nonneg hB0 hd0)).trans_eq (mul_one _)
    have e2 : 2 * SmoothCutoff.bumpBound m / r * dist p p' =
        SmoothCutoff.bumpBound m / r * dist p p' + SmoothCutoff.bumpBound m / r * dist p p' := by
      ring
    rw [e2]
    linarith
  · have h1 : 1 < dist p p' / r := (one_lt_div hr).2 hdr
    have hφ : |SmoothCutoff.parabolicBump r z (p.1, p.2.val) -
        SmoothCutoff.parabolicBump r z (p'.1, p'.2.val)| ≤ 1 := by
      have a1 := SmoothCutoff.parabolicBump_nonneg r z (p.1, p.2.val)
      have a2 := SmoothCutoff.parabolicBump_le_one r z (p.1, p.2.val)
      have a3 := SmoothCutoff.parabolicBump_nonneg r z (p'.1, p'.2.val)
      have a4 := SmoothCutoff.parabolicBump_le_one r z (p'.1, p'.2.val)
      rw [abs_sub_le_iff]
      constructor <;> linarith
    have e : 2 * SmoothCutoff.bumpBound m / r * dist p p' =
        2 * SmoothCutoff.bumpBound m * (dist p p' / r) := by ring
    rw [e]
    have h3 : dist p p' / r ≤ 2 * SmoothCutoff.bumpBound m * (dist p p' / r) := by
      have h4 : 0 ≤ dist p p' / r := div_nonneg hd0 hr.le
      nlinarith
    linarith

/-- A base parameter is the point of its coordinates. -/
theorem d1eattach_point_eq (p : Space m) : point p.1 p.2.val = p :=
  Prod.ext rfl (Metric.Snowflaking.toSnowflaking_ofSnowflaking p.2)

/-- A nonzero value of the bump lies in the open `3r`-ball: the closed support of the bump lies
strictly inside it. -/
theorem d1eattach_dist_lt_of_bump_ne_zero {r : ℝ} (hr : 0 < r) (z p : Space m)
    (h : SmoothCutoff.parabolicBump r z (p.1, p.2.val) ≠ 0) : dist p z < 3 * r := by
  have hmem : (p.1, p.2.val) ∈ SmoothCutoff.bumpSupportSet r z := by
    by_contra hn
    exact h (SmoothCutoff.parabolicBump_eq_zero hr hn)
  have h1 := SmoothCutoff.point_mem_ball_of_mem_bumpSupportSet hr hmem
  rw [d1eattach_point_eq p, Metric.mem_ball] at h1
  exact h1

/-- The bump is one at its centre. -/
theorem d1eattach_bump_self {r : ℝ} (hr : 0 < r) (z : Space m) :
    SmoothCutoff.parabolicBump r z (z.1, z.2.val) = 1 := by
  have h : point (z.1, z.2.val).1 (z.1, z.2.val).2 ∈ Metric.ball z (2 * r) := by
    rw [d1eattach_point_eq z]
    exact Metric.mem_ball_self (by positivity)
  exact SmoothCutoff.parabolicBump_eq_one hr h

end Bump

/-! ## The attachment of one completion datum -/

section Attachment

variable {n k : ℕ} {ι : Type*} {q : Space n} {R c₀ Cd Cs σ δ E κ θ γ : ℝ}
  {N : NeckRegion n k .vertical ι q R c₀ Cd Cs σ δ E κ θ γ} {χ ζ : ℝ}
  (K : d1e_VerticalCompletion N χ ζ)

/-- A term vanishes outside the open ball `P_b(p_c, χ d_c)`. -/
theorem d1eattach_bumpTerm_eq_zero (hχ : 0 < χ) {c : Space n} (hc : c ∈ N.stopping)
    {p : Space (NeckType.vertical.rank k)} (hp : χ * N.radius c ≤ dist p (K.pre c)) :
    K.bumpTerm c p = 0 := by
  have hd : 0 < N.radius c := hc.2
  have hr : 0 < χ * N.radius c / 3 := div_pos (mul_pos hχ hd) (by norm_num)
  have hφ : SmoothCutoff.parabolicBump (χ * N.radius c / 3) (K.pre c) (p.1, p.2.val) = 0 := by
    by_contra h
    have h1 := d1eattach_dist_lt_of_bump_ne_zero hr (K.pre c) p h
    have h2 : 3 * (χ * N.radius c / 3) = χ * N.radius c := by ring
    linarith
  simp only [d1e_VerticalCompletion.bumpTerm, hφ, zero_smul]

/-- Disjointness of the open bump balls. -/
theorem d1eattach_eq_of_active {c c' : Space n} (hc : c ∈ N.stopping) (hc' : c' ∈ N.stopping)
    {p : Space (NeckType.vertical.rank k)} (h1 : dist p (K.pre c) < χ * N.radius c)
    (h2 : dist p (K.pre c') < χ * N.radius c') : c = c' := by
  by_contra hne
  have h3 := K.ball_disjoint c hc c' hc' hne
  have h4 := dist_triangle_left (K.pre c) (K.pre c') p
  linarith

/-- At each parameter at most one term is active. -/
theorem d1eattach_exists_active (hχ : 0 < χ) (p : Space (NeckType.vertical.rank k)) :
    ∃ s : Finset N.stopping, s.card ≤ 1 ∧
      ∀ c : N.stopping, c ∉ s → K.bumpTerm (c : Space n) p = 0 := by
  classical
  by_cases h : ∃ c : N.stopping, dist p (K.pre c) < χ * N.radius c
  · obtain ⟨c₀, hc₀⟩ := h
    refine ⟨{c₀}, by simp, fun c hc => ?_⟩
    refine d1eattach_bumpTerm_eq_zero K hχ c.2 (not_lt.mp fun hlt => hc ?_)
    rw [Finset.mem_singleton]
    exact Subtype.ext (d1eattach_eq_of_active K c.2 c₀.2 hlt hc₀)
  · push Not at h
    exact ⟨∅, by simp, fun c _ => d1eattach_bumpTerm_eq_zero K hχ c.2 (h c)⟩

/-- The attachment is the finite sum over any finite set containing the active terms. -/
theorem d1eattach_attachment_eq_sum {p : Space (NeckType.vertical.rank k)}
    {s : Finset N.stopping} (hs : ∀ c : N.stopping, c ∉ s → K.bumpTerm (c : Space n) p = 0) :
    K.attachment p = ∑ c ∈ s, K.bumpTerm (c : Space n) p := by
  unfold d1e_VerticalCompletion.attachment
  exact tsum_eq_sum hs

/-- `Lip_P g_c ≤ 12 B ζ/χ ≤ 1/12`. -/
theorem d1eattach_norm_bumpTerm_sub_le (hχ : 0 < χ)
    (hζ : ζ ≤ (144 * SmoothCutoff.bumpBound (NeckType.vertical.rank k))⁻¹ * χ)
    {c : Space n} (hc : c ∈ N.stopping) (p p' : Space (NeckType.vertical.rank k)) :
    ‖K.bumpTerm c p - K.bumpTerm c p'‖ ≤ 1 / 12 * dist p p' := by
  have hd : 0 < N.radius c := hc.2
  have hr : 0 < χ * N.radius c / 3 := div_pos (mul_pos hχ hd) (by norm_num)
  have hv : ‖c.1 - K.limitMap (K.pre c)‖ ≤ 2 * ζ * N.radius c := by
    rw [norm_sub_rev]
    exact K.stop_error c hc
  have hφ := d1eattach_abs_bump_sub_le hr (K.pre c) p p'
  have hd0 : 0 ≤ dist p p' := dist_nonneg
  have hB1 : 1 ≤ SmoothCutoff.bumpBound (NeckType.vertical.rank k) :=
    SmoothCutoff.one_le_bumpBound _
  simp only [d1e_VerticalCompletion.bumpTerm]
  rw [← sub_smul, norm_smul, Real.norm_eq_abs]
  set B := SmoothCutoff.bumpBound (NeckType.vertical.rank k) with hB
  have hB0 : B ≠ 0 := (lt_of_lt_of_le one_pos hB1).ne'
  have hχ0 : χ ≠ 0 := hχ.ne'
  have hd0' : N.radius c ≠ 0 := hd.ne'
  have hv0 : 0 ≤ 2 * ζ * N.radius c := (norm_nonneg _).trans hv
  have hφ0 : 0 ≤ 2 * B / (χ * N.radius c / 3) * dist p p' :=
    mul_nonneg (div_nonneg (by linarith) hr.le) hd0
  have h12 : 12 * B * ζ / χ ≤ 1 / 12 := by
    rw [div_le_iff₀ hχ]
    have h1 : 12 * B * ζ ≤ 12 * B * ((144 * B)⁻¹ * χ) :=
      mul_le_mul_of_nonneg_left hζ (by linarith)
    have e : 12 * B * ((144 * B)⁻¹ * χ) = 1 / 12 * χ := by
      field_simp
      ring
    linarith
  calc |SmoothCutoff.parabolicBump (χ * N.radius c / 3) (K.pre c) (p.1, p.2.val) -
        SmoothCutoff.parabolicBump (χ * N.radius c / 3) (K.pre c) (p'.1, p'.2.val)| *
        ‖c.1 - K.limitMap (K.pre c)‖
      ≤ (2 * B / (χ * N.radius c / 3) * dist p p') * (2 * ζ * N.radius c) :=
        mul_le_mul hφ hv (norm_nonneg _) hφ0
    _ = 12 * B * ζ / χ * dist p p' := by
        field_simp
        ring
    _ ≤ 1 / 12 * dist p p' := mul_le_mul_of_nonneg_right h12 hd0

/-- **`Lip_P G ≤ 1/6`**: two parameters see at most two active terms. -/
theorem d1eattach_norm_attachment_sub_le (hχ : 0 < χ)
    (hζ : ζ ≤ (144 * SmoothCutoff.bumpBound (NeckType.vertical.rank k))⁻¹ * χ)
    (p p' : Space (NeckType.vertical.rank k)) :
    ‖K.attachment p - K.attachment p'‖ ≤ 1 / 6 * dist p p' := by
  classical
  obtain ⟨s₁, hs₁, h₁⟩ := d1eattach_exists_active K hχ p
  obtain ⟨s₂, hs₂, h₂⟩ := d1eattach_exists_active K hχ p'
  have e₁ : K.attachment p = ∑ c ∈ s₁ ∪ s₂, K.bumpTerm (c : Space n) p :=
    d1eattach_attachment_eq_sum K fun c hc => h₁ c fun h => hc (Finset.mem_union_left _ h)
  have e₂ : K.attachment p' = ∑ c ∈ s₁ ∪ s₂, K.bumpTerm (c : Space n) p' :=
    d1eattach_attachment_eq_sum K fun c hc => h₂ c fun h => hc (Finset.mem_union_right _ h)
  have hcard : ((s₁ ∪ s₂).card : ℝ) ≤ 2 := by
    have h := Finset.card_union_le s₁ s₂
    have h' : (s₁ ∪ s₂).card ≤ 2 := by omega
    exact_mod_cast h'
  have hd0 : 0 ≤ 1 / 12 * dist p p' := by positivity
  rw [e₁, e₂, ← Finset.sum_sub_distrib]
  calc ‖∑ c ∈ s₁ ∪ s₂, (K.bumpTerm (c : Space n) p - K.bumpTerm (c : Space n) p')‖
      ≤ ∑ c ∈ s₁ ∪ s₂, ‖K.bumpTerm (c : Space n) p - K.bumpTerm (c : Space n) p'‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _c ∈ s₁ ∪ s₂, 1 / 12 * dist p p' :=
        Finset.sum_le_sum fun c _ => d1eattach_norm_bumpTerm_sub_le K hχ hζ c.2 p p'
    _ = ((s₁ ∪ s₂).card : ℝ) * (1 / 12 * dist p p') := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * (1 / 12 * dist p p') := mul_le_mul_of_nonneg_right hcard hd0
    _ = 1 / 6 * dist p p' := by ring

/-- **Exact attachment** at a stop: `G(p_c) = v_c`. -/
theorem d1eattach_attachment_pre (hχ : 0 < χ) {c : Space n} (hc : c ∈ N.stopping) :
    K.attachment (K.pre c) = c.1 - K.limitMap (K.pre c) := by
  have hd : 0 < N.radius c := hc.2
  have hr : 0 < χ * N.radius c / 3 := div_pos (mul_pos hχ hd) (by norm_num)
  have hzero : ∀ c' : N.stopping, c' ≠ ⟨c, hc⟩ →
      K.bumpTerm (c' : Space n) (K.pre c) = 0 := by
    intro c' hne
    refine d1eattach_bumpTerm_eq_zero K hχ c'.2 ?_
    have hne' : c ≠ (c' : Space n) := fun h => hne (Subtype.ext h.symm)
    have h1 := K.ball_disjoint c hc c' c'.2 hne'
    have h2 : 0 ≤ χ * N.radius c := (mul_pos hχ hd).le
    linarith
  unfold d1e_VerticalCompletion.attachment
  rw [tsum_eq_single ⟨c, hc⟩ hzero]
  show SmoothCutoff.parabolicBump (χ * N.radius c / 3) (K.pre c) ((K.pre c).1, (K.pre c).2.val) •
      (c.1 - K.limitMap (K.pre c)) = _
  rw [d1eattach_bump_self hr, one_smul]

/-- `Φ(p_c) = c` for every stop. -/
theorem d1eattach_map_pre (hχ : 0 < χ) {c : Space n} (hc : c ∈ N.stopping) :
    K.map (K.pre c) = c := by
  have h1 : K.spatialMap (K.pre c) = c.1 := by
    simp only [d1e_VerticalCompletion.spatialMap, d1eattach_attachment_pre K hχ hc,
      add_sub_cancel]
  exact Prod.ext h1 (K.pre_time c hc)

/-- At a core preimage every bump vanishes, so `Φ = Φ⁰` there. -/
theorem d1eattach_map_of_core (hχ : 0 < χ) {p : Space (NeckType.vertical.rank k)}
    (hp : timePreservingMap (d1e_projectionLimit N.family K.chart) p ∈ N.core) :
    K.map p = timePreservingMap (d1e_projectionLimit N.family K.chart) p := by
  have hall : ∀ c : N.stopping, c ∉ (∅ : Finset N.stopping) →
      K.bumpTerm (c : Space n) p = 0 :=
    fun c _ => d1eattach_bumpTerm_eq_zero K hχ c.2 (K.core_avoid c c.2 p hp)
  have hG : K.attachment p = 0 := by
    rw [d1eattach_attachment_eq_sum K hall, Finset.sum_empty]
  show (K.limitMap p + K.attachment p, p.2) = _
  rw [hG, add_zero]
  rfl

/-- `|Φ⁰(p_c) - c| ≤ 2 ζ d_c` as parabolic points (same time). -/
theorem d1eattach_dist_limit_pre {c : Space n} (hc : c ∈ N.stopping) :
    dist (timePreservingMap (d1e_projectionLimit N.family K.chart) (K.pre c)) c ≤
      2 * ζ * N.radius c := by
  have e : dist (timePreservingMap (d1e_projectionLimit N.family K.chart) (K.pre c)) c =
      max ‖K.limitMap (K.pre c) - c.1‖ (Real.sqrt |(K.pre c).2.val - c.2.val|) :=
    dist_point (K.limitMap (K.pre c)) c.1 (K.pre c).2.val c.2.val
  have h2 : ‖K.limitMap (K.pre c) - c.1‖ ≤ 2 * ζ * N.radius c := K.stop_error c hc
  rw [e, K.pre_time c hc, sub_self, abs_zero, Real.sqrt_zero]
  exact max_le h2 ((norm_nonneg _).trans h2)

/-- **Compact support of `G`**: the stop parameters are bounded by the lower metric bound of
`Φ⁰`, `centers_subset` and `radius_le`. -/
theorem d1eattach_hasCompactSupport (hχ : 0 < χ)
    (hlow : ∀ p p' : Space (NeckType.vertical.rank k),
      4 / 5 * dist p p' ≤ dist (timePreservingMap (d1e_projectionLimit N.family K.chart) p)
        (timePreservingMap (d1e_projectionLimit N.family K.chart) p')) :
    HasCompactSupport K.attachment := by
  classical
  have hCR : 0 < Cd * R := mul_pos N.parameters.Cd_pos N.parameters.R_pos
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : Space (NeckType.vertical.rank k), p₀ = point 0 0 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 5 / 4 * (2 * |ζ| * (Cd * R) + R +
      dist (timePreservingMap (d1e_projectionLimit N.family K.chart) p₀) q) := ⟨_, rfl⟩
  have hpre : ∀ c ∈ N.stopping, dist (K.pre c) p₀ ≤ M := by
    intro c hc
    have hd : 0 < N.radius c := hc.2
    have hdle : N.radius c ≤ Cd * R := N.radius_le c hc.1
    have hcq : dist c q ≤ R := N.centers_subset hc.1
    have h1 := d1eattach_dist_limit_pre K hc
    have h3 : 2 * ζ * N.radius c ≤ 2 * |ζ| * (Cd * R) := by
      have h4 : ζ * N.radius c ≤ |ζ| * N.radius c :=
        mul_le_mul_of_nonneg_right (le_abs_self ζ) hd.le
      have h5 : |ζ| * N.radius c ≤ |ζ| * (Cd * R) :=
        mul_le_mul_of_nonneg_left hdle (abs_nonneg _)
      linarith
    have h6 := dist_triangle4
      (timePreservingMap (d1e_projectionLimit N.family K.chart) (K.pre c)) c q
      (timePreservingMap (d1e_projectionLimit N.family K.chart) p₀)
    have h7 := hlow (K.pre c) p₀
    rw [dist_comm q] at h6
    rw [hM]
    linarith
  refine HasCompactSupport.intro (isCompact_closedBall p₀ (M + χ * (Cd * R))) fun p hp => ?_
  have hall : ∀ c : N.stopping, c ∉ (∅ : Finset N.stopping) →
      K.bumpTerm (c : Space n) p = 0 := by
    intro c _
    refine d1eattach_bumpTerm_eq_zero K hχ c.2 (not_lt.mp fun hlt => hp ?_)
    rw [Metric.mem_closedBall]
    have h1 := dist_triangle p (K.pre c) p₀
    have h2 : χ * N.radius c ≤ χ * (Cd * R) :=
      mul_le_mul_of_nonneg_left (N.radius_le c c.2.1) hχ.le
    have h3 := hpre c c.2
    linarith
  rw [d1eattach_attachment_eq_sum K hall, Finset.sum_empty]

/-- `Φ` and `Φ⁰` differ only in the spatial coordinate, by `G`. -/
theorem d1eattach_dist_bounds (p p' : Space (NeckType.vertical.rank k)) :
    dist (K.map p) (K.map p') ≤
        dist (timePreservingMap (d1e_projectionLimit N.family K.chart) p)
          (timePreservingMap (d1e_projectionLimit N.family K.chart) p') +
        ‖K.attachment p - K.attachment p'‖ ∧
      dist (timePreservingMap (d1e_projectionLimit N.family K.chart) p)
          (timePreservingMap (d1e_projectionLimit N.family K.chart) p') ≤
        dist (K.map p) (K.map p') + ‖K.attachment p - K.attachment p'‖ := by
  have eM : dist (K.map p) (K.map p') =
      max (dist (K.spatialMap p) (K.spatialMap p')) (dist p.2 p'.2) := Prod.dist_eq
  have eL : dist (timePreservingMap (d1e_projectionLimit N.family K.chart) p)
        (timePreservingMap (d1e_projectionLimit N.family K.chart) p') =
      max (dist (K.limitMap p) (K.limitMap p')) (dist p.2 p'.2) := Prod.dist_eq
  have hsd : K.spatialMap p - K.spatialMap p' =
      (K.limitMap p - K.limitMap p') + (K.attachment p - K.attachment p') := by
    simp only [d1e_VerticalCompletion.spatialMap]
    abel
  have hup : dist (K.spatialMap p) (K.spatialMap p') ≤
      dist (K.limitMap p) (K.limitMap p') + ‖K.attachment p - K.attachment p'‖ := by
    rw [dist_eq_norm, dist_eq_norm, hsd]
    exact norm_add_le _ _
  have hlo : dist (K.limitMap p) (K.limitMap p') ≤
      dist (K.spatialMap p) (K.spatialMap p') + ‖K.attachment p - K.attachment p'‖ := by
    rw [dist_eq_norm, dist_eq_norm]
    have e : K.limitMap p - K.limitMap p' =
        (K.spatialMap p - K.spatialMap p') - (K.attachment p - K.attachment p') := by
      rw [hsd]
      abel
    rw [e]
    exact norm_sub_le _ _
  have he : 0 ≤ ‖K.attachment p - K.attachment p'‖ := norm_nonneg _
  rw [eM, eL]
  constructor
  · exact max_le (hup.trans (add_le_add_left (le_max_left _ _) _))
      ((le_max_right _ _).trans (le_add_of_nonneg_right he))
  · exact max_le (hlo.trans (add_le_add_left (le_max_left _ _) _))
      ((le_max_right _ _).trans (le_add_of_nonneg_right he))

/-- **`Lip_P (F - F₀) ≤ 11/10 + 1/6 + 1 ≤ 3`**. -/
theorem d1eattach_lipschitz_displacement (hχ : 0 < χ)
    (hζ : ζ ≤ (144 * SmoothCutoff.bumpBound (NeckType.vertical.rank k))⁻¹ * χ)
    (hup : ∀ p p' : Space (NeckType.vertical.rank k),
      dist (timePreservingMap (d1e_projectionLimit N.family K.chart) p)
        (timePreservingMap (d1e_projectionLimit N.family K.chart) p') ≤ 11 / 10 * dist p p') :
    LipschitzWith 3 K.displacement := by
  refine LipschitzWith.of_dist_le_mul fun p p' => ?_
  have h3 : ((3 : ℝ≥0) : ℝ) = 3 := by norm_num
  rw [h3, dist_eq_norm]
  have hdd : K.displacement p - K.displacement p' =
      (K.limitMap p - K.limitMap p') + (K.attachment p - K.attachment p') -
        K.chart.isometry (p.1 - p'.1) := by
    simp only [d1e_VerticalCompletion.displacement, d1e_VerticalCompletion.spatialMap,
      d1e_VerticalCompletion.initialMap, map_sub]
    abel
  have eL : dist (timePreservingMap (d1e_projectionLimit N.family K.chart) p)
        (timePreservingMap (d1e_projectionLimit N.family K.chart) p') =
      max (dist (K.limitMap p) (K.limitMap p')) (dist p.2 p'.2) := Prod.dist_eq
  have hL : ‖K.limitMap p - K.limitMap p'‖ ≤ 11 / 10 * dist p p' := by
    rw [← dist_eq_norm]
    exact (le_max_left _ _).trans (eL ▸ hup p p')
  have hG := d1eattach_norm_attachment_sub_le K hχ hζ p p'
  have hU : ‖K.chart.isometry (p.1 - p'.1)‖ ≤ dist p p' := by
    rw [LinearIsometry.norm_map]
    exact d1eattach_norm_fst_le p p'
  have hd0 : 0 ≤ dist p p' := dist_nonneg
  rw [hdd]
  calc ‖(K.limitMap p - K.limitMap p') + (K.attachment p - K.attachment p') -
        K.chart.isometry (p.1 - p'.1)‖
      ≤ ‖(K.limitMap p - K.limitMap p') + (K.attachment p - K.attachment p')‖ +
          ‖K.chart.isometry (p.1 - p'.1)‖ := norm_sub_le _ _
    _ ≤ ‖K.limitMap p - K.limitMap p'‖ + ‖K.attachment p - K.attachment p'‖ +
          ‖K.chart.isometry (p.1 - p'.1)‖ := add_le_add_left (norm_add_le _ _) _
    _ ≤ 3 * dist p p' := by linarith

end Attachment

/-- **Smooth separated attachment** (`d1e_AttachmentStatement`). The margin is `c_A = (144 B)⁻¹`,
`B = SmoothCutoff.bumpBound (k - 2)`. -/
theorem d1e_attachment_proof : d1e_AttachmentStatement := by
  intro n k
  have hB1 : 1 ≤ SmoothCutoff.bumpBound (NeckType.vertical.rank k) :=
    SmoothCutoff.one_le_bumpBound _
  refine ⟨(144 * SmoothCutoff.bumpBound (NeckType.vertical.rank k))⁻¹,
    inv_pos.2 (by linarith), ?_⟩
  intro ι q R c₀ Cd Cs σ δ E κ θ γ N χ ζ hχ hζ K hΦ hcore
  have hG := d1eattach_norm_attachment_sub_le K hχ hζ
  refine ⟨fun p p' => ?_, ?_, ?_, d1eattach_hasCompactSupport K hχ fun p p' => (hΦ p p').1,
    d1eattach_lipschitz_displacement K hχ hζ fun p p' => (hΦ p p').2⟩
  · obtain ⟨h1, h2⟩ := d1eattach_dist_bounds K p p'
    obtain ⟨h3, h4⟩ := hΦ p p'
    have h5 := hG p p'
    have hd0 : 0 ≤ dist p p' := dist_nonneg
    constructor <;> linarith
  · intro z hz
    rcases (N.radius_nonneg z hz).eq_or_lt with h0 | hpos
    · have hzc : z ∈ N.core := ⟨hz, h0.symm⟩
      obtain ⟨p, hp⟩ := hcore z hzc
      refine ⟨p, ?_⟩
      have hp' : timePreservingMap (d1e_projectionLimit N.family K.chart) p ∈ N.core := by
        rw [hp]
        exact hzc
      rw [d1eattach_map_of_core K hχ hp', hp]
    · exact ⟨K.pre z, d1eattach_map_pre K hχ ⟨hz, hpos⟩⟩
  · exact (LipschitzWith.of_dist_le' (K := 1 / 6) fun p p' =>
      (dist_eq_norm _ _).trans_le (hG p p')).continuous

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
