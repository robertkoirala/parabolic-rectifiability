import ParabolicRectifiability.Metric.Measure

/-! # Geometry of robust reservoirs

The ingredients of the reservoir lemma `exists_reservoir_sets_proof`, in reusable form.

* **Robust frames** (`frame_lower_bound`): if each `d_j` has a unit witness `e_j`
  orthogonal to the earlier vectors with `|⟪e_j, d_j⟫| ≥ η R`, and `‖d_l‖ ≤ Λ R`, then
  `‖Σ_l v_l d_l‖ ≥ s R ‖v‖` with the explicit `s = frameConst m η Λ`. This replaces the
  determinant and Gram–Schmidt computation: the coefficient with the last index above
  a geometric threshold dominates. `perturbed_lower_bound` is the matrix perturbation
  step (vertices moved by at most `ε R`).
* **Slab volume** (`parabolicVolume_ball_inter_slab_le'`): a slab `{|⟪e, u⟫ - β| < h}`
  meets `P(x, R)` in volume at most `2^(m+1) h R^(m+1)`. A tube about an affine subspace
  of dimension below `m` lies in such a slab, so this is the only volume bound needed.
* **Heavy cells and selection**: the grid of mesh `R / M` cuts `P(x, R)` into `(2M)^m`
  cells of spatial diameter at most `m R / M`; heavy cells escape every light set
  (`exists_heavy_not_mem`); successive selection (`exists_successive_selection`)
  produces points whose differences carry the frame witnesses.
* **Barycenters** (`norm_integral_spatial_sub_le`): the spatial barycenter of a
  probability measure carried by a set obeys every bound valid on that set.
-/

noncomputable section

open scoped ENNReal

namespace ParabolicRectifiability
namespace Reservoirs

/-! ## Robust frames -/

section Frames

open Finset

/-- Coordinatewise bounds give a Euclidean bound, with the crude constant `m`. -/
theorem norm_le_of_forall_abs_le {m : ℕ} (u : EuclideanSpace ℝ (Fin m)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, |u i| ≤ C) : ‖u‖ ≤ m * C := by
  have hm : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · simp [hm]
    · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith
  have hsq : ‖u‖ ^ 2 ≤ (m * C) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖u i‖ ^ 2 ≤ ∑ _i : Fin m, C ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
      _ = m * C ^ 2 := by simp
      _ ≤ (m * C) ^ 2 := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right hm (sq_nonneg C)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- The ratio `μ = η / (2 (m + 1) (Λ + η))` between successive coefficient thresholds. -/
def frameRatio (m : ℕ) (η Λ : ℝ) : ℝ := η / (2 * (m + 1) * (Λ + η))

/-- The lower singular-value constant `μ ^ m η / (2 (m + 1))` of a robust frame. -/
def frameConst (m : ℕ) (η Λ : ℝ) : ℝ := frameRatio m η Λ ^ m * η / (2 * (m + 1))

variable {m : ℕ} {η Λ : ℝ}

theorem frameRatio_pos (hη : 0 < η) (hΛ : 0 ≤ Λ) : 0 < frameRatio m η Λ := by
  unfold frameRatio; positivity

theorem frameRatio_le_one (hη : 0 < η) (hΛ : 0 ≤ Λ) : frameRatio m η Λ ≤ 1 := by
  unfold frameRatio
  rw [div_le_one (by positivity)]
  have : (1 : ℝ) ≤ m + 1 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  nlinarith

theorem mul_frameRatio_mul_le (hη : 0 < η) (hΛ : 0 ≤ Λ) :
    m * frameRatio m η Λ * Λ ≤ η / 2 := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hD : 0 < 2 * ((m : ℝ) + 1) * (Λ + η) := by positivity
  have key : (m : ℝ) * Λ ≤ ((m : ℝ) + 1) * (Λ + η) := by nlinarith
  unfold frameRatio
  rw [show (m : ℝ) * (η / (2 * (m + 1) * (Λ + η))) * Λ =
      η * (m * Λ) / (2 * (m + 1) * (Λ + η)) by ring, div_le_iff₀ hD]
  nlinarith

theorem frameConst_pos (hη : 0 < η) (hΛ : 0 ≤ Λ) : 0 < frameConst m η Λ := by
  have := frameRatio_pos (m := m) hη hΛ
  unfold frameConst; positivity

/-- **Robust frame.** If every `d_j` has a unit witness orthogonal to the earlier vectors
with `|⟪e_j, d_j⟫| ≥ η R`, and all `‖d_l‖ ≤ Λ R`, then the matrix `[d_0 ⋯ d_(m-1)]` has
lower singular value at least `frameConst m η Λ * R`. -/
theorem frame_lower_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hη : 0 < η) (hΛ : 0 ≤ Λ) (hR : 0 < R)
    (d : Fin m → E) (hd : ∀ l, ‖d l‖ ≤ Λ * R)
    (he : ∀ j, ∃ e : E, ‖e‖ = 1 ∧ (∀ i, i < j → inner ℝ e (d i) = 0) ∧
      η * R ≤ |inner ℝ e (d j)|)
    (v : Fin m → ℝ) :
    frameConst m η Λ * R * ‖WithLp.toLp 2 v‖ ≤ ‖∑ l, v l • d l‖ := by
  rcases isEmpty_or_nonempty (Fin m) with hm | hm
  · have : WithLp.toLp 2 v = 0 := by
      ext i
      exact isEmptyElim i
    rw [this, norm_zero, mul_zero]
    exact norm_nonneg _
  set μ := frameRatio m η Λ with hμ
  have hμ0 : 0 < μ := frameRatio_pos hη hΛ
  have hμ1 : μ ≤ 1 := frameRatio_le_one hη hΛ
  obtain ⟨l₀, -, hl₀⟩ := Finset.exists_max_image univ (fun l => |v l|) univ_nonempty
  set M := |v l₀| with hM
  have hM0 : 0 ≤ M := abs_nonneg _
  -- The last index whose coefficient lies above its geometric threshold.
  set F := univ.filter (fun l : Fin m => μ ^ (l : ℕ) * M ≤ |v l|) with hF
  have hFne : F.Nonempty := ⟨l₀, by
    rw [hF, mem_filter]
    exact ⟨mem_univ _, mul_le_of_le_one_left hM0 (pow_le_one₀ hμ0.le hμ1)⟩⟩
  set j := F.max' hFne with hjdef
  have hj : μ ^ (j : ℕ) * M ≤ |v j| := (mem_filter.mp (F.max'_mem hFne)).2
  have htail : ∀ l, j < l → |v l| ≤ μ ^ ((j : ℕ) + 1) * M := by
    intro l hl
    have hlF : l ∉ F := fun h => absurd (F.le_max' l h) (not_le.mpr hl)
    have hlt : |v l| < μ ^ (l : ℕ) * M :=
      not_le.mp fun h => hlF (mem_filter.mpr ⟨mem_univ _, h⟩)
    have hjl : (j : ℕ) + 1 ≤ l := Nat.succ_le_of_lt (Fin.lt_def.mp hl)
    exact hlt.le.trans (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hμ0.le hμ1 hjl) hM0)
  obtain ⟨e, he1, he0, hej⟩ := he j
  -- Split the combination at `j`.
  set w : Fin m → ℝ := fun l => if l ≤ j then v l else 0 with hw
  set t : Fin m → ℝ := fun l => if l ≤ j then 0 else v l with ht
  have hsplit : ∑ l, v l • d l = ∑ l, w l • d l + ∑ l, t l • d l := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h : l ≤ j <;> simp [w, t, h]
  have hlow : |v j| * (η * R) ≤ ‖∑ l, w l • d l‖ := by
    have hinner : inner ℝ e (∑ l, w l • d l) = v j * inner ℝ e (d j) := by
      rw [inner_sum, Finset.sum_eq_single j]
      · simp [w, real_inner_smul_right]
      · intro l _ hlj
        rcases lt_or_gt_of_ne hlj with h | h
        · simp [real_inner_smul_right, he0 l h]
        · simp [w, not_le.mpr h]
      · simp
    calc |v j| * (η * R) ≤ |v j| * |inner ℝ e (d j)| :=
          mul_le_mul_of_nonneg_left hej (abs_nonneg _)
      _ = |inner ℝ e (∑ l, w l • d l)| := by rw [hinner, abs_mul]
      _ ≤ ‖e‖ * ‖∑ l, w l • d l‖ := abs_real_inner_le_norm _ _
      _ = ‖∑ l, w l • d l‖ := by rw [he1, one_mul]
  have hup : ‖∑ l, t l • d l‖ ≤ m * (μ ^ ((j : ℕ) + 1) * M * (Λ * R)) := by
    calc ‖∑ l, t l • d l‖ ≤ ∑ l, ‖t l • d l‖ := norm_sum_le _ _
      _ ≤ ∑ _l : Fin m, μ ^ ((j : ℕ) + 1) * M * (Λ * R) := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [norm_smul, Real.norm_eq_abs]
          by_cases h : l ≤ j
          · simp only [t, h, ite_true, abs_zero, zero_mul]
            positivity
          · simp only [t, h, ite_false]
            exact mul_le_mul (htail l (not_le.mp h)) (hd l) (norm_nonneg _) (by positivity)
      _ = m * (μ ^ ((j : ℕ) + 1) * M * (Λ * R)) := by simp
  have hvnorm : ‖WithLp.toLp 2 v‖ ≤ m * M :=
    norm_le_of_forall_abs_le _ hM0 fun i => by simpa using hl₀ i (mem_univ i)
  -- Assemble the inequalities.
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : μ ^ (j : ℕ) * M * (η * R) ≤ |v j| * (η * R) :=
    mul_le_mul_of_nonneg_right hj (by positivity)
  have h2 : (m : ℝ) * (μ ^ ((j : ℕ) + 1) * M * (Λ * R)) ≤ μ ^ (j : ℕ) * M * R * (η / 2) := by
    have := mul_frameRatio_mul_le (m := m) hη hΛ
    calc (m : ℝ) * (μ ^ ((j : ℕ) + 1) * M * (Λ * R))
        = (μ ^ (j : ℕ) * M * R) * (m * μ * Λ) := by ring
      _ ≤ (μ ^ (j : ℕ) * M * R) * (η / 2) := mul_le_mul_of_nonneg_left this (by positivity)
  have h3 : frameConst m η Λ * R * ‖WithLp.toLp 2 v‖ ≤ μ ^ (j : ℕ) * M * R * (η / 2) := by
    have hjm : (j : ℕ) ≤ m := j.isLt.le
    have hpow : μ ^ m ≤ μ ^ (j : ℕ) := pow_le_pow_of_le_one hμ0.le hμ1 hjm
    have hfc : 0 ≤ frameConst m η Λ := (frameConst_pos hη hΛ).le
    calc frameConst m η Λ * R * ‖WithLp.toLp 2 v‖
        ≤ frameConst m η Λ * R * (((m : ℝ) + 1) * M) := by
          refine mul_le_mul_of_nonneg_left (hvnorm.trans ?_) (by positivity)
          nlinarith
      _ = μ ^ m * M * R * (η / 2) := by
          unfold frameConst
          rw [← hμ]
          field_simp
      _ ≤ μ ^ (j : ℕ) * M * R * (η / 2) := by gcongr
  have htri : ‖∑ l, w l • d l‖ ≤ ‖∑ l, v l • d l‖ + ‖∑ l, t l • d l‖ := by
    calc ‖∑ l, w l • d l‖ = ‖(∑ l, w l • d l + ∑ l, t l • d l) - ∑ l, t l • d l‖ := by
          rw [add_sub_cancel_right]
      _ ≤ _ := by rw [← hsplit]; exact norm_sub_le _ _
  nlinarith

/-- **Matrix perturbation.** Moving every vertex of a frame with lower bound `s R` by at
most `ε R` leaves the lower bound `(s - 2 m ε) R`. -/
theorem perturbed_lower_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {s ε R : ℝ} (q b : Fin (m + 1) → E) (hb : ∀ l, ‖b l - q l‖ ≤ ε * R)
    (hq : ∀ v : Fin m → ℝ, s * R * ‖WithLp.toLp 2 v‖ ≤ ‖∑ l, v l • (q l.succ - q 0)‖)
    (v : Fin m → ℝ) :
    (s - 2 * m * ε) * R * ‖WithLp.toLp 2 v‖ ≤ ‖∑ l, v l • (b l.succ - b 0)‖ := by
  have hεR : 0 ≤ ε * R := (norm_nonneg _).trans (hb 0)
  have hv : ∀ l, |v l| ≤ ‖WithLp.toLp 2 v‖ := fun l => by
    simpa using PiLp.norm_apply_le (WithLp.toLp 2 v) l
  set B := ∑ l, v l • ((b l.succ - q l.succ) - (b 0 - q 0)) with hB
  have herr : ‖B‖ ≤ m * (‖WithLp.toLp 2 v‖ * (2 * (ε * R))) := by
    calc ‖B‖ ≤ ∑ l, ‖v l • ((b l.succ - q l.succ) - (b 0 - q 0))‖ := norm_sum_le _ _
      _ ≤ ∑ _l : Fin m, ‖WithLp.toLp 2 v‖ * (2 * (ε * R)) := by
        refine sum_le_sum fun l _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        refine mul_le_mul (hv l) ?_ (norm_nonneg _) (norm_nonneg _)
        calc ‖(b l.succ - q l.succ) - (b 0 - q 0)‖
            ≤ ‖b l.succ - q l.succ‖ + ‖b 0 - q 0‖ := norm_sub_le _ _
          _ ≤ ε * R + ε * R := add_le_add (hb _) (hb _)
          _ = 2 * (ε * R) := by ring
      _ = m * (‖WithLp.toLp 2 v‖ * (2 * (ε * R))) := by simp
  have hsum : ∑ l, v l • (b l.succ - b 0) = ∑ l, v l • (q l.succ - q 0) + B := by
    rw [hB, ← sum_add_distrib]
    refine sum_congr rfl fun l _ => ?_
    rw [← smul_add]
    congr 1
    abel
  have htri : ‖∑ l, v l • (q l.succ - q 0)‖ ≤ ‖∑ l, v l • (b l.succ - b 0)‖ + ‖B‖ := by
    calc ‖∑ l, v l • (q l.succ - q 0)‖ = ‖(∑ l, v l • (q l.succ - q 0) + B) - B‖ := by
          rw [add_sub_cancel_right]
      _ ≤ _ := by rw [← hsum]; exact norm_sub_le _ _
  have := hq v
  have hexp : (s - 2 * m * ε) * R * ‖WithLp.toLp 2 v‖ =
      s * R * ‖WithLp.toLp 2 v‖ - m * (‖WithLp.toLp 2 v‖ * (2 * (ε * R))) := by ring
  linarith

end Frames

open MeasureTheory Set

/-! ## Slab volume -/

/-- **Spatial slab volume.** -/
theorem volume_ball_inter_slab_le {m : ℕ} (x e : Spatial (m + 1)) (he : ‖e‖ = 1)
    (β h R : ℝ) :
    volume {u : Spatial (m + 1) | ‖u - x‖ < R ∧ |inner ℝ e u - β| < h} ≤
      ENNReal.ofReal (2 * h) * ENNReal.ofReal (2 * R) ^ m := by
  classical
  set e₀ : Spatial (m + 1) := EuclideanSpace.single 0 1 with he₀def
  have he₀ : ‖e₀‖ = 1 := by simp [e₀]
  set ψ : Spatial (m + 1) ≃ₗᵢ[ℝ] Spatial (m + 1) := Submodule.reflection (ℝ ∙ (e - e₀))ᗮ with hψ
  have hψe : ψ e = e₀ := Submodule.reflection_sub (he.trans he₀.symm)
  have hcoord : ∀ u, inner ℝ e u = (ψ u) 0 := by
    intro u
    rw [← ψ.inner_map_map e u, hψe, he₀def, EuclideanSpace.inner_single_left]
    simp
  set y : Spatial (m + 1) := ψ x with hy
  set I : Fin (m + 1) → Set ℝ :=
    Fin.cons (Ioo (β - h) (β + h)) (fun i => Ioo (y i.succ - R) (y i.succ + R)) with hI
  have hImeas : ∀ i, MeasurableSet (I i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [I, Fin.cons_zero]; exact measurableSet_Ioo
    · simp only [I, Fin.cons_succ]; exact measurableSet_Ioo
  have hbox : MeasurableSet (WithLp.ofLp ⁻¹' Set.pi univ I : Set (Spatial (m + 1))) :=
    (MeasurableSet.univ_pi hImeas).preimage (PiLp.volume_preserving_ofLp (Fin (m + 1))).measurable
  have hsub : {u : Spatial (m + 1) | ‖u - x‖ < R ∧ |inner ℝ e u - β| < h} ⊆
      ψ ⁻¹' (WithLp.ofLp ⁻¹' Set.pi univ I) := by
    rintro u ⟨hux, hue⟩
    simp only [mem_preimage, mem_pi, mem_univ, true_implies]
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [I, Fin.cons_zero, mem_Ioo]
      rw [hcoord] at hue
      have := abs_lt.mp hue
      change β - h < (ψ u) 0 ∧ (ψ u) 0 < β + h
      constructor <;> linarith [this.1, this.2]
    · simp only [I, Fin.cons_succ, mem_Ioo]
      have hlt : |(ψ u) i.succ - y i.succ| < R := by
        calc |(ψ u) i.succ - y i.succ| = ‖(ψ u - ψ x) i.succ‖ := by
              rw [hy, PiLp.sub_apply, Real.norm_eq_abs]
          _ ≤ ‖ψ u - ψ x‖ := PiLp.norm_apply_le _ _
          _ = ‖u - x‖ := by rw [← map_sub, LinearIsometryEquiv.norm_map]
          _ < R := hux
      have := abs_lt.mp hlt
      change y i.succ - R < (ψ u) i.succ ∧ (ψ u) i.succ < y i.succ + R
      constructor <;> linarith [this.1, this.2]
  have hlen : ∀ a r : ℝ, a + r - (a - r) = 2 * r := fun a r => by ring
  calc volume {u : Spatial (m + 1) | ‖u - x‖ < R ∧ |inner ℝ e u - β| < h}
      ≤ volume (ψ ⁻¹' (WithLp.ofLp ⁻¹' Set.pi univ I)) := measure_mono hsub
    _ = volume (WithLp.ofLp ⁻¹' Set.pi univ I : Set (Spatial (m + 1))) :=
        ψ.measurePreserving.measure_preimage hbox.nullMeasurableSet
    _ = volume (Set.pi univ I) :=
        (PiLp.volume_preserving_ofLp (Fin (m + 1))).measure_preimage
          (MeasurableSet.univ_pi hImeas).nullMeasurableSet
    _ = ∏ i, volume (I i) := volume_pi_pi I
    _ = volume (I 0) * ∏ i : Fin m, volume (I i.succ) := Fin.prod_univ_succ _
    _ = ENNReal.ofReal (2 * h) * ENNReal.ofReal (2 * R) ^ m := by
        simp only [I, Fin.cons_zero, Fin.cons_succ, Real.volume_Ioo, hlen, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin]

/-- **Parabolic slab volume.** A spatial slab of half-width `h` meets `P(x, R)` in
parabolic volume at most `2h (2R)^(m-1) · 2R²` (`m ≥ 1`). -/
theorem parabolicVolume_ball_inter_slab_le {m : ℕ} (x : Space (m + 1)) {R : ℝ} (hR : 0 < R)
    (e : Spatial (m + 1)) (he : ‖e‖ = 1) (β h : ℝ) :
    parabolicVolume (m + 1) (Metric.ball x R ∩ {z | |inner ℝ e z.1 - β| < h}) ≤
      ENNReal.ofReal (2 * h) * ENNReal.ofReal (2 * R) ^ m * ENNReal.ofReal (2 * R ^ 2) := by
  rw [parabolicVolume_apply, coordinateVolume_eq_volume, preimage_inter,
    coordinates_symm_preimage_ball x R hR]
  have hslab : (coordinatesMeasurableEquiv (m + 1)).symm ⁻¹' {z : Space (m + 1) |
      |inner ℝ e z.1 - β| < h} = {y : Coordinates (m + 1) | |inner ℝ e y.1 - β| < h} := by
    ext y
    simp [coordinatesMeasurableEquiv_symm_apply, point]
  rw [hslab]
  calc volume ((Metric.ball x.1 R ×ˢ Ioo (x.2.val - R ^ 2) (x.2.val + R ^ 2)) ∩
        {y : Coordinates (m + 1) | |inner ℝ e y.1 - β| < h})
      ≤ volume ({u : Spatial (m + 1) | ‖u - x.1‖ < R ∧ |inner ℝ e u - β| < h} ×ˢ
          Ioo (x.2.val - R ^ 2) (x.2.val + R ^ 2)) := by
        refine measure_mono ?_
        rintro ⟨u, t⟩ ⟨⟨hu, ht⟩, hs⟩
        exact ⟨⟨by simpa [dist_eq_norm] using hu, hs⟩, ht⟩
    _ = volume {u : Spatial (m + 1) | ‖u - x.1‖ < R ∧ |inner ℝ e u - β| < h} *
          volume (Ioo (x.2.val - R ^ 2) (x.2.val + R ^ 2)) := by
        rw [Measure.volume_eq_prod, Measure.prod_prod]
    _ ≤ ENNReal.ofReal (2 * h) * ENNReal.ofReal (2 * R) ^ m * ENNReal.ofReal (2 * R ^ 2) := by
        rw [Real.volume_Ioo, show x.2.val + R ^ 2 - (x.2.val - R ^ 2) = 2 * R ^ 2 by ring]
        gcongr
        exact volume_ball_inter_slab_le x.1 e he β h R

/-- The parabolic slab bound in single-power form, for every `m` (at `m = 0` there is no
unit spatial vector). -/
theorem parabolicVolume_ball_inter_slab_le' {m : ℕ} (x : Space m) {R : ℝ} (hR : 0 < R)
    (e : Spatial m) (he : ‖e‖ = 1) (β : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    parabolicVolume m (Metric.ball x R ∩ {z | |inner ℝ e z.1 - β| < h}) ≤
      ENNReal.ofReal (2 ^ (m + 1) * h * R ^ (m + 1)) := by
  cases m with
  | zero =>
    exfalso
    simp [EuclideanSpace.norm_eq] at he
  | succ m =>
    refine (parabolicVolume_ball_inter_slab_le x hR e he β h).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring

/-! ## The spatial grid -/

/-- The grid index `⌊M (z_i - x_i) / R⌋` of `z` at mesh `R / M` relative to `x`. -/
def gridIndex {m : ℕ} (M : ℕ) (x : Space m) (R : ℝ) (z : Space m) : Fin m → ℤ :=
  fun i => ⌊(M : ℝ) * (z.1 i - x.1 i) / R⌋

/-- The indices `[-M, M)^m` of the grid cells of `P(x, R)`. -/
def gridIndices (m M : ℕ) : Finset (Fin m → ℤ) :=
  Fintype.piFinset fun _ => Finset.Ico (-(M : ℤ)) M

/-- The grid cell with index `g` inside `P(x, R)`. -/
def gridCell {m : ℕ} (M : ℕ) (x : Space m) (R : ℝ) (g : Fin m → ℤ) : Set (Space m) :=
  Metric.ball x R ∩ {z | gridIndex M x R z = g}

theorem card_gridIndices (m M : ℕ) : (gridIndices m M).card = (2 * M) ^ m := by
  rw [gridIndices, Fintype.card_piFinset]
  simp only [Int.card_Ico, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

theorem measurable_gridIndex {m : ℕ} (M : ℕ) (x : Space m) (R : ℝ) :
    Measurable (gridIndex M x R) := by
  refine Measurable.of_eval fun i => ?_
  have hc : Measurable fun z : Space m => z.1 i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable.comp measurable_spatial
  exact ((measurable_const.mul (hc.sub measurable_const)).div_const R).floor

theorem measurableSet_gridCell {m : ℕ} (M : ℕ) (x : Space m) (R : ℝ) (g : Fin m → ℤ) :
    MeasurableSet (gridCell M x R g) :=
  Metric.isOpen_ball.measurableSet.inter (measurable_gridIndex M x R (measurableSet_singleton g))

theorem gridCell_subset_ball {m : ℕ} (M : ℕ) (x : Space m) (R : ℝ) (g : Fin m → ℤ) :
    gridCell M x R g ⊆ Metric.ball x R :=
  inter_subset_left

theorem norm_spatial_sub_lt_of_mem_ball {m : ℕ} {x z : Space m} {R : ℝ}
    (hz : z ∈ Metric.ball x R) : ‖z.1 - x.1‖ < R := by
  have : dist z.1 x.1 ≤ dist z x := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  rw [← dist_eq_norm]
  exact this.trans_lt hz

theorem gridIndex_mem {m M : ℕ} (hM : 0 < M) {x z : Space m} {R : ℝ} (hR : 0 < R)
    (hz : z ∈ Metric.ball x R) : gridIndex M x R z ∈ gridIndices m M := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hzx := norm_spatial_sub_lt_of_mem_ball hz
  refine Fintype.mem_piFinset.mpr fun i => Finset.mem_Ico.mpr ⟨?_, ?_⟩
  all_goals
    have hi : |z.1 i - x.1 i| < R := by
      calc |z.1 i - x.1 i| = ‖(z.1 - x.1) i‖ := by rw [PiLp.sub_apply, Real.norm_eq_abs]
        _ ≤ ‖z.1 - x.1‖ := PiLp.norm_apply_le _ _
        _ < R := hzx
    obtain ⟨hi1, hi2⟩ := abs_lt.mp hi
  · refine Int.le_floor.mpr ?_
    rw [le_div_iff₀ hR]
    push_cast
    nlinarith
  · refine Int.floor_lt.mpr ?_
    rw [div_lt_iff₀ hR]
    push_cast
    nlinarith

theorem mem_gridCell_of_mem_ball {m M : ℕ} {x z : Space m} {R : ℝ}
    (hz : z ∈ Metric.ball x R) : z ∈ gridCell M x R (gridIndex M x R z) :=
  ⟨hz, rfl⟩

/-- Points of one grid cell are within `m R / M` in space. -/
theorem norm_sub_le_of_mem_gridCell {m M : ℕ} (hM : 0 < M) {x : Space m} {R : ℝ} (hR : 0 < R)
    {g : Fin m → ℤ} {z z' : Space m} (hz : z ∈ gridCell M x R g)
    (hz' : z' ∈ gridCell M x R g) : ‖z.1 - z'.1‖ ≤ m * (R / M) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  refine norm_le_of_forall_abs_le _ (by positivity) fun i => ?_
  have heq : ⌊(M : ℝ) * (z.1 i - x.1 i) / R⌋ = ⌊(M : ℝ) * (z'.1 i - x.1 i) / R⌋ := by
    have h1 := congrFun hz.2 i
    have h2 := congrFun hz'.2 i
    simp only [gridIndex] at h1 h2
    rw [h1, h2]
  have hlt := Int.abs_sub_lt_one_of_floor_eq_floor heq
  rw [show (M : ℝ) * (z.1 i - x.1 i) / R - (M : ℝ) * (z'.1 i - x.1 i) / R =
      (M / R) * (z.1 i - z'.1 i) by ring, abs_mul, abs_of_pos (by positivity)] at hlt
  rw [PiLp.sub_apply]
  calc |z.1 i - z'.1 i| = R / M * (M / R * |z.1 i - z'.1 i|) := by
        rw [← mul_assoc, div_mul_div_comm, mul_comm R (M : ℝ), div_self (by positivity), one_mul]
    _ ≤ R / M * 1 := mul_le_mul_of_nonneg_left hlt.le (by positivity)
    _ = R / M := mul_one _

/-! ## Heavy cells -/

/-- **Heavy cells escape a light set.** If `B` is covered by the cells `C g`, `g ∈ s`,
has mass at least `a > 0`, and `T` carries less than `a / 2` of `B`, then some cell of
mass at least `a / (2 #s)` has a point outside `T`. -/
theorem exists_heavy_not_mem {X G : Type*} [MeasurableSpace X] (σ : Measure X)
    (s : Finset G) (C : G → Set X) (B T : Set X) (hcover : B ⊆ ⋃ g ∈ s, C g) {a : ℝ}
    (ha : 0 < a) (hB : ENNReal.ofReal a ≤ σ B) (hT : σ (B ∩ T) < ENNReal.ofReal (a / 2)) :
    ∃ g ∈ s, ENNReal.ofReal (a / (2 * s.card)) ≤ σ (C g) ∧ ∃ z ∈ C g, z ∉ T := by
  classical
  by_contra hcon'
  have hcon : ∀ g ∈ s, ENNReal.ofReal (a / (2 * s.card)) ≤ σ (C g) → ∀ z ∈ C g, z ∈ T :=
    fun g hg hh z hz => by_contra fun hzT => hcon' ⟨g, hg, hh, z, hz, hzT⟩
  set s' := s.filter (fun g => σ (C g) < ENNReal.ofReal (a / (2 * s.card))) with hs'
  have hsub : B ⊆ (B ∩ T) ∪ ⋃ g ∈ s', C g := by
    intro z hz
    obtain ⟨g, hg, hzg⟩ : ∃ g ∈ s, z ∈ C g := by simpa using hcover hz
    by_cases hheavy : ENNReal.ofReal (a / (2 * s.card)) ≤ σ (C g)
    · exact Or.inl ⟨hz, hcon g hg hheavy z hzg⟩
    · exact Or.inr (mem_iUnion₂.mpr ⟨g, Finset.mem_filter.mpr ⟨hg, not_le.mp hheavy⟩, hzg⟩)
  have hsum : ∑ g ∈ s', σ (C g) ≤ ENNReal.ofReal (a / 2) := by
    calc ∑ g ∈ s', σ (C g) ≤ ∑ _g ∈ s', ENNReal.ofReal (a / (2 * s.card)) :=
          Finset.sum_le_sum fun g hg => (Finset.mem_filter.mp hg).2.le
      _ ≤ ∑ _g ∈ s, ENNReal.ofReal (a / (2 * s.card)) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ ≤ ENNReal.ofReal (a / 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          rcases Nat.eq_zero_or_pos s.card with h0 | hpos
          · simp [h0]
          · rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
            have : (s.card : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
            field_simp
  have hlt : σ B < ENNReal.ofReal a := by
    calc σ B ≤ σ (B ∩ T) + σ (⋃ g ∈ s', C g) := (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ σ (B ∩ T) + ∑ g ∈ s', σ (C g) := by gcongr; exact measure_biUnion_finset_le _ _
      _ < ENNReal.ofReal (a / 2) + ENNReal.ofReal (a / 2) :=
          ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum) hT hsum
      _ = ENNReal.ofReal a := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  exact absurd hB (not_le.mpr hlt)

/-! ## Successive selection -/

/-- **Tube-avoiding selection.** If some point is admissible, and every slab
`{|⟪e, q - q₀⟫| < η}` about an affine hyperplane misses an admissible point, then there
are admissible `q_0, …, q_m` whose differences `q_j - q_0` have unit witnesses `e_j`
orthogonal to the earlier differences with `|⟪e_j, q_j - q_0⟫| ≥ η`. -/
theorem exists_successive_selection {m : ℕ} (P : Spatial m → Prop) {η : ℝ}
    (hP : ∃ q, P q)
    (hslab : ∀ e : Spatial m, ‖e‖ = 1 → ∀ q₀ : Spatial m,
      ∃ q, P q ∧ η ≤ |inner ℝ e (q - q₀)|) :
    ∃ q : Fin (m + 1) → Spatial m, (∀ l, P (q l)) ∧
      ∀ j : Fin m, ∃ e : Spatial m, ‖e‖ = 1 ∧
        (∀ i : Fin m, i < j → inner ℝ e (q i.succ - q 0) = 0) ∧
        η ≤ |inner ℝ e (q j.succ - q 0)| := by
  have key : ∀ j : ℕ, j ≤ m → ∃ q : ℕ → Spatial m, (∀ l ≤ j, P (q l)) ∧
      ∀ l, 1 ≤ l → l ≤ j → ∃ e : Spatial m, ‖e‖ = 1 ∧
        (∀ i, 1 ≤ i → i < l → inner ℝ e (q i - q 0) = 0) ∧
        η ≤ |inner ℝ e (q l - q 0)| := by
    intro j
    induction j with
    | zero =>
      intro _
      obtain ⟨q₀, hq₀⟩ := hP
      exact ⟨fun _ => q₀, fun _ _ => hq₀, fun l h1 h2 => absurd (h1.trans h2) (by norm_num)⟩
    | succ j ih =>
      intro hj
      obtain ⟨q, hqP, hqe⟩ := ih (Nat.le_of_succ_le hj)
      -- The span of the first `j` differences is a proper subspace.
      set b : Fin j → Spatial m := fun i => q ((i : ℕ) + 1) - q 0 with hb
      set V : Submodule ℝ (Spatial m) := Submodule.span ℝ (Set.range b) with hVdef
      have hV : V ≠ ⊤ := by
        intro hVtop
        have h1 : Module.finrank ℝ V ≤ j := (finrank_range_le_card b).trans (by simp)
        rw [hVtop, finrank_top, finrank_euclideanSpace_fin] at h1
        omega
      have hVperp : Vᗮ ≠ ⊥ := fun h => hV (Submodule.orthogonal_eq_bot_iff.mp h)
      obtain ⟨e', he'V, he'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVperp
      set e : Spatial m := ‖e'‖⁻¹ • e' with he
      have he1 : ‖e‖ = 1 := by
        rw [he, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr he'0)]
      have heV : e ∈ Vᗮ := Vᗮ.smul_mem _ he'V
      obtain ⟨q', hq'P, hq'⟩ := hslab e he1 (q 0)
      have h0 : Function.update q (j + 1) q' 0 = q 0 := Function.update_of_ne (by omega) _ _
      refine ⟨Function.update q (j + 1) q', fun l hl => ?_, fun l h1 hl => ?_⟩
      · rcases eq_or_ne l (j + 1) with rfl | hne
        · rw [Function.update_self]; exact hq'P
        · rw [Function.update_of_ne hne]; exact hqP l (by omega)
      · rcases eq_or_ne l (j + 1) with rfl | hne
        · refine ⟨e, he1, fun i hi1 hi2 => ?_, ?_⟩
          · rw [Function.update_of_ne (by omega : i ≠ j + 1), h0]
            have hmem : q i - q 0 ∈ V := by
              have : q i - q 0 = b ⟨i - 1, by omega⟩ := by
                simp only [hb]
                rw [Nat.sub_add_cancel hi1]
              rw [this]
              exact Submodule.subset_span (Set.mem_range_self _)
            exact Submodule.inner_left_of_mem_orthogonal hmem heV
          · rw [Function.update_self, h0]; exact hq'
        · obtain ⟨e₁, he₁, he₁0, he₁l⟩ := hqe l h1 (by omega)
          refine ⟨e₁, he₁, fun i hi1 hi2 => ?_, ?_⟩
          · rw [Function.update_of_ne (by omega : i ≠ j + 1), h0]
            exact he₁0 i hi1 hi2
          · rw [Function.update_of_ne hne, h0]
            exact he₁l
  obtain ⟨q, hqP, hqe⟩ := key m le_rfl
  refine ⟨fun l => q l, fun l => hqP l (Nat.lt_succ_iff.mp l.isLt), fun j => ?_⟩
  have hjm := j.isLt
  obtain ⟨e, he1, he0, hej⟩ := hqe ((j : ℕ) + 1) (by omega) (by omega)
  refine ⟨e, he1, fun i hi => ?_, ?_⟩
  · simp only [Fin.val_succ, Fin.val_zero]
    exact he0 ((i : ℕ) + 1) (by omega) (by have := Fin.lt_def.mp hi; omega)
  · simpa only [Fin.val_succ, Fin.val_zero] using hej

/-! ## Barycenters -/

/-- The spatial barycenter of a probability measure carried by `S` lies within any
bound `C` on `‖z.1 - q‖` over `S`. -/
theorem norm_integral_spatial_sub_le {m : ℕ} (ρ : Measure (Space m)) [IsProbabilityMeasure ρ]
    (S : Set (Space m)) (hS : ρ Sᶜ = 0) (q : Spatial m) {C : ℝ}
    (hC : ∀ z ∈ S, ‖z.1 - q‖ ≤ C) : ‖(∫ z, z.1 ∂ρ) - q‖ ≤ C := by
  have hS' : ∀ᵐ z ∂ρ, z ∈ S := by
    rw [ae_iff]
    exact hS
  have hae : ∀ᵐ z ∂ρ, ‖z.1 - q‖ ≤ C := by
    filter_upwards [hS'] with z hz using hC z hz
  have hmeas : AEStronglyMeasurable (fun z : Space m => z.1 - q) ρ :=
    (measurable_spatial.sub measurable_const).aestronglyMeasurable
  have hint : Integrable (fun z : Space m => z.1 - q) ρ := Integrable.of_bound hmeas C hae
  have hint1 : Integrable (fun z : Space m => z.1) ρ := by
    exact (hint.add (integrable_const q)).congr (ae_of_all _ fun z => by simp)
  have heq : (∫ z, z.1 ∂ρ) - q = ∫ z, (z.1 - q) ∂ρ := by
    rw [integral_sub hint1 (integrable_const q)]
    simp
  rw [heq]
  simpa using norm_integral_le_of_norm_le_const hae

end Reservoirs
end ParabolicRectifiability
