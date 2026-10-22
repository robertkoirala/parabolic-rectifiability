import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy

/-! # The initial tube and the artificial root

Proof of `d1c_rootThinness_proof : PartitionEnergy.PointToFitStatement → RootThinnessStatement`
(implication form over the point-to-fit statement).

Constants: `Λ₀ = 4`, `B = 13`, and for a tolerance `η > 0`
`b₀ = min(1, (η/4)^{k+2}) / (A (Λ/2)^{k+2})`.

Route. The root `Q_*` has centre `q ∈ S` and `S ⊆ supp μ ∩ P(q, 2ℓ_*)`; the root forest puts
`S` within `5R` of `a` and `ℓ_* ≤ R`, so `P(q, 8ℓ_*) ⊆ P(a, 13R)`. The prescribed root model
`Π_* = 𝒢.model 𝒢.root` has `fit μ Π_* q (4ℓ_*) ≤ fit μ Π_* q (Λℓ_*) ≤ (Λℓ_*)^{k+2} b`
(`Λ ≥ 4`; the root term of the chain budget), i.e. `e (2ℓ_*)^{k+2}` with `e = (Λ/2)^{k+2} b`.
Point-to-fit at centre `q`, radius `2ℓ_*` gives `d_P(z, Π_*) ≤ 4 (A e)^{1/(k+2)} ℓ_* ≤ η ℓ_*`
on `S`, hence on `closure S` (continuity of `infDist`). The model set is
`T.lowerModelSet L_* τ_*`, so the spatial distance to `L_*` and (horizontally) `√|t - τ_*|` are
at most `d_P(z, Π_*)`. The artificial root `(π_{L_*} x_q, τ_*)` (horizontal) or
`(π_{L_*} x_q, t_q)` (vertical) is then within `η ℓ_*` of `q`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

section

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

/-- The coefficient-ball fit of a member's own model is at most `(Λ ℓ_Q)^{k+2} b`. -/
theorem d1crthin_fit_le_budget (𝒢 : GoodRegion P μ k Λ b) (Q : ℕ × Space n)
    (hQ : Q ∈ 𝒢.members) (hpos : 0 < Λ * P.scale Q.1) :
    fit μ (𝒢.model Q) Q.2 (Λ * P.scale Q.1) ≤
      ENNReal.ofReal (Λ * P.scale Q.1) ^ (k + 2) * ENNReal.ofReal b := by
  have hbelow : P.IsBelow Q Q := ⟨(𝒢.below_root Q hQ).1, le_rfl, subset_rfl⟩
  have hcoeff : P.modelCoeff μ Λ (𝒢.model Q) Q ≤ ENNReal.ofReal b := by
    refine le_trans ?_ (𝒢.budget Q hQ)
    exact ENNReal.le_tsum
      (f := fun Q' : {Q' : ℕ × Space n // Q' ∈ 𝒢.members ∧ P.IsBelow Q Q'} =>
        P.modelCoeff μ Λ (𝒢.model Q'.1) Q'.1) ⟨Q, hQ, hbelow⟩
  have hx0 : ENNReal.ofReal (Λ * P.scale Q.1) ≠ 0 := (ENNReal.ofReal_pos.mpr hpos).ne'
  have hxt : ENNReal.ofReal (Λ * P.scale Q.1) ≠ ⊤ := ENNReal.ofReal_ne_top
  have heq : fit μ (𝒢.model Q) Q.2 (Λ * P.scale Q.1) =
      ENNReal.ofReal (Λ * P.scale Q.1) ^ (k + 2) * P.modelCoeff μ Λ (𝒢.model Q) Q := by
    rw [DirectPartition.modelCoeff, ← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel hx0 hxt,
      one_pow, one_mul]
  rw [heq]
  gcongr

/-- `ℓ_* ≤ ℓ₀`. -/
theorem d1crthin_rootScale_le (𝒢 : GoodRegion P μ k Λ b) : 𝒢.rootScale ≤ ℓ₀ := by
  unfold GoodRegion.rootScale DirectPartition.scale coherentScale
  exact div_le_self P.scale_pos.le (one_le_pow₀ (by norm_num))

/-- A cell lies in the partitioned set. -/
theorem d1crthin_cell_subset (P : DirectPartition E ℓ₀) (Q : ℕ × Space n) (hQ : P.IsCell Q) :
    P.cellOf Q ⊆ E := by
  intro x hx
  rw [← P.cell_cover Q.1]
  exact Set.mem_biUnion hQ hx

/-- The root centre `q` lies in the root cell. -/
theorem d1crthin_root_mem (𝒢 : GoodRegion P μ k Λ b) : 𝒢.root.2 ∈ 𝒢.rootCell := by
  have hc : 𝒢.root.2 ∈ P.center 𝒢.root.1 := 𝒢.root_isCell
  apply P.inner_subset 𝒢.root.1 𝒢.root.2 hc
  exact ⟨P.center_subset _ hc, Metric.mem_ball_self (div_pos (d1c_rootScale_pos 𝒢) (by norm_num))⟩

end

/-- Every point of a root-forest region's root cell is within `5R` of `a`. -/
theorem d1crthin_dist_lt {n : ℕ} {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ} {a : Space n} {R : ℝ}
    (P : DirectPartition μ.support R) (𝒢 : GoodRegion P μ k Λ b) (hF : P.InForest a R 𝒢.root) :
    ∀ g ∈ 𝒢.rootCell, dist g a < 5 * R := by
  intro g hg
  obtain ⟨z₀, hz₀, ⟨w, hw0, hwa⟩, -, -, hsub⟩ := hF
  have hball := P.cell_subset_ball 0 z₀ hz₀
  have h0 : coherentScale R 0 = R := by simp [coherentScale]
  rw [h0] at hball
  have hg0 : g ∈ Metric.ball z₀ (2 * R) := hball (hsub hg)
  have hw0' : w ∈ Metric.ball z₀ (2 * R) := hball hw0
  rw [Metric.mem_ball] at hg0 hw0' hwa
  have hc := dist_comm z₀ w
  calc dist g a ≤ dist g z₀ + dist z₀ w + dist w a := dist_triangle4 _ _ _ _
    _ < 2 * R + 2 * R + R := by linarith
    _ = 5 * R := by ring

/-- `√|t_z - t_w| ≤ d_P(z, w)`. -/
theorem d1crthin_sqrt_le_dist {n : ℕ} (z w : Space n) :
    Real.sqrt |z.2.val - w.2.val| ≤ dist z w := by
  calc Real.sqrt |z.2.val - w.2.val|
      ≤ max ‖z.1 - w.1‖ (Real.sqrt |z.2.val - w.2.val|) := le_max_right _ _
    _ = dist (point z.1 z.2.val) (point w.1 w.2.val) := (dist_point _ _ _ _).symm
    _ = dist z w := rfl

/-- **The tube reading of a full-model distance**: since `modelSet M` is
`T.lowerModelSet (modelPlane T M) (modelTime T M)`, a bound `d_P(z, M) ≤ c` bounds the spatial
distance to the plane by `c` and, horizontally, `|t_z - τ|` by `c²`. -/
theorem d1crthin_tube {n k : ℕ} (T : NeckType) (M : Models n k T.toFamilyKind) (z : Space n)
    (c : ℝ) (h : Metric.infDist z (modelSet M) ≤ c) :
    Metric.infDist z.1 (NeckSelection.modelPlane T M).toSet ≤ c ∧
      (T = .horizontal → |z.2.val - NeckSelection.modelTime T M| ≤ c ^ 2) := by
  have hset := NeckSelection.lowerModelSet_modelPlane T M
  have hne : (modelSet M).Nonempty := modelSet_nonempty M
  constructor
  · refine le_trans ((Metric.le_infDist hne).mpr fun w hw => ?_) h
    have hw' : w.1 ∈ (NeckSelection.modelPlane T M).toSet := by
      rw [← hset] at hw
      cases T with
      | horizontal => exact hw.1
      | vertical => exact hw
    calc Metric.infDist z.1 (NeckSelection.modelPlane T M).toSet ≤ dist z.1 w.1 :=
          Metric.infDist_le_dist_of_mem hw'
      _ ≤ dist z w := by rw [Prod.dist_eq]; exact le_max_left _ _
  · intro hT
    subst hT
    have hsq : Real.sqrt |z.2.val - NeckSelection.modelTime .horizontal M| ≤ c := by
      refine le_trans ((Metric.le_infDist hne).mpr fun w hw => ?_) h
      rw [← hset] at hw
      have hwt : w.2.val = NeckSelection.modelTime .horizontal M := hw.2
      rw [← hwt]
      exact d1crthin_sqrt_le_dist z w
    have h0 := Real.sq_sqrt (abs_nonneg (z.2.val - NeckSelection.modelTime .horizontal M))
    rw [← h0]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2

/-- `x ≤ c^{k+2}` gives `x^{1/(k+2)} ≤ c`. -/
theorem d1crthin_rpow_le (k : ℕ) {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) (h : x ≤ c ^ (k + 2)) :
    x ^ ((1 : ℝ) / (k + 2)) ≤ c := by
  have hp : ((k : ℝ) + 2) ≠ 0 := by positivity
  calc x ^ ((1 : ℝ) / (k + 2)) ≤ (c ^ (k + 2)) ^ ((1 : ℝ) / (k + 2)) :=
        Real.rpow_le_rpow hx h (by positivity)
    _ = c := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc]
        have h1 : ((k + 2 : ℕ) : ℝ) * (1 / ((k : ℝ) + 2)) = 1 := by
          rw [Nat.cast_add, Nat.cast_ofNat]
          exact mul_one_div_cancel hp
        rw [h1, Real.rpow_one]

/-- `(x y)^p w = x^p w y^p`. -/
theorem d1crthin_pow_identity (x y w : ℝ) (p : ℕ) : (x * y) ^ p * w = x ^ p * w * y ^ p := by
  rw [mul_pow]; ring

/-- **The initial tube and the artificial root** (`RootThinnessStatement`). -/
theorem d1c_rootThinness_proof :
    PartitionEnergy.PointToFitStatement → RootThinnessStatement := by
  intro hP2F n hn k hk hkn A hA
  refine ⟨4, by norm_num, fun Λ hΛ => ⟨13, by norm_num, fun η hη => ?_⟩⟩
  have hΛ0 : 0 < Λ := by linarith
  have hA0 : 0 < A := by linarith
  have hc0 : 0 < (Λ / 2) ^ (k + 2) := pow_pos (by linarith) _
  have hη4 : 0 < η / 4 := div_pos hη (by norm_num)
  have hm0 : 0 < min 1 ((η / 4) ^ (k + 2)) := lt_min one_pos (pow_pos hη4 _)
  refine ⟨min 1 ((η / 4) ^ (k + 2)) / (A * (Λ / 2) ^ (k + 2)),
    div_pos hm0 (mul_pos hA0 hc0), fun b hb hbb => ?_⟩
  intro μ hμc hμr a ha R hR hADR P 𝒢 hF
  have he0 : 0 ≤ (Λ / 2) ^ (k + 2) * b := mul_nonneg hc0.le hb.le
  have hAe : A * ((Λ / 2) ^ (k + 2) * b) ≤ min 1 ((η / 4) ^ (k + 2)) := by
    have h := (le_div_iff₀ (mul_pos hA0 hc0)).mp hbb
    calc A * ((Λ / 2) ^ (k + 2) * b) = b * (A * (Λ / 2) ^ (k + 2)) := by ring
      _ ≤ _ := h
  have hroot : (A * ((Λ / 2) ^ (k + 2) * b)) ^ ((1 : ℝ) / (k + 2)) ≤ η / 4 :=
    d1crthin_rpow_le k (mul_nonneg hA0.le he0) hη4.le (hAe.trans (min_le_right _ _))
  have hℓ : 0 < 𝒢.rootScale := d1c_rootScale_pos 𝒢
  have hℓR : 𝒢.rootScale ≤ R := d1crthin_rootScale_le 𝒢
  have hq : 𝒢.root.2 ∈ 𝒢.rootCell := d1crthin_root_mem 𝒢
  have hqa : dist 𝒢.root.2 a < 5 * R := d1crthin_dist_lt P 𝒢 hF _ hq
  have hsub : Metric.ball 𝒢.root.2 (4 * (2 * 𝒢.rootScale)) ⊆ Metric.ball a (13 * R) :=
    Metric.ball_subset_ball' (by linarith)
  have h4 : 4 * (2 * 𝒢.rootScale) ≤ 13 * R := by linarith
  have hpos : 0 < Λ * 𝒢.rootScale := mul_pos hΛ0 hℓ
  have hfit : fit μ (𝒢.model 𝒢.root) 𝒢.root.2 (2 * (2 * 𝒢.rootScale)) ≤
      ENNReal.ofReal ((Λ / 2) ^ (k + 2) * b * (2 * 𝒢.rootScale) ^ (k + 2)) := by
    calc fit μ (𝒢.model 𝒢.root) 𝒢.root.2 (2 * (2 * 𝒢.rootScale))
        ≤ fit μ (𝒢.model 𝒢.root) 𝒢.root.2 (Λ * 𝒢.rootScale) := by
          apply MeasureTheory.lintegral_mono_set
          apply Metric.ball_subset_ball
          nlinarith
      _ ≤ ENNReal.ofReal (Λ * 𝒢.rootScale) ^ (k + 2) * ENNReal.ofReal b :=
          d1crthin_fit_le_budget 𝒢 𝒢.root 𝒢.root_mem hpos
      _ = ENNReal.ofReal ((Λ / 2) ^ (k + 2) * b * (2 * 𝒢.rootScale) ^ (k + 2)) := by
          rw [← ENNReal.ofReal_pow hpos.le, ← ENNReal.ofReal_mul (pow_nonneg hpos.le _)]
          congr 1
          rw [show Λ * 𝒢.rootScale = Λ / 2 * (2 * 𝒢.rootScale) by ring]
          exact d1crthin_pow_identity _ _ _ _
  have hP := hP2F n k 𝒢.type.toFamilyKind μ A a (13 * R) hA hADR 𝒢.root.2 (2 * 𝒢.rootScale)
    (by linarith) hsub h4 (𝒢.model 𝒢.root) _ he0 (hAe.trans (min_le_left _ _)) hfit
  have hS : ∀ z ∈ 𝒢.rootCell,
      Metric.infDist z (modelSet (𝒢.model 𝒢.root)) ≤ η * 𝒢.rootScale := by
    intro z hz
    have hz' : z ∈ μ.support ∩ Metric.ball 𝒢.root.2 (2 * 𝒢.rootScale) :=
      ⟨d1crthin_cell_subset P 𝒢.root 𝒢.root_isCell hz,
        P.cell_subset_ball 𝒢.root.1 𝒢.root.2 𝒢.root_isCell hz⟩
    have h := mul_le_mul_of_nonneg_right hroot hℓ.le
    refine (hP z hz').trans ?_
    nlinarith
  have hcl : ∀ z ∈ closure 𝒢.rootCell,
      Metric.infDist z (modelSet (𝒢.model 𝒢.root)) ≤ η * 𝒢.rootScale := fun z hz =>
    closure_minimal (t := {z | Metric.infDist z (modelSet (𝒢.model 𝒢.root)) ≤ η * 𝒢.rootScale})
      hS (isClosed_le (Metric.continuous_infDist_pt _) continuous_const) hz
  have hηℓ : 0 ≤ η * 𝒢.rootScale := (mul_pos hη hℓ).le
  have hq' := d1crthin_tube 𝒢.type (𝒢.model 𝒢.root) 𝒢.root.2 _ (hcl _ (subset_closure hq))
  have hproj : ‖𝒢.root.2.1 - (rootPlane 𝒢).projection 𝒢.root.2.1‖ ≤ η * 𝒢.rootScale := by
    rw [← AffineSpatialPlane.spatial_infDist_eq]
    exact hq'.1
  have hfst : (rootCenter 𝒢).1 = (rootPlane 𝒢).projection 𝒢.root.2.1 := by
    unfold rootCenter
    split_ifs <;> rfl
  refine ⟨fun z hz => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := d1crthin_tube 𝒢.type (𝒢.model 𝒢.root) z _ (hcl z hz)
    exact ⟨hcl z hz, h1, h2⟩
  · by_cases hT : 𝒢.type = .horizontal
    · have ht := hq'.2 hT
      have hrc : rootCenter 𝒢 = point ((rootPlane 𝒢).projection 𝒢.root.2.1)
          (NeckSelection.modelTime 𝒢.type (𝒢.model 𝒢.root)) := by
        simp only [rootCenter, hT, ↓reduceIte]
      rw [hrc]
      calc dist (point ((rootPlane 𝒢).projection 𝒢.root.2.1)
            (NeckSelection.modelTime 𝒢.type (𝒢.model 𝒢.root))) 𝒢.root.2
          = dist (point ((rootPlane 𝒢).projection 𝒢.root.2.1)
              (NeckSelection.modelTime 𝒢.type (𝒢.model 𝒢.root)))
              (point 𝒢.root.2.1 𝒢.root.2.2.val) := rfl
        _ = max ‖(rootPlane 𝒢).projection 𝒢.root.2.1 - 𝒢.root.2.1‖
              (Real.sqrt |NeckSelection.modelTime 𝒢.type (𝒢.model 𝒢.root) - 𝒢.root.2.2.val|) :=
            dist_point _ _ _ _
        _ ≤ η * 𝒢.rootScale := by
            refine max_le (by rw [norm_sub_rev]; exact hproj) ?_
            rw [abs_sub_comm]
            calc Real.sqrt |𝒢.root.2.2.val - NeckSelection.modelTime 𝒢.type (𝒢.model 𝒢.root)|
                ≤ Real.sqrt ((η * 𝒢.rootScale) ^ 2) := Real.sqrt_le_sqrt ht
              _ = η * 𝒢.rootScale := Real.sqrt_sq hηℓ
    · have hrc : rootCenter 𝒢 = ((rootPlane 𝒢).projection 𝒢.root.2.1, 𝒢.root.2.2) := by
        simp only [rootCenter, hT, ↓reduceIte]
      rw [hrc, Prod.dist_eq, dist_self, dist_eq_norm, norm_sub_rev]
      exact max_le hproj hηℓ
  · rw [hfst, norm_sub_rev]
    exact hproj

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
