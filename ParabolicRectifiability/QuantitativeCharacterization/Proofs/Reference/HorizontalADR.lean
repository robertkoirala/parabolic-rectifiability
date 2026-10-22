import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.HorizontalCarrier
import ParabolicRectifiability.Foundations.ADR

/-! # Uniform ADR of horizontal references

Proof of `ba1_horizontal_adr`.

Notation: `H` a horizontal `L`-reference with spatial map `F`, domain `D`, plateau function `T`,
closed Whitney cubes `Q_i` of side `ℓ_i`, anchors `a_i`; `σ = (F,T)_# L^k`, `Γ = supp σ`;
`ω_k = |B(0,1)|` in `ℝ^k`. The constants depend only on `(k, L)`.

* **Upper bound** (`b1adrh_upper`, every centre `z ∈ X`): the preimage of `P(z,r)` lies in a
  spatial ball `B(v₀, 2Lr)`, so `σ(P(z,r)) ≤ (2L)^k ω_k r^k`.
* **Lower bound at trace points** (`b1adrh_lower_trace`): `B(u, r/(3L))` maps into
  `P((F u, τ u), r)` (`b1adrh_ball_subset`, from the anchor bound), so `σ ≥ ω_k (r/(3L))^k`.
* **Lower bound at closed plateau points** (`b1adrh_lower_plateau`): the point
  `(F v, τ(a_i))` with `v` in the **closed** cube `Q_i` (at its own plateau height, which covers
  boundary points whose face is assigned to a neighbour). For `r ≥ 22 L √k ℓ_i` the anchor
  trace point `(F a_i, τ a_i)` lies within `11 L √k ℓ_i ≤ r/2` and its own lower bound at radius
  `r/2` applies. Otherwise the inward box of side `min(r/(L(k+1)), ℓ_i)` at `v` inside
  `int Q_i ⊆ Φ_i` (height `τ(a_i)`, spatial distance `< r/L`) has volume
  `≥ min(r/(L(k+1)), ℓ_i)^k ≥ (r/(22(k+1)L))^k`.
* **Lower bound on the support** (`b1adrh_lower`): every point `(F v, T v)` of the range of `(F,T)`
  is a trace point or a closed plateau point, so `σ(P((F v, T v), ρ)) ≥ c ρ^k`
  (`b1adrh_lower_range`). For `z ∈ Γ`, `P(z, r/2)` has positive measure, hence contains a range
  point `w`, and `P(w, r/2) ⊆ P(z, r)`: `σ(P(z,r)) ≥ c 2^{-k} r^k`.

The statement proof `ba1_horizontal_adr_proof` takes the measurability of `(F,T)` from the hypothesis
`hbasic` of its type. The support description (trace together with the closed plateau faces) is
the separate named lemma `b1adrh_carrier_eq`; the ADR proof does not
need it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

variable {n k : ℕ} {L : ℝ}

/-! ### Coordinate boxes (the box lemmas of the fine-scale estimate, re-proved here) -/

theorem b1adrh_continuous_coord (α : Fin k) : Continuous fun x : Spatial k => x α := by
  fun_prop

/-- The volume of a coordinate box is the product of the side measures. -/
theorem b1adrh_volume_box (s : Fin k → Set ℝ) (hs : ∀ α, MeasurableSet (s α)) :
    volume {x : Spatial k | ∀ α, x α ∈ s α} = ∏ α, volume (s α) := by
  have hset : {x : Spatial k | ∀ α, x α ∈ s α} =
      (WithLp.ofLp : Spatial k → (Fin k → ℝ)) ⁻¹' (Set.univ.pi s) := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, mem_univ_pi]
  rw [hset, (PiLp.volume_preserving_ofLp (Fin k)).measure_preimage
    (MeasurableSet.univ_pi hs).nullMeasurableSet, volume_pi_pi]

/-- Open coordinate boxes are open. -/
theorem b1adrh_isOpen_openBox (lo hi : Fin k → ℝ) :
    IsOpen {x : Spatial k | ∀ α, lo α < x α ∧ x α < hi α} := by
  have hset : {x : Spatial k | ∀ α, lo α < x α ∧ x α < hi α} =
      ⋂ α, ({x : Spatial k | lo α < x α} ∩ {x : Spatial k | x α < hi α}) := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, mem_inter_iff]
  rw [hset]
  exact isOpen_iInter_of_finite fun α =>
    (isOpen_lt continuous_const (b1adrh_continuous_coord α)).inter
      (isOpen_lt (b1adrh_continuous_coord α) continuous_const)

/-- **Inward box.** A box `[lo, lo + ℓ]^k` meeting `B(b,R)` at `q` contains an open sub-box of
side `m = min(R,ℓ)` inside `B(b,(k+1)R)`; hence `m^k ≤ |open box ∩ B(b,(k+1)R)|`. -/
theorem b1adrh_volume_inner_box_ge (lo : Fin k → ℝ) {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R)
    (b q : Spatial k) (hqb : dist q b < R) (hq : ∀ β, lo β ≤ q β ∧ q β ≤ lo β + ℓ) :
    ENNReal.ofReal (min R ℓ ^ k) ≤
      volume ({x : Spatial k | ∀ β, lo β < x β ∧ x β < lo β + ℓ} ∩
        Metric.ball b ((k + 1) * R)) := by
  have hm0 : 0 < min R ℓ := lt_min hR hℓ
  have hmR : min R ℓ ≤ R := min_le_left _ _
  have hmℓ : min R ℓ ≤ ℓ := min_le_right _ _
  set m := min R ℓ with hm
  let c : Fin k → ℝ := fun β => min (q β) (lo β + ℓ - m)
  have hc1 : ∀ β, lo β ≤ c β := fun β => le_min (hq β).1 (by linarith)
  have hc2 : ∀ β, c β + m ≤ lo β + ℓ := fun β => by
    have := min_le_right (q β) (lo β + ℓ - m)
    show min (q β) (lo β + ℓ - m) + m ≤ lo β + ℓ
    linarith
  have hc3 : ∀ β, c β ≤ q β := fun β => min_le_left _ _
  have hc4 : ∀ β, q β ≤ c β + m := fun β => by
    show q β ≤ min (q β) (lo β + ℓ - m) + m
    rcases min_cases (q β) (lo β + ℓ - m) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
      linarith
    · rw [h]
      linarith [(hq β).2]
  have hsub : {x : Spatial k | ∀ β, x β ∈ Ioo (c β) (c β + m)} ⊆
      {x : Spatial k | ∀ β, lo β < x β ∧ x β < lo β + ℓ} ∩ Metric.ball b ((k + 1) * R) := by
    intro x hx
    refine ⟨fun β => ⟨(hc1 β).trans_lt (hx β).1, (hx β).2.trans_le (hc2 β)⟩, ?_⟩
    have hcoord : ∀ β, dist (x β) (q β) ≤ m := fun β => by
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [(hx β).1, (hx β).2, hc3 β, hc4 β]
    have hk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos k with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ k := by exact_mod_cast h
        nlinarith
    have hxq : dist x q ≤ k * m := by
      rw [PiLp.dist_eq_of_L2]
      calc √(∑ β, dist (x β) (q β) ^ 2) ≤ √((k * m) ^ 2) := by
            apply Real.sqrt_le_sqrt
            calc ∑ β, dist (x β) (q β) ^ 2 ≤ ∑ _β : Fin k, m ^ 2 :=
                  Finset.sum_le_sum fun β _ => pow_le_pow_left₀ dist_nonneg (hcoord β) 2
              _ = k * m ^ 2 := by rw [Fin.sum_const, nsmul_eq_mul]
              _ ≤ (k * m) ^ 2 := by
                  rw [mul_pow]
                  exact mul_le_mul_of_nonneg_right hk (sq_nonneg m)
        _ = k * m := Real.sqrt_sq (by positivity)
    have hkm : (k : ℝ) * m ≤ k * R := mul_le_mul_of_nonneg_left hmR (Nat.cast_nonneg k)
    rw [Metric.mem_ball]
    calc dist x b ≤ dist x q + dist q b := dist_triangle _ _ _
      _ < (k + 1) * R := by linarith
  calc ENNReal.ofReal (m ^ k) = ∏ _β : Fin k, ENNReal.ofReal m := by
        rw [Fin.prod_const, ENNReal.ofReal_pow hm0.le]
    _ = ∏ β, volume (Ioo (c β) (c β + m)) := by
        refine Finset.prod_congr rfl fun β _ => ?_
        rw [Real.volume_Ioo]
        congr 1
        ring
    _ = volume {x : Spatial k | ∀ β, x β ∈ Ioo (c β) (c β + m)} :=
        (b1adrh_volume_box (fun β => Ioo (c β) (c β + m)) fun _ => measurableSet_Ioo).symm
    _ ≤ _ := measure_mono hsub

/-- The open box `(lo, lo + ℓ_i)^k` lies in the interior of `Q_i`. -/
theorem b1adrh_openBox_subset_interior (H : HorizontalReference n k L) (i : H.cubeIndex) :
    {x : Spatial k | ∀ α, b1adrh_lo H i α < x α ∧ x α < b1adrh_lo H i α + b1adrh_side H i} ⊆
      interior (H.cube i) :=
  interior_maximal (fun x hx => (b1adrh_mem_cube H i x).2 fun α => ⟨(hx α).1.le, (hx α).2.le⟩)
    (b1adrh_isOpen_openBox (b1adrh_lo H i) (fun α => b1adrh_lo H i α + b1adrh_side H i))

/-- Points of `Q_i` are within `11 √k ℓ_i` of the anchor `a_i`:
`|v - a_i| ≤ |v - x| + |x - a_i| ≤ √k ℓ_i + dist(Q_i,D) ≤ √k ℓ_i + 10 diam Q_i`. -/
theorem b1adrh_anchor_near (H : HorizontalReference n k L) (i : H.cubeIndex) {v : Spatial k}
    (hv : v ∈ H.cube i) : dist v (H.anchor i) ≤ 11 * (√(k : ℝ) * b1adrh_side H i) := by
  obtain ⟨x, hx, hxa⟩ := H.anchor_nearest i
  have h1 := H.whitney_upper i
  have h2 := b1adrh_diam_le H i
  have h3 := b1adrh_dist_le H i hv hx
  have h4 := dist_triangle v x (H.anchor i)
  linarith

/-! ### Volumes of Euclidean balls -/

/-- `ω_k = |B(0,1)|`, the volume of the unit ball of `ℝ^k`. -/
def b1adrh_omega (k : ℕ) : ℝ :=
  (volume (Metric.ball (0 : Spatial k) 1)).toReal

theorem b1adrh_omega_pos (k : ℕ) : 0 < b1adrh_omega k := by
  unfold b1adrh_omega
  exact ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne'
    (measure_ball_lt_top (μ := volume)).ne

/-- `|B(u,ρ)| = ω_k ρ^k`. -/
theorem b1adrh_volume_ball (u : Spatial k) {ρ : ℝ} (hρ : 0 < ρ) :
    volume (Metric.ball u ρ) = ENNReal.ofReal (b1adrh_omega k * ρ ^ k) := by
  rw [Measure.addHaar_ball_of_pos volume u hρ, finrank_euclideanSpace_fin,
    ENNReal.ofReal_mul (b1adrh_omega_pos k).le, b1adrh_omega,
    ENNReal.ofReal_toReal
      (measure_ball_lt_top (μ := volume) (x := (0 : Spatial k)) (r := 1)).ne, mul_comm]

/-! ### Upper bound -/

/-- The parabolic distance dominates the spatial distance. -/
theorem b1adrh_dist_fst_le (z w : Space n) : dist z.1 w.1 ≤ dist z w := by
  rw [Prod.dist_eq]
  exact le_max_left _ _

/-- The upper ADR constant `(2L)^k ω_k`. -/
def b1adrh_upperConst (k : ℕ) (L : ℝ) : ℝ :=
  (2 * L) ^ k * b1adrh_omega k

/-- **Upper ADR bound, at every centre**: `σ(P(z,r)) ≤ (2L)^k ω_k r^k` for every `z ∈ X` and
`r > 0`. If `v₀` lies in the preimage of `P(z,r)`, the whole preimage lies in `B(v₀, 2Lr)`,
because `|v - v₀| ≤ L |F v - F v₀| < 2Lr`. -/
theorem b1adrh_upper (H : HorizontalReference n k L) (hmeas : Measurable H.map)
    (z : Space n) {r : ℝ} (hr : 0 < r) :
    H.measure (Metric.ball z r) ≤ ENNReal.ofReal (b1adrh_upperConst k L * r ^ k) := by
  have hL := b1adrh_L_pos H
  rw [HorizontalReference.measure, Measure.map_apply hmeas measurableSet_ball]
  rcases (H.map ⁻¹' Metric.ball z r).eq_empty_or_nonempty with h | ⟨v₀, hv₀⟩
  · rw [h, measure_empty]
    exact zero_le
  · have hsub : H.map ⁻¹' Metric.ball z r ⊆ Metric.ball v₀ (2 * L * r) := by
      intro v hv
      rw [mem_preimage, Metric.mem_ball] at hv hv₀
      have h1 : dist (H.spatialMap v) z.1 < r := (b1adrh_dist_fst_le (H.map v) z).trans_lt hv
      have h2 : dist (H.spatialMap v₀) z.1 < r :=
        (b1adrh_dist_fst_le (H.map v₀) z).trans_lt hv₀
      have h3 := dist_triangle_right (H.spatialMap v) (H.spatialMap v₀) z.1
      have h5 : dist (H.spatialMap v) (H.spatialMap v₀) < 2 * r := by linarith
      rw [Metric.mem_ball]
      calc dist v v₀ ≤ L * dist (H.spatialMap v) (H.spatialMap v₀) :=
            (H.spatialMap_bilipschitz v v₀).1
        _ < L * (2 * r) := mul_lt_mul_of_pos_left h5 hL
        _ = 2 * L * r := by ring
    calc volume (H.map ⁻¹' Metric.ball z r) ≤ volume (Metric.ball v₀ (2 * L * r)) :=
          measure_mono hsub
      _ = ENNReal.ofReal (b1adrh_omega k * (2 * L * r) ^ k) :=
          b1adrh_volume_ball v₀ (by positivity)
      _ = ENNReal.ofReal (b1adrh_upperConst k L * r ^ k) := by
          congr 1
          rw [b1adrh_upperConst, mul_pow (2 * L) r k]
          ring

/-! ### Lower bounds -/

/-- **Lower bound at a trace point**: for `u ∈ D`, `σ(P((F u, τ u), r)) ≥ ω_k (r/(3L))^k`. -/
theorem b1adrh_lower_trace (H : HorizontalReference n k L) (hmeas : Measurable H.map)
    {u : Spatial k} (hu : u ∈ H.domain) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (b1adrh_omega k * (r / (3 * L)) ^ k) ≤
      H.measure (Metric.ball (H.map u) r) := by
  have hL := b1adrh_L_pos H
  rw [← b1adrh_volume_ball u (by positivity : 0 < r / (3 * L))]
  exact (measure_mono (b1adrh_ball_subset H hu hr)).trans
    (Measure.le_map_apply hmeas.aemeasurable _)

/-- The lower ADR constant at range points, `c_{k,L} = min(ω_k (6L)^{-k}, (22(k+1)L)^{-k})`. -/
def b1adrh_lowerConst (k : ℕ) (L : ℝ) : ℝ :=
  min (b1adrh_omega k / (6 * L) ^ k) (1 / (22 * ((k : ℝ) + 1) * L) ^ k)

theorem b1adrh_lowerConst_pos (k : ℕ) {L : ℝ} (hL : 0 < L) : 0 < b1adrh_lowerConst k L :=
  lt_min (div_pos (b1adrh_omega_pos k) (pow_pos (by positivity) k))
    (div_pos one_pos (pow_pos (by positivity) k))

theorem b1adrh_lowerConst_le_trace (k : ℕ) {L : ℝ} (hL : 0 < L) {r : ℝ} (hr : 0 < r) :
    b1adrh_lowerConst k L * r ^ k ≤ b1adrh_omega k * (r / (3 * L)) ^ k := by
  have hω := b1adrh_omega_pos k
  have h1 : b1adrh_lowerConst k L ≤ b1adrh_omega k / (6 * L) ^ k := min_le_left _ _
  have h2 : (3 * L) ^ k ≤ (6 * L) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
  calc b1adrh_lowerConst k L * r ^ k ≤ b1adrh_omega k / (6 * L) ^ k * r ^ k :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = b1adrh_omega k * r ^ k / (6 * L) ^ k := by ring
    _ ≤ b1adrh_omega k * r ^ k / (3 * L) ^ k :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) h2
    _ = b1adrh_omega k * (r / (3 * L)) ^ k := by
        rw [div_pow]
        ring

/-- **Lower bound at a closed plateau point**: for `v` in the **closed** cube `Q_i`, at the
plateau height `τ(a_i)` of `Q_i`, `σ(P((F v, τ(a_i)), r)) ≥ c_{k,L} r^k`. Large radii
(`r ≥ 22 L √k ℓ_i`) use the anchor trace point; smaller radii an inward box in `int Q_i`. -/
theorem b1adrh_lower_plateau (H : HorizontalReference n k L) (hmeas : Measurable H.map)
    (i : H.cubeIndex) {v : Spatial k} (hv : v ∈ H.cube i) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (b1adrh_lowerConst k L * r ^ k) ≤
      H.measure (Metric.ball (point (H.spatialMap v) (H.height (H.anchor i))) r) := by
  have hL := b1adrh_L_pos H
  have hℓ := b1adrh_side_pos H i
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hsq : √(k : ℝ) ≤ (k : ℝ) + 1 := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  have hsq0 : 0 ≤ √(k : ℝ) := Real.sqrt_nonneg _
  by_cases hcase : 22 * L * (√(k : ℝ) * b1adrh_side H i) ≤ r
  · -- Large radii: the anchor trace point `(F a_i, τ a_i)` is within `r/2`.
    have hd : dist (H.map (H.anchor i)) (point (H.spatialMap v) (H.height (H.anchor i))) ≤
        11 * L * (√(k : ℝ) * b1adrh_side H i) := by
      rw [HorizontalReference.map, dist_point, sub_self, abs_zero, Real.sqrt_zero,
        max_eq_left (norm_nonneg _), ← dist_eq_norm]
      calc dist (H.spatialMap (H.anchor i)) (H.spatialMap v) ≤ L * dist (H.anchor i) v :=
            (H.spatialMap_bilipschitz _ _).2
        _ ≤ L * (11 * (√(k : ℝ) * b1adrh_side H i)) := by
            rw [dist_comm]
            exact mul_le_mul_of_nonneg_left (b1adrh_anchor_near H i hv) hL.le
        _ = 11 * L * (√(k : ℝ) * b1adrh_side H i) := by ring
    have hsub : Metric.ball (H.map (H.anchor i)) (r / 2) ⊆
        Metric.ball (point (H.spatialMap v) (H.height (H.anchor i))) r :=
      Metric.ball_subset_ball' (by linarith)
    refine le_trans ?_ ((b1adrh_lower_trace H hmeas (H.anchor_mem i) (half_pos hr)).trans
      (measure_mono hsub))
    apply ENNReal.ofReal_le_ofReal
    have he : r / 2 / (3 * L) = r / (6 * L) := by
      rw [div_div]
      congr 1
      ring
    rw [he]
    calc b1adrh_lowerConst k L * r ^ k ≤ b1adrh_omega k / (6 * L) ^ k * r ^ k :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ = b1adrh_omega k * (r / (6 * L)) ^ k := by
          rw [div_pow]
          ring
  · -- Small and intermediate radii: an inward box inside `int Q_i ⊆ Φ_i`.
    have hcase' : r < 22 * L * (√(k : ℝ) * b1adrh_side H i) := not_le.1 hcase
    have hR : 0 < r / L / ((k : ℝ) + 1) := by positivity
    have hbox := b1adrh_volume_inner_box_ge (b1adrh_lo H i) hℓ hR v v
      (by rw [dist_self]; exact hR) ((b1adrh_mem_cube H i v).1 hv)
    have hkR : ((k : ℝ) + 1) * (r / L / ((k : ℝ) + 1)) = r / L :=
      mul_div_cancel₀ (r / L) (by positivity : ((k : ℝ) + 1) ≠ 0)
    rw [hkR] at hbox
    have hsub : {x : Spatial k | ∀ β, b1adrh_lo H i β < x β ∧
          x β < b1adrh_lo H i β + b1adrh_side H i} ∩ Metric.ball v (r / L) ⊆
        H.map ⁻¹' Metric.ball (point (H.spatialMap v) (H.height (H.anchor i))) r := by
      rintro w ⟨hw1, hw2⟩
      have hwi : w ∈ H.face i :=
        H.interior_subset_face i (b1adrh_openBox_subset_interior H i hw1)
      rw [Metric.mem_ball, lt_div_iff₀ hL] at hw2
      simp only [mem_preimage, HorizontalReference.map]
      rw [H.height_plateau i w hwi, mem_ball_point _ _ _ _ _ hr, sub_self, abs_zero,
        ← dist_eq_norm]
      refine ⟨?_, by positivity⟩
      calc dist (H.spatialMap w) (H.spatialMap v) ≤ L * dist w v :=
            (H.spatialMap_bilipschitz w v).2
        _ < r := by linarith
    refine le_trans ?_ (hbox.trans ((measure_mono hsub).trans
      (Measure.le_map_apply hmeas.aemeasurable _)))
    apply ENNReal.ofReal_le_ofReal
    have hm0 : 0 ≤ r / (22 * ((k : ℝ) + 1) * L) := by positivity
    have hm1 : r / (22 * ((k : ℝ) + 1) * L) ≤ r / L / ((k : ℝ) + 1) := by
      rw [div_div]
      refine div_le_div_of_nonneg_left hr.le (by positivity) ?_
      have hLk : 0 ≤ L * (k : ℝ) := by positivity
      linarith
    have hm2 : r / (22 * ((k : ℝ) + 1) * L) ≤ b1adrh_side H i := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 22 * ((k : ℝ) + 1) * L)]
      have h1 : 22 * L * (√(k : ℝ) * b1adrh_side H i) ≤
          22 * L * (((k : ℝ) + 1) * b1adrh_side H i) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hℓ.le) (by positivity)
      linarith
    calc b1adrh_lowerConst k L * r ^ k ≤ 1 / (22 * ((k : ℝ) + 1) * L) ^ k * r ^ k :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = (r / (22 * ((k : ℝ) + 1) * L)) ^ k := by
          rw [div_pow]
          ring
      _ ≤ min (r / L / ((k : ℝ) + 1)) (b1adrh_side H i) ^ k :=
          pow_le_pow_left₀ hm0 (le_min hm1 hm2) k

/-- **Lower bound at every point of the range of `(F,T)`**: `σ(P((F v, T v), r)) ≥ c_{k,L} r^k`.
Every `v` lies in `D` (a trace point) or in a face `Φ_i ⊆ Q_i`, where `T v = τ(a_i)` (a closed
plateau point). -/
theorem b1adrh_lower_range (H : HorizontalReference n k L) (hmeas : Measurable H.map)
    (v : Spatial k) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (b1adrh_lowerConst k L * r ^ k) ≤ H.measure (Metric.ball (H.map v) r) := by
  rcases b1adrh_domain_or_face H v with hv | ⟨i, hv⟩
  · exact (ENNReal.ofReal_le_ofReal (b1adrh_lowerConst_le_trace k (b1adrh_L_pos H) hr)).trans
      (b1adrh_lower_trace H hmeas hv hr)
  · have he : H.map v = point (H.spatialMap v) (H.height (H.anchor i)) := by
      rw [HorizontalReference.map, H.height_plateau i v hv]
    rw [he]
    exact b1adrh_lower_plateau H hmeas i (H.face_subset_cube i hv) hr

/-- **Lower ADR bound on the support**: for `z ∈ Γ = supp σ` and `r > 0`,
`σ(P(z,r)) ≥ c_{k,L} 2^{-k} r^k`. The ball `P(z, r/2)` has positive measure, so it contains a
range point `(F v, T v)`, and `P((F v, T v), r/2) ⊆ P(z,r)`. -/
theorem b1adrh_lower (H : HorizontalReference n k L) (hmeas : Measurable H.map)
    {z : Space n} (hz : z ∈ H.measure.support) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (b1adrh_lowerConst k L / 2 ^ k * r ^ k) ≤ H.measure (Metric.ball z r) := by
  have hpos : 0 < H.measure (Metric.ball z (r / 2)) :=
    (Measure.mem_support_iff_forall z).1 hz _ (Metric.ball_mem_nhds z (half_pos hr))
  have hne : (H.map ⁻¹' Metric.ball z (r / 2)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    rw [HorizontalReference.measure, Measure.map_apply hmeas measurableSet_ball, h,
      measure_empty] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨v, hv⟩ := hne
  rw [mem_preimage, Metric.mem_ball] at hv
  have hsub : Metric.ball (H.map v) (r / 2) ⊆ Metric.ball z r :=
    Metric.ball_subset_ball' (by linarith)
  calc ENNReal.ofReal (b1adrh_lowerConst k L / 2 ^ k * r ^ k) =
        ENNReal.ofReal (b1adrh_lowerConst k L * (r / 2) ^ k) := by
        congr 1
        rw [div_pow]
        ring
    _ ≤ H.measure (Metric.ball (H.map v) (r / 2)) := b1adrh_lower_range H hmeas v (half_pos hr)
    _ ≤ H.measure (Metric.ball z r) := measure_mono hsub

/-! ### The ADR constant and the statement -/

/-- The ADR constant `A = max(1, (2L)^k ω_k, 2^k / c_{k,L})`, depending only on `(k, L)`. -/
def b1adrh_adrConst (k : ℕ) (L : ℝ) : ℝ :=
  max 1 (max (b1adrh_upperConst k L) (2 ^ k / b1adrh_lowerConst k L))

theorem b1adrh_upperConst_le (k : ℕ) (L : ℝ) :
    b1adrh_upperConst k L ≤ b1adrh_adrConst k L :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem b1adrh_adrConst_inv_le (k : ℕ) {L : ℝ} (hL : 0 < L) :
    (b1adrh_adrConst k L)⁻¹ ≤ b1adrh_lowerConst k L / 2 ^ k := by
  have hc := b1adrh_lowerConst_pos k hL
  have h1 : 2 ^ k / b1adrh_lowerConst k L ≤ b1adrh_adrConst k L :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  calc (b1adrh_adrConst k L)⁻¹ ≤ (2 ^ k / b1adrh_lowerConst k L)⁻¹ :=
        inv_anti₀ (div_pos (pow_pos two_pos k) hc) h1
    _ = b1adrh_lowerConst k L / 2 ^ k := inv_div _ _

/-- **Uniform ADR of one horizontal reference**, given the measurability of `(F,T)`:
`A⁻¹ r^k ≤ σ(P(z,r)) ≤ A r^k` for `z ∈ supp σ`, `r > 0`, with `A = b1adrh_adrConst k L`. -/
theorem b1adrh_isADR (H : HorizontalReference n k L) (hmeas : Measurable H.map) :
    IsADR (b1adrh_adrConst k L) k H.measure := by
  have hL := b1adrh_L_pos H
  intro z hz r hr
  constructor
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) (b1adrh_lower H hmeas hz hr)
    exact mul_le_mul_of_nonneg_right (b1adrh_adrConst_inv_le k hL) (by positivity)
  · refine (b1adrh_upper H hmeas z hr).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (b1adrh_upperConst_le k L) (by positivity)

/-- **Uniform ADR of horizontal references** (`ba1_horizontal_adr`), in the implication
form of its type: given the conclusion `hbasic` of `ba1_horizontal_basic` (only its
measurability clause is used), for `1 ≤ L` the constant
`A = max(1, (2L)^k ω_k, 2^k / min(ω_k (6L)^{-k}, (22(k+1)L)^{-k}))`, which depends only on
`(k, L)`, makes the natural measure of every horizontal `L`-reference globally `k`-ADR. -/
theorem ba1_horizontal_adr_proof
    (hbasic : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∀ H : HorizontalReference n k L,
      Measurable H.map ∧ IsClosed H.carrier ∧ IsFiniteMeasureOnCompacts H.measure ∧
        H.measure.InnerRegular) :
    ∀ (n k : ℕ) (L : ℝ), 1 ≤ L →
      ∃ A : ℝ, 1 ≤ A ∧ ∀ H : HorizontalReference n k L, IsADR A k H.measure :=
  fun n k L hL => ⟨b1adrh_adrConst k L, le_max_left _ _,
    fun H => b1adrh_isADR H (hbasic n k L hL H).1⟩

end ParabolicRectifiability.QuantitativeCharacterization
