import ParabolicRectifiability.QuantitativeCharacterization.References
import ParabolicRectifiability.Measure.ScaleEnergy

/-! # Fine scales of the horizontal temporal energy

Proof of `ba1_horizontal_fine`; the type of `ba1_horizontal_fine_proof` is the statement type.

The actual parabolic time restriction `|T(v) - T(u)| < r²` is kept throughout. For a centre `u`
in the face of a Whitney cube `Q` with lower corner `a` and side `ℓ`, write
`τ_L(u,r) = r^{-k-2} ∫_{|v-u| < L r, |T v - T u| < r²} |T v - T u| dv`.

* **Cost bound** (`b1hfin_cost_le`): the time restriction bounds the integrand by `r²` and the
  domain by `B(u, L r)`, so `τ_L(u,r) ≤ L^k |B(0,1)|`.
* **Interior vanishing** (`b1hfin_cost_eq_zero`): if every coordinate of `u` is more than `L r`
  away from both faces `a_α`, `a_α + ℓ` of the cube, then `B(u, L r)` lies in the open box, hence
  in `int Q ⊆ face Q`, where `T` is constant; so `τ_L(u,r) = 0`. This is the coordinate form of
  `τ_L(u,r) = 0` for `L r < d_Q(u)`.
* Hence `τ_L(u,r) ≤ L^k |B(0,1)| · 1_{Bad_Q}(u,r)` (`b1hfin_cost_le_indicator`), where
  `Bad_Q = {(u,r) : ∃ α, u_α ≤ a_α + L r ∨ a_α + ℓ ≤ u_α + L r}` is closed.
* **Order of integration.** Instead of integrating the logarithmic profile
  `C L^k log₊(L min(R,ℓ)/d_Q(u))` over centres, Tonelli exchanges the centre and scale
  integrals (this is the layer-cake formula). At a fixed scale `r`, the bad centres in
  `B(b,R) ∩ Q` lie in `2k` clipped coordinate strips of width `L r`, each of volume at most
  `L r (2 m)^{k-1}`, `m = min(R, ℓ)` (`b1hfin_volume_strip_le`, `b1hfin_slice_le`); then
  `∫_0^m L r dr/r = L m`. Each cube therefore contributes at most `K_{k,L} m^k`.
* **Small and large cubes at once** (`b1hfin_volume_inner_box_ge`): a cube that meets `B(b,R)`
  contains an open sub-box of side `m` inside `B(b,(k+1)R)`, so
  `m^k ≤ |int Q ∩ B(b,(k+1)R)|`. For small cubes (`ℓ ≤ R`) this is the whole cube; for large
  cubes (`ℓ > R`) it is the inward box that makes them boundedly many. Disjoint interiors sum to
  at most `|B(b,(k+1)R)| = (k+1)^k |B(0,1)| R^k`.

The constant is `C = L^{k+1} |B(0,1)|² 2k 2^{k-1} (k+1)^k + 1`, depending only on `(k,L)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-! ## Coordinate boxes in `ℝ^k` -/

/-- Coordinates of `ℝ^k` are continuous. -/
theorem b1hfin_continuous_coord {k : ℕ} (α : Fin k) : Continuous fun x : Spatial k => x α := by
  fun_prop

/-- The volume of a coordinate box `{x : x_α ∈ s_α for all α}` is the product of the side
measures. -/
theorem b1hfin_volume_box {k : ℕ} (s : Fin k → Set ℝ) (hs : ∀ α, MeasurableSet (s α)) :
    volume {x : Spatial k | ∀ α, x α ∈ s α} = ∏ α, volume (s α) := by
  have hset : {x : Spatial k | ∀ α, x α ∈ s α} =
      (WithLp.ofLp : Spatial k → (Fin k → ℝ)) ⁻¹' (Set.univ.pi s) := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, mem_univ_pi]
  rw [hset, (PiLp.volume_preserving_ofLp (Fin k)).measure_preimage
    (MeasurableSet.univ_pi hs).nullMeasurableSet, volume_pi_pi]

/-- Open coordinate boxes are open. -/
theorem b1hfin_isOpen_openBox {k : ℕ} (lo hi : Fin k → ℝ) :
    IsOpen {x : Spatial k | ∀ α, lo α < x α ∧ x α < hi α} := by
  have hset : {x : Spatial k | ∀ α, lo α < x α ∧ x α < hi α} =
      ⋂ α, ({x : Spatial k | lo α < x α} ∩ {x : Spatial k | x α < hi α}) := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, mem_inter_iff]
  rw [hset]
  exact isOpen_iInter_of_finite fun α =>
    (isOpen_lt continuous_const (b1hfin_continuous_coord α)).inter
      (isOpen_lt (b1hfin_continuous_coord α) continuous_const)

/-- A coordinate strip `{p ≤ x_α ≤ p + s}` of a box of side `ℓ` clipped to the ball `B(b,R)` has
volume at most `s (2 min(R,ℓ))^{k-1}`: the other sides have length at most
`min(ℓ, 2R) ≤ 2 min(R,ℓ)`. -/
theorem b1hfin_volume_strip_le {k : ℕ} (lo : Fin k → ℝ) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (b : Spatial k)
    (R : ℝ) (hR : 0 ≤ R) (α : Fin k) (p s : ℝ) (hs : 0 ≤ s) (S : Set (Spatial k))
    (hS : ∀ x ∈ S, dist x b < R ∧ (∀ β, lo β ≤ x β ∧ x β ≤ lo β + ℓ) ∧
      p ≤ x α ∧ x α ≤ p + s) :
    volume S ≤ ENNReal.ofReal (s * (2 * min R ℓ) ^ (k - 1)) := by
  classical
  let J : Fin k → Set ℝ := fun β =>
    if β = α then Icc p (p + s) else Icc (max (lo β) (b β - R)) (min (lo β + ℓ) (b β + R))
  have hJα : J α = Icc p (p + s) := ite_eq_left rfl
  have hJβ : ∀ β, β ≠ α → J β = Icc (max (lo β) (b β - R)) (min (lo β + ℓ) (b β + R)) :=
    fun β hβ => ite_eq_right hβ
  have hsub : S ⊆ {x : Spatial k | ∀ β, x β ∈ J β} := by
    intro x hx β
    obtain ⟨hxb, hbox, hp, hps⟩ := hS x hx
    by_cases hβ : β = α
    · rw [hβ, hJα]
      exact ⟨hp, hps⟩
    · rw [hJβ β hβ]
      have h := (PiLp.dist_apply_le x b β).trans_lt hxb
      rw [Real.dist_eq, abs_lt] at h
      exact ⟨max_le (hbox β).1 (by linarith [h.1]), le_min (hbox β).2 (by linarith [h.2])⟩
  have hJm : ∀ β, MeasurableSet (J β) := fun β => by
    by_cases hβ : β = α
    · rw [hβ, hJα]
      exact measurableSet_Icc
    · rw [hJβ β hβ]
      exact measurableSet_Icc
  have hvolα : volume (J α) = ENNReal.ofReal s := by
    rw [hJα, Real.volume_Icc]
    congr 1
    ring
  have hvolβ : ∀ β ∈ Finset.univ.erase α, volume (J β) ≤ ENNReal.ofReal (2 * min R ℓ) := by
    intro β hβ
    rw [hJβ β (Finset.ne_of_mem_erase hβ), Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    have h1 := min_le_left (lo β + ℓ) (b β + R)
    have h2 := min_le_right (lo β + ℓ) (b β + R)
    have h3 := le_max_left (lo β) (b β - R)
    have h4 := le_max_right (lo β) (b β - R)
    rcases min_cases R ℓ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
  have h2m : 0 ≤ 2 * min R ℓ := by
    have := le_min hR hℓ
    linarith
  calc volume S ≤ volume {x : Spatial k | ∀ β, x β ∈ J β} := measure_mono hsub
    _ = ∏ β, volume (J β) := b1hfin_volume_box J hJm
    _ = volume (J α) * ∏ β ∈ Finset.univ.erase α, volume (J β) :=
        (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ α)).symm
    _ ≤ ENNReal.ofReal s * ∏ _β ∈ Finset.univ.erase α, ENNReal.ofReal (2 * min R ℓ) :=
        mul_le_mul' hvolα.le (Finset.prod_le_prod hvolβ)
    _ = ENNReal.ofReal (s * (2 * min R ℓ) ^ (k - 1)) := by
        rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ α), Finset.card_univ,
          Fintype.card_fin, ← ENNReal.ofReal_pow h2m, ← ENNReal.ofReal_mul hs]

/-- A box of side `ℓ` meeting `B(b,R)` at `q` contains an open sub-box of side `m = min(R,ℓ)`
inside `B(b,(k+1)R)`; hence `m^k ≤ |open box ∩ B(b,(k+1)R)|`. -/
theorem b1hfin_volume_inner_box_ge {k : ℕ} (lo : Fin k → ℝ) {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R)
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
        (b1hfin_volume_box (fun β => Ioo (c β) (c β + m)) fun _ => measurableSet_Ioo).symm
    _ ≤ _ := measure_mono hsub

/-! ## Whitney cubes as coordinate boxes -/

/-- The lower corner `a_α = c_α + λ 2^j m_α` of the Whitney cube `i`. -/
def b1hfin_lo {n k : ℕ} {L : ℝ} (H : HorizontalReference n k L) (i : H.cubeIndex)
    (α : Fin k) : ℝ :=
  H.gridOrigin α + H.gridScale * (2 : ℝ) ^ H.cubeLevel i * (H.cubeCorner i α : ℝ)

/-- The closed Whitney cube `i` is the box `[a, a + ℓ]^k`, `ℓ = λ 2^j`. -/
theorem b1hfin_mem_cube {n k : ℕ} {L : ℝ} (H : HorizontalReference n k L) (i : H.cubeIndex)
    (x : Spatial k) :
    x ∈ H.cube i ↔ ∀ α, b1hfin_lo H i α ≤ x α ∧
      x α ≤ b1hfin_lo H i α + H.gridScale * (2 : ℝ) ^ H.cubeLevel i := by
  rw [H.cube_eq i]
  simp only [dyadicCube, mem_ofPred_eq, b1hfin_lo]
  have e : ∀ α : Fin k, H.gridOrigin α + H.gridScale * (2 : ℝ) ^ H.cubeLevel i *
      ((H.cubeCorner i α : ℝ) + 1) = H.gridOrigin α + H.gridScale * (2 : ℝ) ^ H.cubeLevel i *
        (H.cubeCorner i α : ℝ) + H.gridScale * (2 : ℝ) ^ H.cubeLevel i := fun α => by ring
  constructor
  · intro h α
    obtain ⟨h1, h2⟩ := h α
    exact ⟨h1, by linarith [e α]⟩
  · intro h α
    obtain ⟨h1, h2⟩ := h α
    exact ⟨h1, by linarith [e α]⟩

theorem b1hfin_side_pos {n k : ℕ} {L : ℝ} (H : HorizontalReference n k L) (i : H.cubeIndex) :
    0 < H.gridScale * (2 : ℝ) ^ H.cubeLevel i :=
  mul_pos H.gridScale_pos (zpow_pos two_pos _)

/-- The open box `(a, a + ℓ)^k` lies in the interior of the cube. -/
theorem b1hfin_openBox_subset_interior {n k : ℕ} {L : ℝ} (H : HorizontalReference n k L)
    (i : H.cubeIndex) :
    {x : Spatial k | ∀ α, b1hfin_lo H i α < x α ∧
        x α < b1hfin_lo H i α + H.gridScale * (2 : ℝ) ^ H.cubeLevel i} ⊆
      interior (H.cube i) :=
  interior_maximal (fun x hx => (b1hfin_mem_cube H i x).2 fun α => ⟨(hx α).1.le, (hx α).2.le⟩)
    (b1hfin_isOpen_openBox (b1hfin_lo H i)
      (fun α => b1hfin_lo H i α + H.gridScale * (2 : ℝ) ^ H.cubeLevel i))

/-! ## The temporal cost at one centre and one scale -/

/-- **The cost bound** `τ_L(u,r) ≤ L^k |B(0,1)|`, from the actual time restriction. -/
theorem b1hfin_cost_le {k : ℕ} (T : Spatial k → ℝ) {L : ℝ} (hL : 0 < L) (u : Spatial k) {r : ℝ}
    (hr : 0 < r) :
    (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
        (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |T v - T u| < r ^ 2},
          ENNReal.ofReal |T v - T u|) ≤
      ENNReal.ofReal (L ^ k * (volume (Metric.ball (0 : Spatial k) 1)).toReal) := by
  have hωfin : volume (Metric.ball (0 : Spatial k) 1) ≠ ∞ := MeasureTheory.measure_ball_ne_top
  have hω0 : 0 ≤ (volume (Metric.ball (0 : Spatial k) 1)).toReal := ENNReal.toReal_nonneg
  have hfr : Module.finrank ℝ (Spatial k) = k := finrank_euclideanSpace_fin
  have h1 : (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |T v - T u| < r ^ 2},
      ENNReal.ofReal |T v - T u|) ≤ ENNReal.ofReal (r ^ 2) * volume (Metric.ball u (L * r)) := by
    calc (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |T v - T u| < r ^ 2},
          ENNReal.ofReal |T v - T u|)
        ≤ ∫⁻ _ in {v : Spatial k | dist v u < L * r ∧ |T v - T u| < r ^ 2},
            ENNReal.ofReal (r ^ 2) :=
          setLIntegral_mono measurable_const fun v hv => ENNReal.ofReal_le_ofReal hv.2.le
      _ = ENNReal.ofReal (r ^ 2) *
            volume {v : Spatial k | dist v u < L * r ∧ |T v - T u| < r ^ 2} :=
          setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (r ^ 2) * volume (Metric.ball u (L * r)) := by
          gcongr
          intro v hv
          exact hv.1
  have h3 : volume (Metric.ball u (L * r)) =
      ENNReal.ofReal ((L * r) ^ k) *
        ENNReal.ofReal (volume (Metric.ball (0 : Spatial k) 1)).toReal := by
    rw [Measure.addHaar_ball_of_pos volume u (mul_pos hL hr), hfr, ENNReal.ofReal_toReal hωfin]
  have hreal : r⁻¹ ^ (k + 2) * (r ^ 2 * ((L * r) ^ k *
      (volume (Metric.ball (0 : Spatial k) 1)).toReal)) =
      L ^ k * (volume (Metric.ball (0 : Spatial k) 1)).toReal := by
    have e : r⁻¹ ^ (k + 2) * (r ^ 2 * ((L * r) ^ k *
        (volume (Metric.ball (0 : Spatial k) 1)).toReal)) =
        L ^ k * (volume (Metric.ball (0 : Spatial k) 1)).toReal * (r⁻¹ * r) ^ (k + 2) := by
      ring
    rw [e, inv_mul_cancel₀ hr.ne', one_pow, mul_one]
  have hinv : (ENNReal.ofReal r)⁻¹ ^ (k + 2) = ENNReal.ofReal (r⁻¹ ^ (k + 2)) := by
    rw [ENNReal.ofReal_pow (inv_nonneg.2 hr.le), ENNReal.ofReal_inv_of_pos hr]
  have ha : (0 : ℝ) ≤ r⁻¹ ^ (k + 2) := by positivity
  have hb : (0 : ℝ) ≤ r ^ 2 := by positivity
  have hc : (0 : ℝ) ≤ (L * r) ^ k := by positivity
  calc _ ≤ (ENNReal.ofReal r)⁻¹ ^ (k + 2) * (ENNReal.ofReal (r ^ 2) *
          (ENNReal.ofReal ((L * r) ^ k) *
            ENNReal.ofReal (volume (Metric.ball (0 : Spatial k) 1)).toReal)) := by
        rw [← h3]
        gcongr
    _ = ENNReal.ofReal (r⁻¹ ^ (k + 2) * (r ^ 2 * ((L * r) ^ k *
          (volume (Metric.ball (0 : Spatial k) 1)).toReal))) := by
        rw [hinv, ← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_mul ha]
    _ = _ := by rw [hreal]

/-- **Interior vanishing.** If every coordinate of `u ∈ face Q` is more than `ρ` away from both
faces of the cube, then `T` is constant on `B(u,ρ)` and the cost over any `S ⊆ B(u,ρ)`
vanishes. -/
theorem b1hfin_cost_eq_zero {n k : ℕ} {L : ℝ} (H : HorizontalReference n k L) (i : H.cubeIndex)
    {u : Spatial k} (hu : u ∈ H.face i) {ρ : ℝ}
    (hin : ∀ α, b1hfin_lo H i α + ρ < u α ∧
      u α + ρ < b1hfin_lo H i α + H.gridScale * (2 : ℝ) ^ H.cubeLevel i)
    (S : Set (Spatial k)) (hS : ∀ v ∈ S, dist v u < ρ) :
    (∫⁻ v in S, ENNReal.ofReal |H.height v - H.height u|) = 0 := by
  have hball : ∀ v : Spatial k, dist v u < ρ → H.height v = H.height u := by
    intro v hv
    have hvbox : ∀ α, b1hfin_lo H i α < v α ∧
        v α < b1hfin_lo H i α + H.gridScale * (2 : ℝ) ^ H.cubeLevel i := by
      intro α
      have h := (PiLp.dist_apply_le v u α).trans_lt hv
      rw [Real.dist_eq, abs_lt] at h
      obtain ⟨h1, h2⟩ := hin α
      constructor <;> linarith [h.1, h.2]
    have hvface : v ∈ H.face i :=
      H.interior_subset_face i (b1hfin_openBox_subset_interior H i hvbox)
    rw [H.height_plateau i v hvface, H.height_plateau i u hu]
  refine le_antisymm ?_ zero_le
  calc (∫⁻ v in S, ENNReal.ofReal |H.height v - H.height u|)
      ≤ ∫⁻ _ in S, (0 : ℝ≥0∞) :=
        setLIntegral_mono measurable_const fun v hv => by
          simp [hball v (hS v hv)]
    _ = 0 := lintegral_zero

/-- The closed set of centre-scale pairs `(u,r)` for which some coordinate of `u` is within
`L r` of a face of the cube `i`. -/
def b1hfin_bad {n k : ℕ} {L : ℝ} (H : HorizontalReference n k L) (i : H.cubeIndex) :
    Set (Spatial k × ℝ) :=
  ⋃ α : Fin k, ({p : Spatial k × ℝ | p.1 α ≤ b1hfin_lo H i α + L * p.2} ∪
    {p : Spatial k × ℝ |
      b1hfin_lo H i α + H.gridScale * (2 : ℝ) ^ H.cubeLevel i ≤ p.1 α + L * p.2})

theorem b1hfin_measurableSet_bad {n k : ℕ} {L : ℝ} (H : HorizontalReference n k L)
    (i : H.cubeIndex) : MeasurableSet (b1hfin_bad H i) := by
  apply IsClosed.measurableSet
  apply isClosed_iUnion_of_finite
  intro α
  have hc : Continuous fun p : Spatial k × ℝ => p.1 α :=
    (b1hfin_continuous_coord α).comp continuous_fst
  exact (isClosed_le hc (continuous_const.add (continuous_const.mul continuous_snd))).union
    (isClosed_le continuous_const (hc.add (continuous_const.mul continuous_snd)))

/-- `τ_L(u,r) ≤ L^k |B(0,1)| · 1_{Bad}(u,r)` for centres in the face of the cube. -/
theorem b1hfin_cost_le_indicator {n k : ℕ} {L : ℝ} (hL : 1 ≤ L) (H : HorizontalReference n k L)
    (i : H.cubeIndex) {u : Spatial k} (hu : u ∈ H.face i) {r : ℝ} (hr : 0 < r) :
    (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
        (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
          ENNReal.ofReal |H.height v - H.height u|) ≤
      (b1hfin_bad H i).indicator
        (fun _ => ENNReal.ofReal (L ^ k * (volume (Metric.ball (0 : Spatial k) 1)).toReal))
        (u, r) := by
  by_cases h : (u, r) ∈ b1hfin_bad H i
  · rw [Set.indicator_of_mem h]
    exact b1hfin_cost_le H.height (by linarith) u hr
  · rw [Set.indicator_of_notMem h]
    have hin : ∀ α, b1hfin_lo H i α + L * r < u α ∧
        u α + L * r < b1hfin_lo H i α + H.gridScale * (2 : ℝ) ^ H.cubeLevel i := by
      intro α
      have hα : (u, r) ∉ ({p : Spatial k × ℝ | p.1 α ≤ b1hfin_lo H i α + L * p.2} ∪
          {p : Spatial k × ℝ |
            b1hfin_lo H i α + H.gridScale * (2 : ℝ) ^ H.cubeLevel i ≤ p.1 α + L * p.2}) :=
        fun hmem => h (mem_iUnion.2 ⟨α, hmem⟩)
      simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hα
      exact ⟨by linarith [hα.1], by linarith [hα.2]⟩
    have hz := b1hfin_cost_eq_zero H i hu hin
      {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2} (fun v hv => hv.1)
    simp only [hz, mul_zero, le_refl]

/-! ## The scale integral and the strips at one scale -/

/-- `∫_{(0,m)} r dr/r ≤ m`. -/
theorem b1hfin_scale_ofReal_le (m : ℝ) :
    ∫⁻ r in Ioo 0 m, ENNReal.ofReal r ∂scaleMeasure ≤ ENNReal.ofReal m := by
  rw [scaleMeasure, setLIntegral_withDensity_eq_setLIntegral_mul _ measurable_scaleDensity
    ENNReal.measurable_ofReal measurableSet_Ioo]
  calc _ ≤ ∫⁻ _ in Ioo 0 m, (1 : ℝ≥0∞) ∂volume.restrict (Ioi 0) := by
        apply setLIntegral_mono' measurableSet_Ioo
        intro r hr
        show ENNReal.ofReal (1 / r) * ENNReal.ofReal r ≤ 1
        rw [← ENNReal.ofReal_mul (one_div_nonneg.2 hr.1.le), one_div_mul_cancel hr.1.ne',
          ENNReal.ofReal_one]
    _ = (volume.restrict (Ioi 0)) (Ioo 0 m) := setLIntegral_one _
    _ ≤ volume (Ioo 0 m) := Measure.restrict_apply_le _ _
    _ = ENNReal.ofReal m := by rw [Real.volume_Ioo, sub_zero]

/-- At a fixed scale `r`, the bad centres of `B(b,R) ∩ face Q` lie in `2k` clipped strips of
width `L r`, so their volume is at most `k · 2 · L r (2 min(R,ℓ))^{k-1}`. -/
theorem b1hfin_slice_le {n k : ℕ} {L : ℝ} (hL : 0 ≤ L) (H : HorizontalReference n k L)
    (i : H.cubeIndex) (b : Spatial k) {R : ℝ} (hR : 0 ≤ R) {r : ℝ} (hr : 0 ≤ r) :
    volume ({u : Spatial k | (u, r) ∈ b1hfin_bad H i} ∩ (Metric.ball b R ∩ H.face i)) ≤
      ENNReal.ofReal (k * (2 * (L * r *
        (2 * min R (H.gridScale * (2 : ℝ) ^ H.cubeLevel i)) ^ (k - 1)))) := by
  have hℓ0 := (b1hfin_side_pos H i).le
  have hX : 0 ≤ L * r * (2 * min R (H.gridScale * (2 : ℝ) ^ H.cubeLevel i)) ^ (k - 1) := by
    have : 0 ≤ min R (H.gridScale * (2 : ℝ) ^ H.cubeLevel i) := le_min hR hℓ0
    positivity
  have hsub : {u : Spatial k | (u, r) ∈ b1hfin_bad H i} ∩ (Metric.ball b R ∩ H.face i) ⊆
      ⋃ α : Fin k, ({u | u ∈ Metric.ball b R ∩ H.face i ∧ u α ≤ b1hfin_lo H i α + L * r} ∪
        {u | u ∈ Metric.ball b R ∩ H.face i ∧
          b1hfin_lo H i α + H.gridScale * (2 : ℝ) ^ H.cubeLevel i ≤ u α + L * r}) := by
    rintro u ⟨hbad, hu⟩
    obtain ⟨α, hα⟩ := mem_iUnion.1 hbad
    exact mem_iUnion.2 ⟨α, hα.imp (fun h => ⟨hu, h⟩) (fun h => ⟨hu, h⟩)⟩
  have hstrip1 : ∀ α : Fin k,
      volume {u | u ∈ Metric.ball b R ∩ H.face i ∧ u α ≤ b1hfin_lo H i α + L * r} ≤
        ENNReal.ofReal (L * r * (2 * min R (H.gridScale * (2 : ℝ) ^ H.cubeLevel i)) ^ (k - 1)) := by
    intro α
    apply b1hfin_volume_strip_le (b1hfin_lo H i) _ hℓ0 b R hR α (b1hfin_lo H i α) (L * r)
      (mul_nonneg hL hr)
    rintro u ⟨⟨hub, huf⟩, hα⟩
    have hbox := (b1hfin_mem_cube H i u).1 (H.face_subset_cube i huf)
    exact ⟨hub, hbox, (hbox α).1, hα⟩
  have hstrip2 : ∀ α : Fin k,
      volume {u | u ∈ Metric.ball b R ∩ H.face i ∧
          b1hfin_lo H i α + H.gridScale * (2 : ℝ) ^ H.cubeLevel i ≤ u α + L * r} ≤
        ENNReal.ofReal (L * r * (2 * min R (H.gridScale * (2 : ℝ) ^ H.cubeLevel i)) ^ (k - 1)) := by
    intro α
    apply b1hfin_volume_strip_le (b1hfin_lo H i) _ hℓ0 b R hR α
      (b1hfin_lo H i α + H.gridScale * (2 : ℝ) ^ H.cubeLevel i - L * r) (L * r)
      (mul_nonneg hL hr)
    rintro u ⟨⟨hub, huf⟩, hα⟩
    have hbox := (b1hfin_mem_cube H i u).1 (H.face_subset_cube i huf)
    exact ⟨hub, hbox, by linarith, by linarith [(hbox α).2]⟩
  refine (measure_mono hsub).trans ((measure_iUnion_fintype_le volume _).trans
    ((Finset.sum_le_sum fun α _ =>
      (measure_union_le _ _).trans (add_le_add (hstrip1 α) (hstrip2 α))).trans (le_of_eq ?_)))
  rw [Fin.sum_const, ← ENNReal.ofReal_add hX hX, ← two_mul, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg k)]

/-! ## One cube -/

/-- **One cube.** The fine part of the temporal energy over `B(b,R) ∩ face Q` is at most
`K_{k,L} |int Q ∩ B(b,(k+1)R)|` with `K_{k,L} = L^k |B(0,1)| · 2k L 2^{k-1}`. -/
theorem b1hfin_cube_term_le {n k : ℕ} {L : ℝ} (hL : 1 ≤ L) (H : HorizontalReference n k L)
    (i : H.cubeIndex) (b : Spatial k) {R : ℝ} (hR : 0 < R) :
    (∫⁻ u in Metric.ball b R ∩ H.face i,
        ∫⁻ r in Ioo 0 (min R (H.gridScale * (2 : ℝ) ^ H.cubeLevel i)),
          (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
            (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
              ENNReal.ofReal |H.height v - H.height u|) ∂scaleMeasure) ≤
      ENNReal.ofReal (L ^ k * (volume (Metric.ball (0 : Spatial k) 1)).toReal *
          (2 * k * L * 2 ^ (k - 1))) *
        volume (interior (H.cube i) ∩ Metric.ball b ((k + 1) * R)) := by
  rcases (Metric.ball b R ∩ H.face i).eq_empty_or_nonempty with hempty | ⟨q, hqb, hqf⟩
  · rw [hempty, Measure.restrict_empty, lintegral_zero_measure]
    exact zero_le
  have hk : 1 ≤ k := H.available.1
  have hL0 : 0 < L := by linarith
  have hℓ0 := b1hfin_side_pos H i
  have hm0 : 0 < min R (H.gridScale * (2 : ℝ) ^ H.cubeLevel i) := lt_min hR hℓ0
  set m := min R (H.gridScale * (2 : ℝ) ^ H.cubeLevel i) with hm
  have hω0 : 0 ≤ (volume (Metric.ball (0 : Spatial k) 1)).toReal := ENNReal.toReal_nonneg
  set A : ℝ := L ^ k * (volume (Metric.ball (0 : Spatial k) 1)).toReal with hA
  have hA0 : 0 ≤ A := mul_nonneg (pow_nonneg hL0.le k) hω0
  have hBF : MeasurableSet (Metric.ball b R ∩ H.face i) :=
    measurableSet_ball.inter (H.face_measurable i)
  -- Step 1: the cost is at most `A` times the indicator of the bad set.
  have step1 :
      (∫⁻ u in Metric.ball b R ∩ H.face i, ∫⁻ r in Ioo 0 m,
          (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
            (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
              ENNReal.ofReal |H.height v - H.height u|) ∂scaleMeasure) ≤
        ∫⁻ u in Metric.ball b R ∩ H.face i, ∫⁻ r in Ioo 0 m,
          (b1hfin_bad H i).indicator (fun _ => ENNReal.ofReal A) (u, r) ∂scaleMeasure := by
    apply setLIntegral_mono' hBF
    intro u hu
    apply setLIntegral_mono' measurableSet_Ioo
    intro r hr
    exact b1hfin_cost_le_indicator hL H i hu.2 hr.1
  -- Step 2: exchange the centre and scale integrals.
  have hGm : Measurable (Function.uncurry fun (u : Spatial k) (r : ℝ) =>
      (b1hfin_bad H i).indicator (fun _ => ENNReal.ofReal A) (u, r)) :=
    measurable_const.indicator (b1hfin_measurableSet_bad H i)
  have step2 :
      (∫⁻ u in Metric.ball b R ∩ H.face i, ∫⁻ r in Ioo 0 m,
          (b1hfin_bad H i).indicator (fun _ => ENNReal.ofReal A) (u, r) ∂scaleMeasure) =
        ∫⁻ r in Ioo 0 m, (∫⁻ u in Metric.ball b R ∩ H.face i,
          (b1hfin_bad H i).indicator (fun _ => ENNReal.ofReal A) (u, r)) ∂scaleMeasure :=
    lintegral_lintegral_swap hGm.aemeasurable
  -- Step 3: at a fixed scale, the bad centres have volume `O(L r m^{k-1})`.
  have step3 : ∀ r ∈ Ioo 0 m,
      (∫⁻ u in Metric.ball b R ∩ H.face i,
          (b1hfin_bad H i).indicator (fun _ => ENNReal.ofReal A) (u, r)) ≤
        ENNReal.ofReal (A * (k * (2 * (L * (2 * m) ^ (k - 1))))) * ENNReal.ofReal r := by
    intro r hr
    have hslice : MeasurableSet {u : Spatial k | (u, r) ∈ b1hfin_bad H i} :=
      (b1hfin_measurableSet_bad H i).preimage (measurable_id.prodMk measurable_const)
    have heq : (fun u : Spatial k =>
        (b1hfin_bad H i).indicator (fun _ => ENNReal.ofReal A) (u, r)) =
        {u : Spatial k | (u, r) ∈ b1hfin_bad H i}.indicator (fun _ => ENNReal.ofReal A) := by
      funext u
      by_cases hu : (u, r) ∈ b1hfin_bad H i
      · rw [Set.indicator_of_mem hu,
          Set.indicator_of_mem (show u ∈ {u : Spatial k | (u, r) ∈ b1hfin_bad H i} from hu)]
      · rw [Set.indicator_of_notMem hu,
          Set.indicator_of_notMem (show u ∉ {u : Spatial k | (u, r) ∈ b1hfin_bad H i} from hu)]
    rw [heq, lintegral_indicator_const hslice, Measure.restrict_apply hslice]
    have hs := b1hfin_slice_le hL0.le H i b hR.le hr.1.le
    have hY : (0 : ℝ) ≤ A * (k * (2 * (L * (2 * m) ^ (k - 1)))) := by positivity
    calc ENNReal.ofReal A *
          volume ({u : Spatial k | (u, r) ∈ b1hfin_bad H i} ∩ (Metric.ball b R ∩ H.face i))
        ≤ ENNReal.ofReal A * ENNReal.ofReal (k * (2 * (L * r * (2 * m) ^ (k - 1)))) := by
          gcongr
      _ = ENNReal.ofReal (A * (k * (2 * (L * (2 * m) ^ (k - 1))))) * ENNReal.ofReal r := by
          rw [← ENNReal.ofReal_mul hA0, ← ENNReal.ofReal_mul hY]
          congr 1
          ring
  -- Step 4: integrate in the scale, `∫_0^m r dr/r ≤ m`.
  have step4 :
      (∫⁻ r in Ioo 0 m, (∫⁻ u in Metric.ball b R ∩ H.face i,
          (b1hfin_bad H i).indicator (fun _ => ENNReal.ofReal A) (u, r)) ∂scaleMeasure) ≤
        ENNReal.ofReal (A * (k * (2 * (L * (2 * m) ^ (k - 1))))) * ENNReal.ofReal m := by
    calc _ ≤ ∫⁻ r in Ioo 0 m,
            ENNReal.ofReal (A * (k * (2 * (L * (2 * m) ^ (k - 1))))) * ENNReal.ofReal r
              ∂scaleMeasure :=
          setLIntegral_mono' measurableSet_Ioo step3
      _ = ENNReal.ofReal (A * (k * (2 * (L * (2 * m) ^ (k - 1))))) *
            ∫⁻ r in Ioo 0 m, ENNReal.ofReal r ∂scaleMeasure :=
          lintegral_const_mul _ ENNReal.measurable_ofReal
      _ ≤ _ := by
          gcongr
          exact b1hfin_scale_ofReal_le m
  -- Step 5: the inward box of side `m`.
  have hlow : ENNReal.ofReal (m ^ k) ≤
      volume (interior (H.cube i) ∩ Metric.ball b ((k + 1) * R)) := by
    have hqbox := (b1hfin_mem_cube H i q).1 (H.face_subset_cube i hqf)
    refine (b1hfin_volume_inner_box_ge (b1hfin_lo H i) hℓ0 hR b q hqb hqbox).trans
      (measure_mono ?_)
    exact inter_subset_inter_left _ (b1hfin_openBox_subset_interior H i)
  have hreal : A * (k * (2 * (L * (2 * m) ^ (k - 1)))) * m =
      A * (2 * k * L * 2 ^ (k - 1)) * m ^ k := by
    have e1 : (2 * m) ^ (k - 1) * m = 2 ^ (k - 1) * m ^ k := by
      rw [mul_pow, mul_assoc, pow_sub_one_mul (by omega : k ≠ 0)]
    calc A * (k * (2 * (L * (2 * m) ^ (k - 1)))) * m =
          A * (2 * k * L) * ((2 * m) ^ (k - 1) * m) := by ring
      _ = _ := by rw [e1]; ring
  have hK0 : (0 : ℝ) ≤ A * (2 * k * L * 2 ^ (k - 1)) := by positivity
  have hY : (0 : ℝ) ≤ A * (k * (2 * (L * (2 * m) ^ (k - 1)))) := by positivity
  calc _ ≤ _ := step1
    _ = _ := step2
    _ ≤ _ := step4
    _ = ENNReal.ofReal (A * (2 * k * L * 2 ^ (k - 1))) * ENNReal.ofReal (m ^ k) := by
        rw [← ENNReal.ofReal_mul hY, ← ENNReal.ofReal_mul hK0, hreal]
    _ ≤ _ := by gcongr

/-! ## The statement -/

/-- **Fine scales of the temporal energy** (`ba1_horizontal_fine`). -/
theorem ba1_horizontal_fine_proof :
    ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∃ C : ℝ, 0 < C ∧
      ∀ (H : HorizontalReference n k L) (b : Spatial k) (R : ℝ), 0 < R →
        (∑' i : H.cubeIndex, ∫⁻ u in Metric.ball b R ∩ H.face i,
          ∫⁻ r in Ioo 0 (min R (H.gridScale * (2 : ℝ) ^ H.cubeLevel i)),
            (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
              (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
                ENNReal.ofReal |H.height v - H.height u|) ∂scaleMeasure) ≤
          ENNReal.ofReal (C * R ^ k) := by
  intro n k L hL
  have hL0 : 0 < L := by linarith
  have hω0 : 0 ≤ (volume (Metric.ball (0 : Spatial k) 1)).toReal := ENNReal.toReal_nonneg
  have hωfin : volume (Metric.ball (0 : Spatial k) 1) ≠ ∞ := MeasureTheory.measure_ball_ne_top
  have hfr : Module.finrank ℝ (Spatial k) = k := finrank_euclideanSpace_fin
  set ω : ℝ := (volume (Metric.ball (0 : Spatial k) 1)).toReal with hω
  have hK0 : 0 ≤ L ^ k * ω * (2 * k * L * 2 ^ (k - 1)) :=
    mul_nonneg (mul_nonneg (pow_nonneg hL0.le k) hω0) (by positivity)
  set K : ℝ := L ^ k * ω * (2 * k * L * 2 ^ (k - 1)) with hK
  have hC0 : 0 ≤ K * ((k : ℝ) + 1) ^ k * ω :=
    mul_nonneg (mul_nonneg hK0 (by positivity)) hω0
  refine ⟨K * ((k : ℝ) + 1) ^ k * ω + 1, by linarith, ?_⟩
  intro H b R hR
  have hR' : 0 < ((k : ℝ) + 1) * R := by positivity
  have hXk : (0 : ℝ) ≤ (((k : ℝ) + 1) * R) ^ k := by positivity
  calc _ ≤ ∑' i : H.cubeIndex, ENNReal.ofReal K *
          volume (interior (H.cube i) ∩ Metric.ball b ((k + 1) * R)) :=
        ENNReal.tsum_le_tsum fun i => b1hfin_cube_term_le hL H i b hR
    _ = ENNReal.ofReal K *
          volume (⋃ i : H.cubeIndex, interior (H.cube i) ∩ Metric.ball b ((k + 1) * R)) := by
        rw [ENNReal.tsum_mul_left, measure_iUnion]
        · intro i j hij
          exact (H.cube_interior_disjoint i j hij).mono inter_subset_left inter_subset_left
        · intro i
          exact isOpen_interior.measurableSet.inter measurableSet_ball
    _ ≤ ENNReal.ofReal K * volume (Metric.ball b ((k + 1) * R)) := by
        gcongr
        exact iUnion_subset fun i => inter_subset_right
    _ = ENNReal.ofReal (K * (((k : ℝ) + 1) * R) ^ k * ω) := by
        rw [Measure.addHaar_ball_of_pos volume b hR', hfr, ENNReal.ofReal_mul (mul_nonneg hK0 hXk),
          ENNReal.ofReal_mul hK0, hω, ENNReal.ofReal_toReal hωfin]
        ring
    _ ≤ ENNReal.ofReal ((K * ((k : ℝ) + 1) ^ k * ω + 1) * R ^ k) := by
        apply ENNReal.ofReal_le_ofReal
        have hRk : 0 ≤ R ^ k := by positivity
        have e : K * (((k : ℝ) + 1) * R) ^ k * ω = K * ((k : ℝ) + 1) ^ k * ω * R ^ k := by
          rw [mul_pow]
          ring
        rw [e]
        nlinarith

end ParabolicRectifiability.QuantitativeCharacterization
