import ParabolicRectifiability.Geometry.Neck.CollapseLowerModel

/-!
# Finite cell covers of tubes

Elementary tools for the collapsed and terminal tube covers:

* `gm2_holeChildren_of_key`: a Borel assignment `A` with a measurable discarded part `D`
  and a finite-valued measurable cell index on `A \ D`, whose cells have diameter `< R`,
  has `HoleChildren` of radius `R` with discard `D`, one child per occupied cell,
  centered at a retained point of that cell;
* floor cells `gm2_cell e x₀ h x = (⌊⟪e i, x - x₀⟫ / h⌋)_i` in finitely many unit
  coordinates, their range in a ball and the closeness of two points in one cell;
* the projection onto a plane of rank `m` changes by at most `m h` inside one cell of an
  orthonormal basis of its direction;
* Chebyshev's inequality for the discarded tube complement.

The counting is by cells of a grid in the coordinates of the model plane: a cell of
side `h` in `m` plane coordinates of a ball of radius `d` gives at most `(2⌈d/h⌉)^m`
cells, with no volume argument.
-/

noncomputable section

namespace ParabolicRectifiability

namespace ChargeCollapse

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

/-! ## Children from a finite cell index -/

/-- If the retained part `A \ D` has a measurable cell index with values in a finite set
`S`, and two retained points in one cell are at distance `< R`, then `A` has children of
radius `R` with discarded part `D`, one per occupied cell, centered at a retained point
of that cell. -/
theorem gm2_holeChildren_of_key {n : ℕ} {κ : Type*} (ν : Measure (Space n))
    {A D : Set (Space n)} (hA : MeasurableSet A) (hD : MeasurableSet D) (hDA : D ⊆ A)
    {R : ℝ} (key : Space n → κ) (hkey : ∀ a, MeasurableSet (key ⁻¹' {a})) (S : Finset κ)
    (hS : ∀ z ∈ A \ D, key z ∈ S)
    (hclose : ∀ z ∈ A \ D, ∀ w ∈ A \ D, key z = key w → dist z w < R) :
    ∃ Hc : HoleChildren ν A R, Hc.discard = D ∧ Hc.count ≤ S.card := by
  classical
  let S' := S.filter (fun a => ∃ z ∈ A \ D, key z = a)
  have hwit : ∀ a : S', ∃ z, z ∈ A \ D ∧ key z = a := fun a => by
    obtain ⟨z, hz, hza⟩ := (Finset.mem_filter.1 a.2).2
    exact ⟨z, hz, hza⟩
  let e : Fin S'.card ≃ S' := S'.equivFin.symm
  let ctr : Fin S'.card → Space n := fun i => Classical.choose (hwit (e i))
  have hctr : ∀ i, ctr i ∈ A \ D ∧ key (ctr i) = e i := fun i =>
    Classical.choose_spec (hwit (e i))
  refine ⟨{ count := S'.card
            discard := D
            center := ctr
            childSet := fun i => (A \ D) ∩ key ⁻¹' {((e i : S') : κ)}
            measurableSet_discard := hD
            measurableSet_childSet := fun i => (hA.diff hD).inter (hkey _)
            discard_subset := hDA
            childSet_subset := fun i => inter_subset_left.trans Set.sdiff_subset
            center_mem := fun i => (hctr i).1.1
            childSet_subset_ball := ?_
            cover := ?_
            disjoint_discard := ?_
            disjoint_childSet := ?_ }, rfl, Finset.card_filter_le _ _⟩
  · intro i z hz
    rw [Metric.mem_ball]
    exact hclose z hz.1 (ctr i) (hctr i).1
      ((show key z = ((e i : S') : κ) from hz.2).trans (hctr i).2.symm)
  · intro z hz
    by_cases hzD : z ∈ D
    · exact Or.inl hzD
    · have hzr : z ∈ A \ D := ⟨hz, hzD⟩
      have hmem : key z ∈ S' := Finset.mem_filter.2 ⟨hS z hzr, z, hzr, rfl⟩
      refine Or.inr (mem_iUnion.2 ⟨e.symm ⟨key z, hmem⟩, hzr, ?_⟩)
      show key z = ((e (e.symm ⟨key z, hmem⟩) : S') : κ)
      rw [e.apply_symm_apply]
  · intro i
    exact Set.disjoint_left.2 fun z hzD hz => hz.1.2 hzD
  · intro i j hij
    refine Set.disjoint_left.2 fun z hzi hzj => hij (e.injective (Subtype.ext ?_))
    exact (show key z = ((e i : S') : κ) from hzi.2).symm.trans hzj.2

/-! ## Floor cells -/

/-- Equal floors at spacing `h` give a difference below `h`. -/
theorem gm2_abs_sub_lt_of_floor_eq {a a' h : ℝ} (hh : 0 < h) (heq : ⌊a / h⌋ = ⌊a' / h⌋) :
    |a - a'| < h := by
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor heq
  rwa [← sub_div, abs_div, abs_of_pos hh, div_lt_one hh] at h1

/-- The floor cell of a number of modulus `< D` lies in `[-⌈y⌉, ⌈y⌉)` once `D/h ≤ y`. -/
theorem gm2_floor_mem_Ico {a D h y : ℝ} (hh : 0 < h) (ha : |a| < D) (hy : D / h ≤ y) :
    ⌊a / h⌋ ∈ Finset.Ico (-(⌈y⌉₊ : ℤ)) (⌈y⌉₊ : ℤ) := by
  have hlt : |a / h| < D / h := by
    rw [abs_div, abs_of_pos hh]
    exact div_lt_div_of_pos_right ha hh
  have hc : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
  rw [abs_lt] at hlt
  rw [Finset.mem_Ico, Int.le_floor, Int.floor_lt]
  push_cast
  constructor <;> linarith

/-- The cell of `x` in the coordinates `⟪e i, x - x₀⟫` at spacing `h`. -/
def gm2_cell {n : ℕ} {ι : Type*} (e : ι → Spatial n) (x₀ : Spatial n) (h : ℝ)
    (x : Spatial n) : ι → ℤ :=
  fun i => ⌊⟪e i, x - x₀⟫ / h⌋

/-- Two points in one cell have coordinate differences below `h`. -/
theorem gm2_cell_close {n : ℕ} {ι : Type*} {e : ι → Spatial n} {x₀ : Spatial n} {h : ℝ}
    (hh : 0 < h) {x x' : Spatial n} (heq : gm2_cell e x₀ h x = gm2_cell e x₀ h x') (i : ι) :
    |⟪e i, x - x'⟫| < h := by
  have h0 : ⌊⟪e i, x - x₀⟫ / h⌋ = ⌊⟪e i, x' - x₀⟫ / h⌋ := congrFun heq i
  have h1 := gm2_abs_sub_lt_of_floor_eq hh h0
  rwa [← inner_sub_right, sub_sub_sub_cancel_right] at h1

/-- The cells of a ball of radius `D` in unit coordinates lie in a box. -/
theorem gm2_cell_mem {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → Spatial n}
    (he : ∀ i, ‖e i‖ ≤ 1) {x₀ x : Spatial n} {h D y : ℝ} (hh : 0 < h) (hx : ‖x - x₀‖ < D)
    (hy : D / h ≤ y) :
    gm2_cell e x₀ h x ∈ Fintype.piFinset fun _ : ι => Finset.Ico (-(⌈y⌉₊ : ℤ)) (⌈y⌉₊ : ℤ) := by
  rw [Fintype.mem_piFinset]
  intro i
  refine gm2_floor_mem_Ico hh ?_ hy
  calc |⟪e i, x - x₀⟫| ≤ ‖e i‖ * ‖x - x₀‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 * ‖x - x₀‖ := mul_le_mul_of_nonneg_right (he i) (norm_nonneg _)
    _ < D := by rwa [one_mul]

/-- The number of cells in the box. -/
theorem gm2_card_box (m N : ℕ) :
    (Fintype.piFinset fun _ : Fin m => Finset.Ico (-(N : ℤ)) (N : ℤ)).card = (2 * N) ^ m := by
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Int.card_Ico]
  have h : ((N : ℤ) - -(N : ℤ)) = ((2 * N : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-- The time cells. -/
theorem gm2_card_Ico (N : ℕ) : (Finset.Ico (-(N : ℤ)) (N : ℤ)).card = 2 * N := by
  rw [Int.card_Ico]
  have h : ((N : ℤ) - -(N : ℤ)) = ((2 * N : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-- A cell index of a continuous map is measurable. -/
theorem gm2_measurable_cell {n : ℕ} {ι : Type*} (e : ι → Spatial n) (x₀ : Spatial n) (h : ℝ)
    {f : Space n → Spatial n} (hf : Continuous f) :
    Measurable fun z => gm2_cell e x₀ h (f z) := by
  refine Measurable.of_eval fun i => ?_
  show Measurable fun z => ⌊⟪e i, f z - x₀⟫ / h⌋
  exact ((continuous_const.inner (hf.sub continuous_const)).div_const h).measurable.floor

/-! ## Norms through orthonormal coordinates -/

/-- `‖P_U v‖ ≤ ∑ |⟪b i, v⟫|` for an orthonormal basis `b` of `U`. -/
theorem gm2_norm_starProjection_le {n : ℕ} {ι : Type*} [Fintype ι]
    (U : Submodule ℝ (Spatial n)) [U.HasOrthogonalProjection] (b : OrthonormalBasis ι ℝ U)
    (v : Spatial n) : ‖U.starProjection v‖ ≤ ∑ i, |⟪(b i : Spatial n), v⟫| := by
  rw [b.starProjection_eq_sum_rankOne, _root_.sum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [InnerProductSpace.rankOne_apply, norm_smul, Real.norm_eq_abs]
  have h1 : ‖(b i : Spatial n)‖ = 1 := b.orthonormal.1 i
  rw [h1, mul_one]

/-- `‖v‖ ≤ ∑ |⟪b i, v⟫|` for an orthonormal basis `b` of the whole space. -/
theorem gm2_norm_le_sum {n : ℕ} {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (Spatial n))
    (v : Spatial n) : ‖v‖ ≤ ∑ i, |⟪b i, v⟫| := by
  conv_lhs => rw [← b.sum_repr' v]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, Real.norm_eq_abs, b.orthonormal.1 i, mul_one]

/-- A sum of `|c i| < h` is at most `card ι * h`. -/
theorem gm2_sum_abs_le {ι : Type*} [Fintype ι] {c : ι → ℝ} {h : ℝ} (hc : ∀ i, |c i| < h) :
    ∑ i, |c i| ≤ Fintype.card ι * h := by
  calc ∑ i, |c i| ≤ ∑ _i : ι, h := Finset.sum_le_sum fun i _ => (hc i).le
    _ = Fintype.card ι * h := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Unit coordinate vectors along the direction of a plane. -/
def gm2_planeBasis {n m : ℕ} (L : AffineSpatialPlane n m) :
    Fin (Module.finrank ℝ L.direction) → Spatial n :=
  fun i => (stdOrthonormalBasis ℝ L.direction i : Spatial n)

theorem gm2_planeBasis_norm {n m : ℕ} (L : AffineSpatialPlane n m)
    (i : Fin (Module.finrank ℝ L.direction)) : ‖gm2_planeBasis L i‖ ≤ 1 :=
  ((stdOrthonormalBasis ℝ L.direction).orthonormal.1 i).le

/-- Inside one plane cell of spacing `h`, the projection to a plane of rank `m` moves by
at most `m h`. -/
theorem gm2_projection_close {n m : ℕ} (L : AffineSpatialPlane n m) {x₀ x x' : Spatial n}
    {h : ℝ} (hh : 0 < h)
    (heq : gm2_cell (gm2_planeBasis L) x₀ h x = gm2_cell (gm2_planeBasis L) x₀ h x') :
    ‖L.projection x - L.projection x'‖ ≤ m * h := by
  have hdiff : L.projection x - L.projection x' = L.direction.starProjection (x - x') := by
    simp only [AffineSpatialPlane.projection, AffineSpatialPlane.linearProjection, map_sub]
    abel
  rw [hdiff]
  refine (gm2_norm_starProjection_le L.direction (stdOrthonormalBasis ℝ L.direction)
    (x - x')).trans ?_
  refine (gm2_sum_abs_le fun i => gm2_cell_close hh heq i).trans ?_
  rw [Fintype.card_fin, L.rank_eq]

/-- Two points within `a` of a plane and in one plane cell are within `2a + m h`. -/
theorem gm2_plane_cell_close {n m : ℕ} (L : AffineSpatialPlane n m) {x₀ x x' : Spatial n}
    {h a : ℝ} (hh : 0 < h)
    (heq : gm2_cell (gm2_planeBasis L) x₀ h x = gm2_cell (gm2_planeBasis L) x₀ h x')
    (hx : ‖x - L.projection x‖ < a) (hx' : ‖x' - L.projection x'‖ < a) :
    ‖x - x'‖ < 2 * a + m * h := by
  have hp := gm2_projection_close L hh heq
  calc ‖x - x'‖ ≤ ‖x - L.projection x‖ + ‖L.projection x - x'‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖x - L.projection x‖ + (‖L.projection x - L.projection x'‖ +
          ‖L.projection x' - x'‖) := by
        gcongr
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖x - L.projection x‖ + ‖L.projection x - L.projection x'‖ +
          ‖x' - L.projection x'‖ := by rw [norm_sub_rev (L.projection x') x', add_assoc]
    _ < 2 * a + m * h := by linarith

/-! ## Metric facts -/

theorem gm2_mem_ball {n : ℕ} {c z : Space n} {d : ℝ} (hd : 0 < d)
    (hz : z ∈ Metric.ball c d) : ‖z.1 - c.1‖ < d ∧ |z.2.val - c.2.val| < d ^ 2 := by
  rw [Metric.mem_ball, gm2_dist_eq, max_lt_iff, Real.sqrt_lt' hd] at hz
  exact hz

theorem gm2_dist_lt {n : ℕ} {z w : Space n} {R : ℝ} (hR : 0 < R) (h1 : ‖z.1 - w.1‖ < R)
    (h2 : |z.2.val - w.2.val| < R ^ 2) : dist z w < R := by
  rw [gm2_dist_eq, max_lt_iff, Real.sqrt_lt' hR]
  exact ⟨h1, h2⟩

/-- A point whose squared distance to `M` is below `r^2` has a point of `M` within `r`. -/
theorem gm2_exists_near {n : ℕ} (M : Set (Space n)) (z : Space n) {r : ℝ} (hr : 0 < r)
    (h : ¬ ENNReal.ofReal (r ^ 2) ≤ Metric.infEDist z M ^ 2) : ∃ w ∈ M, dist z w < r := by
  have h1 : Metric.infEDist z M < ENNReal.ofReal r := by
    by_contra hc
    apply h
    rw [ENNReal.ofReal_pow hr.le]
    exact pow_le_pow_left₀ zero_le (not_lt.1 hc) 2
  obtain ⟨w, hw, hzw⟩ := Metric.infEDist_lt_iff.1 h1
  refine ⟨w, hw, ?_⟩
  rwa [edist_dist, ENNReal.ofReal_lt_ofReal_iff hr] at hzw

/-! ## Chebyshev for the discarded part -/

theorem gm2_measure_le_of_lintegral {n : ℕ} (ν : Measure (Space n)) {A : Set (Space n)}
    {f : Space n → ℝ≥0∞} (hf : Measurable f) {ε X : ℝ} (hε : 0 < ε)
    (hint : ∫⁻ z in A, f z ∂ν ≤ ENNReal.ofReal X) :
    ν (A ∩ {z | ENNReal.ofReal ε ≤ f z}) ≤ ENNReal.ofReal (X / ε) := by
  have h1 : ν (A ∩ {z | ENNReal.ofReal ε ≤ f z}) * ENNReal.ofReal ε ≤ ENNReal.ofReal X := by
    calc ν (A ∩ {z | ENNReal.ofReal ε ≤ f z}) * ENNReal.ofReal ε
        = ∫⁻ _z in A ∩ {z | ENNReal.ofReal ε ≤ f z}, ENNReal.ofReal ε ∂ν := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ z in A ∩ {z | ENNReal.ofReal ε ≤ f z}, f z ∂ν :=
          setLIntegral_mono hf fun z hz => hz.2
      _ ≤ ∫⁻ z in A, f z ∂ν := lintegral_mono_set inter_subset_left
      _ ≤ ENNReal.ofReal X := hint
  rw [ENNReal.ofReal_div_of_pos hε, ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_pos.2 hε).ne') (Or.inl ENNReal.ofReal_ne_top)]
  exact h1

/-! ## Counting -/

/-- `m · s/(m+1) ≤ s`. -/
theorem gm2_mul_spacing_le (m : ℕ) {s : ℝ} (hs : 0 ≤ s) : (m : ℝ) * (s / (m + 1)) ≤ s := by
  have h1 : (m : ℝ) * (s / (m + 1)) = s * (m / (m + 1)) := by ring
  have h2 : (m : ℝ) / (m + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  rw [h1]
  calc s * (m / (m + 1)) ≤ s * 1 := by gcongr
    _ = s := mul_one s

/-- `(2⌈y/ρ⌉)^p ρ^p ≤ (2(y+1))^p` for `0 < ρ ≤ 1`. -/
theorem gm2_pow_bound {ρ y : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hy : 0 ≤ y) (p : ℕ) :
    (2 * (⌈y / ρ⌉₊ : ℝ)) ^ p * ρ ^ p ≤ (2 * (y + 1)) ^ p := by
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have hc : (⌈y / ρ⌉₊ : ℝ) < y / ρ + 1 := Nat.ceil_lt_add_one (div_nonneg hy hρ.le)
  calc 2 * (⌈y / ρ⌉₊ : ℝ) * ρ ≤ 2 * (y / ρ + 1) * ρ := by gcongr
    _ = 2 * (y / ρ * ρ) + 2 * ρ := by ring
    _ = 2 * y + 2 * ρ := by rw [div_mul_cancel₀ y hρ.ne']
    _ ≤ 2 * (y + 1) := by linarith

end ChargeCollapse

end ParabolicRectifiability
