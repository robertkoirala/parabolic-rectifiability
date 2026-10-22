import ParabolicRectifiability.Geometry.Neck.ComparisonEnergy
import ParabolicRectifiability.Geometry.SmoothPartition
import ParabolicRectifiability.Geometry.CoherentProjection

/-!
# The coherent chart construction

Definitions for the coherent chart construction underlying `vertical_coherent_chart`:

* the fixed constants `C₀, C₁, C_r, A, C₂, C_a, C_Δ, C_t`, `ε = Aδ/h` and the
  coverage coefficient `η = κ + (5+A)δ/h`, and the three groups of explicit
  smallness conditions (`DeltaSmall`, `EnergySmall`, `CoverageSmall`);
* the level weights `θ_{j,a}`, taken from the smooth partition
  `parabolicWeight r_j I_j z_j`, curried so that they are the weight functions of
  `CoherentProjection.sigma`;
* the stage maps `σ_j` and the recursion `F_0 = x_* + U_* u`,
  `F_{j+1} = σ_j(F_j, t)`;
* the actual tangent space `T_j = range D_u F_j`, activity of an index;
* the local comparison coefficient `e_j(q)` and the path square sum.

The partition constant `C₀` is `partitionConstant n σ ≥ 1`. All other constants are
fixed functions of it, hence of `n` and `σ` only.

The partition's own weights are uncurried functions on `Coordinates n`; the
curried weight `weight F j a x t := parabolicWeight … a (x, t)` below is
definitionally
`curriedWeight (parabolicWeight (F.scale j) (F.index j) (F.center j)) a x t`.
The weight hypotheses are supplied elsewhere:
* first order: `weightBounds_curriedWeight`, `weightBounds_parabolicWeight`,
  `differentiableAt_parabolicWeight_spatial` and `…_time` supply
  `CoherentProjection.WeightBounds` and the differentiability hypotheses of
  `CoherentProjection.one_step`;
* second order (for the Hessian bound `CoherentProjection.hessian_norm_le`):
  spatial `ContDiffAt ℝ 2` and `∑_a ‖D_x²θ_a‖ ≤ C₀/r²`, from the partition's second
  derivative clause (`hessian_norm_le_parabolicWeight`).

Proved here: positivity of the scales, smoothness of every stage
map, existence of an initial parametrization, monotone consistency of the
smallness conditions (`smallness_of_le`, with explicit thresholds), a geometric
displacement sum, the bound
`e_j ≤ δ` (`localError_le`) and the incidence of `e_j` in the ambient comparison
function `E_j` (`localError_zero_le_verticalEnergy`, `localError_succ_le_verticalEnergy`).
-/

noncomputable section

namespace ParabolicRectifiability

namespace CoherentChart

open scoped ENNReal ContDiff
open Filter Topology

variable {n m : ℕ} {ι : Type*}

/-! ## Fixed constants -/

/-- The scale ratio `h = 1/10`. -/
def ratio : ℝ := 1 / 10

/-- The partition constant `C₀ = partitionConstant n σ ≥ 1` of the smooth parabolic partition. -/
def chartC₀ (n : ℕ) (σ : ℝ) : ℝ := partitionConstant n σ

/-- `C₁ = 10 (1 + C₀)²` (projection bound). -/
def chartC₁ (n : ℕ) (σ : ℝ) : ℝ := 10 * (1 + chartC₀ n σ) ^ 2

/-- `C_r = 8 (1 + 5 C₀)` (reset bound). -/
def chartCr (n : ℕ) (σ : ℝ) : ℝ := 8 * (1 + 5 * chartC₀ n σ)

/-- `A = 20 + 2 C_r`. -/
def chartA (n : ℕ) (σ : ℝ) : ℝ := 20 + 2 * chartCr n σ

/-- `C₂ = 2 C₁` (second-derivative bound). -/
def chartC₂ (n : ℕ) (σ : ℝ) : ℝ := 2 * chartC₁ n σ

/-- `C_a = 2 h C₂`. -/
def chartCa (n : ℕ) (σ : ℝ) : ℝ := 2 * ratio * chartC₂ n σ

/-- `C_Δ = 6 C_a + C₀` (increment bound). -/
def chartCΔ (n : ℕ) (σ : ℝ) : ℝ := 6 * chartCa n σ + chartC₀ n σ

/-- `C_t = (2 + C_Δ)/(1 - h)` (time-modulus bound). -/
def chartCt (n : ℕ) (σ : ℝ) : ℝ := (2 + chartCΔ n σ) / (1 - ratio)

/-- `ε = A δ / h`. -/
def chartEps (n : ℕ) (σ δ : ℝ) : ℝ := chartA n σ * δ / ratio

/-- The coverage coefficient `η = κ + (5 + A) δ / h`. -/
def coverageCoeff (n : ℕ) (σ κ δ : ℝ) : ℝ := κ + (5 + chartA n σ) * δ / ratio

/-- The smallness conditions that involve only `δ` and the fixed constants. -/
structure DeltaSmall (n : ℕ) (σ δ : ℝ) : Prop where
  eps_le : chartEps n σ δ ≤ 1 / 100
  quadratic : chartC₁ n σ * chartEps n σ δ ^ 2 ≤ 1 / 2
  contraction : ratio * (1 + chartC₂ n σ * chartEps n σ δ) ≤ 1 / 2
  reset : chartCr n σ * δ ≤ 1 / 10
  taylor : (chartCa n σ / 2 + 2 / (ratio * (1 - ratio))) * chartEps n σ δ ≤ 9 / 100
  time : chartCt n σ * chartEps n σ δ ≤ 9 / 100
  hessian : 6 / 5 * chartCa n σ * chartEps n σ δ / ratio ≤ 1 / 100

/-- The path-energy condition `C₁ A² E / h² ≤ log(1.01)`. -/
def EnergySmall (n : ℕ) (σ E : ℝ) : Prop :=
  chartC₁ n σ * chartA n σ ^ 2 * E / ratio ^ 2 ≤ Real.log (101 / 100)

/-- The coverage condition `η = κ + (5 + A) δ / h ≤ 0.01`. -/
def CoverageSmall (n : ℕ) (σ κ δ : ℝ) : Prop := coverageCoeff n σ κ δ ≤ 1 / 100

/-! ## Weights, stage maps and the recursion -/

section Family

variable (F : CoherentFamily n m ι)

/-- The level-`j` weights `θ_{j,a}(x,t) = ψ_{j,a} f(Ψ_j)`: the smooth partition
weights of radius `r_j`, finite family `I_j` and centers `z_{j,·}`, curried. They
depend only on the level-`j` data, not on any truncation level. -/
def weight (j : ℕ) (a : ι) (x : Spatial n) (t : ℝ) : ℝ :=
  parabolicWeight (F.scale j) (F.index j) (F.center j) a (x, t)

/-- The stage map `σ_j(x,t) = x + ∑_{a ∈ I_j} θ_{j,a}(x,t) (π_{L_{j,a}} x - x)`. -/
def stageMap (j : ℕ) (x : Spatial n) (t : ℝ) : Spatial n :=
  CoherentProjection.sigma (F.index j) (F.plane j) (weight F j) x t

/-- An index is active at `(x,t)` if its weight, its first or second spatial
derivative, or its time derivative is nonzero there. -/
def IsActive (j : ℕ) (a : ι) (x : Spatial n) (t : ℝ) : Prop :=
  CoherentProjection.Active (weight F j) a x t

/-- The initial parametrization data: a point `x_* ∈ L_*` and a linear isometry
`U_* : ℝ^m → ℝ^n` whose image is the direction of `L_*`. -/
structure InitialChart where
  origin : Spatial n
  origin_mem : origin ∈ F.initialPlane.toSet
  isometry : Spatial m →ₗᵢ[ℝ] Spatial n
  range_eq : LinearMap.range isometry.toLinearMap = F.initialPlane.direction

/-- The finite recursion `F_0(u,t) = x_* + U_* u`, `F_{j+1}(u,t) = σ_j(F_j(u,t), t)`.
`stage F P j` is the chart map `F_j`; the finite chart through stage `N + 1` is
`stage F P (N + 1)`. -/
def stage (P : InitialChart F) : ℕ → Spatial m → ℝ → Spatial n
  | 0, u, _ => P.origin + P.isometry u
  | j + 1, u, t => stageMap F j (stage P j u t) t

/-- The path point `q_j = (F_j(u,t), t)`. -/
def pathPoint (P : InitialChart F) (j : ℕ) (u : Spatial m) (t : ℝ) : Space n :=
  point (stage F P j u t) t

/-- The actual tangent space `T_j = range D_u F_j(u,t)`. -/
def tangent (P : InitialChart F) (j : ℕ) (u : Spatial m) (t : ℝ) : Submodule ℝ (Spatial n) :=
  LinearMap.range (fderiv ℝ (fun v => stage F P j v t) u : Spatial m →ₗ[ℝ] Spatial n)

/-! ## The local comparison coefficient and the path square sum -/

/-- The local comparison coefficient `e_j(q)`. It is zero
outside `⋃_{a ∈ I_j} P(z_{j,a}, 3 r_j)`. Inside, `e_0(q)` is the maximum of the
root comparisons with centers within `10 r_0` of `q`, and `e_{j+1}(q)` is the
maximum of the level-`j` same-level comparisons and the `(j, j+1)` adjacent
comparisons whose centers all lie within `8 r_j` of `q` (such pairs are within
`16 r_j < 20 r_j`, so they lie in the comparison ranges). An empty maximum is `0`.
The value is a finite maximum of finite numbers, recorded in `ℝ≥0∞`. -/
def localError : ℕ → Space n → ℝ≥0∞
  | 0, q =>
    ⨆ (_ : ∃ a ∈ F.index 0, dist q (F.center 0 a) < 3 * F.scale 0),
      ⨆ a ∈ F.index 0, ⨆ (_ : dist (F.center 0 a) q ≤ 10 * F.scale 0),
        ENNReal.ofReal
          (planeComparison (F.center 0 a).1 (F.scale 0) (F.plane 0 a) F.initialPlane)
  | j + 1, q =>
    ⨆ (_ : ∃ a ∈ F.index (j + 1), dist q (F.center (j + 1) a) < 3 * F.scale (j + 1)),
      max
        (⨆ a ∈ F.index j, ⨆ b ∈ F.index j,
          ⨆ (_ : dist (F.center j a) q ≤ 8 * F.scale j ∧ dist (F.center j b) q ≤ 8 * F.scale j),
            ENNReal.ofReal
              (planeComparison (F.center j a).1 (F.scale j) (F.plane j a) (F.plane j b)))
        (⨆ a ∈ F.index (j + 1), ⨆ b ∈ F.index j,
          ⨆ (_ : dist (F.center (j + 1) a) q ≤ 8 * F.scale j ∧
              dist (F.center j b) q ≤ 8 * F.scale j),
            ENNReal.ofReal
              (planeComparison (F.center j b).1 (F.scale j) (F.plane (j + 1) a) (F.plane j b)))

/-- The path square sum `∑_{j=0}^{N} e_j(F_j(u,t), t)^2`. -/
def pathSquareSum (P : InitialChart F) (N : ℕ) (u : Spatial m) (t : ℝ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (N + 1), localError F j (pathPoint F P j u t) ^ 2

/-- The path bound `sup_{u,t} ∑_{j=0}^{N} e_j(F_j(u,t), t)^2 ≤ E`.
For `E ≥ 0` this is the usual real bound. The right side is `ENNReal.ofReal E`, so for
`E < 0` the predicate means zero path energy (rather than the impossible real
inequality); the statements using it remain true in that case. -/
def PathBoundUpTo (P : InitialChart F) (E : ℝ) (N : ℕ) : Prop :=
  ∀ (u : Spatial m) (t : ℝ), pathSquareSum F P N u t ≤ ENNReal.ofReal E

/-! ## Proved facts about the definitions -/

theorem ratio_pos : (0 : ℝ) < ratio := by norm_num [ratio]

theorem scale_pos (j : ℕ) : 0 < F.scale j :=
  div_pos F.initialRadius_pos (pow_pos (by norm_num) j)

theorem scale_succ (j : ℕ) : F.scale (j + 1) = ratio * F.scale j := by
  simp only [CoherentFamily.scale, coherentScale, ratio, pow_succ]
  ring

theorem one_le_chartC₀ (n : ℕ) {σ : ℝ} (hσ : 0 < σ) : 1 ≤ chartC₀ n σ :=
  one_le_partitionConstant n hσ

theorem contDiff_weight (j : ℕ) (a : ι) :
    ContDiff ℝ ∞ (fun p : Spatial n × ℝ => weight F j a p.1 p.2) :=
  contDiff_parabolicWeight (F.scale j) (F.index j) (F.center j) a

/-- Smooth input maps stay smooth after a stage map. -/
theorem contDiff_stageMap_comp {g : Spatial m × ℝ → Spatial n} (hg : ContDiff ℝ ∞ g)
    (j : ℕ) : ContDiff ℝ ∞ (fun p => stageMap F j (g p) p.2) := by
  unfold stageMap CoherentProjection.sigma
  refine hg.add (ContDiff.sum fun a _ => ?_)
  refine ((contDiff_weight F j a).comp (hg.prodMk contDiff_snd)).smul ?_
  unfold AffineSpatialPlane.projection
  exact (contDiff_const.add ((F.plane j a).linearProjection.contDiff.comp hg)).sub hg

/-- Every stage map is smooth on the whole parameter space. -/
theorem contDiff_stage (P : InitialChart F) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : Spatial m × ℝ => stage F P j p.1 p.2) := by
  induction j with
  | zero =>
    show ContDiff ℝ ∞ fun p : Spatial m × ℝ => P.origin + P.isometry p.1
    exact contDiff_const.add (P.isometry.toContinuousLinearMap.contDiff.comp contDiff_fst)
  | succ j ih =>
    show ContDiff ℝ ∞ fun p : Spatial m × ℝ => stageMap F j (stage F P j p.1 p.2) p.2
    exact contDiff_stageMap_comp F ih j

/-- An initial parametrization exists: an orthonormal basis of the direction of `L_*`
gives the isometry `U_*`, and the canonical anchor lies on `L_*`. -/
theorem nonempty_initialChart : Nonempty (InitialChart F) := by
  let L := F.initialPlane
  let b := (stdOrthonormalBasis ℝ L.direction).reindex (finCongr L.rank_eq)
  let U : Spatial m →ₗᵢ[ℝ] Spatial n := L.direction.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  refine ⟨⟨L.anchor, L.anchor_mem, U, ?_⟩⟩
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact (b.repr.symm u).2
  · intro hx
    refine ⟨b.repr ⟨x, hx⟩, ?_⟩
    simp [U]

/-- A geometric displacement sum: steps `‖f (i+1) - f i‖ ≤ c r_i` for `k ≤ i < l`
give `‖f l - f k‖ ≤ c r_k / (1 - h)`. -/
theorem norm_sub_le_geometric {E : Type*} [SeminormedAddCommGroup E] (f : ℕ → E) (c : ℝ)
    (hc : 0 ≤ c) {k l : ℕ} (hkl : k ≤ l)
    (hstep : ∀ i, k ≤ i → i < l → ‖f (i + 1) - f i‖ ≤ c * F.scale i) :
    ‖f l - f k‖ ≤ c * F.scale k / (1 - ratio) := by
  -- strengthened claim: ‖f l - f k‖ ≤ (c / (1 - h)) (r_k - r_l)
  have key : ∀ l', k ≤ l' → l' ≤ l →
      ‖f l' - f k‖ ≤ c / (1 - ratio) * (F.scale k - F.scale l') := by
    intro l' hkl' hl'l
    induction l', hkl' using Nat.le_induction with
    | base => simp
    | succ l' hkl' ih =>
      have h1 := ih (Nat.le_of_succ_le hl'l)
      have h2 := hstep l' hkl' (Nat.lt_of_succ_le hl'l)
      have hs := scale_succ F l'
      have hr := scale_pos F l'
      calc ‖f (l' + 1) - f k‖ ≤ ‖f (l' + 1) - f l'‖ + ‖f l' - f k‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ c * F.scale l' + c / (1 - ratio) * (F.scale k - F.scale l') := add_le_add h2 h1
        _ = c / (1 - ratio) * (F.scale k - F.scale (l' + 1)) := by
            rw [hs]; simp only [ratio]; ring
  have hl := key l hkl le_rfl
  have hr := (scale_pos F l).le
  have hc' : 0 ≤ c / (1 - ratio) := div_nonneg hc (by norm_num [ratio])
  calc ‖f l - f k‖ ≤ c / (1 - ratio) * (F.scale k - F.scale l) := hl
    _ ≤ c / (1 - ratio) * F.scale k := mul_le_mul_of_nonneg_left (by linarith) hc'
    _ = c * F.scale k / (1 - ratio) := by ring

end Family

/-! ## The local comparison coefficient: `e_j ≤ δ` and incidence inside `E_j`

The two incidence lemmas carry a level-zero exception: they require
`d_P(q,w) ≤ 2 r_0` at the root and `d_P(q,w) ≤ 4 r_j` at level `j + 1`. -/

/-- Under finite coherence, `e_j ≤ δ` for `j ≤ N`. The pairs used in `e_j`
are within `16 r_{j-1} ≤ 20 r_{j-1}` of each other. -/
theorem localError_le {F : CoherentFamily n m ι} {σ δ : ℝ} {N : ℕ}
    (hF : F.IsCoherentUpTo σ δ N) {j : ℕ} (hj : j ≤ N) (q : Space n) :
    localError F j q ≤ ENNReal.ofReal δ := by
  cases j with
  | zero =>
    simp only [localError]
    refine iSup_le fun _ => iSup₂_le fun a ha => iSup_le fun _ => ?_
    exact ENNReal.ofReal_le_ofReal (hF.root a ha)
  | succ j =>
    have hr := scale_pos F j
    simp only [localError]
    refine iSup_le fun _ => max_le ?_ ?_
    · refine iSup₂_le fun a ha => iSup₂_le fun b hb => iSup_le fun h => ?_
      refine ENNReal.ofReal_le_ofReal (hF.same j (by omega) a ha b hb ?_)
      calc dist (F.center j a) (F.center j b)
          ≤ dist (F.center j a) q + dist (F.center j b) q := dist_triangle_right _ _ _
        _ ≤ 8 * F.scale j + 8 * F.scale j := add_le_add h.1 h.2
        _ ≤ 20 * F.scale j := by linarith
    · refine iSup₂_le fun a ha => iSup₂_le fun b hb => iSup_le fun h => ?_
      refine ENNReal.ofReal_le_ofReal (hF.adjacent j (by omega) a ha b hb ?_)
      calc dist (F.center (j + 1) a) (F.center j b)
          ≤ dist (F.center (j + 1) a) q + dist (F.center j b) q := dist_triangle_right _ _ _
        _ ≤ 8 * F.scale j + 8 * F.scale j := add_le_add h.1 h.2
        _ ≤ 20 * F.scale j := by linarith

/-- Root level: comparisons in `e_0(q)` (centers within `10 r_0`) occur in `E_0(w)`
(centers within `12 r_0`) when `d_P(q,w) ≤ 2 r_0`. -/
theorem localError_zero_le_verticalEnergy (F : CoherentFamily n m ι) {q w : Space n}
    (hqw : dist q w ≤ 2 * F.scale 0) :
    localError F 0 q ≤ F.comparisonEnergy (fun z : Space n => z) 0 w := by
  simp only [localError, CoherentFamily.comparisonEnergy, CoherentFamily.rootComparisonTerm]
  refine iSup_le fun _ => iSup₂_le fun a ha => iSup_le fun h => ?_
  refine le_iSup₂_of_le a ha (le_iSup_of_le ?_ le_rfl)
  calc dist (F.center 0 a) w ≤ dist (F.center 0 a) q + dist q w := dist_triangle _ _ _
    _ ≤ 10 * F.scale 0 + 2 * F.scale 0 := add_le_add h hqw
    _ = 12 * F.scale 0 := by ring

/-- Later levels: comparisons in `e_{j+1}(q)` (centers within `8 r_j`) occur in
`E_{j+1}(w)` (pairs within `20 r_j`, centers within `12 r_j`) when `d_P(q,w) ≤ 4 r_j`. -/
theorem localError_succ_le_verticalEnergy (F : CoherentFamily n m ι) (j : ℕ) {q w : Space n}
    (hqw : dist q w ≤ 4 * F.scale j) :
    localError F (j + 1) q ≤ F.comparisonEnergy (fun z : Space n => z) (j + 1) w := by
  have hr := scale_pos F j
  simp only [localError, CoherentFamily.comparisonEnergy,
    CoherentFamily.sameLevelComparisonTerm, CoherentFamily.adjacentComparisonTerm]
  refine iSup_le fun _ => max_le_max ?_ ?_
  · refine iSup₂_le fun a ha => iSup₂_le fun b hb => iSup_le fun h => ?_
    refine le_iSup₂_of_le a ha (le_iSup₂_of_le b hb (le_iSup_of_le ⟨?_, ?_, ?_⟩ le_rfl))
    · calc dist (F.center j a) (F.center j b)
          ≤ dist (F.center j a) q + dist (F.center j b) q := dist_triangle_right _ _ _
        _ ≤ 8 * F.scale j + 8 * F.scale j := add_le_add h.1 h.2
        _ ≤ 20 * F.scale j := by linarith
    · calc dist (F.center j a) w ≤ dist (F.center j a) q + dist q w := dist_triangle _ _ _
        _ ≤ 8 * F.scale j + 4 * F.scale j := add_le_add h.1 hqw
        _ = 12 * F.scale j := by ring
    · calc dist (F.center j b) w ≤ dist (F.center j b) q + dist q w := dist_triangle _ _ _
        _ ≤ 8 * F.scale j + 4 * F.scale j := add_le_add h.2 hqw
        _ = 12 * F.scale j := by ring
  · refine iSup₂_le fun a ha => iSup₂_le fun b hb => iSup_le fun h => ?_
    refine le_iSup₂_of_le a ha (le_iSup₂_of_le b hb (le_iSup_of_le ⟨?_, ?_, ?_⟩ le_rfl))
    · calc dist (F.center (j + 1) a) (F.center j b)
          ≤ dist (F.center (j + 1) a) q + dist (F.center j b) q := dist_triangle_right _ _ _
        _ ≤ 8 * F.scale j + 8 * F.scale j := add_le_add h.1 h.2
        _ ≤ 20 * F.scale j := by linarith
    · calc dist (F.center (j + 1) a) w
          ≤ dist (F.center (j + 1) a) q + dist q w := dist_triangle _ _ _
        _ ≤ 8 * F.scale j + 4 * F.scale j := add_le_add h.1 hqw
        _ = 12 * F.scale j := by ring
    · calc dist (F.center j b) w ≤ dist (F.center j b) q + dist q w := dist_triangle _ _ _
        _ ≤ 8 * F.scale j + 4 * F.scale j := add_le_add h.2 hqw
        _ = 12 * F.scale j := by ring

/-! ## Consistency of the smallness conditions -/

/-- A common upper bound for the fixed constants. -/
def chartK (n : ℕ) (σ : ℝ) : ℝ :=
  1 + chartC₁ n σ + chartC₂ n σ + chartCr n σ + chartCa n σ + chartCt n σ + chartA n σ

section Consistency

variable {σ : ℝ}

/-- Signs of the fixed constants: `C₀ ≥ 1`, `A ≥ 20`, all others nonnegative. -/
theorem chartConsts_bounds (hσ : 0 < σ) :
    1 ≤ chartC₀ n σ ∧ 0 ≤ chartC₁ n σ ∧ 0 ≤ chartC₂ n σ ∧ 0 ≤ chartCr n σ ∧
      0 ≤ chartCa n σ ∧ 0 ≤ chartCΔ n σ ∧ 0 ≤ chartCt n σ ∧ 20 ≤ chartA n σ := by
  have h0 := one_le_chartC₀ n hσ
  have h1 : 0 ≤ chartC₁ n σ := by unfold chartC₁; positivity
  have h2 : 0 ≤ chartC₂ n σ := by unfold chartC₂ chartC₁; positivity
  have hr : 0 ≤ chartCr n σ := by unfold chartCr; linarith
  have ha : 0 ≤ chartCa n σ := by unfold chartCa ratio chartC₂ chartC₁; positivity
  have hd : 0 ≤ chartCΔ n σ := by unfold chartCΔ; linarith
  have ht : 0 ≤ chartCt n σ := by
    unfold chartCt ratio; apply div_nonneg <;> linarith
  have hA : 20 ≤ chartA n σ := by unfold chartA; linarith
  exact ⟨h0, h1, h2, hr, ha, hd, ht, hA⟩

private theorem one_le_chartK (hσ : 0 < σ) : 1 ≤ chartK n σ := by
  obtain ⟨-, h1, h2, hr, ha, -, ht, hA⟩ := chartConsts_bounds (n := n) hσ
  unfold chartK; linarith

/-- The explicit coherence threshold `δ₀ = 1 / (10⁵ K²)`. -/
def deltaThreshold (n : ℕ) (σ : ℝ) : ℝ := 1 / (10 ^ 5 * chartK n σ ^ 2)

/-- The explicit energy threshold `E₀ = h² log(1.01) / (C₁ A²)`. -/
def energyThreshold (n : ℕ) (σ : ℝ) : ℝ :=
  ratio ^ 2 * Real.log (101 / 100) / (chartC₁ n σ * chartA n σ ^ 2)

/-- The coverage threshold `κ₀ = 1/200`. -/
def heightThreshold : ℝ := 1 / 200

theorem deltaThreshold_pos (hσ : 0 < σ) : 0 < deltaThreshold n σ := by
  have hK : 0 < chartK n σ := lt_of_lt_of_le one_pos (one_le_chartK hσ)
  exact div_pos one_pos (mul_pos (by norm_num) (pow_pos hK 2))

theorem energyThreshold_pos (hσ : 0 < σ) : 0 < energyThreshold n σ := by
  obtain ⟨h0, -, -, -, -, -, -, hA⟩ := chartConsts_bounds (n := n) hσ
  have h1 : 0 < chartC₁ n σ := by
    unfold chartC₁; exact mul_pos (by norm_num) (pow_pos (by linarith) 2)
  have hlog : 0 < Real.log (101 / 100 : ℝ) := Real.log_pos (by norm_num)
  exact div_pos (mul_pos (by norm_num [ratio]) hlog)
    (mul_pos h1 (pow_pos (by linarith) 2))

theorem chartEps_eq (δ : ℝ) : chartEps n σ δ = 10 * chartA n σ * δ := by
  unfold chartEps ratio; ring

theorem chartEps_nonneg (hσ : 0 < σ) {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ chartEps n σ δ := by
  obtain ⟨-, -, -, -, -, -, -, hA⟩ := chartConsts_bounds (n := n) hσ
  rw [chartEps_eq]
  exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hδ

/-- `ε K ≤ 10⁻⁴` below the coherence threshold. -/
private theorem eps_mul_K_le (hσ : 0 < σ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hδ₀ : δ ≤ deltaThreshold n σ) :
    0 ≤ chartEps n σ δ ∧ chartEps n σ δ * chartK n σ ≤ 1 / 10 ^ 4 := by
  obtain ⟨-, h1, h2, hr, ha, -, ht, hA⟩ := chartConsts_bounds (n := n) hσ
  have hK := one_le_chartK (n := n) hσ
  have hKpos : 0 < chartK n σ := by linarith
  have hAK : chartA n σ ≤ chartK n σ := by unfold chartK; linarith
  have hX : (0 : ℝ) < 10 ^ 5 * chartK n σ ^ 2 := mul_pos (by norm_num) (pow_pos hKpos 2)
  have hδK : δ * (10 ^ 5 * chartK n σ ^ 2) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hδ₀ hX.le
    rwa [deltaThreshold, one_div_mul_cancel hX.ne'] at this
  rw [chartEps_eq]
  refine ⟨mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hδ, ?_⟩
  have h3 : chartA n σ * (10 * δ * chartK n σ) ≤ chartK n σ * (10 * δ * chartK n σ) :=
    mul_le_mul_of_nonneg_right hAK (mul_nonneg (mul_nonneg (by norm_num) hδ) hKpos.le)
  nlinarith

/-- **The smallness conditions are consistent**, with explicit thresholds:
below `δ₀ = 1/(10⁵K²)`, `E₀ = h² log(1.01)/(C₁A²)` and `κ₀ = 1/200`, all three groups
of smallness conditions hold, and moreover `(5 + A) δ / h ≤ 1/200`. The
thresholds depend only on `n` and `σ` and are independent of each other. -/
theorem smallness_of_le (hσ : 0 < σ) {δ E κ : ℝ} (hδ : 0 ≤ δ) (hδ₀ : δ ≤ deltaThreshold n σ)
    (hE₀ : E ≤ energyThreshold n σ) (hκ₀ : κ ≤ heightThreshold) :
    DeltaSmall n σ δ ∧ EnergySmall n σ E ∧ CoverageSmall n σ κ δ ∧
      (5 + chartA n σ) * δ / ratio ≤ 1 / 200 := by
  obtain ⟨h0, h1, h2, hr, ha, hd, ht, hA⟩ := chartConsts_bounds (n := n) hσ
  obtain ⟨he0, heK⟩ := eps_mul_K_le (n := n) hσ hδ hδ₀
  have hK := one_le_chartK (n := n) hσ
  have hmul : ∀ c : ℝ, c ≤ chartK n σ → c * chartEps n σ δ ≤ 1 / 10 ^ 4 := by
    intro c hc
    have := mul_le_mul_of_nonneg_right hc he0
    nlinarith
  have hc1 := hmul _ (by unfold chartK; linarith : chartC₁ n σ ≤ chartK n σ)
  have hc2 := hmul _ (by unfold chartK; linarith : chartC₂ n σ ≤ chartK n σ)
  have hcr := hmul _ (by unfold chartK; linarith : chartCr n σ ≤ chartK n σ)
  have hca := hmul _ (by unfold chartK; linarith : chartCa n σ ≤ chartK n σ)
  have hct := hmul _ (by unfold chartK; linarith : chartCt n σ ≤ chartK n σ)
  have he_le := hmul 1 (by linarith)
  rw [one_mul] at he_le
  have heA := chartEps_eq (n := n) (σ := σ) δ
  have hδe : 200 * δ ≤ chartEps n σ δ := by rw [heA]; nlinarith
  have hcov : (5 + chartA n σ) * δ / ratio ≤ 1 / 200 := by
    unfold ratio
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, hcov⟩
  · linarith
  · nlinarith
  · unfold ratio; nlinarith
  · nlinarith
  · have h29 : 2 / (ratio * (1 - ratio)) = 200 / 9 := by unfold ratio; norm_num
    rw [h29]; nlinarith
  · linarith
  · unfold ratio; nlinarith
  · unfold EnergySmall
    unfold energyThreshold at hE₀
    have h1pos : 0 < chartC₁ n σ := by
      unfold chartC₁; exact mul_pos (by norm_num) (pow_pos (by linarith) 2)
    have hden : 0 < chartC₁ n σ * chartA n σ ^ 2 := mul_pos h1pos (pow_pos (by linarith) 2)
    have hr2 : (0 : ℝ) < ratio ^ 2 := by unfold ratio; norm_num
    rw [div_le_iff₀ hr2]
    rw [le_div_iff₀ hden] at hE₀
    calc chartC₁ n σ * chartA n σ ^ 2 * E = E * (chartC₁ n σ * chartA n σ ^ 2) := by ring
      _ ≤ ratio ^ 2 * Real.log (101 / 100) := hE₀
      _ = Real.log (101 / 100) * ratio ^ 2 := by ring
  · unfold CoverageSmall coverageCoeff
    unfold heightThreshold at hκ₀
    linarith

end Consistency

end CoherentChart

end ParabolicRectifiability
