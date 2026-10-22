import ParabolicRectifiability.Measure.Neck.Definitions
import ParabolicRectifiability.Geometry.Neck.Conclusions

/-!
# Certificates of a constructed neck

The conclusions certified for a neck built from a source measure:

* `NeckRegion.HasParametrization`: the exact center parametrization of the neck's own type;
* `NeckRegion.IsCertified`: the certified geometric and source conclusions of the
  neck built from a Radon source;
* `IsCertifiedCore`: `K` is the core of a certified neck (the per-vertex output of the
  countable neck decomposition).

It also proves the consequences of certification used later:

* `nonempty_horizontalCoreChart_of_restrict`;
* `IsCertifiedCore.isHorizontalCore`, `IsCertifiedCore.isVerticalCore`;
* `IsCertifiedCore.subset_support`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

/-! ## Conclusion shapes -/

namespace NeckRegion

variable {n k : ℕ} {T : NeckType} {ι : Type*} {q : Space n}
  {R c₀ Cd Cs σ δ E κ θ γ : ℝ}

/-- The exact center parametrization of the neck's own type: the
vertical time-preserving parametrization, or the horizontal spatial parametrization
with time defined only on the compact parameter set. -/
def HasParametrization (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ) (Λ : ℝ) : Prop :=
  (T = .horizontal → N.HasHorizontalParametrization Λ) ∧
    (T = .vertical → N.HasVerticalParametrization Λ)

/-- The certified geometric and source conclusions for a neck `N` built
from the source `ν`, with noncollapse level `a`, tail bound `B` and constant `L`:

* the core is compact; the core and all stopping centers have the exact
  parametrization with distortion `L`; local and total joint content are bounded by
  `L`; the core's own Hausdorff measure has upper growth and positive lower density
  almost everywhere;
* core lower bound: `ν(P(z,r)) ≥ a r^k / L` for `z ∈ C₀`, `0 < r ≤ R` (the bound is for
  the source `ν`, not for its core restriction);
* core domination: `H^k_P ⌞ C₀ ≤ (L/a) ν`;
* core square bound: `∫_0^∞ β_{ν,T}(z,r)^2 dr/r ≤ L B` on `C₀`;
* square bound for the core measure: `∫_0^∞ β_{η,T}(z,r)^2 dr/r ≤ L B / a` on `C₀`,
  `η = H^k_P ⌞ C₀`.

All squares use the fixed type of the neck. -/
structure IsCertified (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ)
    (ν : Measure (Space n)) (a B L : ℝ) : Prop where
  isCompact_core : IsCompact N.core
  parametrization : N.HasParametrization L
  localContent : N.HasLocalContentBound L
  totalContent : N.HasTotalContentBound L
  coreDensity : N.HasCoreDensity L
  core_lower : ∀ z ∈ N.core, ∀ r : ℝ, 0 < r → r ≤ R →
    ENNReal.ofReal (a * r ^ k / L) ≤ ν (Metric.ball z r)
  core_domination : (hausdorffP n k).restrict N.core ≤ ENNReal.ofReal (L / a) • ν
  core_square : ∀ z ∈ N.core,
    allScaleEnergy ν k T.toFamilyKind z ≤ ENNReal.ofReal (L * B)
  eta_square : ∀ z ∈ N.core,
    allScaleEnergy ((hausdorffP n k).restrict N.core) k T.toFamilyKind z ≤
      ENNReal.ofReal (L * B / a)

end NeckRegion

/-- `K` is the core of a certified neck of type `T` over the container `P(q,R)`, built
from the source `ν` (the per-vertex output of the neck decomposition, with separation
`c₀ = 1/20` of the stopping centers). -/
def IsCertifiedCore {n : ℕ} (k : ℕ) (T : NeckType) (q : Space n) (R a B L : ℝ)
    (ν : Measure (Space n)) (K : Set (Space n)) : Prop :=
  ∃ (ι : Type) (Cd Cs σ δ E κ θ γ : ℝ)
    (N : NeckRegion n k T ι q R (1 / 20) Cd Cs σ δ E κ θ γ),
    N.core = K ∧ N.IsCertified ν a B L

/-! ## Consequences for the cores -/

/-- Restricting a horizontal center parametrization to the preimage of a closed subset
of its image gives a horizontal core chart. The time function stays defined only on
the compact parameter subset. -/
theorem nonempty_horizontalCoreChart_of_restrict {n k : ℕ} (hk : 1 ≤ k ∧ k ≤ n)
    {Λ : ℝ} (hΛ : 0 < Λ) {G : Spatial k → Spatial n}
    (hG : ∀ u v : Spatial k, Λ⁻¹ * ‖u - v‖ ≤ ‖G u - G v‖ ∧ ‖G u - G v‖ ≤ Λ * ‖u - v‖)
    {A : Set (Spatial k)} {τ : A → ℝ} (hA : IsCompact A)
    (hφ : ∀ u v : A, Λ⁻¹ * dist u v ≤ dist (point (G u) (τ u)) (point (G v) (τ v)) ∧
      dist (point (G u) (τ u)) (point (G v) (τ v)) ≤ Λ * dist u v)
    {K : Set (Space n)} (hK : IsClosed K)
    (hKsub : K ⊆ Set.range (fun u : A => point (G u) (τ u))) :
    Nonempty (HorizontalCoreChart n k K) := by
  have hφlip : LipschitzWith ⟨Λ, hΛ.le⟩ (fun u : A => point (G u) (τ u)) :=
    LipschitzWith.of_dist_le_mul fun u v => (hφ u v).2
  have hGlip : LipschitzWith ⟨Λ, hΛ.le⟩ G :=
    LipschitzWith.of_dist_le_mul fun u v => by
      rw [dist_eq_norm, dist_eq_norm]
      exact (hG u v).2
  have hGanti : AntilipschitzWith ⟨Λ, hΛ.le⟩ G :=
    AntilipschitzWith.of_le_mul_dist fun u v => by
      rw [dist_eq_norm, dist_eq_norm]
      exact (inv_mul_le_iff₀ hΛ).mp (hG u v).1
  have : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have hcpt : IsCompact (Subtype.val '' ((fun u : A => point (G u) (τ u)) ⁻¹' K)) :=
    (hK.preimage hφlip.continuous).isCompact.image continuous_subtype_val
  have hmem : ∀ u : ↥(Subtype.val '' ((fun u : A => point (G u) (τ u)) ⁻¹' K)),
      (u : Spatial k) ∈ A := by
    rintro ⟨u, x, -, rfl⟩
    exact x.2
  refine ⟨{
    dimension := hk
    domain := Subtype.val '' ((fun u : A => point (G u) (τ u)) ⁻¹' K)
    compact_domain := hcpt
    spatial := G
    time := fun u => τ ⟨u.1, hmem u⟩
    constant := ⟨Λ, hΛ.le⟩
    spatial_lipschitz := hGlip
    spatial_antilipschitz := hGanti
    chart_lipschitz := LipschitzWith.of_dist_le_mul fun u v =>
      (hφ ⟨u.1, hmem u⟩ ⟨v.1, hmem v⟩).2
    chart_antilipschitz := AntilipschitzWith.of_le_mul_dist fun u v =>
      (inv_mul_le_iff₀ hΛ).mp (hφ ⟨u.1, hmem u⟩ ⟨v.1, hmem v⟩).1
    image := ?_ }⟩
  ext z
  constructor
  · rintro ⟨⟨u, x, hx, rfl⟩, rfl⟩
    exact hx
  · intro hz
    obtain ⟨x, hx⟩ := hKsub hz
    have hx' : point (G x) (τ x) = z := hx
    have hxK : x ∈ (fun u : A => point (G u) (τ u)) ⁻¹' K := by
      show point (G x) (τ x) ∈ K
      rw [hx']
      exact hz
    exact ⟨⟨x.1, x, hxK, rfl⟩, hx'⟩

/-- A certified horizontal core satisfies the horizontal core hypothesis
`IsHorizontalCore`: compactness, the restricted global spatial
chart with time on the compact core preimage, and the finite own-Hausdorff horizontal
square (from the square bound for the core measure). -/
theorem IsCertifiedCore.isHorizontalCore {n k : ℕ} {q : Space n} {R a B L : ℝ}
    {ν : Measure (Space n)} {K : Set (Space n)}
    (h : IsCertifiedCore k .horizontal q R a B L ν K) (hL : 0 < L) :
    IsHorizontalCore k K := by
  obtain ⟨_, _, _, _, _, _, _, _, _, N, rfl, hN⟩ := h
  have hcompact : IsCompact N.core := hN.isCompact_core
  have hmeas : MeasurableSet N.core := hcompact.isClosed.measurableSet
  obtain ⟨hpar, -⟩ := hN.parametrization
  obtain ⟨G, hG, A, τ, hA, hφ, hrange⟩ := hpar rfl
  have hav : 1 ≤ k ∧ k ≤ n := N.available
  refine ⟨hcompact,
    nonempty_horizontalCoreChart_of_restrict hav hL hG hA hφ hcompact.isClosed ?_, ?_⟩
  · intro z hz
    rw [hrange]
    exact hz.1
  · filter_upwards [ae_restrict_mem hmeas] with z hz
    exact lt_of_le_of_lt
      ((lintegral_mono_set Set.Ioo_subset_Ioi_self).trans (hN.eta_square z hz))
      ENNReal.ofReal_lt_top

/-- A certified vertical core, below the ambient dimension, satisfies the vertical core
hypothesis `IsVerticalCore`: compactness, finite own Hausdorff measure
(total content), upper growth and almost-everywhere positive lower density of its own
Hausdorff measure, and the finite own-Hausdorff
vertical square. The lower density is that of `H^k_P ⌞ C₀`, not of
the source. -/
theorem IsCertifiedCore.isVerticalCore {n k : ℕ} {q : Space n} {R a B L : ℝ}
    {ν : Measure (Space n)} {K : Set (Space n)}
    (h : IsCertifiedCore k .vertical q R a B L ν K) (hk : k < n + 2) (hL : 0 ≤ L) :
    IsVerticalCore k K := by
  obtain ⟨_, _, _, _, _, _, _, _, _, N, rfl, hN⟩ := h
  have hcompact : IsCompact N.core := hN.isCompact_core
  have hmeas : MeasurableSet N.core := hcompact.isClosed.measurableSet
  have hav : 2 ≤ k ∧ k ≤ n + 2 := N.available
  obtain ⟨hup, hlow⟩ := hN.coreDensity
  refine ⟨hav.1, hk, hcompact, ?_, L, 1, hL, one_pos, fun z r hr _ => hup z r hr, ?_⟩
  · exact (le_self_add.trans hN.totalContent).trans_lt ENNReal.ofReal_lt_top
  · filter_upwards [hlow, ae_restrict_mem hmeas] with z hz hzK
    exact ⟨hz, lt_of_le_of_lt
      ((lintegral_mono_set Set.Ioo_subset_Ioi_self).trans (hN.eta_square z hzK))
      ENNReal.ofReal_lt_top⟩

/-- The core of a certified neck lies in the support of its source: the core lower bound
gives positive mass to every small ball about a core point. -/
theorem IsCertifiedCore.subset_support {n k : ℕ} {T : NeckType} {q : Space n}
    {R a B L : ℝ} {ν : Measure (Space n)} {K : Set (Space n)}
    (h : IsCertifiedCore k T q R a B L ν K) (hR : 0 < R) (ha : 0 < a) (hL : 0 < L) :
    K ⊆ ν.support := by
  obtain ⟨_, _, _, _, _, _, _, _, _, N, rfl, hN⟩ := h
  intro z hz
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  have hr : 0 < min ε R := lt_min hε hR
  have hpos : 0 < ENNReal.ofReal (a * min ε R ^ k / L) :=
    ENNReal.ofReal_pos.mpr (div_pos (mul_pos ha (pow_pos hr k)) hL)
  exact (hpos.trans_le (hN.core_lower z hz (min ε R) hr (min_le_right ε R))).trans_le
    (measure_mono ((Metric.ball_subset_ball (min_le_left ε R)).trans hεU))

end ParabolicRectifiability
