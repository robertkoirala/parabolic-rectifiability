import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reverse.CouplingAllocation

/-! # The buffered allocation in kernel form

Proof of `d2_coupling_of_parts` under the name `d2_coupling_of_parts_proof`, with its implication
type over the named statements of the reverse bound (cells, Hall inequality, on-carrier comparison
and kernel of a partition).

* **Partition-bind identity** (`d2cpl_bind_partition`): for a kernel equal to `τ_j`
  on disjoint measurable `P_j` and to `δ_y` off their union,
  `λ.bind κ = Σ_j λ(P_j) τ_j + λ⌊(⋃_j P_j)ᶜ`.
* **Exact marginal identity** (`d2cpl_marginal_eq`): after omitting the zero-mass
  cells, `(μ⌊P(c,2ρ)).bind κ = Σ_{j∈J} σ.withDensity h_j + μ⌊(Γ ∩ P(c,2ρ))`; the normalization
  uses `0 < μ(Q'_j) < ∞`, and the omitted-cell remainder is null by countability.
* **Every-point displacement** (`d2cpl_displacement`): for every `y`, `κ_y`-a.e.
  `d(y,v) ≤ (C₀ + 1) d(y,Γ)`; on a positive cell `τ_j` is carried by `E_j = Γ ∩ P̄(g_j,s_j)`, and
  off the positive cells `κ_y = δ_y`. This is the stronger condition of the constructed kernel,
  not a claim about an arbitrary disintegration.
* **Domination**: `Σ_j σ.withDensity h_j ≤ D₁ σ` (a.e. capacity bound) and the on-carrier
  comparison `μ⌊(Γ ∩ P(c,2ρ)) ≤ D σ` give `(μ⌊P(c,2ρ)).bind κ ≤ (D + D₁) σ`.

Constants (see the statement docstring): `C₀` from the cells statement,
`Ch` from the Hall statement at `(A_ref, C₀)`, `C_disp = C₀ + 1`, `Bal = 2 + 3C₀ + 3Ch`; for
`A ≥ 1`, `D` from the on-carrier statement, `D₁` from the Hall statement, `D₀ = D + D₁`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization.ReverseTree

open ParabolicRectifiability.Foundations

/-! ## The partition-bind identity -/

/-- **Partition-bind identity**. For countably many disjoint measurable `P_j` and a
kernel `κ` with `κ y = τ_j` on `P_j` and `κ y = δ_y` off `⋃_j P_j`:
`λ.bind κ = Σ_j λ(P_j) τ_j + λ⌊(⋃_j P_j)ᶜ`. -/
theorem d2cpl_bind_partition {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (lam : Measure X) (P : ι → Set X) (τ : ι → Measure X)
    (hPm : ∀ j, MeasurableSet (P j)) (hPd : Pairwise fun i j => Disjoint (P i) (P j))
    (κ : ProbabilityTheory.Kernel X X)
    (hκP : ∀ j, ∀ y ∈ P j, κ y = τ j) (hκ0 : ∀ y, (∀ j, y ∉ P j) → κ y = Measure.dirac y) :
    lam.bind κ = Measure.sum (fun j => lam (P j) • τ j) + lam.restrict (⋃ j, P j)ᶜ := by
  have hU : MeasurableSet (⋃ j, P j) := MeasurableSet.iUnion hPm
  ext B hB
  rw [Measure.bind_apply hB κ.measurable.aemeasurable, Measure.add_apply,
    Measure.sum_apply _ hB, Measure.restrict_apply hB, ← lintegral_add_compl _ hU,
    lintegral_iUnion hPm hPd]
  congr 1
  · refine tsum_congr fun j => ?_
    have hj : ∫⁻ y in P j, κ y B ∂lam = ∫⁻ y in P j, τ j B ∂lam := by
      refine setLIntegral_congr_fun (hPm j) fun y hy => ?_
      show κ y B = τ j B
      rw [hκP j y hy]
    rw [hj, setLIntegral_const, Measure.smul_apply, smul_eq_mul, mul_comm]
  · have hc : ∫⁻ y in (⋃ j, P j)ᶜ, κ y B ∂lam =
        ∫⁻ y in (⋃ j, P j)ᶜ, B.indicator 1 y ∂lam := by
      refine setLIntegral_congr_fun hU.compl fun y hy => ?_
      have hy' : ∀ j, y ∉ P j := fun j hj => hy (mem_iUnion.mpr ⟨j, hj⟩)
      show κ y B = B.indicator 1 y
      rw [hκ0 y hy', Measure.dirac_apply' _ hB]
    rw [hc, lintegral_indicator_one hB, Measure.restrict_apply hB]

/-! ## The exact marginal identity and the domination -/

/-- **Exact marginal identity**. For the kernel of the positive-mass clipped
cells with the normalized targets `τ_j`:
`(μ⌊P(c,2ρ)).bind κ = Σ_{j∈J} σ.withDensity h_j + μ⌊(Γ ∩ P(c,2ρ))`. -/
theorem d2cpl_marginal_eq {n : ℕ} (μ : Measure (Space n)) (Γ : Set (Space n))
    (σ : Measure (Space n)) (Q : ℕ → Set (Space n)) (hQm : ∀ j, MeasurableSet (Q j))
    (hQd : Pairwise fun i j => Disjoint (Q i) (Q j)) (hQU : (⋃ j, Q j) = Γᶜ) (c : Space n)
    (ρ : ℝ) (h : d2cpl_Pos μ Q c ρ → Space n → ℝ≥0∞)
    (hτ : ∀ j, μ (d2cpl_clip Q c ρ j.1) • d2cpl_tau μ σ Q c ρ h j = σ.withDensity (h j))
    (κ : ProbabilityTheory.Kernel (Space n) (Space n))
    (hκP : ∀ j : d2cpl_Pos μ Q c ρ, ∀ y ∈ d2cpl_clip Q c ρ j.1, κ y = d2cpl_tau μ σ Q c ρ h j)
    (hκ0 : ∀ y, (∀ j : d2cpl_Pos μ Q c ρ, y ∉ d2cpl_clip Q c ρ j.1) → κ y = Measure.dirac y) :
    (μ.restrict (Metric.ball c (2 * ρ))).bind κ =
      Measure.sum (fun j : d2cpl_Pos μ Q c ρ => σ.withDensity (h j)) +
        μ.restrict (Γ ∩ Metric.ball c (2 * ρ)) := by
  rw [d2cpl_bind_partition (μ.restrict (Metric.ball c (2 * ρ)))
    (fun j : d2cpl_Pos μ Q c ρ => d2cpl_clip Q c ρ j.1) (d2cpl_tau μ σ Q c ρ h)
    (fun j => d2cpl_measurableSet_clip hQm c ρ j.1) (d2cpl_pos_pairwise_disjoint μ hQd c ρ) κ
    hκP hκ0]
  congr 1
  · congr 1
    funext j
    rw [Measure.restrict_apply (d2cpl_measurableSet_clip hQm c ρ j.1),
      inter_eq_left.mpr (d2cpl_clip_subset_ball Q c ρ j.1), hτ j]
  · rw [Measure.restrict_restrict
      (MeasurableSet.iUnion fun j : d2cpl_Pos μ Q c ρ => d2cpl_measurableSet_clip hQm c ρ j.1).compl]
    exact Measure.restrict_congr_set (d2cpl_compl_ae_eq_carrier μ Γ Q hQU c ρ)

/-- The allocated targets are dominated by the capacity: `Σ_j σ.withDensity h_j ≤ D σ` when
`Σ_j h_j ≤ D` `σ`-a.e. -/
theorem d2cpl_sum_withDensity_le {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (σ : Measure X) {h : ι → X → ℝ≥0∞} (hm : ∀ j, Measurable (h j)) {D : ℝ≥0∞}
    (hsum : ∀ᵐ x ∂σ, ∑' j, h j x ≤ D) :
    Measure.sum (fun j => σ.withDensity (h j)) ≤ D • σ := by
  rw [← withDensity_tsum hm, ← withDensity_const]
  refine withDensity_mono (hsum.mono fun x hx => ?_)
  show (∑' j, h j) x ≤ D
  rw [ENNReal.tsum_apply]
  exact hx

/-! ## The every-point displacement -/

/-- A point `y` of a cell `Q_j ⊆ P(g_j, C₀ s_j)` with `s_j ≤ d(y,Γ)` and a target point
`v ∈ P̄(g_j,s_j)` satisfy `d(y,v) ≤ (C₀ + 1) d(y,Γ)`. -/
theorem d2cpl_dist_le_of_mem_target {n : ℕ} {Γ : Set (Space n)} {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    {a y v : Space n} {r : ℝ} (hya : y ∈ Metric.ball a (C₀ * r))
    (hv : v ∈ Metric.closedBall a r) (hr : r ≤ Metric.infDist y Γ) :
    dist y v ≤ (C₀ + 1) * Metric.infDist y Γ := by
  have h1 : dist y a < C₀ * r := Metric.mem_ball.mp hya
  have h2 : dist a v ≤ r := by rw [dist_comm]; exact Metric.mem_closedBall.mp hv
  have h3 : (C₀ + 1) * r ≤ (C₀ + 1) * Metric.infDist y Γ :=
    mul_le_mul_of_nonneg_left hr (by linarith)
  calc dist y v ≤ dist y a + dist a v := dist_triangle _ _ _
    _ ≤ C₀ * r + r := add_le_add h1.le h2
    _ = (C₀ + 1) * r := by ring
    _ ≤ (C₀ + 1) * Metric.infDist y Γ := h3

/-- **Every-point displacement**. For every `y`, `κ_y`-a.e.
`d(y,v) ≤ (C₀ + 1) d(y,Γ)`: on a positive clipped cell `κ_y = τ_j` is carried by
`E_j = Γ ∩ P̄(g_j,s_j)`; elsewhere `κ_y = δ_y`. -/
theorem d2cpl_displacement {n : ℕ} (μ σ : Measure (Space n)) (Γ : Set (Space n))
    (Q : ℕ → Set (Space n)) (g : ℕ → Space n) (s : ℕ → ℝ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hQsub : ∀ j, Q j ⊆ Metric.ball (g j) (C₀ * s j))
    (hle : ∀ j, ∀ y ∈ Q j, s j ≤ Metric.infDist y Γ)
    (c : Space n) (ρ : ℝ) (h : d2cpl_Pos μ Q c ρ → Space n → ℝ≥0∞)
    (hτE : ∀ j, d2cpl_tau μ σ Q c ρ h j (d2cpl_target Γ g s j.1)ᶜ = 0)
    (κ : ProbabilityTheory.Kernel (Space n) (Space n))
    (hκP : ∀ j : d2cpl_Pos μ Q c ρ, ∀ y ∈ d2cpl_clip Q c ρ j.1, κ y = d2cpl_tau μ σ Q c ρ h j)
    (hκ0 : ∀ y, (∀ j : d2cpl_Pos μ Q c ρ, y ∉ d2cpl_clip Q c ρ j.1) → κ y = Measure.dirac y) :
    ∀ y, ∀ᵐ v ∂(κ y), dist y v ≤ (C₀ + 1) * Metric.infDist y Γ := by
  intro y
  by_cases hy : ∃ j : d2cpl_Pos μ Q c ρ, y ∈ d2cpl_clip Q c ρ j.1
  · obtain ⟨j, hyj⟩ := hy
    have hyQ : y ∈ Q j.1 := d2cpl_clip_subset_cell Q c ρ j.1 hyj
    rw [hκP j y hyj]
    have hE : ∀ᵐ v ∂(d2cpl_tau μ σ Q c ρ h j), v ∈ d2cpl_target Γ g s j.1 :=
      ae_iff.mpr (hτE j)
    filter_upwards [hE] with v hv
    exact d2cpl_dist_le_of_mem_target hC₀ (hQsub j.1 hyQ) hv.2 (hle j.1 y hyQ)
  · push Not at hy
    rw [hκ0 y hy]
    have hmeasv : MeasurableSet {v : Space n | dist y v ≤ (C₀ + 1) * Metric.infDist y Γ} :=
      measurableSet_le (continuous_const.dist continuous_id').measurable measurable_const
    refine (ae_dirac_iff hmeasv).mpr ?_
    rw [dist_self]
    exact mul_nonneg (by linarith) Metric.infDist_nonneg

/-! ## The statement -/

/-- **`d2_coupling_of_parts`** (`CouplingStatement` from its four parts). Implication type of the statement.

Constants: `C_disp = C₀ + 1`, `Bal = 2 + 3C₀ + 3Ch` (both before `A`), `D₀ = D + D₁`. The kernel
sends the positive-mass clipped cells `Q'_j = Q_j ∩ P(c,2ρ)` to the normalized Hall targets
`τ_j = μ(Q'_j)⁻¹ σ.withDensity h_j` and is the identity elsewhere. -/
theorem d2_coupling_of_parts_proof :
    WhitneyCellsStatement → OnCarrierStatement → HallInequalityStatement →
      KernelOfPartitionStatement → CouplingStatement := by
  intro hW hOn hH hK n hn k hk hkn Aref hAref
  obtain ⟨C₀, hC₀, hcells⟩ := hW n
  obtain ⟨Ch, hCh, hHall⟩ := hH n hn k hk hkn Aref hAref C₀ hC₀
  refine ⟨C₀ + 1, by linarith, 2 + 3 * C₀ + 3 * Ch, by linarith, ?_⟩
  intro A hA
  obtain ⟨D, hD, hOnA⟩ := hOn n hn k hk hkn Aref hAref A hA
  obtain ⟨D₁, hD₁, hHallA⟩ := hHall A hA
  refine ⟨D + D₁, by linarith, ?_⟩
  intro μ hμfin hμreg Γ σ hσfin hσΓ hADR c ρ hρ hΓc hgrowth
  have := hμfin
  have := hσfin
  have hΓcl : IsClosed Γ := by rw [← hσΓ]; exact Measure.isClosed_support
  -- Whitney cells of `Γᶜ`.
  obtain ⟨Q, g, s, hQm, hQd, hQU, hg, hs, hQsub, hle⟩ :=
    hcells Γ hΓcl (hΓc.mono inter_subset_right)
  -- Hall densities and normalized targets.
  obtain ⟨h, hmeas, hzero, hint, hsum⟩ := d2cpl_exists_densities hC₀ hCh hD₁ hHallA μ Γ σ hσΓ
    hADR Q g s hQm hQd hg hs hQsub hle c ρ hΓc hgrowth
  have hτ := d2cpl_tau_spec μ σ Γ Q g s c ρ h hmeas hzero hint
  -- The kernel of the positive-mass clipped cells.
  obtain ⟨κ, hκM, hκP, hκ0⟩ := hK n (d2cpl_Pos μ Q c ρ) (fun j => d2cpl_clip Q c ρ j.1)
    (d2cpl_tau μ σ Q c ρ h) (fun j => d2cpl_measurableSet_clip hQm c ρ j.1)
    (d2cpl_pos_pairwise_disjoint μ hQd c ρ) (fun j => (hτ j).1)
  refine ⟨κ, hκM, d2cpl_displacement μ σ Γ Q g s (by linarith) hQsub hle c ρ h
    (fun j => (hτ j).2.1) κ hκP hκ0, ?_⟩
  -- The exact marginal identity and the domination.
  rw [d2cpl_marginal_eq μ Γ σ Q hQm hQd hQU c ρ h (fun j => (hτ j).2.2) κ hκP hκ0]
  have hbuf : 2 * ρ ≤ (2 + 3 * C₀ + 3 * Ch) * ρ := by
    have h1 : 0 ≤ C₀ * ρ := mul_nonneg (by linarith) hρ.le
    have h2 : 0 ≤ Ch * ρ := mul_nonneg (by linarith) hρ.le
    linarith
  have h1 : Measure.sum (fun j : d2cpl_Pos μ Q c ρ => σ.withDensity (h j)) ≤
      ENNReal.ofReal D₁ • σ :=
    d2cpl_sum_withDensity_le σ hmeas hsum
  have h2 : μ.restrict (Γ ∩ Metric.ball c (2 * ρ)) ≤ ENNReal.ofReal D • σ :=
    hOnA μ hμfin hμreg Γ σ hσfin hσΓ hADR c (2 * ρ) (by linarith)
      (d2cpl_growth_mono hbuf hgrowth)
  calc _ ≤ ENNReal.ofReal D₁ • σ + ENNReal.ofReal D • σ := add_le_add h1 h2
    _ = ENNReal.ofReal (D + D₁) • σ := by
      rw [← add_smul, ENNReal.ofReal_add hD.le hD₁.le, add_comm]

end ParabolicRectifiability.QuantitativeCharacterization.ReverseTree
