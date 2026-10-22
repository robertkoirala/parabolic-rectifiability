import ParabolicRectifiability.Enhancements.Proofs.GraphDomains.GraphDomainLemmas
import ParabolicRectifiability.Foundations.Proofs.GraphEnvelope.Statements

/-! # Assembly of the fixed-carrier graph-domain cover

The main theorem `exists_fixedCarrier_graphDomainCover_of_providers` proves, in implication form
over four statements assumed as hypotheses, exactly the type of
`Enhancements.exists_fixedCarrier_graphDomainCover`: a compact carrier of finite parabolic
Hausdorff measure that is covered, modulo `H_P^k`, by graphs of small slope admits graph domains
with a mesh, a trace estimate, and global and local charge bounds. The intermediate lemmas it
uses are those of the namespace `GraphDomainTree`.

Hypotheses (taken as assumptions, never reproved here):
* `hfive : FivefoldSelectionStatement`, the fivefold selection (covering) lemma;
* `henv : HorizontalClosedEnvelopeStatement`, replacing a horizontal graph by one over a closed
  domain;
* `hborelH`: closed-domain horizontal graphs have Borel images
  (`fgenv_horizontal_image_measurableSet_of_isClosed`);
* `hborelV`: full general regular vertical graphs have Borel images
  (`fgenv_vertical_image_measurableSet`).

Structure of the proof:
* `horizontal_hub`, `vertical_hub`: the fixed-carrier constructions for each graph type. Use the
  carrier cover at tolerance `min ε 1`; close the horizontal domains; establish the per-graph
  facts (`horizontalGraph_geometry`, `verticalGraph_geometry`) and the Borel images; assign each
  point to the first graph and prove the trace estimate (`horizontal_assignment`,
  `vertical_assignment`); select density balls in every trace domain
  (`exists_disjoint_halfDensity_balls`, with the fivefold selection); build the patch family
  with both charge bounds (`horizontal_patches`, `vertical_patches`). The constant is a finite
  maximum over `k ≤ n + 2` of the explicit constants.
* `exists_fixedCarrier_graphDomainCover_of_providers`: the singleton family of a fixed type,
  with empty data for the absent type; `C = max C_H C_V`.

The assumptions `1 ≤ k`, `1 ≤ n` and `H_P^k(K) < ∞` of the statement are not used by this
construction, which also covers a Hausdorff-null carrier. No growth, density or source
hypothesis is assumed; the graph covers of the carrier are an input of the statement.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Enhancements.GraphDomainTree

open ParabolicRectifiability.Foundations
open ParabolicRectifiability.Characterization (FivefoldSelectionStatement)

/-! ## Elementary facts -/

/-- A uniform real bound for finitely many finite extended constants. -/
theorem exists_uniform_bound (f : ℕ → ℝ≥0∞) (hf : ∀ k, f k ≠ ⊤) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k, k ≤ N → f k ≤ ENNReal.ofReal C := by
  have hs : (∑ j ∈ Finset.range (N + 1), f j) ≠ ⊤ :=
    (ENNReal.sum_lt_top.mpr fun j _ => (hf j).lt_top).ne
  refine ⟨(∑ j ∈ Finset.range (N + 1), f j).toReal + 1,
    add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg one_pos, fun k hk => ?_⟩
  calc f k ≤ ∑ j ∈ Finset.range (N + 1), f j :=
        Finset.single_le_sum (f := f) (fun j _ => zero_le) (Finset.mem_range.mpr (by omega))
    _ = ENNReal.ofReal (∑ j ∈ Finset.range (N + 1), f j).toReal := (ENNReal.ofReal_toReal hs).symm
    _ ≤ ENNReal.ofReal ((∑ j ∈ Finset.range (N + 1), f j).toReal + 1) :=
        ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one)

/-- Inner-product volume of a ball in a spatial subspace (horizontal case). -/
theorem volume_ball_direction {n : ℕ} (W : Submodule ℝ (Spatial n)) (p : W) {r : ℝ}
    (hr : 0 < r) :
    volume (Metric.ball p r) =
      omega (Module.finrank ℝ W) * ENNReal.ofReal r ^ (Module.finrank ℝ W) := by
  have hm := (subspaceCoordinates_spatial_measurePreserving W).measure_preimage_equiv
    (Metric.ball (subspaceCoordinates W p) r)
  have hpre : (subspaceCoordinates W).toHomeomorph.toMeasurableEquiv ⁻¹'
      Metric.ball (subspaceCoordinates W p) r = Metric.ball p r :=
    (subspaceCoordinates W).isometry.preimage_ball p r
  rw [hpre] at hm
  rw [hm, volume_spatial_ball _ hr]

theorem horizontal_constant_ne_top (k : ℕ) :
    omega k + 2 * 5 ^ k * (1 + omega k + 2 ^ k * horizontalHausdorffConstant k * omega k) ≠ ⊤ := by
  have h1 := (omega_lt_top k).ne
  have h2 := (horizontalHausdorffConstant_lt_top k).ne
  exact ENNReal.add_ne_top.mpr ⟨h1, ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))
    (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, h1⟩,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) h2) h1⟩)⟩

theorem vertical_constant_ne_top (k : ℕ) :
    2 * omega (k - 2) + 2 * 5 ^ k * (1 + 2 * omega (k - 2) +
      2 ^ k * verticalHausdorffConstant (k - 2) * (2 * omega (k - 2))) ≠ ⊤ := by
  have h1 : 2 * omega (k - 2) ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top (omega_lt_top _).ne
  have h2 := (verticalHausdorffConstant_lt_top (k - 2)).ne
  exact ENNReal.add_ne_top.mpr ⟨h1, ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))
    (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, h1⟩,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) h2) h1⟩)⟩

/-! ## Empty data for an absent type -/

/-- The empty horizontal data of the empty carrier. -/
def emptyHorizontalData (n k : ℕ) (ε δ : ℝ) : HorizontalDomainData n k ε δ ∅ where
  graphIndex := ∅
  graph := fun j => (Set.notMem_empty _ j.2).elim
  trace := fun _ => ∅
  measurableSet_trace := fun _ => MeasurableSet.empty
  trace_subset := fun _ => empty_subset _
  pairwise_disjoint_trace := fun _ _ _ => Set.empty_disjoint _
  trace_cover := by simp
  measurableSet_tracePreimage := fun j => (Set.notMem_empty _ j.2).elim
  patchIndex := ∅
  patchGraph := fun α => (Set.notMem_empty _ α.2).elim
  center := fun α => (Set.notMem_empty _ α.2).elim
  center_mem_tracePreimage := fun α => (Set.notMem_empty _ α.2).elim
  centerPoint_mem := fun α => (Set.notMem_empty _ α.2).elim
  radius := fun _ => 1
  radius_pos := fun _ => one_pos
  radius_le := fun α => (Set.notMem_empty _ α.2).elim
  measurableSet_patch := fun α => (Set.notMem_empty _ α.2).elim
  patch_cover := by simp

/-- The empty vertical data of the empty carrier. -/
def emptyVerticalData (n k : ℕ) (ε δ : ℝ) : VerticalDomainData n k ε δ ∅ where
  graphIndex := ∅
  graph := fun j => (Set.notMem_empty _ j.2).elim
  trace := fun _ => ∅
  measurableSet_trace := fun _ => MeasurableSet.empty
  trace_subset := fun _ => empty_subset _
  pairwise_disjoint_trace := fun _ _ _ => Set.empty_disjoint _
  trace_cover := by simp
  measurableSet_tracePreimage := fun j => (Set.notMem_empty _ j.2).elim
  patchIndex := ∅
  patchGraph := fun α => (Set.notMem_empty _ α.2).elim
  center := fun α => (Set.notMem_empty _ α.2).elim
  center_mem_tracePreimage := fun α => (Set.notMem_empty _ α.2).elim
  centerPoint_mem := fun α => (Set.notMem_empty _ α.2).elim
  radius := fun _ => 1
  radius_pos := fun _ => one_pos
  radius_le := fun α => (Set.notMem_empty _ α.2).elim
  measurableSet_patch := fun α => (Set.notMem_empty _ α.2).elim
  patch_cover := by simp

theorem emptyHorizontalData_traceVolume (n k : ℕ) (ε δ : ℝ) (U : Set (Space n)) :
    (emptyHorizontalData n k ε δ).traceVolume U = 0 :=
  ENNReal.tsum_eq_zero.mpr fun j => (Set.notMem_empty _ j.2).elim

theorem emptyHorizontalData_totalCharge (n k : ℕ) (ε δ : ℝ) :
    (emptyHorizontalData n k ε δ).totalCharge = 0 :=
  ENNReal.tsum_eq_zero.mpr fun α => (Set.notMem_empty _ α.2).elim

theorem emptyHorizontalData_localCharge (n k : ℕ) (ε δ : ℝ) (q : Space n) (R : ℝ) :
    (emptyHorizontalData n k ε δ).localCharge q R = 0 :=
  ENNReal.tsum_eq_zero.mpr fun α => (Set.notMem_empty _ α.1.2).elim

theorem emptyVerticalData_traceVolume (n k : ℕ) (ε δ : ℝ) (U : Set (Space n)) :
    (emptyVerticalData n k ε δ).traceVolume U = 0 :=
  ENNReal.tsum_eq_zero.mpr fun j => (Set.notMem_empty _ j.2).elim

theorem emptyVerticalData_totalCharge (n k : ℕ) (ε δ : ℝ) :
    (emptyVerticalData n k ε δ).totalCharge = 0 :=
  ENNReal.tsum_eq_zero.mpr fun α => (Set.notMem_empty _ α.2).elim

theorem emptyVerticalData_localCharge (n k : ℕ) (ε δ : ℝ) (q : Space n) (R : ℝ) :
    (emptyVerticalData n k ε δ).localCharge q R = 0 :=
  ENNReal.tsum_eq_zero.mpr fun α => (Set.notMem_empty _ α.1.2).elim

/-- The graph-domain cover of the singleton horizontal family `(K, ∅)`. -/
def horizontalCover {n k : ℕ} {C ε δ : ℝ} {K : Set (Space n)}
    (D : HorizontalDomainData n k ε δ K)
    (ht : ∀ U : Set (Space n), MeasurableSet U →
      D.traceVolume U ≤ ENNReal.ofReal C * hausdorffP n k (K ∩ U))
    (hc : D.totalCharge ≤ ENNReal.ofReal C * hausdorffP n k K)
    (hl : ∀ (q : Space n) (R : ℝ), 0 < R →
      D.localCharge q R ≤ ENNReal.ofReal C * hausdorffP n k (K ∩ Metric.ball q (2 * R))) :
    GraphDomainCover n k C ε δ K ∅ where
  horizontal := D
  vertical := emptyVerticalData n k ε δ
  trace_le U hU := by
    rw [emptyVerticalData_traceVolume, add_zero, union_empty]
    exact ht U hU
  totalCharge_le := by
    rw [emptyVerticalData_totalCharge, add_zero, union_empty]
    exact hc
  horizontal_totalCharge_le := by
    rw [union_empty]
    exact hc
  vertical_totalCharge_le := by
    rw [emptyVerticalData_totalCharge]
    exact zero_le
  localCharge_le q R hR := by
    rw [emptyVerticalData_localCharge, add_zero, union_empty]
    exact hl q R hR
  horizontal_localCharge_le q R hR := by
    rw [union_empty]
    exact hl q R hR
  vertical_localCharge_le q R _ := by
    rw [emptyVerticalData_localCharge]
    exact zero_le

/-- The graph-domain cover of the singleton vertical family `(∅, K)`. -/
def verticalCover {n k : ℕ} {C ε δ : ℝ} {K : Set (Space n)}
    (D : VerticalDomainData n k ε δ K)
    (ht : ∀ U : Set (Space n), MeasurableSet U →
      D.traceVolume U ≤ ENNReal.ofReal C * hausdorffP n k (K ∩ U))
    (hc : D.totalCharge ≤ ENNReal.ofReal C * hausdorffP n k K)
    (hl : ∀ (q : Space n) (R : ℝ), 0 < R →
      D.localCharge q R ≤ ENNReal.ofReal C * hausdorffP n k (K ∩ Metric.ball q (2 * R))) :
    GraphDomainCover n k C ε δ ∅ K where
  horizontal := emptyHorizontalData n k ε δ
  vertical := D
  trace_le U hU := by
    rw [emptyHorizontalData_traceVolume, zero_add, empty_union]
    exact ht U hU
  totalCharge_le := by
    rw [emptyHorizontalData_totalCharge, zero_add, empty_union]
    exact hc
  horizontal_totalCharge_le := by
    rw [emptyHorizontalData_totalCharge]
    exact zero_le
  vertical_totalCharge_le := by
    rw [empty_union]
    exact hc
  localCharge_le q R hR := by
    rw [emptyHorizontalData_localCharge, zero_add, empty_union]
    exact hl q R hR
  horizontal_localCharge_le q R _ := by
    rw [emptyHorizontalData_localCharge]
    exact zero_le
  vertical_localCharge_le q R hR := by
    rw [empty_union]
    exact hl q R hR

/-! ## The typed hubs -/

/-- **Typed hub, horizontal.** Under the fivefold selection, the closed-envelope statement and
the Borel-image statement for closed-domain horizontal graphs: for every `n` there is `C > 0`
such that every compact `K` with horizontal covers modulo `H_P^k` at every tolerance has, for all
`ε, δ > 0`, horizontal domain data with mesh `δ` and graphs of slope `≤ min ε 1`, the trace
estimate with constant `C`, and the global and local charge bounds with constant `C`. -/
theorem horizontal_hub (hfive : FivefoldSelectionStatement)
    (henv : HorizontalClosedEnvelopeStatement)
    (hborelH : ∀ (n k : ℕ) (ε : ℝ) (G : HorizontalGraph n k ε), IsClosed G.domain →
      MeasurableSet G.image)
    (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, k ≤ n + 2 → ∀ K : Set (Space n), IsCompact K →
      (∀ η : ℝ, 0 < η → HasHorizontalGraphCover k K η) → ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∃ D : HorizontalDomainData n k ε δ K,
        (∀ U : Set (Space n), MeasurableSet U →
          D.traceVolume U ≤ ENNReal.ofReal C * hausdorffP n k (K ∩ U)) ∧
        D.totalCharge ≤ ENNReal.ofReal C * hausdorffP n k K ∧
        ∀ (q : Space n) (R : ℝ), 0 < R →
          D.localCharge q R ≤ ENNReal.ofReal C * hausdorffP n k (K ∩ Metric.ball q (2 * R)) := by
  obtain ⟨C, hC, hCf⟩ := exists_uniform_bound
    (fun k => omega k + 2 * 5 ^ k * (1 + omega k + 2 ^ k * horizontalHausdorffConstant k * omega k))
    horizontal_constant_ne_top (n + 2)
  refine ⟨C, hC, ?_⟩
  intro k hk K hK hcov ε δ hε hδ
  have hfk : omega k + 2 * 5 ^ k * (1 + omega k + 2 ^ k * horizontalHausdorffConstant k * omega k)
      ≤ ENNReal.ofReal C := hCf k hk
  have hc1 : omega k ≤ ENNReal.ofReal C := le_self_add.trans hfk
  have hc2 : 2 * 5 ^ k * (1 + omega k + 2 ^ k * horizontalHausdorffConstant k * omega k) ≤
      ENNReal.ofReal C := le_add_self.trans hfk
  -- the carrier cover at tolerance `min ε 1`, with closed domains
  obtain ⟨I, G₀, hG₀⟩ := hcov (min ε 1) (lt_min hε one_pos)
  choose G hGsub hGc using fun i => henv n k (min ε 1) (G₀ i)
  have geo := fun i => horizontalGraph_geometry (min_le_right ε 1) (G i) (hGc i)
  have hcovG : hausdorffP n k (K \ ⋃ i, (G i).image) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_right (iUnion_mono hGsub)) hG₀
  -- first-graph assignment and the trace estimate (Borel images of closed-domain graphs)
  obtain ⟨F, hFm, hFsub, hFdisj, hFcov, hEb, htrace⟩ :=
    horizontal_assignment (omega k) K hK.isClosed.measurableSet hK.isBounded I G
      (fun i => hborelH n k (min ε 1) (G i) (hGc i)) (fun i => (geo i).1)
      (fun i u w => ((geo i).2.2.1 u w).1) (fun i => (geo i).2.2.2.1) hcovG
  have hEm : ∀ i, MeasurableSet (horizontalPreimage (G i) (F i)) :=
    fun i => (geo i).1 _ (hFm i)
  have hballG : ∀ i (p : (G i).direction) (r : ℝ), 0 < r →
      volume (Metric.ball p r) = omega k * ENNReal.ofReal r ^ k := by
    intro i p r hr
    rw [volume_ball_direction _ p hr, (G i).rank_eq]
  -- density selection in every trace domain (with the fivefold selection)
  choose L p r hp hr hdisj hhalf hcov5 using fun i =>
    exists_disjoint_halfDensity_balls hfive (volume : Measure (G i).direction) k (omega k)
      (omega_pos k).ne' (omega_lt_top k).ne (hballG i) _ (hEm i) (hEb i) δ hδ
  -- the patch family and its charges
  obtain ⟨D, hDt, hDc, hDl⟩ := horizontal_patches (omega k)
    (2 ^ k * horizontalHausdorffConstant k) (omega_pos k).ne' (omega_lt_top k).ne K I G F
    hFm hFsub hFdisj hFcov hEm (fun i => (geo i).2.1) (fun i => (geo i).2.2.1)
    (fun i => (geo i).2.2.2.1) (fun i => (geo i).2.2.2.2)
    (fun i p r hr => (hballG i p r hr).le) L p r hp hr hdisj hhalf hcov5
  refine ⟨D, fun U hU => ?_, ?_, fun q R hR => ?_⟩
  · rw [hDt U]
    exact (htrace U hU).trans (mul_le_mul' hc1 le_rfl)
  · exact hDc.trans (mul_le_mul' hc2 le_rfl)
  · exact (hDl q R hR).trans (mul_le_mul' hc2 le_rfl)

/-- **Typed hub, vertical.** Under the fivefold selection and the Borel-image statement for
vertical graphs: the same conclusion for full general regular vertical graphs. -/
theorem vertical_hub (hfive : FivefoldSelectionStatement)
    (hborelV : ∀ (n k : ℕ) (ε : ℝ) (G : GeneralRegularVerticalGraph n k ε),
      MeasurableSet G.image)
    (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, k ≤ n + 2 → ∀ K : Set (Space n), IsCompact K →
      (∀ η : ℝ, 0 < η → HasGeneralRegularVerticalGraphCover k K η) →
      ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∃ D : VerticalDomainData n k ε δ K,
        (∀ U : Set (Space n), MeasurableSet U →
          D.traceVolume U ≤ ENNReal.ofReal C * hausdorffP n k (K ∩ U)) ∧
        D.totalCharge ≤ ENNReal.ofReal C * hausdorffP n k K ∧
        ∀ (q : Space n) (R : ℝ), 0 < R →
          D.localCharge q R ≤ ENNReal.ofReal C * hausdorffP n k (K ∩ Metric.ball q (2 * R)) := by
  obtain ⟨C, hC, hCf⟩ := exists_uniform_bound
    (fun k => 2 * omega (k - 2) + 2 * 5 ^ k * (1 + 2 * omega (k - 2) +
      2 ^ k * verticalHausdorffConstant (k - 2) * (2 * omega (k - 2))))
    vertical_constant_ne_top (n + 2)
  refine ⟨C, hC, ?_⟩
  intro k hk K hK hcov ε δ hε hδ
  have hfk : 2 * omega (k - 2) + 2 * 5 ^ k * (1 + 2 * omega (k - 2) +
      2 ^ k * verticalHausdorffConstant (k - 2) * (2 * omega (k - 2))) ≤ ENNReal.ofReal C :=
    hCf k hk
  have hc1 : 2 * omega (k - 2) ≤ ENNReal.ofReal C := le_self_add.trans hfk
  have hc2 : 2 * 5 ^ k * (1 + 2 * omega (k - 2) +
      2 ^ k * verticalHausdorffConstant (k - 2) * (2 * omega (k - 2))) ≤ ENNReal.ofReal C :=
    le_add_self.trans hfk
  have hv0 : 2 * omega (k - 2) ≠ 0 := mul_ne_zero two_ne_zero (omega_pos _).ne'
  have hvt : 2 * omega (k - 2) ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top (omega_lt_top _).ne
  obtain ⟨I, G, hG⟩ := hcov (min ε 1) (lt_min hε one_pos)
  have geo := fun i => verticalGraph_geometry (min_le_right ε 1) (G i)
  -- first-graph assignment and the trace estimate (Borel images of vertical graphs)
  obtain ⟨F, hFm, hFsub, hFdisj, hFcov, hEb, htrace⟩ :=
    vertical_assignment (2 * omega (k - 2)) K hK.isClosed.measurableSet hK.isBounded I G
      (fun i => hborelV n k (min ε 1) (G i)) (fun i => (geo i).1)
      (fun i p q => ((geo i).2.2.1 p q).1) (fun i => (geo i).2.2.2.1) hG
  have hEm : ∀ i, MeasurableSet ((G i).map ⁻¹' F i) := fun i => (geo i).1 _ (hFm i)
  have hballG : ∀ i (p : SubspaceSpace (G i).direction) (r : ℝ), 0 < r →
      intrinsicParabolicVolume (G i).direction (Metric.ball p r) =
        2 * omega (k - 2) * ENNReal.ofReal r ^ k := by
    intro i p r hr
    have hfr : Module.finrank ℝ (G i).direction = k - 2 := by
      have := (G i).rank_eq
      omega
    rw [intrinsicParabolicVolume_ball_of_dimension _ k (G i).rank_eq p r hr, hfr]
  -- density selection in every trace domain (with the fivefold selection)
  choose L p r hp hr hdisj hhalf hcov5 using fun i =>
    exists_disjoint_halfDensity_balls hfive (intrinsicParabolicVolume (G i).direction) k
      (2 * omega (k - 2)) hv0 hvt (hballG i) _ (hEm i) (hEb i) δ hδ
  obtain ⟨D, hDt, hDc, hDl⟩ := vertical_patches (2 * omega (k - 2))
    (2 ^ k * verticalHausdorffConstant (k - 2)) hv0 hvt K I G F
    hFm hFsub hFdisj hFcov hEm (fun i => (geo i).2.1) (fun i => (geo i).2.2.1)
    (fun i => (geo i).2.2.2.1) (fun i => (geo i).2.2.2.2)
    (fun i p r hr => (hballG i p r hr).le) L p r hp hr hdisj hhalf hcov5
  refine ⟨D, fun U hU => ?_, ?_, fun q R hR => ?_⟩
  · rw [hDt U]
    exact (htrace U hU).trans (mul_le_mul' hc1 le_rfl)
  · exact hDc.trans (mul_le_mul' hc2 le_rfl)
  · exact (hDl q R hR).trans (mul_le_mul' hc2 le_rfl)

/-! ## The main statement -/

/-- **The fixed-carrier graph-domain cover, in implication form.** After the four hypotheses
(fivefold selection; closed envelope and Borel images for horizontal graphs; Borel images for
vertical graphs), the type is exactly that of
`Enhancements.exists_fixedCarrier_graphDomainCover`. The constant is the maximum of the two
typed hub constants. -/
theorem exists_fixedCarrier_graphDomainCover_of_providers (hfive : FivefoldSelectionStatement)
    (henv : HorizontalClosedEnvelopeStatement)
    (hborelH : ∀ (n k : ℕ) (ε : ℝ) (G : HorizontalGraph n k ε), IsClosed G.domain →
      MeasurableSet G.image)
    (hborelV : ∀ (n k : ℕ) (ε : ℝ) (G : GeneralRegularVerticalGraph n k ε),
      MeasurableSet G.image)
    (n : ℕ) (_hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
      ∀ T : FamilyKind, T ≠ .mixed → Nonempty (Models n k T) →
      ∀ K : Set (Space n), IsCompact K → hausdorffP n k K < ⊤ →
      (∀ η : ℝ, 0 < η → HasTypedGraphCover T k K η) →
      ∀ ε δ : ℝ, 0 < ε → 0 < δ →
        Nonempty (GraphDomainCover n k C ε δ
          (if T = .horizontal then K else ∅) (if T = .vertical then K else ∅)) := by
  obtain ⟨CH, hCH, hH⟩ := horizontal_hub hfive henv hborelH n
  obtain ⟨CV, hCV, hV⟩ := vertical_hub hfive hborelV n
  have hmono : ∀ {C' : ℝ} {x y : ℝ≥0∞}, C' ≤ max CH CV → x ≤ ENNReal.ofReal C' * y →
      x ≤ ENNReal.ofReal (max CH CV) * y :=
    fun hC' h => h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hC') le_rfl)
  refine ⟨max CH CV, lt_max_of_lt_left hCH, ?_⟩
  intro k _ hkn T hT _ K hK _ hcov ε δ hε hδ
  cases T with
  | horizontal =>
    have e1 : (if (FamilyKind.horizontal : FamilyKind) = .horizontal then K else ∅) = K := by
      simp
    have e2 : (if (FamilyKind.horizontal : FamilyKind) = .vertical then K else ∅) = ∅ := by
      simp
    rw [e1, e2]
    obtain ⟨D, hDt, hDc, hDl⟩ := hH k hkn K hK hcov ε δ hε hδ
    exact ⟨horizontalCover D (fun U hU => hmono (le_max_left _ _) (hDt U hU))
      (hmono (le_max_left _ _) hDc) (fun q R hR => hmono (le_max_left _ _) (hDl q R hR))⟩
  | vertical =>
    have e1 : (if (FamilyKind.vertical : FamilyKind) = .horizontal then K else ∅) = ∅ := by
      simp
    have e2 : (if (FamilyKind.vertical : FamilyKind) = .vertical then K else ∅) = K := by
      simp
    rw [e1, e2]
    obtain ⟨D, hDt, hDc, hDl⟩ := hV k hkn K hK hcov ε δ hε hδ
    exact ⟨verticalCover D (fun U hU => hmono (le_max_right _ _) (hDt U hU))
      (hmono (le_max_right _ _) hDc) (fun q R hR => hmono (le_max_right _ _) (hDl q R hR))⟩
  | mixed => exact absurd rfl hT

end ParabolicRectifiability.Enhancements.GraphDomainTree
