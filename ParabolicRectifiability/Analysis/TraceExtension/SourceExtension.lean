import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Boxes
import ParabolicRectifiability.Analysis.TraceExtension.Whitney.PartitionConstruction
import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Transfer
import ParabolicRectifiability.Analysis.TraceExtension.Whitney.NodeMeasure
import ParabolicRectifiability.Analysis.TraceExtension.SourceEstimates
import ParabolicRectifiability.Analysis.TraceExtension.NodeEstimates
import ParabolicRectifiability.Analysis.TraceExtension.NodeError

/-! # Extension from a diffuse source

Assembly of the source extension `exists_affine_extension_of_source_proof`: a source
`σ ≤ dp` with
lower density `c` on a nonempty compact `F₀` and finite source energy on `F₀`, and a
function `f` that is `L`-Lipschitz on a Borel set carrying `σ` and containing `F₀`,
give a global `C L`-Lipschitz extension of `f|F₀` with affine Carleson constant
`C (L² + B)`, where `C = C(m, c)`.

Proof outline: the maximal eligible boxes of `F₀` give Whitney data with
`D = D_m`, `a = A_W - D_m ≥ 2`, center separation `1/2` and, through the smooth
partition `exists_whitneyBoxes_partition_proof`, the upper center distance `b` and the
partition constants `H, b, K, N`. The Whitney source allocation (taken as the hypothesis
`h3a`) and the moment coefficients `exists_moment_coefficients_proof` define the node
function `g`. One common slope bound `κ L`, with `κ = max(C_lip, C_fit)`, makes `g`
`κ L`-Lipschitz on the node set (`allocated_node_lipschitz_proof`) and makes the source
fits admissible in the constrained node error (`node_error_le_source_error_of_leaves`).
The node errors integrate (`lintegral_Ioi_scaleMeasure_le_of_le_comp_mul_proof`) to
per-node scale bounds `C_e B`, hence the node Carleson bound `C_c C_e B R^k`
(`whitney_node_carleson_le_proof`), and the Whitney transfer
(`whitney_transfer_unconditional`) bounds the filling. All constants are fixed from `m`
and `c` before the data and the value space.

The allocation is stated for index types in an arbitrary universe; the Whitney
boxes live in `Type`, so the data are reindexed along `ULift` and the allocation is
transported back.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

universe u w

namespace WhitneyData

/-- Whitney data reindexed along `ULift`: the same cells, centers and radii. -/
def ulift {m : ℕ} {ι : Type u} {F₀ : Set (Space m)} {D a : ℝ}
    (W : WhitneyData m ι F₀ D a) : WhitneyData m (ULift.{w} ι) F₀ D a where
  cell j := W.cell j.down
  center j := W.center j.down
  radius j := W.radius j.down
  one_le_D := W.one_le_D
  a_pos := W.a_pos
  radius_pos j := W.radius_pos j.down
  measurableSet_cell j := W.measurableSet_cell j.down
  center_mem j := W.center_mem j.down
  pairwise_disjoint i j hij := W.pairwise_disjoint fun h => hij (congrArg ULift.up h)
  iUnion_cell := by
    rw [← W.iUnion_cell]
    exact ULift.down_surjective.iUnion_comp W.cell
  volume_cell j := W.volume_cell j.down
  cell_subset j := W.cell_subset j.down
  le_infDist j := W.le_infDist j.down

end WhitneyData

namespace WhitneySourceAllocation

/-- An allocation for the data reindexed along `ULift` is an allocation for the
original data. -/
def ofULift {m : ℕ} {ι : Type u} {F₀ : Set (Space m)} {D a : ℝ}
    {W : WhitneyData m ι F₀ D a} {σ : Measure (Space m)} {A C_B c₂ : ℝ}
    (S : WhitneySourceAllocation (W.ulift : WhitneyData m (ULift.{w} ι) F₀ D a)
      σ A C_B c₂) :
    WhitneySourceAllocation W σ A C_B c₂ where
  anchor i := S.anchor (ULift.up i)
  anchor_mem i := S.anchor_mem (ULift.up i)
  dist_anchor i := S.dist_anchor (ULift.up i)
  reservoir i := S.reservoir (ULift.up i)
  measurableSet_reservoir i := S.measurableSet_reservoir (ULift.up i)
  reservoir_subset i := S.reservoir_subset (ULift.up i)
  density i := S.density (ULift.up i)
  measurable_density i := S.measurable_density (ULift.up i)
  density_eq_zero i := S.density_eq_zero (ULift.up i)
  lintegral_density i := S.lintegral_density (ULift.up i)
  sum_density_le := by
    filter_upwards [S.sum_density_le] with x hx
    let e : ι × Fin (m + 1) ≃ ULift.{w} ι × Fin (m + 1) :=
      Equiv.prodCongr Equiv.ulift.symm (Equiv.refl _)
    exact (e.tsum_eq (fun p => S.density p.1 p.2 x)).trans_le hx
  simplex i := S.simplex (ULift.up i)

end WhitneySourceAllocation

/-- Monotonicity of the affine Carleson bound in its constant. -/
private theorem hasAffineCarlesonBound_of_le {m : ℕ} {Y : Type*} [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] {F : Space m → Y} {B B' : ℝ}
    (h : HasAffineCarlesonBound (parabolicVolume m) F B) (hBB' : B ≤ B') :
    HasAffineCarlesonBound (parabolicVolume m) F B' := by
  unfold HasAffineCarlesonBound at h ⊢
  refine ⟨h.1.trans hBB', fun z R hR => (h.2 z R hR).trans ?_⟩
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hBB' (pow_nonneg hR.le _))

/-- **Source extension.** A source `σ ≤ dp` with lower density `c` on a nonempty compact
`F₀` and finite source energy on `F₀`, and `f` `L`-Lipschitz on a Borel set carrying `σ`
and containing `F₀`, give a global `C L`-Lipschitz extension of `f|F₀` with affine
Carleson constant `C (L² + B)`, `C = C(m, c)`. The Whitney source allocation (the
statement proved by `exists_whitney_source_allocation_proof`) is the hypothesis `h3a`.

Parameters: `D = D_m`, `a = A_W - D_m ≥ 2`, separation `s₀ = 1/2`
(`exists_whitneyBoxes_data_proof`), and the partition constants `H, b, K, N` of
`exists_whitneyBoxes_partition_proof`. The common slope bound is
`L' = κ L`, `κ = max(C_lip, C_fit)`, with `C_lip` from `allocated_node_lipschitz_proof` and
`C_fit` from `node_error_le_source_error_of_leaves`. The final constant is
`C = C_g (1 + κ + κ² + C_c C_e)` with `C_g` from the Whitney transfer, `C_c` from the node
Carleson bound and `C_e` from the node–source comparison. -/
theorem exists_affine_extension_of_source_proof
    (h3a : ∀ (m : ℕ) (c D a b : ℝ) (_hc : 0 < c),
      ∃ A C_B c₂ : ℝ, 0 < A ∧ 0 < C_B ∧ 0 < c₂ ∧ ∀ {ι : Type*} [Countable ι]
        {F₀ : Set (Space m)} (W : WhitneyData m ι F₀ D a), IsCompact F₀ → F₀.Nonempty →
        (∀ j, Metric.infDist (W.center j) F₀ ≤ b * W.radius j) →
        ∀ σ : Measure (Space m), σ ≤ parabolicVolume m →
        (∀ x ∈ F₀, ∀ r : ℝ, 0 < r → ENNReal.ofReal (c * r ^ (m + 2)) ≤ σ (Metric.ball x r)) →
        Nonempty (WhitneySourceAllocation W σ A C_B c₂))
    (m : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
      [FiniteDimensional ℝ Y] (F₀ : Set (Space m)), IsCompact F₀ → F₀.Nonempty →
      ∀ σ : Measure (Space m), σ ≤ parabolicVolume m →
      ∀ T : Set (Space m), MeasurableSet T → F₀ ⊆ T → σ Tᶜ = 0 →
      ∀ (f : Space m → Y) (L : ℝ≥0), LipschitzOnWith L f T →
      (∀ x ∈ F₀, ∀ r : ℝ, 0 < r → ENNReal.ofReal (c * r ^ (m + 2)) ≤ σ (Metric.ball x r)) →
      ∀ B : ℝ, 0 ≤ B →
      (∀ x ∈ F₀, ∫⁻ r in Ioi 0, affineErrorSq σ f x r ∂scaleMeasure ≤ ENNReal.ofReal B) →
      ∃ F : Space m → Y, (∀ x ∈ F₀, F x = f x) ∧ LipschitzWith (C * L) F ∧
        HasAffineCarlesonBound (parabolicVolume m) F (C * ((L : ℝ) ^ 2 + B)) := by
  -- Whitney parameters `D = D_m`, `a = A_W - D_m ≥ 2`.
  have hD1 : (1 : ℝ) ≤ whitneyD m := le_max_left _ _
  have ha : (2 : ℝ) ≤ whitneyA m - whitneyD m := by
    have h104 : (10 : ℝ) ^ 4 = 10000 := by norm_num
    show (2 : ℝ) ≤ 10 ^ 4 * whitneyD m - whitneyD m
    rw [h104]
    linarith
  -- Partition constants, from the Whitney boxes and their overlap bounds.
  obtain ⟨H, b, K, N, hH, hpart⟩ :=
    exists_whitneyBoxes_partition_proof exists_whitneyBoxes_data_proof
      whitneyBoxes_enlarged_overlap_proof m
  -- Allocation constants and moment coefficients.
  obtain ⟨A, C_B, c₂, -, -, hc₂, halloc⟩ :=
    h3a m c (whitneyD m) (whitneyA m - whitneyD m) b hc
  obtain ⟨Cm, -, hmom⟩ :=
    exists_moment_coefficients_proof m (whitneyD m) (whitneyA m - whitneyD m) b A C_B c₂ hc₂
  -- Node Lipschitz constant, separation `1/2`.
  obtain ⟨Clip, hlip⟩ :=
    allocated_node_lipschitz_proof m (whitneyD m) (whitneyA m - whitneyD m) b (1 / 2) A C_B c₂
      Cm (by norm_num)
  -- Node error against source error.
  obtain ⟨Ce, C₁, Cfit, hCe, hC₁, -, herr⟩ :=
    node_error_le_source_error_of_leaves m c (whitneyD m) (whitneyA m - whitneyD m) b A C_B c₂
      Cm hc (allocated_node_estimates_proof m (whitneyD m) (whitneyA m - whitneyD m) A C_B c₂ Cm)
      (fun σ hσ F₀ hF₀ hden => volume_restrict_le_of_source_density_proof c hc σ hσ F₀ hF₀ hden)
      (exists_source_fit_slope_le_proof m c hc)
  -- Node Carleson constant and Whitney transfer constant.
  obtain ⟨Cc, hCc, hcarl⟩ :=
    whitney_node_carleson_le_proof m (whitneyD m) (whitneyA m - whitneyD m)
  obtain ⟨Cg, hCg, htr⟩ :=
    whitney_transfer_unconditional m (whitneyD m) (whitneyA m - whitneyD m) H b K N ha hH
  -- The common slope factor `κ = max(C_lip, C_fit)` and the final constant.
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ≥0, κ = max Clip (Real.toNNReal Cfit) := ⟨_, rfl⟩
  obtain ⟨Cs, hCsdef⟩ : ∃ Cs : ℝ≥0, Cs = Real.toNNReal (Cc * Ce) := ⟨_, rfl⟩
  have hClip : Clip ≤ κ := hκ ▸ le_max_left _ _
  have hCfit : Cfit ≤ (κ : ℝ) :=
    (Real.le_coe_toNNReal Cfit).trans (NNReal.coe_le_coe.mpr (hκ ▸ le_max_right _ _))
  have hCs : Cc * Ce ≤ (Cs : ℝ) := hCsdef ▸ Real.le_coe_toNNReal _
  refine ⟨Cg * (1 + κ + κ ^ 2 + Cs), mul_pos hCg (by positivity), ?_⟩
  intro Y _ _ _ F₀ hF₀ hne σ hσ T hTm hF₀T hTc f L hfL hden B hB hen
  -- Whitney data and smooth partition.
  obtain ⟨W, hW, -, -, hsep⟩ := exists_whitneyBoxes_data_proof m F₀ hF₀ hne
  obtain ⟨P, -⟩ := hpart F₀ hF₀ hne W hW
  have hb : ∀ j, Metric.infDist (W.center j) F₀ ≤ b * W.radius j := P.infDist_center_le
  have hsep' : ∀ i j, i ≠ j →
      1 / 2 * max (W.radius i) (W.radius j) ≤ dist (W.center i) (W.center j) := by
    intro i j hij
    rw [(hW i).2.2, (hW j).2.2, (hW i).2.1, (hW j).2.1]
    have := hsep i j hij
    linarith
  -- The allocation, transported back from the `ULift` reindexing.
  obtain ⟨S'⟩ := halloc W.ulift hF₀ hne (fun j => hb j.down) σ hσ hden
  obtain ⟨S, -⟩ : ∃ S : WhitneySourceAllocation W σ A C_B c₂, True := ⟨S'.ofULift, trivial⟩
  obtain ⟨coef, hcoef⟩ := hmom W hb σ hσ S
  -- The node function `g = S.nodeFunction coef f` and the common slope bound `κ L`.
  have hlipg := hlip W hF₀ hne hb hsep' σ hσ S coef hcoef f L T hTc hF₀T hfL
  have hgL : LipschitzOnWith (κ * L) (S.nodeFunction coef f) W.nodeSet :=
    hlipg.2.2.weaken (mul_le_mul_left hClip _)
  have hfitL : Cfit * (L : ℝ) ≤ ((κ * L : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_mul]
    exact mul_le_mul_of_nonneg_right hCfit L.coe_nonneg
  have herr' := herr W hF₀ hne hb σ hσ hden S coef hcoef f L T hTm hTc hF₀T hfL (κ * L) hfitL
  -- Per-node scale bounds.
  have hnodeF : ∀ p ∈ F₀, ∫⁻ s in Ioi 0,
      constrainedAffineErrorSq W.nodeMeasure (S.nodeFunction coef f) (κ * L) p s
        ∂scaleMeasure ≤ ENNReal.ofReal (Ce * B) := by
    intro p hp
    calc ∫⁻ s in Ioi 0,
          constrainedAffineErrorSq W.nodeMeasure (S.nodeFunction coef f) (κ * L) p s
            ∂scaleMeasure
        ≤ ENNReal.ofReal Ce * ∫⁻ r in Ioi 0, affineErrorSq σ f p r ∂scaleMeasure :=
          lintegral_Ioi_scaleMeasure_le_of_le_comp_mul_proof
            (fun s => constrainedAffineErrorSq W.nodeMeasure (S.nodeFunction coef f) (κ * L) p s)
            (fun r => affineErrorSq σ f p r) 0 Ce C₁ le_rfl hC₁
            (fun s hs => herr'.1 p hp s hs)
      _ ≤ ENNReal.ofReal Ce * ENNReal.ofReal B := mul_le_mul_right (hen p hp) _
      _ = ENNReal.ofReal (Ce * B) := (ENNReal.ofReal_mul hCe).symm
  have hnodeC : ∀ i, ∫⁻ s in Ioi (W.radius i),
      constrainedAffineErrorSq W.nodeMeasure (S.nodeFunction coef f) (κ * L) (W.center i) s
        ∂scaleMeasure ≤ ENNReal.ofReal (Ce * B) := by
    intro i
    calc ∫⁻ s in Ioi (W.radius i),
          constrainedAffineErrorSq W.nodeMeasure (S.nodeFunction coef f) (κ * L) (W.center i) s
            ∂scaleMeasure
        ≤ ENNReal.ofReal Ce * ∫⁻ r in Ioi 0, affineErrorSq σ f (S.anchor i) r ∂scaleMeasure :=
          lintegral_Ioi_scaleMeasure_le_of_le_comp_mul_proof
            (fun s => constrainedAffineErrorSq W.nodeMeasure (S.nodeFunction coef f) (κ * L)
              (W.center i) s)
            (fun r => affineErrorSq σ f (S.anchor i) r) (W.radius i) Ce C₁
            (W.radius_pos i).le hC₁ (fun s hs => herr'.2 i s hs.le)
      _ ≤ ENNReal.ofReal Ce * ENNReal.ofReal B :=
          mul_le_mul_right (hen _ (S.anchor_mem i)) _
      _ = ENNReal.ofReal (Ce * B) := (ENNReal.ofReal_mul hCe).symm
  -- Node Carleson bound and Whitney transfer.
  have hcarlW := hcarl W (S.nodeFunction coef f) (κ * L) (Ce * B) (mul_nonneg hCe hB)
    hnodeF hnodeC
  obtain ⟨hFlip, hFcarl⟩ :=
    htr W hF₀ hne P (S.nodeFunction coef f) (κ * L) hgL (Cc * (Ce * B))
      (mul_nonneg hCc (mul_nonneg hCe hB)) hcarlW
  refine ⟨whitneyFilling P.toWhitneyWeights (S.nodeFunction coef f), ?_, ?_, ?_⟩
  · intro x hx
    simp only [whitneyFilling, hx, ↓reduceIte]
    exact hlipg.2.1 x hx
  · refine hFlip.weaken ?_
    rw [← mul_assoc]
    refine mul_le_mul_left (mul_le_mul_right ?_ Cg) L
    calc κ ≤ 1 + κ := le_add_self
      _ ≤ 1 + κ + κ ^ 2 := le_self_add
      _ ≤ 1 + κ + κ ^ 2 + Cs := le_self_add
  · refine hasAffineCarlesonBound_of_le hFcarl ?_
    have hκ0 : (0 : ℝ) ≤ κ := κ.coe_nonneg
    have hCs0 : (0 : ℝ) ≤ Cs := Cs.coe_nonneg
    have hM : (κ : ℝ) ^ 2 ≤ 1 + κ + κ ^ 2 + Cs := by linarith
    have hM' : Cc * Ce ≤ 1 + κ + κ ^ 2 + Cs := by nlinarith [sq_nonneg (κ : ℝ)]
    have h1 : (κ : ℝ) ^ 2 * (L : ℝ) ^ 2 ≤ (1 + κ + κ ^ 2 + Cs) * (L : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hM (sq_nonneg _)
    have h2 : Cc * Ce * B ≤ (1 + κ + κ ^ 2 + Cs) * B := mul_le_mul_of_nonneg_right hM' hB
    have h3 : ((κ : ℝ) * L) ^ 2 + Cc * (Ce * B) ≤
        (1 + κ + κ ^ 2 + Cs) * ((L : ℝ) ^ 2 + B) := by
      nlinarith
    push_cast
    calc (Cg : ℝ) * (((κ : ℝ) * L) ^ 2 + Cc * (Ce * B))
        ≤ Cg * ((1 + κ + κ ^ 2 + Cs) * ((L : ℝ) ^ 2 + B)) :=
          mul_le_mul_of_nonneg_left h3 Cg.coe_nonneg
      _ = Cg * (1 + κ + κ ^ 2 + Cs) * ((L : ℝ) ^ 2 + B) := by ring

end ParabolicRectifiability
