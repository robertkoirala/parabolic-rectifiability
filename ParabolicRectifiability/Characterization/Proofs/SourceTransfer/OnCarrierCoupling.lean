import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.TransferStatements

/-! # The on-carrier coupling

Proves `b3_onCarrierCoupling` (`OnCarrierCouplingStatement`).

For replacement data `(I, z_i, r_i, E_i)`, write `G_A = adrGoodSet Γ ν k A` and
`B_i = Γ ∩ P(z_i, r_i)`. The coupling is
`π_A = (y ↦ (y,y))_# (ν⌊G_A) + Σ_i (ν⌊E_i) ⊗ (σ(B_i)⁻¹ • σ⌊B_i)`.

* ADR and `σ(Γᶜ) = 0` give `0 < σ(B_i) < ∞`, so each normalized `σ(B_i)⁻¹ • σ⌊B_i` is a
  probability measure and the `i`-th product has first marginal `ν⌊E_i`.
* `G_A` is Borel **only through the exact allocation**: `G_A ⊆ Γ` by definition and
  `⋃ E_i = Γ \ G_A`, so `G_A = Γ \ ⋃ E_i`. With `ν(Γᶜ) = 0` this gives
  `ν = ν⌊G_A + Σ_i ν⌊E_i` (the first marginal).
* The second marginal of the `i`-th product is `ν(E_i) • σ(B_i)⁻¹ • σ⌊B_i
  = (ν(E_i)/σ(B_i)) • σ⌊B_i`; the sum is `b3_replacedSource` exactly.
* `π_A` is carried by the Borel set `(diag ∩ G_A × X) ∪ ⋃_i E_i × B_i`, which gives the
  support conjunct and, with `E_i ⊆ P(z_i, 5r_i)` and `d(x,z_i) ≥ 20 r_i`, the localization
  `d(x,v) < s + 6 r_i < 2s` (since `s > 15 r_i`).

No condition `ν ≪ σ` is used.
-/

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace ParabolicRectifiability.Characterization.SourceTransferTree

open ParabolicRectifiability.Foundations

/-- The reference measure does not charge the complement of its carrier. -/
theorem b3oncpl_measure_compl {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)}
    {σ : Measure (Space n)} (hσ : IsADRCarrier k c C Γ σ) : σ Γᶜ = 0 := by
  rw [← hσ.support_eq]
  exact Measure.measure_compl_support

/-- A relative ball `Γ ∩ P(z,r)` centred on the carrier has positive finite reference mass. -/
theorem b3oncpl_relBall_ne_zero_ne_top {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)}
    {σ : Measure (Space n)} (hσ : IsADRCarrier k c C Γ σ) {z : Space n} (hz : z ∈ Γ) {r : ℝ}
    (hr : 0 < r) : σ (Γ ∩ Metric.ball z r) ≠ 0 ∧ σ (Γ ∩ Metric.ball z r) ≠ ∞ := by
  have hball : σ (Γ ∩ Metric.ball z r) = σ (Metric.ball z r) := by
    rw [inter_comm]
    exact measure_inter_conull (b3oncpl_measure_compl hσ)
  rw [hball]
  refine ⟨?_, ?_⟩
  · have h1 : 0 < ENNReal.ofReal (c * r ^ k) :=
      ENNReal.ofReal_pos.2 (mul_pos hσ.lower_pos (pow_pos hr k))
    exact (lt_of_lt_of_le h1 (hσ.lower z hz r hr)).ne'
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hσ.upper z hz r hr)

/-- The normalized restriction `σ(B)⁻¹ • σ⌊B` is a probability measure when `0 < σ(B) < ∞`. -/
theorem b3oncpl_isProbabilityMeasure_normalized {n : ℕ} {σ : Measure (Space n)}
    {B : Set (Space n)} (h0 : σ B ≠ 0) (htop : σ B ≠ ∞) :
    IsProbabilityMeasure ((σ B)⁻¹ • σ.restrict B) :=
  ⟨by rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
    ENNReal.inv_mul_cancel h0 htop]⟩

/-- The second marginal of `μ ⊗ (σ(B)⁻¹ • σ⌊B)` for a finite `μ`: `(μ(X)/σ(B)) • σ⌊B`. -/
theorem b3oncpl_snd_prod_normalized {n : ℕ} {σ : Measure (Space n)} {B : Set (Space n)}
    (μ : Measure (Space n)) [IsFiniteMeasure μ]
    [IsProbabilityMeasure ((σ B)⁻¹ • σ.restrict B)] :
    (μ.prod ((σ B)⁻¹ • σ.restrict B)).snd = (μ univ / σ B) • σ.restrict B := by
  ext1 s hs
  rw [Measure.snd_apply hs, ← univ_prod, Measure.prod_prod, Measure.smul_apply,
    Measure.smul_apply, smul_eq_mul, smul_eq_mul, div_eq_mul_inv, mul_assoc]

/-- The on-carrier coupling
`π_A = (y ↦ (y,y))_# (ν⌊G_A) + Σ_i (ν⌊E_i) ⊗ (σ(B_i)⁻¹ • σ⌊B_i)`. -/
def b3oncpl_coupling {n : ℕ} (k : ℕ) (Γ : Set (Space n)) (σ ν : Measure (Space n)) (A : ℝ)
    (I : Set ℕ) (z : I → Space n) (r : I → ℝ) (E : I → Set (Space n)) :
    Measure (Space n × Space n) :=
  (ν.restrict (adrGoodSet Γ ν k A)).map (fun y => (y, y)) +
    Measure.sum (fun i : I => (ν.restrict (E i)).prod
      ((σ (Γ ∩ Metric.ball (z i) (r i)))⁻¹ • σ.restrict (Γ ∩ Metric.ball (z i) (r i))))

/-- The on-carrier coupling: `OnCarrierCouplingStatement`. -/
theorem b3_onCarrierCoupling_proof : OnCarrierCouplingStatement := by
  intro n k c C C₀ C₁ Γ σ hσ ν hν hνΓ A _hA I z r E hD
  unfold b3_IsReplacementData at hD
  obtain ⟨hzr, -, -, hEm, hE5, hEdisj, hEU, -, -, -⟩ := hD
  have hΓm : MeasurableSet Γ := hσ.isClosed.measurableSet
  -- `G_A` is Borel only through the exact allocation `⋃ E_i = Γ \ G_A`.
  have hGsub : adrGoodSet Γ ν k A ⊆ Γ := fun y hy => hy.1
  have hGeq : adrGoodSet Γ ν k A = Γ \ ⋃ i, E i := by
    rw [hEU, Set.sdiff_sdiff_cancel_left hGsub]
  have hGm : MeasurableSet (adrGoodSet Γ ν k A) := by
    rw [hGeq]
    exact hΓm.diff (MeasurableSet.iUnion hEm)
  -- Exact allocation of the source: `ν = ν⌊G_A + Σ_i ν⌊E_i`.
  have hνres : ν.restrict Γ = ν := Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hνΓ)
  have hΓeq : Γ = adrGoodSet Γ ν k A ∪ ⋃ i, E i := by
    rw [hEU, Set.union_sdiff_cancel hGsub]
  have hdisj : Disjoint (adrGoodSet Γ ν k A) (⋃ i, E i) := by
    rw [hEU]
    exact Set.disjoint_sdiff_right
  have halloc : ν = ν.restrict (adrGoodSet Γ ν k A) +
      Measure.sum (fun i : I => ν.restrict (E i)) := by
    calc ν = ν.restrict Γ := hνres.symm
      _ = ν.restrict (adrGoodSet Γ ν k A ∪ ⋃ i, E i) := by rw [← hΓeq]
      _ = _ := by
        rw [Measure.restrict_union hdisj (MeasurableSet.iUnion hEm),
          Measure.restrict_iUnion hEdisj hEm]
  -- The normalized reference pieces.
  have hBm : ∀ i : I, MeasurableSet (Γ ∩ Metric.ball (z i) (r i)) :=
    fun i => hΓm.inter measurableSet_ball
  have hprob : ∀ i : I, IsProbabilityMeasure
      ((σ (Γ ∩ Metric.ball (z i) (r i)))⁻¹ • σ.restrict (Γ ∩ Metric.ball (z i) (r i))) :=
    fun i =>
      have h := b3oncpl_relBall_ne_zero_ne_top hσ (hzr i).1 (hzr i).2
      b3oncpl_isProbabilityMeasure_normalized h.1 h.2
  have hdiag : Measurable (fun y : Space n => (y, y)) := measurable_id.prodMk measurable_id
  -- First marginal.
  have hfst : (b3oncpl_coupling k Γ σ ν A I z r E).fst = ν := by
    rw [b3oncpl_coupling, Measure.fst_add, Measure.fst_sum,
      Measure.fst_map_prodMk (X := fun y => y) (Y := fun y => y) measurable_id measurable_id,
      Measure.map_id']
    refine Eq.trans ?_ halloc.symm
    refine congrArg (ν.restrict (adrGoodSet Γ ν k A) + ·)
      (congrArg Measure.sum (funext fun i => ?_))
    have := hprob i
    exact Measure.fst_prod
  -- Second marginal.
  have hsnd : (b3oncpl_coupling k Γ σ ν A I z r E).snd = b3_replacedSource k Γ σ ν A I z r E := by
    rw [b3oncpl_coupling, Measure.snd_add, Measure.snd_sum,
      Measure.snd_map_prodMk (X := fun y => y) (Y := fun y => y) measurable_id measurable_id,
      Measure.map_id', b3_replacedSource]
    refine congrArg (ν.restrict (adrGoodSet Γ ν k A) + ·)
      (congrArg Measure.sum (funext fun i => ?_))
    have := hprob i
    have h := b3oncpl_snd_prod_normalized (σ := σ) (B := Γ ∩ Metric.ball (z i) (r i))
      (ν.restrict (E i))
    rw [Measure.restrict_apply_univ] at h
    exact h
  -- Finiteness.
  have hfin : IsFiniteMeasure (b3oncpl_coupling k Γ σ ν A I z r E) :=
    ⟨by
      rw [← Measure.fst_univ (ρ := b3oncpl_coupling k Γ σ ν A I z r E), hfst]
      exact measure_lt_top ν univ⟩
  -- The coupling is carried by a Borel set of admissible pairs.
  have hSm : MeasurableSet (({p : Space n × Space n | p.2 = p.1} ∩
      Prod.fst ⁻¹' adrGoodSet Γ ν k A) ∪
        ⋃ i : I, E i ×ˢ (Γ ∩ Metric.ball (z i) (r i))) :=
    ((measurableSet_eq_fun measurable_snd measurable_fst).inter (measurable_fst hGm)).union
      (MeasurableSet.iUnion fun i => (hEm i).prod (hBm i))
  have hS : ∀ᵐ p ∂(b3oncpl_coupling k Γ σ ν A I z r E),
      p ∈ ({p : Space n × Space n | p.2 = p.1} ∩ Prod.fst ⁻¹' adrGoodSet Γ ν k A) ∪
        ⋃ i : I, E i ×ˢ (Γ ∩ Metric.ball (z i) (r i)) := by
    rw [b3oncpl_coupling]
    refine ae_add_measure_iff.2 ⟨?_, Measure.ae_sum_iff.2 fun i => ?_⟩
    · refine (ae_map_iff hdiag.aemeasurable hSm).2 ?_
      filter_upwards [ae_restrict_mem hGm] with y hy
      exact mem_union_left _
        (mem_inter (show ((y, y) : Space n × Space n).2 = (y, y).1 from rfl) hy)
    · have := hprob i
      refine (Measure.ae_prod_mem_iff_ae_ae_mem hSm).2 ?_
      filter_upwards [ae_restrict_mem (hEm i)] with y hy
      filter_upwards [Measure.ae_smul_measure (ae_restrict_mem (hBm i))
        (σ (Γ ∩ Metric.ball (z i) (r i)))⁻¹] with v hv
      exact mem_union_right _ (mem_iUnion.2 ⟨i, mk_mem_prod hy hv⟩)
  refine ⟨b3oncpl_coupling k Γ σ ν A I z r E, hfin, hfst, hsnd, ?_, ?_⟩
  · -- Support: pairs stay in place in `G_A` or move from `E_i` into `B_i`.
    filter_upwards [hS] with p hp
    rcases hp with ⟨h2, hG⟩ | hp
    · exact Or.inl ⟨h2, hG⟩
    · obtain ⟨i, hy, hv⟩ := mem_iUnion.1 hp
      exact Or.inr ⟨i, hy, hv⟩
  · -- Localization outside the excluded balls.
    intro x _ hx s hs
    filter_upwards [hS] with p hp hp1
    rw [Metric.mem_ball] at hp1 ⊢
    rcases hp with ⟨h2, -⟩ | hp
    · have h2' : p.2 = p.1 := h2
      rw [h2']
      linarith
    · obtain ⟨i, hy, hv⟩ := mem_iUnion.1 hp
      have hxz : 20 * r i ≤ dist x (z i) := not_lt.1 (fun h => hx i (Metric.mem_ball.2 h))
      have h1 : dist p.1 (z i) < 5 * r i := Metric.mem_ball.1 (hE5 i hy).2
      have h2 : dist p.2 (z i) < r i := Metric.mem_ball.1 hv.2
      have hri : 0 < r i := (hzr i).2
      have t1 := dist_triangle x p.1 (z i)
      have t2 := dist_triangle p.2 (z i) x
      have t3 := dist_comm x p.1
      have t4 := dist_comm (z i) x
      linarith

/-- Check that the proof has the type `OnCarrierCouplingStatement`. -/
example : OnCarrierCouplingStatement := b3_onCarrierCoupling_proof

end ParabolicRectifiability.Characterization.SourceTransferTree
