import ParabolicRectifiability.QuantitativeCharacterization.Statements.PiecesComponents
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Ambient.RootCovering

/-! # The one-reference certificate

Proof of `dp2_OneReferenceCertificateStatement`. It extends the single-ball covering
`damb_covering` from the ambient reference to an
arbitrary `ρ : Reference n k L` with `L ≥ 2`: for `a ∈ supp ν` and `R > 0`, the index `{0}`, the
reference `ρ`, the centre `a`, the radius `2R`, the empty bad set and the whole tested cylinder
`rootPairs ν a R` as the only scale set. The distance floor is `0` since `supp ν ⊆ Γ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- The single-ball covering of the root `P(a,R)` by the model ball `P(a,2R)` with an arbitrary
`L`-reference `ρ` whose carrier contains `supp ν`, `L ≥ 2`. -/
def dp2_orc_covering {n k : ℕ} {L : ℝ} (hL : 2 ≤ L) (ρ : Reference n k L)
    (ν : Measure (Space n)) (hsupp : ν.support ⊆ ρ.carrier) (a : Space n) (ha : a ∈ ν.support)
    (R : ℝ) (hR : 0 < R) : RegularMixedCovering k ((2 : ℝ) ^ k) L ν a R where
  index := {0}
  reference := fun _ => ρ
  center := fun _ => a
  radius := fun _ => 2 * R
  badSet := ∅
  scaleSet := fun _ => rootPairs ν a R
  center_mem_support := fun _ => ha
  radius_pos := fun _ => by positivity
  ball_subset := fun _ => Metric.ball_subset_ball (by nlinarith)
  ball_meets_carrier := fun _ => ⟨a, Metric.mem_ball_self (by positivity), hsupp ha⟩
  root_packing := by
    rw [damb_tsum_singleton]
    show ENNReal.ofReal (2 * R) ^ k ≤ ENNReal.ofReal ((2 : ℝ) ^ k * R ^ k)
    rw [← ENNReal.ofReal_pow (by positivity), mul_pow]
  local_packing := fun b s hs => by
    rw [damb_tsum_singleton]
    split_ifs with h
    · have h2 : 2 * R ≤ s := h.2
      show ENNReal.ofReal (2 * R) ^ k ≤ ENNReal.ofReal ((2 : ℝ) ^ k * s ^ k)
      rw [← ENNReal.ofReal_pow (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc (2 * R) ^ k ≤ s ^ k := by gcongr
        _ ≤ (2 : ℝ) ^ k * s ^ k :=
          le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
    · exact zero_le
  measurable_badSet := MeasurableSet.empty
  measurable_scaleSet := fun _ => damb_measurableSet_rootPairs ν a R
  badSet_subset := empty_subset _
  scaleSet_subset := fun _ => Subset.rfl
  bad_inter_scale_null := fun _ => measure_mono_null (fun _ hp => hp.1) measure_empty
  scale_inter_scale_null := fun i j hij =>
    (hij (Subtype.ext ((Set.mem_singleton_iff.mp i.2).trans
      (Set.mem_singleton_iff.mp j.2).symm))).elim
  cover_null := measure_mono_null
    (fun _ hp => (hp.2 (Or.inr (Set.mem_iUnion.mpr ⟨⟨0, Set.mem_singleton 0⟩, hp.1⟩))).elim)
    measure_empty
  scaleSet_cover := fun _ p hp => by
    have hp' : p.1 ∈ Metric.ball a R ∩ ν.support ∧ p.2 ∈ Ioo 0 R := hp
    obtain ⟨⟨hball, hz⟩, hpos, hlt⟩ := hp'
    have h2 : p.1 ∈ Metric.ball a (2 * R) := Metric.ball_subset_ball (by linarith) hball
    have hdist : L⁻¹ * Metric.infDist p.1 ρ.carrier ≤ p.2 := by
      rw [Metric.infDist_zero_of_mem (hsupp hz), mul_zero]
      exact hpos.le
    have hlt2 : p.2 < 2 * R := by linarith
    exact ⟨⟨hball, h2⟩, hdist, hlt2⟩
  bad_bound := measure_empty.trans_le (zero_le)

/-- **The one-reference certificate**: the type is
`dp2_OneReferenceCertificateStatement`. -/
theorem dp2_one_reference_certificate_proof : dp2_OneReferenceCertificateStatement :=
  fun _ _ _ hL ρ ν hac hsupp =>
    ⟨hac, fun a ha R hR => ⟨dp2_orc_covering hL ρ ν hsupp a ha R hR⟩⟩

end ParabolicRectifiability.QuantitativeCharacterization
