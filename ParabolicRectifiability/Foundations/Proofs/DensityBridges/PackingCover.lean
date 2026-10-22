import ParabolicRectifiability.Foundations.Statements.DensityBridges
import ParabolicRectifiability.Characterization.Statements.SourceTransfer
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.ElementaryLemmas

/-! # The fixed-slack covering estimate

Proof of `fpack_restrict_ball_le_add_of_fivefold`, as
`fpack_restrict_ball_le_add_of_fivefold_proof`. The fivefold selection
`FivefoldSelectionStatement` is the first hypothesis. The good-radius and finite-packing
statements enter through their proofs `fpack_exists_good_radius_proof` and
`fpack_tsum_le_of_finite_packing_proof`, so no extra premise is needed.

Route. Let `N` be the
`ρ₀`-null density exception. The index set consists of the good pairs `(z, r)`: centre
`z ∈ (K ∩ P(q,ρ)) \ N`, radius `0 < r < 5ρ` and good **outer** mass
`ρ₀(P(z,r)) ≤ (A+ε) r^k`. Fivefold selection is applied to the **inner** balls `P(z, r/5)`; it
returns a countable `J` with disjoint inner balls whose fivefold dilates, the outer balls
`P(z_j, 5 (r_j/5)) = P(z_j, r_j)`, cover every good centre. By the good-radius statement every
point of `(K ∩ P(q,ρ)) \ N` is a good centre, so countable subadditivity bounds the mass by
`5^k (A+ε) ∑_j (r_j/5)^k`, and the finite-packing statement at `(q,ρ)` bounds the sum of inner radii by `C_K ρ^k`.
No containment of the outer balls in `P(q,ρ)` is used; `A = 0` and `C_K = 0` need no separate
case. Helper prefix `fbfb2_`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- The good outer mass bound `(A+ε) r^k`, rewritten through the inner radius `r/5`:
`ofReal ((A+ε) r^k) = ofReal ((A+ε) 5^k) · ofReal (r/5)^k`. -/
theorem fbfb2_ofReal_good_bound (A ε r : ℝ) (hAε : 0 ≤ A + ε) (hr : 0 ≤ r) (k : ℕ) :
    ENNReal.ofReal ((A + ε) * r ^ k) =
      ENNReal.ofReal ((A + ε) * 5 ^ k) * ENNReal.ofReal (r / 5) ^ k := by
  rw [← ENNReal.ofReal_pow (div_nonneg hr (by norm_num)),
    ← ENNReal.ofReal_mul (mul_nonneg hAε (by positivity))]
  congr 1
  have h : (r / 5 * 5) ^ k = r ^ k := by
    congr 1
    ring
  rw [← h, mul_pow]
  ring

theorem fpack_restrict_ball_le_add_of_fivefold_proof
    (h5 : Characterization.FivefoldSelectionStatement) :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ K : Set (Space n), MeasurableSet K →
    ∀ R₀ C_K : ℝ, 0 < R₀ → 0 ≤ C_K →
    (∀ (q : Space n) (ρ : ℝ), 0 < ρ → ρ ≤ R₀ →
      ∀ (l : ℕ) (z : Fin l → Space n) (r : Fin l → ℝ),
        (∀ i, z i ∈ K ∩ Metric.ball q ρ) →
        (∀ i, 0 < r i ∧ r i ≤ ρ) →
        (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
        (∑ i, ENNReal.ofReal (r i) ^ k) ≤ ENNReal.ofReal (C_K * ρ ^ k)) →
    ∀ ρ₀ : Measure (Space n), IsFiniteMeasureOnCompacts ρ₀ → ρ₀.InnerRegular →
    ∀ A : ℝ, 0 ≤ A →
    (∀ᵐ z ∂ρ₀, z ∈ K → lowerDensity ρ₀ k z ≤ ENNReal.ofReal A) →
    ∀ (q : Space n) (ρ : ℝ), 0 < ρ → ρ ≤ R₀ →
    ∀ ε : ℝ, 0 < ε →
      ρ₀.restrict K (Metric.ball q ρ) ≤ ENNReal.ofReal (5 ^ k * C_K * (A + ε) * ρ ^ k) := by
  intro n _hn k _hk1 _hkn K hK R₀ C_K _hR₀ _hC hpack ρ₀ _hfin _hreg A hA hae q ρ hρ hρR ε hε
  have hAε : 0 ≤ A + ε := by linarith
  -- The source-null density exception `N`, kept explicit.
  obtain ⟨N, hN_def⟩ : ∃ N : Set (Space n),
      N = {z | ¬ (z ∈ K → lowerDensity ρ₀ k z ≤ ENNReal.ofReal A)} := ⟨_, rfl⟩
  have hN : ρ₀ N = 0 := by
    rw [hN_def]
    exact ae_iff.1 hae
  -- Fivefold selection on the inner balls `P(z, r/5)` of the good pairs `(z, r)`.
  obtain ⟨J, hJc, hJd, hJcov⟩ := h5 (Space n)
    {p : Space n × ℝ // p.1 ∈ K ∩ Metric.ball q ρ ∧ p.1 ∉ N ∧ 0 < p.2 ∧ p.2 < 5 * ρ ∧
      ρ₀ (Metric.ball p.1 p.2) ≤ ENNReal.ofReal ((A + ε) * p.2 ^ k)}
    (fun p => p.1.1) (fun p => p.1.2 / 5)
    (fun p => div_pos p.2.2.2.1 (by norm_num))
    ⟨ρ, fun p => by
      show p.1.2 / 5 ≤ ρ
      linarith [p.2.2.2.2.1]⟩
  -- Every point of `(P(q,ρ) ∩ K) \ N` lies in a selected outer ball `P(z_j, 5 (r_j/5))`.
  have hcover : Metric.ball q ρ ∩ K ⊆ N ∪ ⋃ j ∈ J, Metric.ball j.1.1 (5 * (j.1.2 / 5)) := by
    intro z hz
    by_cases hzN : z ∈ N
    · exact Or.inl hzN
    · right
      have hzN' := hzN
      rw [hN_def] at hzN'
      simp only [Set.mem_ofPred_eq, not_not] at hzN'
      have hdens : lowerDensity ρ₀ k z ≤ ENNReal.ofReal A := hzN' hz.2
      obtain ⟨r, hr0, hr5, hrm⟩ :=
        fpack_exists_good_radius_proof ρ₀ k z A hA hdens ε hε (5 * ρ) (by linarith)
      obtain ⟨j, hjJ, hzj⟩ := hJcov ⟨(z, r), ⟨hz.2, hz.1⟩, hzN, hr0, hr5, hrm⟩
      exact Set.mem_biUnion hjJ hzj
  -- Good outer masses, written through the inner radii.
  have hmass : ∀ j : J, ρ₀ (Metric.ball j.1.1.1 (5 * (j.1.1.2 / 5))) ≤
      ENNReal.ofReal ((A + ε) * 5 ^ k) * ENNReal.ofReal (j.1.1.2 / 5) ^ k := by
    intro j
    obtain ⟨_, _, hpos, _, hgood⟩ := j.1.2
    have h5r : 5 * (j.1.1.2 / 5) = j.1.1.2 := by ring
    rw [h5r]
    exact hgood.trans (le_of_eq (fbfb2_ofReal_good_bound A ε j.1.1.2 hAε hpos.le k))
  -- Finite packing at `(q, ρ)` on the disjoint inner family indexed by `J`.
  have hP2 : (∑' j : J, ENNReal.ofReal (j.1.1.2 / 5) ^ k) ≤ ENNReal.ofReal (C_K * ρ ^ k) :=
    fpack_tsum_le_of_finite_packing_proof k K C_K q ρ (hpack q ρ hρ hρR)
      (ι := J) (fun j => j.1.1.1) (fun j => j.1.1.2 / 5)
      (fun j => j.1.2.1)
      (fun j => ⟨div_pos j.1.2.2.2.1 (by norm_num), by
        show j.1.1.2 / 5 ≤ ρ
        linarith [j.1.2.2.2.2.1]⟩)
      (fun i j hij => hJd i.2 j.2 (fun h => hij (Subtype.ext h)))
  have hsum : ∑' j : J, ρ₀ (Metric.ball j.1.1.1 (5 * (j.1.1.2 / 5))) ≤
      ENNReal.ofReal ((A + ε) * 5 ^ k) * ENNReal.ofReal (C_K * ρ ^ k) := by
    calc ∑' j : J, ρ₀ (Metric.ball j.1.1.1 (5 * (j.1.1.2 / 5)))
        ≤ ∑' j : J, ENNReal.ofReal ((A + ε) * 5 ^ k) * ENNReal.ofReal (j.1.1.2 / 5) ^ k :=
          ENNReal.tsum_le_tsum hmass
      _ = ENNReal.ofReal ((A + ε) * 5 ^ k) * ∑' j : J, ENNReal.ofReal (j.1.1.2 / 5) ^ k :=
          ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal ((A + ε) * 5 ^ k) * ENNReal.ofReal (C_K * ρ ^ k) := by
          gcongr
  calc ρ₀.restrict K (Metric.ball q ρ) = ρ₀ (Metric.ball q ρ ∩ K) := Measure.restrict_apply' hK
    _ ≤ ρ₀ (N ∪ ⋃ j ∈ J, Metric.ball j.1.1 (5 * (j.1.2 / 5))) := measure_mono hcover
    _ ≤ ρ₀ N + ρ₀ (⋃ j ∈ J, Metric.ball j.1.1 (5 * (j.1.2 / 5))) := measure_union_le _ _
    _ = ρ₀ (⋃ j ∈ J, Metric.ball j.1.1 (5 * (j.1.2 / 5))) := by rw [hN, zero_add]
    _ ≤ ∑' j : J, ρ₀ (Metric.ball j.1.1.1 (5 * (j.1.1.2 / 5))) :=
        measure_biUnion_le ρ₀ hJc (fun j => Metric.ball j.1.1 (5 * (j.1.2 / 5)))
    _ ≤ ENNReal.ofReal ((A + ε) * 5 ^ k) * ENNReal.ofReal (C_K * ρ ^ k) := hsum
    _ = ENNReal.ofReal (5 ^ k * C_K * (A + ε) * ρ ^ k) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hAε (by positivity))]
        congr 1
        ring

end ParabolicRectifiability.Foundations
