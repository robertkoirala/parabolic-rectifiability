import ParabolicRectifiability.BetaP.Proofs.Counterexamples.RowStatements

/-! # Squeeze limit

Proof of `C2SqueezeLimitStatement`: `C ε^p → 0`, squeeze `g → 0⁺`, compose with `Φ`. -/

open MeasureTheory Set Filter Topology

namespace ParabolicRectifiability.BetaP

theorem c2_squeeze_limit_proof : C2SqueezeLimitStatement := by
  intro Φ hΦ g C p ε₀ c hC hp hε₀ hc hg
  have hpow : Tendsto (fun ε : ℝ => C * ε ^ p) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ => ε ^ p) (𝓝 0) (𝓝 ((0 : ℝ) ^ p)) :=
      (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto
    rw [Real.zero_rpow hp.ne'] at h0
    have := (h0.const_mul C).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ ε₀ ∧ 0 < ε := by
    have hmem : Ioc (0 : ℝ) ε₀ ∈ 𝓝[>] (0 : ℝ) := Ioc_mem_nhdsGT hε₀
    exact Filter.mem_of_superset hmem fun ε h => ⟨h.2, h.1⟩
  have hgt : Tendsto g (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hpow
      (hsmall.mono fun ε h => (hg ε h.2 h.1).1.le)
      (hsmall.mono fun ε h => (hg ε h.2 h.1).2), ?_⟩
    exact hsmall.mono fun ε h => (hg ε h.2 h.1).1
  have hcomp : Tendsto (Φ ∘ g) (𝓝[>] 0) (𝓝 0) := hΦ.comp hgt
  have hlt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Φ (g ε) < c := hcomp.eventually (gt_mem_nhds hc)
  obtain ⟨ε, h1, h2⟩ := (hlt.and hsmall).exists
  exact ⟨ε, h2.2, h2.1, h1⟩

end ParabolicRectifiability.BetaP
