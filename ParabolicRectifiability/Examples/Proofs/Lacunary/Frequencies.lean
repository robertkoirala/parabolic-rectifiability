import ParabolicRectifiability.Examples.Proofs.Lacunary.FrequencyLemmas

/-! # Assembly of the lacunary frequency construction

* `e2_lacunaryFrequencyExistence` is the unfolded body of `BetaP.LacunaryFrequencyExistence`
  (definitionally, not syntactically, equal). It imports no `BetaP` module; the theorem
  `BetaP.c2_lacunaryFrequencyExistence` closes the `BetaP` type by `exact`.
* `e2_lacunary_convergence` has exactly the type of `lacunary_series_convergence`.
* `e2_nonregular_frequencies_of`, `e2_exponent_frequencies_of`: the frequency witnesses of the
  two amplitude sequences, **in implication form over the existence body**, so that statements
  taking `hFreq : LacunaryFrequencyExistence` apply them to `hFreq` instead of reconstructing
  frequencies.
-/

noncomputable section

namespace ParabolicRectifiability.Examples

/-- **Existence of frequencies.** For amplitudes `0 < a_j ≤ 1` there are frequencies with
`IsLacunaryData a N`. The unfolded body of
`BetaP.LacunaryFrequencyExistence`. -/
theorem e2_lacunaryFrequencyExistence :
    ∀ a : ℕ → ℝ, (∀ j, 0 < a j) → (∀ j, a j ≤ 1) → ∃ N : ℕ → ℕ, IsLacunaryData a N :=
  fun a ha ha1 => ⟨e2_lacunaryFrequency a, e2_lacunaryState_assembly e2_lacunaryStep_spec a ha ha1⟩

/-- **Convergence of the lacunary series.** Exactly the type of `lacunary_series_convergence`: under the standing
hypotheses the series converges absolutely at every `t` and uniformly on `ℝ`. Only the
summable nonnegative majorant of `E2LacunaryWeightStatement` is used (`0 < ε ≤ 3/16` is not needed). -/
theorem e2_lacunary_convergence : LacunaryConvergenceStatement := by
  intro ε a N _ _ hD
  obtain ⟨hpos, -, -, hsum, -⟩ := e2_lacunaryWeight a N hD
  exact e2_lacunary_weierstrass ε a N (fun j => (hpos j).le) hsum

/-- Frequencies for the nonregular amplitudes `a_j = (j+1)^{-1/2}`, from any proof
of the existence body (in particular from `hFreq : BetaP.LacunaryFrequencyExistence`). -/
theorem e2_nonregular_frequencies_of
    (hF : ∀ a : ℕ → ℝ, (∀ j, 0 < a j) → (∀ j, a j ≤ 1) → ∃ N : ℕ → ℕ, IsLacunaryData a N) :
    ∃ N : ℕ → ℕ, IsLacunaryData nonregularAmplitude N :=
  hF _ (fun j => (e2_nonregularAmplitude_admissible j).1)
    (fun j => (e2_nonregularAmplitude_admissible j).2)

/-- Frequencies for the exponent amplitudes with `c₀ = log 2 / 2`, from any proof of the
existence body. -/
theorem e2_exponent_frequencies_of
    (hF : ∀ a : ℕ → ℝ, (∀ j, 0 < a j) → (∀ j, a j ≤ 1) → ∃ N : ℕ → ℕ, IsLacunaryData a N) :
    ∃ N : ℕ → ℕ, IsLacunaryData (exponentAmplitude (Real.log 2 / 2)) N := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨hpos, hle⟩ := e2_exponentAmplitude_admissible (Real.log 2 / 2) (half_pos hlog)
  exact hF _ hpos (hle.mpr (half_le_self hlog.le))

end ParabolicRectifiability.Examples
