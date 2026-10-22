import ParabolicRectifiability.Characterization.Proofs.Replacement.Components

/-! # Replacement of the bad region

The theorem `bad_region_replacement_of_leaves` has exactly the type `ReplacementStatement` of
`bad_region_replacement`. It is assembled from the four component estimates and the two
input estimates `b3_rp_input_fivefold` and `b3_rp_input_goodDomination`.

Assembly, for `C₀ = max (C 5^k) 1` and `C₁ = max ((5^k + 205^k)/c) 1` (positive before any
ADR hypothesis, as the quantifier order of the statement requires):
* (i) gives `G_A` closed (hence Borel), nonempty, and the bad-mass clause; in particular
  `σ(Ω_A) < ∞`;
* (ii.a), applied to `G = G_A ⊆ Γ`, gives the disjoint Whitney relative balls in `Ω_A`, the
  fivefold covering of `Ω_A` and the proximity to `G_A`;
* (ii.b) gives the exact Borel allocation `E_i ⊆ 5B_i` of `Ω_A` and the piece bounds;
* (iii), with the domination supplied by `GoodDominationStatement`, gives `ν_A ≤ C₁ A σ` and
  `ν_A(Γ) = ν(Γ)`.
The conclusions are collected in `b3_IsReplacementData`, which is definitionally the body of
`ReplacementStatement`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Characterization.ReplacementTree

open ParabolicRectifiability.Foundations
open ParabolicRectifiability.Characterization.SourceTransferTree

/-- Replacement of the bad region, assembled from the component estimates
`b3_rp_goodSet`, `b3_rp_whitneySelection`, `b3_rp_allocation` and `b3_rp_assembly`. The type is exactly `ReplacementStatement`. -/
theorem bad_region_replacement_of_leaves : ReplacementStatement := by
  intro k c C
  refine ⟨max (C * 5 ^ k) 1, max ((5 ^ k + 205 ^ k) / c) 1,
    lt_max_of_lt_right one_pos, lt_max_of_lt_right one_pos, ?_⟩
  intro n hn Γ σ hΓ ν hν hνΓ A hA
  have := hν
  obtain ⟨hGc, hGne, hbad⟩ :=
    b3_rp_goodSet b3_rp_input_fivefold n hn k c C Γ σ hΓ ν hν hνΓ A hA
  have hGsub : adrGoodSet Γ ν k A ⊆ Γ := fun x hx => hx.1
  have hfin : σ (Γ \ adrGoodSet Γ ν k A) < ⊤ :=
    hbad.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν Γ))
  obtain ⟨I, z, r, hzr, hdisjB, hBsub, hcover, hnear⟩ :=
    b3_rp_whitneySelection b3_rp_input_fivefold n k c C Γ σ hΓ (adrGoodSet Γ ν k A) hGc hGne
      hGsub hfin
  obtain ⟨E, hEm, hEsub, hEdisj, hEunion, hpiece⟩ :=
    b3_rp_allocation n k Γ ν A hΓ.isClosed.measurableSet hGc.measurableSet I z r
      (fun i => (hzr i).2) hcover hnear
  obtain ⟨hdom, hmass⟩ :=
    b3_rp_assembly n k c C Γ σ hΓ ν hν hνΓ A hA hGc.measurableSet
      (b3_rp_input_goodDomination n hn k c C Γ σ hΓ ν hν hνΓ A hA)
      I z r E hzr hdisjB hEm hEdisj hEunion hpiece
  have hdata : b3_IsReplacementData k (max (C * 5 ^ k) 1) (max ((5 ^ k + 205 ^ k) / c) 1)
      Γ σ ν A I z r E :=
    ⟨hzr, hdisjB, hBsub, hEm, hEsub, hEdisj, hEunion, hbad, hpiece, hdom, hmass⟩
  exact ⟨I, z, r, E, hdata⟩

end ParabolicRectifiability.Characterization.ReplacementTree
