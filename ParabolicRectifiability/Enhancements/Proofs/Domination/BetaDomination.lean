import ParabolicRectifiability.Foundations.Statements.Measurability
import ParabolicRectifiability.Foundations.Proofs.BetaEnergyDomination

/-! # Beta domination under measure domination

`fmeas3_betaSq_le_of_le_ofReal_smul`: if `ν ≤ c μ` with `c > 0`, then
`b_ν(z,r) ≤ c b_μ(z,r)` at every centre and radius. This is the beta clause of
`BetaEnergyDominationStatement`; the energy clause is derived from it by integrating against
`dr/r` in `fmeas3_betaSq_squareEnergy_le_of_le_ofReal_smul`, which is used by the density
corollaries.

The declarations live in the namespace `ParabolicRectifiability.Foundations`, next to the
statement.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- **Beta domination under measure domination.**

For every `n`, `k`, family `T`, measures `μ, ν` and real `c > 0` with
`ν ≤ c μ`, and every centre `z` and real radius `r`, `b_ν(z,r) ≤ c b_μ(z,r)`. No dimension
guard and no regularity of `μ` or `ν` is needed: for `r ≤ 0` both sides vanish, and an
unavailable family has `b = ⊤` on both sides at `r > 0`.

Proof: if `r ≤ 0`,
`betaSq_of_nonpos` on both sides. If `r > 0`, split on `isEmpty_or_nonempty (Models n k T)`:
available family: `betaSq_mono_measure h` gives `b_ν ≤ b_{c•μ}` and `betaSq_smul μ (ofReal c)
ofReal_ne_top` gives `b_{c•μ} = c b_μ`; unavailable family: `betaSq_of_isEmpty` makes
`b_μ = ⊤`, so the right side is `ofReal c * ⊤ = ⊤` (`ENNReal.mul_top`, `ofReal c ≠ 0` from
`c > 0`), and `le_top` closes it. The proof is
`fmeas3_betaSq_le_of_le_ofReal_smul_proof`. -/
theorem fmeas3_betaSq_le_of_le_ofReal_smul {n : ℕ} (k : ℕ) (T : FamilyKind)
    {μ ν : Measure (Space n)} {c : ℝ} (hc : 0 < c) (h : ν ≤ ENNReal.ofReal c • μ)
    (z : Space n) (r : ℝ) :
    betaSq ν k T z r ≤ ENNReal.ofReal c * betaSq μ k T z r := by
  exact fmeas3_betaSq_le_of_le_ofReal_smul_proof k T hc h z r

end ParabolicRectifiability.Foundations
