import ParabolicRectifiability.Characterization.Statements.SourceTransfer

/-! # Continuous approximation for a Radon source

Proves `RadonApproximationStatement` with Mathlib only.

Route: the isometry `e : Y → Space n` with
closed range is a closed embedding, hence a measurable embedding, and preimages of compact sets
are compact. So the push-forward `ρ.map e` is finite on compact sets of the proper space
`Space n`, hence locally finite and (Mathlib) regular. The integrable `f` extends by zero off the
range to an integrable `F` on `Space n` with `F ∘ e = f`, and Mathlib's compact-support density
in `L¹` (`Integrable.exists_hasCompactSupport_lintegral_sub_le`) gives a continuous compactly
supported `g` with `∫⁻ ‖F - g‖ₑ d(ρ.map e)` small. Pulling back along the measurable embedding
gives the bound on `Y`. The Borel restriction `ρ.restrict B` is again finite on compact sets,
so the same argument applies; inner regularity of `ρ` is not needed on this route.
-/

noncomputable section

open MeasureTheory Set Function Topology
open scoped ENNReal

namespace ParabolicRectifiability.Characterization

/-- The common core: a measure on `Y` that is finite on compact sets, pushed forward along a
closed isometric embedding into `Space n`, admits `L¹` approximation of every integrable
function by restrictions of continuous compactly supported ambient functions. -/
theorem bp2_radonApproximation_core {n : ℕ} {Y : Type} [MetricSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] {e : Y → Space n} (he : Isometry e) (hcl : IsClosed (Set.range e))
    (ρ : Measure Y) (hρ : ∀ K : Set Y, IsCompact K → ρ K < ⊤)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : Y → E) (hf : Integrable f ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : Space n → E, Continuous g ∧ HasCompactSupport g ∧
      ∫⁻ y, ‖f y - g (e y)‖ₑ ∂ρ < ENNReal.ofReal ε := by
  have hce : IsClosedEmbedding e := ⟨he.isEmbedding, hcl⟩
  have hme : MeasurableEmbedding e := hce.measurableEmbedding
  have : IsFiniteMeasureOnCompacts (ρ.map e) := ⟨fun K hK => by
    rw [hme.map_apply]
    exact hρ _ (hce.isCompact_preimage hK)⟩
  have hFe : Function.extend e f 0 ∘ e = f :=
    funext fun y => he.injective.extend_apply f 0 y
  have hF : Integrable (Function.extend e f 0) (ρ.map e) := by
    rw [hme.integrable_map_iff, hFe]
    exact hf
  have hε2 : ENNReal.ofReal (ε / 2) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (half_pos hε)).ne'
  obtain ⟨g, hgs, hgl, hgc, -⟩ := hF.exists_hasCompactSupport_lintegral_sub_le hε2
  refine ⟨g, hgc, hgs, ?_⟩
  have hpull : ∫⁻ x, ‖Function.extend e f 0 x - g x‖ₑ ∂(ρ.map e) =
      ∫⁻ y, ‖f y - g (e y)‖ₑ ∂ρ := by
    rw [hme.lintegral_map]
    refine lintegral_congr fun y => ?_
    rw [he.injective.extend_apply f 0 y]
  rw [← hpull]
  exact lt_of_le_of_lt hgl ((ENNReal.ofReal_lt_ofReal_iff hε).2 (half_lt_self hε))

/-- `RadonApproximationStatement`, for the source itself and for its Borel restrictions. -/
theorem bp2_radonApproximation_proof : RadonApproximationStatement := by
  intro n _ Y _ _ _ e he hcl ρ hρc _ E _ _ _
  have := hρc
  refine ⟨fun f hf ε hε =>
    bp2_radonApproximation_core he hcl ρ (fun K hK => hK.measure_lt_top) f hf ε hε, ?_⟩
  intro B _ f hf ε hε
  exact bp2_radonApproximation_core he hcl (ρ.restrict B)
    (fun K hK => lt_of_le_of_lt (Measure.restrict_apply_le B K) hK.measure_lt_top) f hf ε hε

end ParabolicRectifiability.Characterization
