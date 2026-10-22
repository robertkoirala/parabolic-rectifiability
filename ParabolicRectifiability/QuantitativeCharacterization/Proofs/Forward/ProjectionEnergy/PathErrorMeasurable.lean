import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.ProjectionEnergy

/-! # Borel measurability of the path errors `d_j`

Proof of `d1e2_PathErrorMeasurableStatement`.

Proof sketch: the path point `p ↦ (F_j(p.1, p.2.val), p.2.val)` is continuous (`contDiff_stage`), hence
measurable. The local comparison coefficient `CoherentChart.localError F j` is Borel: each
`⨆ a ∈ F.index j, …` runs over a `Finset` (finite induction; the index type need not be
countable, so `Measurable.iSup` is not used), each inner `⨆ (_ : dist … ≤ …), c` is a
measurable `if` on a closed set, and the outer `⨆ (_ : ∃ a ∈ F.index j, dist q (z a) < 3 r_j), …`
is a measurable `if` on an open set. Finally `ENNReal.measurable_toReal`.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

/-- A supremum over a measurable condition is a measurable `if`. -/
theorem d1e2pmeas_measurable_iSup_prop {X : Type*} [MeasurableSpace X] {p : X → Prop}
    {f : X → ℝ≥0∞} (hp : MeasurableSet {x | p x}) (hf : Measurable f) :
    Measurable fun x => ⨆ (_ : p x), f x := by
  classical
  have h : (fun x => ⨆ (_ : p x), f x) = fun x => if p x then f x else 0 := by
    funext x
    by_cases hx : p x
    · rw [iSup_pos hx]
      simp [hx]
    · rw [iSup_neg hx]
      simp [hx]
  rw [h]
  exact Measurable.ite hp hf measurable_const

/-- A supremum over a `Finset` of measurable functions is measurable (no countability of the
index type is needed). -/
theorem d1e2pmeas_measurable_biSup {X ι : Type*} [MeasurableSpace X] (s : Finset ι)
    {g : ι → X → ℝ≥0∞} (hg : ∀ a ∈ s, Measurable (g a)) :
    Measurable fun x => ⨆ a ∈ s, g a x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h : (fun x => ⨆ a ∈ (∅ : Finset ι), g a x) = fun _ => 0 := by
      funext x
      simp only [Finset.notMem_empty, iSup_false, iSup_bot]
      exact ENNReal.bot_eq_zero
    rw [h]
    exact measurable_const
  | insert a s ha ih =>
    have h : (fun x => ⨆ b ∈ insert a s, g b x) = fun x => max (g a x) (⨆ b ∈ s, g b x) := by
      funext x
      rw [Finset.iSup_insert]
    rw [h]
    exact (hg a (Finset.mem_insert_self a s)).max
      (ih fun b hb => hg b (Finset.mem_insert_of_mem hb))

/-- The set of points within distance `< r` of some center of a finite family is open. -/
theorem d1e2pmeas_isOpen_exists {X ι : Type*} [PseudoMetricSpace X] (s : Finset ι)
    (c : ι → X) (r : ℝ) : IsOpen {q : X | ∃ a ∈ s, dist q (c a) < r} := by
  have h : {q : X | ∃ a ∈ s, dist q (c a) < r} = ⋃ a, ⋃ (_ : a ∈ s), Metric.ball (c a) r := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Metric.mem_ball, exists_prop]
  rw [h]
  exact isOpen_iUnion fun a => isOpen_iUnion fun _ => Metric.isOpen_ball

/-- The local comparison coefficient `e_j` of the coherent chart is Borel measurable. -/
theorem d1e2pmeas_measurable_localError {n m : ℕ} {ι : Type*} (F : CoherentFamily n m ι)
    (j : ℕ) : Measurable (CoherentChart.localError F j) := by
  have hcl : ∀ (c : Space n) (r : ℝ), MeasurableSet {q : Space n | dist c q ≤ r} :=
    fun c r => (isClosed_le (continuous_const.dist continuous_id) continuous_const).measurableSet
  cases j with
  | zero =>
    show Measurable fun q => CoherentChart.localError F 0 q
    simp only [CoherentChart.localError]
    refine d1e2pmeas_measurable_iSup_prop (d1e2pmeas_isOpen_exists _ _ _).measurableSet ?_
    refine d1e2pmeas_measurable_biSup _ fun a _ => ?_
    exact d1e2pmeas_measurable_iSup_prop (hcl _ _) measurable_const
  | succ j =>
    show Measurable fun q => CoherentChart.localError F (j + 1) q
    simp only [CoherentChart.localError]
    refine d1e2pmeas_measurable_iSup_prop (d1e2pmeas_isOpen_exists _ _ _).measurableSet ?_
    refine Measurable.max ?_ ?_
    · refine d1e2pmeas_measurable_biSup _ fun a _ => d1e2pmeas_measurable_biSup _ fun b _ => ?_
      exact d1e2pmeas_measurable_iSup_prop ((hcl _ _).inter (hcl _ _)) measurable_const
    · refine d1e2pmeas_measurable_biSup _ fun a _ => d1e2pmeas_measurable_biSup _ fun b _ => ?_
      exact d1e2pmeas_measurable_iSup_prop ((hcl _ _).inter (hcl _ _)) measurable_const

/-- The path point `p ↦ q_j(p) = (F_j(p.1, p.2.val), p.2.val)` is continuous on `Space m`. -/
theorem d1e2pmeas_continuous_pathPoint {n m : ℕ} {ι : Type*} (F : CoherentFamily n m ι)
    (P : CoherentChart.InitialChart F) (j : ℕ) :
    Continuous fun p : Space m => CoherentChart.pathPoint F P j p.1 p.2.val := by
  have hv : Continuous fun p : Space m => p.2.val :=
    Metric.Snowflaking.continuous_ofSnowflaking.comp continuous_snd
  have hs : Continuous fun p : Space m => CoherentChart.stage F P j p.1 p.2.val :=
    (CoherentChart.contDiff_stage F P j).continuous.comp (continuous_fst.prodMk hv)
  unfold CoherentChart.pathPoint point
  exact hs.prodMk (Metric.Snowflaking.continuous_toSnowflaking.comp hv)

/-- **Measurability of the path errors**: every path error `d_j` is Borel measurable. -/
theorem d1e2_pathError_measurable_proof : d1e2_PathErrorMeasurableStatement := by
  intro n m ι F P j
  unfold d1e_pathError
  exact ENNReal.measurable_toReal.comp
    ((d1e2pmeas_measurable_localError F j).comp (d1e2pmeas_continuous_pathPoint F P j).measurable)

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
