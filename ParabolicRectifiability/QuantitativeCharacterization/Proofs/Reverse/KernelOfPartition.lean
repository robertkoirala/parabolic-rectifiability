import ParabolicRectifiability.QuantitativeCharacterization.Statements.ReverseBound

/-! # A Markov kernel on a countable Borel partition

Proof of `d2_kernel_of_partition` (`KernelOfPartitionStatement`).

Construction: `κ = piecewise (⋃ P) (Σ_j piecewise (P j) (const (τ j)) 0) (deterministic id)`.
On `P j` disjointness kills every summand but the `j`-th, so `κ y = τ j`; off `⋃ P` the kernel
is `δ_y`. Both values are probability measures, hence `κ` is Markov. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ProbabilityTheory

namespace ParabolicRectifiability.QuantitativeCharacterization.ReverseTree

/-- Countable measurable pasting of constant probability measures on disjoint measurable cells
and the identity kernel off their union, on an arbitrary measurable space. -/
theorem d2ker_exists_kernel {X : Type*} [MeasurableSpace X] {ι : Type} [Countable ι]
    (P : ι → Set X) (τ : ι → Measure X) (hP : ∀ j, MeasurableSet (P j))
    (hdisj : Pairwise fun i j => Disjoint (P i) (P j))
    (hτ : ∀ j, IsProbabilityMeasure (τ j)) :
    ∃ κ : Kernel X X, IsMarkovKernel κ ∧
      (∀ j, ∀ y ∈ P j, κ y = τ j) ∧ (∀ y, (∀ j, y ∉ P j) → κ y = Measure.dirac y) := by
  classical
  have hU : MeasurableSet (⋃ j, P j) := MeasurableSet.iUnion hP
  let κ₁ : Kernel X X :=
    Kernel.sum fun j => Kernel.piecewise (hP j) (Kernel.const X (τ j)) 0
  let κ : Kernel X X := Kernel.piecewise hU κ₁ (Kernel.deterministic id measurable_id)
  have hon : ∀ j, ∀ y ∈ P j, κ y = τ j := by
    intro j y hy
    have hyU : y ∈ ⋃ j, P j := mem_iUnion.2 ⟨j, hy⟩
    ext s hs
    simp only [κ, κ₁, Kernel.piecewise_apply, hyU, ↓reduceIte]
    rw [Kernel.sum_apply' _ _ hs, tsum_eq_single j]
    · simp [Kernel.piecewise_apply, hy, Kernel.const_apply]
    · intro i hij
      have hyi : y ∉ P i := fun hi => (hdisj hij).ne_of_mem hi hy rfl
      simp [Kernel.piecewise_apply, hyi]
  have hoff : ∀ y, (∀ j, y ∉ P j) → κ y = Measure.dirac y := by
    intro y hy
    have hyU : y ∉ ⋃ j, P j := by
      simp only [mem_iUnion, not_exists]
      exact hy
    simp only [κ, Kernel.piecewise_apply, hyU, ↓reduceIte, Kernel.deterministic_apply, id_eq]
  refine ⟨κ, ⟨fun y => ?_⟩, hon, hoff⟩
  by_cases hy : ∃ j, y ∈ P j
  · obtain ⟨j, hj⟩ := hy
    rw [hon j y hj]
    exact hτ j
  · have hy' : ∀ j, y ∉ P j := fun j hj => hy ⟨j, hj⟩
    rw [hoff y hy']
    infer_instance

/-- **Proof of the statement `d2_kernel_of_partition`** (`KernelOfPartitionStatement`). -/
theorem d2_kernel_of_partition_proof : KernelOfPartitionStatement := by
  intro n ι _ P τ hP hdisj hτ
  exact d2ker_exists_kernel P τ hP hdisj hτ

end ParabolicRectifiability.QuantitativeCharacterization.ReverseTree
