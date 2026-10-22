import ParabolicRectifiability.Characterization.Proofs.FiniteHausdorff.Components
import ParabolicRectifiability.Characterization.Statements.Branches
import ParabolicRectifiability.Characterization.Assembly.CoveringLemmas

/-! # The finite-Hausdorff criterion: assembly

Main theorem: `b4_finite_hausdorff_criterion : FiniteHausdorffCriterionStatement`
(the statement used as `finite_hausdorff_criterion`): a Borel set of finite `H_P^k` measure
whose square energy is finite almost everywhere at some scale is regularly rectifiable of the
given type.

The non-ambient branch applies the scaled rectifiable Reifenberg core property
(`ScaledRectifiableReifenbergCoreStatement`) to the full source `ν = H_P^k⌊F` on the balls
`P(z_j, 5 r_j)` with endpoint `10 r_j < s`, threshold `e` and allowance `0`; the ambient branch
uses `AmbientZeroGraphCoverStatement`. Besides the intermediate statements of the companion
file (`b4_tail_truncation`, …), the proof uses `squareEnergy_mono_measure`,
`hausdorffP_restrict_isFinite`, `exists_natSubset_reindex`, `iUnion_eq_of_range_eq` and
`squareEnergy_mono_endpoint`. No packing, content or graphicality is assumed: graphs enter only
through the decomposition supplied by the core property.

Proved here: countable unions of typed graph covers modulo `H_P^k`
(`b4_hasTypedGraphCover_of_iUnion`), the zero exceptional mass by source domination
(`b4_threshold_null`), one error level (`b4_cover_at_error`), vanishing errors
(`b4_nonambient_branch`) and the ambient case (`b4_ambient_branch`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

/-! ## Countable unions of typed graph covers -/

/-- Countably many countable families, each indexed by a subset of `ℕ`, over a countable index
type, merge into one family indexed by a subset of `ℕ` with the same union of images. -/
theorem b4_exists_merge {ι α X : Type*} [Countable ι] (img : α → Set X) (I : ι → Set ℕ)
    (G : ∀ i, I i → α) :
    ∃ (J : Set ℕ) (g : J → α), (⋃ j, img (g j)) = ⋃ i, ⋃ x, img (G i x) := by
  obtain ⟨J, g, hg⟩ := exists_natSubset_reindex (fun s : Σ i, I i => G s.1 s.2)
  exact ⟨J, g, (iUnion_eq_of_range_eq hg img).trans
    (iUnion_sigma (fun s : Σ i, I i => img (G s.1 s.2)))⟩

/-- If the pieces `K' i` cover `K` modulo `H_P^k` and each `V i` covers `K' i` modulo `H_P^k`,
the `V i` cover `K` modulo `H_P^k`. -/
theorem b4_null_of_pieces {n k : ℕ} {ι : Type*} [Countable ι] (K : Set (Space n))
    (K' V : ι → Set (Space n)) (hnull : hausdorffP n k (K \ ⋃ i, K' i) = 0)
    (hV : ∀ i, hausdorffP n k (K' i \ V i) = 0) :
    hausdorffP n k (K \ ⋃ i, V i) = 0 := by
  refine measure_mono_null ?_ (measure_union_null hnull (measure_iUnion_null hV))
  intro z hz
  by_cases h : z ∈ ⋃ i, K' i
  · obtain ⟨i, hi⟩ := mem_iUnion.1 h
    exact Or.inr (mem_iUnion.2 ⟨i, hi, fun hzV => hz.2 (mem_iUnion.2 ⟨i, hzV⟩)⟩)
  · exact Or.inl ⟨hz.1, h⟩

/-- Typed graph covers (modulo `H_P^k`, tolerance `ε`) of countably many pieces covering `K`
modulo `H_P^k` give a typed graph cover of `K` at the same tolerance. -/
theorem b4_hasTypedGraphCover_of_iUnion {n k : ℕ} (T : FamilyKind) (ε : ℝ) {ι : Type*}
    [Countable ι] (K : Set (Space n)) (K' : ι → Set (Space n))
    (hcov : ∀ i, HasTypedGraphCover T k (K' i) ε)
    (hnull : hausdorffP n k (K \ ⋃ i, K' i) = 0) : HasTypedGraphCover T k K ε := by
  cases T with
  | horizontal =>
    have hcov' : ∀ i, ∃ (I : Set ℕ) (G : I → HorizontalGraph n k ε),
        hausdorffP n k (K' i \ ⋃ x, (G x).image) = 0 := hcov
    choose I G hG using hcov'
    obtain ⟨J, g, hg⟩ := b4_exists_merge (fun H : HorizontalGraph n k ε => H.image) I G
    exact ⟨J, g, (congrArg (fun S : Set (Space n) => hausdorffP n k (K \ S)) hg).trans
      (b4_null_of_pieces K K' (fun i => ⋃ x, (G i x).image) hnull hG)⟩
  | vertical =>
    have hcov' : ∀ i, ∃ (I : Set ℕ) (G : I → GeneralRegularVerticalGraph n k ε),
        hausdorffP n k (K' i \ ⋃ x, (G x).image) = 0 := hcov
    choose I G hG using hcov'
    obtain ⟨J, g, hg⟩ :=
      b4_exists_merge (fun V : GeneralRegularVerticalGraph n k ε => V.image) I G
    exact ⟨J, g, (congrArg (fun S : Set (Space n) => hausdorffP n k (K \ S)) hg).trans
      (b4_null_of_pieces K K' (fun i => ⋃ x, (G i x).image) hnull hG)⟩
  | mixed =>
    have hcov' : ∀ i, ∃ (I I' : Set ℕ) (H : I → HorizontalGraph n k ε)
        (V : I' → GeneralRegularVerticalGraph n k ε),
        hausdorffP n k (K' i \ ((⋃ x, (H x).image) ∪ ⋃ y, (V y).image)) = 0 := hcov
    choose I I' H V hHV using hcov'
    obtain ⟨J, g, hg⟩ := b4_exists_merge (fun G : HorizontalGraph n k ε => G.image) I H
    obtain ⟨J', g', hg'⟩ :=
      b4_exists_merge (fun G : GeneralRegularVerticalGraph n k ε => G.image) I' V
    have hU : ((⋃ j, (g j).image) ∪ ⋃ j, (g' j).image) =
        ⋃ i, ((⋃ x, (H i x).image) ∪ ⋃ y, (V i y).image) := by
      rw [iUnion_union_distrib]
      exact congrArg₂ (· ∪ ·) hg hg'
    exact ⟨J, J', g, g', (congrArg (fun S : Set (Space n) => hausdorffP n k (K \ S)) hU).trans
      (b4_null_of_pieces K K' (fun i => (⋃ x, (H i x).image) ∪ ⋃ y, (V i y).image) hnull hHV)⟩

/-! ## Zero exceptional mass by source domination -/

/-- Source domination and the endpoint: if `F ⊆ E` is
Borel and `S^s_{η,T} ≤ e` on `F` for `η = H_P^k⌊E`, then for `ν = H_P^k⌊F` and every endpoint
`t ≤ s` the set `{S^t_{ν,T} > e}` is `ν`-null, since `S^t_ν ≤ S^s_ν ≤ S^s_η` (endpoint
monotonicity and `squareEnergy_mono_measure` with `ν ≤ η`) and `ν` lives on `F`. -/
theorem b4_threshold_null {n k : ℕ} (T : FamilyKind) {E F : Set (Space n)}
    (hF : MeasurableSet F) (hFE : F ⊆ E) {s e : ℝ}
    (hFs : ∀ z ∈ F, squareEnergy ((hausdorffP n k).restrict E) k T s z ≤ ENNReal.ofReal e)
    {t : ℝ} (hts : t ≤ s) :
    (hausdorffP n k).restrict F
      {w | ENNReal.ofReal e < squareEnergy ((hausdorffP n k).restrict F) k T t w} = 0 := by
  refine measure_mono_null ?_ (ae_iff.1 (ae_restrict_mem hF))
  intro w hw
  simp only [mem_ofPred_eq] at hw ⊢
  intro hwF
  have hle : squareEnergy ((hausdorffP n k).restrict F) k T t w ≤ ENNReal.ofReal e :=
    ((squareEnergy_mono_endpoint ((hausdorffP n k).restrict F) k T hts w).trans
      (squareEnergy_mono_measure (Measure.restrict_mono hFE (le_refl (hausdorffP n k)))
        k T s w)).trans (hFs w hwF)
  exact (not_lt.2 hle) hw

/-! ## One error level -/

/-- **One error level.** For the given tolerance `ε > 0` and error
`e > 0` there is a set `K` with a typed graph cover of type `T` at tolerance `ε` and
`H_P^k(E \ K) ≤ e (1 + (C 5^k / c) H_P^k(E))`, where `C` is the core constant and `c` the density
constant.

Steps: tail truncation (`b4_tail_truncation`) gives `s` and `F`; `ν = H_P^k⌊F` is finite,
hence locally Radon (Mathlib instances), and `ν ≪ H_P^k`; the density bound and the fivefold
selection give the balls `P(z_j, r_j)`, `10 r_j < s`; for each `j`, the core property
(`b4_input_scaledRectifiableReifenbergCore`, second conjunct) is applied to the full source `ν` at
`a = z_j`, `R = 5 r_j`, `M = e`, `Γ = 0`, whose exceptional mass vanishes by
`b4_threshold_null` at the endpoint `2 · 5 r_j ≤ s`; each decomposition yields a covered set
`U_j` missing at most the remainder mass `≤ C e (5 r_j)^k`
(`b4_cover_of_localCoreDecomposition`); `K = ⋃_j U_j` is covered by
`b4_hasTypedGraphCover_of_iUnion`, and `b4_missed_mass_bound` gives the bound. -/
theorem b4_cover_at_error {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 2) (T : FamilyKind)
    (hT : Nonempty (Models n k T)) {E : Set (Space n)} (hE : MeasurableSet E)
    (hEfin : hausdorffP n k E < ⊤) {R : ℝ} (hR : 0 < R)
    (hae : ∀ᵐ z ∂(hausdorffP n k).restrict E,
      squareEnergy ((hausdorffP n k).restrict E) k T R z < ⊤)
    {C : ℝ} (hCpos : 0 < C) (hC : Enhancements.ScaledThresholdCoreProperty n C)
    {c : ℝ} (hcpos : 0 < c)
    (hdens : ∀ F : Set (Space n), MeasurableSet F → hausdorffP n k F < ⊤ →
      ∀ᵐ z ∂(hausdorffP n k).restrict F, ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ r < δ ∧
        ENNReal.ofReal (c * r ^ k) ≤ (hausdorffP n k).restrict F (Metric.ball z r))
    {ε : ℝ} (hε : 0 < ε) {e : ℝ} (he : 0 < e) :
    ∃ K : Set (Space n), HasTypedGraphCover T k K ε ∧
      hausdorffP n k (E \ K) ≤
        ENNReal.ofReal e * (1 + ENNReal.ofReal (C * 5 ^ k / c) * hausdorffP n k E) := by
  obtain ⟨s, hs, F, hFm, hFE, hFs, hEF⟩ := b4_tail_truncation n k T E hE hEfin R hR hae e he
  have hFfin : hausdorffP n k F < ⊤ := (measure_mono hFE).trans_lt hEfin
  have hνfin : IsFiniteMeasure ((hausdorffP n k).restrict F) := hausdorffP_restrict_isFinite hFfin
  have hνc : IsFiniteMeasureOnCompacts ((hausdorffP n k).restrict F) := inferInstance
  have hνr : ((hausdorffP n k).restrict F).InnerRegular := inferInstance
  have hνac : (hausdorffP n k).restrict F ≪ hausdorffP n k :=
    Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  obtain ⟨J, z, r, hr, hrs, hdisj, hlow, hcov⟩ :=
    b4_fivefold_density_selection b4_input_fivefoldSelection n k ((hausdorffP n k).restrict F) c
      s hs (hdens F hFm hFfin)
  have hthr : ∀ j : J, (hausdorffP n k).restrict F (Metric.ball (z j) (5 * r j) ∩
      {w | ENNReal.ofReal e <
        squareEnergy ((hausdorffP n k).restrict F) k T (2 * (5 * r j)) w}) ≤
        ENNReal.ofReal 0 := by
    intro j
    rw [ENNReal.ofReal_zero, nonpos_iff_eq_zero]
    exact measure_mono_null inter_subset_right
      (b4_threshold_null T hFm hFE hFs (by linarith [hrs j]))
  choose EH EV hdec hloss using fun j : J =>
    hC k hk hkn ((hausdorffP n k).restrict F) hνc hνr (z j) (5 * r j) (by linarith [hr j]) T hT
      e 0 he.le le_rfl (hthr j)
  choose U hU hUmiss using fun j : J =>
    b4_cover_of_localCoreDecomposition n k T C (z j) (5 * r j) ((hausdorffP n k).restrict F)
      (EH j) (EV j) hνac (hdec j) ε hε
  refine ⟨⋃ j, U j, b4_hasTypedGraphCover_of_iUnion T ε (⋃ j, U j) U hU (by simp), ?_⟩
  exact b4_missed_mass_bound n k E F hFm hFE C c e hCpos.le hcpos he.le hEF.le J z r hr hdisj
    hlow hcov U fun j => (hUmiss j).trans ((hloss j).trans_eq (by rw [add_zero]))

/-! ## The two branches -/

/-- **Non-ambient branch, vanishing errors.** The core constant `C`
(second conjunct of `b4_input_scaledRectifiableReifenbergCore` at `n`) and the density constant `c`
(`b4_hausdorff_restrict_ball_lower_bound` at `n`, `k`) are fixed first; for each tolerance
`ε > 0` the error levels `e_j = 1/(j+1)` give sets `K_j` (`b4_cover_at_error`) with
`H_P^k(E \ ⋃_j K_j) ≤ e_j (1 + (C 5^k/c) H_P^k(E)) → 0`, so the countable union of their
covers is a typed cover of `E` modulo `H_P^k`. The argument is valid for every `k` in the
range; it is used for `k ≠ n + 2`. -/
theorem b4_nonambient_branch {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n + 2)
    (T : FamilyKind) (hT : Nonempty (Models n k T)) {E : Set (Space n)}
    (hE : MeasurableSet E) (hEfin : hausdorffP n k E < ⊤) {R : ℝ} (hR : 0 < R)
    (hae : ∀ᵐ z ∂(hausdorffP n k).restrict E,
      squareEnergy ((hausdorffP n k).restrict E) k T R z < ⊤) :
    IsRegularlyRectifiableSet T k E := by
  obtain ⟨C, hCpos, hC⟩ := And.right b4_input_scaledRectifiableReifenbergCore n hn
  obtain ⟨c, hcpos, hdens⟩ := b4_hausdorff_restrict_ball_lower_bound n hn k hk hkn
  intro ε hε
  have hA : (1 + ENNReal.ofReal (C * 5 ^ k / c) * hausdorffP n k E) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEfin.ne⟩
  choose K hK hKerr using fun j : ℕ =>
    b4_cover_at_error hk hkn T hT hE hEfin hR hae hCpos hC hcpos hdens hε
      (e := 1 / ((j : ℝ) + 1)) (by positivity)
  refine b4_hasTypedGraphCover_of_iUnion T ε E K hK ?_
  have h1 : Tendsto (fun j : ℕ => ENNReal.ofReal (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim := ENNReal.Tendsto.mul_const h1 (Or.inr hA)
  rw [zero_mul] at hlim
  exact nonpos_iff_eq_zero.1 (ge_of_tendsto' hlim fun j =>
    (measure_mono (Set.sdiff_subset_sdiff_right (subset_iUnion K j))).trans (hKerr j))

/-- **Ambient branch**: at `k = n + 2` the available families
are `.vertical` and `.mixed` (no horizontal model, `HorizontalModel.nonempty_iff`), and every
set is regularly rectifiable of both types by the second conjunct of
`b4_input_ambientZeroGraphCover`, independently of energy. -/
theorem b4_ambient_branch (n : ℕ) (hn : 1 ≤ n) (T : FamilyKind)
    (hT : Nonempty (Models n (n + 2) T)) (E : Set (Space n)) :
    IsRegularlyRectifiableSet T (n + 2) E := by
  obtain ⟨-, hall⟩ := b4_input_ambientZeroGraphCover n hn
  cases T with
  | horizontal =>
    have h : 1 ≤ n + 2 ∧ n + 2 ≤ n := HorizontalModel.nonempty_iff.mp hT
    exact absurd h.2 (by omega)
  | vertical => exact (hall E).1
  | mixed => exact (hall E).2

/-! ## The finite-Hausdorff criterion -/

/-- **Finite-Hausdorff criterion.** First conjunct: a Borel set of finite `H_P^k` measure with
a.e. finite square energy at some scale is regularly rectifiable of type `T`; for
`k = n + 2` by `b4_ambient_branch`, otherwise by `b4_nonambient_branch`. Second conjunct: the
ambient zero-norm vertical graph `b4_ambient_zero_norm_graph`. -/
theorem b4_finite_hausdorff_criterion : FiniteHausdorffCriterionStatement := by
  refine ⟨?_, b4_ambient_zero_norm_graph⟩
  intro n hn k hk hkn T hT E hE hEfin hR
  obtain ⟨R, hRpos, hae⟩ := hR
  by_cases hk2 : k = n + 2
  · subst hk2
    exact b4_ambient_branch n hn T hT E
  · exact b4_nonambient_branch hn hk hkn T hT hE hEfin hRpos hae

end ParabolicRectifiability.Characterization
