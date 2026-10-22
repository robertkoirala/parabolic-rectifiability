import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.TransferComponents
import ParabolicRectifiability.Measure.BetaLaws

/-! # Transfer of square finiteness from an ADR measure to a source

The main theorem `adr_source_transfer_of_leaves` has exactly the type
`SourceTransferStatement` (the statement of `adr_source_transfer`). It is assembled from the
component estimates `b3_couplingEnergy`, `b3_exceptionalMass`, ….

Structure (on-carrier displacement, off-carrier probability kernel, integrated
errors, exceptional-set removal):
* `b3_onCarrier`: for a finite source `ν` carried by `Γ` and each level `A > 0`,
  the replacement data give the on-carrier coupling, the fixed-plane energy
  inequality `S^{1/2}_ν ≤ 2·2^{k+2} S^1_{ν_A} + 2·err`, the domination `ν_A ≤ C₁ A σ`
  (`squareEnergy_mono_measure`, `squareEnergy_smul`), the integrated error, and the
  annulus fill to the endpoint `1`. Off the excluded centres `Ξ_A`, of mass at most
  `(C 20^k / c)(C₀ / A) ν(Γ)`, the square of `ν` is finite `σ`-a.e. The exceptional-set removal
  lets `A = j + 1 → ∞`; the exceptional sets need not be nested.
* `b3_offCarrier`: the kernel coupling moves `μ` to `ν = π.snd`, carried by `Γ`;
  the fixed-plane energy inequality `S^{1/4}_μ ≤ 2·4^{k+2} S^1_ν + 2·err`, the integrated
  error and the annulus fill give `S^1_μ < ∞` wherever `S^1_ν < ∞`, `σ`-a.e. on `Γ`.
* `adr_source_transfer_of_leaves`: combine the two.

The named statements `OnCarrierErrorStatement`, `OffCarrierErrorStatement` and
`OffCarrierCouplingStatement` are proved here:
* `b3_onCarrierError_of_parts`, `b3_offCarrierError_of_parts`: the Tonelli bridge
  `b3_couplingErrorTonelli` (measurability and the integral identity, with `D = Γ \ Ξ_A`,
  resp. `D = Γ`, Borel because `Γ` is closed) followed by the geometric estimate;
* `b3_offCarrierCoupling_of_parts`: the kernel `b3_offCarrierKernel`, its coupling
  `b3_kernelCoupling`, and the localization conjunct derived from the displacement
  (`b3_mem_ball_of_displacement`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Characterization.SourceTransferTree

open ParabolicRectifiability.Foundations

/-- Availability of a model family bounds the dimension by the ambient endpoint. -/
theorem b3_le_of_nonempty_models {n k : ℕ} {T : FamilyKind} (h : Nonempty (Models n k T)) :
    k ≤ n + 2 := by
  cases T with
  | horizontal => exact (HorizontalModel.nonempty_iff.mp h).2.trans (by omega)
  | vertical => exact (VerticalModel.nonempty_iff.mp h).2
  | mixed => rcases AdmissibleModel.nonempty_iff.mp h with h | h <;> omega

/-- Annulus fill for a finite source: a finite square up to any
positive endpoint gives a finite square up to `1`. -/
theorem b3_squareEnergy_one_lt_top {n k : ℕ} (hn : 1 ≤ n) (hk : 0 < k) {T : FamilyKind}
    (hT : Nonempty (Models n k T)) (μ : Measure (Space n)) [IsFiniteMeasure μ] (z : Space n)
    {R : ℝ} (hR : 0 < R) (h : squareEnergy μ k T R z < ⊤) : squareEnergy μ k T 1 z < ⊤ :=
  (b3_input_squareFinitenessEndpoint n hn k hk (b3_le_of_nonempty_models hT) T μ
    inferInstance inferInstance z R 1 hR one_pos).mp h

/-- Localization from displacement: for `x ∈ Γ`, a pair `(y,v)` with `y ∈ P(x,s)` and
`d(y,v) ≤ 3 dist(y,Γ)` has `v ∈ P(x,4s)` (since `dist(y,Γ) ≤ d(y,x)`). -/
theorem b3_mem_ball_of_displacement {n : ℕ} {Γ : Set (Space n)} {x y v : Space n} {s : ℝ}
    (hx : x ∈ Γ) (hy : y ∈ Metric.ball x s) (hd : edist y v ≤ 3 * Metric.infEDist y Γ) :
    v ∈ Metric.ball x (4 * s) := by
  have h1 : edist y v ≤ ENNReal.ofReal (3 * dist y x) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ← edist_dist, ENNReal.ofReal_ofNat]
    exact hd.trans (by gcongr; exact Metric.infEDist_le_edist_of_mem hx)
  have h2 : dist y v ≤ 3 * dist y x := (edist_le_ofReal (by positivity)).mp h1
  rw [Metric.mem_ball] at hy ⊢
  have h3 := dist_triangle v y x
  rw [dist_comm v y] at h3
  linarith

/-- `OnCarrierErrorStatement` from the Tonelli bridge and the on-carrier
estimate. -/
theorem b3_onCarrierError_of_parts : OnCarrierErrorStatement := by
  intro n k c C C₀ C₁ Γ σ hΓ ν hν hνΓ A hA I z r E hdata π hπ hfst hsupp R
  have hD : MeasurableSet (Γ \ ⋃ i, Metric.ball (z i) (20 * r i)) :=
    hΓ.isClosed.measurableSet.diff (MeasurableSet.iUnion fun i => measurableSet_ball)
  obtain ⟨hmeas, heq⟩ := b3_couplingErrorTonelli n k σ hΓ.finiteOnCompacts π hπ _ hD R
  exact ⟨hmeas, heq.trans_le (b3_onCarrierErrorEstimate n k c C C₀ C₁ Γ σ hΓ ν hν hνΓ A hA
    I z r E hdata π hπ hfst hsupp R)⟩

/-- `OffCarrierErrorStatement` from the Tonelli bridge and the off-carrier
estimate. -/
theorem b3_offCarrierError_of_parts : OffCarrierErrorStatement := by
  intro n k c C Γ σ hΓ π hπ hdisp R
  obtain ⟨hmeas, heq⟩ := b3_couplingErrorTonelli n k σ hΓ.finiteOnCompacts π hπ Γ
    hΓ.isClosed.measurableSet R
  exact ⟨hmeas, heq.trans_le (b3_offCarrierErrorEstimate n k c C Γ σ hΓ π hπ hdisp R)⟩

/-- `OffCarrierCouplingStatement` from the moving-ball kernel and its
coupling; the localization conjunct is derived from the displacement. -/
theorem b3_offCarrierCoupling_of_parts : OffCarrierCouplingStatement := by
  intro n k c C Γ σ hΓ μ hμ
  obtain ⟨K, hK, hKΓ, hKd⟩ := b3_offCarrierKernel n k c C Γ σ hΓ
  obtain ⟨π, hπ, hfst, hsnd, hdisp⟩ :=
    b3_kernelCoupling n Γ hΓ.isClosed.measurableSet K hK hKΓ hKd μ hμ
  refine ⟨π, hπ, hfst, hsnd, hdisp, fun x hx s _ => ?_⟩
  filter_upwards [hdisp] with p hp hp1
  exact b3_mem_ball_of_displacement hx hp1 hp

/-- **On-carrier transfer**: for a finite source `ν` carried by the reference
carrier, the square of `ν` is finite at `σ`-a.e. point of `Γ`. -/
theorem b3_onCarrier {n : ℕ} (hn : 1 ≤ n) {k : ℕ} {c C : ℝ} {Γ : Set (Space n)}
    {σ : Measure (Space n)} (hΓ : IsADRCarrier k c C Γ σ) {T : FamilyKind}
    (hT : Nonempty (Models n k T)) (hσ : ∀ᵐ z ∂σ, squareEnergy σ k T 1 z < ⊤)
    (ν : Measure (Space n)) [IsFiniteMeasure ν] (hνΓ : ν Γᶜ = 0) :
    ∀ᵐ x ∂σ, x ∈ Γ → squareEnergy ν k T 1 x < ⊤ := by
  have := hT
  obtain ⟨C₀, C₁, _hC₀, _hC₁, hrep⟩ := b3_input_replacement k c C
  -- One level `A`: finiteness off the excluded centres `Ξ_A`, whose mass is `O(ν(Γ)/A)`.
  have hlevel : ∀ A : ℝ, 0 < A → ∃ Ξ : Set (Space n),
      σ Ξ ≤ ENNReal.ofReal (C * 20 ^ k / c) * (ENNReal.ofReal (C₀ / A) * ν Γ) ∧
      ∀ᵐ x ∂σ, x ∈ Γ → x ∉ Ξ → squareEnergy ν k T 1 x < ⊤ := by
    intro A hA
    obtain ⟨I, z, r, E, hdata⟩ := hrep n hn Γ σ hΓ ν inferInstance hνΓ A hA
    have hdata' : b3_IsReplacementData k C₀ C₁ Γ σ ν A I z r E := hdata
    refine ⟨⋃ i, Metric.ball (z i) (20 * r i), ?_, ?_⟩
    · refine (b3_exceptionalMass n k c C C₀ C₁ Γ σ hΓ ν A I z r E hdata').trans ?_
      gcongr
      exact hdata'.2.2.2.2.2.2.2.1
    · obtain ⟨π, hπ, hfst, hsnd, hsupp, hloc⟩ :=
        b3_onCarrierCoupling n k c C C₀ C₁ Γ σ hΓ ν inferInstance hνΓ A hA I z r E hdata'
      obtain ⟨hmeas, hint⟩ := b3_onCarrierError_of_parts n k c C C₀ C₁ Γ σ hΓ ν inferInstance
        hνΓ A hA I z r E hdata' π hπ hfst hsupp (1 / 2)
      have hΞmeas : MeasurableSet (Γ \ ⋃ i, Metric.ball (z i) (20 * r i)) :=
        hΓ.isClosed.measurableSet.diff (MeasurableSet.iUnion fun i => measurableSet_ball)
      have herr : ∀ᵐ x ∂σ, x ∈ Γ \ ⋃ i, Metric.ball (z i) (20 * r i) →
          b3_couplingError k π x (1 / 2) < ⊤ := by
        rw [← ae_restrict_iff' hΞmeas]
        exact ae_lt_top hmeas (hint.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (measure_lt_top ν Γ))).ne
      have hdom : b3_replacedSource k Γ σ ν A I z r E ≤ ENNReal.ofReal (C₁ * A) • σ :=
        hdata'.2.2.2.2.2.2.2.2.2.1
      filter_upwards [hσ, herr] with x hxσ hxerr hxΓ hxΞ
      have hxi : ∀ i, x ∉ Metric.ball (z i) (20 * r i) := fun i hi =>
        hxΞ (mem_iUnion.mpr ⟨i, hi⟩)
      have hcpl := b3_couplingEnergy n k T π hπ x (1 / 2) 2 (by norm_num) (by norm_num)
        (fun s hs _ => hloc x hxΓ hxi s hs)
      rw [hfst, hsnd, show (2 : ℝ) * (1 / 2) = 1 by norm_num] at hcpl
      have hνA : squareEnergy (b3_replacedSource k Γ σ ν A I z r E) k T 1 x ≤
          ENNReal.ofReal (C₁ * A) * squareEnergy σ k T 1 x :=
        (squareEnergy_mono_measure hdom k T 1 x).trans_eq
          (squareEnergy_smul σ _ ENNReal.ofReal_ne_top k T 1 x)
      have hhalf : squareEnergy ν k T (1 / 2) x < ⊤ := by
        refine hcpl.trans_lt (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
        · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (hνA.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hxσ))
        · exact ENNReal.mul_lt_top (by simp) (hxerr ⟨hxΓ, hxΞ⟩)
      exact b3_squareEnergy_one_lt_top hn hΓ.dimension_pos hT ν x (by norm_num) hhalf
  -- Exceptional-set removal: the bad set has measure at most `O(ν(Γ)/A)` for every `A`.
  rw [ae_iff]
  have hbound : ∀ j : ℕ, σ {x | ¬(x ∈ Γ → squareEnergy ν k T 1 x < ⊤)} ≤
      ENNReal.ofReal (C * 20 ^ k / c) * (ENNReal.ofReal (C₀ / ((j : ℝ) + 1)) * ν Γ) := by
    intro j
    obtain ⟨Ξ, hΞ, hae⟩ := hlevel ((j : ℝ) + 1) (by positivity)
    rw [ae_iff] at hae
    calc σ {x | ¬(x ∈ Γ → squareEnergy ν k T 1 x < ⊤)}
        ≤ σ (Ξ ∪ {x | ¬(x ∈ Γ → x ∉ Ξ → squareEnergy ν k T 1 x < ⊤)}) := by
          refine measure_mono fun x hx => ?_
          by_cases hxΞ : x ∈ Ξ
          · exact Or.inl hxΞ
          · exact Or.inr fun h => hx fun hxΓ => h hxΓ hxΞ
      _ ≤ σ Ξ + σ {x | ¬(x ∈ Γ → x ∉ Ξ → squareEnergy ν k T 1 x < ⊤)} :=
          measure_union_le _ _
      _ = σ Ξ := by rw [hae, add_zero]
      _ ≤ _ := hΞ
  have hlim : Tendsto (fun j : ℕ => ENNReal.ofReal (C * 20 ^ k / c) *
      (ENNReal.ofReal (C₀ / ((j : ℝ) + 1)) * ν Γ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => C₀ / ((j : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul C₀
      rw [mul_zero] at this
      exact this.congr fun j => mul_one_div _ _
    have h2 : Tendsto (fun j : ℕ => ENNReal.ofReal (C₀ / ((j : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal h1
    have h3 := ENNReal.Tendsto.mul_const h2 (Or.inr (measure_ne_top ν Γ))
    have h4 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (C * 20 ^ k / c)) h3
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using h4
  exact le_antisymm (ge_of_tendsto' hlim hbound) (by simp)

/-- **Off-carrier reduction**: every finite ambient source `μ` is moved by the
kernel coupling to a finite source `ν` carried by `Γ`, and at `σ`-a.e. point of `Γ` a finite
square of `ν` gives a finite square of `μ`. -/
theorem b3_offCarrier {n : ℕ} (hn : 1 ≤ n) {k : ℕ} {c C : ℝ} {Γ : Set (Space n)}
    {σ : Measure (Space n)} (hΓ : IsADRCarrier k c C Γ σ) {T : FamilyKind}
    (hT : Nonempty (Models n k T)) (μ : Measure (Space n)) [IsFiniteMeasure μ] :
    ∃ ν : Measure (Space n), IsFiniteMeasure ν ∧ ν Γᶜ = 0 ∧
      ∀ᵐ x ∂σ, x ∈ Γ → squareEnergy ν k T 1 x < ⊤ → squareEnergy μ k T 1 x < ⊤ := by
  obtain ⟨π, hπ, hfst, hsndΓ, hdisp, hloc⟩ :=
    b3_offCarrierCoupling_of_parts n k c C Γ σ hΓ μ inferInstance
  have : IsFiniteMeasure π := hπ
  obtain ⟨hmeas, hint⟩ := b3_offCarrierError_of_parts n k c C Γ σ hΓ π hπ hdisp (1 / 4)
  refine ⟨π.snd, inferInstance, hsndΓ, ?_⟩
  have herr : ∀ᵐ x ∂σ, x ∈ Γ → b3_couplingError k π x (1 / 4) < ⊤ := by
    rw [← ae_restrict_iff' hΓ.isClosed.measurableSet]
    exact ae_lt_top hmeas (hint.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (measure_lt_top π.fst Γᶜ))).ne
  filter_upwards [herr] with x hxerr hxΓ hxν
  have hcpl := b3_couplingEnergy n k T π hπ x (1 / 4) 4 (by norm_num) (by norm_num)
    (fun s hs _ => hloc x hxΓ s hs)
  rw [hfst, show (4 : ℝ) * (1 / 4) = 1 by norm_num] at hcpl
  have hq : squareEnergy μ k T (1 / 4) x < ⊤ :=
    hcpl.trans_lt (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hxν,
      ENNReal.mul_lt_top (by simp) (hxerr hxΓ)⟩)
  exact b3_squareEnergy_one_lt_top hn hΓ.dimension_pos hT μ x (by norm_num) hq

/-- Transfer of square finiteness from an ADR measure to a source, assembled from the
component estimates. The type is exactly
`SourceTransferStatement`. -/
theorem adr_source_transfer_of_leaves : SourceTransferStatement := by
  intro n hn k c C Γ σ hΓ T hT hσ μ hμ
  have := hμ
  obtain ⟨ν, hν, hνΓ, hoff⟩ := b3_offCarrier hn hΓ hT μ
  have := hν
  have hon := b3_onCarrier hn hΓ hT hσ ν hνΓ
  filter_upwards [hoff, hon] with x h1 h2 hxΓ using h1 hxΓ (h2 hxΓ)

end ParabolicRectifiability.Characterization.SourceTransferTree
