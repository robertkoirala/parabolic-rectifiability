import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy
import ParabolicRectifiability.Geometry.Neck.HoleGrid

/-! # Tube covering and tube mass

Helper lemmas for the covariance lower bound (`d1a_covarianceLower_proof`) and the fitting gap
(`d1a_fittingGap_proof`).

Let `L` be an affine spatial plane of any rank `m` (rank zero included: then `L` is a point and
the tube is a spatial ball, as in the horizontal `k = 1` collapse of the covariance bound), `g` a
centre, `r > 0`, `0 < δ ≤ 1`, and `S ⊆ P(g, r)` a set all of whose points `z = (x, t)` satisfy
`‖x - P_L x‖ < δ r`.

* **Vertical tube** (whole time interval): `S` is covered by at most `C_n δ^{-(m+2)}` parabolic
  balls of radius `3 δ r` centred in `S` (`d1atube_cover_vertical`).
* **Horizontal tube** (time window `|t - τ| ≤ (δ r)^2`): at most `C_n δ^{-m}` such balls
  (`d1atube_cover_horizontal`).

Here `C_n = d1atube_countConst n = 4 (2n + 4)^n`. Construction: floor cells of side
`δ r / (m + 1)` in the `m` orthonormal coordinates of the direction of `L` (and, vertically, time
cells of length `(δ r)^2`); two points of `S` in one cell are within `3 δ r`; one centre per
occupied cell (the grid helpers of `Geometry.Neck`, as in the tube cover of the collapsed
children).

With `UpperRecenteringStatement` (taken as a hypothesis) and local ADR in `P(a, ρ)` with
`P(g, 4r) ⊆ P(a, ρ)`, `4r ≤ ρ` and `δ ≤ 1/2`, every covering ball `P(y, 3δr)` has mass
`≤ 2^k A (3 δ r)^k`, whence (`d1atube_mass_vertical`, `d1atube_mass_horizontal`)
`μ(S) ≤ C_n 6^k A δ^j r^k` whenever `m + 2 + j = k` (vertical) or `m + j = k` (horizontal);
`d1atube_massConst n k = C_n 6^k`. The uses are:

* covariance, vertical: `L'` of rank `k - 3`, `j = 1`; horizontal: `L'` of rank `k - 1`
  (a point at `k = 1`), time window from the horizontal fit, `j = 1`;
* fitting gap: the spatial plane of `V` (rank `k - 2`), the time of `H`, `j = 2`
  (`d1atube_gap_mass`, directly in terms of `modelCost H + modelCost V`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace PartitionEnergy

/-! ## Constants -/

/-- The cell-count constant `C_n = 4 (2n + 4)^n` of both tube covers. -/
def d1atube_countConst (n : ℕ) : ℝ := 4 * (2 * (n : ℝ) + 4) ^ n

/-- The tube-mass constant `C_n 6^k`. -/
def d1atube_massConst (n k : ℕ) : ℝ := d1atube_countConst n * 6 ^ k

theorem d1atube_countConst_pos (n : ℕ) : 0 < d1atube_countConst n := by
  unfold d1atube_countConst
  positivity

theorem d1atube_massConst_pos (n k : ℕ) : 0 < d1atube_massConst n k := by
  unfold d1atube_massConst
  have := d1atube_countConst_pos n
  positivity

/-! ## Covers from a finite cell index -/

/-- One centre per occupied cell: if `key` maps `S` into a finite set `K` and two points of
`S` with the same key are within `R`, then `S` is covered by at most `#K` balls of radius `R`
centred in `S`. -/
theorem d1atube_cover_of_key {n : ℕ} {κ : Type*} [DecidableEq κ] (S : Set (Space n))
    (key : Space n → κ) (K : Finset κ) (hK : ∀ z ∈ S, key z ∈ K) {R : ℝ}
    (hclose : ∀ z ∈ S, ∀ w ∈ S, key z = key w → dist z w < R) :
    ∃ Y : Finset (Space n), (↑Y : Set (Space n)) ⊆ S ∧
      S ⊆ ⋃ y ∈ Y, Metric.ball y R ∧ Y.card ≤ K.card := by
  classical
  let O := K.filter (fun a => ∃ z ∈ S, key z = a)
  have hwit : ∀ a ∈ O, ∃ z, z ∈ S ∧ key z = a := fun a ha => by
    obtain ⟨z, hz, hza⟩ := (Finset.mem_filter.1 ha).2
    exact ⟨z, hz, hza⟩
  let c : O → Space n := fun a => Classical.choose (hwit a.1 a.2)
  have hc : ∀ a : O, c a ∈ S ∧ key (c a) = a.1 := fun a => Classical.choose_spec (hwit a.1 a.2)
  refine ⟨O.attach.image c, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    exact (hc a).1
  · intro z hz
    have ha : key z ∈ O := Finset.mem_filter.2 ⟨hK z hz, z, hz, rfl⟩
    refine Set.mem_iUnion₂.2 ⟨c ⟨key z, ha⟩,
      Finset.mem_image.2 ⟨⟨key z, ha⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    rw [Metric.mem_ball]
    exact hclose z hz _ (hc ⟨key z, ha⟩).1 (hc ⟨key z, ha⟩).2.symm
  · calc (O.attach.image c).card ≤ O.attach.card := Finset.card_image_le
      _ = O.card := Finset.card_attach
      _ ≤ K.card := Finset.card_filter_le _ _

/-- The cell count `(2⌈(m+1)/ρ⌉)^m ρ^m ≤ (2n+4)^n` for `m ≤ n`, `0 < ρ ≤ 1` (the same bound
as `ChargeCollapse.gm2_collapsed_count`, restated to avoid importing its module). -/
theorem d1atube_count {n m : ℕ} (hmn : m ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    (2 * (⌈((m : ℝ) + 1) / ρ⌉₊ : ℝ)) ^ m * ρ ^ m ≤ (2 * n + 4) ^ n := by
  have hm : (m : ℝ) ≤ n := by exact_mod_cast hmn
  calc (2 * (⌈((m : ℝ) + 1) / ρ⌉₊ : ℝ)) ^ m * ρ ^ m ≤ (2 * ((m : ℝ) + 1 + 1)) ^ m :=
        ChargeCollapse.gm2_pow_bound hρ hρ1 (by positivity) m
    _ ≤ (2 * n + 4) ^ m := by
        gcongr
        linarith
    _ ≤ (2 * n + 4) ^ n := pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
        hmn

/-! ## The two tube covers -/

/-- **Vertical tube cover.** A set `S ⊆ P(g, r)` in the spatial `δ r`-tube of a plane `L` of
rank `m` (all times) is covered by balls of radius `3 δ r` centred in `S`, at most
`C_n δ^{-(m+2)}` of them. -/
theorem d1atube_cover_vertical {n m : ℕ} (L : AffineSpatialPlane n m) (g : Space n) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (S : Set (Space n))
    (hSg : S ⊆ Metric.ball g r) (hS : ∀ z ∈ S, ‖z.1 - L.projection z.1‖ < δ * r) :
    ∃ Y : Finset (Space n), (↑Y : Set (Space n)) ⊆ S ∧
      S ⊆ ⋃ y ∈ Y, Metric.ball y (3 * δ * r) ∧
      (Y.card : ℝ) * δ ^ (m + 2) ≤ d1atube_countConst n := by
  classical
  have hmn : m ≤ n := AffineSpatialPlane.nonempty_iff.mp ⟨L⟩
  set h₀ : ℝ := δ * r / ((m : ℝ) + 1) with hh₀
  have hh₀pos : 0 < h₀ := by rw [hh₀]; positivity
  have hmh : (m : ℝ) * h₀ ≤ δ * r := ChargeCollapse.gm2_mul_spacing_le _ (by positivity)
  have hht : 0 < (δ * r) ^ 2 := by positivity
  set N : ℕ := ⌈((m : ℝ) + 1) / δ⌉₊
  set Nt : ℕ := ⌈(1 : ℝ) / δ ^ 2⌉₊ with hNt
  let key : Space n → (Fin (Module.finrank ℝ L.direction) → ℤ) × ℤ := fun z =>
    (ChargeCollapse.gm2_cell (ChargeCollapse.gm2_planeBasis L) g.1 h₀ z.1,
      ⌊(z.2.val - g.2.val) / (δ * r) ^ 2⌋)
  set K := (Fintype.piFinset fun _ : Fin (Module.finrank ℝ L.direction) =>
    Finset.Ico (-(N : ℤ)) (N : ℤ)) ×ˢ Finset.Ico (-(Nt : ℤ)) (Nt : ℤ) with hKdef
  have hK : ∀ z ∈ S, key z ∈ K := by
    intro z hz
    have hb := ChargeCollapse.gm2_mem_ball hr (hSg hz)
    refine Finset.mem_product.2 ⟨?_, ?_⟩
    · refine ChargeCollapse.gm2_cell_mem (ChargeCollapse.gm2_planeBasis_norm L) hh₀pos hb.1
        (le_of_eq ?_)
      rw [hh₀]
      field_simp
    · refine ChargeCollapse.gm2_floor_mem_Ico hht hb.2 (le_of_eq ?_)
      field_simp
  have hclose : ∀ z ∈ S, ∀ w ∈ S, key z = key w → dist z w < 3 * δ * r := by
    intro z hz w hw hzw
    obtain ⟨hzw1, hzw2⟩ := Prod.ext_iff.1 hzw
    have h1 := ChargeCollapse.gm2_plane_cell_close L hh₀pos hzw1 (hS z hz) (hS w hw)
    have h2 := ChargeCollapse.gm2_abs_sub_lt_of_floor_eq hht hzw2
    rw [sub_sub_sub_cancel_right] at h2
    have hp : 0 ≤ (δ * r) ^ 2 := sq_nonneg _
    refine ChargeCollapse.gm2_dist_lt (by positivity) (by linarith) (lt_of_lt_of_le h2 ?_)
    calc (δ * r) ^ 2 ≤ 9 * (δ * r) ^ 2 := by linarith
      _ = (3 * δ * r) ^ 2 := by ring
  obtain ⟨Y, hYS, hcov, hcard⟩ := d1atube_cover_of_key S key K hK hclose
  refine ⟨Y, hYS, hcov, ?_⟩
  have hcardK : K.card = (2 * N) ^ m * (2 * Nt) := by
    rw [hKdef, Finset.card_product, ChargeCollapse.gm2_card_box, ChargeCollapse.gm2_card_Ico,
      L.rank_eq]
  have hc1 : (Y.card : ℝ) ≤ (2 * (N : ℝ)) ^ m * (2 * (Nt : ℝ)) := by
    have := hcard.trans hcardK.le
    exact_mod_cast this
  have hcnt := d1atube_count (n := n) (m := m) hmn hδ hδ1
  have htime : (2 * (Nt : ℝ)) * δ ^ 2 ≤ 4 := by
    have h := ChargeCollapse.gm2_pow_bound (ρ := δ ^ 2) (y := 1) (by positivity)
      (pow_le_one₀ hδ.le hδ1) zero_le_one 1
    simp only [pow_one] at h
    rw [← hNt] at h
    linarith
  have hB0 : 0 ≤ (2 * (Nt : ℝ)) * δ ^ 2 := by positivity
  unfold d1atube_countConst
  calc (Y.card : ℝ) * δ ^ (m + 2)
      ≤ (2 * (N : ℝ)) ^ m * (2 * (Nt : ℝ)) * δ ^ (m + 2) := by gcongr
    _ = ((2 * (N : ℝ)) ^ m * δ ^ m) * ((2 * (Nt : ℝ)) * δ ^ 2) := by rw [pow_add]; ring
    _ ≤ (2 * n + 4) ^ n * 4 := mul_le_mul hcnt htime hB0 (by positivity)
    _ = 4 * (2 * n + 4) ^ n := mul_comm _ _

/-- **Horizontal tube cover.** A set `S ⊆ P(g, r)` in the spatial `δ r`-tube of a plane `L` of
rank `m` and in the time window `|t - τ| ≤ (δ r)^2` is covered by balls of radius `3 δ r`
centred in `S`, at most `C_n δ^{-m}` of them. -/
theorem d1atube_cover_horizontal {n m : ℕ} (L : AffineSpatialPlane n m) (g : Space n) (τ : ℝ)
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (S : Set (Space n))
    (hSg : S ⊆ Metric.ball g r)
    (hS : ∀ z ∈ S, ‖z.1 - L.projection z.1‖ < δ * r ∧ |z.2.val - τ| ≤ (δ * r) ^ 2) :
    ∃ Y : Finset (Space n), (↑Y : Set (Space n)) ⊆ S ∧
      S ⊆ ⋃ y ∈ Y, Metric.ball y (3 * δ * r) ∧
      (Y.card : ℝ) * δ ^ m ≤ d1atube_countConst n := by
  classical
  have hmn : m ≤ n := AffineSpatialPlane.nonempty_iff.mp ⟨L⟩
  set h₀ : ℝ := δ * r / ((m : ℝ) + 1) with hh₀
  have hh₀pos : 0 < h₀ := by rw [hh₀]; positivity
  have hmh : (m : ℝ) * h₀ ≤ δ * r := ChargeCollapse.gm2_mul_spacing_le _ (by positivity)
  set N : ℕ := ⌈((m : ℝ) + 1) / δ⌉₊
  let key : Space n → (Fin (Module.finrank ℝ L.direction) → ℤ) := fun z =>
    ChargeCollapse.gm2_cell (ChargeCollapse.gm2_planeBasis L) g.1 h₀ z.1
  set K := Fintype.piFinset fun _ : Fin (Module.finrank ℝ L.direction) =>
    Finset.Ico (-(N : ℤ)) (N : ℤ) with hKdef
  have hK : ∀ z ∈ S, key z ∈ K := by
    intro z hz
    refine ChargeCollapse.gm2_cell_mem (ChargeCollapse.gm2_planeBasis_norm L) hh₀pos
      (ChargeCollapse.gm2_mem_ball hr (hSg hz)).1 (le_of_eq ?_)
    rw [hh₀]
    field_simp
  have hclose : ∀ z ∈ S, ∀ w ∈ S, key z = key w → dist z w < 3 * δ * r := by
    intro z hz w hw hzw
    have h1 := ChargeCollapse.gm2_plane_cell_close L hh₀pos hzw (hS z hz).1 (hS w hw).1
    have h2 : |z.2.val - w.2.val| ≤ (δ * r) ^ 2 + (δ * r) ^ 2 := by
      calc |z.2.val - w.2.val| ≤ |z.2.val - τ| + |τ - w.2.val| := abs_sub_le _ _ _
        _ ≤ (δ * r) ^ 2 + (δ * r) ^ 2 := by
          rw [abs_sub_comm τ]
          exact add_le_add (hS z hz).2 (hS w hw).2
    have hp : 0 < (δ * r) ^ 2 := by positivity
    refine ChargeCollapse.gm2_dist_lt (by positivity) (by linarith) ?_
    calc |z.2.val - w.2.val| ≤ (δ * r) ^ 2 + (δ * r) ^ 2 := h2
      _ < 9 * (δ * r) ^ 2 := by linarith
      _ = (3 * δ * r) ^ 2 := by ring
  obtain ⟨Y, hYS, hcov, hcard⟩ := d1atube_cover_of_key S key K hK hclose
  refine ⟨Y, hYS, hcov, ?_⟩
  have hcardK : K.card = (2 * N) ^ m := by
    rw [hKdef, ChargeCollapse.gm2_card_box, L.rank_eq]
  have hc1 : (Y.card : ℝ) ≤ (2 * (N : ℝ)) ^ m := by
    have := hcard.trans hcardK.le
    exact_mod_cast this
  have hcnt := d1atube_count (n := n) (m := m) hmn hδ hδ1
  have hpos : 0 ≤ (2 * (n : ℝ) + 4) ^ n := by positivity
  unfold d1atube_countConst
  calc (Y.card : ℝ) * δ ^ m ≤ (2 * (N : ℝ)) ^ m * δ ^ m := by gcongr
    _ ≤ (2 * n + 4) ^ n := hcnt
    _ ≤ 4 * (2 * n + 4) ^ n := by linarith

/-! ## Mass of a cover by upper recentring -/

/-- **Mass of a finite cover.** Under `UpperRecenteringStatement` and local ADR in `P(a, ρ)`,
with `P(g, 4r) ⊆ P(a, ρ)` and `4r ≤ ρ`, a set covered by the balls `P(y, s)`, `y ∈ Y ⊆ P(g, r)`,
`0 < s ≤ 2r`, has mass at most `#Y · 2^k A s^k`. -/
theorem d1atube_mass_of_cover {n k : ℕ} (hUR : UpperRecenteringStatement)
    {μ : Measure (Space n)} {A : ℝ} {a : Space n} {ρ : ℝ} (hADR : LocalADR μ k A a ρ)
    {g : Space n} {r : ℝ} (hball : Metric.ball g (4 * r) ⊆ Metric.ball a ρ) (h4 : 4 * r ≤ ρ)
    {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 2 * r) (S : Set (Space n)) (Y : Finset (Space n))
    (hY : (↑Y : Set (Space n)) ⊆ Metric.ball g r) (hcov : S ⊆ ⋃ y ∈ Y, Metric.ball y s) :
    μ S ≤ ENNReal.ofReal ((Y.card : ℝ) * (2 ^ k * A * s ^ k)) := by
  have hX : ∀ y ∈ Y, μ (Metric.ball y s) ≤ ENNReal.ofReal (2 ^ k * A * s ^ k) := by
    intro y hy
    refine hUR n k μ A a ρ hADR y s hs ?_ (by linarith)
    intro w hw
    apply hball
    have hyg := Metric.mem_ball.1 (hY (Finset.mem_coe.2 hy))
    rw [Metric.mem_ball] at hw ⊢
    calc dist w g ≤ dist w y + dist y g := dist_triangle _ _ _
      _ < s + r := add_lt_add hw hyg
      _ ≤ 4 * r := by linarith
  calc μ S ≤ μ (⋃ y ∈ Y, Metric.ball y s) := measure_mono hcov
    _ ≤ ∑ y ∈ Y, μ (Metric.ball y s) := measure_biUnion_finset_le Y _
    _ ≤ ∑ _y ∈ Y, ENNReal.ofReal (2 ^ k * A * s ^ k) := Finset.sum_le_sum hX
    _ = ENNReal.ofReal ((Y.card : ℝ) * (2 ^ k * A * s ^ k)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

/-- The exponent bookkeeping: `c δ^p ≤ C_n` and `p + j = k` give
`c · 2^k A (3 δ r)^k ≤ C_n 6^k A δ^j r^k`. -/
theorem d1atube_arith {n k p j : ℕ} {A δ r c : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ) (hr : 0 < r)
    (hpj : p + j = k) (hc : c * δ ^ p ≤ d1atube_countConst n) :
    c * (2 ^ k * A * (3 * δ * r) ^ k) ≤ d1atube_massConst n k * A * δ ^ j * r ^ k := by
  have hk : (3 * δ * r) ^ k = 3 ^ k * δ ^ p * δ ^ j * r ^ k := by
    rw [← hpj]
    ring
  rw [hk]
  unfold d1atube_massConst
  have h6 : (6 : ℝ) ^ k = 2 ^ k * 3 ^ k := by
    rw [← mul_pow]
    norm_num
  rw [h6]
  have hP : 0 ≤ 2 ^ k * 3 ^ k * A * δ ^ j * r ^ k :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hA) (pow_nonneg hδ.le _))
      (pow_nonneg hr.le _)
  calc c * (2 ^ k * A * (3 ^ k * δ ^ p * δ ^ j * r ^ k))
      = (c * δ ^ p) * (2 ^ k * 3 ^ k * A * δ ^ j * r ^ k) := by ring
    _ ≤ d1atube_countConst n * (2 ^ k * 3 ^ k * A * δ ^ j * r ^ k) :=
        mul_le_mul_of_nonneg_right hc hP
    _ = d1atube_countConst n * (2 ^ k * 3 ^ k) * A * δ ^ j * r ^ k := by ring

/-! ## The two tube-mass estimates -/

/-- **Vertical tube mass.** Under `UpperRecenteringStatement`, local ADR in `P(a, ρ)` with
`A ≥ 0`, `P(g, 4r) ⊆ P(a, ρ)`, `4r ≤ ρ` and `0 < δ ≤ 1/2`: every `S ⊆ P(g, r)` in the spatial
`δ r`-tube of a plane of rank `m` with `m + 2 + j = k` has `μ(S) ≤ C_n 6^k A δ^j r^k`. -/
theorem d1atube_mass_vertical {n k m j : ℕ} (hUR : UpperRecenteringStatement)
    {μ : Measure (Space n)} {A : ℝ} (hA : 0 ≤ A) {a : Space n} {ρ : ℝ}
    (hADR : LocalADR μ k A a ρ) {g : Space n} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball g (4 * r) ⊆ Metric.ball a ρ) (h4 : 4 * r ≤ ρ)
    {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (L : AffineSpatialPlane n m) (hj : m + 2 + j = k)
    (S : Set (Space n)) (hSg : S ⊆ Metric.ball g r)
    (hS : ∀ z ∈ S, ‖z.1 - L.projection z.1‖ < δ * r) :
    μ S ≤ ENNReal.ofReal (d1atube_massConst n k * A * δ ^ j * r ^ k) := by
  obtain ⟨Y, hYS, hcov, hcard⟩ :=
    d1atube_cover_vertical L g hr hδ (by linarith) S hSg hS
  have hs2 : 3 * δ * r ≤ 2 * r := by
    have := mul_le_mul_of_nonneg_right hδ2 hr.le
    linarith
  exact (d1atube_mass_of_cover hUR hADR hball h4 (by positivity) hs2 S Y (hYS.trans hSg)
    hcov).trans (ENNReal.ofReal_le_ofReal (d1atube_arith hA hδ hr hj hcard))

/-- **Horizontal tube mass.** Same hypotheses; every `S ⊆ P(g, r)` in the spatial `δ r`-tube of
a plane of rank `m` and in the time window `|t - τ| ≤ (δ r)^2`, with `m + j = k`, has
`μ(S) ≤ C_n 6^k A δ^j r^k`. Rank zero (`L` a point) is included. -/
theorem d1atube_mass_horizontal {n k m j : ℕ} (hUR : UpperRecenteringStatement)
    {μ : Measure (Space n)} {A : ℝ} (hA : 0 ≤ A) {a : Space n} {ρ : ℝ}
    (hADR : LocalADR μ k A a ρ) {g : Space n} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball g (4 * r) ⊆ Metric.ball a ρ) (h4 : 4 * r ≤ ρ)
    {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (L : AffineSpatialPlane n m) (τ : ℝ)
    (hj : m + j = k) (S : Set (Space n)) (hSg : S ⊆ Metric.ball g r)
    (hS : ∀ z ∈ S, ‖z.1 - L.projection z.1‖ < δ * r ∧ |z.2.val - τ| ≤ (δ * r) ^ 2) :
    μ S ≤ ENNReal.ofReal (d1atube_massConst n k * A * δ ^ j * r ^ k) := by
  obtain ⟨Y, hYS, hcov, hcard⟩ :=
    d1atube_cover_horizontal L g τ hr hδ (by linarith) S hSg hS
  have hs2 : 3 * δ * r ≤ 2 * r := by
    have := mul_le_mul_of_nonneg_right hδ2 hr.le
    linarith
  exact (d1atube_mass_of_cover hUR hADR hball h4 (by positivity) hs2 S Y (hYS.trans hSg)
    hcov).trans (ENNReal.ofReal_le_ofReal (d1atube_arith hA hδ hr hj hcard))

/-! ## Model-set adapters and the fitting-gap form -/

/-- A point at squared parabolic distance `< s^2` from a vertical model `(b + W) × ℝ` is within
spatial distance `s` of `b + W`. (`modelSet V` is `V.toSet` by definition.) -/
theorem d1atube_vertical_near {n k : ℕ} (V : VerticalModel n k) (z : Space n) {s : ℝ}
    (hs : 0 < s) (h : Metric.infEDist z V.toSet ^ 2 < ENNReal.ofReal (s ^ 2)) :
    ‖z.1 - V.spatial.projection z.1‖ < s := by
  obtain ⟨w, hw, hzw⟩ := ChargeCollapse.gm2_exists_near V.toSet z hs (not_le.2 h)
  have hw' : w.1 ∈ V.spatial.toSet := hw
  rw [ChargeCollapse.gm2_dist_eq, max_lt_iff] at hzw
  exact (V.spatial.nearest z.1 hw').trans_lt hzw.1

/-- A point at squared parabolic distance `< s^2` from a horizontal model `(a + U) × {τ}` is
within spatial distance `s` of `a + U` and has `|t - τ| < s^2`. -/
theorem d1atube_horizontal_near {n k : ℕ} (H : HorizontalModel n k) (z : Space n) {s : ℝ}
    (hs : 0 < s) (h : Metric.infEDist z H.toSet ^ 2 < ENNReal.ofReal (s ^ 2)) :
    ‖z.1 - H.spatial.projection z.1‖ < s ∧ |z.2.val - H.time| < s ^ 2 := by
  obtain ⟨w, hw, hzw⟩ := ChargeCollapse.gm2_exists_near H.toSet z hs (not_le.2 h)
  have hw' : w.1 ∈ H.spatial.toSet ∧ w.2.val = H.time := hw
  rw [ChargeCollapse.gm2_dist_eq, max_lt_iff, Real.sqrt_lt' hs] at hzw
  refine ⟨(H.spatial.nearest z.1 hw'.1).trans_lt hzw.1, ?_⟩
  rw [← hw'.2]
  exact hzw.2

/-- **Fitting-gap tube mass.** Under the hypotheses of the tube-mass estimates,
the points `w ∈ S ⊆ P(z, r)` with `d_P(w, H)^2 + d_P(w, V)^2 < (δ r)^2` (the costs of a
horizontal `H` and a vertical `V`) have total mass `≤ C_n 6^k A δ^2 r^k`. -/
theorem d1atube_gap_mass {n k : ℕ} (hUR : UpperRecenteringStatement)
    {μ : Measure (Space n)} {A : ℝ} (hA : 0 ≤ A) {a : Space n} {ρ : ℝ}
    (hADR : LocalADR μ k A a ρ) {z : Space n} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball z (4 * r) ⊆ Metric.ball a ρ) (h4 : 4 * r ≤ ρ)
    {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (H : Models n k .horizontal) (V : Models n k .vertical)
    (S : Set (Space n)) (hSz : S ⊆ Metric.ball z r)
    (hS : ∀ w ∈ S, modelCost H w + modelCost V w < ENNReal.ofReal ((δ * r) ^ 2)) :
    μ S ≤ ENNReal.ofReal (d1atube_massConst n k * A * δ ^ 2 * r ^ k) := by
  let H' : HorizontalModel n k := H
  let V' : VerticalModel n k := V
  have hdr : 0 < δ * r := by positivity
  refine d1atube_mass_horizontal hUR hA hADR hr hball h4 hδ hδ2 V'.spatial H'.time V'.rank_eq
    S hSz ?_
  intro w hw
  have hH : Metric.infEDist w H'.toSet ^ 2 < ENNReal.ofReal ((δ * r) ^ 2) :=
    lt_of_le_of_lt le_self_add (hS w hw)
  have hV : Metric.infEDist w V'.toSet ^ 2 < ENNReal.ofReal ((δ * r) ^ 2) :=
    lt_of_le_of_lt le_add_self (hS w hw)
  exact ⟨d1atube_vertical_near V' w hdr hV, (d1atube_horizontal_near H' w hdr hH).2.le⟩

end PartitionEnergy

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
