import ParabolicRectifiability.Foundations.SupportBounds
import ParabolicRectifiability.Metric.Similarity

/-! # The support bundle transported by a parabolic similarity

Proves `fsim_hasRegularSupportBounds_preimage_similarity_proof` with the type of
`fsim_hasRegularSupportBounds_preimage_similarity`, keeping the Hausdorff law `hH`, the tube law
`hT` and the transported covers as hypotheses.

Notation: `S = similarity a R hR`. Helpers (prefix `fsimb4_`):
* `S⁻¹' P̄(b, ρ) = P̄(S.symm b, R ρ)` for every real `ρ` (so `ρ < 0` needs no case split);
* `S⁻¹' K ∩ P(q, s) = S⁻¹'(K ∩ P(S q, s / R))`;
* the tube field via `hT` (checkpoint), then the remaining fields one by one.

All `ENNReal` arithmetic uses only `ofReal R ^ m * ofReal x = ofReal (R ^ m * x)` for `R > 0`,
valid for every real `x` (no sign information on `C` is needed).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Foundations

/-! ## Elementary helpers -/

theorem fsimb4_mul_div {R : ℝ} (hR : 0 < R) (x : ℝ) : R * (x / R) = x :=
  mul_div_cancel₀ x hR.ne'

/-- `ofReal R ^ m * ofReal x = ofReal (R ^ m * x)` for `R > 0` and every real `x`. -/
theorem fsimb4_ofReal_pow_mul {R : ℝ} (hR : 0 < R) (m : ℕ) (x : ℝ) :
    ENNReal.ofReal R ^ m * ENNReal.ofReal x = ENNReal.ofReal (R ^ m * x) := by
  rw [ENNReal.ofReal_mul (pow_nonneg hR.le m), ENNReal.ofReal_pow hR.le]

/-- `R^k · C (x/R)^k = C x^k`. -/
theorem fsimb4_scale_real {R : ℝ} (hR : 0 < R) (k : ℕ) (C x : ℝ) :
    R ^ k * (C * (x / R) ^ k) = C * x ^ k := by
  calc R ^ k * (C * (x / R) ^ k) = C * (R * (x / R)) ^ k := by rw [mul_pow]; ring
    _ = C * x ^ k := by rw [fsimb4_mul_div hR]

/-- The tube constant: `R^{n+2} · C ρ^k (r/R)^{n+2-k} = C (R ρ)^k r^{n+2-k}` for `k ≤ n + 2`. -/
theorem fsimb4_tube_real {n k : ℕ} (hkn : k ≤ n + 2) (C : ℝ) {R : ℝ} (hR : 0 < R)
    (ρ r : ℝ) :
    R ^ (n + 2) * (C * ρ ^ k * (r / R) ^ (n + 2 - k)) = C * (R * ρ) ^ k * r ^ (n + 2 - k) := by
  obtain ⟨m, hm⟩ : ∃ m, n + 2 - k = m := ⟨_, rfl⟩
  have hnm : n + 2 = k + m := by omega
  rw [hm, hnm, pow_add]
  calc R ^ k * R ^ m * (C * ρ ^ k * (r / R) ^ m)
      = C * (R * ρ) ^ k * (R * (r / R)) ^ m := by rw [mul_pow, mul_pow]; ring
    _ = C * (R * ρ) ^ k * r ^ m := by rw [fsimb4_mul_div hR]

/-! ## Geometric helpers -/

/-- `S⁻¹' P̄(b, ρ) = P̄(S.symm b, R ρ)`, for every real `ρ`. -/
theorem fsimb4_preimage_closedBall {n : ℕ} (a : Space n) (R : ℝ) (hR : 0 < R)
    (b : Space n) (ρ : ℝ) :
    similarity a R hR ⁻¹' Metric.closedBall b ρ =
      Metric.closedBall ((similarity a R hR).symm b) (R * ρ) := by
  ext w
  simp only [mem_preimage, Metric.mem_closedBall]
  have hd : dist (similarity a R hR w) b = R⁻¹ * dist w ((similarity a R hR).symm b) := by
    rw [← dist_similarity a R hR w ((similarity a R hR).symm b), Homeomorph.apply_symm_apply]
  rw [hd, inv_mul_le_iff₀ hR]

/-- `S⁻¹' K ∩ P(q, s) = S⁻¹'(K ∩ P(S q, s / R))`, for every set `K` and real `s`. -/
theorem fsimb4_preimage_inter_ball {n : ℕ} (a : Space n) (R : ℝ) (hR : 0 < R)
    (K : Set (Space n)) (q : Space n) (s : ℝ) :
    similarity a R hR ⁻¹' K ∩ Metric.ball q s =
      similarity a R hR ⁻¹' (K ∩ Metric.ball (similarity a R hR q) (s / R)) := by
  rw [preimage_inter, preimage_similarity_ball, fsimb4_mul_div hR]

/-- Scale bookkeeping: `0 < s ≤ R ρ` gives `0 < s / R ≤ ρ`. -/
theorem fsimb4_div_scale {R : ℝ} (hR : 0 < R) {ρ s : ℝ} (hs : 0 < s) (hsR : s ≤ R * ρ) :
    0 < s / R ∧ s / R ≤ ρ :=
  ⟨div_pos hs hR, (div_le_iff₀ hR).2 (by linarith [mul_comm R ρ])⟩

/-- Points of `S⁻¹'(KH ∪ KV) ∩ P(q, s)` are sent by `S` into `(KH ∪ KV) ∩ P(S q, s / R)`. -/
theorem fsimb4_mem_image {n : ℕ} (a : Space n) (R : ℝ) (hR : 0 < R)
    (KH KV : Set (Space n)) (q : Space n) (s : ℝ) {x : Space n}
    (hx : x ∈ (similarity a R hR ⁻¹' KH ∪ similarity a R hR ⁻¹' KV) ∩ Metric.ball q s) :
    similarity a R hR x ∈ (KH ∪ KV) ∩ Metric.ball (similarity a R hR q) (s / R) := by
  rw [← preimage_union, fsimb4_preimage_inter_ball] at hx
  exact hx

/-! ## The fields -/

/-- **Tube field (checkpoint)**, from `hT`. -/
theorem fsimb4_minkowski {n k : ℕ} (hkn : k ≤ n + 2) (C : ℝ)
    (a : Space n) (R : ℝ) (hR : 0 < R)
    (hT : ∀ (K : Set (Space n)) (r : ℝ),
      parabolicVolume n {z | Metric.infEDist z (similarity a R hR ⁻¹' K) < ENNReal.ofReal r} =
        ENNReal.ofReal R ^ (n + 2) *
          parabolicVolume n {w | Metric.infEDist w K < ENNReal.ofReal (r / R)})
    (b : Space n) (ρ : ℝ) (KH KV : Set (Space n)) (h : HasRegularSupportBounds k C b ρ KH KV) :
    ∀ r, 0 < r → r ≤ R * ρ →
      parabolicVolume n {z | Metric.infEDist z
          (similarity a R hR ⁻¹' KH ∪ similarity a R hR ⁻¹' KV) < ENNReal.ofReal r} ≤
        ENNReal.ofReal (C * (R * ρ) ^ k * r ^ (n + 2 - k)) := by
  intro r hr hrR
  obtain ⟨hr', hrρ⟩ := fsimb4_div_scale hR hr hrR
  rw [← preimage_union, hT (KH ∪ KV) r]
  calc ENNReal.ofReal R ^ (n + 2) *
        parabolicVolume n {w | Metric.infEDist w (KH ∪ KV) < ENNReal.ofReal (r / R)}
      ≤ ENNReal.ofReal R ^ (n + 2) * ENNReal.ofReal (C * ρ ^ k * (r / R) ^ (n + 2 - k)) := by
        gcongr
        exact h.minkowski _ hr' hrρ
    _ = ENNReal.ofReal (C * (R * ρ) ^ k * r ^ (n + 2 - k)) := by
        rw [fsimb4_ofReal_pow_mul hR, fsimb4_tube_real hkn C hR]

/-- Global Hausdorff field, from `hH`. -/
theorem fsimb4_hausdorff_total {n k : ℕ} (C : ℝ) (a : Space n) (R : ℝ) (hR : 0 < R)
    (hH : ∀ A : Set (Space n),
      hausdorffP n k (similarity a R hR ⁻¹' A) = ENNReal.ofReal R ^ k * hausdorffP n k A)
    (b : Space n) (ρ : ℝ) (KH KV : Set (Space n)) (h : HasRegularSupportBounds k C b ρ KH KV) :
    hausdorffP n k (similarity a R hR ⁻¹' KH ∪ similarity a R hR ⁻¹' KV) ≤
      ENNReal.ofReal (C * (R * ρ) ^ k) := by
  rw [← preimage_union, hH]
  calc ENNReal.ofReal R ^ k * hausdorffP n k (KH ∪ KV)
      ≤ ENNReal.ofReal R ^ k * ENNReal.ofReal (C * ρ ^ k) := by
        gcongr
        exact h.hausdorff_total
    _ = ENNReal.ofReal (C * (R * ρ) ^ k) := by
        rw [fsimb4_ofReal_pow_mul hR]
        congr 1
        rw [mul_pow]
        ring

/-- Local Hausdorff field, from `hH` at the scale `s / R`. -/
theorem fsimb4_hausdorff_local {n k : ℕ} (C : ℝ) (a : Space n) (R : ℝ) (hR : 0 < R)
    (hH : ∀ A : Set (Space n),
      hausdorffP n k (similarity a R hR ⁻¹' A) = ENNReal.ofReal R ^ k * hausdorffP n k A)
    (b : Space n) (ρ : ℝ) (KH KV : Set (Space n)) (h : HasRegularSupportBounds k C b ρ KH KV) :
    ∀ q s, 0 < s → s ≤ R * ρ →
      hausdorffP n k ((similarity a R hR ⁻¹' KH ∪ similarity a R hR ⁻¹' KV) ∩
        Metric.ball q s) ≤ ENNReal.ofReal (C * s ^ k) := by
  intro q s hs hsR
  obtain ⟨hs', hsρ⟩ := fsimb4_div_scale hR hs hsR
  rw [← preimage_union, fsimb4_preimage_inter_ball, hH]
  calc ENNReal.ofReal R ^ k *
        hausdorffP n k ((KH ∪ KV) ∩ Metric.ball (similarity a R hR q) (s / R))
      ≤ ENNReal.ofReal R ^ k * ENNReal.ofReal (C * (s / R) ^ k) := by
        gcongr
        exact h.hausdorff_local _ _ hs' hsρ
    _ = ENNReal.ofReal (C * s ^ k) := by
        rw [fsimb4_ofReal_pow_mul hR, fsimb4_scale_real hR]

/-- Separated-set field: `S` maps an `r`-separated set injectively onto an `r/R`-separated
set at the scale `s / R`, and `(s/R)/(r/R) = s/r`. -/
theorem fsimb4_separated {n k : ℕ} (C : ℝ) (a : Space n) (R : ℝ) (hR : 0 < R)
    (b : Space n) (ρ : ℝ) (KH KV : Set (Space n)) (h : HasRegularSupportBounds k C b ρ KH KV) :
    ∀ q s r, 0 < s → s ≤ R * ρ → 0 < r → r ≤ s →
      ∀ F : Finset (Space n), (↑F : Set (Space n)) ⊆
          (similarity a R hR ⁻¹' KH ∪ similarity a R hR ⁻¹' KV) ∩ Metric.ball q s →
        (∀ x ∈ F, ∀ y ∈ F, x ≠ y → r ≤ dist x y) →
          (F.card : ℝ) ≤ C * (s / r) ^ k := by
  classical
  intro q s r hs hsR hr hrs F hF hsep
  obtain ⟨hs', hsρ⟩ := fsimb4_div_scale hR hs hsR
  have hr' : 0 < r / R := div_pos hr hR
  have hrs' : r / R ≤ s / R := div_le_div_of_nonneg_right hrs hR.le
  have hF' : (↑(F.image (similarity a R hR)) : Set (Space n)) ⊆
      (KH ∪ KV) ∩ Metric.ball (similarity a R hR q) (s / R) := by
    intro y hy
    rw [Finset.coe_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact fsimb4_mem_image a R hR KH KV q s (hF hx)
  have hsep' : ∀ x ∈ F.image (similarity a R hR), ∀ y ∈ F.image (similarity a R hR),
      x ≠ y → r / R ≤ dist x y := by
    intro x hx y hy hxy
    rw [Finset.mem_image] at hx hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    have hne : x ≠ y := fun hxy' => hxy (by rw [hxy'])
    rw [dist_similarity, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hsep x hx y hy hne) (inv_nonneg.2 hR.le)
  have key := h.separated (similarity a R hR q) (s / R) (r / R) hs' hsρ hr' hrs'
    (F.image (similarity a R hR)) hF' hsep'
  rw [Finset.card_image_of_injective _ (similarity a R hR).injective,
    div_div_div_cancel_right₀ hR.ne'] at key
  exact key

/-- Disjointness of the image balls `P(S z_i, r_i / R) = S '' P(z_i, r_i)`. -/
theorem fsimb4_disjoint_balls {n : ℕ} (a : Space n) (R : ℝ) (hR : 0 < R)
    (z w : Space n) (r t : ℝ) (hd : Disjoint (Metric.ball z r) (Metric.ball w t)) :
    Disjoint (Metric.ball (similarity a R hR z) (r / R))
      (Metric.ball (similarity a R hR w) (t / R)) := by
  rw [← image_similarity_ball, ← image_similarity_ball,
    disjoint_image_iff (similarity a R hR).injective]
  exact hd

/-- `ofReal r ^ k = ofReal R ^ k * ofReal (r / R) ^ k` for `R > 0`. -/
theorem fsimb4_ofReal_pow_split {R : ℝ} (hR : 0 < R) (k : ℕ) (r : ℝ) :
    ENNReal.ofReal r ^ k = ENNReal.ofReal R ^ k * ENNReal.ofReal (r / R) ^ k := by
  rw [← mul_pow, ← ENNReal.ofReal_mul hR.le, fsimb4_mul_div hR]

/-- Finite packing field. -/
theorem fsimb4_finite_packing {n k : ℕ} (C : ℝ) (a : Space n) (R : ℝ) (hR : 0 < R)
    (b : Space n) (ρ : ℝ) (KH KV : Set (Space n)) (h : HasRegularSupportBounds k C b ρ KH KV) :
    ∀ q s, 0 < s → s ≤ R * ρ →
      ∀ (l : ℕ) (z : Fin l → Space n) (r : Fin l → ℝ),
        (∀ i, z i ∈ (similarity a R hR ⁻¹' KH ∪ similarity a R hR ⁻¹' KV) ∩
          Metric.ball q s) →
        (∀ i, 0 < r i ∧ r i ≤ s) →
        (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
        (∑ i, ENNReal.ofReal (r i) ^ k) ≤ ENNReal.ofReal (C * s ^ k) := by
  intro q s hs hsR l z r hz hr hdisj
  obtain ⟨hs', hsρ⟩ := fsimb4_div_scale hR hs hsR
  have key := h.finite_packing (similarity a R hR q) (s / R) hs' hsρ l
    (fun i => similarity a R hR (z i)) (fun i => r i / R)
    (fun i => fsimb4_mem_image a R hR KH KV q s (hz i))
    (fun i => ⟨div_pos (hr i).1 hR, div_le_div_of_nonneg_right (hr i).2 hR.le⟩)
    (fun i j hij => fsimb4_disjoint_balls a R hR _ _ _ _ (hdisj i j hij))
  calc (∑ i, ENNReal.ofReal (r i) ^ k)
      = ∑ i, ENNReal.ofReal R ^ k * ENNReal.ofReal (r i / R) ^ k :=
        Finset.sum_congr rfl fun i _ => fsimb4_ofReal_pow_split hR k (r i)
    _ = ENNReal.ofReal R ^ k * ∑ i, ENNReal.ofReal (r i / R) ^ k := by
        rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal R ^ k * ENNReal.ofReal (C * (s / R) ^ k) := by
        gcongr
    _ = ENNReal.ofReal (C * s ^ k) := by
        rw [fsimb4_ofReal_pow_mul hR, fsimb4_scale_real hR]

/-- Countable packing field: sums in `ℝ≥0∞` scale by exactly `(ofReal R)^k`. -/
theorem fsimb4_countable_packing {n k : ℕ} (C : ℝ) (a : Space n) (R : ℝ) (hR : 0 < R)
    (b : Space n) (ρ : ℝ) (KH KV : Set (Space n)) (h : HasRegularSupportBounds k C b ρ KH KV) :
    ∀ q s, 0 < s → s ≤ R * ρ →
      ∀ (I : Set ℕ) (z : I → Space n) (r : I → ℝ),
        (∀ i, z i ∈ (similarity a R hR ⁻¹' KH ∪ similarity a R hR ⁻¹' KV) ∩
          Metric.ball q s) →
        (∀ i, 0 < r i ∧ r i ≤ s) →
        (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
        (∑' i, ENNReal.ofReal (r i) ^ k) ≤ ENNReal.ofReal (C * s ^ k) := by
  intro q s hs hsR I z r hz hr hdisj
  obtain ⟨hs', hsρ⟩ := fsimb4_div_scale hR hs hsR
  have key := h.countable_packing (similarity a R hR q) (s / R) hs' hsρ I
    (fun i => similarity a R hR (z i)) (fun i => r i / R)
    (fun i => fsimb4_mem_image a R hR KH KV q s (hz i))
    (fun i => ⟨div_pos (hr i).1 hR, div_le_div_of_nonneg_right (hr i).2 hR.le⟩)
    (fun i j hij => fsimb4_disjoint_balls a R hR _ _ _ _ (hdisj i j hij))
  calc (∑' i, ENNReal.ofReal (r i) ^ k)
      = ∑' i, ENNReal.ofReal R ^ k * ENNReal.ofReal (r i / R) ^ k :=
        tsum_congr fun i => fsimb4_ofReal_pow_split hR k (r i)
    _ = ENNReal.ofReal R ^ k * ∑' i, ENNReal.ofReal (r i / R) ^ k :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal R ^ k * ENNReal.ofReal (C * (s / R) ^ k) := by
        gcongr
    _ = ENNReal.ofReal (C * s ^ k) := by
        rw [fsimb4_ofReal_pow_mul hR, fsimb4_scale_real hR]

/-! ## The support bundle -/

/-- **The support bundle transported by the similarity** (the type of
`fsim_hasRegularSupportBounds_preimage_similarity`).
The bundle `HasRegularSupportBounds k C b ρ` of `(K_H, K_V)` transports to the bundle
`HasRegularSupportBounds k C (S.symm b) (R ρ)` of `(S⁻¹' K_H, S⁻¹' K_V)` with the same
constant `C`, for every centre `b`, every real scale `ρ` and every real `C`, given the
Hausdorff law `hH`, the tube law `hT` and the transported covers `hHcov`, `hVcov`. -/
theorem fsim_hasRegularSupportBounds_preimage_similarity_proof {n k : ℕ} (hkn : k ≤ n + 2)
    (C : ℝ) (a : Space n) (R : ℝ) (hR : 0 < R)
    (hH : ∀ A : Set (Space n),
      hausdorffP n k (similarity a R hR ⁻¹' A) = ENNReal.ofReal R ^ k * hausdorffP n k A)
    (hT : ∀ (K : Set (Space n)) (r : ℝ),
      parabolicVolume n {z | Metric.infEDist z (similarity a R hR ⁻¹' K) < ENNReal.ofReal r} =
        ENNReal.ofReal R ^ (n + 2) *
          parabolicVolume n {w | Metric.infEDist w K < ENNReal.ofReal (r / R)})
    (b : Space n) (ρ : ℝ) (KH KV : Set (Space n)) (h : HasRegularSupportBounds k C b ρ KH KV)
    (hHcov : ∀ ε : ℝ, 0 < ε → HasHorizontalGraphCover k (similarity a R hR ⁻¹' KH) ε)
    (hVcov : ∀ ε : ℝ, 0 < ε →
      HasGeneralRegularVerticalGraphCover k (similarity a R hR ⁻¹' KV) ε) :
    HasRegularSupportBounds k C ((similarity a R hR).symm b) (R * ρ)
      (similarity a R hR ⁻¹' KH) (similarity a R hR ⁻¹' KV) where
  horizontal_compact := (similarity a R hR).isCompact_preimage.2 h.horizontal_compact
  vertical_compact := (similarity a R hR).isCompact_preimage.2 h.vertical_compact
  horizontal_subset := by
    rw [← fsimb4_preimage_closedBall]
    exact preimage_mono h.horizontal_subset
  vertical_subset := by
    rw [← fsimb4_preimage_closedBall]
    exact preimage_mono h.vertical_subset
  horizontal_unavailable := fun hk => by rw [h.horizontal_unavailable hk, preimage_empty]
  vertical_unavailable := fun hk => by rw [h.vertical_unavailable hk, preimage_empty]
  horizontal_graphs := hHcov
  vertical_graphs := hVcov
  hausdorff_total := fsimb4_hausdorff_total C a R hR hH b ρ KH KV h
  hausdorff_local := fsimb4_hausdorff_local C a R hR hH b ρ KH KV h
  separated := fsimb4_separated C a R hR b ρ KH KV h
  minkowski := fsimb4_minkowski hkn C a R hR hT b ρ KH KV h
  finite_packing := fsimb4_finite_packing C a R hR b ρ KH KV h
  countable_packing := fsimb4_countable_packing C a R hR b ρ KH KV h

end ParabolicRectifiability.Foundations
