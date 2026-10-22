import ParabolicRectifiability.Geometry.Neck.Conclusions
import ParabolicRectifiability.Geometry.ExactAttachment

/-!
# Neck: horizontal distance and exact attachment

Three statements about necks, each proved under the name `<name>_proof` with the type of
`<name>`:

* `horizontal_dist_eq_of_mem_centers_proof`: on the centers of a horizontal neck with
  `γ ≤ min(c₀², 1)/4` the parabolic distance equals the spatial distance.
* `vertical_hasParametrization_of_chart_proof`: exact vertical attachment with distortion `2`.
* `horizontal_hasParametrization_of_chart_proof`: exact horizontal attachment with
  distortion `2`.

The attachment statements apply `ExactAttachment.exists_exact_attachment_vertical`
and `ExactAttachment.exists_exact_attachment_spatial` with `L = 5/4`. Compactness of the
parameter set is proved, not assumed: an antilipschitz, Lipschitz map on a complete space is a
closed embedding, so the preimage of the compact center set is compact.
-/

noncomputable section

namespace ParabolicRectifiability

namespace NeckHubTree

open MeasureTheory Set Topology
open scoped ENNReal NNReal

universe u

/-! ## Elementary helpers -/

/-- The parabolic distance in coordinates. -/
theorem nk2_dist_eq {n : ℕ} (z w : Space n) :
    dist z w = max ‖z.1 - w.1‖ (Real.sqrt |z.2.val - w.2.val|) :=
  dist_point z.1 w.1 z.2.val w.2.val

theorem nk2_min_sq_le {c₀ : ℝ} : min (c₀ ^ 2) 1 ≤ (min c₀ 1) ^ 2 := by
  rcases le_total c₀ 1 with h | h
  · rw [min_eq_left h]; exact min_le_left _ _
  · rw [min_eq_right h, one_pow]; exact min_le_right _ _

section Region

variable {n k : ℕ} {T : NeckType} {ι : Type u} {q : Space n}
  {R c₀ Cd Cs σ δ E κ θ γ : ℝ}

theorem nk2_mem_core (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ) {c : Space n} :
    c ∈ N.core ↔ c ∈ N.centers ∧ N.radius c = 0 := Iff.rfl

theorem nk2_mem_stopping (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ) {c : Space n} :
    c ∈ N.stopping ↔ c ∈ N.centers ∧ 0 < N.radius c := Iff.rfl

/-- Combined separation of two distinct centers: `min(c₀,1) max(d_c, d_{c'}) ≤ d_P(c,c')`,
from `stop_separation` (both stopping) or `core_separation` (one in the core). -/
theorem nk2_min_mul_max_le_dist (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ)
    {c c' : Space n} (hc : c ∈ N.centers) (hc' : c' ∈ N.centers) (hne : c ≠ c') :
    min c₀ 1 * max (N.radius c) (N.radius c') ≤ dist c c' := by
  have h0 := N.radius_nonneg c hc
  have h0' := N.radius_nonneg c' hc'
  have hm0 : 0 ≤ max (N.radius c) (N.radius c') := le_max_of_le_left h0
  rcases h0.lt_or_eq with hp | hz
  · rcases h0'.lt_or_eq with hp' | hz'
    · calc min c₀ 1 * max (N.radius c) (N.radius c')
          ≤ c₀ * max (N.radius c) (N.radius c') :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hm0
        _ ≤ dist c c' := N.stop_separation c hc c' hc' hp hp' hne
    · rw [← hz', max_eq_left h0]
      calc min c₀ 1 * N.radius c ≤ 1 * N.radius c :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) h0
        _ = N.radius c := one_mul _
        _ ≤ dist c c' := N.core_separation c hc hp c' hc' hz'.symm
  · rcases h0'.lt_or_eq with hp' | hz'
    · rw [← hz, max_eq_right h0']
      calc min c₀ 1 * N.radius c' ≤ 1 * N.radius c' :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) h0'
        _ = N.radius c' := one_mul _
        _ ≤ dist c' c := N.core_separation c' hc' hp' c hc hz.symm
        _ = dist c c' := dist_comm _ _
    · rw [← hz, ← hz', max_self, mul_zero]
      exact dist_nonneg

end Region

/-! ## Isometry of spatial projection on the centers -/

/-- **Distance on the centers** (`horizontal_dist_eq_of_mem_centers`). With `a = |x_c - x_{c'}|`,
`b² = |t_c - t_{c'}|`, `d = max(d_c, d_{c'})` and `c_* = min(c₀,1)`: record time
compatibility gives `b² ≤ γ max(a², d²)`. If `d = 0` then `b² ≤ γ a² ≤ a²`. If `d > 0` and
`b > a`: for `a > d`, `b² ≤ γ a² ≤ a² < b²`; for `a ≤ d`, `b² ≤ γ d² < c_*² d² ≤ d_P² = b²`.
Hence `b ≤ a` and `d_P(c,c') = a`. -/
theorem horizontal_dist_eq_of_mem_centers_proof {n k : ℕ} {ι : Type u} {q : Space n}
    {R c₀ Cd Cs σ δ E κ θ γ : ℝ} (N : NeckRegion n k .horizontal ι q R c₀ Cd Cs σ δ E κ θ γ) :
    γ ≤ min (c₀ ^ 2) 1 / 4 →
    ∀ c ∈ N.centers, ∀ c' ∈ N.centers, dist c c' = dist c.1 c'.1 := by
  intro hγ c hc c' hc'
  by_cases hcc : c = c'
  · subst hcc
    rw [dist_self, dist_self]
  have hc₀ : 0 < c₀ := N.parameters.c₀_pos
  have hγ0 : 0 ≤ γ := N.parameters.γ_nonneg rfl
  have hγ1 : γ ≤ 1 / 4 := hγ.trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  have htc : |c.2.val - c'.2.val| ≤
      γ * max (‖c.1 - c'.1‖ ^ 2) (max (N.radius c ^ 2) (N.radius c' ^ 2)) :=
    N.timeCompatible rfl (.inr c) (.inr c') hc hc'
  have hsep := nk2_min_mul_max_le_dist N hc hc' hcc
  have hdist := nk2_dist_eq c c'
  set a := ‖c.1 - c'.1‖ with ha
  set b2 := |c.2.val - c'.2.val| with hb2
  set d := max (N.radius c) (N.radius c') with hd
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb20 : 0 ≤ b2 := abs_nonneg _
  have hd0 : 0 ≤ d := le_max_of_le_left (N.radius_nonneg c hc)
  have hmaxsq : max (N.radius c ^ 2) (N.radius c' ^ 2) = d ^ 2 := by
    rcases le_total (N.radius c) (N.radius c') with h | h
    · rw [hd, max_eq_right h, max_eq_right (pow_le_pow_left₀ (N.radius_nonneg c hc) h 2)]
    · rw [hd, max_eq_left h, max_eq_left (pow_le_pow_left₀ (N.radius_nonneg c' hc') h 2)]
  rw [hmaxsq] at htc
  -- the key inequality `b² ≤ a²`
  have key : b2 ≤ a ^ 2 := by
    rcases hd0.lt_or_eq with hdpos | hdz
    · by_contra hba
      rw [not_le] at hba
      rcases lt_or_ge d a with had | had
      · -- `a > d`: the maximum is `a²`
        have hmax : max (a ^ 2) (d ^ 2) = a ^ 2 :=
          max_eq_left (pow_le_pow_left₀ hd0 had.le 2)
        rw [hmax] at htc
        have : γ * a ^ 2 ≤ a ^ 2 := by
          have := mul_le_mul_of_nonneg_right (hγ1.trans (by norm_num : (1 / 4 : ℝ) ≤ 1))
            (sq_nonneg a)
          linarith
        linarith
      · -- `a ≤ d`: the maximum is `d²`, and separation contradicts `b > a`
        have hmax : max (a ^ 2) (d ^ 2) = d ^ 2 :=
          max_eq_right (pow_le_pow_left₀ ha0 had 2)
        rw [hmax] at htc
        have hab : a < Real.sqrt b2 := (Real.lt_sqrt ha0).2 hba
        have hdb : dist c c' = Real.sqrt b2 := by
          rw [hdist]; exact max_eq_right hab.le
        have hm : 0 < min c₀ 1 := lt_min hc₀ one_pos
        have hlow : (min c₀ 1 * d) ^ 2 ≤ b2 := by
          have h1 : min c₀ 1 * d ≤ Real.sqrt b2 := hdb ▸ hsep
          exact (Real.le_sqrt (mul_nonneg hm.le hd0) hb20).1 h1
        have hpos : 0 < (min c₀ 1) ^ 2 * d ^ 2 := by positivity
        have h2 : γ * d ^ 2 ≤ min (c₀ ^ 2) 1 / 4 * d ^ 2 :=
          mul_le_mul_of_nonneg_right hγ (sq_nonneg d)
        have h3 : min (c₀ ^ 2) 1 / 4 * d ^ 2 ≤ (min c₀ 1) ^ 2 / 4 * d ^ 2 :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right nk2_min_sq_le (by norm_num)) (sq_nonneg d)
        rw [mul_pow] at hlow
        linarith
    · -- `d = 0`: `b² ≤ γ a² ≤ a²`
      rw [← hdz] at htc
      have hmax : max (a ^ 2) ((0 : ℝ) ^ 2) = a ^ 2 :=
        max_eq_left (by rw [zero_pow two_ne_zero]; exact sq_nonneg a)
      rw [hmax] at htc
      have := mul_le_mul_of_nonneg_right (hγ1.trans (by norm_num : (1 / 4 : ℝ) ≤ 1))
        (sq_nonneg a)
      linarith
  rw [hdist, dist_eq_norm]
  exact max_eq_left ((Real.sqrt_le_left ha0).2 key)

/-! ## Compact preimage adapter -/

/-- A Lipschitz and antilipschitz map on a complete space is a closed embedding, so the
preimage of a compact set is compact. -/
theorem nk2_isCompact_preimage {α β : Type*} [MetricSpace α] [CompleteSpace α] [MetricSpace β]
    {K K' : ℝ≥0} {f : α → β} (hlip : LipschitzWith K f) (hanti : AntilipschitzWith K' f)
    {S : Set β} (hS : IsCompact S) : IsCompact (f ⁻¹' S) :=
  (hanti.isClosedEmbedding hlip.uniformContinuous).isCompact_preimage hS

/-- The attachment constant `L = 5/4` as a nonnegative real. -/
def nk2L : ℝ≥0 := ⟨5 / 4, by norm_num⟩

theorem nk2L_coe : (nk2L : ℝ) = 5 / 4 := rfl

theorem nk2L_le : (nk2L : ℝ) ≤ 3 / 2 := by rw [nk2L_coe]; norm_num

theorem nk2_two_coe : ((2 : ℝ≥0) : ℝ) = 2 := by norm_num

/-! ## Vertical exact attachment -/

/-- **Vertical exact attachment** (`vertical_hasParametrization_of_chart`). `exists_exact_attachment_vertical`
with `L = 5/4`, `F⁰(p) = G(p.1, t_p)`, `C₀ = 𝒞₀`, the stopping centers as index type and the
supplied parameters at the centers' own times. The corrected map is `G + G'`; the parameter set
is `A = Φ⁻¹(𝒞)`, compact by `nk2_isCompact_preimage`; `Φ(A) = 𝒞` because `Φ` agrees with the
old map on core preimages and attaches every stopping center. -/
theorem vertical_hasParametrization_of_chart_proof {n k : ℕ} {ι : Type u} {q : Space n}
    {R c₀ Cd Cs σ δ E κ θ γ : ℝ} (N : NeckRegion n k .vertical ι q R c₀ Cd Cs σ δ E κ θ γ)
    (G : Spatial (k - 2) → ℝ → Spatial n) :
    (∀ p p' : Space (k - 2),
      4 / 5 * dist p p' ≤ dist (timePreservingMap G p) (timePreservingMap G p') ∧
        dist (timePreservingMap G p) (timePreservingMap G p') ≤ 11 / 10 * dist p p') →
    N.core ⊆ Set.range (timePreservingMap G) →
    (∀ c ∈ N.stopping, ∃ u : Spatial (k - 2),
      ‖G u c.2.val - c.1‖ ≤ 2 * (min c₀ 1 / 720) * N.radius c) →
    N.HasVerticalParametrization 2 := by
  intro hbi hcore hstop
  have hc₀ : 0 < c₀ := N.parameters.c₀_pos
  let F₀ : Space (k - 2) → Spatial n := fun p => G p.1 p.2.val
  have hΦ : ∀ p : Space (k - 2), ((F₀ p, p.2) : Space n) = timePreservingMap G p :=
    fun _ => rfl
  have hlip : LipschitzWith nk2L (fun p : Space (k - 2) => ((F₀ p, p.2) : Space n)) :=
    LipschitzWith.of_dist_le_mul fun p p' => by
      rw [hΦ, hΦ, nk2L_coe]
      have h1 := (hbi p p').2
      have h2 : (0 : ℝ) ≤ dist p p' := dist_nonneg
      linarith
  have hanti : AntilipschitzWith nk2L (fun p : Space (k - 2) => ((F₀ p, p.2) : Space n)) :=
    AntilipschitzWith.of_le_mul_dist fun p p' => by
      rw [hΦ, hΦ, nk2L_coe]
      have h1 := (hbi p p').1
      linarith
  choose u hu using hstop
  let p : N.stopping → Space (k - 2) := fun i => ((u i i.2, (i : Space n).2) : Space (k - 2))
  obtain ⟨G', hL2, hA2, hfix, hatt, -⟩ :=
    ExactAttachment.exists_exact_attachment_vertical F₀ nk2L nk2L_le hlip hanti N.core
      (fun i : N.stopping => (i : Space n)) (fun i => N.radius i) c₀
      (fun i => ((nk2_mem_stopping N).1 i.2).2)
      (fun i j hij => N.stop_separation i ((nk2_mem_stopping N).1 i.2).1 j
        ((nk2_mem_stopping N).1 j.2).1 ((nk2_mem_stopping N).1 i.2).2
        ((nk2_mem_stopping N).1 j.2).2 (fun h => hij (Subtype.ext h)))
      (fun i z hz => N.core_separation i ((nk2_mem_stopping N).1 i.2).1
        ((nk2_mem_stopping N).1 i.2).2 z ((nk2_mem_core N).1 hz).1 ((nk2_mem_core N).1 hz).2)
      p (fun _ => rfl) (min c₀ 1 / 720) (by positivity) le_rfl (fun i => hu i i.2)
  let Ψ : Space (k - 2) → Space n := fun r => ((F₀ r + G' r, r.2) : Space n)
  let Gout : Spatial (k - 2) → ℝ → Spatial n := fun v t => G v t + G' (point v t)
  have hΨ : ∀ r : Space (k - 2), timePreservingMap Gout r = Ψ r := fun _ => rfl
  refine ⟨Gout, Ψ ⁻¹' N.centers, fun r r' => ?_, nk2_isCompact_preimage hL2 hA2
    N.isCompact_centers, ?_⟩
  · rw [hΨ, hΨ]
    have h1 : dist r r' ≤ 2 * dist (Ψ r) (Ψ r') := by
      have := hA2.le_mul_dist r r'
      rwa [nk2_two_coe] at this
    have h2 : dist (Ψ r) (Ψ r') ≤ 2 * dist r r' := by
      have := hL2.dist_le_mul r r'
      rwa [nk2_two_coe] at this
    exact ⟨by linarith, h2⟩
  · have hfun : timePreservingMap Gout = Ψ := funext hΨ
    rw [hfun]
    refine Set.image_preimage_eq_of_subset fun z hz => ?_
    rcases (N.radius_nonneg z hz).lt_or_eq with hpos | hz0
    · have hs : z ∈ N.stopping := (nk2_mem_stopping N).2 ⟨hz, hpos⟩
      exact ⟨p ⟨z, hs⟩, hatt ⟨z, hs⟩⟩
    · have hzc : z ∈ N.core := (nk2_mem_core N).2 ⟨hz, hz0.symm⟩
      obtain ⟨r, hr⟩ := hcore hzc
      have hG0 : G' r = 0 := hfix r (by rw [hΦ r, hr]; exact hzc)
      refine ⟨r, ?_⟩
      show ((F₀ r + G' r, r.2) : Space n) = z
      rw [hG0, add_zero, hΦ r]
      exact hr

/-! ## Horizontal exact attachment -/

/-- **Horizontal exact attachment** (`horizontal_hasParametrization_of_chart`). `exists_exact_attachment_spatial`
with `L = 5/4`, `C₀ = π_x 𝒞₀` and spatial stopping centers, whose separations are the parabolic
ones by the isometry hypothesis. The corrected map `F = G + G'` is `2`-bi-Lipschitz;
`A = F⁻¹(π_x 𝒞)` is compact; `τ(u)` is the time of the (unique) center over `F(u)`; on `A` the
map `u ↦ (F u, τ u)` has `d_P = |F u - F v|`, and its range is exactly `𝒞`. -/
theorem horizontal_hasParametrization_of_chart_proof {n k : ℕ} {ι : Type u} {q : Space n}
    {R c₀ Cd Cs σ δ E κ θ γ : ℝ} (N : NeckRegion n k .horizontal ι q R c₀ Cd Cs σ δ E κ θ γ) :
    (∀ c ∈ N.centers, ∀ c' ∈ N.centers, dist c c' = dist c.1 c'.1) →
    ∀ G : Spatial k → Spatial n,
    (∀ u v : Spatial k,
      4 / 5 * ‖u - v‖ ≤ ‖G u - G v‖ ∧ ‖G u - G v‖ ≤ 11 / 10 * ‖u - v‖) →
    (∀ z ∈ N.core, z.1 ∈ Set.range G) →
    (∀ c ∈ N.stopping, ∃ u : Spatial k, ‖G u - c.1‖ ≤ 2 * (min c₀ 1 / 720) * N.radius c) →
    N.HasHorizontalParametrization 2 := by
  intro hiso G hbi hcore hstop
  have hc₀ : 0 < c₀ := N.parameters.c₀_pos
  have hlip : LipschitzWith nk2L G :=
    LipschitzWith.of_dist_le_mul fun u v => by
      rw [dist_eq_norm, dist_eq_norm, nk2L_coe]
      have h1 := (hbi u v).2
      have h2 : (0 : ℝ) ≤ ‖u - v‖ := norm_nonneg _
      linarith
  have hanti : AntilipschitzWith nk2L G :=
    AntilipschitzWith.of_le_mul_dist fun u v => by
      rw [dist_eq_norm, dist_eq_norm, nk2L_coe]
      have h1 := (hbi u v).1
      linarith
  choose u hu using hstop
  obtain ⟨G', hL2, hA2, hfix, hatt, -⟩ :=
    ExactAttachment.exists_exact_attachment_spatial G nk2L nk2L_le hlip hanti
      ((fun z : Space n => z.1) '' N.core) (fun i : N.stopping => (i : Space n).1)
      (fun i => N.radius i) c₀
      (fun i => ((nk2_mem_stopping N).1 i.2).2)
      (fun i j hij => by
        rw [← hiso i ((nk2_mem_stopping N).1 i.2).1 j ((nk2_mem_stopping N).1 j.2).1]
        exact N.stop_separation i ((nk2_mem_stopping N).1 i.2).1 j
          ((nk2_mem_stopping N).1 j.2).1 ((nk2_mem_stopping N).1 i.2).2
          ((nk2_mem_stopping N).1 j.2).2 (fun h => hij (Subtype.ext h)))
      (by
        intro i z hz
        obtain ⟨w, hw, rfl⟩ := hz
        show N.radius i ≤ dist (i : Space n).1 w.1
        rw [← hiso i ((nk2_mem_stopping N).1 i.2).1 w ((nk2_mem_core N).1 hw).1]
        exact N.core_separation i ((nk2_mem_stopping N).1 i.2).1
          ((nk2_mem_stopping N).1 i.2).2 w ((nk2_mem_core N).1 hw).1 ((nk2_mem_core N).1 hw).2)
      (fun i => u i i.2) (min c₀ 1 / 720) (by positivity) le_rfl (fun i => hu i i.2)
  let F : Spatial k → Spatial n := fun v => G v + G' v
  have hFlip : ∀ v w : Spatial k, dist (F v) (F w) ≤ 2 * dist v w := fun v w => by
    have := hL2.dist_le_mul v w
    rwa [nk2_two_coe] at this
  have hFanti : ∀ v w : Spatial k, dist v w ≤ 2 * dist (F v) (F w) := fun v w => by
    have := hA2.le_mul_dist v w
    rwa [nk2_two_coe] at this
  let A : Set (Spatial k) := F ⁻¹' ((fun z : Space n => z.1) '' N.centers)
  have hspec : ∀ v : A, ∃ c, c ∈ N.centers ∧ c.1 = F v := fun v => v.2
  let cen : A → Space n := fun v => Classical.choose (hspec v)
  have hcen : ∀ v : A, cen v ∈ N.centers ∧ (cen v).1 = F v :=
    fun v => Classical.choose_spec (hspec v)
  let τ : A → ℝ := fun v => (cen v).2.val
  have hpt : ∀ v : A, point (F v) (τ v) = cen v := fun v => by
    have h : point (F v) (τ v) = point (cen v).1 (cen v).2.val := by rw [(hcen v).2]
    exact h
  refine ⟨F, fun v w => ?_, A, τ, nk2_isCompact_preimage hL2 hA2
    (N.isCompact_centers.image continuous_fst), fun v w => ?_, ?_⟩
  · rw [← dist_eq_norm, ← dist_eq_norm]
    have h1 := hFanti v w
    exact ⟨by linarith, hFlip v w⟩
  · rw [hpt, hpt, hiso _ (hcen v).1 _ (hcen w).1, (hcen v).2, (hcen w).2, Subtype.dist_eq]
    have h1 := hFanti v w
    exact ⟨by linarith, hFlip v w⟩
  · apply Set.Subset.antisymm
    · rintro _ ⟨v, rfl⟩
      show point (F v) (τ v) ∈ N.centers
      rw [hpt]
      exact (hcen v).1
    · intro c hc
      -- a parameter over the spatial position of `c`
      have hex : ∃ r : Spatial k, F r = c.1 := by
        rcases (N.radius_nonneg c hc).lt_or_eq with hpos | hc0
        · have hs : c ∈ N.stopping := (nk2_mem_stopping N).2 ⟨hc, hpos⟩
          exact ⟨u c hs, hatt ⟨c, hs⟩⟩
        · have hcc : c ∈ N.core := (nk2_mem_core N).2 ⟨hc, hc0.symm⟩
          obtain ⟨r, hr⟩ := hcore c hcc
          have hG0 : G' r = 0 := hfix r ⟨c, hcc, hr.symm⟩
          refine ⟨r, ?_⟩
          show G r + G' r = c.1
          rw [hG0, add_zero, hr]
      obtain ⟨r, hr⟩ := hex
      have hrA : r ∈ A := ⟨c, hc, hr.symm⟩
      refine ⟨⟨r, hrA⟩, ?_⟩
      refine (hpt ⟨r, hrA⟩).trans ?_
      have h1 : (cen ⟨r, hrA⟩).1 = c.1 := (hcen ⟨r, hrA⟩).2.trans hr
      apply dist_eq_zero.1
      rw [hiso _ (hcen ⟨r, hrA⟩).1 c hc, h1, dist_self]

end NeckHubTree

end ParabolicRectifiability
