import Mathlib

open MeasureTheory Filter Topology Set

namespace GlobalTheory.CompanionTheory.HolMean

/- English proof (translation)
Take `⟨ε, hε, hεs⟩` from `Metric.mem_nhds_iff.mp (Filter.inter_mem hV (hU.mem_nhds hz₀))`. Use `⟨ε / 2, half_pos hε, Metric.ball z₀ (ε / 2), Metric.ball_mem_nhds z₀ (half_pos hε), ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Conclude with `(hεs (Metric.ball_subset_ball (by linarith) hz)).2`. Introduce `f hf C hC z hz`.

Establish `hsub : Metric.closedBall z (ε / 2) ⊆ V ∩ U`. Introduce `w hw`. Apply `hεs` to reduce the goal to its premises. Rewrite `hz`, the goal using `[Metric.mem_ball]`. Rewrite `hw` using `[Metric.mem_closedBall]`.

Combine the equalities or inequalities in the displayed calculation. Apply `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (half_pos hε)` to reduce the goal to its premises. Apply `DifferentiableOn.diffContOnCl` to reduce the goal to its premises. Conclude with `hf.mono (Metric.closure_ball_subset_closedBall.trans (hsub.trans Set.inter_subset_right))`. Introduce `w hw`.

Conclude with `hC w (hsub (Metric.sphere_subset_closedBall hw))`.
-/
lemma cauchy_nhds {U V : Set ℂ} (hU : IsOpen U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hV : V ∈ 𝓝 z₀) :
    ∃ R : ℝ, 0 < R ∧ ∃ W ∈ 𝓝 z₀, W ⊆ U ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
      ∀ C : ℝ, (∀ z ∈ V ∩ U, ‖f z‖ ≤ C) → ∀ z ∈ W, ‖deriv f z‖ ≤ C / R := by
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hV (hU.mem_nhds hz₀))
  refine ⟨ε / 2, half_pos hε, Metric.ball z₀ (ε / 2), Metric.ball_mem_nhds z₀ (half_pos hε), ?_, ?_⟩
  · intro z hz
    exact (hεs (Metric.ball_subset_ball (by linarith) hz)).2
  · intro f hf C hC z hz
    have hsub : Metric.closedBall z (ε / 2) ⊆ V ∩ U := by
      intro w hw
      apply hεs
      rw [Metric.mem_ball] at hz ⊢
      rw [Metric.mem_closedBall] at hw
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := by linarith
        _ = ε := by ring
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (half_pos hε)
    · apply DifferentiableOn.diffContOnCl
      exact hf.mono (Metric.closure_ball_subset_closedBall.trans (hsub.trans Set.inter_subset_right))
    · intro w hw
      exact hC w (hsub (Metric.sphere_subset_closedBall hw))

section Series

variable {κ : Type} {U : Set ℂ}

/- English proof (translation)
Establish `key : ∀ z₀ ∈ U, ∃ ε > 0, Metric.ball z₀ ε ⊆ U ∧ ∃ u : κ → ℝ, Summable u ∧ ∀ z ∈ Metric.ball z₀ ε, ∀ k, ‖F k z‖ ≤ u k`. Introduce `z₀ hz₀`. Take `⟨V, hV, u, hu, hle⟩` from `hb z₀ hz₀`. Take `⟨ε, hε, hεs⟩` from `Metric.mem_nhds_iff.mp (Filter.inter_mem hV (hU.mem_nhds hz₀))`. Conclude with `⟨ε, hε, fun z hz => (hεs hz).2, u, hu, fun z hz k => hle z (hεs hz) k⟩`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `z₀ hz₀`. Take `⟨ε, hε, hsub, u, hu, hle⟩` from `key z₀ hz₀`. Establish `hd` using `Complex.differentiableOn_tsum_of_summable_norm hu (fun k => (hF k).mono hsub) Metric.isOpen_ball (fun k w hw => hle w hw k)`. Conclude with `(hd.differentiableAt (Metric.ball_mem_nhds z₀ hε)).differentiableWithinAt`.

Introduce `z₀ hz₀`. Take `⟨ε, hε, hsub, u, hu, hle⟩` from `key z₀ hz₀`. Conclude with `(Complex.hasSum_deriv_of_summable_norm hu (fun k => (hF k).mono hsub) Metric.isOpen_ball (fun k w hw => hle w hw k) (Metric.mem_ball_self hε)).tsum_eq.symm`. Introduce `z₀ hz₀`. Take `⟨V, hV, u, hu, hle⟩` from `hb z₀ hz₀`.

Take `⟨R, hR, W, hW, hWU, hest⟩` from `cauchy_nhds hU hz₀ hV`. Use `⟨W, hW, fun k => u k / R, hu.div_const R, ?_⟩` and prove the remaining obligations. Introduce `z hz k`. Conclude with `hest (F k) (hF k) (u k) (fun w hw => hle w hw k) z hz.1`.
-/
lemma series_step (hU : IsOpen U) (F : κ → ℂ → ℂ) (hF : ∀ k, DifferentiableOn ℂ (F k) U)
    (hb : ∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ u : κ → ℝ, Summable u ∧ ∀ z ∈ V ∩ U, ∀ k, ‖F k z‖ ≤ u k) :
    DifferentiableOn ℂ (fun w => ∑' k, F k w) U ∧
    (∀ z ∈ U, deriv (fun w => ∑' k, F k w) z = ∑' k, deriv (F k) z) ∧
    (∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ u : κ → ℝ, Summable u ∧ ∀ z ∈ V ∩ U, ∀ k, ‖deriv (F k) z‖ ≤ u k) := by
  have key : ∀ z₀ ∈ U, ∃ ε > 0, Metric.ball z₀ ε ⊆ U ∧ ∃ u : κ → ℝ, Summable u ∧
      ∀ z ∈ Metric.ball z₀ ε, ∀ k, ‖F k z‖ ≤ u k := by
    intro z₀ hz₀
    obtain ⟨V, hV, u, hu, hle⟩ := hb z₀ hz₀
    obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hV (hU.mem_nhds hz₀))
    exact ⟨ε, hε, fun z hz => (hεs hz).2, u, hu, fun z hz k => hle z (hεs hz) k⟩
  refine ⟨?_, ?_, ?_⟩
  · intro z₀ hz₀
    obtain ⟨ε, hε, hsub, u, hu, hle⟩ := key z₀ hz₀
    have hd := Complex.differentiableOn_tsum_of_summable_norm hu (fun k => (hF k).mono hsub)
      Metric.isOpen_ball (fun k w hw => hle w hw k)
    exact (hd.differentiableAt (Metric.ball_mem_nhds z₀ hε)).differentiableWithinAt
  · intro z₀ hz₀
    obtain ⟨ε, hε, hsub, u, hu, hle⟩ := key z₀ hz₀
    exact (Complex.hasSum_deriv_of_summable_norm hu (fun k => (hF k).mono hsub) Metric.isOpen_ball
      (fun k w hw => hle w hw k) (Metric.mem_ball_self hε)).tsum_eq.symm
  · intro z₀ hz₀
    obtain ⟨V, hV, u, hu, hle⟩ := hb z₀ hz₀
    obtain ⟨R, hR, W, hW, hWU, hest⟩ := cauchy_nhds hU hz₀ hV
    refine ⟨W, hW, fun k => u k / R, hu.div_const R, ?_⟩
    intro z hz k
    exact hest (F k) (hF k) (u k) (fun w hw => hle w hw k) z hz.1

/- English proof (translation)
Establish `loc : ∀ (n : ℕ) (f g : ℂ → ℂ), Set.EqOn f g U → Set.EqOn (iteratedDeriv n f) (iteratedDeriv n g) U`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `f g h z hz`.

Simplify using `only [iteratedDeriv_zero]`. Conclude with `h hz`. Consider the case `succ n ih`. Introduce `f g h z hz`. Rewrite using `[iteratedDeriv_succ, iteratedDeriv_succ]`.

Conclude with `Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (hU.mem_nhds hz) (ih f g h))`. Proceed by induction on `r with`. Consider the case `zero`. Introduce `F _ _ z _`. Simplify using `only [iteratedDeriv_zero]`.

Consider the case `succ r ih`. Introduce `F hF hb z hz`. Take `⟨_, hder, hb'⟩` from `series_step hU F hF hb`. Establish `hF' : ∀ k, DifferentiableOn ℂ (deriv (F k)) U` using `fun k => (hF k).deriv hU`. Simplify using `only [iteratedDeriv_succ']`.

Rewrite using `[loc r (deriv (fun w => ∑' k, F k w)) (fun w => ∑' k, deriv (F k) w) (fun w hw => hder w hw) hz]`. Conclude with `ih (fun k => deriv (F k)) hF' hb' z hz`.
-/
lemma iteratedDeriv_series (hU : IsOpen U) (r : ℕ) : ∀ (F : κ → ℂ → ℂ),
    (∀ k, DifferentiableOn ℂ (F k) U) →
    (∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ u : κ → ℝ, Summable u ∧ ∀ z ∈ V ∩ U, ∀ k, ‖F k z‖ ≤ u k) →
    ∀ z ∈ U, iteratedDeriv r (fun w => ∑' k, F k w) z = ∑' k, iteratedDeriv r (F k) z := by
  have loc : ∀ (n : ℕ) (f g : ℂ → ℂ), Set.EqOn f g U →
      Set.EqOn (iteratedDeriv n f) (iteratedDeriv n g) U := by
    intro n
    induction n with
    | zero =>
      intro f g h z hz
      simp only [iteratedDeriv_zero]
      exact h hz
    | succ n ih =>
      intro f g h z hz
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      exact Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (hU.mem_nhds hz) (ih f g h))
  induction r with
  | zero =>
    intro F _ _ z _
    simp only [iteratedDeriv_zero]
  | succ r ih =>
    intro F hF hb z hz
    obtain ⟨_, hder, hb'⟩ := series_step hU F hF hb
    have hF' : ∀ k, DifferentiableOn ℂ (deriv (F k)) U := fun k => (hF k).deriv hU
    simp only [iteratedDeriv_succ']
    rw [loc r (deriv (fun w => ∑' k, F k w)) (fun w => ∑' k, deriv (F k) w)
      (fun w hw => hder w hw) hz]
    exact ih (fun k => deriv (F k)) hF' hb' z hz

end Series

section Measurability

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {U : Set ℂ}

/- English proof (translation)
Take `⟨δ, hδ, hball⟩` from `Metric.isOpen_iff.mp hU z hz`. Take `⟨t, htpos, htlt, ht0⟩ : ∃ t : ℕ → ℝ, (∀ n, 0 < t n) ∧ (∀ n, t n < δ) ∧ Tendsto t atTop (𝓝 0)` from `⟨fun n => δ / ((n : ℝ) + 2), fun n => div_pos hδ (by positivity), fun n => div_lt_self hδ (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith), tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)⟩`. Establish `hmem : ∀ n, z + (t n : ℂ) ∈ U`. Introduce `n`. Apply `hball` to reduce the goal to its premises.

Rewrite using `[Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (htpos n)]`. Conclude with `htlt n`. Establish `hz0 : AEStronglyMeasurable (G z) μ` using `by simpa using hm 0 (by simpa using hz)`. Establish `htc : Tendsto (fun n => (t n : ℂ)) atTop (𝓝[≠] 0)`. Use `tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩` and prove the remaining obligations.

Use `(Complex.continuous_ofReal.tendsto 0).comp ht0` as an intermediate fact. Rewrite `this` using `[Complex.ofReal_zero]`. Conclude with `this`. Conclude with `Set.mem_compl_singleton_iff.mpr (Complex.ofReal_ne_zero.mpr (htpos n).ne')`. Use `aestronglyMeasurable_of_tendsto_ae (f := fun n ω => ((t n : ℂ))⁻¹ • (G (z + t n) ω - G z ω)) atTop (fun n => ?_) (ae_of_all μ fun ω => ?_)` and prove the remaining obligations.

Conclude with `((hm (t n) (hmem n)).sub hz0).const_smul ((t n : ℂ))⁻¹`. Establish `hda : HasDerivAt (fun w => G w ω) (deriv (fun w => G w ω) z) z` using `(((hd ω) z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt`. Conclude with `hda.tendsto_slope_zero.comp htc`.
-/
lemma aesm_deriv (hU : IsOpen U) (G : ℂ → Ω → ℂ)
    (hd : ∀ ω, DifferentiableOn ℂ (fun z => G z ω) U) {z : ℂ} (hz : z ∈ U)
    (hm : ∀ x : ℝ, z + x ∈ U → AEStronglyMeasurable (G (z + x)) μ) :
    AEStronglyMeasurable (fun ω => deriv (fun w => G w ω) z) μ := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU z hz
  obtain ⟨t, htpos, htlt, ht0⟩ : ∃ t : ℕ → ℝ, (∀ n, 0 < t n) ∧ (∀ n, t n < δ) ∧
      Tendsto t atTop (𝓝 0) :=
    ⟨fun n => δ / ((n : ℝ) + 2), fun n => div_pos hδ (by positivity),
     fun n => div_lt_self hδ (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith),
     tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)⟩
  have hmem : ∀ n, z + (t n : ℂ) ∈ U := by
    intro n
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (htpos n)]
    exact htlt n
  have hz0 : AEStronglyMeasurable (G z) μ := by simpa using hm 0 (by simpa using hz)
  have htc : Tendsto (fun n => (t n : ℂ)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
    · have := (Complex.continuous_ofReal.tendsto 0).comp ht0
      rw [Complex.ofReal_zero] at this
      exact this
    · exact Set.mem_compl_singleton_iff.mpr (Complex.ofReal_ne_zero.mpr (htpos n).ne')
  refine aestronglyMeasurable_of_tendsto_ae
    (f := fun n ω => ((t n : ℂ))⁻¹ • (G (z + t n) ω - G z ω)) atTop (fun n => ?_)
    (ae_of_all μ fun ω => ?_)
  · exact ((hm (t n) (hmem n)).sub hz0).const_smul ((t n : ℂ))⁻¹
  · have hda : HasDerivAt (fun w => G w ω) (deriv (fun w => G w ω) z) z :=
      (((hd ω) z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
    exact hda.tendsto_slope_zero.comp htc

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `G _ hm t ht`. Simplify using `only [iteratedDeriv_zero]`. Conclude with `hm t ht`.

Consider the case `succ n ih`. Introduce `G hd hm t ht`. Simplify using `only [iteratedDeriv_succ']`. Establish `hd' : ∀ ω, DifferentiableOn ℂ (fun z => deriv (fun w => G w ω) z) U` using `fun ω => (hd ω).deriv hU`. Establish `hm' : ∀ s : ℝ, (s : ℂ) ∈ U → AEStronglyMeasurable (fun ω => deriv (fun w => G w ω) (s : ℂ)) μ`.

Introduce `s hs`. Use `aesm_deriv hU G hd hs (fun x hx => ?_)` and prove the remaining obligations. Establish `h` using `hm (s + x) (by rw [Complex.ofReal_add]; exact hx)`. Rewrite `h` using `[Complex.ofReal_add]`. Conclude with `h`.

Conclude with `ih (fun z ω => deriv (fun w => G w ω) z) hd' hm' t ht`.
-/
lemma aesm_iteratedDeriv_real (hU : IsOpen U) (n : ℕ) : ∀ G : ℂ → Ω → ℂ,
    (∀ ω, DifferentiableOn ℂ (fun z => G z ω) U) →
    (∀ t : ℝ, (t : ℂ) ∈ U → AEStronglyMeasurable (G t) μ) →
    ∀ t : ℝ, (t : ℂ) ∈ U → AEStronglyMeasurable (fun ω => iteratedDeriv n (fun w => G w ω) t) μ := by
  induction n with
  | zero =>
    intro G _ hm t ht
    simp only [iteratedDeriv_zero]
    exact hm t ht
  | succ n ih =>
    intro G hd hm t ht
    simp only [iteratedDeriv_succ']
    have hd' : ∀ ω, DifferentiableOn ℂ (fun z => deriv (fun w => G w ω) z) U :=
      fun ω => (hd ω).deriv hU
    have hm' : ∀ s : ℝ, (s : ℂ) ∈ U →
        AEStronglyMeasurable (fun ω => deriv (fun w => G w ω) (s : ℂ)) μ := by
      intro s hs
      refine aesm_deriv hU G hd hs (fun x hx => ?_)
      have h := hm (s + x) (by rw [Complex.ofReal_add]; exact hx)
      rw [Complex.ofReal_add] at h
      exact h
    exact ih (fun z ω => deriv (fun w => G w ω) z) hd' hm' t ht

/- English proof (translation)
Take `⟨t, ρ, hρ, hzb, hsub⟩` from `hball z hz`. Establish `htU : (t : ℂ) ∈ U` using `hsub (Metric.mem_ball_self hρ)`. Establish `hterm : ∀ n : ℕ, AEStronglyMeasurable (fun ω => ((n.factorial : ℂ))⁻¹ • (z - t) ^ n • iteratedDeriv n (fun w => G w ω) (t : ℂ)) μ`. Introduce `n`. Conclude with `((aesm_iteratedDeriv_real hU n G hd hm t htU).const_smul ((z - t) ^ n)).const_smul ((n.factorial : ℂ))⁻¹`.

Use `aestronglyMeasurable_of_tendsto_ae (f := fun N ω => ∑ n ∈ Finset.range N, ((n.factorial : ℂ))⁻¹ • (z - t) ^ n • iteratedDeriv n (fun w => G w ω) (t : ℂ)) atTop (fun N => ?_) (ae_of_all μ fun ω => ?_)` and prove the remaining obligations. Establish `h` using `Finset.aestronglyMeasurable_sum (μ := μ) (Finset.range N) (fun n _ => hterm n)`. Rewrite `h` using `[Finset.sum_fn]`. Conclude with `h`. Establish `hs` using `Complex.hasSum_taylorSeries_on_ball ((hd ω).mono hsub) hzb`.

Conclude with `hs.tendsto_sum_nat`.
-/
lemma aesm_of_real (hU : IsOpen U)
    (hball : ∀ z ∈ U, ∃ (t ρ : ℝ), 0 < ρ ∧ z ∈ Metric.ball (t : ℂ) ρ ∧ Metric.ball (t : ℂ) ρ ⊆ U)
    (G : ℂ → Ω → ℂ) (hd : ∀ ω, DifferentiableOn ℂ (fun z => G z ω) U)
    (hm : ∀ t : ℝ, (t : ℂ) ∈ U → AEStronglyMeasurable (G t) μ) {z : ℂ} (hz : z ∈ U) :
    AEStronglyMeasurable (G z) μ := by
  obtain ⟨t, ρ, hρ, hzb, hsub⟩ := hball z hz
  have htU : (t : ℂ) ∈ U := hsub (Metric.mem_ball_self hρ)
  have hterm : ∀ n : ℕ, AEStronglyMeasurable (fun ω => ((n.factorial : ℂ))⁻¹ •
      (z - t) ^ n • iteratedDeriv n (fun w => G w ω) (t : ℂ)) μ := by
    intro n
    exact ((aesm_iteratedDeriv_real hU n G hd hm t htU).const_smul ((z - t) ^ n)).const_smul
      ((n.factorial : ℂ))⁻¹
  refine aestronglyMeasurable_of_tendsto_ae
    (f := fun N ω => ∑ n ∈ Finset.range N, ((n.factorial : ℂ))⁻¹ •
      (z - t) ^ n • iteratedDeriv n (fun w => G w ω) (t : ℂ)) atTop (fun N => ?_)
    (ae_of_all μ fun ω => ?_)
  · have h := Finset.aestronglyMeasurable_sum (μ := μ) (Finset.range N) (fun n _ => hterm n)
    rw [Finset.sum_fn] at h
    exact h
  · have hs := Complex.hasSum_taylorSeries_on_ball ((hd ω).mono hsub) hzb
    exact hs.tendsto_sum_nat

end Measurability

section Integral

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {U : Set ℂ}

/- English proof (translation)
Establish `h2 : ∀ z ∈ U, AEStronglyMeasurable (fun ω => deriv (fun w => G w ω) z) μ` using `fun z hz => aesm_deriv hU G hd hz (fun x hx => hm _ hx)`. Establish `h3 : ∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ g : Ω → ℝ, Integrable g μ ∧ ∀ z ∈ V ∩ U, ∀ ω, ‖deriv (fun w => G w ω) z‖ ≤ g ω`. Introduce `z₀ hz₀`. Take `⟨V, hV, g, hg, hle⟩` from `hb z₀ hz₀`. Take `⟨R, hR, W, hW, hWU, hest⟩` from `cauchy_nhds hU hz₀ hV`.

Use `⟨W, hW, fun ω => g ω / R, hg.div_const R, ?_⟩` and prove the remaining obligations. Introduce `z hz ω`. Conclude with `hest (fun w => G w ω) (hd ω) (g ω) (fun w hw => hle w hw ω) z hz.1`. Use `⟨?_, h2, h3⟩` and prove the remaining obligations. Introduce `z hz`.

Take `⟨V, hV, g, hg, hle⟩` from `hb z hz`. Take `⟨W, hW, g', hg', hle'⟩` from `h3 z hz`. Take `⟨ε, hε, hεs⟩` from `Metric.mem_nhds_iff.mp (Filter.inter_mem hW (hU.mem_nhds hz))`. Establish `hint : Integrable (G z) μ` using `hg.mono' (hm z hz) (ae_of_all μ fun ω => hle z ⟨mem_of_mem_nhds hV, hz⟩ ω)`. Conclude with `(hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := G) (F' := fun x ω => deriv (fun w => G w ω) x) (bound := g') (Metric.ball_mem_nhds z hε) (Filter.eventually_of_mem (hU.mem_nhds hz) hm) hint (h2 z hz) (ae_of_all μ fun ω x hx => hle' x (hεs hx) ω) hg' (ae_of_all μ fun ω x hx …`.
-/
lemma integral_step (hU : IsOpen U) (G : ℂ → Ω → ℂ)
    (hd : ∀ ω, DifferentiableOn ℂ (fun z => G z ω) U)
    (hm : ∀ z ∈ U, AEStronglyMeasurable (G z) μ)
    (hb : ∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ g : Ω → ℝ, Integrable g μ ∧ ∀ z ∈ V ∩ U, ∀ ω, ‖G z ω‖ ≤ g ω) :
    (∀ z ∈ U, HasDerivAt (fun w => ∫ ω, G w ω ∂μ) (∫ ω, deriv (fun w => G w ω) z ∂μ) z) ∧
    (∀ z ∈ U, AEStronglyMeasurable (fun ω => deriv (fun w => G w ω) z) μ) ∧
    (∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ z ∈ V ∩ U, ∀ ω, ‖deriv (fun w => G w ω) z‖ ≤ g ω) := by
  have h2 : ∀ z ∈ U, AEStronglyMeasurable (fun ω => deriv (fun w => G w ω) z) μ :=
    fun z hz => aesm_deriv hU G hd hz (fun x hx => hm _ hx)
  have h3 : ∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ z ∈ V ∩ U, ∀ ω, ‖deriv (fun w => G w ω) z‖ ≤ g ω := by
    intro z₀ hz₀
    obtain ⟨V, hV, g, hg, hle⟩ := hb z₀ hz₀
    obtain ⟨R, hR, W, hW, hWU, hest⟩ := cauchy_nhds hU hz₀ hV
    refine ⟨W, hW, fun ω => g ω / R, hg.div_const R, ?_⟩
    intro z hz ω
    exact hest (fun w => G w ω) (hd ω) (g ω) (fun w hw => hle w hw ω) z hz.1
  refine ⟨?_, h2, h3⟩
  intro z hz
  obtain ⟨V, hV, g, hg, hle⟩ := hb z hz
  obtain ⟨W, hW, g', hg', hle'⟩ := h3 z hz
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hW (hU.mem_nhds hz))
  have hint : Integrable (G z) μ :=
    hg.mono' (hm z hz) (ae_of_all μ fun ω => hle z ⟨mem_of_mem_nhds hV, hz⟩ ω)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := G) (F' := fun x ω => deriv (fun w => G w ω) x) (bound := g') (Metric.ball_mem_nhds z hε)
    (Filter.eventually_of_mem (hU.mem_nhds hz) hm) hint (h2 z hz)
    (ae_of_all μ fun ω x hx => hle' x (hεs hx) ω) hg'
    (ae_of_all μ fun ω x hx =>
      (((hd ω) x (hεs hx).2).differentiableAt (hU.mem_nhds (hεs hx).2)).hasDerivAt)).2

/- English proof (translation)
Establish `loc : ∀ (n : ℕ) (f g : ℂ → ℂ), Set.EqOn f g U → Set.EqOn (iteratedDeriv n f) (iteratedDeriv n g) U`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `f g h z hz`.

Simplify using `only [iteratedDeriv_zero]`. Conclude with `h hz`. Consider the case `succ n ih`. Introduce `f g h z hz`. Rewrite using `[iteratedDeriv_succ, iteratedDeriv_succ]`.

Conclude with `Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (hU.mem_nhds hz) (ih f g h))`. Proceed by induction on `r with`. Consider the case `zero`. Introduce `G _ _ _ z _`. Simplify using `only [iteratedDeriv_zero]`.

Consider the case `succ r ih`. Introduce `G hd hm hb z hz`. Take `⟨h1, h2, h3⟩` from `integral_step hU G hd hm hb`. Establish `hd' : ∀ ω, DifferentiableOn ℂ (fun z => deriv (fun w => G w ω) z) U` using `fun ω => (hd ω).deriv hU`. Simplify using `only [iteratedDeriv_succ']`.

Use `(loc r (deriv (fun w => ∫ ω, G w ω ∂μ)) (fun w => ∫ ω, deriv (fun w' => G w' ω) w ∂μ) (fun w hw => (h1 w hw).deriv) hz).trans ?_` and prove the remaining obligations. Conclude with `ih (fun z ω => deriv (fun w => G w ω) z) hd' h2 h3 z hz`.
-/
lemma iteratedDeriv_integral (hU : IsOpen U) (r : ℕ) : ∀ G : ℂ → Ω → ℂ,
    (∀ ω, DifferentiableOn ℂ (fun z => G z ω) U) →
    (∀ z ∈ U, AEStronglyMeasurable (G z) μ) →
    (∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ g : Ω → ℝ, Integrable g μ ∧ ∀ z ∈ V ∩ U, ∀ ω, ‖G z ω‖ ≤ g ω) →
    ∀ z ∈ U, iteratedDeriv r (fun w => ∫ ω, G w ω ∂μ) z =
      ∫ ω, iteratedDeriv r (fun w => G w ω) z ∂μ := by
  have loc : ∀ (n : ℕ) (f g : ℂ → ℂ), Set.EqOn f g U →
      Set.EqOn (iteratedDeriv n f) (iteratedDeriv n g) U := by
    intro n
    induction n with
    | zero =>
      intro f g h z hz
      simp only [iteratedDeriv_zero]
      exact h hz
    | succ n ih =>
      intro f g h z hz
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      exact Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (hU.mem_nhds hz) (ih f g h))
  induction r with
  | zero =>
    intro G _ _ _ z _
    simp only [iteratedDeriv_zero]
  | succ r ih =>
    intro G hd hm hb z hz
    obtain ⟨h1, h2, h3⟩ := integral_step hU G hd hm hb
    have hd' : ∀ ω, DifferentiableOn ℂ (fun z => deriv (fun w => G w ω) z) U :=
      fun ω => (hd ω).deriv hU
    simp only [iteratedDeriv_succ']
    refine (loc r (deriv (fun w => ∫ ω, G w ω ∂μ)) (fun w => ∫ ω, deriv (fun w' => G w' ω) w ∂μ)
      (fun w hw => (h1 w hw).deriv) hz).trans ?_
    exact ih (fun z ω => deriv (fun w => G w ω) z) hd' h2 h3 z hz

end Integral

/- English proof (translation)
Establish `hser : ∀ p ω, ∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ u : κ → ℝ, Summable u ∧ ∀ z ∈ V ∩ U, ∀ k, ‖F p z ω k‖ ≤ u k`. Introduce `p ω z₀ hz₀`. Take `⟨N, hN, M, g, hM, hg, hMg, hle⟩` from `hB (p, z₀) ⟨Set.mem_univ _, hz₀⟩`. Take `⟨A, hA, V, hV, hAV⟩` from `mem_nhds_prod_iff.mp hN`. Conclude with `⟨V, hV, M ω, hM ω, fun z hz k => hle (p, z) (hAV ⟨mem_of_mem_nhds hA, hz.1⟩) hz.2 ω k⟩`.

Establish `hdS : ∀ p ω, DifferentiableOn ℂ (fun z => ∑' k, F p z ω k) U` using `fun p ω => (series_step hU (fun k z => F p z ω k) (fun k => hF p ω k) (hser p ω)).1`. Establish `hmeas : ∀ p z, z ∈ U → AEStronglyMeasurable (fun ω => ∑' k, F p z ω k) μ` using `fun p z hz => aesm_of_real hU hball (fun z ω => ∑' k, F p z ω k) (hdS p) (hFm p) hz`. Establish `hint : ∀ p, ∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ g : Ω → ℝ, Integrable g μ ∧ ∀ z ∈ V ∩ U, ∀ ω, ‖∑' k, F p z ω k‖ ≤ g ω`. Introduce `p z₀ hz₀`. Take `⟨N, hN, M, g, hM, hg, hMg, hle⟩` from `hB (p, z₀) ⟨Set.mem_univ _, hz₀⟩`.

Take `⟨A, hA, V, hV, hAV⟩` from `mem_nhds_prod_iff.mp hN`. Use `⟨V, hV, g, hg, fun z hz ω => ?_⟩` and prove the remaining obligations. Conclude with `(tsum_of_norm_bounded (hM ω).hasSum (fun k => hle (p, z) (hAV ⟨mem_of_mem_nhds hA, hz.1⟩) hz.2 ω k)).trans (hMg ω)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `q hq`.

Take `⟨N, hN, M, g, hM, hg, hMg, hle⟩` from `hB q hq`. Establish `hS : ∀ q' ∈ (Set.univ ×ˢ U) ∩ N, ∀ ω, ‖∑' k, F q'.1 q'.2 ω k‖ ≤ g ω` using `fun q' hq' ω => (tsum_of_norm_bounded (hM ω).hasSum (fun k => hle q' hq'.2 hq'.1.2 ω k)).trans (hMg ω)`. Use `continuousWithinAt_of_dominated (bound := g) ?_ ?_ hg ?_` and prove the remaining obligations. Conclude with `Filter.eventually_of_mem self_mem_nhdsWithin (fun q' hq' => hmeas q'.1 q'.2 hq'.2)`. Conclude with `Filter.eventually_of_mem (inter_mem_nhdsWithin _ hN) (fun q' hq' => ae_of_all μ (hS q' hq'))`.

Use `ae_of_all μ fun ω => ?_` and prove the remaining obligations. Establish `hc : ContinuousOn (fun q' : P × ℂ => ∑' k, F q'.1 q'.2 ω k) ((Set.univ ×ˢ U) ∩ N)` using `continuousOn_tsum (fun k => (hFc ω k).mono Set.inter_subset_left) (hM ω) (fun k q' hq' => hle q' hq'.2 hq'.1.2 ω k)`. Conclude with `(continuousWithinAt_inter hN).mp (hc q ⟨hq, mem_of_mem_nhds hN⟩)`. Introduce `p z hz`. Conclude with `(((integral_step hU (fun z ω => ∑' k, F p z ω k) (hdS p) (fun z hz => hmeas p z hz) (hint p)).1 z hz).differentiableAt).differentiableWithinAt`.

Introduce `p z hz r`. Use `(iteratedDeriv_integral hU r (fun z ω => ∑' k, F p z ω k) (hdS p) (fun z hz => hmeas p z hz) (hint p) z hz).trans ?_` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `ω`. Conclude with `iteratedDeriv_series hU r (fun k z => F p z ω k) (fun k => hF p ω k) (hser p ω) z hz`.
-/
theorem holomorphic_mean (P Ω κ : Type) [TopologicalSpace P] [FirstCountableTopology P]
    [MeasurableSpace Ω] [Countable κ] (μ : Measure Ω) (U : Set ℂ)
    (hU : IsOpen U)
    (hball : ∀ z ∈ U, ∃ (t ρ : ℝ), 0 < ρ ∧ z ∈ Metric.ball (t : ℂ) ρ ∧ Metric.ball (t : ℂ) ρ ⊆ U)
    (F : P → ℂ → Ω → κ → ℂ) (hF : ∀ p ω k, DifferentiableOn ℂ (fun z => F p z ω k) U)
    (hFc : ∀ ω k, ContinuousOn (fun q : P × ℂ => F q.1 q.2 ω k) (Set.univ ×ˢ U))
    (hFm : ∀ p (t : ℝ), (t : ℂ) ∈ U → AEStronglyMeasurable (fun ω => ∑' k, F p t ω k) μ)
    (hB : ∀ q ∈ (Set.univ : Set P) ×ˢ U, ∃ N ∈ 𝓝 q, ∃ (M : Ω → κ → ℝ) (g : Ω → ℝ),
      (∀ ω, Summable (M ω)) ∧ Integrable g μ ∧ (∀ ω, ∑' k, M ω k ≤ g ω) ∧
      ∀ q' ∈ N, q'.2 ∈ U → ∀ ω k, ‖F q'.1 q'.2 ω k‖ ≤ M ω k) :
    ContinuousOn (fun q : P × ℂ => ∫ ω, ∑' k, F q.1 q.2 ω k ∂μ) (Set.univ ×ˢ U) ∧
      (∀ p, DifferentiableOn ℂ (fun z => ∫ ω, ∑' k, F p z ω k ∂μ) U) ∧
      ∀ p, ∀ z ∈ U, ∀ r : ℕ, iteratedDeriv r (fun z => ∫ ω, ∑' k, F p z ω k ∂μ) z =
        ∫ ω, ∑' k, iteratedDeriv r (fun z => F p z ω k) z ∂μ := by
  have hser : ∀ p ω, ∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ u : κ → ℝ, Summable u ∧
      ∀ z ∈ V ∩ U, ∀ k, ‖F p z ω k‖ ≤ u k := by
    intro p ω z₀ hz₀
    obtain ⟨N, hN, M, g, hM, hg, hMg, hle⟩ := hB (p, z₀) ⟨Set.mem_univ _, hz₀⟩
    obtain ⟨A, hA, V, hV, hAV⟩ := mem_nhds_prod_iff.mp hN
    exact ⟨V, hV, M ω, hM ω, fun z hz k => hle (p, z) (hAV ⟨mem_of_mem_nhds hA, hz.1⟩) hz.2 ω k⟩
  have hdS : ∀ p ω, DifferentiableOn ℂ (fun z => ∑' k, F p z ω k) U := fun p ω =>
    (series_step hU (fun k z => F p z ω k) (fun k => hF p ω k) (hser p ω)).1
  have hmeas : ∀ p z, z ∈ U → AEStronglyMeasurable (fun ω => ∑' k, F p z ω k) μ :=
    fun p z hz => aesm_of_real hU hball (fun z ω => ∑' k, F p z ω k) (hdS p) (hFm p) hz
  have hint : ∀ p, ∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ z ∈ V ∩ U, ∀ ω, ‖∑' k, F p z ω k‖ ≤ g ω := by
    intro p z₀ hz₀
    obtain ⟨N, hN, M, g, hM, hg, hMg, hle⟩ := hB (p, z₀) ⟨Set.mem_univ _, hz₀⟩
    obtain ⟨A, hA, V, hV, hAV⟩ := mem_nhds_prod_iff.mp hN
    refine ⟨V, hV, g, hg, fun z hz ω => ?_⟩
    exact (tsum_of_norm_bounded (hM ω).hasSum
      (fun k => hle (p, z) (hAV ⟨mem_of_mem_nhds hA, hz.1⟩) hz.2 ω k)).trans (hMg ω)
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨N, hN, M, g, hM, hg, hMg, hle⟩ := hB q hq
    have hS : ∀ q' ∈ (Set.univ ×ˢ U) ∩ N, ∀ ω, ‖∑' k, F q'.1 q'.2 ω k‖ ≤ g ω := fun q' hq' ω =>
      (tsum_of_norm_bounded (hM ω).hasSum (fun k => hle q' hq'.2 hq'.1.2 ω k)).trans (hMg ω)
    refine continuousWithinAt_of_dominated (bound := g) ?_ ?_ hg ?_
    · exact Filter.eventually_of_mem self_mem_nhdsWithin (fun q' hq' => hmeas q'.1 q'.2 hq'.2)
    · exact Filter.eventually_of_mem (inter_mem_nhdsWithin _ hN)
        (fun q' hq' => ae_of_all μ (hS q' hq'))
    · refine ae_of_all μ fun ω => ?_
      have hc : ContinuousOn (fun q' : P × ℂ => ∑' k, F q'.1 q'.2 ω k) ((Set.univ ×ˢ U) ∩ N) :=
        continuousOn_tsum (fun k => (hFc ω k).mono Set.inter_subset_left) (hM ω)
          (fun k q' hq' => hle q' hq'.2 hq'.1.2 ω k)
      exact (continuousWithinAt_inter hN).mp (hc q ⟨hq, mem_of_mem_nhds hN⟩)
  · intro p z hz
    exact (((integral_step hU (fun z ω => ∑' k, F p z ω k) (hdS p) (fun z hz => hmeas p z hz)
      (hint p)).1 z hz).differentiableAt).differentiableWithinAt
  · intro p z hz r
    refine (iteratedDeriv_integral hU r (fun z ω => ∑' k, F p z ω k) (hdS p)
      (fun z hz => hmeas p z hz) (hint p) z hz).trans ?_
    congr 1
    funext ω
    exact iteratedDeriv_series hU r (fun k z => F p z ω k) (fun k => hF p ω k) (hser p ω) z hz

end GlobalTheory.CompanionTheory.HolMean
