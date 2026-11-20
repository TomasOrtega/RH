import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.TChartSplit

noncomputable section

open scoped Topology
open Filter Set Metric GlobalTheory.Cont

namespace GlobalTheory.CompanionTheory.DivMult

/- English proof (translation)
Establish `hAn : AnalyticOnNhd ℂ A univ` using `fun z _ => hA.analyticAt z`. Establish `hnz : ¬∀ᶠ z in 𝓝 s₀, A z = 0`. Introduce `hev`. Take `⟨w, hw⟩` from `hne`. Use `hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ s₀) (hev.mono fun z hz => by simp [hz])` as an intermediate fact.

Conclude with `hw (by simpa using this (mem_univ w))`. Take `⟨k, g, hg, hg0, hev⟩` from `(hA.analyticAt s₀).exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnz`. Establish `hpos : 0 < ‖g s₀‖` using `norm_pos_iff.mpr hg0`. Establish `hcont : ∀ᶠ z in 𝓝 s₀, ‖g z - g s₀‖ < ‖g s₀‖ / 2`. Establish `h2 : ball (g s₀) (‖g s₀‖ / 2) ∈ 𝓝 (g s₀)` using `ball_mem_nhds _ (by positivity)`.

Use `filter_upwards [hg.continuousAt h2] with z hz`. Simplify `hz` using `[dist_eq_norm]`. Take `⟨r, hr, hball⟩` from `Metric.eventually_nhds_iff_ball.mp (hev.and (hcont.and hg.eventually_analyticAt))`. Use `⟨k, g, r, 2 / ‖g s₀‖, hr, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`.

Conclude with `(hball z hz).2.2.differentiableAt.differentiableWithinAt`. Introduce `z hz h0`. Establish `h1` using `(hball z hz).2.1`. Rewrite `h1` using `[h0, zero_sub, norm_neg]`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `z hz`. Simplify `(hball z hz).1` using `[smul_eq_mul]`. Introduce `z hz`. Establish `h1` using `(hball z hz).2.1`. Establish `hlow : ‖g s₀‖ / 2 ≤ ‖g z‖`.

Establish `h3` using `norm_sub_norm_le (g s₀) (g z)`. Rewrite `h3` using `[norm_sub_rev]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_factor {A : ℂ → ℂ} (hA : Differentiable ℂ A) (hne : ∃ z, A z ≠ 0) (s₀ : ℂ) :
    ∃ (k : ℕ) (u : ℂ → ℂ) (r M : ℝ), 0 < r ∧ DifferentiableOn ℂ u (ball s₀ r) ∧ (∀ s ∈ ball s₀ r, u s ≠ 0) ∧
      (∀ s ∈ ball s₀ r, A s = (s - s₀) ^ k * u s) ∧ ∀ s ∈ ball s₀ r, ‖(u s)⁻¹‖ ≤ M := by
  have hAn : AnalyticOnNhd ℂ A univ := fun z _ => hA.analyticAt z
  have hnz : ¬∀ᶠ z in 𝓝 s₀, A z = 0 := by
    intro hev
    obtain ⟨w, hw⟩ := hne
    have := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ s₀)
      (hev.mono fun z hz => by simp [hz])
    exact hw (by simpa using this (mem_univ w))
  obtain ⟨k, g, hg, hg0, hev⟩ := (hA.analyticAt s₀).exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnz
  have hpos : 0 < ‖g s₀‖ := norm_pos_iff.mpr hg0
  have hcont : ∀ᶠ z in 𝓝 s₀, ‖g z - g s₀‖ < ‖g s₀‖ / 2 := by
    have h2 : ball (g s₀) (‖g s₀‖ / 2) ∈ 𝓝 (g s₀) := ball_mem_nhds _ (by positivity)
    filter_upwards [hg.continuousAt h2] with z hz
    simpa [dist_eq_norm] using hz
  obtain ⟨r, hr, hball⟩ :=
    Metric.eventually_nhds_iff_ball.mp (hev.and (hcont.and hg.eventually_analyticAt))
  refine ⟨k, g, r, 2 / ‖g s₀‖, hr, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hball z hz).2.2.differentiableAt.differentiableWithinAt
  · intro z hz h0
    have h1 := (hball z hz).2.1
    rw [h0, zero_sub, norm_neg] at h1
    linarith
  · intro z hz
    simpa [smul_eq_mul] using (hball z hz).1
  · intro z hz
    have h1 := (hball z hz).2.1
    have hlow : ‖g s₀‖ / 2 ≤ ‖g z‖ := by
      have h3 := norm_sub_norm_le (g s₀) (g z)
      rw [norm_sub_rev] at h3
      linarith
    calc ‖(g z)⁻¹‖ = ‖g z‖⁻¹ := norm_inv _
      _ ≤ (‖g s₀‖ / 2)⁻¹ := inv_anti₀ (by positivity) hlow
      _ = 2 / ‖g s₀‖ := inv_div _ _

def glue (h F A : ℂ → ℂ) (R : ℝ) (z : ℂ) : ℂ := if R < z.re then h z else F z / A z

variable {h F A : ℂ → ℂ} {R : ℝ}

/- English proof (translation)
Unfold `glue`. Use `split_ifs with c`. Rewrite using `[he z c, mul_div_cancel_left₀ _ hz]`. Both sides reduce to the same expression.
-/
theorem glue_eq (he : ∀ z : ℂ, R < z.re → F z = A z * h z) {z : ℂ} (hz : A z ≠ 0) : glue h F A R z = F z / A z := by
  unfold glue
  split_ifs with c
  · rw [he z c, mul_div_cancel_left₀ _ hz]
  · rfl

/- English proof (translation)
Establish `hAn : AnalyticOnNhd ℂ A univ` using `fun z _ => hA.analyticAt z`. Break down `(hA.analyticAt s).eventually_eq_zero_or_eventually_ne_zero with hev | hev` into its components or cases. It suffices to derive a contradiction. Take `⟨w, hw⟩` from `hne`. Use `hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ s) (hev.mono fun z hz => by simp [hz])` as an intermediate fact.

Conclude with `hw (by simpa using this (mem_univ w))`. Use `filter_upwards [hev] with z hz using glue_eq he hz`.
-/
theorem glue_eventuallyEq (hA : Differentiable ℂ A) (hne : ∃ z, A z ≠ 0) (he : ∀ z : ℂ, R < z.re → F z = A z * h z) (s : ℂ) :
    glue h F A R =ᶠ[𝓝[≠] s] fun z => F z / A z := by
  have hAn : AnalyticOnNhd ℂ A univ := fun z _ => hA.analyticAt z
  rcases (hA.analyticAt s).eventually_eq_zero_or_eventually_ne_zero with hev | hev
  · exfalso
    obtain ⟨w, hw⟩ := hne
    have := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ s)
      (hev.mono fun z hz => by simp [hz])
    exact hw (by simpa using this (mem_univ w))
  · filter_upwards [hev] with z hz using glue_eq he hz

/- English proof (translation)
Use `⟨isRightDomain_univ, fun s _ => ?_, ⟨R, fun z hz => ?_⟩⟩` and prove the remaining obligations. Establish `hm : MeromorphicAt (fun z => F z / A z) s` using `(hF.analyticAt s).meromorphicAt.div (hA.analyticAt s).meromorphicAt`. Conclude with `hm.congr (glue_eventuallyEq hA hne he s).symm`. Establish `hz' : R < z.re` using `hz`. Simplify using `[glue, hz']`.
-/
theorem isMerExt_glue (hA : Differentiable ℂ A) (hne : ∃ z, A z ≠ 0) (hF : Differentiable ℂ F)
    (he : ∀ z : ℂ, R < z.re → F z = A z * h z) : IsMerExt h univ (glue h F A R) := by
  refine ⟨isRightDomain_univ, fun s _ => ?_, ⟨R, fun z hz => ?_⟩⟩
  · have hm : MeromorphicAt (fun z => F z / A z) s :=
      (hF.analyticAt s).meromorphicAt.div (hA.analyticAt s).meromorphicAt
    exact hm.congr (glue_eventuallyEq hA hne he s).symm
  · have hz' : R < z.re := hz
    simp [glue, hz']

/- English proof (translation)
Establish `hM` using `isMerExt_glue hA hne hF he`. Establish `hE : IsExtAt h s (glue h F A R)` using `hM.isExtAt (mem_univ s)`. Establish `hcont : ContinuousAt (fun z => F z / A z) s` using `hF.continuous.continuousAt.div hA.continuous.continuousAt hs`. Establish `ht : Tendsto (glue h F A R) (𝓝[≠] s) (𝓝 (F s / A s))` using `Tendsto.congr' (glue_eventuallyEq hA hne he s).symm (hcont.tendsto.mono_left nhdsWithin_le_nhds)`. Conclude with `(hE.holValueAt_iff.mpr ht).valueAt.cont_eq`.
-/
theorem cont_eq_div (hA : Differentiable ℂ A) (hne : ∃ z, A z ≠ 0) (hF : Differentiable ℂ F)
    (he : ∀ z : ℂ, R < z.re → F z = A z * h z) {s : ℂ} (hs : A s ≠ 0) : cont h s = F s / A s := by
  have hM := isMerExt_glue hA hne hF he
  have hE : IsExtAt h s (glue h F A R) := hM.isExtAt (mem_univ s)
  have hcont : ContinuousAt (fun z => F z / A z) s :=
    hF.continuous.continuousAt.div hA.continuous.continuousAt hs
  have ht : Tendsto (glue h F A R) (𝓝[≠] s) (𝓝 (F s / A s)) :=
    Tendsto.congr' (glue_eventuallyEq hA hne he s).symm (hcont.tendsto.mono_left nhdsWithin_le_nhds)
  exact (hE.holValueAt_iff.mpr ht).valueAt.cont_eq

/- English proof (translation)
Unfold `ResidueKilled.Tr.Div`. Introduce `D T e H A R hA hne hH hHc hmul hbd`. Unfold `GlobalTheory.EisCont.ContMod GlobalTheory.Cont.Continues`. Use `⟨fun g => ⟨_, isMerExt_glue hA hne (hH g) (fun z hz => hmul z hz g)⟩, fun s₀ => ?_⟩` and prove the remaining obligations. Take `⟨k, u, r, M, hr, hu, hu0, hfac, hM⟩` from `exists_factor hA hne s₀`.

Take `⟨C, N, hCN⟩` from `hbd (‖s₀‖ + r)`. Establish `hu1 : ContinuousOn (fun x : ℂ × _ => u x.1) (ball s₀ r ×ˢ (univ : Set (Formalism.L2.Theta.GA D T)))` using `hu.continuousOn.comp continuous_fst.continuousOn (fun x hx => hx.1)`. Unfold `GlobalTheory.EisCont.RegAt`. Use `⟨k, r, fun s g => H s g * (u s)⁻¹, hr, ?_, ?_, ?_, C * M, N, ?_⟩` and prove the remaining obligations. Introduce `s hs hss g`.

Establish `hAs : A s = (s - s₀) ^ k * u s` using `hfac s hs`. Establish `hus : u s ≠ 0` using `hu0 s hs`. Establish `hpow : (s - s₀) ^ k ≠ 0` using `pow_ne_zero _ (sub_ne_zero.mpr hss)`. Establish `hA0 : A s ≠ 0` using `by rw [hAs]; exact mul_ne_zero hpow hus`. Use `show H s g * (u s)⁻¹ = (s - s₀) ^ k * cont (fun z => e z g) s`.

Rewrite using `[cont_eq_div hA hne (hH g) (fun z hz => hmul z hz g) hA0, hAs]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`. Introduce `g`. Conclude with `(hH g).differentiableOn.mul (hu.inv hu0)`.

Conclude with `hHc.continuousOn.mul (hu1.inv₀ (fun x hx => hu0 x.1 hx.1))`. Introduce `s hs g`. Establish `hs1 : ‖s - s₀‖ < r` using `by simpa [dist_eq_norm] using hs`. Establish `hs2` using `norm_sub_norm_le s s₀`. Establish `hsr : ‖s‖ ≤ ‖s₀‖ + r` using `by linarith`.

Establish `hH1` using `hCN s hsr g`. Establish `hM1` using `hM s hs`. Use `show ‖H s g * (u s)⁻¹‖ ≤ C * M * GlobalTheory.Grow.height T g ^ N`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem div_multiplier : ResidueKilled.Tr.Div := by
  unfold ResidueKilled.Tr.Div
  intro D T e H A R hA hne hH hHc hmul hbd
  unfold GlobalTheory.EisCont.ContMod GlobalTheory.Cont.Continues
  refine ⟨fun g => ⟨_, isMerExt_glue hA hne (hH g) (fun z hz => hmul z hz g)⟩, fun s₀ => ?_⟩
  obtain ⟨k, u, r, M, hr, hu, hu0, hfac, hM⟩ := exists_factor hA hne s₀
  obtain ⟨C, N, hCN⟩ := hbd (‖s₀‖ + r)
  have hu1 : ContinuousOn (fun x : ℂ × _ => u x.1) (ball s₀ r ×ˢ (univ : Set (Formalism.L2.Theta.GA D T))) :=
    hu.continuousOn.comp continuous_fst.continuousOn (fun x hx => hx.1)
  unfold GlobalTheory.EisCont.RegAt
  refine ⟨k, r, fun s g => H s g * (u s)⁻¹, hr, ?_, ?_, ?_, C * M, N, ?_⟩
  · intro s hs hss g
    have hAs : A s = (s - s₀) ^ k * u s := hfac s hs
    have hus : u s ≠ 0 := hu0 s hs
    have hpow : (s - s₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hss)
    have hA0 : A s ≠ 0 := by rw [hAs]; exact mul_ne_zero hpow hus
    show H s g * (u s)⁻¹ = (s - s₀) ^ k * cont (fun z => e z g) s
    rw [cont_eq_div hA hne (hH g) (fun z hz => hmul z hz g) hA0, hAs]
    field_simp
    try ring
  · intro g
    exact (hH g).differentiableOn.mul (hu.inv hu0)
  · exact hHc.continuousOn.mul (hu1.inv₀ (fun x hx => hu0 x.1 hx.1))
  · intro s hs g
    have hs1 : ‖s - s₀‖ < r := by simpa [dist_eq_norm] using hs
    have hs2 := norm_sub_norm_le s s₀
    have hsr : ‖s‖ ≤ ‖s₀‖ + r := by linarith
    have hH1 := hCN s hsr g
    have hM1 := hM s hs
    show ‖H s g * (u s)⁻¹‖ ≤ C * M * GlobalTheory.Grow.height T g ^ N
    calc ‖H s g * (u s)⁻¹‖ = ‖H s g‖ * ‖(u s)⁻¹‖ := norm_mul _ _
      _ ≤ (C * GlobalTheory.Grow.height T g ^ N) * M := mul_le_mul hH1 hM1 (norm_nonneg _) (le_trans (norm_nonneg _) hH1)
      _ = C * M * GlobalTheory.Grow.height T g ^ N := by ring

end GlobalTheory.CompanionTheory.DivMult

end
