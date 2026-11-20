import Mathlib

open Topology Filter

namespace GlobalTheory.CompanionTheory.HolFamily

/- English proof (translation)
Introduce `G _ U E hU hd hc z hz j`. Take `⟨R, hR, hball⟩` from `Metric.isOpen_iff.1 hU z hz`. Establish `hr : 0 < R / 2` using `by positivity`. Establish `hcl : Metric.closedBall z (R / 2) ⊆ U` using `(Metric.closedBall_subset_ball (by linarith)).trans hball`. Rewrite using `[continuous_iff_continuousAt]`.

Introduce `g0`. Rewrite using `[Metric.continuousAt_iff']`. Introduce `ε hε`. Establish `hfac : (0 : ℝ) < (j.factorial : ℝ)` using `by exact_mod_cast j.factorial_pos`. Establish `hrj : 0 < (R / 2) ^ j` using `pow_pos hr j`.

Take `⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε * (R / 2) ^ j / (2 * (j.factorial : ℝ))` from `⟨_, rfl⟩`. Establish `hδ : 0 < δ` using `by rw [hδdef]; positivity`. Establish `htube : ∀ᶠ g in 𝓝 g0, ∀ w ∈ Metric.sphere z (R / 2), ‖E w g - E w g0‖ < δ`. Use `(isCompact_sphere z (R / 2)).eventually_forall_of_forall_eventually (P := fun g w => ‖E w g - E w g0‖ < δ) ?_` and prove the remaining obligations. Introduce `w hw`.

Establish `hwU : w ∈ U` using `hcl (Metric.sphere_subset_closedBall hw)`. Establish `hcont : ContinuousAt (fun y : ℂ × G => E y.1 y.2) (w, g0)` using `hc.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hwU, trivial⟩)`. Establish `hA : ContinuousAt (fun p : G × ℂ => E p.2 p.1) (g0, w)` using `ContinuousAt.comp (f := fun p : G × ℂ => (p.2, p.1)) (g := fun y : ℂ × G => E y.1 y.2) hcont continuous_swap.continuousAt`. Establish `hB : ContinuousAt (fun p : G × ℂ => E p.2 g0) (g0, w)` using `ContinuousAt.comp (f := fun p : G × ℂ => (p.2, g0)) (g := fun y : ℂ × G => E y.1 y.2) hcont (by fun_prop)`. Establish `hN : ContinuousAt (fun p : G × ℂ => ‖E p.2 p.1 - E p.2 g0‖) (g0, w)` using `(hA.sub hB).norm`.

Establish `hlt : ‖E w g0 - E w g0‖ < δ` using `by simpa using hδ`. Conclude with `hN.eventually_lt continuousAt_const hlt`. Use `filter_upwards [htube] with g hg`. Establish `hzn : U ∈ 𝓝 z` using `hU.mem_nhds hz`. Establish `h1 : ContDiffAt ℂ j (E · g) z` using `((hd g).analyticAt hzn).contDiffAt`.

Establish `h2 : ContDiffAt ℂ j (E · g0) z` using `((hd g0).analyticAt hzn).contDiffAt`. Rewrite using `[dist_eq_norm, ← iteratedDeriv_fun_sub h1 h2]`. Establish `hdc : DiffContOnCl ℂ (fun x => E x g - E x g0) (Metric.ball z (R / 2))` using `((hd g).sub (hd g0)).diffContOnCl_ball hcl`. Establish `hb` using `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (C := δ) j hr hdc (fun w hw => (hg w hw).le)`. Use `hb.trans_lt ?_` and prove the remaining obligations.

Establish `: (j.factorial : ℝ) * δ / (R / 2) ^ j = ε / 2`. Rewrite using `[hδdef]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem continuous_iteratedDeriv_family :
    ∀ {G : Type} [TopologicalSpace G] (U : Set ℂ) (Ê : ℂ → G → ℂ), IsOpen U →
      (∀ g, DifferentiableOn ℂ (Ê · g) U) →
      ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ) →
      ∀ z ∈ U, ∀ j : ℕ, Continuous fun g => iteratedDeriv j (Ê · g) z := by
  intro G _ U E hU hd hc z hz j
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 hU z hz
  have hr : 0 < R / 2 := by positivity
  have hcl : Metric.closedBall z (R / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  rw [continuous_iff_continuousAt]
  intro g0
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hfac : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast j.factorial_pos
  have hrj : 0 < (R / 2) ^ j := pow_pos hr j
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε * (R / 2) ^ j / (2 * (j.factorial : ℝ)) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have htube : ∀ᶠ g in 𝓝 g0, ∀ w ∈ Metric.sphere z (R / 2), ‖E w g - E w g0‖ < δ := by
    refine (isCompact_sphere z (R / 2)).eventually_forall_of_forall_eventually
      (P := fun g w => ‖E w g - E w g0‖ < δ) ?_
    intro w hw
    have hwU : w ∈ U := hcl (Metric.sphere_subset_closedBall hw)
    have hcont : ContinuousAt (fun y : ℂ × G => E y.1 y.2) (w, g0) :=
      hc.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hwU, trivial⟩)
    have hA : ContinuousAt (fun p : G × ℂ => E p.2 p.1) (g0, w) :=
      ContinuousAt.comp (f := fun p : G × ℂ => (p.2, p.1))
        (g := fun y : ℂ × G => E y.1 y.2) hcont continuous_swap.continuousAt
    have hB : ContinuousAt (fun p : G × ℂ => E p.2 g0) (g0, w) :=
      ContinuousAt.comp (f := fun p : G × ℂ => (p.2, g0))
        (g := fun y : ℂ × G => E y.1 y.2) hcont (by fun_prop)
    have hN : ContinuousAt (fun p : G × ℂ => ‖E p.2 p.1 - E p.2 g0‖) (g0, w) := (hA.sub hB).norm
    have hlt : ‖E w g0 - E w g0‖ < δ := by simpa using hδ
    exact hN.eventually_lt continuousAt_const hlt
  filter_upwards [htube] with g hg
  have hzn : U ∈ 𝓝 z := hU.mem_nhds hz
  have h1 : ContDiffAt ℂ j (E · g) z := ((hd g).analyticAt hzn).contDiffAt
  have h2 : ContDiffAt ℂ j (E · g0) z := ((hd g0).analyticAt hzn).contDiffAt
  rw [dist_eq_norm, ← iteratedDeriv_fun_sub h1 h2]
  have hdc : DiffContOnCl ℂ (fun x => E x g - E x g0) (Metric.ball z (R / 2)) :=
    ((hd g).sub (hd g0)).diffContOnCl_ball hcl
  have hb := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (C := δ) j hr hdc
    (fun w hw => (hg w hw).le)
  refine hb.trans_lt ?_
  have : (j.factorial : ℝ) * δ / (R / 2) ^ j = ε / 2 := by
    rw [hδdef]; field_simp
  rw [this]
  linarith

end GlobalTheory.CompanionTheory.HolFamily
