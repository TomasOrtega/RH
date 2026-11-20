import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockFormApply
open MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Establish `hF : Continuous (fun p : ℝ × V => (M p.1 p.2 p.2).re)` using `Complex.continuous_re.comp hc`. Establish `hscale : ∀ t (c : ℝ) (u : V), (M t (c • u) (c • u)).re = c ^ 2 * (M t u u).re`. Introduce `t c u`. Simplify using `only [map_smul, LinearMap.smul_apply, Complex.smul_re, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `key : ∀ (ε : ℝ) (t : ℝ), (∀ u ∈ Metric.sphere (0:V) 1, (M t u u).re < -ε) → ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2)`. Introduce `ε t ht x`. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules.

Establish `hn : ‖x‖ ≠ 0` using `norm_ne_zero_iff.mpr hx`. Establish `hu : ‖x‖⁻¹ • x ∈ Metric.sphere (0:V) 1`. Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]`. Establish `h1` using `ht _ hu`. Establish `hx' : x = ‖x‖ • (‖x‖⁻¹ • x)` using `by rw [smul_smul, mul_inv_cancel₀ hn, one_smul]`.

Establish `h2 : (M t x x).re = ‖x‖ ^ 2 * (M t (‖x‖⁻¹ • x) (‖x‖⁻¹ • x)).re` using `by conv_lhs => rw [hx']`. Conclude with `hscale t _ _`. Rewrite using `[h2]`. Establish `hp : 0 ≤ ‖x‖ ^ 2` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hS : IsCompact (Metric.sphere (0:V) 1)` using `isCompact_sphere 0 1`. Break down `(Metric.sphere (0:V) 1).eq_empty_or_nonempty with hE | hNE` into its components or cases. Use `⟨1, one_pos, Filter.Eventually.of_forall fun t => key 1 t ?_⟩` and prove the remaining obligations. Introduce `u hu`. Rewrite `hu` using `[hE]`.

Conclude with `absurd hu (Set.notMem_empty _)`. Establish `hcont0 : ContinuousOn (fun u : V => (M t₀ u u).re) (Metric.sphere 0 1)` using `(hF.comp (Continuous.prodMk_right t₀)).continuousOn`. Take `⟨u₀, hu₀, hmax⟩` from `hS.exists_isMaxOn hNE hcont0`. Establish `hu₀0 : u₀ ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at hu₀`. Establish `hm : (M t₀ u₀ u₀).re < 0` using `hneg t₀ u₀ hu₀0`. Use `⟨-(M t₀ u₀ u₀).re / 2, by linarith, ?_⟩` and prove the remaining obligations. Establish `hev : ∀ᶠ t in nhds t₀, ∀ u ∈ Metric.sphere (0:V) 1, (M t u u).re < -(-(M t₀ u₀ u₀).re / 2)`. Apply `hS.eventually_forall_of_forall_eventually` to reduce the goal to its premises.

Introduce `u hu`. Establish `hlt : (M t₀ u u).re < -(-(M t₀ u₀ u₀).re / 2)`. Use `hmax hu` as an intermediate fact. Simplify using `only [Set.mem_setOf_eq] at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `hF.continuousAt.eventually_lt continuousAt_const hlt`. Conclude with `hev.mono fun t ht => key _ t ht`.
-/
theorem quadForm_eventually_unif_negDef {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ)
    (hc : Continuous (fun p : ℝ × V => M p.1 p.2 p.2))
    (hneg : ∀ t v, v ≠ 0 → (M t v v).re < 0) (t₀ : ℝ) :
    ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2) := by
  have hF : Continuous (fun p : ℝ × V => (M p.1 p.2 p.2).re) := Complex.continuous_re.comp hc
  have hscale : ∀ t (c : ℝ) (u : V), (M t (c • u) (c • u)).re = c ^ 2 * (M t u u).re := by
    intro t c u
    simp only [map_smul, LinearMap.smul_apply, Complex.smul_re, smul_eq_mul]
    ring
  have key : ∀ (ε : ℝ) (t : ℝ), (∀ u ∈ Metric.sphere (0:V) 1, (M t u u).re < -ε) →
      ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2) := by
    intro ε t ht x
    by_cases hx : x = 0
    · subst hx; simp
    · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hu : ‖x‖⁻¹ • x ∈ Metric.sphere (0:V) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
      have h1 := ht _ hu
      have hx' : x = ‖x‖ • (‖x‖⁻¹ • x) := by rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
      have h2 : (M t x x).re = ‖x‖ ^ 2 * (M t (‖x‖⁻¹ • x) (‖x‖⁻¹ • x)).re := by
        conv_lhs => rw [hx']
        exact hscale t _ _
      rw [h2]
      have hp : 0 ≤ ‖x‖ ^ 2 := by positivity
      nlinarith
  have hS : IsCompact (Metric.sphere (0:V) 1) := isCompact_sphere 0 1
  rcases (Metric.sphere (0:V) 1).eq_empty_or_nonempty with hE | hNE
  · refine ⟨1, one_pos, Filter.Eventually.of_forall fun t => key 1 t ?_⟩
    intro u hu
    rw [hE] at hu
    exact absurd hu (Set.notMem_empty _)
  · have hcont0 : ContinuousOn (fun u : V => (M t₀ u u).re) (Metric.sphere 0 1) :=
      (hF.comp (Continuous.prodMk_right t₀)).continuousOn
    obtain ⟨u₀, hu₀, hmax⟩ := hS.exists_isMaxOn hNE hcont0
    have hu₀0 : u₀ ≠ 0 := by
      rintro rfl
      simp at hu₀
    have hm : (M t₀ u₀ u₀).re < 0 := hneg t₀ u₀ hu₀0
    refine ⟨-(M t₀ u₀ u₀).re / 2, by linarith, ?_⟩
    have hev : ∀ᶠ t in nhds t₀, ∀ u ∈ Metric.sphere (0:V) 1,
        (M t u u).re < -(-(M t₀ u₀ u₀).re / 2) := by
      apply hS.eventually_forall_of_forall_eventually
      intro u hu
      have hlt : (M t₀ u u).re < -(-(M t₀ u₀ u₀).re / 2) := by
        have := hmax hu
        simp only [Set.mem_setOf_eq] at this
        linarith
      exact hF.continuousAt.eventually_lt continuousAt_const hlt
    exact hev.mono fun t ht => key _ t ht

/- English proof (translation)
Introduce `M hc hneg t₀` and use `quadForm_eventually_unif_negDef M hc hneg t₀`.
-/
theorem quadForm_unif_target : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ),
    Continuous (fun p : ℝ × V => M p.1 p.2 p.2) → (∀ t v, v ≠ 0 → (M t v v).re < 0) →
    ∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2) :=
  fun M hc hneg t₀ => quadForm_eventually_unif_negDef M hc hneg t₀

end GlobalTheory
