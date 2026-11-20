import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected

noncomputable section

open Set Filter Topology GlobalTheory.Cont

namespace PositivityTheory.SiegelWeilFormula.Atop

/- English proof (translation)
Use `set S := p.roots.toFinset with hS`. Establish `hroot : ∀ z, p.eval z = 0 → z ∈ S` using `fun z hz => by`. Rewrite using `[hS, Multiset.mem_toFinset, Polynomial.mem_roots hp]`. Conclude with `hz`. Use `set σ₁ : ℝ := |t| + ∑ a ∈ S, |a.re| with hσ₁`.

Establish `hright : ∀ z : ℂ, σ₁ < z.re → t < z.re ∧ p.eval z ≠ 0`. Introduce `z hz`. Establish `h0 : 0 ≤ ∑ a ∈ S, |a.re|` using `Finset.sum_nonneg fun a _ => abs_nonneg _`. Establish `ht` using `le_abs_self t`. Use `⟨by linarith, fun h0' => ?_⟩` and prove the remaining obligations.

Establish `hz' : |z.re| ≤ ∑ a ∈ S, |a.re|` using `Finset.single_le_sum (f := fun a : ℂ => |a.re|) (fun a _ => abs_nonneg _) (hroot z h0')`. Use `le_abs_self z.re` as an intermediate fact. Combine the linear relations using `[abs_nonneg t]`. Use `set Q : ℂ → G → ℂ := fun z g => Ê z g / p.eval z with hQ`. Establish `hpan : ∀ z, AnalyticAt ℂ (fun z => p.eval z) z` using `fun z => p.differentiable.analyticAt z`.

Establish `hmer : ∀ g, IsMerExt (h · g) U (Q · g)`. Introduce `g`. Use `⟨hR, fun z hz => ?_, ⟨σ₁, fun z hz => ?_⟩⟩` and prove the remaining obligations. Conclude with `(((hd g).analyticAt (hU.mem_nhds hz)).meromorphicAt).div (hpan z).meromorphicAt`. Take `⟨h1, h2⟩` from `hright z hz show Ê z g / p.eval z = h z g`.

Rewrite using `[he z h1 g, mul_div_cancel_left₀ _ h2]`. Establish `hext : ∀ g z, z ∈ U → IsExtAt (h · g) z (Q · g)` using `fun g z hz => ⟨U, hz, hmer g⟩`. Establish `htend : ∀ g, Tendsto (Q · g) (𝓝[≠] s₀) (𝓝 (v g))` using `fun g => (hext g s₀ hs).holValueAt_iff.1 (hv g)`. Establish `hnhds : U ∩ ((((S.erase s₀ : Finset ℂ) : Set ℂ))ᶜ) ∈ 𝓝 s₀` using `Filter.inter_mem (hU.mem_nhds hs) ((Finset.finite_toSet _).isClosed.isOpen_compl.mem_nhds (by simp))`. Take `⟨r₁, hr₁, hball⟩` from `Metric.mem_nhds_iff.1 hnhds`.

Establish `hbU : ∀ z ∈ Metric.ball s₀ r₁, z ∈ U` using `fun z hz => (hball hz).1`. Establish `hbp : ∀ z ∈ Metric.ball s₀ r₁, z ≠ s₀ → p.eval z ≠ 0` using `fun z hz hne h0 => (hball hz).2 (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hne, hroot z h0⟩))`. Establish `hQd : ∀ g, ∀ z ∈ Metric.ball s₀ r₁, z ≠ s₀ → DifferentiableAt ℂ (Q · g) z` using `fun g z hz hne => ((hd g).differentiableAt (hU.mem_nhds (hbU z hz))).div (p.differentiable z) (hbp z hz hne)`. Use `set F : ℂ → G → ℂ := fun z g => Function.update (fun w => Q w g) s₀ (v g) z with hF`. Establish `hFQ : ∀ g z, z ≠ s₀ → F z g = Q z g` using `fun g z hne => by show Function.update (fun w => Q w g) s₀ (v g) z = Q z g`.

Conclude with `Function.update_of_ne hne _ _`. Establish `hFs : ∀ g, F s₀ g = v g` using `fun g => by show Function.update (fun w => Q w g) s₀ (v g) s₀ = v g`. Conclude with `Function.update_self _ _ _`. Establish `hFd : ∀ g, DifferentiableOn ℂ (F · g) (Metric.ball s₀ r₁)`. Introduce `g`.

Use `(Complex.differentiableOn_compl_singleton_and_continuousAt_iff (Metric.ball_mem_nhds s₀ hr₁)).1 ⟨?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Establish `hne : z ≠ s₀` using `fun e => hz.2 (Set.mem_singleton_iff.2 e)`. Use `((hQd g z hz.1 hne).congr_of_eventuallyEq ?_).differentiableWithinAt` and prove the remaining obligations. Use `filter_upwards [isOpen_ne.mem_nhds hne] with w hw`.

Conclude with `hFQ g w hw`. Use `show ContinuousAt (Function.update (fun w => Q w g) s₀ (v g)) s₀`. Conclude with `continuousAt_update_same.2 (htend g)`. Establish `hHol : ∀ g, ∀ z ∈ Metric.ball s₀ r₁, HolValueAt (h · g) z (F z g)`. Introduce `g z hz`.

Distinguish the cases in `hne : z = s₀`. Substitute `hne` using the available equality. Rewrite using `[hFs]`. Conclude with `hv g`. Rewrite using `[hFQ g z hne]`.

Conclude with `(hext g z (hbU z hz)).holValueAt_iff.2 ((hQd g z hz hne).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)`. Use `set ρ : ℝ := 3 * r₁ / 4 with hρ`. Establish `hρ0 : ρ ≠ 0` using `by rw [hρ]; positivity`. Use `set K : ℂ × G → ℝ → ℂ := fun y θ => (circleMap 0 ρ θ * Complex.I) • ((circleMap s₀ ρ θ - y.1)⁻¹ • (Ê (circleMap s₀ ρ θ) y.2 / p.eval (circleMap s₀ ρ θ))) with hK`. Establish `hcirc : ∀ θ, circleMap s₀ ρ θ ∈ Metric.ball s₀ r₁` using `fun θ => by`.

Rewrite using `[Metric.mem_ball, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_pos (by rw [hρ]; positivity)]`. Rewrite using `[hρ]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hrep : ∀ y ∈ Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G), F y.1 y.2 = (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, K y θ`. Introduce and unpack `⟨z, g⟩ ⟨hz, -⟩`.

Establish `hzρ : z ∈ Metric.ball s₀ ρ` using `Metric.ball_subset_ball (by rw [hρ]; linarith) hz`. Establish `hcl : Metric.closedBall s₀ ρ ⊆ Metric.ball s₀ r₁` using `Metric.closedBall_subset_ball (by rw [hρ]; linarith)`. Rewrite using `[← Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable (s := ∅) Set.countable_empty hzρ ((hFd g).continuousOn.mono hcl) (fun x hx => (hFd g).differentiableAt (Metric.isOpen_ball.mem_nhds (hcl (Metric.ball_subset_closedBall hx.1))))]`. Use `congr 1`. Unfold `circleIntegral`.

Use `intervalIntegral.integral_congr fun θ _ => ?_` and prove the remaining obligations. Simplify using `only [hK, deriv_circleMap]`. Rewrite using `[hFQ g _ (circleMap_ne_center hρ0)]`. Establish `hcont : ContinuousOn (fun y : ℂ × G => (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, K y θ) (Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G))`. Rewrite using `[continuousOn_iff_continuous_restrict]`.

Use `show Continuous fun x : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) => (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, K x.1 θ`. It suffices to establish `hI : Continuous fun x : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) => ∫ θ in (0 : ℝ)..2 * Real.pi, K x.1 θ from (continuous_const : Continuous fun _ : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) => (2 * Real.pi * Complex.I : ℂ)⁻¹).smul hI`. Use `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun (x : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G))) θ => K x.1 θ) ?_ 0 (2 * Real.pi)` and prove the remaining obligations. Use `show Continuous fun q : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) × ℝ => (circleMap 0 ρ q.2 * Complex.I) • ((circleMap s₀ ρ q.2 - q.1.1.1)⁻¹ • (Ê (circleMap s₀ ρ q.2) q.1.1.2 / p.eval (circleMap s₀ ρ q.2)))`. Establish `hc1 : Continuous fun q : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) × ℝ => circleMap s₀ ρ q.2` using `(continuous_circleMap s₀ ρ).comp continuous_snd`.

Establish `hE : Continuous fun q : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) × ℝ => Ê (circleMap s₀ ρ q.2) q.1.1.2` using `hc.comp_continuous (f := fun q : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) × ℝ => (circleMap s₀ ρ q.2, q.1.1.2)) (hc1.prodMk (continuous_snd.comp (continuous_subtype_val.comp continuous_fst))) (fun q => ⟨hbU _ (hcirc q.2), Set.mem_univ _⟩)`. Establish `hP : Continuous fun q : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) × ℝ => p.eval (circleMap s₀ ρ q.2)` using `p.continuous.comp hc1`. Establish `hz : Continuous fun q : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) × ℝ => q.1.1.1` using `continuous_fst.comp (continuous_subtype_val.comp continuous_fst)`. Use `((continuous_circleMap 0 ρ).comp continuous_snd |>.mul continuous_const).smul ?_` and prove the remaining obligations. Use `((hc1.sub hz).inv₀ fun q => ?_).smul (hE.div hP fun q => ?_)` and prove the remaining obligations.

Establish `hq : q.1.1.1 ∈ Metric.ball s₀ ρ` using `Metric.ball_subset_ball (by rw [hρ]; linarith) q.1.2.1`. Conclude with `sub_ne_zero.2 (circleMap_ne_mem_ball hq q.2)`. Conclude with `hbp _ (hcirc q.2) (circleMap_ne_center hρ0)`. Use `⟨r₁ / 2, F, by positivity, hcont.congr hrep, fun g => (hFd g).mono (Metric.ball_subset_ball (by linarith)), hFs, fun g z hz => hHol g z (Metric.ball_subset_ball (by linarith) hz)⟩` and prove the remaining obligations.
-/
theorem vacData_of {G : Type} [TopologicalSpace G] (h : ℂ → G → ℂ) (s₀ : ℂ) (v : G → ℂ)
    (U : Set ℂ) (p : Polynomial ℂ) (Ê : ℂ → G → ℂ) (t : ℝ) (hU : IsOpen U) (hR : IsRightDomain U) (hs : s₀ ∈ U)
    (hp : p ≠ 0) (hd : ∀ g, DifferentiableOn ℂ (Ê · g) U)
    (hc : ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ))
    (he : ∀ z : ℂ, t < z.re → ∀ g, Ê z g = p.eval z * h z g) (hv : ∀ g, HolValueAt (h · g) s₀ (v g)) :
    ∃ (r : ℝ) (F : ℂ → G → ℂ), 0 < r ∧ ContinuousOn (fun y : ℂ × G => F y.1 y.2) (Metric.ball s₀ r ×ˢ Set.univ) ∧
      (∀ g, DifferentiableOn ℂ (F · g) (Metric.ball s₀ r)) ∧ (∀ g, F s₀ g = v g) ∧
      ∀ g, ∀ z ∈ Metric.ball s₀ r, HolValueAt (h · g) z (F z g) := by
  classical

  set S := p.roots.toFinset with hS
  have hroot : ∀ z, p.eval z = 0 → z ∈ S := fun z hz => by
    rw [hS, Multiset.mem_toFinset, Polynomial.mem_roots hp]; exact hz
  set σ₁ : ℝ := |t| + ∑ a ∈ S, |a.re| with hσ₁
  have hright : ∀ z : ℂ, σ₁ < z.re → t < z.re ∧ p.eval z ≠ 0 := by
    intro z hz
    have h0 : 0 ≤ ∑ a ∈ S, |a.re| := Finset.sum_nonneg fun a _ => abs_nonneg _
    have ht := le_abs_self t
    refine ⟨by linarith, fun h0' => ?_⟩
    have hz' : |z.re| ≤ ∑ a ∈ S, |a.re| :=
      Finset.single_le_sum (f := fun a : ℂ => |a.re|) (fun a _ => abs_nonneg _) (hroot z h0')
    have := le_abs_self z.re
    linarith [abs_nonneg t]

  set Q : ℂ → G → ℂ := fun z g => Ê z g / p.eval z with hQ
  have hpan : ∀ z, AnalyticAt ℂ (fun z => p.eval z) z := fun z => p.differentiable.analyticAt z
  have hmer : ∀ g, IsMerExt (h · g) U (Q · g) := by
    intro g
    refine ⟨hR, fun z hz => ?_, ⟨σ₁, fun z hz => ?_⟩⟩
    · exact (((hd g).analyticAt (hU.mem_nhds hz)).meromorphicAt).div (hpan z).meromorphicAt
    · obtain ⟨h1, h2⟩ := hright z hz
      show Ê z g / p.eval z = h z g
      rw [he z h1 g, mul_div_cancel_left₀ _ h2]
  have hext : ∀ g z, z ∈ U → IsExtAt (h · g) z (Q · g) := fun g z hz => ⟨U, hz, hmer g⟩
  have htend : ∀ g, Tendsto (Q · g) (𝓝[≠] s₀) (𝓝 (v g)) := fun g => (hext g s₀ hs).holValueAt_iff.1 (hv g)

  have hnhds : U ∩ ((((S.erase s₀ : Finset ℂ) : Set ℂ))ᶜ) ∈ 𝓝 s₀ :=
    Filter.inter_mem (hU.mem_nhds hs) ((Finset.finite_toSet _).isClosed.isOpen_compl.mem_nhds (by simp))
  obtain ⟨r₁, hr₁, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  have hbU : ∀ z ∈ Metric.ball s₀ r₁, z ∈ U := fun z hz => (hball hz).1
  have hbp : ∀ z ∈ Metric.ball s₀ r₁, z ≠ s₀ → p.eval z ≠ 0 := fun z hz hne h0 =>
    (hball hz).2 (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hne, hroot z h0⟩))
  have hQd : ∀ g, ∀ z ∈ Metric.ball s₀ r₁, z ≠ s₀ → DifferentiableAt ℂ (Q · g) z := fun g z hz hne =>
    ((hd g).differentiableAt (hU.mem_nhds (hbU z hz))).div (p.differentiable z) (hbp z hz hne)

  set F : ℂ → G → ℂ := fun z g => Function.update (fun w => Q w g) s₀ (v g) z with hF
  have hFQ : ∀ g z, z ≠ s₀ → F z g = Q z g := fun g z hne => by
    show Function.update (fun w => Q w g) s₀ (v g) z = Q z g
    exact Function.update_of_ne hne _ _
  have hFs : ∀ g, F s₀ g = v g := fun g => by
    show Function.update (fun w => Q w g) s₀ (v g) s₀ = v g
    exact Function.update_self _ _ _
  have hFd : ∀ g, DifferentiableOn ℂ (F · g) (Metric.ball s₀ r₁) := by
    intro g
    refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (Metric.ball_mem_nhds s₀ hr₁)).1 ⟨?_, ?_⟩
    · intro z hz
      have hne : z ≠ s₀ := fun e => hz.2 (Set.mem_singleton_iff.2 e)
      refine ((hQd g z hz.1 hne).congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [isOpen_ne.mem_nhds hne] with w hw
      exact hFQ g w hw
    · show ContinuousAt (Function.update (fun w => Q w g) s₀ (v g)) s₀
      exact continuousAt_update_same.2 (htend g)
  have hHol : ∀ g, ∀ z ∈ Metric.ball s₀ r₁, HolValueAt (h · g) z (F z g) := by
    intro g z hz
    by_cases hne : z = s₀
    · subst hne; rw [hFs]; exact hv g
    · rw [hFQ g z hne]
      exact (hext g z (hbU z hz)).holValueAt_iff.2
        ((hQd g z hz hne).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

  set ρ : ℝ := 3 * r₁ / 4 with hρ
  have hρ0 : ρ ≠ 0 := by rw [hρ]; positivity
  set K : ℂ × G → ℝ → ℂ := fun y θ => (circleMap 0 ρ θ * Complex.I) •
    ((circleMap s₀ ρ θ - y.1)⁻¹ • (Ê (circleMap s₀ ρ θ) y.2 / p.eval (circleMap s₀ ρ θ))) with hK
  have hcirc : ∀ θ, circleMap s₀ ρ θ ∈ Metric.ball s₀ r₁ := fun θ => by
    rw [Metric.mem_ball, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_pos (by rw [hρ]; positivity)]
    rw [hρ]; linarith
  have hrep : ∀ y ∈ Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G),
      F y.1 y.2 = (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, K y θ := by
    rintro ⟨z, g⟩ ⟨hz, -⟩
    have hzρ : z ∈ Metric.ball s₀ ρ := Metric.ball_subset_ball (by rw [hρ]; linarith) hz
    have hcl : Metric.closedBall s₀ ρ ⊆ Metric.ball s₀ r₁ := Metric.closedBall_subset_ball (by rw [hρ]; linarith)
    rw [← Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      (s := ∅) Set.countable_empty hzρ ((hFd g).continuousOn.mono hcl)
      (fun x hx => (hFd g).differentiableAt (Metric.isOpen_ball.mem_nhds (hcl (Metric.ball_subset_closedBall hx.1))))]
    congr 1
    unfold circleIntegral
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hK, deriv_circleMap]
    rw [hFQ g _ (circleMap_ne_center hρ0)]
  have hcont : ContinuousOn (fun y : ℂ × G => (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, K y θ)
      (Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) := by
    rw [continuousOn_iff_continuous_restrict]
    show Continuous fun x : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) =>
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, K x.1 θ
    suffices hI : Continuous fun x : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) =>
        ∫ θ in (0 : ℝ)..2 * Real.pi, K x.1 θ from
      (continuous_const : Continuous fun _ : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) =>
        (2 * Real.pi * Complex.I : ℂ)⁻¹).smul hI
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (x : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G))) θ => K x.1 θ) ?_ 0 (2 * Real.pi)
    show Continuous fun q : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) × ℝ => (circleMap 0 ρ q.2 * Complex.I) •
      ((circleMap s₀ ρ q.2 - q.1.1.1)⁻¹ • (Ê (circleMap s₀ ρ q.2) q.1.1.2 / p.eval (circleMap s₀ ρ q.2)))
    have hc1 : Continuous fun q : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) × ℝ => circleMap s₀ ρ q.2 :=
      (continuous_circleMap s₀ ρ).comp continuous_snd
    have hE : Continuous fun q : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) × ℝ =>
        Ê (circleMap s₀ ρ q.2) q.1.1.2 :=
      hc.comp_continuous (f := fun q : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) × ℝ =>
        (circleMap s₀ ρ q.2, q.1.1.2)) (hc1.prodMk (continuous_snd.comp (continuous_subtype_val.comp continuous_fst)))
        (fun q => ⟨hbU _ (hcirc q.2), Set.mem_univ _⟩)
    have hP : Continuous fun q : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) × ℝ => p.eval (circleMap s₀ ρ q.2) :=
      p.continuous.comp hc1
    have hz : Continuous fun q : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) × ℝ => q.1.1.1 :=
      continuous_fst.comp (continuous_subtype_val.comp continuous_fst)
    refine ((continuous_circleMap 0 ρ).comp continuous_snd |>.mul continuous_const).smul ?_
    refine ((hc1.sub hz).inv₀ fun q => ?_).smul (hE.div hP fun q => ?_)
    · have hq : q.1.1.1 ∈ Metric.ball s₀ ρ := Metric.ball_subset_ball (by rw [hρ]; linarith) q.1.2.1
      exact sub_ne_zero.2 (circleMap_ne_mem_ball hq q.2)
    · exact hbp _ (hcirc q.2) (circleMap_ne_center hρ0)
  refine ⟨r₁ / 2, F, by positivity, hcont.congr hrep, fun g => (hFd g).mono (Metric.ball_subset_ball (by linarith)),
    hFs, fun g z hz => hHol g z (Metric.ball_subset_ball (by linarith) hz)⟩

end PositivityTheory.SiegelWeilFormula.Atop

end
