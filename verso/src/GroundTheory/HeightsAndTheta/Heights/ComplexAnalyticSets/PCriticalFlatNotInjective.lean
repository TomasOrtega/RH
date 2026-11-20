import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCriticalFlatNotInjective
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.HolomorphicZerosNotIsolated
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicInverse
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularLocusDense
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAnalyticImplicitChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric

/- English proof (translation)
Introduce `k U f a hk hU hf haU hJa hflat hinj`. Use `set J : (Fin k → ℂ) → ℂ := fun z => LinearMap.det (fderiv ℂ f z : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) with hJdef`. Establish `hJan : AnalyticOnNhd ℂ J U` using `fun z hz => analyticAt_det_fderiv (InjectiveHolomorphicInverse.analyticAt_of_differentiableOn hU hf hz)`. Use `set Z : Set (Fin k → ℂ) := {z | J z = 0} with hZdef`. Establish `hZ : IsAnalyticNear Z a`.

Use `⟨U, 1, fun _ => J, hU, haU, fun _ => hJan, ?_⟩` and prove the remaining obligations. Use extensionality with `z`. Simplify using `only [hZdef, Set.mem_inter_iff, Set.mem_ofPred_eq, forall_const]`. The claim follows by propositional logic. Take `⟨N, hN, haN, hdense⟩` from `RegularLocusDense.proof AnalyticImplicitChart.proof (Fin k) Z a hZ`.

Establish `hB : IsOpen (N ∩ U)` using `hN.inter hU`. Establish `ha : a ∈ closure (regLocus (Z ∩ (N ∩ U)))` using `hdense (N ∩ U) hB Set.inter_subset_left ⟨hJa, haN, haU⟩`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : (regLocus (Z ∩ (N ∩ U))).Nonempty := by`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[Set.not_nonempty_iff_eq_empty]`.

Rewrite `ha` using `[h, closure_empty]`. Conclude with `ha`. Take `⟨⟨hcZ, hcB⟩, d, A, O, V, g, hO, hV, hcV, hg, hAg, hYV⟩` from `hc`. Take `⟨y0, hy0O, hgy0⟩ : c ∈ g '' O` from `hYV ▸ ⟨⟨hcZ, hcB⟩, hcV⟩`. Establish `hgO : ∀ y ∈ O, J (g y) = 0 ∧ g y ∈ U`.

Introduce `y hy`. Establish `h1 : g y ∈ Z ∩ (N ∩ U) ∩ V` using `hYV ▸ Set.mem_image_of_mem g hy`. Conclude with `⟨h1.1.1, h1.1.2.2⟩`. Break down `Nat.eq_zero_or_pos d with rfl | hd` into its components or cases. Take `⟨z, ⟨hzV, hzB⟩, hzc, hz0⟩` from `exists_zero_ne_near hk (hJan c hcB.2) hcZ (Filter.inter_mem (hV.mem_nhds hcV) (hB.mem_nhds hcB))`.

Take `⟨y1, -, hgy1⟩ : z ∈ g '' O` from `hYV ▸ ⟨⟨hz0, hzB⟩, hzV⟩`. Conclude with `hzc (by rw [← hgy1, ← hgy0, Subsingleton.elim y1 y0])`. Establish `: Nonempty (Fin d)` using `⟨⟨0, hd⟩⟩`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.1 hO y0 hy0O`. Establish `hconst : ∀ y ∈ ball y0 ε, f (g y) = f (g y0)`.

Introduce `y hy`. Establish `hdiff : ∀ x ∈ ball y0 ε, DifferentiableAt ℂ (f ∘ g) x` using `fun x hx => (hf.differentiableAt (hU.mem_nhds (hgO x (hball hx)).2)).comp x (hg x (hball hx)).differentiableAt`. Use `(convex_ball y0 ε).is_const_of_fderivWithin_eq_zero (f := f ∘ g) (fun x hx => (hdiff x hx).differentiableWithinAt) (fun x hx => ?_) hy (mem_ball_self hε)` and prove the remaining obligations. Rewrite using `[fderivWithin_of_isOpen isOpen_ball hx, fderiv_comp x (hf.differentiableAt (hU.mem_nhds (hgO x (hball hx)).2)) (hg x (hball hx)).differentiableAt, hflat (g x) (hgO x (hball hx)).2 (hgO x (hball hx)).1, ContinuousLinearMap.zero_comp]`. Use `set y1 : Fin d → ℂ := y0 + ((ε / 2 : ℝ) : ℂ) • (fun _ => (1 : ℂ)) with hy1`.

Establish `hy1ball : y1 ∈ ball y0 ε`. Rewrite using `[mem_ball, dist_eq_norm, hy1, add_sub_cancel_left, norm_smul, pi_norm_const, norm_one, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hy10 : y1 ≠ y0`. Introduce `h`.

Establish `h2` using `congrFun (congrArg (· - y0) h) ⟨0, hd⟩`. Simplify using `only [hy1, add_sub_cancel_left, sub_self, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_one, Complex.ofReal_eq_zero] at h2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `heq : g y1 = g y0` using `hinj (hgO y1 (hball hy1ball)).2 (hgO y0 hy0O).2 (hconst y1 hy1ball)`. Conclude with `hy10 (by rw [← hAg y1 (hball hy1ball), ← hAg y0 hy0O, heq])`.
-/
theorem CriticalFlatNotInjective.proof : CriticalFlatNotInjective.Statement := by
  intro k U f a hk hU hf haU hJa hflat hinj
  set J : (Fin k → ℂ) → ℂ := fun z => LinearMap.det (fderiv ℂ f z : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) with hJdef
  have hJan : AnalyticOnNhd ℂ J U := fun z hz =>
    analyticAt_det_fderiv (InjectiveHolomorphicInverse.analyticAt_of_differentiableOn hU hf hz)
  set Z : Set (Fin k → ℂ) := {z | J z = 0} with hZdef
  have hZ : IsAnalyticNear Z a := by
    refine ⟨U, 1, fun _ => J, hU, haU, fun _ => hJan, ?_⟩
    ext z
    simp only [hZdef, Set.mem_inter_iff, Set.mem_ofPred_eq, forall_const]
    tauto
  obtain ⟨N, hN, haN, hdense⟩ :=
    RegularLocusDense.proof AnalyticImplicitChart.proof (Fin k) Z a hZ
  have hB : IsOpen (N ∩ U) := hN.inter hU
  have ha : a ∈ closure (regLocus (Z ∩ (N ∩ U))) :=
    hdense (N ∩ U) hB Set.inter_subset_left ⟨hJa, haN, haU⟩
  obtain ⟨c, hc⟩ : (regLocus (Z ∩ (N ∩ U))).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at ha
    exact ha
  obtain ⟨⟨hcZ, hcB⟩, d, A, O, V, g, hO, hV, hcV, hg, hAg, hYV⟩ := hc
  obtain ⟨y0, hy0O, hgy0⟩ : c ∈ g '' O := hYV ▸ ⟨⟨hcZ, hcB⟩, hcV⟩

  have hgO : ∀ y ∈ O, J (g y) = 0 ∧ g y ∈ U := by
    intro y hy
    have h1 : g y ∈ Z ∩ (N ∩ U) ∩ V := hYV ▸ Set.mem_image_of_mem g hy
    exact ⟨h1.1.1, h1.1.2.2⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  ·
    obtain ⟨z, ⟨hzV, hzB⟩, hzc, hz0⟩ := exists_zero_ne_near hk (hJan c hcB.2) hcZ
      (Filter.inter_mem (hV.mem_nhds hcV) (hB.mem_nhds hcB))
    obtain ⟨y1, -, hgy1⟩ : z ∈ g '' O := hYV ▸ ⟨⟨hz0, hzB⟩, hzV⟩
    exact hzc (by rw [← hgy1, ← hgy0, Subsingleton.elim y1 y0])
  ·
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO y0 hy0O
    have hconst : ∀ y ∈ ball y0 ε, f (g y) = f (g y0) := by
      intro y hy
      have hdiff : ∀ x ∈ ball y0 ε, DifferentiableAt ℂ (f ∘ g) x := fun x hx =>
        (hf.differentiableAt (hU.mem_nhds (hgO x (hball hx)).2)).comp x
          (hg x (hball hx)).differentiableAt
      refine (convex_ball y0 ε).is_const_of_fderivWithin_eq_zero (f := f ∘ g)
        (fun x hx => (hdiff x hx).differentiableWithinAt) (fun x hx => ?_) hy (mem_ball_self hε)
      rw [fderivWithin_of_isOpen isOpen_ball hx,
        fderiv_comp x (hf.differentiableAt (hU.mem_nhds (hgO x (hball hx)).2))
          (hg x (hball hx)).differentiableAt,
        hflat (g x) (hgO x (hball hx)).2 (hgO x (hball hx)).1, ContinuousLinearMap.zero_comp]
    set y1 : Fin d → ℂ := y0 + ((ε / 2 : ℝ) : ℂ) • (fun _ => (1 : ℂ)) with hy1
    have hy1ball : y1 ∈ ball y0 ε := by
      rw [mem_ball, dist_eq_norm, hy1, add_sub_cancel_left, norm_smul, pi_norm_const, norm_one, mul_one,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    have hy10 : y1 ≠ y0 := by
      intro h
      have h2 := congrFun (congrArg (· - y0) h) ⟨0, hd⟩
      simp only [hy1, add_sub_cancel_left, sub_self, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
        mul_one, Complex.ofReal_eq_zero] at h2
      linarith
    have heq : g y1 = g y0 :=
      hinj (hgO y1 (hball hy1ball)).2 (hgO y0 hy0O).2 (hconst y1 hy1ball)
    exact hy10 (by rw [← hAg y1 (hball hy1ball), ← hAg y0 hy0O, heq])

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
