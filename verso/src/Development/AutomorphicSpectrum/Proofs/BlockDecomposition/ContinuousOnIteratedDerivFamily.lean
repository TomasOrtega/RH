import Mathlib

open Filter Topology

namespace GlobalTheory.CompanionTheory.HolFamily

/- English proof (translation)
Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem continuousOn_deriv_family (P : Type) [TopologicalSpace P] (U : Set ℂ) (hU : IsOpen U)
    (H : P → ℂ → ℂ) (hc : ContinuousOn (fun q : P × ℂ => H q.1 q.2) (Set.univ ×ˢ U))
    (hd : ∀ p, DifferentiableOn ℂ (H p) U) :
    ContinuousOn (fun q : P × ℂ => deriv (H q.1) q.2) (Set.univ ×ˢ U) := by
  rintro ⟨p0, z0⟩ ⟨-, hz0⟩
  simp only at hz0
  obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.1 hU z0 hz0
  have hR : 0 < e / 3 := by positivity
  set R := e / 3 with hRdef
  have hKU : Metric.closedBall z0 (2 * R) ⊆ U := by
    refine (Metric.closedBall_subset_ball ?_).trans hball
    rw [hRdef]; linarith
  let K : Set ℂ := Metric.closedBall z0 (2 * R)
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_closedBall z0 (2 * R))
  have hFc : Continuous (fun x : P × K => H x.1 x.2) := by
    have : Continuous (fun x : P × K => ((x.1, (x.2 : ℂ)) : P × ℂ)) := by fun_prop
    exact hc.comp_continuous this (fun x => ⟨Set.mem_univ _, hKU x.2.2⟩)
  let F : C(P × K, ℂ) := ⟨fun x => H x.1 x.2, hFc⟩
  let G : C(P, C(K, ℂ)) := F.curry
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  have hGc : Tendsto G (𝓝 p0) (𝓝 (G p0)) := G.continuous.tendsto p0
  have h1 : ∀ᶠ p in 𝓝 p0, dist (G p) (G p0) < ε / 2 * R / 2 :=
    (Metric.tendsto_nhds.1 hGc) _ (by positivity)
  have hdc : ContinuousAt (deriv (H p0)) z0 :=
    ((hd p0).deriv hU).continuousOn.continuousAt (hU.mem_nhds hz0)
  have h2 : ∀ᶠ z in 𝓝 z0, dist (deriv (H p0) z) (deriv (H p0) z0) < ε / 2 :=
    (Metric.tendsto_nhds.1 hdc) _ (by positivity)
  have h3 : ∀ᶠ z in 𝓝 z0, z ∈ Metric.ball z0 R := Metric.ball_mem_nhds z0 hR
  have h4 := h1.prod_nhds (h2.and h3)
  filter_upwards [nhdsWithin_le_nhds h4]
  rintro ⟨p, z⟩ ⟨hp, hz, hzR⟩
  simp only at hp hz hzR ⊢
  have hsub : Metric.closedBall z R ⊆ K := by
    intro w hw
    rw [Metric.mem_closedBall] at hw ⊢
    rw [Metric.mem_ball] at hzR
    have := dist_triangle w z z0
    linarith
  have hfd : DifferentiableOn ℂ (fun w => H p w - H p0 w) U := (hd p).sub (hd p0)
  have hzU : z ∈ U := hKU (hsub (Metric.mem_closedBall_self hR.le))
  have hnh : U ∈ 𝓝 z := hU.mem_nhds hzU
  have hderiv : deriv (fun w => H p w - H p0 w) z = deriv (H p) z - deriv (H p0) z :=
    deriv_fun_sub ((hd p).differentiableAt hnh) ((hd p0).differentiableAt hnh)
  have hbound : ∀ w ∈ Metric.sphere z R, ‖H p w - H p0 w‖ ≤ ε / 2 * R / 2 := by
    intro w hw
    have hwK : w ∈ K := hsub (Metric.sphere_subset_closedBall hw)
    have := ContinuousMap.dist_apply_le_dist (f := G p) (g := G p0) (⟨w, hwK⟩ : K)
    have h5 : dist (G p ⟨w, hwK⟩) (G p0 ⟨w, hwK⟩) = ‖H p w - H p0 w‖ := by
      rw [dist_eq_norm]; rfl
    rw [← h5]
    exact this.trans hp.le
  have hcauchy : ‖deriv (fun w => H p w - H p0 w) z‖ ≤ ε / 2 * R / 2 / R :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR
      (hfd.diffContOnCl_ball (hsub.trans hKU)) hbound
  have hval : ε / 2 * R / 2 / R = ε / 4 := by field_simp; ring
  rw [hval, hderiv] at hcauchy
  calc dist (deriv (H p) z) (deriv (H p0) z0)
      ≤ dist (deriv (H p) z) (deriv (H p0) z) + dist (deriv (H p0) z) (deriv (H p0) z0) :=
        dist_triangle _ _ _
    _ < ε := by
        rw [dist_eq_norm (deriv (H p) z)]
        linarith

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Rewrite the conclusion using the stated equalities. Proceed by induction. Treat this case separately. Treat this case separately.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem continuousOn_iteratedDeriv_family :
    ∀ (P : Type) [TopologicalSpace P] (U : Set ℂ), IsOpen U → ∀ H : P → ℂ → ℂ,
      ContinuousOn (fun q : P × ℂ => H q.1 q.2) (Set.univ ×ˢ U) →
      (∀ p, DifferentiableOn ℂ (H p) U) →
        ∀ r : ℕ, ContinuousOn (fun q : P × ℂ => iteratedDeriv r (H q.1) q.2) (Set.univ ×ˢ U) := by
  intro P _ U hU H hc hd r
  have hdiff : ∀ (r : ℕ) (p : P), DifferentiableOn ℂ (iteratedDeriv r (H p)) U := by
    intro r p
    induction r with
    | zero => simpa [iteratedDeriv_zero] using hd p
    | succ r ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv hU
  induction r with
  | zero => simpa [iteratedDeriv_zero] using hc
  | succ r ih =>
    simp only [iteratedDeriv_succ]
    exact continuousOn_deriv_family P U hU (fun p => iteratedDeriv r (H p)) ih (hdiff r)

end GlobalTheory.CompanionTheory.HolFamily
