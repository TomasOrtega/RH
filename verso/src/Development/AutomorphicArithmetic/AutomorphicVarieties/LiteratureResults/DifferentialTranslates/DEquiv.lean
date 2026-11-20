import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction

noncomputable section

open Matrix
open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
private theorem extDeriv_comp_linear_eq_of_differentiableAt {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ} (f : V → V [⋀^Fin n]→L[ℝ] W)
    (A : V →L[ℝ] V) (M : W →L[ℝ] W) (p : V) (hf : DifferentiableAt ℝ f (A p))
    (v : Fin (n + 1) → V) :
    extDeriv (fun x => (ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ V W W (Fin n) M ∘SL
      ContinuousAlternatingMap.compContinuousLinearMapCLM A) (f (A x))) p v =
      M (extDeriv f (A p) (A ∘ v)) := by
  set L := ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ V W W (Fin n) M ∘SL
      ContinuousAlternatingMap.compContinuousLinearMapCLM A with hL
  have hd : DifferentiableAt ℝ (fun x => L (f (A x))) p :=
    L.differentiableAt.comp p (hf.comp p A.differentiableAt)
  have key : ∀ u : Fin n → V, HasFDerivAt (fun x => L (f (A x)) u)
      (M ∘L ((fderiv ℝ f (A p)).flipAlternating (A ∘ u)) ∘L A) p := by
    intro u
    exact M.hasFDerivAt.comp p
      ((hf.hasFDerivAt.continuousAlternatingMap_apply_const (A ∘ u)).comp p A.hasFDerivAt)
  rw [extDeriv_apply hd, extDeriv_apply hf, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(key _).fderiv, fderiv_continuousAlternatingMap_apply_const hf]
  simp
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Express the relevant assertion in an equivalent form by its definition. Consider separately whether the proposition holds or fails.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem dEquiv : DEquiv := by
  intro Γ V S _ _ _ d G q γ w
  apply Subtype.ext
  funext s p
  change G.Y.indicator (extDeriv (fun x => G.tr q γ
      ((w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) x)))) p =
    G.tr (q + 1) γ (G.Y.indicator
      (extDeriv ((w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) ((G.σ γ⁻¹) s))) ((G.ρ γ⁻¹) p))
  by_cases hp : p ∈ G.Y
  · have hAp : (G.ρ γ⁻¹) p ∈ G.Y := G.maps γ⁻¹ p hp
    rw [Set.indicator_of_mem hp, Set.indicator_of_mem hAp]
    refine ContinuousAlternatingMap.ext fun v => ?_
    have hdiff : DifferentiableAt ℝ ((w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) ((G.σ γ⁻¹) s))
        ((G.ρ γ⁻¹) p) :=
      ((w.2 ((G.σ γ⁻¹) s)).1.contDiffAt (G.isOpen.mem_nhds hAp)).differentiableAt (by simp)
    exact extDeriv_comp_linear_eq_of_differentiableAt _ _ (mulVecL (G.ξ γ)) p hdiff v
  · have hAp : (G.ρ γ⁻¹) p ∉ G.Y := by
      intro h
      have h2 := G.maps γ _ h
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        ContinuousLinearMap.one_apply] at h2
      exact hp h2
    rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hAp, map_zero]

end UpperTheory.V.Lit.Dr
