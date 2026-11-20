import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction

noncomputable section

open Matrix
open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

/- English proof (translation)
Use `set L := ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ V W W (Fin n) M ∘SL ContinuousAlternatingMap.compContinuousLinearMapCLM A with hL`. Establish `hd : DifferentiableAt ℝ (fun x => L (f (A x))) p` using `L.differentiableAt.comp p (hf.comp p A.differentiableAt)`. Establish `key : ∀ u : Fin n → V, HasFDerivAt (fun x => L (f (A x)) u) (M ∘L ((fderiv ℝ f (A p)).flipAlternating (A ∘ u)) ∘L A) p`. Introduce `u`. Conclude with `M.hasFDerivAt.comp p ((hf.hasFDerivAt.continuousAlternatingMap_apply_const (A ∘ u)).comp p A.hasFDerivAt)`.

Rewrite using `[extDeriv_apply hd, extDeriv_apply hf, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[(key _).fderiv, fderiv_continuousAlternatingMap_apply_const hf]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
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
Introduce `Γ V S _ _ _ d G q γ w`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `s p`. Express the relevant statement in the definitionally equal form `G.Y.indicator (extDeriv (fun x => G.tr q γ ((w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) x)))) p = G.tr (q + 1) γ (G.Y.indicator (extDeriv ((w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) ((G.σ γ⁻¹) s))) ((G.ρ γ⁻¹) p))`. Distinguish the cases in `hp : p ∈ G.Y`.

Establish `hAp : (G.ρ γ⁻¹) p ∈ G.Y` using `G.maps γ⁻¹ p hp`. Rewrite using `[Set.indicator_of_mem hp, Set.indicator_of_mem hAp]`. Use `ContinuousAlternatingMap.ext fun v => ?_` and prove the remaining obligations. Establish `hdiff : DifferentiableAt ℝ ((w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) ((G.σ γ⁻¹) s)) ((G.ρ γ⁻¹) p)` using `((w.2 ((G.σ γ⁻¹) s)).1.contDiffAt (G.isOpen.mem_nhds hAp)).differentiableAt (by simp)`. Conclude with `extDeriv_comp_linear_eq_of_differentiableAt _ _ (mulVecL (G.ξ γ)) p hdiff v`.

Establish `hAp : (G.ρ γ⁻¹) p ∉ G.Y`. Introduce `h`. Establish `h2` using `G.maps γ _ h`. Rewrite `h2` using `[← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]`. Conclude with `hp h2`.

Rewrite using `[Set.indicator_of_notMem hp, Set.indicator_of_notMem hAp, map_zero]`.
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
