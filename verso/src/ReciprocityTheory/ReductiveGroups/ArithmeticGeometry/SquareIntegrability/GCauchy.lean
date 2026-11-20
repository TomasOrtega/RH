import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContDiffOfDifferentiableFd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.RCauchy

namespace ReciprocityTheory.ChartRestriction.G.I2

open Classical in
/- English proof (translation)
Introduce `ι _ F hF S hS α`. Use `set N := Fintype.card ι`. Set `e : ι ≃ Fin N` to `Fintype.equivFin ι`. Set `T : (Fin N → ℂ) →L[ℂ] EuclideanSpace ℂ ι` to `(EuclideanSpace.equiv ι ℂ).symm.toContinuousLinearMap.comp (LinearMap.funLeft ℂ ℂ e).toContinuousLinearMap`. Establish `hT : ∀ z : Fin N → ℂ, ‖T z‖ ^ 2 = ∑ j, ‖z j‖ ^ 2`.

Introduce `z`. Rewrite using `[EuclideanSpace.norm_sq_eq]`. Simplify using `only [T, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, LinearMap.coe_toContinuousLinearMap', Function.comp_apply, LinearMap.funLeft_apply]`. Simplify using `only [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply]`. Conclude with `Fintype.sum_equiv e _ _ (fun i => by simp)`.

Establish `hTs : ∀ i : ι, T (Pi.single (e i) 1) = EuclideanSpace.single i 1`. Introduce `i`. Use extensionality with `j`. Simplify using `only [T, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, LinearMap.coe_toContinuousLinearMap', Function.comp_apply, LinearMap.funLeft_apply, EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply, EuclideanSpace.single_apply]`. Distinguish the cases in `h : j = i`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Pi.single_apply, e.injective.ne h]`. Use `set G : (Fin N → ℂ) → ℂ := F ∘ T`. Establish `hG : Differentiable ℂ G` using `hF.comp T.differentiable`.

Establish `hGS : ∀ z, ‖G z‖ ^ 2 * Real.exp (-Real.pi * ∑ i, ‖z i‖ ^ 2) ≤ S`. Introduce `z`. Use `hS (T z)` as an intermediate fact. Rewrite `this` using `[hT z]`. Then use the resulting hypothesis. Use `set k := Multiset.card (Finsupp.toMultiset α)`.

Use `set l : Fin k → Fin N := fun j => e ((Finsupp.toMultiset α).toList.get (j.cast (Multiset.length_toList _).symm))`. Establish `hc` using `cauchy_gauss_le G hG S hGS l`. Establish `hF' : ContDiff ℂ k F` using `contDiff_of_differentiable_fd hF k`. Establish `hcomp : iteratedFDeriv ℂ k G 0 (fun j => Pi.single (l j) 1) = iteratedFDeriv ℂ k F 0 (fun j => EuclideanSpace.single ((Finsupp.toMultiset α).toList.get (j.cast (Multiset.length_toList _).symm)) 1)`. Rewrite using `[show G = F ∘ T from rfl, T.iteratedFDeriv_comp_right hF' 0 le_rfl]`.

Simplify using `only [ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Conclude with `hTs _`. Establish `hk : k = α.degree`.

Simplify using `only [k, Finsupp.card_toMultiset]`. Use `first`. Consider the case `rfl`. Consider the case `simp [Finsupp.sum, Finsupp.degree]`. Establish `hdeg : (k : ℝ) = (α.degree : ℝ)` using `by rw [hk]`.

Unfold `polyDeriv`. Rewrite using `[MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl, one_mul]`. Rewrite using `[← hdeg, ← hcomp]`. Conclude with `hc`.
-/
theorem gCauchy : GCauchyStatement := by
  intro ι _ F hF S hS α
  set N := Fintype.card ι
  let e : ι ≃ Fin N := Fintype.equivFin ι

  let T : (Fin N → ℂ) →L[ℂ] EuclideanSpace ℂ ι :=
    (EuclideanSpace.equiv ι ℂ).symm.toContinuousLinearMap.comp
      (LinearMap.funLeft ℂ ℂ e).toContinuousLinearMap
  have hT : ∀ z : Fin N → ℂ, ‖T z‖ ^ 2 = ∑ j, ‖z j‖ ^ 2 := by
    intro z
    rw [EuclideanSpace.norm_sq_eq]
    simp only [T, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
      LinearMap.coe_toContinuousLinearMap', Function.comp_apply, LinearMap.funLeft_apply]
    simp only [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply]
    exact Fintype.sum_equiv e _ _ (fun i => by simp)
  have hTs : ∀ i : ι, T (Pi.single (e i) 1) = EuclideanSpace.single i 1 := by
    intro i
    ext j
    simp only [T, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
      LinearMap.coe_toContinuousLinearMap', Function.comp_apply, LinearMap.funLeft_apply,
      EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply, EuclideanSpace.single_apply]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Pi.single_apply, e.injective.ne h]
  set G : (Fin N → ℂ) → ℂ := F ∘ T
  have hG : Differentiable ℂ G := hF.comp T.differentiable
  have hGS : ∀ z, ‖G z‖ ^ 2 * Real.exp (-Real.pi * ∑ i, ‖z i‖ ^ 2) ≤ S := by
    intro z
    have := hS (T z)
    rwa [hT z] at this
  set k := Multiset.card (Finsupp.toMultiset α)
  set l : Fin k → Fin N := fun j =>
    e ((Finsupp.toMultiset α).toList.get (j.cast (Multiset.length_toList _).symm))
  have hc := cauchy_gauss_le G hG S hGS l
  have hF' : ContDiff ℂ k F := contDiff_of_differentiable_fd hF k
  have hcomp : iteratedFDeriv ℂ k G 0 (fun j => Pi.single (l j) 1) =
      iteratedFDeriv ℂ k F 0 (fun j => EuclideanSpace.single
        ((Finsupp.toMultiset α).toList.get (j.cast (Multiset.length_toList _).symm)) 1) := by
    rw [show G = F ∘ T from rfl, T.iteratedFDeriv_comp_right hF' 0 le_rfl]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
    congr 1
    funext j
    exact hTs _
  have hk : k = α.degree := by
    simp only [k, Finsupp.card_toMultiset]
    first
      | rfl
      | simp [Finsupp.sum, Finsupp.degree]
  have hdeg : (k : ℝ) = (α.degree : ℝ) := by rw [hk]
  unfold polyDeriv
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl, one_mul]
  rw [← hdeg, ← hcomp]
  exact hc

end ReciprocityTheory.ChartRestriction.G.I2
