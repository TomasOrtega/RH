import Mathlib
open IsLocalRing CategoryTheory Limits

namespace GlobalTheory.EtaleDescent

open TensorProduct

/- English proof (translation)
Introduce `J _ _ D c hc A _ _ _`. Establish `hc'` using `isColimitOfPreserves (forget _) hc`. Take `⟨ι, σ, _, _, P, hP⟩` from `(Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero (R := c.pt) (S := A)).mp inferInstance |>.out`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, P.coeffs ⊆ Set.range (c.ι.app j).hom := by`. Establish `hfin` using `P.finite_coeffs`.

Use `choose jx x hx using fun y : c.pt ↦ Types.jointly_surjective_of_isColimit hc' y`. Take `⟨j, hj⟩` from `IsFiltered.sup_objs_exists (hfin.toFinset.image jx)`. Use `⟨j, fun y hy ↦ ?_⟩` and prove the remaining obligations. Take `⟨f⟩` from `hj (Finset.mem_image_of_mem jx (hfin.mem_toFinset.mpr hy))`. Use `⟨D.map f (x y), ?_⟩` and prove the remaining obligations.

Establish `h1` using `hx y`. Establish `h2` using `congr(($(c.w f)).hom (x y))`. Simplify using `only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2`. Rewrite using `[h2]`. Conclude with `h1`.

Use `letI : Algebra (D.obj j) c.pt := (c.ι.app j).hom.toAlgebra`. Use `letI : Algebra (D.obj j) A := ((algebraMap c.pt A).comp (c.ι.app j).hom).toAlgebra`. Use `haveI : IsScalarTower (D.obj j) c.pt A := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)`. Use `haveI : P.HasCoeffs (D.obj j) := ⟨by rw [RingHom.coe_range]; exact hj⟩`. Use `letI : Fintype σ := Fintype.ofFinite σ`.

Set `P₀` to `P.toPreSubmersivePresentation.ofHasCoeffs (D.obj j)`. Establish `hP₀ : P₀.jacobian = Ideal.Quotient.mk _ (P.jacobianOfHasCoeffs (D.obj j))`. Simplify using `only [P₀]`. Rewrite using `[Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]`. Simplify using `[Algebra.SubmersivePresentation.jacobianOfHasCoeffs]`.

Rewrite using `[← Algebra.Generators.algebraMap_apply]`. Both sides reduce to the same expression. Use `set E : MvPolynomial ι (D.obj j) := ∑ i, P.jacobianRelationsOfHasCoeffs (D.obj j) i * P.relationOfHasCoeffs (D.obj j) i - (P.jacobianOfHasCoeffs (D.obj j) * P.invJacobianOfHasCoeffs (D.obj j) - 1) with hEdef`. Establish `hE : E.map (algebraMap (D.obj j) c.pt) = 0`. Simplify using `[E, P.map_relationOfHasCoeffs, P.jacobianRelations_spec]`.

Establish `hdie : ∀ m : E.support, ∃ (k : J) (f : j ⟶ k), D.map f (E.coeff m) = 0`. Introduce `m`. Establish `h0 : (c.ι.app j).hom (E.coeff m) = (c.ι.app j).hom 0`. Rewrite using `[map_zero]`. Use `congr(MvPolynomial.coeff (m : ι →₀ ℕ) $hE)` as an intermediate fact.

Simplify using `only [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at this`. Conclude with `this`. Take `⟨k, f, e⟩` from `(Types.FilteredColimit.isColimit_eq_iff' hc' (E.coeff m) 0).1 (by exact h0)`. Conclude with `⟨k, f, by simpa using e⟩`. Use `choose k f hf using hdie`.

Take `⟨c'⟩` from `IsFiltered.cocone_nonempty (WidePushoutShape.wideSpan j k f)`. Use `set K := c'.pt`. Use `set g : j ⟶ K := c'.ι.app none`. Establish `hEK : E.map (D.map g).hom = 0`. Use extensionality with `m`.

Rewrite using `[MvPolynomial.coeff_map, MvPolynomial.coeff_zero]`. Distinguish the cases in `hm : m ∈ E.support`. Establish `hw` using `c'.w (WidePushoutShape.Hom.init ⟨m, hm⟩)`. Establish `h3 : (D.map g).hom (E.coeff m) = (D.map ((WidePushoutShape.wideSpan j k f).map (WidePushoutShape.Hom.init ⟨m, hm⟩) ≫ c'.ι.app (some ⟨m, hm⟩))).hom (E.coeff m)`. Rewrite using `[hw]`.

Both sides reduce to the same expression. Rewrite using `[h3, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply]`. Use `erw [hf ⟨m, hm⟩]`. Conclude with `map_zero _`. Rewrite using `[MvPolynomial.notMem_support_iff.mp hm, map_zero]`.

Use `letI : Algebra (D.obj j) (D.obj K) := (D.map g).hom.toAlgebra`. Use `letI : Algebra (D.obj K) c.pt := (c.ι.app K).hom.toAlgebra`. Use `haveI : IsScalarTower (D.obj j) (D.obj K) c.pt := IsScalarTower.of_algebraMap_eq (fun x ↦ by`. Express the relevant statement in the definitionally equal form `(c.ι.app j).hom x = (c.ι.app K).hom ((D.map g).hom x)`. Rewrite using `[← c.w g]`.

Use the proof step `rfl)`. Set `M` to `P.ModelOfHasCoeffs (D.obj j)`. Set `Q` to `P₀.baseChange (D.obj K)`. Set `φ : MvPolynomial ι (D.obj j) →ₐ[D.obj j] D.obj K ⊗[D.obj j] M` to `(Algebra.TensorProduct.includeRight).comp (Ideal.Quotient.mkₐ _ _)`. Establish `hφrel : ∀ i, φ (P.relationOfHasCoeffs (D.obj j) i) = 0`.

Introduce `i`. Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.includeRight (Ideal.Quotient.mk _ (P.relationOfHasCoeffs (D.obj j) i)) = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i)), map_zero]`. Establish `hφE : φ E = 0`. Rewrite using `[MvPolynomial.aeval_unique φ, MvPolynomial.aeval_def, IsScalarTower.algebraMap_eq (D.obj j) (D.obj K) (D.obj K ⊗[D.obj j] M), ← MvPolynomial.eval₂_map]`.

Express the relevant statement in the definitionally equal form `MvPolynomial.eval₂ _ _ (E.map (D.map g).hom) = 0`. Rewrite using `[hEK, MvPolynomial.eval₂_zero]`. Establish `hQ : IsUnit Q.jacobian`. Rewrite using `[Algebra.PreSubmersivePresentation.baseChange_jacobian, hP₀]`. Use `IsUnit.of_mul_eq_one (φ (P.invJacobianOfHasCoeffs (D.obj j))) ?_` and prove the remaining obligations.

Establish `h1 : P.jacobianOfHasCoeffs (D.obj j) * P.invJacobianOfHasCoeffs (D.obj j) = ∑ i, P.jacobianRelationsOfHasCoeffs (D.obj j) i * P.relationOfHasCoeffs (D.obj j) i - E + 1`. Rewrite using `[hEdef]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `congr(φ $h1)`. Simplify using `only [map_mul, map_add, map_sub, map_sum, map_one, hφrel, mul_zero, Finset.sum_const_zero, hφE, sub_zero, zero_add] at h2`.

Conclude with `h2`. Set `Q' : Algebra.SubmersivePresentation (D.obj K) (D.obj K ⊗[D.obj j] M) ι σ` to `{ toPreSubmersivePresentation := Q, jacobian_isUnit := hQ }`. Use `haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 (D.obj K) (D.obj K ⊗[D.obj j] M) := Q'.isStandardSmoothOfRelativeDimension (by rw [← hP]; rfl)`. Use `⟨K, D.obj K ⊗[D.obj j] M, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩` and prove the remaining obligations. Conclude with `(Algebra.TensorProduct.cancelBaseChange (D.obj j) (D.obj K) c.pt c.pt M).trans (P.tensorModelOfHasCoeffsEquiv (D.obj j))`.
-/
theorem exists_etale_model_of_isColimit :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (A : Type) [CommRing A] [Algebra c.pt A] [Algebra.Etale c.pt A], ∃ (j : J), letI : Algebra (D.obj j) c.pt := (c.ι.app j).hom.toAlgebra; ∃ (Aj : Type) (_ : CommRing Aj) (_ : Algebra (D.obj j) Aj), Algebra.Etale (D.obj j) Aj ∧ Nonempty (TensorProduct (D.obj j) c.pt Aj ≃ₐ[c.pt] A) := by
  intro J _ _ D c hc A _ _ _
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  obtain ⟨ι, σ, _, _, P, hP⟩ :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero (R := c.pt) (S := A)).mp
      inferInstance |>.out

  obtain ⟨j, hj⟩ : ∃ j, P.coeffs ⊆ Set.range (c.ι.app j).hom := by
    have hfin := P.finite_coeffs
    choose jx x hx using fun y : c.pt ↦ Types.jointly_surjective_of_isColimit hc' y
    obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (hfin.toFinset.image jx)
    refine ⟨j, fun y hy ↦ ?_⟩
    obtain ⟨f⟩ := hj (Finset.mem_image_of_mem jx (hfin.mem_toFinset.mpr hy))
    refine ⟨D.map f (x y), ?_⟩
    have h1 := hx y
    have h2 := congr(($(c.w f)).hom (x y))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
    rw [h2]
    exact h1
  letI : Algebra (D.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  letI : Algebra (D.obj j) A := ((algebraMap c.pt A).comp (c.ι.app j).hom).toAlgebra
  haveI : IsScalarTower (D.obj j) c.pt A := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  haveI : P.HasCoeffs (D.obj j) := ⟨by rw [RingHom.coe_range]; exact hj⟩
  letI : Fintype σ := Fintype.ofFinite σ
  let P₀ := P.toPreSubmersivePresentation.ofHasCoeffs (D.obj j)
  have hP₀ : P₀.jacobian = Ideal.Quotient.mk _ (P.jacobianOfHasCoeffs (D.obj j)) := by
    simp only [P₀]
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp [Algebra.SubmersivePresentation.jacobianOfHasCoeffs]
    rw [← Algebra.Generators.algebraMap_apply]
    rfl

  set E : MvPolynomial ι (D.obj j) :=
    ∑ i, P.jacobianRelationsOfHasCoeffs (D.obj j) i * P.relationOfHasCoeffs (D.obj j) i -
      (P.jacobianOfHasCoeffs (D.obj j) * P.invJacobianOfHasCoeffs (D.obj j) - 1) with hEdef
  have hE : E.map (algebraMap (D.obj j) c.pt) = 0 := by
    simp [E, P.map_relationOfHasCoeffs, P.jacobianRelations_spec]

  have hdie : ∀ m : E.support, ∃ (k : J) (f : j ⟶ k), D.map f (E.coeff m) = 0 := by
    intro m
    have h0 : (c.ι.app j).hom (E.coeff m) = (c.ι.app j).hom 0 := by
      rw [map_zero]
      have := congr(MvPolynomial.coeff (m : ι →₀ ℕ) $hE)
      simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at this
      exact this
    obtain ⟨k, f, e⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc' (E.coeff m) 0).1 (by exact h0)
    exact ⟨k, f, by simpa using e⟩
  choose k f hf using hdie
  obtain ⟨c'⟩ := IsFiltered.cocone_nonempty (WidePushoutShape.wideSpan j k f)
  set K := c'.pt
  set g : j ⟶ K := c'.ι.app none
  have hEK : E.map (D.map g).hom = 0 := by
    ext m
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
    by_cases hm : m ∈ E.support
    · have hw := c'.w (WidePushoutShape.Hom.init ⟨m, hm⟩)
      have h3 : (D.map g).hom (E.coeff m) = (D.map ((WidePushoutShape.wideSpan j k f).map
          (WidePushoutShape.Hom.init ⟨m, hm⟩) ≫ c'.ι.app (some ⟨m, hm⟩))).hom (E.coeff m) := by
        rw [hw]
        rfl
      rw [h3, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply]
      erw [hf ⟨m, hm⟩]
      exact map_zero _
    · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]

  letI : Algebra (D.obj j) (D.obj K) := (D.map g).hom.toAlgebra
  letI : Algebra (D.obj K) c.pt := (c.ι.app K).hom.toAlgebra
  haveI : IsScalarTower (D.obj j) (D.obj K) c.pt := IsScalarTower.of_algebraMap_eq (fun x ↦ by
    change (c.ι.app j).hom x = (c.ι.app K).hom ((D.map g).hom x)
    rw [← c.w g]
    rfl)
  let M := P.ModelOfHasCoeffs (D.obj j)
  let Q := P₀.baseChange (D.obj K)
  let φ : MvPolynomial ι (D.obj j) →ₐ[D.obj j] D.obj K ⊗[D.obj j] M :=
    (Algebra.TensorProduct.includeRight).comp (Ideal.Quotient.mkₐ _ _)
  have hφrel : ∀ i, φ (P.relationOfHasCoeffs (D.obj j) i) = 0 := by
    intro i
    change Algebra.TensorProduct.includeRight (Ideal.Quotient.mk _ (P.relationOfHasCoeffs (D.obj j) i)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i)), map_zero]
  have hφE : φ E = 0 := by
    rw [MvPolynomial.aeval_unique φ, MvPolynomial.aeval_def,
      IsScalarTower.algebraMap_eq (D.obj j) (D.obj K) (D.obj K ⊗[D.obj j] M),
      ← MvPolynomial.eval₂_map]
    change MvPolynomial.eval₂ _ _ (E.map (D.map g).hom) = 0
    rw [hEK, MvPolynomial.eval₂_zero]
  have hQ : IsUnit Q.jacobian := by
    rw [Algebra.PreSubmersivePresentation.baseChange_jacobian, hP₀]
    refine IsUnit.of_mul_eq_one (φ (P.invJacobianOfHasCoeffs (D.obj j))) ?_
    have h1 : P.jacobianOfHasCoeffs (D.obj j) * P.invJacobianOfHasCoeffs (D.obj j) =
        ∑ i, P.jacobianRelationsOfHasCoeffs (D.obj j) i * P.relationOfHasCoeffs (D.obj j) i
          - E + 1 := by
      rw [hEdef]; ring
    have h2 := congr(φ $h1)
    simp only [map_mul, map_add, map_sub, map_sum, map_one, hφrel, mul_zero,
      Finset.sum_const_zero, hφE, sub_zero, zero_add] at h2
    exact h2
  let Q' : Algebra.SubmersivePresentation (D.obj K) (D.obj K ⊗[D.obj j] M) ι σ :=
    { toPreSubmersivePresentation := Q, jacobian_isUnit := hQ }
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 (D.obj K) (D.obj K ⊗[D.obj j] M) :=
    Q'.isStandardSmoothOfRelativeDimension (by rw [← hP]; rfl)
  refine ⟨K, D.obj K ⊗[D.obj j] M, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  exact (Algebra.TensorProduct.cancelBaseChange (D.obj j) (D.obj K) c.pt c.pt M).trans
    (P.tensorModelOfHasCoeffsEquiv (D.obj j))

end GlobalTheory.EtaleDescent
