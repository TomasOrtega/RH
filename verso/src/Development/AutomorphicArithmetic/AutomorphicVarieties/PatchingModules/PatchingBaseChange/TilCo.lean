import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.BaseChangeResidueSurjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

/- English proof (translation)
Introduce `O O' _ _ _ _ _ _ _ R _ _ _`. Use `haveI hT := UpperTheory.V.CA.cl_bc O O' R`. Set `f : R →+* O' ⊗[O] R` to `(Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R).toRingHom`. Establish `hint : f.IsIntegral`. Introduce `x`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact f.isIntegralElem_zero`. Consider the case `tmul o r`. Establish `ho : IsIntegral O ((Algebra.TensorProduct.includeLeft : O' →ₐ[O] O' ⊗[O] R) o)` using `(Algebra.IsIntegral.isIntegral (R := O) o).map _`. Rewrite `ho` using `[Algebra.TensorProduct.includeLeft_apply]`.

Take `⟨p, hp, hpe⟩` from `ho`. Establish `h1 : f.IsIntegralElem (o ⊗ₜ[O] (1 : R))`. Use `⟨p.map (algebraMap O R), hp.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map]`. Establish `hc : f.comp (algebraMap O R) = algebraMap O (O' ⊗[O] R)` using `(Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R).comp_algebraMap`.

Rewrite using `[hc]`. Conclude with `hpe`. Establish `he : o ⊗ₜ[O] r = (o ⊗ₜ[O] (1 : R)) * f r` using `by show _ = _ * ((1 : O') ⊗ₜ[O] r)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[he]`.

Conclude with `RingHom.IsIntegralElem.mul f h1 f.isIntegralElem_map`. Consider the case `add x y hx hy => exact RingHom.IsIntegralElem.add f hx hy`. Establish `hloc : IsLocalHom f`. Use `((IsLocalRing.local_hom_TFAE f).out 0 4).mpr ?_` and prove the remaining obligations. Use `haveI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hint (maximalIdeal (O' ⊗[O] R))`.

Conclude with `IsLocalRing.eq_maximalIdeal this`. Use `haveI hco : IsCO O' (Til O O' R) := UpperTheory.V.Alg.co_mvps O' (O' ⊗[O] R) Unit`. Use `⟨hco, ?_, ?_⟩` and prove the remaining obligations. Use `⟨fun r hr => ?_⟩` and prove the remaining obligations. Establish `hr' : IsUnit (PowerSeries.C ((1 : O') ⊗ₜ[O] r) : PowerSeries (O' ⊗[O] R))` using `hr`.

Rewrite `hr'` using `[PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C]`. Conclude with `hloc.map_nonunit r hr'`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] show ¬ IsUnit (PowerSeries.X : PowerSeries (O' ⊗[O] R))`. Rewrite using `[PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]`. Conclude with `not_isUnit_zero`.
-/
theorem UpperTheory.V.Pa.BC.til_co :
    ∀ (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] (R : Type) [CommRing R] [Algebra O R] [IsCO O R], ∃ _ : IsCO O' (Til O O' R), IsLocalHom (Til.ι O O' R) ∧ Til.s O O' R ∈ maximalIdeal (Til O O' R) := by
  intro O O' _ _ _ _ _ _ _ R _ _ _
  haveI hT := UpperTheory.V.CA.cl_bc O O' R
  let f : R →+* O' ⊗[O] R := (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R).toRingHom
  have hint : f.IsIntegral := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact f.isIntegralElem_zero
    | tmul o r =>
      have ho : IsIntegral O ((Algebra.TensorProduct.includeLeft : O' →ₐ[O] O' ⊗[O] R) o) :=
        (Algebra.IsIntegral.isIntegral (R := O) o).map _
      rw [Algebra.TensorProduct.includeLeft_apply] at ho
      obtain ⟨p, hp, hpe⟩ := ho
      have h1 : f.IsIntegralElem (o ⊗ₜ[O] (1 : R)) := by
        refine ⟨p.map (algebraMap O R), hp.map _, ?_⟩
        rw [Polynomial.eval₂_map]
        have hc : f.comp (algebraMap O R) = algebraMap O (O' ⊗[O] R) :=
          (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R).comp_algebraMap
        rw [hc]
        exact hpe
      have he : o ⊗ₜ[O] r = (o ⊗ₜ[O] (1 : R)) * f r := by
        show _ = _ * ((1 : O') ⊗ₜ[O] r)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [he]
      exact RingHom.IsIntegralElem.mul f h1 f.isIntegralElem_map
    | add x y hx hy => exact RingHom.IsIntegralElem.add f hx hy
  have hloc : IsLocalHom f := by
    refine ((IsLocalRing.local_hom_TFAE f).out 0 4).mpr ?_
    haveI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hint (maximalIdeal (O' ⊗[O] R))
    exact IsLocalRing.eq_maximalIdeal this
  haveI hco : IsCO O' (Til O O' R) := UpperTheory.V.Alg.co_mvps O' (O' ⊗[O] R) Unit
  refine ⟨hco, ?_, ?_⟩
  · refine ⟨fun r hr => ?_⟩
    have hr' : IsUnit (PowerSeries.C ((1 : O') ⊗ₜ[O] r) : PowerSeries (O' ⊗[O] R)) := hr
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C] at hr'
    exact hloc.map_nonunit r hr'
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    show ¬ IsUnit (PowerSeries.X : PowerSeries (O' ⊗[O] R))
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
    exact not_isUnit_zero
