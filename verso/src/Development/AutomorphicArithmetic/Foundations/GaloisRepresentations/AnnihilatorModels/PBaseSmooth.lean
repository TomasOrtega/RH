import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `hC hR l O R _ _ _ _ _ _ ϖ hϖ hl _`. Establish `hflat : Module.Flat O R` using `Algebra.Smooth.flat O R`. Establish `hlO : (l : O) ∈ nonZeroDivisors O` using `mem_nonZeroDivisors_of_ne_zero hl`. Use `⟨?_, hC l O R hl, ?_⟩` and prove the remaining obligations. Establish `hreg : IsSMulRegular R (l : O)` using `Module.Flat.isSMulRegular_of_nonZeroDivisors hlO`.

Establish `key : ∀ x : R, (l : R) * x = 0 → x = 0`. Introduce `x hx`. Apply `hreg` to reduce the goal to its premises. Simplify using `only [Algebra.smul_def, map_natCast, mul_zero]`. Conclude with `hx`.

Rewrite using `[mem_nonZeroDivisors_iff]`. Conclude with `⟨key, fun x hx => key x (by rw [mul_comm]; exact hx)⟩`. Rewrite using `[Ideal.isRadical_iff_quotient_reduced]`. Establish `hspan : Ideal.span {(algebraMap O R) ϖ} = (IsLocalRing.maximalIdeal O).map (algebraMap O R)`. Rewrite using `[(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span, Set.image_singleton]`.

Rewrite using `[hspan]`. Use `haveI : Algebra.Smooth (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] R) := Algebra.Smooth.baseChange O R (IsLocalRing.ResidueField O)`. Establish `hred : IsReduced (IsLocalRing.ResidueField O ⊗[O] R)` using `hR (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] R)`. Use `haveI : IsReduced ((O ⧸ IsLocalRing.maximalIdeal O) ⊗[O] R) := hred`. Set `e` to `((Algebra.TensorProduct.quotIdealMapEquivTensorQuot R (IsLocalRing.maximalIdeal O)).restrictScalars O).trans (Algebra.TensorProduct.comm O R (O ⧸ IsLocalRing.maximalIdeal O))`.

Conclude with `isReduced_of_injective e.toRingHom e.injective`.
-/
theorem UpperTheory.Gal.crystallineComparison.baseSmooth_of :
    SmoothClosed → SmoothReduced → BaseOfSmooth := by
  intro hC hR l O R _ _ _ _ _ _ ϖ hϖ hl _
  have hflat : Module.Flat O R := Algebra.Smooth.flat O R
  have hlO : (l : O) ∈ nonZeroDivisors O := mem_nonZeroDivisors_of_ne_zero hl
  refine ⟨?_, hC l O R hl, ?_⟩
  · have hreg : IsSMulRegular R (l : O) := Module.Flat.isSMulRegular_of_nonZeroDivisors hlO
    have key : ∀ x : R, (l : R) * x = 0 → x = 0 := by
      intro x hx
      apply hreg
      simp only [Algebra.smul_def, map_natCast, mul_zero]
      exact hx
    rw [mem_nonZeroDivisors_iff]
    exact ⟨key, fun x hx => key x (by rw [mul_comm]; exact hx)⟩
  · rw [Ideal.isRadical_iff_quotient_reduced]
    have hspan : Ideal.span {(algebraMap O R) ϖ} = (IsLocalRing.maximalIdeal O).map (algebraMap O R) := by
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span, Set.image_singleton]
    rw [hspan]
    haveI : Algebra.Smooth (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] R) :=
      Algebra.Smooth.baseChange O R (IsLocalRing.ResidueField O)
    have hred : IsReduced (IsLocalRing.ResidueField O ⊗[O] R) :=
      hR (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] R)
    haveI : IsReduced ((O ⧸ IsLocalRing.maximalIdeal O) ⊗[O] R) := hred
    let e := ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot R (IsLocalRing.maximalIdeal O)).restrictScalars O).trans
      (Algebra.TensorProduct.comm O R (O ⧸ IsLocalRing.maximalIdeal O))
    exact isReduced_of_injective e.toRingHom e.injective
