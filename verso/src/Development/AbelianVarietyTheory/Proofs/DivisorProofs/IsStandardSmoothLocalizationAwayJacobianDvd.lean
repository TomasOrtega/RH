import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

/- English proof (translation)
Use `set A := MvPolynomial ν R ⧸ Ideal.span (Set.range F)`. Use `set T := Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)`. Set `P` to `Algebra.PreSubmersivePresentation.naive (v := F) m hm`. Set `Q` to `Algebra.SubmersivePresentation.localizationAway T (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)`. Establish `hPjac : P.jacobian = Ideal.Quotient.mk (Ideal.span (Set.range F)) (Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t)).det`.

Rewrite using `[P.jacobian_eq_jacobiMatrix_det, Algebra.Generators.algebraMap_apply]`. Establish `hM : P.jacobiMatrix = Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t)`. Use extensionality with `i j`. Simplify using `[P]`. Rewrite using `[hM]`.

Establish `: MvPolynomial.aeval P.val = Ideal.Quotient.mkₐ R (Ideal.span (Set.range F))` using `MvPolynomial.algHom_ext fun v => by simp [P]`. Rewrite using `[this]`. Both sides reduce to the same expression. Set `P' : Algebra.SubmersivePresentation R T (Unit ⊕ ν) (Unit ⊕ σ)` to `{ __ := Q.toPreSubmersivePresentation.comp P jacobian_isUnit := by`. Rewrite using `[Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian, Algebra.smul_def]`.

Use `IsUnit.mul ?_ Q.jacobian_isUnit` and prove the remaining obligations. Rewrite using `[hPjac]`. Conclude with `isUnit_of_dvd_unit (map_dvd _ (map_dvd _ hdvd)) (IsLocalization.Away.algebraMap_isUnit _) }`. Use `P'.isStandardSmoothOfRelativeDimension ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Q.toPreSubmersivePresentation.comp P).dimension = _`.

Rewrite using `[Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]`. Simplify using `[Algebra.Presentation.dimension, P]`.
-/
theorem isStandardSmoothOfRelativeDimension_localizationAway_of_det_dvd
    (R ν σ : Type) [CommRing R] [Finite ν] [Fintype σ] [DecidableEq σ] (m : σ → ν)
    (hm : Function.Injective m) (F : σ → MvPolynomial ν R) (h : MvPolynomial ν R)
    (hdvd : (Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t)).det ∣ h) :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ν - Nat.card σ) R
      (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)) := by
  classical
  set A := MvPolynomial ν R ⧸ Ideal.span (Set.range F)
  set T := Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)
  let P := Algebra.PreSubmersivePresentation.naive (v := F) m hm
  let Q := Algebra.SubmersivePresentation.localizationAway T
    (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)
  have hPjac : P.jacobian = Ideal.Quotient.mk (Ideal.span (Set.range F))
      (Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t)).det := by
    rw [P.jacobian_eq_jacobiMatrix_det, Algebra.Generators.algebraMap_apply]
    have hM : P.jacobiMatrix = Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t) := by
      ext i j
      simp [P]
    rw [hM]
    have : MvPolynomial.aeval P.val = Ideal.Quotient.mkₐ R (Ideal.span (Set.range F)) :=
      MvPolynomial.algHom_ext fun v => by simp [P]
    rw [this]
    rfl
  let P' : Algebra.SubmersivePresentation R T (Unit ⊕ ν) (Unit ⊕ σ) :=
    { __ := Q.toPreSubmersivePresentation.comp P
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.smul_def]
        refine IsUnit.mul ?_ Q.jacobian_isUnit
        rw [hPjac]
        exact isUnit_of_dvd_unit (map_dvd _ (map_dvd _ hdvd))
          (IsLocalization.Away.algebraMap_isUnit _) }
  refine P'.isStandardSmoothOfRelativeDimension ?_
  change (Q.toPreSubmersivePresentation.comp P).dimension = _
  rw [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
  simp [Algebra.Presentation.dimension, P]

end GlobalTheory.Pinch
