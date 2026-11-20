import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.InfLifts
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2

/- English proof (translation)
Introduce `hS E Ω _ _ _ _ _ _ n hn π Y hY`. Proceed by induction on `hY with`. Consider the case `refl`. Introduce `τ`. Conclude with `congrArg (CG.mk π).infChar (RingHom.comp_id τ).symm`.

Consider the case `@tail Y Z _ hs ih`. Introduce `τ`. Take `⟨alg, tow, hG, hP, hW⟩` from `hs`. Establish `hcomp : (algebraMap Y.K Z.K).comp (algebraMap E Y.K) = algebraMap E Z.K`. Use extensionality with `x`.

Apply `(algebraMap Z.K Ω).injective` to reduce the goal to its premises. Rewrite using `[RingHom.comp_apply, ← IsScalarTower.algebraMap_apply Y.K Z.K Ω, ← IsScalarTower.algebraMap_apply E Y.K Ω, ← IsScalarTower.algebraMap_apply E Z.K Ω]`. Rewrite using `[hS Y.K Z.K hP n hn Y.π Z.π hW τ, ih (τ.comp (algebraMap Y.K Z.K)), RingHom.comp_assoc, hcomp]`.
-/
theorem UpperTheory.Gal.ToralGalois.R2.infLifts :
    InfStep → InfLifts := by
  intro hS E Ω _ _ _ _ _ _ n hn π Y hY
  induction hY with
  | refl =>
    intro τ
    exact congrArg (CG.mk π).infChar (RingHom.comp_id τ).symm
  | @tail Y Z _ hs ih =>
    intro τ
    obtain ⟨alg, tow, hG, hP, hW⟩ := hs
    have hcomp : (algebraMap Y.K Z.K).comp (algebraMap E Y.K) = algebraMap E Z.K := by
      ext x
      apply (algebraMap Z.K Ω).injective
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply Y.K Z.K Ω,
        ← IsScalarTower.algebraMap_apply E Y.K Ω, ← IsScalarTower.algebraMap_apply E Z.K Ω]
    rw [hS Y.K Z.K hP n hn Y.π Z.π hW τ, ih (τ.comp (algebraMap Y.K Z.K)), RingHom.comp_assoc, hcomp]
