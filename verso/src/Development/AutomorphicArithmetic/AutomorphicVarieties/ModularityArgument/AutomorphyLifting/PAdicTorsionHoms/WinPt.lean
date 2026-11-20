import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PlainAtR
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PlainIff

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Gam UpperTheory.V.Z.Win
open GroundTheory.Global.SemiLocal UpperTheory.V.Published

/- English proof (translation)
Introduce `_ hW K _ _ _ n hn π`. Take `⟨t, ht⟩` from `hW K n hn π`. Use `⟨t, fun v h => ?_⟩` and prove the remaining obligations. Establish `e` using `(UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.plainIff K n hn π v).1 h`. Conclude with `ht v e.1 e.2`.
-/
theorem UpperTheory.V.Z.Win.winPt :
    Z.Gam.SuppFacts → ImaginaryQuadraticEtaCharacter.WinOf → WinPt := by
  intro _ hW K _ _ _ n hn π
  obtain ⟨t, ht⟩ := hW K n hn π
  refine ⟨t, fun v h => ?_⟩
  have e := (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.plainIff K n hn π v).1 h
  exact ht v e.1 e.2
