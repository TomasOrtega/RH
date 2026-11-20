import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.PtLawsOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.IneInf

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Z.Win

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem UpperTheory.V.Keep.infCyc :
    UpperTheory.V.Keep.InfCyc := by
  intro F Ω _ _ _ _ _ l _ A hA U hU
  obtain ⟨s, hsU, hsI, hs⟩ := UpperTheory.V.Z.Sym.Ga.ineInf F Ω l A hA U hU
  exact ⟨s, ⟨hsU, hsI⟩, hs⟩
