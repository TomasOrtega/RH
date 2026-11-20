import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.DiscreteSeriesUpqUnique
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKTypeMultiplicityOneFock
import Formalism.SharpRestriction.CuspSpanNormBounds.HCFiniteKMultiplicityGapped
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FinalClosed

namespace CompanionTheory.DiscreteSeriesGap.GapInv

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dsUnique_dec : GlobalTheory.Dec.DSUnique :=
  GlobalTheory.Published.discreteSeriesUpqUnique_iff.1 GlobalTheory.CompanionTheory.Front.discreteSeriesUpqUnique

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lowKMultOne_dec : GlobalTheory.Dec.LowKMultOne := CompanionTheory.D.LK.low_K_type_multiplicity_one

end CompanionTheory.DiscreteSeriesGap.GapInv
