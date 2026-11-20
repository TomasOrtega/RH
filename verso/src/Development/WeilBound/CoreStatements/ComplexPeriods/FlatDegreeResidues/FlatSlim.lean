import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlatDegreeStOfResKGaga
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GagaSections

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem FlatDegreeResidue.flatDegreeSt_of_resK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.FlatCore.FlatDegreeSt :=
  fun h => GlobalTheory.CompanionTheory.Ar.Br.flatDegreeSt_of_resK_gaga h GlobalTheory.CompanionTheory.Gaga.gagaSections
