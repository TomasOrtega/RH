import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTriplesTorsion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.PelSt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.LN.pelSt_holds | exact GlobalTheory.LN.pelSt_holds | (intros; apply GlobalTheory.LN.pelSt_holds <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.linearUniformisation_triples_torsion : GlobalTheory.LN.PelSt := by
  first | exact @GlobalTheory.LN.pelSt_holds | exact GlobalTheory.LN.pelSt_holds | (intros; apply GlobalTheory.LN.pelSt_holds <;> assumption)
