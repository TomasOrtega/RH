import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExactKeyFormulaProofStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

namespace GlobalTheory.KeyFamClosing

/- English proof (translation)
The claim follows from `GlobalTheory.KeyFamOfExact.keyFam_of_keyFormula GlobalTheory.T.exactKeyFormula_proof`.
-/
theorem keyFam_one : KeyFam fun _ => 1 :=
  GlobalTheory.KeyFamOfExact.keyFam_of_keyFormula GlobalTheory.T.exactKeyFormula_proof

end GlobalTheory.KeyFamClosing
