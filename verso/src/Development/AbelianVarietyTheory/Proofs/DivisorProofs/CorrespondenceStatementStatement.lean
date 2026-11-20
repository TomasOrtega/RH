import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CorrespondenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCorrespondenceStatement.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.correspondence_statement : CorrSt := by
  first | exact @GlobalTheory.ShFam.GalCarry.corrSt | exact GlobalTheory.ShFam.GalCarry.corrSt | (intros; apply GlobalTheory.ShFam.GalCarry.corrSt <;> assumption)
