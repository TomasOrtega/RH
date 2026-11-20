import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointHTOfFarguesHodgeTate
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FPointHTOfFarguesHodgeTate.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.pointHT_of_fargues_hodge_tate : FarguesHodgeTate → PointHT := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.Fargues.pointHT | exact GlobalTheory.CompanionTheory.Ar.HT.Fargues.pointHT | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.Fargues.pointHT <;> assumption)
