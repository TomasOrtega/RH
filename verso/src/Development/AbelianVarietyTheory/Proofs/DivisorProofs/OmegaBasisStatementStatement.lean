import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutsSecOfIsLat
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory.LineNorm (IsTanBasis)
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)
open GlobalTheory.OmegaHT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FOmegaBasisStatement.lean&line=185#L185)
-/
theorem _root_.GlobalTheory.T.OmegaBasisStatement : GlobalTheory.OmegaHT.BasisSt := by
  first | exact @GlobalTheory.OmegaHT.RankForms.basisSt | exact GlobalTheory.OmegaHT.RankForms.basisSt | (intros; apply GlobalTheory.OmegaHT.RankForms.basisSt <;> assumption)
