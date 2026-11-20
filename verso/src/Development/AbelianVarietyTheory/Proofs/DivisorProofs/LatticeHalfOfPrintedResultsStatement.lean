import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeHalfOfPublished
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatHalfSt
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
/- English proof (citation)
Apply `GlobalTheory.ChainPts.latHalfSt` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLatticeHalfOfPublished.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.lattice_half_of_hypotheses : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.PrismaticDieudonnePerfd → GlobalTheory.GroupBplus.GroupAllSt → LatHalfSt := by
  first | exact @GlobalTheory.ChainPts.latHalfSt | exact GlobalTheory.ChainPts.latHalfSt | (intros; apply GlobalTheory.ChainPts.latHalfSt <;> assumption)
