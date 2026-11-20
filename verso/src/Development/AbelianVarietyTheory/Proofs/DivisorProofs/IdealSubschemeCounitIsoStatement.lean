import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSubschemeCounitIso
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfHomPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrobCokernelSmulHomPow
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIdealSubschemeCounitIso.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.ideal_subscheme_counit_iso : ∀ {X : Scheme.{0}} (I : X.IdealSheafData) (G : I.subscheme.Modules) [G.IsQuasicoherent], IsIso ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).counit.app G) := by
  first | exact @GlobalTheory.QCoh.ClosedCounit.isIso_counit_subschemeι | exact GlobalTheory.QCoh.ClosedCounit.isIso_counit_subschemeι | (intros; apply GlobalTheory.QCoh.ClosedCounit.isIso_counit_subschemeι <;> assumption)
