import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KillingElementPullback
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfHomPull
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MixedLocalChains.Pres.kills_pull` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKillingElementPullback.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.killing_element_pullback : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (P : Pres B) (g : Γ(B.X, ⊤)), Kills g P.mod → Kills (f.f.appTop g) (P.pull f).mod := by
  first | exact @GlobalTheory.MixedLocalChains.Pres.kills_pull | exact GlobalTheory.MixedLocalChains.Pres.kills_pull | (intros; apply GlobalTheory.MixedLocalChains.Pres.kills_pull <;> assumption)
