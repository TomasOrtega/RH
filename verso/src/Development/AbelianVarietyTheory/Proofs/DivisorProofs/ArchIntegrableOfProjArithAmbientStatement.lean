import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrableOfProjArithAmbient
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MixHt.archIntegrable_of_isAmb` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FArchIntegrableOfProjArithAmbient.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.archIntegrable_of_projArithAmbient : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ (M N : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), N.ArchIntegrable M e hr := by
  first | exact @GlobalTheory.MixHt.archIntegrable_of_isAmb | exact GlobalTheory.MixHt.archIntegrable_of_isAmb | (intros; apply GlobalTheory.MixHt.archIntegrable_of_isAmb <;> assumption)
