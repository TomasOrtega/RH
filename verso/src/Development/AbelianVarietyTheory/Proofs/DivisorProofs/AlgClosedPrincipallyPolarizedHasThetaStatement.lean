import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgClosedPrincipallyPolarizedHasTheta
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThetaAlgClosed.hasTheta_of_isAlgClosed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAlgClosedPrincipallyPolarizedHasTheta.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.algClosed_principally_polarized_hasTheta : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (P : PPAS (Sp Ω)), P.HasTheta := by
  first | exact @GlobalTheory.ThetaAlgClosed.hasTheta_of_isAlgClosed | exact GlobalTheory.ThetaAlgClosed.hasTheta_of_isAlgClosed | (intros; apply GlobalTheory.ThetaAlgClosed.hasTheta_of_isAlgClosed <;> assumption)
