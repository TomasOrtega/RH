import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgClosedPrincipallyPolarizedHasTheta
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.ThetaAlgClosed.hasTheta_of_isAlgClosed | exact GlobalTheory.ThetaAlgClosed.hasTheta_of_isAlgClosed | (intros; apply GlobalTheory.ThetaAlgClosed.hasTheta_of_isAlgClosed <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.algClosed_principally_polarized_hasTheta : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (P : PPAS (Sp Ω)), P.HasTheta := by
  first | exact @GlobalTheory.ThetaAlgClosed.hasTheta_of_isAlgClosed | exact GlobalTheory.ThetaAlgClosed.hasTheta_of_isAlgClosed | (intros; apply GlobalTheory.ThetaAlgClosed.hasTheta_of_isAlgClosed <;> assumption)
