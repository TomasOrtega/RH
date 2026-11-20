import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFormCongrOfEventuallyEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsTorsionFormCongrOfEventuallyEq.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.isTorsionForm_congr_of_eventuallyEq : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (g n : ℕ) (τ τ' : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (b : E) (T : Ext (n + n)), τ =ᶠ[𝓝 b] τ' → IsTorsionForm τ M j h β b T → IsTorsionForm τ' M j h β b T := by
  first | exact @GlobalTheory.TorsionGerm.isTorsionForm_congr | exact GlobalTheory.TorsionGerm.isTorsionForm_congr | (intros; apply GlobalTheory.TorsionGerm.isTorsionForm_congr <;> assumption)
