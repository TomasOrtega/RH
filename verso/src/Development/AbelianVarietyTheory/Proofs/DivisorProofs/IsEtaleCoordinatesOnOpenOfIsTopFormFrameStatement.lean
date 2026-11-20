import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenOfIsTopFormFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsEtaleCoordinatesOnOpenOfIsTopFormFrame.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.isEtaleCoordinatesOnOpen_of_isTopFormFrame : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (V : Y.Opens) (z : Fin n → Γ(Y, V)), IsFrame (dOn q z) → IsAffineOpen V ∧ IsEtCoord q V z := by
  first | exact @GlobalTheory.FrameEtale.isEtCoord_of_isFrame | exact GlobalTheory.FrameEtale.isEtCoord_of_isFrame | (intros; apply GlobalTheory.FrameEtale.isEtCoord_of_isFrame <;> assumption)
