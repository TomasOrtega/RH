import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveSpaceOrderArithVarietyFubiniStudyDegre
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PSpaceDeg.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FProjectiveSpaceOrderArithVarietyFubiniStudyDegre.lean&line=176#L176)
-/
theorem _root_.GlobalTheory.T.projectiveSpace_order_arithVariety_fubiniStudyDegree : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (D : ℕ), IsArithVar (PSpace.str k D) D ∧ gdeg (ProjSpace.hermitianTwistingSheaf k D) D = Nat.card (k →+* ℂ) ∧ Nat.card (k →+* ℂ) = Module.finrank ℤ k := by
  first | exact @GlobalTheory.PSpaceDeg.main | exact GlobalTheory.PSpaceDeg.main | (intros; apply GlobalTheory.PSpaceDeg.main <;> assumption)
