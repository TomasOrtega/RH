import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensitySiegelPeriod
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FChernDensitySiegelPeriod.lean&line=155#L155)
-/
theorem _root_.GlobalTheory.T.chern_density_siegel_period : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (σ : k →+* ℂ) (P : PPAS S) (h : VMetric p (omega P.A) P.g) (H : h.IsCInf) (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ) (ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ), IsPeriodChart h c τ ex → ∀ y ∈ c.e.source, c.chernDens ((VMetric.det H).φ σ) y = sdens (τ (c.e y)) (tauU (fderiv ℂ (fun x => symPart (τ x)) (c.e y) (EuclideanSpace.single 0 1))) / (4 * Real.pi) := by
  first | exact @GlobalTheory.ThetaRR.HodgeDens.chernDens_det_omega | exact GlobalTheory.ThetaRR.HodgeDens.chernDens_det_omega | (intros; apply GlobalTheory.ThetaRR.HodgeDens.chernDens_det_omega <;> assumption)
