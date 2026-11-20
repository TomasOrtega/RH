import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaFourierCoefficientHasSum
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FexTheta.hasSum_aT` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FThetaFourierCoefficientHasSum.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.theta_fourier_coefficient_hasSum : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (c : HeckeCharacter K)
  (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v), AdmM M → ∀ (Sv : Finset Pl) (m : Pl →₀ ℤ), ∀ g ∈ Gp M,
    HasSum (fun ξ : K => aT n t M Sv g m ξ) (∫ u, ctM M Sv m u * thP n t (twM M Sv m u) g ∂muU Sv) := by
  first | exact @GlobalTheory.CompanionTheory.FexTheta.hasSum_aT | exact GlobalTheory.CompanionTheory.FexTheta.hasSum_aT | (intros; apply GlobalTheory.CompanionTheory.FexTheta.hasSum_aT <;> assumption)
