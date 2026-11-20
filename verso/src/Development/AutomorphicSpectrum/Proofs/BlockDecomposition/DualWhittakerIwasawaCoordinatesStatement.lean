import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualWhittakerIwasawaCoordinates
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.DualHol.Coord.coords` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDualWhittakerIwasawaCoordinates.lean&line=113#L113)
-/
theorem _root_.GlobalTheory.T.dual_whittaker_iwasawa_coordinates : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (a b : Fˣ) (k : GL (Fin 2) F), k ∈ GLnLocal.integralGL F 2 → ∃ k₃ ∈ GLnLocal.integralGL F 3, ∃ k₂ ∈ GLnLocal.integralGL F 2, (∀ W : GL (Fin 3) F → ℂ, GL2LocalData.dW3 W (GL2LocalData.em (dg2 (a * b) b * k)) = W (dg 1 b⁻¹ (a * b)⁻¹ * k₃)) ∧ (∀ W' : GL (Fin 2) F → ℂ, GL2LocalData.dW2 W' (dg2 (a * b) b * k) = W' (dg2 b⁻¹ (a * b)⁻¹ * k₂)) := by
  first | exact @GlobalTheory.CompanionTheory.DualHol.Coord.coords | exact GlobalTheory.CompanionTheory.DualHol.Coord.coords | (intros; apply GlobalTheory.CompanionTheory.DualHol.Coord.coords <;> assumption)
