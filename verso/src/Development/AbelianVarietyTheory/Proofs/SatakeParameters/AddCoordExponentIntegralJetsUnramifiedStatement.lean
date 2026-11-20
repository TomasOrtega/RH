import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AddCoordExponentIntegralJetsUnramified
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AddJet.addC_integral_jets` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FAddCoordExponentIntegralJetsUnramified.lean&line=437#L437)
-/
theorem _root_.GlobalTheory.T.addCoord_exponent_integral_jets_unramified : ∀ (l : ℕ) [Fact l.Prime] (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)), UnrOK (MaximalUnramifiedExtension l) l σ → IsLawOfLog l F → F1 F be0 → F2 l σ be0 → ∀ n : Fin 2 →₀ ℕ, ‖(((n 0).factorial * (n 1).factorial : ℕ) : MaximalUnramifiedExtension l) * MvPowerSeries.coeff n (addC l be0)‖ ≤ 1 := by
  first | exact @GlobalTheory.AddJet.addC_integral_jets | exact GlobalTheory.AddJet.addC_integral_jets | (intros; apply GlobalTheory.AddJet.addC_integral_jets <;> assumption)
