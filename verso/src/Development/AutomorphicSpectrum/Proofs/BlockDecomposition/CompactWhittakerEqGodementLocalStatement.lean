import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactWhittakerEqGodementLocal
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCompactWhittakerEqGodementLocal.lean&line=234#L234)
-/
theorem _root_.GlobalTheory.T.compact_whittaker_eq_godement_local : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ c₁ c₂ : Fˣ →* ℂˣ, IsUnit1 c₁ → IsUnit1 c₂ → ∀ Φ : F × F → ℂ, IsLocallyConstant Φ → HasCompactSupport Φ → ∃ φ ∈ GodementSectionLocal.schwartzBruhat2 F, GL2LocalData.WcS χ c₁ c₂ Φ = W2 χ c₂ c₁ φ := by
  first | exact @GlobalTheory.CompanionTheory.WcSplit.compact_whittaker_eq_godement | exact GlobalTheory.CompanionTheory.WcSplit.compact_whittaker_eq_godement | (intros; apply GlobalTheory.CompanionTheory.WcSplit.compact_whittaker_eq_godement <;> assumption)
