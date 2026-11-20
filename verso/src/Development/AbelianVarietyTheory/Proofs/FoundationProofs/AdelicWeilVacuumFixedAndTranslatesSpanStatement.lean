import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdelicWeilVacuumFixedAndTranslatesSpan
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinWeil.Vacuum.vacuum_fixed_span` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FAdelicWeilVacuumFixedAndTranslatesSpan.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.adelicWeil_vacuum_fixed_and_translates_span : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA → ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), e0 ≠ 0 → ∃ h : e0 ∈ TTs D (tor0 D cc δ) N N', Fixes WA (latA D cc N N') ⟨e0, h⟩ ∧ Submodule.span ℂ (Set.range fun ζ => WA ζ ⟨e0, h⟩) = ⊤ := by
  first | exact @GlobalTheory.FinWeil.Vacuum.vacuum_fixed_span | exact GlobalTheory.FinWeil.Vacuum.vacuum_fixed_span | (intros; apply GlobalTheory.FinWeil.Vacuum.vacuum_fixed_span <;> assumption)
