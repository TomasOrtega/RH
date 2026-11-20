import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GramLogUnitaryTriangularInvariance
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.PB.flagDomain_open_and_minors` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FGramLogUnitaryTriangularInvariance.lean&line=145#L145)
-/
theorem _root_.GlobalTheory.T.isOpen_flag_domain_nondegenerate_minors : ∀ (N j : ℕ), j ≤ N → IsOpen {g : Matrix (Fin N) (Fin N) ℂ | InFlagDomain N j g} ∧ ∀ g : Matrix (Fin N) (Fin N) ℂ, InFlagDomain N j g → ∀ k, (gramHead (sigForm N j) k g).det ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.flagDomain_open_and_minors | exact GlobalTheory.CompanionTheory.Ar.PB.flagDomain_open_and_minors | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.flagDomain_open_and_minors <;> assumption)
