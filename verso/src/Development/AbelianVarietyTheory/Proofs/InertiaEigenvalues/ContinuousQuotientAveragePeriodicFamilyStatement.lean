import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousQuotientAveragePeriodicFamily
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspGeneric.continuous_avg_of_periodic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FContinuousQuotientAveragePeriodicFamily.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.continuous_quotientAverage_periodic_family : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ (X : Type) [TopologicalSpace X] (F : X × G → ℂ), Continuous F → (∀ x, ∀ γ ∈ Γ, ∀ y, F (x, γ + y) = F (x, y)) → Continuous fun x => avg Γ (fun y => F (x, y)) := by
  first | exact @GlobalTheory.CuspGeneric.continuous_avg_of_periodic | exact GlobalTheory.CuspGeneric.continuous_avg_of_periodic | (intros; apply GlobalTheory.CuspGeneric.continuous_avg_of_periodic <;> assumption)
