import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTotallyPositiveApproxAtFinitePlaces
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinPlaceApproxPos.approxpos_target` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsTotallyPositiveApproxAtFinitePlaces.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.exists_totallyPositive_approx_at_finite_places : ∀ (F : Type) [Field F] [NumberField F] (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) (t : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → F) (M : ℕ), ∃ a : F, (∀ v ∈ T, v.valuation F (a - t v) ≤ WithZero.exp (-(M : ℤ))) ∧ ∀ φ : F →+* ℝ, 0 < φ a := by
  first | exact @GlobalTheory.FinPlaceApproxPos.approxpos_target | exact GlobalTheory.FinPlaceApproxPos.approxpos_target | (intros; apply GlobalTheory.FinPlaceApproxPos.approxpos_target <;> assumption)
