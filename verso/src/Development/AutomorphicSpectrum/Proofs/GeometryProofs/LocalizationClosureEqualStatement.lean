import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationClosureEqual
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitOfSumEqOne
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.locSub_eq_of_inverse_family` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FLocalizationClosureEqual.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.localization_closure_equal : ∀ {K : Type} [Field K] {Q : Type} [Fintype Q] (A B : Subring K) (t : Q → K), (∀ q, t q ≠ 0) → (∀ q, t q ∈ A) → (∀ q, (t q)⁻¹ ∈ B) → A ≤ Subring.closure ((B : Set K) ∪ Set.range t) → B ≤ Subring.closure ((A : Set K) ∪ Set.range fun q => (t q)⁻¹) → locSub A (∏ q, t q) = locSub B (∏ q, t q)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.locSub_eq_of_inverse_family | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.locSub_eq_of_inverse_family | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.locSub_eq_of_inverse_family <;> assumption)
