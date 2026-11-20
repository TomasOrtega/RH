import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedOfHeightOneLocalizations
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.associated_of_associated_at_height_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FAssociatedOfHeightOneLocalizations.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.associated_of_height_one_localizations : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (a b : A), a ≠ 0 → b ≠ 0 → (∀ (q : Ideal A) [q.IsPrime], q.height = 1 → Associated (algebraMap A (Localization.AtPrime q) a) (algebraMap A (Localization.AtPrime q) b)) → Associated a b := by
  first | exact @GlobalTheory.associated_of_associated_at_height_one | exact GlobalTheory.associated_of_associated_at_height_one | (intros; apply GlobalTheory.associated_of_associated_at_height_one <;> assumption)
