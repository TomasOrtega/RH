import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KaehlerRelationOfDerivationOnLargeSubalgebra
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
open GlobalTheory.AlmostEt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FKaehlerRelationOfDerivationOnLargeSubalgebra.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.kaehler_relation_of_derivation_on_large_subalgebra : ∀ (A S : Type) [CommRing A] [CommRing S] [Algebra A S] (n : ℕ) (x y : Fin n → S), ∑ i, x i • KaehlerDifferential.D A S (y i) = 0 → ∃ T : Finset S, ∀ C : Subalgebra A S, (↑T : Set S) ⊆ C → (∀ i, y i ∈ C) → ∀ (M : Type) [AddCommGroup M] [Module S M] (D : S → M), IsDerOn C D → ∑ i, x i • D (y i) = 0 := by
  first | exact @GlobalTheory.AlmostEt.kaehler_rel_local | exact GlobalTheory.AlmostEt.kaehler_rel_local | (intros; apply GlobalTheory.AlmostEt.kaehler_rel_local <;> assumption)
