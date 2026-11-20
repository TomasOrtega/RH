import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FrobeniusSplittingClosed
open GlobalTheory GlobalTheory.DI
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FWeilBound%2FCoreStatements%2FPublishedTheorems%2FNadelVanishingPairs%2FNadelVanishingLemmas%2FFrobeniusSplittingClosed.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.frobenius_splitting_closed : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K) (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)), IsOddDer d → IsDatum p d f h → IsPhi p f h Φ → (∀ x, Φ x ∅ = 0) ∧ ∀ x, Dtot d (Φ x) = 0 := by
  first | exact @_root_.GlobalTheory.DI.phi_closed | exact _root_.GlobalTheory.DI.phi_closed | (intros; apply _root_.GlobalTheory.DI.phi_closed <;> assumption)
