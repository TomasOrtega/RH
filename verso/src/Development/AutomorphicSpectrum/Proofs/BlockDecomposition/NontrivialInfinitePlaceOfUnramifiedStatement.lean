import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialInfinitePlaceOfUnramified
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNontrivialInfinitePlaceOfUnramified.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.nontrivial_infinite_place_of_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → Nontrivial (InfinitePlace E) := by
  first | exact @GlobalTheory.CompanionTheory.UnrCM.nontrivial_infinitePlace | exact GlobalTheory.CompanionTheory.UnrCM.nontrivial_infinitePlace | (intros; apply GlobalTheory.CompanionTheory.UnrCM.nontrivial_infinitePlace <;> assumption)
