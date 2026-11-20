import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimAddOneLeOfSsubset
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTopologicalKrullDimAddOneLeOfSsubset.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.topologicalKrullDim_add_one_le_of_irreducible_ssubset : ∀ (T : Type) [TopologicalSpace T] (A B : Set T), IsClosed A → IsIrreducible A → IsIrreducible B → A ⊂ B → topologicalKrullDim A + 1 ≤ topologicalKrullDim B := by
  first | exact @GlobalTheory.topologicalKrullDim_add_one_le_of_ssubset | exact GlobalTheory.topologicalKrullDim_add_one_le_of_ssubset | (intros; apply GlobalTheory.topologicalKrullDim_add_one_le_of_ssubset <;> assumption)
