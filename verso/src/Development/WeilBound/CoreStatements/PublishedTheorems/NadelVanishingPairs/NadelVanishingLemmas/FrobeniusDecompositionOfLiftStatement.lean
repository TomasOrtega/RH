import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FrobeniusDecompositionOfLift
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier
/- English proof (citation)
Apply `GlobalTheory.LogDR.decomp_of_isLifted` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FWeilBound%2FCoreStatements%2FPublishedTheorems%2FNadelVanishingPairs%2FNadelVanishingLemmas%2FFrobeniusDecompositionOfLift.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.frobenius_decomposition_of_lift : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι), n < p → IsLifted p (suppAll E) 𝒜.U 𝒜.x → Decomp p 𝒜 := by
  first | exact @_root_.GlobalTheory.LogDR.decomp_of_isLifted | exact _root_.GlobalTheory.LogDR.decomp_of_isLifted | (intros; apply _root_.GlobalTheory.LogDR.decomp_of_isLifted <;> assumption)
