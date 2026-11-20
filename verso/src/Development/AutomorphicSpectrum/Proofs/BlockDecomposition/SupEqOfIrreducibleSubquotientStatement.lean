import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupEqOfIrreducibleSubquotient
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSupEqOfIrreducibleSubquotient.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.sup_eq_of_irreducible_subquotient : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (A B E : Subrepresentation ρ), B ≤ A → (subQuot A B).IsIrreducible → E ≤ A → ¬ E ≤ B → E ⊔ B = A := by
  first | exact @GlobalTheory.CompanionTheory.GenCore.sup_eq_of_isIrreducible_subQuot | exact GlobalTheory.CompanionTheory.GenCore.sup_eq_of_isIrreducible_subQuot | (intros; apply GlobalTheory.CompanionTheory.GenCore.sup_eq_of_isIrreducible_subQuot <;> assumption)
