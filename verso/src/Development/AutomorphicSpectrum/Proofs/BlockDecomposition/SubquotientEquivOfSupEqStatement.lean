import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientEquivOfSupEq
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSubquotientEquivOfSupEq.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.subquotient_equiv_of_sup_eq : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (A B E : Subrepresentation ρ), E ≤ A → E ⊔ B = A → Nonempty ((subQuot E B).Equiv (subQuot A B)) := by
  first | exact @GlobalTheory.CompanionTheory.RepSecondIso.subQuot_equiv_of_sup | exact GlobalTheory.CompanionTheory.RepSecondIso.subQuot_equiv_of_sup | (intros; apply GlobalTheory.CompanionTheory.RepSecondIso.subQuot_equiv_of_sup <;> assumption)
