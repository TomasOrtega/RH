import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericSubquotientIffWhittakerQuotient
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGenericSubquotientIffWhittakerQuotient.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.generic_subquotient_iff_whittaker_quotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → ∀ A B : Subrepresentation ρ, B ≤ A → (IsGenericFor ψ (subQuot A B) ↔ ¬ A.toSubmodule ≤ B.toSubmodule ⊔ twKer ρ (unipB k (Fin N)) (whitChar ψ N)) := by
  first | exact @GlobalTheory.CompanionTheory.PRep.WhitQuot.isGenericFor_subQuot_iff | exact GlobalTheory.CompanionTheory.PRep.WhitQuot.isGenericFor_subQuot_iff | (intros; apply GlobalTheory.CompanionTheory.PRep.WhitQuot.isGenericFor_subQuot_iff <;> assumption)
