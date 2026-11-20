import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FinitePresentationOfFaithfullyFlat

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FFinitePresentationOfFaithfullyFlat.lean&line=131#L131)
-/
theorem _root_.GlobalTheory.T.finitePresentation_of_faithfully_flat : ∀ (R C D : Type) [CommRing R] [CommRing C] [CommRing D] [Algebra R C] [Algebra C D] [Algebra R D] [IsScalarTower R C D], Module.Finite C D → Module.Projective C D → Module.FaithfullyFlat C D → Algebra.FinitePresentation R D → Algebra.FinitePresentation R C := by
  first | exact @GlobalTheory.CompanionTheory.FinPresDescent.finitePresentation_of_finite_projective_faithfullyFlat | exact GlobalTheory.CompanionTheory.FinPresDescent.finitePresentation_of_finite_projective_faithfullyFlat | (intros; apply GlobalTheory.CompanionTheory.FinPresDescent.finitePresentation_of_finite_projective_faithfullyFlat <;> assumption)
