import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemistableGenericFibreLocalization

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSemistableGenericFibreLocalization.lean&line=158#L158)
-/
theorem _root_.GlobalTheory.T.semistable_generic_fibre_localization : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (m r : ℕ), 1 ≤ r → r ≤ m → ∀ (F : Type) [Field F] [Algebra O F] [IsLocalization.Away ϖ F], (IsLocalization.Away.map F (Localization.Away (algebraMap O (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ}) ϖ)) (algebraMap O (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ})) ϖ).Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Semistable.smooth_generic_fibre | exact GlobalTheory.CompanionTheory.Semistable.smooth_generic_fibre | (intros; apply GlobalTheory.CompanionTheory.Semistable.smooth_generic_fibre <;> assumption)
