import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemistableSpecialFibreProperty

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SemistableSpecial.special_fibre_isReduced` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSemistableSpecialFibreProperty.lean&line=90#L90)
-/
theorem _root_.GlobalTheory.T.semistable_special_fibre_property : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (m r : ℕ), 1 ≤ r → r ≤ m → IsReduced ((MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ}) ⧸ Ideal.span {algebraMap O (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ}) ϖ}) := by
  first | exact @GlobalTheory.CompanionTheory.SemistableSpecial.special_fibre_isReduced | exact GlobalTheory.CompanionTheory.SemistableSpecial.special_fibre_isReduced | (intros; apply GlobalTheory.CompanionTheory.SemistableSpecial.special_fibre_isReduced <;> assumption)
