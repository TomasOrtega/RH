import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KoszulSyzygyAntisymmetricCoefficients
open MvPolynomial Finset
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKoszulSyzygyAntisymmetricCoefficients.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.koszul_syzygy_antisymmetric_coefficients : ∀ (A : Type) [CommRing A] (r : ℕ) (G : Fin r → MvPolynomial (Fin r) A), ∑ i, X i * G i = 0 → ∃ H : Fin r → Fin r → MvPolynomial (Fin r) A, (∀ i j, H i j = -H j i) ∧ (∀ i, H i i = 0) ∧ ∀ i, G i = ∑ j, X j * H i j := by
  first | exact @GlobalTheory.koszul_relations_among_variables | exact GlobalTheory.koszul_relations_among_variables | (intros; apply GlobalTheory.koszul_relations_among_variables <;> assumption)
