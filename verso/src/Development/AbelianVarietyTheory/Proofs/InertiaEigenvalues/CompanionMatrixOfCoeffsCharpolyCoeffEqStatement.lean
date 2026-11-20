import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompanionMatrixOfCoeffsCharpolyCoeffEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.JR Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCompanionMatrixOfCoeffsCharpolyCoeffEq.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.companionMatrixOfCoeffs_charpoly_coeff_eq : ∀ (k : Type) [CommRing k] (r : ℕ) (p : Fin r → k) (i : Fin r), (companion p).charpoly.coeff (i : ℕ) = p i := by
  first | exact @GlobalTheory.JR.CompanionCharpoly.charpoly_companion_coeff_ring | exact GlobalTheory.JR.CompanionCharpoly.charpoly_companion_coeff_ring | (intros; apply GlobalTheory.JR.CompanionCharpoly.charpoly_companion_coeff_ring <;> assumption)
