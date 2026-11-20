import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrBasisMemOfIsLocalRingOfVarietyPoint
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FieldPair.exists_trBasis_mem_of_isLocModel` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsTrBasisMemOfIsLocalRingOfVarietyPoint.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.exists_trBasis_mem_of_isLocalRingOfVarietyPoint : ∀ {K : Type} [Field K] (c : ℂ →+* K) (R : Subring K) (n : ℕ), IsLocModel c R →
    (∃ x : Fin n → K, TrBasis c x) → ∃ xi : Fin n → R, TrBasis c (fun j => (xi j : K)) := by
  first | exact @GlobalTheory.FieldPair.exists_trBasis_mem_of_isLocModel | exact GlobalTheory.FieldPair.exists_trBasis_mem_of_isLocModel | (intros; apply GlobalTheory.FieldPair.exists_trBasis_mem_of_isLocModel <;> assumption)
