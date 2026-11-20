import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldOfUniquePrimeStalk
import Mathlib
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsFieldOfUniquePrimeStalk.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.isField_of_unique_prime_stalk : ∀ (R : CommRingCat.{0}) (q : Spec R), (∀ q' : Spec R, q' = q) → IsField ((Spec R).presheaf.stalk q) → IsField R := by
  first | exact @GlobalTheory.isField_of_spec_singleton_stalk_isField | exact GlobalTheory.isField_of_spec_singleton_stalk_isField | (intros; apply GlobalTheory.isField_of_spec_singleton_stalk_isField <;> assumption)
