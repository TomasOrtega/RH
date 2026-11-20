import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallResidueFieldFunctional
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEqZeroOfForallResidueFieldFunctional.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.eq_zero_of_forall_residueField_functional' : ∀ (A M : Type) [CommRing A] [IsReduced A] [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M] (x : M), (∀ (p : Ideal A) [p.IsPrime] (l : M →ₗ[A] p.ResidueField), l x = 0) → x = 0 := by
  first | exact @GlobalTheory.eq_zero_of_forall_residueField_functional | exact GlobalTheory.eq_zero_of_forall_residueField_functional | (intros; apply GlobalTheory.eq_zero_of_forall_residueField_functional <;> assumption)
