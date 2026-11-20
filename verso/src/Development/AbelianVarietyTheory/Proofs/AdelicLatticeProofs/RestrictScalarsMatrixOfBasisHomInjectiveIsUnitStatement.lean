import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RestrictScalarsMatrixOfBasisHomInjectiveIsUnit
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FRestrictScalarsMatrixOfBasisHomInjectiveIsUnit.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.restrictScalarsMatrixOfBasis_hom_injective_isUnit : ∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A), res b (1 : Matrix κ κ A) = 1 ∧ (∀ g h : Matrix κ κ A, res b (g * h) = res b g * res b h) ∧ Function.Injective (fun g : Matrix κ κ A => res b g) ∧ ∀ g : Matrix κ κ A, IsUnit (res b g).det → IsUnit g := by
  first | exact @GlobalTheory.ClassFin.res_one_mul_injective_isUnit | exact GlobalTheory.ClassFin.res_one_mul_injective_isUnit | (intros; apply GlobalTheory.ClassFin.res_one_mul_injective_isUnit <;> assumption)
