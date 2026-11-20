import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsNilpotentTmulSubTmulOfConstOnFibres
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FIsNilpotentTmulSubTmulOfConstOnFibres.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.isNilpotent_tmul_sub_tmul_of_const_on_fibres' : ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra ℂ B] [Algebra ℂ A] [Algebra B A] [IsScalarTower ℂ B A] [Algebra.FiniteType ℂ A] (f : A), (∀ χ χ' : A →ₐ[ℂ] ℂ, (∀ b : B, χ (algebraMap B A b) = χ' (algebraMap B A b)) → χ f = χ' f) → IsNilpotent (f ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] f) := by
  first | exact @GlobalTheory.ClassFin.isNilpotent_tmul_sub_tmul_of_const_on_fibres | exact GlobalTheory.ClassFin.isNilpotent_tmul_sub_tmul_of_const_on_fibres | (intros; apply GlobalTheory.ClassFin.isNilpotent_tmul_sub_tmul_of_const_on_fibres <;> assumption)
