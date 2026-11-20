import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppOneEqZeroOfKernelIdealOfCompEqPrimeSmul
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PDivGroup.app_one_eq_zero_of_mem_kerIdeal_of_comp_eq_prime_smul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAppOneEqZeroOfKernelIdealOfCompEqPrimeSmul.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.app_one_eq_zero_of_kernel_ideal_of_comp_eq_prime_smul : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (G H : PDivGroup p R) (f : G ⟶ H) (g : H ⟶ G), g ≫ f = (p : ℤ_[p]) • 𝟙 H → ∀ a ∈ kerIdeal (f.app 1), g.app 1 a = 0 := by
  first | exact @GlobalTheory.PDivGroup.app_one_eq_zero_of_mem_kerIdeal_of_comp_eq_prime_smul | exact GlobalTheory.PDivGroup.app_one_eq_zero_of_mem_kerIdeal_of_comp_eq_prime_smul | (intros; apply GlobalTheory.PDivGroup.app_one_eq_zero_of_mem_kerIdeal_of_comp_eq_prime_smul <;> assumption)
