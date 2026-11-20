import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.BI

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem ind_mul_classFun_eq_ind_mul_restrict :
    ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → ℂ) (φ : G → ℂ),
      (∀ g x : G, φ (x⁻¹ * g * x) = φ g) → ind H ψ * φ = ind H (fun h => ψ h * φ h) := by
  intro G _ _ H ψ φ hφ
  funext g
  have key : ∀ x : G, ext0 H (fun h => ψ h * φ h) (x⁻¹ * g * x) = ext0 H ψ (x⁻¹ * g * x) * φ g := by
    intro x
    rw [← hφ g x]
    unfold ext0
    split_ifs <;> simp
  simp only [Pi.mul_apply, ind]
  simp_rw [key]
  rw [mul_assoc, finsum_mul]

end GlobalTheory.BI
