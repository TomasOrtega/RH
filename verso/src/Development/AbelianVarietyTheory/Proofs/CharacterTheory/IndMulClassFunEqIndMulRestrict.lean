import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.BI

/- English proof (translation)
Introduce `G _ _ H ψ φ hφ`. Use function extensionality and compare the values at `g`. Establish `key : ∀ x : G, ext0 H (fun h => ψ h * φ h) (x⁻¹ * g * x) = ext0 H ψ (x⁻¹ * g * x) * φ g`. Introduce `x`. Rewrite using `[← hφ g x]`.

Unfold `ext0`. Apply the tactic sequence `split_ifs <;> simp`. Simplify using `only [Pi.mul_apply, ind]`. Repeatedly rewrite using `[key]`. Rewrite using `[mul_assoc, finsum_mul]`.
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
