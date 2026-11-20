import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

/- English proof (translation)
Introduce `x hx`. Establish `hx' : χ.toIdele x = 1` using `h hx`. Use `show (χ⁻¹).toIdele x = 1`. Rewrite `hx'`, the goal using `[HeckeCharacter.toIdele_apply]`. Express the relevant statement in the definitionally equal form `(χ _)⁻¹ = 1`.

Rewrite using `[hx', inv_one]`.
-/
theorem standardOpenSubgroup_le_ker_inv (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F)
    (h : standardOpenSubgroup F ≤ χ.toIdele.ker) :
    standardOpenSubgroup F ≤ (χ⁻¹).toIdele.ker := by
  intro x hx
  have hx' : χ.toIdele x = 1 := h hx
  show (χ⁻¹).toIdele x = 1
  rw [HeckeCharacter.toIdele_apply] at hx' ⊢
  change (χ _)⁻¹ = 1
  rw [hx', inv_one]

end GlobalTheory.CompanionTheory.PartialZeta
