import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPlaceBranchExists
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPlaceOnComponent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimePlaceBranchExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

/- English proof (translation)
Introduce `n I q hrad hdim P`. Take `⟨J, hJ, -, hdimJ, P', hP'⟩` from `h₁ n I q hrad hdim P`. Take `⟨ν, hν⟩` from `h₂ n J q hJ.1.1 hdimJ P'`. Set `ν' : VarBranch I 1 q` to `{ radius := ν.radius, radius_pos := ν.radius_pos, toFun := ν.toFun, differentiableOn := ν.differentiableOn, injOn := ν.injOn, map_zero := ν.map_zero, mapsTo := fun t ht g hg ↦ ν.mapsTo ht g (hJ.1.2 hg) }`. Establish `hord : ∀ f, branchOrder ν' f = branchOrder ν f` using `fun _ ↦ rfl`.

Conclude with `⟨ν', fun f ↦ (hP' f).trans ((hν f).trans (hord f).symm)⟩`.
-/
theorem PlaceBranchExists.proof (h₁ : PlaceOnComponent.Statement) (h₂ : PrimePlaceBranchExists.Statement) :
    PlaceBranchExists.Statement := by
  intro n I q hrad hdim P
  obtain ⟨J, hJ, -, hdimJ, P', hP'⟩ := h₁ n I q hrad hdim P
  obtain ⟨ν, hν⟩ := h₂ n J q hJ.1.1 hdimJ P'

  let ν' : VarBranch I 1 q :=
    { radius := ν.radius, radius_pos := ν.radius_pos, toFun := ν.toFun, differentiableOn := ν.differentiableOn,
      injOn := ν.injOn, map_zero := ν.map_zero,
      mapsTo := fun t ht g hg ↦ ν.mapsTo ht g (hJ.1.2 hg) }
  have hord : ∀ f, branchOrder ν' f = branchOrder ν f := fun _ ↦ rfl
  exact ⟨ν', fun f ↦ (hP' f).trans ((hν f).trans (hord f).symm)⟩

end GroundTheory.Heights₂.Heights
