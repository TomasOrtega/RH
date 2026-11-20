import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

open CategoryTheory Opposite AlgebraicGeometry Limits

noncomputable section

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem isVectorBundle_iff_model {X : Scheme.{0}} (E : X.Modules) :
    GroundTheory.Heights₂.Heights.Model.IsVectorBundle E ↔ IsVectorBundle E := Iff.rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem genTo_eq_baseChangeMap (X : Scheme.{0}) :
    genTo X = GroundTheory.Heights₂.Heights.Model.baseChangeMap (toSpecZ X) ℚ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pbSection_eq_pullSection {A B : Scheme.{0}} (f : A ⟶ B) (M : B.Modules) (t : Γ(M, ⊤)) :
    pbSection f M t = GroundTheory.Heights₂.Heights.Model.pullSection f M t := rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h X _ _ hf L hL s`. Conclude with `h X (toSpecZ X) L hL s`. Introduce `h X f _ _ _ L hL s`. Take `rfl : f = toSpecZ X` from `specZ_hom_ext _ _`.

Conclude with `h X inferInstance L hL s`.
-/
theorem ClearDenominators.equiv :
    GroundTheory.Heights₂.Heights.Model.ClearDenominators.Statement ↔ ClearDenominators.Statement := by
  constructor
  · intro h X _ _ hf L hL s
    exact h X (toSpecZ X) L hL s
  · intro h X f _ _ _ L hL s
    obtain rfl : f = toSpecZ X := specZ_hom_ext _ _
    exact h X inferInstance L hL s

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
