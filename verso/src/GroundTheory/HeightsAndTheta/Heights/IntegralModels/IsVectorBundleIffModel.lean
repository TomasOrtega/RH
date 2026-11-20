import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

open CategoryTheory Opposite AlgebraicGeometry Limits

noncomputable section

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
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
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
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
