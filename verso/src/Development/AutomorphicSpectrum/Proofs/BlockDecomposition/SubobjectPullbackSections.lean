import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem secs_pullback_arrow {X : Scheme.{0}} {E : X.Modules} (D S : Subobject E) (V : X.Opens) :
    secs ((Subobject.pullback D.arrow).obj S) V = (D.arrow.app V) ⁻¹' secs S V := by
  let G : X.Modules ⥤ Type :=
    Scheme.Modules.toPresheaf X ⋙ (evaluation _ _).obj (Opposite.op V) ⋙ forget Ab
  haveI : PreservesLimitsOfSize.{0, 0} ((evaluation (TopologicalSpace.Opens X)ᵒᵖ Ab).obj
      (Opposite.op V)) := ⟨fun {J} _ => evaluation_preservesLimitsOfShape _⟩
  haveI : PreservesLimitsOfShape WalkingCospan (Scheme.Modules.toPresheaf X) := inferInstance
  haveI : PreservesLimitsOfShape WalkingCospan (forget Ab.{0}) := inferInstance
  haveI : PreservesLimitsOfShape WalkingCospan G := inferInstance
  have hp := (Subobject.isPullback D.arrow S).map G
  ext d
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨(Subobject.pullbackπ D.arrow S).app V p, ?_⟩
    exact congr($(hp.w) p)
  · rintro ⟨s, hs⟩
    obtain ⟨p, h₁, h₂⟩ := Types.exists_of_isPullback hp s d hs
    exact ⟨p, h₂⟩

end GlobalTheory.CompanionTheory.GE
