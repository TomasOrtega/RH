import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE

/- English proof (translation)
Set `G : X.Modules ⥤ Type` to `Scheme.Modules.toPresheaf X ⋙ (evaluation _ _).obj (Opposite.op V) ⋙ forget Ab`. Use `haveI : PreservesLimitsOfSize.{0, 0} ((evaluation (TopologicalSpace.Opens X)ᵒᵖ Ab).obj (Opposite.op V)) := ⟨fun {J} _ => evaluation_preservesLimitsOfShape _⟩`. Use `haveI : PreservesLimitsOfShape WalkingCospan (Scheme.Modules.toPresheaf X) := inferInstance`. Use `haveI : PreservesLimitsOfShape WalkingCospan (forget Ab.{0}) := inferInstance`. Use `haveI : PreservesLimitsOfShape WalkingCospan G := inferInstance`.

Establish `hp` using `(Subobject.isPullback D.arrow S).map G`. Use extensionality with `d`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, rfl⟩`. Use `⟨(Subobject.pullbackπ D.arrow S).app V p, ?_⟩` and prove the remaining obligations.

Conclude with `congr($(hp.w) p)`. Introduce and unpack `⟨s, hs⟩`. Take `⟨p, h₁, h₂⟩` from `Types.exists_of_isPullback hp s d hs`. Conclude with `⟨p, h₂⟩`.
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
