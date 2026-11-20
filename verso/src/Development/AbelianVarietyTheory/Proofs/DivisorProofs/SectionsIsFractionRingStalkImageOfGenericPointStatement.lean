import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsIsFractionRingStalkImageOfGenericPoint
import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamIdeal
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSectionsIsFractionRingStalkImageOfGenericPoint.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.sections_isFractionRing_stalk_imageOfGenericPoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y] [GlobalTheory.IsNormalScheme Z] (U : Z.Opens), IsAffineOpen U →
    (U : Set Z) ⊆ Set.range π → ∀ h : GlobalTheory.NormSheafDescent.genPt π ∈ U,
    IsDomain Γ(Z, U) ∧ (letI := GlobalTheory.NormSheafDescent.algAK π U h
      IsFractionRing Γ(Z, U) (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))) := by
  first | exact @GlobalTheory.NormSheafDescent.sections_isDomain_isFractionRing_stalk | exact GlobalTheory.NormSheafDescent.sections_isDomain_isFractionRing_stalk | (intros; apply GlobalTheory.NormSheafDescent.sections_isDomain_isFractionRing_stalk <;> assumption)
