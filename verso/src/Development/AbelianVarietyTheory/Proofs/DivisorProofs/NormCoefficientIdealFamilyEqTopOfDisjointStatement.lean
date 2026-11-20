import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoefficientIdealFamilyEqTopOfDisjoint
import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamIdeal
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NormSheafDescent.famIdeal_eq_top_of_disjoint` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNormCoefficientIdealFamilyEqTopOfDisjoint.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.normCoefficientIdealFamily_eq_top_of_disjoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)))
    (hfd : letI := GlobalTheory.NormSheafDescent.fieldK π hK; letI := GlobalTheory.NormSheafDescent.algKL π
      FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField)
    (I : Y.IdealSheafData) (U : Z.affineOpens), (∀ y ∈ I.support, π y ∉ (U : Set Z)) →
    GlobalTheory.NormSheafDescent.famIdeal π hK hfd I U = ⊤ := by
  first | exact @GlobalTheory.NormSheafDescent.famIdeal_eq_top_of_disjoint | exact GlobalTheory.NormSheafDescent.famIdeal_eq_top_of_disjoint | (intros; apply GlobalTheory.NormSheafDescent.famIdeal_eq_top_of_disjoint <;> assumption)
