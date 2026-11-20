import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsEquivDegreeZeroCocycles
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EtC.HCZero.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEtaleSheafSectionsEquivDegreeZeroCocycles.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.etaleSheafSections_equiv_degreeZeroCocycles : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ ι : F.obj ⋙ forget₂ _ AddCommGrpCat.{1} ⟶ sch.op ⋙ HC R F ⋙ HomologicalComplex.eval _ _ 0, ∀ U : Scheme.{0}ᵒᵖ, Function.Injective (ι.app U) ∧ ∀ z : ((HC R F).obj (op (sch.obj U.unop))).X 0, ((HC R F).obj (op (sch.obj U.unop))).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app U x = z := by
  first | exact @GlobalTheory.EtC.HCZero.main | exact GlobalTheory.EtC.HCZero.main | (intros; apply GlobalTheory.EtC.HCZero.main <;> assumption)
