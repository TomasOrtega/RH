import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHighestWeightVectorDualWeylModuleUpper
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolynomialRepGLComplexAlgebraicWeightEvalPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroupStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsHighestWeightVectorDualWeylModuleUpper.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.exists_highest_weight_vector_dualWeylModule_upper : ∀ (n : ℕ) (lam : DomWeight n), ∃ v : nablaSq ℂ n lam, v ≠ 0 ∧ ∀ B : GL (Fin n) ℂ, (B : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id → GlobalTheory.Branching.sqRep ℂ n lam B v = (∏ i, ((B : Matrix (Fin n) (Fin n) ℂ) i i) ^ (lam.w i)) • v := by
  first | exact @GlobalTheory.HwUpper.exists_hw_upper | exact GlobalTheory.HwUpper.exists_hw_upper | (intros; apply GlobalTheory.HwUpper.exists_hw_upper <;> assumption)
