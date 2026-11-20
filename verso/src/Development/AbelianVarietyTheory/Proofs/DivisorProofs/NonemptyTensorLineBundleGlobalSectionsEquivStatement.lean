import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyTensorLineBundleGlobalSectionsEquiv
import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SecTensor.tensorSecEquiv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNonemptyTensorLineBundleGlobalSectionsEquiv.lean&line=140#L140)
-/
theorem _root_.GlobalTheory.T.nonempty_tensor_lineBundle_globalSections_equiv : ∀ (T : Scheme.{0}) [IsAffine T] (A B : LB T), A.IsLB → B.IsLB → Nonempty (TensorProduct Γ(T, ⊤) (LB.Sec A) (LB.Sec B) ≃ₗ[Γ(T, ⊤)] LB.Sec (GlobalTheory.CechPic.tens A B)) := by
  first | exact @GlobalTheory.SecTensor.tensorSecEquiv | exact GlobalTheory.SecTensor.tensorSecEquiv | (intros; apply GlobalTheory.SecTensor.tensorSecEquiv <;> assumption)
