import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes
import Mathlib
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FStalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.stalkMap_flat_formallyEtale_essFiniteType_of_etale_open : ∀ (M W : Scheme.{0}) (f : M ⟶ W) (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, (f.stalkMap y).hom.Flat ∧ (f.stalkMap y).hom.FormallyEtale ∧ (f.stalkMap y).hom.EssFiniteType := by
  first | exact @GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict | exact GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict | (intros; apply GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict <;> assumption)
