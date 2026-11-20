import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantInducedRepEquivProduct
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothDetPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorTorusCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedCharIntertwiningUnif
open scoped TensorProduct
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDeterminantInducedRepEquivProduct.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.determinant_induced_rep_equiv_product : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ),
    Nonempty ((GlobalTheory.ThK.MidJac.detInd a a' χ₁ χ₂).Equiv (prod₂ (detRep (Fin a) χ₁) (detRep (Fin a') χ₂))) := by
  first | exact @GlobalTheory.DetIndProd.detInd_equiv_prod₂ | exact GlobalTheory.DetIndProd.detInd_equiv_prod₂ | (intros; apply GlobalTheory.DetIndProd.detInd_equiv_prod₂ <;> assumption)
