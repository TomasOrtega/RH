import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRightInverseCentralProjectorUnitElement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UupEqOneOfLeOne
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterGoodIdempotentCuspidalProduc
open GlobalTheory.MeetsGen
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MeetsUnit.exists_rightInv_uElt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsRightInverseCentralProjectorUnitElement.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.exists_right_inverse_centralProjectorUnitElement : ∀ {G : Type} [Group G] [Fintype G] (U : Subgroup G) [Fintype U] (ψ : U →* ℂˣ) (e : MonoidAlgebra ℂ G), e * e = e → (∀ a, e * a = a * e) → (∀ χ : G → ℂ, Formalism.L2.NT.IsIrrChar χ → ∑ g, e.coeff g * χ g = χ 1 → ∑ u : U, χ u * (((ψ u)⁻¹ : ℂˣ) : ℂ) ≠ 0) → ∃ v : MonoidAlgebra ℂ G, uElt U (fun u => (((ψ u)⁻¹ : ℂˣ) : ℂ)) e * v = 1 := by
  first | exact @GlobalTheory.MeetsUnit.exists_rightInv_uElt | exact GlobalTheory.MeetsUnit.exists_rightInv_uElt | (intros; apply GlobalTheory.MeetsUnit.exists_rightInv_uElt <;> assumption)
