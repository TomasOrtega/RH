import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionHeckeUEqSumSlash
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FQExpansionHeckeUEqSumSlash.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.qExpansion_heckeU_eq_sum_slash : ∀ (k l : ℕ) (a : ℕ → ℂ), 1 ≤ k → 0 < l → PolyB a → PolyB (Uo l a) ∧ ∀ τ : ℍ, qs (Uo l a) τ = ∑ j : Fin l, slz k (repU l j) (qs a) τ := by
  first | exact @GlobalTheory.EisM.Uo_qs_sum_slz | exact GlobalTheory.EisM.Uo_qs_sum_slz | (intros; apply GlobalTheory.EisM.Uo_qs_sum_slz <;> assumption)
