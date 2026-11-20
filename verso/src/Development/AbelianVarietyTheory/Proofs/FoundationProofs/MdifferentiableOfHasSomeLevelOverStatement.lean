import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableOfHasSomeLevelOver
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FN.inR_mdifferentiable` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FMdifferentiableOfHasSomeLevelOver.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver : ∀ (E : Subring ℂ) (f : ℍ → ℂ), InR E f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  first | exact @GlobalTheory.FN.inR_mdifferentiable | exact GlobalTheory.FN.inR_mdifferentiable | (intros; apply GlobalTheory.FN.inR_mdifferentiable <;> assumption)
