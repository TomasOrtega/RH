import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSlTwoPermutedModularFamilyOfLevel
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
Apply `GlobalTheory.FamOfLevel.exists_family` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsSlTwoPermutedModularFamilyOfLevel.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.exists_slTwoPermutedModularFamily_of_level : ∀ (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ), (∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[k] γ = f) → ∃ F : GL (Fin 2) (ZMod N) → ℍ → ℂ, IsFam (gact N 1) k F ∧ (∀ γ : SL(2, ℤ), F (redGL N γ) = f ∣[k] γ) ∧ ∀ α, (∃ γ : SL(2, ℤ), α = redGL N γ) ∨ F α = 0 := by
  first | exact @GlobalTheory.FamOfLevel.exists_family | exact GlobalTheory.FamOfLevel.exists_family | (intros; apply GlobalTheory.FamOfLevel.exists_family <;> assumption)
