import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPrincipalElementNormBound
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIdealPrincipalElementNormBound.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.ideal_principal_element_norm_bound : ∀ (E : Type) [Field E] [NumberField E], ∃ C : ℝ, 0 < C ∧ ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ t ∈ 𝔞, t ≠ 0 ∧ (Ideal.absNorm (Ideal.span {t}) : ℝ) ≤ C * Ideal.absNorm 𝔞 := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink.exists_ne_zero_mem_absNorm_le | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink.exists_ne_zero_mem_absNorm_le | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink.exists_ne_zero_mem_absNorm_le <;> assumption)
