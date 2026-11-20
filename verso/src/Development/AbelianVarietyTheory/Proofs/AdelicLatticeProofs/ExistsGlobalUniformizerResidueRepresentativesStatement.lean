import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGlobalUniformizerResidueRepresentatives
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FExistsGlobalUniformizerResidueRepresentatives.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_global_uniformizer_residue_representatives : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), (∃ π : F, v.valuation F π = WithZero.exp (-1) ∧ Valued.v (algebraMap F (v.adicCompletion F) π) = WithZero.exp (-1)) ∧ (∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x) ∧ (∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (a : F)) < 1) ∧ ∃ R : Finset (v.adicCompletion F), R.card ≤ Ideal.absNorm v.asIdeal ∧ (∀ r ∈ R, Valued.v r ≤ 1) ∧ ∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃ r ∈ R, Valued.v (x - r) < 1 := by
  first | exact @GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives | exact GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives | (intros; apply GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives <;> assumption)
