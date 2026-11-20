import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsComplexRingEquivExtendingSubfieldAut
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsComplexRingEquivExtendingSubfieldAut.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.exists_complex_ringEquiv_extending_subfield_aut : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω ≃+* Ω), ∃ g : ℂ ≃+* ℂ, ∀ x, g (ε x) = ε (s x) := by
  first | exact @GlobalTheory.FN.exists_ringEquiv_extend_of_embedding | exact GlobalTheory.FN.exists_ringEquiv_extend_of_embedding | (intros; apply GlobalTheory.FN.exists_ringEquiv_extend_of_embedding <;> assumption)
