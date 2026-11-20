import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPowHeckeCharUnramifiedEverywhere
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Corev.UnrPow.exists_pow_unrAt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FExistsPowHeckeCharUnramifiedEverywhere.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_pow_heckeChar_unramified_everywhere : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L), ∃ N : ℕ, 0 < N ∧ ∀ v : HeightOneSpectrum (𝓞 L), (χ ^ N).UnrAt v := by
  first | exact @GlobalTheory.Corev.UnrPow.exists_pow_unrAt | exact GlobalTheory.Corev.UnrPow.exists_pow_unrAt | (intros; apply GlobalTheory.Corev.UnrPow.exists_pow_unrAt <;> assumption)
