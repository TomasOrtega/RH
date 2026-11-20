import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativeNormCmAbsNorm
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRelativeNormCmAbsNorm.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.relative_norm_cm_absNorm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ t : 𝓞 E, algebraMap F E ((RingOfIntegers.norm F t : 𝓞 F) : F) = (t : E) * σ (t : E) ∧ Ideal.absNorm (Ideal.span {RingOfIntegers.norm F t}) = Ideal.absNorm (Ideal.span {t}) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.NormSig.norm_eq_mul_conj_and_absNorm | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.NormSig.norm_eq_mul_conj_and_absNorm | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.NormSig.norm_eq_mul_conj_and_absNorm <;> assumption)
