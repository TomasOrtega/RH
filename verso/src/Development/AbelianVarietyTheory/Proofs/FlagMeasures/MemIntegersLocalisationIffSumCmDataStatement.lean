import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemIntegersLocalisationIffSumCmData
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Formalism.LocalRingCardinality.DataSpaces
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FMemIntegersLocalisationIffSumCmData.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.mem_integers_localisation_iff_sum_cmData : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ (sig : E →ₐ[F] E), (∀ x, sig x = star x) → ∀ (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p), ∀ y : A.Ep, y ∈ A.O ↔ ∃ (n : ℕ) (c : Fin n → 𝒪[A.Fp]) (x : Fin n → 𝓞 E), y = ∑ i, algebraMap A.Fp A.Ep (c i : A.Fp) * A.ιE (x i : E) := by
  first | exact @GlobalTheory.LocSpan.mem_O_iff | exact GlobalTheory.LocSpan.mem_O_iff | (intros; apply GlobalTheory.LocSpan.mem_O_iff <;> assumption)
