import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticMapUniformizationLine
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors
open Formalism.L2.Host (aboveF)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ConjCount.count_conjI` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEllipticMapUniformizationLine.lean&line=70#L70)
-/
theorem _root_.GlobalTheory.T.count_conj_ideal_eq_count : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (𝔠 : FractionalIdeal (𝓞 E)⁰ E), 𝔠 ≠ 0 → ∀ w : HeightOneSpectrum (𝓞 E), ∃ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) ∧ FractionalIdeal.count E w (conjI σ 𝔠) = FractionalIdeal.count E w' 𝔠 := by
  first | exact @GlobalTheory.ConjCount.count_conjI | exact GlobalTheory.ConjCount.count_conjI | (intros; apply GlobalTheory.ConjCount.count_conjI <;> assumption)
