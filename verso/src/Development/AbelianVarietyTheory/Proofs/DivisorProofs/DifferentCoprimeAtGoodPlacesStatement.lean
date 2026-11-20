import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors
open Formalism.L2.Host (aboveF)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DiffCoprimeP.count_diffE_eq_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDifferentCoprimeAtGoodPlaces.lean&line=106#L106)
-/
theorem _root_.GlobalTheory.T.different_coprime_at_good_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ v ∈ B.P, ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → FractionalIdeal.count E w (diffE E) = 0 := by
  first | exact @GlobalTheory.DiffCoprimeP.count_diffE_eq_zero | exact GlobalTheory.DiffCoprimeP.count_diffE_eq_zero | (intros; apply GlobalTheory.DiffCoprimeP.count_diffE_eq_zero <;> assumption)
