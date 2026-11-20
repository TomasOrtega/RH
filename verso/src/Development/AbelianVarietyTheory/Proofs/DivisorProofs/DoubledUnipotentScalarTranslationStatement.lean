import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnipotentScalarTranslation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipMat

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDoubledUnipotentScalarTranslation.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.doubled_unipotent_scalar_translation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ β : AE F E, ∃ u : UG (cA σ) (dbl (incM F W.J)), (u.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) = GlobalTheory.DblUnip.unipMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) β := by
  first | exact @GlobalTheory.DblUnipU.exists_unip | exact GlobalTheory.DblUnipU.exists_unip | (intros; apply GlobalTheory.DblUnipU.exists_unip <;> assumption)
