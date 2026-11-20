import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPlaceComponentAdeleConjugationEqComplexConj
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanInvolutionConjOfPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisAdaptedToCartanInvolution

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RealPlaceConj.piInf_cA_eq_star` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRealPlaceComponentAdeleConjugationEqComplexConj.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.realPlaceComponent_adeleConjugation_eq_complexConj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (z : AE F E), piInf τ (cA σ z) = star (piInf τ z) := by
  first | exact @GlobalTheory.RealPlaceConj.piInf_cA_eq_star | exact GlobalTheory.RealPlaceConj.piInf_cA_eq_star | (intros; apply GlobalTheory.RealPlaceConj.piInf_cA_eq_star <;> assumption)
