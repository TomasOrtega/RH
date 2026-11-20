import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactSupportSchwartzDecay
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCompactSupportSchwartzDecay.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.compact_support_schwartz_decay : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (m : ℕ) (b₀ : Module.Basis (Fin m) F E) (g : AE F E → ℂ), Continuous g →
    (∃ K : Set (Fin m → FiniteAdeleRing (𝓞 F) F), IsCompact K ∧ ∀ a, (fun i => ((Algebra.TensorProduct.basis (AF F) b₀).equivFun a i).2) ∉ K → g a = 0) →
    (∀ N : ℕ, ∃ C : ℝ, ∀ a, ‖g a‖ * (1 + ‖fun i => evI F ((Algebra.TensorProduct.basis (AF F) b₀).equivFun a i)‖) ^ N ≤ C) →
    ∀ μ : Measure (AE F E)ˣ, μ.IsHaarMeasure → ∀ z : ℕ, 2 ≤ z → Integrable (fun l : (AE F E)ˣ => ‖g l.1‖ * (absE F E l : ℝ) ^ z) μ := by
  first | exact @GlobalTheory.TateConvBasis.integrable_norm_mul_absE_pow | exact GlobalTheory.TateConvBasis.integrable_norm_mul_absE_pow | (intros; apply GlobalTheory.TateConvBasis.integrable_norm_mul_absE_pow <;> assumption)
