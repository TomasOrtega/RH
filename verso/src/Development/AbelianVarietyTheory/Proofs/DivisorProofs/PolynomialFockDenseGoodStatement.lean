import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockDenseGood
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPolynomialFockDenseGood.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.polynomial_fock_dense_good : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    Dense ((M.Pol B.ψ B.emb : Submodule ℂ (SInf F (Fin n × Fin d))) : Set (SInf F (Fin n × Fin d))) := by
  first | exact @GlobalTheory.PolDense.pol_dense_good | exact GlobalTheory.PolDense.pol_dense_good | (intros; apply GlobalTheory.PolDense.pol_dense_good <;> assumption)
