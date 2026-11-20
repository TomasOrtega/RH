import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyRationalUnitary
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDiscreteTopologyRationalUnitary.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.discreteTopology_rational_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E), DiscreteTopology (ratU σ J) := by
  first | exact @GlobalTheory.RatUDiscrete.discreteTopology_ratU | exact GlobalTheory.RatUDiscrete.discreteTopology_ratU | (intros; apply GlobalTheory.RatUDiscrete.discreteTopology_ratU <;> assumption)
