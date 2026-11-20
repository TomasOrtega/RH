import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryCountableDiscrete
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRationalUnitaryCountableDiscrete.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.rational_unitary_countable_discrete : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Countable (ratU σ J) ∧ DiscreteTopology (ratU σ J) := by
  first | exact @GlobalTheory.RatUDisc.countable_discrete_ratU | exact GlobalTheory.RatUDisc.countable_discrete_ratU | (intros; apply GlobalTheory.RatUDisc.countable_discrete_ratU <;> assumption)
