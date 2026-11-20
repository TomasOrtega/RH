import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormPrincipleOfIsCyclic
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FHasseNormPrincipleOfIsCyclic.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.hasseNormPrinciple_of_isCyclic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], IsGalois F E → IsCyclic (E ≃ₐ[F] E) → NP F E := by
  first | exact @GlobalTheory.CNorm.np_cyclic | exact GlobalTheory.CNorm.np_cyclic | (intros; apply GlobalTheory.CNorm.np_cyclic <;> assumption)
