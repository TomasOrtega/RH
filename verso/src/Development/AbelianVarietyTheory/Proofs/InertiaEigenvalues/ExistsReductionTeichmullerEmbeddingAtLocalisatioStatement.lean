import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReductionTeichmullerEmbeddingAtLocalisatio
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsReductionTeichmullerEmbeddingAtLocalisatio.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.exists_reduction_teichmullerEmbedding_at_localisation : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2), D.nd.l i ≠ D.host.g k → ∃ ι : Fb (D.host.g k) (D.host.g_prime k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i), InjPrimeTo (D.nd.l i) ι ∧ RedVia D i k ι := by
  first | exact @GlobalTheory.TypeLeaf.exists_redVia | exact GlobalTheory.TypeLeaf.exists_redVia | (intros; apply GlobalTheory.TypeLeaf.exists_redVia <;> assumption)
