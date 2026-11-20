import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.UsedConclusionOfUsedInputs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationTwoAndConjugationAtQAndDStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionOverQOrDEqUnramifiedSupSqrtStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SqrtNegPrimeMemPadicCyclotomicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SqrtNegPrimeNotMemMaxUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StructureUnramifiedAdjoinSqrtNegPrimeStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.LocalFieldsQD

/- English proof (translation)
Introduce `D`. Use `⟨fun i hi w hw => ?_, GlobalTheory.T.aux_statement D⟩` and prove the remaining obligations. Take `⟨M, hM, y, hy, hK⟩` from `GlobalTheory.T.completion_over_q_or_d_eq_unramified_sup_sqrt D i hi w hw`. Take `⟨-, -, hq8, hd16, -⟩` from `D.host.hyp`. Apply the tactic sequence `have h4 : D.nd.l i % 4 = 3 := by rcases hi with h | h <;> rw [h] <;> omega`.

Establish `h2 : D.nd.l i ≠ 2` using `by omega`. Take `⟨e1, e2, e3, e4⟩` from `GlobalTheory.T.structure_unramified_adjoin_sqrt_neg_prime (D.nd.l i) h2 (D.nbr i w hw).Kw M y hM hy (GlobalTheory.T.sqrt_neg_prime_not_mem_max_unramified _ y hy) (GlobalTheory.T.sqrt_neg_prime_mem_padic_cyclotomic _ h4 y hy) hK`. Conclude with `⟨⟨y, hy, e1⟩, e2, e3, e4⟩`.
-/
theorem main : ∀ D : D7, EmbeddingTypeJumps.Conclusion0 D ∧ EmbeddingTypeJumps.Conclusion1 D := by
  intro D
  refine ⟨fun i hi w hw => ?_, GlobalTheory.T.aux_statement D⟩
  obtain ⟨M, hM, y, hy, hK⟩ := GlobalTheory.T.completion_over_q_or_d_eq_unramified_sup_sqrt D i hi w hw
  obtain ⟨-, -, hq8, hd16, -⟩ := D.host.hyp
  have h4 : D.nd.l i % 4 = 3 := by rcases hi with h | h <;> rw [h] <;> omega
  have h2 : D.nd.l i ≠ 2 := by omega
  obtain ⟨e1, e2, e3, e4⟩ := GlobalTheory.T.structure_unramified_adjoin_sqrt_neg_prime (D.nd.l i) h2 (D.nbr i w hw).Kw M y hM hy
    (GlobalTheory.T.sqrt_neg_prime_not_mem_max_unramified _ y hy) (GlobalTheory.T.sqrt_neg_prime_mem_padic_cyclotomic _ h4 y hy) hK
  exact ⟨⟨y, hy, e1⟩, e2, e3, e4⟩

end GlobalTheory.LocalFieldsQD
