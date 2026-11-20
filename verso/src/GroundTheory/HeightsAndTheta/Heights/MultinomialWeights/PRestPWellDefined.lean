import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Imports
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem liePowerSum_isHomogeneous (d : IndexData) (m : ℕ) (e : Emb d) :
    (liePowerSum d m e).IsHomogeneous m := by
  unfold liePowerSum lowerPowerSum
  split_ifs
  · refine IsHomogeneous.sum _ _ _ fun i _ => ?_
    simpa using (isHomogeneous_X ℚ (e.1, i)).neg.pow m
  · refine IsHomogeneous.sum _ _ _ fun i _ => ?_
    simpa using (isHomogeneous_X ℚ (e.1, i)).pow m

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities.
-/
theorem RestPWellDefined.proof : RestPWellDefined.Statement := by
  intro d vol p φ F Q Q' hQ hQ'
  unfold rest₂
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk2, hkN⟩ := Finset.mem_Icc.mp hk
  congr 1
  funext n
  unfold restSeries
  have hG := liePowerSum_isHomogeneous d (k - 1) ((φ ^ (n + 1)) (τ, false))
  have h := RestTerms.RestTermWellDefined.full d.f d.N F Q Q' hQ hQ' k (by omega) hkN τ _ hG
  unfold RestTerms.restTerm at h
  have e : ∀ R : ℕ → Fin d.f → XPoly d,
      (k : ℚ) * intFl d (liePowerSum d (k - 1) ((φ ^ (n + 1)) (τ, false)) * R k τ) =
        flagNormalisation d.f d.N *
          ((k : ℚ) * RestTerms.flagIntegral d.f d.N (liePowerSum d (k - 1) ((φ ^ (n + 1)) (τ, false)) * R k τ)) := by
    intro R
    simp only [intFl, LinearMap.smul_apply, flagIntegralLin, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    ring
  rw [e Q, e Q', h]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RestPWellDefined.full : RestPWellDefined.Statement := RestPWellDefined.proof

end GroundTheory.Heights₂.Heights.TheoremB
