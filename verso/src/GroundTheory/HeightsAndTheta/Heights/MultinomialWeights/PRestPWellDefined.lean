import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Imports
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

/- English proof (translation)
Unfold `liePowerSum lowerPowerSum`. Use `split_ifs`. Use `IsHomogeneous.sum _ _ _ fun i _ => ?_` and prove the remaining obligations. Simplify using `using (isHomogeneous_X ℚ (e.1, i)).neg.pow m`. Use `IsHomogeneous.sum _ _ _ fun i _ => ?_` and prove the remaining obligations.

Simplify using `using (isHomogeneous_X ℚ (e.1, i)).pow m`.
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
Introduce `d vol p φ F Q Q' hQ hQ'`. Unfold `rest₂`. Use `congr 1`. Use `Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Take `⟨hk2, hkN⟩` from `Finset.mem_Icc.mp hk`.

Use `congr 1`. Use function extensionality and compare the values at `n`. Unfold `restSeries`. Establish `hG` using `liePowerSum_isHomogeneous d (k - 1) ((φ ^ (n + 1)) (τ, false))`. Establish `h` using `RestTerms.RestTermWellDefined.full d.f d.N F Q Q' hQ hQ' k (by omega) hkN τ _ hG`.

Unfold `RestTerms.restTerm at h`. Establish `e : ∀ R : ℕ → Fin d.f → XPoly d, (k : ℚ) * intFl d (liePowerSum d (k - 1) ((φ ^ (n + 1)) (τ, false)) * R k τ) = flagNormalisation d.f d.N * ((k : ℚ) * RestTerms.flagIntegral d.f d.N (liePowerSum d (k - 1) ((φ ^ (n + 1)) (τ, false)) * R k τ))`. Introduce `R`. Simplify using `only [intFl, LinearMap.smul_apply, flagIntegralLin, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e Q, e Q', h]`.
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
The claim follows from `RestPWellDefined.proof`.
-/
theorem RestPWellDefined.full : RestPWellDefined.Statement := RestPWellDefined.proof

end GroundTheory.Heights₂.Heights.TheoremB
