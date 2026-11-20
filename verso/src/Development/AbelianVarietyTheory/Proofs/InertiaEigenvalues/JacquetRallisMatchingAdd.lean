import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitalIntegrandIsLocallyConstantCoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisBorderedMatrixNormalFormInvariantsStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GlobalTheory.JR.MatchAdd.integrable_of_isTest {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {f : X → ℂ} (hf : IsTest f) :
    Integrable f μ :=
  hf.1.continuous.integrable_of_hasCompactSupport hf.2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Equip the data with the indicated structure. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Equip the data with the indicated structure. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem GlobalTheory.JR.match_add : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (f₁' f₂' : Gl r F → ℂ) (f₁ f₂ : Hn r F E → ℂ), IsTest f₁' → IsTest f₂' → IsTest f₁ → IsTest f₂ → Match M f₁' f₁ → Match M f₂' f₂ → Match M (f₁' + f₂') (f₁ + f₂) := by
  intro F E _ _ _ _ _ r M f₁' f₂' f₁ f₂ h₁' h₂' h₁ h₂ m₁ m₂ a ha
  obtain ⟨hG, hU⟩ := GlobalTheory.T.jacquetRallis_orbitalIntegrand_isLocallyConstantCompactSupport F E r M
  obtain ⟨-, hsec, -⟩ := GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants F r
  have ha' : Delta (inv (sec a)) ≠ 0 := by rw [hsec]; exact ha
  have eG : orbG M (f₁' + f₂') (sec a) = orbG M f₁' (sec a) + orbG M f₂' (sec a) := by
    letI := M.mG
    haveI := M.bG
    haveI := M.haarG
    unfold orbG
    simp only [Pi.add_apply, add_mul]
    exact integral_add (MatchAdd.integrable_of_isTest _ (hG _ h₁' _ ha'))
      (MatchAdd.integrable_of_isTest _ (hG _ h₂' _ ha'))
  have eU : ∀ X : Hn r F E, HasInv X a → orbU M (f₁ + f₂) X = orbU M f₁ X + orbU M f₂ X := by
    intro X hX
    letI := M.mU
    haveI := M.bU
    haveI := M.haarU
    unfold orbU
    simp only [Pi.add_apply]
    exact integral_add (MatchAdd.integrable_of_isTest _ (hU _ h₁ a X ha hX))
      (MatchAdd.integrable_of_isTest _ (hU _ h₂ a X ha hX))
  refine ⟨fun X hX => ?_, fun hn => ?_⟩
  · rw [eG, eU X hX, (m₁ a ha).1 X hX, (m₂ a ha).1 X hX]
  · rw [eG, (m₁ a ha).2 hn, (m₂ a ha).2 hn, add_zero]
