import Mathlib
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst

namespace GlobalTheory.CompanionTheory.ExpOneParam

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem continuous_expG_and_toM_inv :
    ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inG ε Z →
      Continuous (fun t : ℝ => Formalism.REAL.expG ε Z t) ∧
        ∀ t : ℝ, Formalism.REAL.toM (Formalism.REAL.expG ε Z t)⁻¹ = NormedSpace.exp (-((t : ℂ) • Z)) := by
  intro n ε Z hZ
  obtain ⟨h0, hadd, hcont, -⟩ := (Formalism.REAL.group_exponential_facts : Formalism.REAL.ExpGFacts) n ε Z hZ
  refine ⟨hcont, fun t => ?_⟩
  have hinv : (Formalism.REAL.expG ε Z t)⁻¹ = Formalism.REAL.expG ε Z (-t) := by
    refine inv_eq_of_mul_eq_one_left ?_
    rw [← hadd, neg_add_cancel, h0]
  rw [hinv, Formalism.REAL.toM_expG ε Z (-t) hZ, Complex.ofReal_neg, neg_smul]

end GlobalTheory.CompanionTheory.ExpOneParam
