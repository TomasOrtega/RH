import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsNormForm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem MapDvdDescent.proof : MapDvdDescent.Statement := by
  classical
  intro K Ω _ _ _ σ f g ⟨G, hG⟩
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K Ω)
    (LinearMap.ker_eq_bot.mpr (algebraMap K Ω).injective)
  have hπa : ∀ a : K, π (algebraMap K Ω a) = a := fun a => by
    simpa using LinearMap.congr_fun hπ a
  have hπm : ∀ (a : K) (y : Ω), π (algebraMap K Ω a * y) = a * π y := fun a y => by
    rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

  let Φ : MvPolynomial σ K := ∑ s ∈ G.support, monomial s (π (coeff s G))
  have hΦ : ∀ s, coeff s Φ = π (coeff s G) := fun s => by
    simp only [Φ, coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [notMem_support_iff.mp h, map_zero]
  refine ⟨Φ, ?_⟩
  ext s
  have h1 := congrArg (fun P => π (coeff s P)) hG
  simp only [coeff_map, hπa, coeff_mul, map_sum, hπm] at h1
  rw [h1, coeff_mul]
  exact Finset.sum_congr rfl fun x _ => by rw [hΦ]

end GroundTheory.Heights₂.Heights
