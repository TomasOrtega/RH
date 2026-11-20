import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.QuotientLatticeByIsotropicSubmoduleStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.PosFormProjection

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_orthogonal_coefficients :
    ∀ (g k : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ),
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) →
      ∀ u : Fin k → Fin g → ℂ, LinearIndependent ℂ u →
      ∀ z : Fin g → ℂ, ∃ c : Fin k → ℂ,
        ∀ j, (z - ∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (u j) = 0 := by
  intro g k Hm hpos u hli z
  let A : (Fin k → ℂ) →ₗ[ℂ] (Fin k → ℂ) :=
    { toFun := fun c j => (∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (u j)
      map_add' := by
        intro a b
        funext j
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, add_dotProduct]
      map_smul' := by
        intro a b
        funext j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul, ← Finset.smul_sum,
          smul_dotProduct] }
  have hinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hw : ∀ j, (∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (u j) = 0 := fun j => congrFun hc j
    have hww : (∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (∑ i, c i • u i) = 0 := by
      rw [star_sum, Matrix.mulVec_sum, dotProduct_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, hw j, smul_zero]
    have hw0 : ∑ i, c i • u i = 0 := by
      by_contra hne
      have := hpos _ hne
      rw [hww] at this
      simp at this
    funext i
    exact Fintype.linearIndependent_iff.mp hli c hw0 i
  obtain ⟨c, hc⟩ := LinearMap.injective_iff_surjective.mp hinj (fun j => z ⬝ᵥ Hm *ᵥ star (u j))
  refine ⟨c, fun j => ?_⟩
  have hcj : (∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (u j) = z ⬝ᵥ Hm *ᵥ star (u j) := congrFun hc j
  rw [sub_dotProduct, hcj, sub_self]

end GlobalTheory.CompanionTheory.Ar.PosFormProjection
