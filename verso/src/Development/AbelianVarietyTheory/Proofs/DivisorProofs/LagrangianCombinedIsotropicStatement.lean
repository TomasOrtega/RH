import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianCombinedIsotropic
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
open ValuativeRel
open scoped Matrix Topology

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLagrangianCombinedIsotropic.lean&line=172#L172)
-/
theorem _root_.GlobalTheory.T.lagrangian_combined_isotropic : ∀ {k : Type} [Field k] {κ : Type} [Fintype κ] (U : Submodule k ((κ → k) × (κ → k))),
    (∀ u ∈ U, ∀ u' ∈ U, u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2 = 0) →
    ∃ (n : ℕ) (wT wM : (Fin n → k) →ₗ[k] (κ → k) × (κ → k)) (I : Finset (Fin n)),
      (∀ Y Y', (wT Y).1 ⬝ᵥ (wT Y').2 - (wT Y').1 ⬝ᵥ (wT Y).2 = 0) ∧
      (∀ z z', (wM z).1 ⬝ᵥ (wM z').2 - (wM z').1 ⬝ᵥ (wM z).2 = 0) ∧
      (∀ Y z, (wT Y).1 ⬝ᵥ (wM z).2 - (wM z).1 ⬝ᵥ (wT Y).2 = Y ⬝ᵥ z) ∧
      (∀ w, ∃ Y z, wT Y + wM z = w) ∧
      (∀ u, u ∈ U ↔ ∃ z : Fin n → k, (∀ i ∉ I, z i = 0) ∧ wM z = u) := by
  first | exact @GlobalTheory.LagrFrame.exists_frame | exact GlobalTheory.LagrFrame.exists_frame | (intros; apply GlobalTheory.LagrFrame.exists_frame <;> assumption)
