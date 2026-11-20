import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOneTmulOfForallFixed
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf

open TensorProduct Module

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finrank_iInf_ker_of_isBaseChange : ∀ (L Ω M M' ι : Type) [Field L] [Field Ω] [Algebra L Ω]
    [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module Ω M'] [Module L M']
    [IsScalarTower L Ω M'] (J : M →ₗ[L] M') (f : ι → M →ₗ[L] M) (f' : ι → M' →ₗ[Ω] M'),
    IsBaseChange Ω J → (∀ i x, f' i (J x) = J (f i x)) →
      finrank Ω ↥(⨅ i, LinearMap.ker (f' i)) = finrank L ↥(⨅ i, LinearMap.ker (f i)) := by
  intro L Ω M M' ι _ _ _ _ _ _ _ _ _ J f f' hJ hf
  have h1 : ⨅ i, LinearMap.ker (f' i) =
      Submodule.span Ω (J '' (⨅ i, LinearMap.ker (f i) : Submodule L M)) := by
    rw [GlobalTheory.GaloisDescent.span_image_iInf hJ]
    exact iInf_congr fun i =>
      (GlobalTheory.GaloisDescent.span_image_ker hJ hJ (f i) (f' i) (fun v => hf i v)).symm
  have h2 : Submodule.span Ω (J '' (⨅ i, LinearMap.ker (f i) : Submodule L M)) =
      ((⨅ i, LinearMap.ker (f i) : Submodule L M).baseChange Ω).map hJ.equiv.toLinearMap := by
    rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image]
    congr 2
    ext x
    simp [IsBaseChange.equiv_tmul]
  rw [h1, h2, LinearEquiv.finrank_map_eq, GlobalTheory.finrank_baseChange]

end GlobalTheory
