import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOneTmulOfForallFixed
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf

open TensorProduct Module

namespace GlobalTheory

/- English proof (translation)
Introduce `L Ω M M' ι _ _ _ _ _ _ _ _ _ J f f' hJ hf`. Establish `h1 : ⨅ i, LinearMap.ker (f' i) = Submodule.span Ω (J '' (⨅ i, LinearMap.ker (f i) : Submodule L M))`. Rewrite using `[GlobalTheory.GaloisDescent.span_image_iInf hJ]`. Conclude with `iInf_congr fun i => (GlobalTheory.GaloisDescent.span_image_ker hJ hJ (f i) (f' i) (fun v => hf i v)).symm`. Establish `h2 : Submodule.span Ω (J '' (⨅ i, LinearMap.ker (f i) : Submodule L M)) = ((⨅ i, LinearMap.ker (f i) : Submodule L M).baseChange Ω).map hJ.equiv.toLinearMap`.

Rewrite using `[Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image]`. Use `congr 2`. Use extensionality with `x`. Simplify using `[IsBaseChange.equiv_tmul]`. Rewrite using `[h1, h2, LinearEquiv.finrank_map_eq, GlobalTheory.finrank_baseChange]`.
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
