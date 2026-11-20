import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

/- English proof (translation)
Introduce `V _ _ ι _ φ v hv`. Establish `hfin : FiniteDimensional ℂ V`. Use `Module.Finite.of_surjective (Fintype.linearCombination ℂ v) ?_` and prove the remaining obligations. Introduce `y`. Conclude with `⟨fun k => φ k y, by rw [Fintype.linearCombination_apply]; exact (hv y).symm⟩`.

Use `⟨hfin, fun u => ?_⟩` and prove the remaining obligations. Establish `hu : u = ∑ k, dualTensorHom ℂ V V (φ k ⊗ₜ u (v k))`. Use extensionality with `y`. Rewrite using `[LinearMap.sum_apply]`. Simplify using `only [dualTensorHom_apply]`.

Use `conv_lhs => rw [hv y]`. Rewrite using `[map_sum]`. Simplify using `[map_smul]`. Use `conv_lhs => rw [hu]`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.trace_eq_contract_apply]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Gal.productCup_of_system.trLin_of :
    TrLin := by
  intro V _ _ ι _ φ v hv
  have hfin : FiniteDimensional ℂ V := by
    refine Module.Finite.of_surjective (Fintype.linearCombination ℂ v) ?_
    intro y
    exact ⟨fun k => φ k y, by rw [Fintype.linearCombination_apply]; exact (hv y).symm⟩
  refine ⟨hfin, fun u => ?_⟩
  have hu : u = ∑ k, dualTensorHom ℂ V V (φ k ⊗ₜ u (v k)) := by
    ext y
    rw [LinearMap.sum_apply]
    simp only [dualTensorHom_apply]
    conv_lhs => rw [hv y]
    rw [map_sum]
    simp [map_smul]
  conv_lhs => rw [hu]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.trace_eq_contract_apply]
  simp
