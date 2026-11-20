import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.OrdBasic

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

/- English proof (translation)
Introduce `R _ M _ _ _ I _ _`. Establish `hH : IsHausdorff I M` using `IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson_bot I)`. Establish `hP : IsPrecomplete I M`. Rewrite using `[← AdicCompletion.of_surjective_iff]`. Establish `hR : Function.Surjective (AdicCompletion.of I R)` using `AdicCompletion.of_surjective_iff.mpr inferInstance`.

Introduce `x`. Take `⟨t, rfl⟩` from `AdicCompletion.ofTensorProduct_surjective_of_finite I M x`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `tmul a m`.

Take `⟨r, rfl⟩` from `hR a`. Use `⟨r • m, ?_⟩` and prove the remaining obligations. Rewrite using `[AdicCompletion.ofTensorProduct_tmul, map_smul]`. Use extensionality with `n`. Rewrite using `[AdicCompletion.val_smul_apply]`.

Simplify using the standard rewrite rules. Apply the tactic sequence `try rfl`. Consider the case `add a b ha hb`. Take `⟨u, hu⟩` from `ha`. Take `⟨v, hv⟩` from `hb`.

Conclude with `⟨u + v, by rw [map_add, map_add, hu, hv]⟩`. Conclude with `{ toIsHausdorff := hH, toIsPrecomplete := hP }`.
-/
theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.completeFin :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] [Module.Finite R M], IsAdicComplete I M := by
  intro R _ M _ _ _ I _ _
  have hH : IsHausdorff I M := IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson_bot I)
  have hP : IsPrecomplete I M := by
    rw [← AdicCompletion.of_surjective_iff]
    have hR : Function.Surjective (AdicCompletion.of I R) := AdicCompletion.of_surjective_iff.mpr inferInstance
    intro x
    obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M x
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a m =>
      obtain ⟨r, rfl⟩ := hR a
      refine ⟨r • m, ?_⟩
      rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
      ext n
      rw [AdicCompletion.val_smul_apply]
      simp
      try rfl
    | add a b ha hb =>
      obtain ⟨u, hu⟩ := ha
      obtain ⟨v, hv⟩ := hb
      exact ⟨u + v, by rw [map_add, map_add, hu, hv]⟩
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }
