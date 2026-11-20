import Mathlib

/- English proof (translation)
Introduce `O M _ _ I _ _ _ _`. Rewrite using `[← AdicCompletion.of_surjective_iff]`. Introduce `y`. Take `⟨t, rfl⟩` from `AdicCompletion.ofTensorProduct_surjective_of_finite I M y`. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => exact ⟨0, by rw [map_zero, map_zero]⟩`. Consider the case `tmul r m`. Take `⟨a, rfl⟩` from `AdicCompletion.of_surjective I O r`. Use `⟨a • m, ?_⟩` and prove the remaining obligations. Rewrite using `[AdicCompletion.ofTensorProduct_tmul, map_smul]`.

Conclude with `(algebraMap_smul (AdicCompletion I O) a (AdicCompletion.of I M m)).symm`. Consider the case `add x z hx hz`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hz`. Conclude with `⟨a + b, by rw [map_add, map_add, ha, hb]⟩`.
-/
theorem UpperTheory.Reformulated.B.PrecompleteOfFiniteOverAdicComplete.curveDVR_prec_finite :
    ∀ {O M : Type} [inst : CommRing O] [IsNoetherianRing O]
    (I : Ideal O) [IsAdicComplete I O] [inst_3 : AddCommGroup M] [inst_4 : _root_.Module O M] [Module.Finite O M],
    IsPrecomplete I M := by
  intro O M _ _ I _ _ _ _
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
  | tmul r m =>
    obtain ⟨a, rfl⟩ := AdicCompletion.of_surjective I O r
    refine ⟨a • m, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    exact (algebraMap_smul (AdicCompletion I O) a (AdicCompletion.of I M m)).symm
  | add x z hx hz =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
