import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.MonoCount

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

/- English proof (translation)
Introduce `D B P j X ka wL wF G la T`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k l hkl`. Unfold `Fk`. Apply `Submodule.span_mono` to reduce the goal to its premises.

Apply `Set.image_mono` to reduce the goal to its premises. Conclude with `SetLike.coe_subset_coe.2 (Submodule.smul_mono_left (Ideal.pow_le_pow_right hkl))`. Unfold `Fk`. Rewrite using `[pow_zero, Ideal.one_eq_top, Submodule.top_smul, Submodule.top_coe, Set.image_univ, (toWK_surjective X la G.w wF (a0 D j T)).range_eq, Submodule.span_univ]`. Unfold `Fk`.

Rewrite using `[Submodule.span_eq_bot]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `(toWK_eq_zero_iff X la G.w wF _ x).2 hx`.
-/
theorem fkFilt_holds : FkFilt := by
  intro D B P j X ka wL wF G la T
  refine ⟨?_, ?_, ?_⟩
  · intro k l hkl
    unfold Fk
    apply Submodule.span_mono
    apply Set.image_mono
    exact SetLike.coe_subset_coe.2 (Submodule.smul_mono_left (Ideal.pow_le_pow_right hkl))
  · unfold Fk
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul, Submodule.top_coe, Set.image_univ,
      (toWK_surjective X la G.w wF (a0 D j T)).range_eq, Submodule.span_univ]
  · unfold Fk
    rw [Submodule.span_eq_bot]
    rintro _ ⟨x, hx, rfl⟩
    exact (toWK_eq_zero_iff X la G.w wF _ x).2 hx

end PoleLengthBounds
