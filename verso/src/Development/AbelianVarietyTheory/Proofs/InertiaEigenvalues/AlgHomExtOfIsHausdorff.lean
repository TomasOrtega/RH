import Mathlib

namespace GlobalTheory.PowerSeriesAdicEval

open PowerSeries

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem exists_algHom_apply_X {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal A) [h : IsAdicComplete I A] {y : A} (hy : y ∈ I) :
    ∃ ev : PowerSeries R →ₐ[R] A, ev PowerSeries.X = y := by
  let _ : WithIdeal A := ⟨I⟩
  let _ : UniformSpace R := ⊥
  have _ : DiscreteUniformity R := ⟨rfl⟩
  have hI : IsAdic I := rfl
  obtain ⟨h1, h2⟩ := hI.isAdicComplete_iff.mp h
  have ha : PowerSeries.HasEval y := WithIdeal.isTopologicallyNilpotent_of_mem hy
  have _ : ContinuousSMul R A := DiscreteTopology.instContinuousSMul R A
  refine ⟨PowerSeries.aeval ha, ?_⟩
  rw [← Polynomial.coe_X, PowerSeries.aeval_coe, Polynomial.aeval_X]

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem algHom_coe {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (f : PowerSeries R →ₐ[R] A) (p : Polynomial R) :
    f (p : PowerSeries R) = Polynomial.aeval (f PowerSeries.X) p := by
  have : f.comp (Polynomial.coeToPowerSeries.algHom R) = Polynomial.aeval (f PowerSeries.X) := by
    apply Polynomial.algHom_ext
    simp
  have h := DFunLike.congr_fun this p
  simpa using h

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem algHom_ext_of_isHausdorff {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal A) [h : IsHausdorff I A] (f f' : PowerSeries R →ₐ[R] A)
    (hX : f PowerSeries.X = f' PowerSeries.X) (hy : f PowerSeries.X ∈ I) : f = f' := by
  apply AlgHom.ext
  intro F
  rw [← sub_eq_zero]
  refine IsHausdorff.haus h _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have e := F.eq_X_pow_mul_shift_add_trunc n
  set G : PowerSeries R := PowerSeries.mk fun i => PowerSeries.coeff (i + n) F
  have : f F - f' F = f PowerSeries.X ^ n * (f G - f' G) := by
    conv_lhs => rw [e]
    rw [map_add, map_add, map_mul, map_mul, map_pow, map_pow, algHom_coe, algHom_coe, ← hX]
    ring
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hy n)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem exists_eval_and_unique :
    ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (y : A),
      IsAdicComplete (Ideal.span {y}) A →
        (∃ ev : PowerSeries R →ₐ[R] A, ev PowerSeries.X = y) ∧
          ∀ f f' : PowerSeries R →ₐ[R] A, f PowerSeries.X = f' PowerSeries.X →
            y ∣ f PowerSeries.X → f = f' := by
  intro R A _ _ _ y h
  exact ⟨exists_algHom_apply_X (Ideal.span {y}) (Ideal.mem_span_singleton_self y),
    fun f f' h1 h2 => algHom_ext_of_isHausdorff (Ideal.span {y}) f f' h1
      (Ideal.mem_span_singleton.2 h2)⟩

end GlobalTheory.PowerSeriesAdicEval
