import Mathlib

open MeasureTheory Set Real
open scoped Nat ComplexConjugate

namespace GlobalTheory

section General

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def complexGaussian (g : ℕ) : Measure E :=
  volume.withDensity fun z => ENNReal.ofReal ((π ^ g)⁻¹ * exp (-‖z‖ ^ 2))

variable {E}

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem integrable_exp_neg_mul_norm_sq {b : ℝ} (hb : 0 < b) :
    Integrable fun z : E => exp (-b * ‖z‖ ^ 2) := by
  by_contra h
  have h1 := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) hb
  rw [integral_undef h] at h1
  exact absurd h1 (by positivity)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_exp_neg_mul_norm_sq {g : ℕ} (hE : Module.finrank ℝ E = 2 * g) {b : ℝ}
    (hb : 0 < b) : ∫ z : E, exp (-b * ‖z‖ ^ 2) = (π / b) ^ g := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb, hE, ← rpow_natCast]
  congr 1
  push_cast
  ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem isProbabilityMeasure_complexGaussian {g : ℕ} (hE : Module.finrank ℝ E = 2 * g) :
    IsProbabilityMeasure (complexGaussian E g) := by
  constructor
  have h := integral_exp_neg_mul_norm_sq hE one_pos
  have hi := integrable_exp_neg_mul_norm_sq (E := E) one_pos
  simp only [neg_mul, one_mul, div_one] at h hi
  rw [complexGaussian, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.const_mul _) (.of_forall fun z => by positivity),
    integral_const_mul, h, inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem integrable_norm_pow_mul_exp_neg_mul_norm_sq (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable fun z : E => ‖z‖ ^ n * exp (-b * ‖z‖ ^ 2) := by
  rcases subsingleton_or_nontrivial E with h | h
  · exact Integrable.of_finite
  rw [integrable_fun_norm_addHaar volume (f := fun r => r ^ n * exp (-b * r ^ 2))]
  have := integrableOn_rpow_mul_exp_neg_mul_sq hb
    (s := ((Module.finrank ℝ E - 1 + n : ℕ) : ℝ)) (lt_of_lt_of_le neg_one_lt_zero (by positivity))
  refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [rpow_natCast, smul_eq_mul, pow_add, mul_assoc]

end General

section Combinatorics

end Combinatorics

section Kernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end Kernel

section Monomials

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem finrank_real_euclideanSpace_complex (ι : Type*) [Fintype ι] :
    Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
  rw [finrank_real_of_complex, finrank_euclideanSpace]

/- English proof (translation)
Introduce a local definition for the expression. Express the relevant assertion in an equivalent form by its definition. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem volume_preserving_ofLp_complex (ι : Type*) [Fintype ι] :
    MeasurePreserving (@WithLp.ofLp 2 (ι → ℂ)) := by
  let e : EuclideanSpace ℂ ι ≃L[ℝ] (ι → ℂ) := PiLp.continuousLinearEquiv 2 ℝ fun _ : ι => ℂ
  change MeasurePreserving e
  refine ⟨e.continuous.measurable, ?_⟩
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map e volume = c • (volume : Measure (ι → ℂ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have h1 : ∫ w : ι → ℂ, ∏ i, exp (-1 * ‖w i‖ ^ 2) = π ^ Fintype.card ι := by
    rw [integral_fintype_prod_volume_eq_pow fun w : ℂ => exp (-1 * ‖w‖ ^ 2),
      integral_exp_neg_mul_norm_sq (E := ℂ) (g := 1) (by simp) one_pos]
    simp
  have h2 : ∫ w : ι → ℂ, ∏ i, exp (-1 * ‖w i‖ ^ 2) ∂(Measure.map e volume) =
      π ^ Fintype.card ι := by
    rw [integral_map e.continuous.measurable.aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop))]
    have := integral_exp_neg_mul_norm_sq (finrank_real_euclideanSpace_complex ι) one_pos
    rw [div_one] at this
    rw [← this]
    refine integral_congr_ae (.of_forall fun z => ?_)
    simp only
    rw [← exp_sum, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    rfl
  rw [hc, integral_smul_nnreal_measure, h1, NNReal.smul_def, smul_eq_mul,
    mul_eq_right₀ (by positivity)] at h2
  rw [hc, show c = 1 by exact_mod_cast h2, one_smul]

end Monomials

section Fin

noncomputable abbrev fockMeasure (g : ℕ) : Measure (EuclideanSpace ℂ (Fin g)) :=
  complexGaussian (EuclideanSpace ℂ (Fin g)) g

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem finrank_real_euclideanSpace_complex_fin (g : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin g)) = 2 * g := by
  rw [finrank_real_euclideanSpace_complex, Fintype.card_fin]

instance (g : ℕ) : IsProbabilityMeasure (fockMeasure g) :=
  isProbabilityMeasure_complexGaussian (finrank_real_euclideanSpace_complex_fin g)

end Fin

end GlobalTheory
