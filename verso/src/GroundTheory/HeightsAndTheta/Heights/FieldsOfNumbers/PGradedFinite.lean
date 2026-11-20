import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

section

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

/- English proof (translation)
Apply `(Finsupp.finite_of_degree_eq (∑ k, m k)).subset` to reduce the goal to its premises. Introduce `d hd`. Simplify using `only [Set.mem_ofPred_eq] at hd ⊢`. Rewrite using `[← hd, Finsupp.weight_eq_sum, Finsupp.degree_eq_sum, Finset.sum_fn, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations.

Simplify using `[blockWeight, Pi.single_apply]`.
-/
theorem finite_monomials_of_multidegree (m : K → ℕ) :
    {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m}.Finite := by
  apply (Finsupp.finite_of_degree_eq (∑ k, m k)).subset
  intro d hd
  simp only [Set.mem_ofPred_eq] at hd ⊢
  rw [← hd, Finsupp.weight_eq_sum, Finsupp.degree_eq_sum, Finset.sum_fn, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [blockWeight, Pi.single_apply]

/- English proof (translation)
Rewrite using `[weightedHomogeneousSubmodule_eq_finsupp_supported]`. Use `(finite_monomials_of_multidegree (ι := ι) m).to_subtype` as an intermediate fact. Conclude with `Module.Finite.of_basis (basisRestrictSupport F {d | Finsupp.weight (blockWeight ι) d = m})`.
-/
theorem finiteDimensional_multiHomogForms (F : Type*) [Field F] (m : K → ℕ) :
    FiniteDimensional F (weightedHomogeneousSubmodule F (blockWeight ι) m) := by
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  have := (finite_monomials_of_multidegree (ι := ι) m).to_subtype
  exact Module.Finite.of_basis
    (basisRestrictSupport F {d | Finsupp.weight (blockWeight ι) d = m})

end

/- English proof (translation)
Introduce `F _ K _ _ ι _ I m`. Establish `hfin` using `finiteDimensional_multiHomogForms (ι := ι) F m`. Establish `hP : FiniteDimensional F (gradedPiece I m)`. Unfold `gradedPiece`. Conclude with `Module.Finite.iff_fg.mpr ((Module.Finite.iff_fg.mp hfin).map (Ideal.Quotient.mkₐ F I).toLinearMap)`.

Use `⟨hP, ?_⟩` and prove the remaining obligations. Unfold `hilbFn`. Rewrite using `[if_pos fun k => Int.natCast_nonneg (m k)]`. Simplify using `only [Int.toNat_natCast]`.
-/
theorem GradedFinite.proof : GradedFinite.Statement := by
  intro F _ K _ _ ι _ I m
  have hfin := finiteDimensional_multiHomogForms (ι := ι) F m
  have hP : FiniteDimensional F (gradedPiece I m) := by
    unfold gradedPiece
    exact Module.Finite.iff_fg.mpr
      ((Module.Finite.iff_fg.mp hfin).map (Ideal.Quotient.mkₐ F I).toLinearMap)
  refine ⟨hP, ?_⟩
  unfold hilbFn
  rw [if_pos fun k => Int.natCast_nonneg (m k)]
  simp only [Int.toNat_natCast]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
