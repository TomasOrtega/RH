import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenFibreHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace GenFibreHomog

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem sum_block_eq_weight (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    ∑ i, m ⟨k, i⟩ = Finsupp.weight (NumbersDVR.blockWeight ι) m k := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [NumbersDVR.blockWeight, Pi.single_apply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem isMultiHomog_of_weighted {f : MRing ι} {b : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f b) : IsMultiHomog f b := by
  intro m hm k
  rw [sum_block_eq_weight, hf (mem_support_iff.mp hm)]

/- English proof (translation)
Proceed by induction. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Treat this case separately.
-/
theorem coeff_mConeMap {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (b : K → ℕ) (f : MRing ι) :
    coeff (Finsupp.equivFunOnFinite.symm b) (mConeMap y f) =
      aeval y (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    have hm := isWeightedHomogeneous_monomial (NumbersDVR.blockWeight ι) m c
      (rfl : Finsupp.weight (NumbersDVR.blockWeight ι) m = _)
    rw [ProjLine.mConeMap_eq_of_isMultiHomog y (isMultiHomog_of_weighted hm),
      weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hm)]
    have hX : (∏ k, (X k : MvPolynomial K Ω) ^ Finsupp.weight (NumbersDVR.blockWeight ι) m k) =
        monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (NumbersDVR.blockWeight ι) m)) 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
      simp
    rw [hX, coeff_C_mul, coeff_monomial]
    by_cases h : b = Finsupp.weight (NumbersDVR.blockWeight ι) m
    · subst h; simp
    · rw [if_neg h, if_neg (fun h' => h (Finsupp.equivFunOnFinite.symm.injective h').symm)]
      simp
  | add p q hp hq => rw [map_add, coeff_add, hp, hq, map_add, map_add]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem isMultiHomogIdeal_mCoordIdeal {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) :
    NumbersDVR.IsMultiHomogIdeal (R := ℤ) (mCoordIdeal y) := by
  intro f hf b
  have hf' : mConeMap y f = 0 := RingHom.mem_ker.mp hf
  refine RingHom.mem_ker.mpr ?_
  change mConeMap y _ = 0
  rw [ProjLine.mConeMap_eq_of_isMultiHomog y
      (isMultiHomog_of_weighted (weightedHomogeneousComponent_isWeightedHomogeneous b f)),
    ← coeff_mConeMap, hf', coeff_zero, map_zero, zero_mul]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isHomogeneous_of_isMultiHomogIdeal {R : Type} [CommRing R] {I : Ideal (MvPolynomial (Σ k, ι k) R)}
    (h : NumbersDVR.IsMultiHomogIdeal I) :
    I.IsHomogeneous (weightedHomogeneousSubmodule R (NumbersDVR.blockWeight ι)) := by
  intro b f hf
  have key : (DirectSum.decompose (weightedHomogeneousSubmodule R (NumbersDVR.blockWeight ι)) f b :
      MvPolynomial (Σ k, ι k) R) = weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f :=
    weightedDecomposition.decompose'_apply R (NumbersDVR.blockWeight ι) f b
  rw [key]
  exact h f hf b

end GenFibreHomog

open GenFibreHomog in
attribute [local instance] MvPolynomial.weightedGradedAlgebra in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem GenFibreHomog.proof : GenFibreHomog.Statement := by
  intro K _ _ ι _ Ω _ y
  have hI := isHomogeneous_of_isMultiHomogIdeal (isMultiHomogIdeal_mCoordIdeal y)
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists _ _).mp hI
  have hJ : ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))).IsHomogeneous
      (weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι)) := by
    rw [hS, Ideal.map_span]
    refine Ideal.homogeneous_span _ _ ?_
    rintro _ ⟨_, ⟨s, -, rfl⟩, rfl⟩
    obtain ⟨b, hb⟩ := s.2
    refine ⟨b, ?_⟩
    rw [mem_weightedHomogeneousSubmodule] at hb ⊢
    intro d hd
    apply hb
    intro h0
    apply hd
    rw [coeff_map, h0, map_zero]
  intro f hf b
  exact weightedHomogeneousComponent_mem_of_mem ℚ _ hJ hf b

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
